module

public import PsiZooProofs.GridInnerProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option linter.style.header false

/-!
# The interior Dirichlet finite-difference Hamiltonian

Units are hbar = m = 1. `Fin n` indexes only the interior points of a physical
`n + 2` point grid: interior index `j` corresponds to full-grid index `j + 1`.
The two omitted endpoints have prescribed value zero. Summing only over
interior columns therefore omits their zero contributions. In dimension zero
the action is empty; in dimension one only the diagonal term remains.

This models the coefficients and N-2 interior degrees of freedom used by
`crankNicolson.ts`, which checks zero endpoints and solves only for interiors.
`hamiltonian.ts` also forces output endpoints to zero, but its interior rows
read stored input endpoints. We make no Hermiticity claim for that operation
on unrestricted full-grid inputs. The correspondence to TypeScript and its
floating-point execution is documented here, not formally verified.
-/

@[expose] public section

open scoped ComplexConjugate

namespace PsiZoo

/-- The three-point Hamiltonian on interior degrees of freedom, with a fixed
real potential. Adjacency uses natural-number indices, with no wraparound. -/
noncomputable def gridHamiltonianMatrix {n : ℕ} (dx : ℝ) (V : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then ((1 / dx ^ 2 + V i : ℝ) : ℂ)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
      ((-1 / (2 * dx ^ 2) : ℝ) : ℂ)
    else 0

/-- Matrix action on an interior state; missing boundary neighbors contribute zero. -/
noncomputable def applyGridHamiltonian {n : ℕ} (dx : ℝ) (V : Fin n → ℝ)
    (psi : Fin n → ℂ) : Fin n → ℂ :=
  (gridHamiltonianMatrix dx V).mulVec psi

/-- Entrywise Hermiticity: the coefficients are real and symmetric. -/
theorem gridHamiltonianMatrix_conj_symm {n : ℕ} (dx : ℝ) (V : Fin n → ℝ)
    (i j : Fin n) :
    gridHamiltonianMatrix dx V i j = conj (gridHamiltonianMatrix dx V j i) := by
  by_cases h : i = j
  · subst j
    simp [gridHamiltonianMatrix]
  · by_cases ha : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · simp only [gridHamiltonianMatrix, h, Ne.symm h, ha, or_comm, ite_true, ite_false]
      exact (Complex.conj_ofReal _).symm
    · simp [gridHamiltonianMatrix, h, Ne.symm h, ha, or_comm]

/-- Hermiticity in Mathlib's standard matrix predicate. -/
theorem gridHamiltonianMatrix_isHermitian {n : ℕ} (dx : ℝ) (V : Fin n → ℝ) :
    (gridHamiltonianMatrix dx V).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact (gridHamiltonianMatrix_conj_symm dx V i j).symm

/-- The interior Hamiltonian is Hermitian for the spatially weighted inner product. -/
theorem gridInnerProduct_applyGridHamiltonian {n : ℕ} (dx : ℝ) (V : Fin n → ℝ)
    (_hdx : 0 < dx) (phi psi : Fin n → ℂ) :
    gridInnerProduct dx phi (applyGridHamiltonian dx V psi) =
      gridInnerProduct dx (applyGridHamiltonian dx V phi) psi := by
  unfold gridInnerProduct
  apply congrArg (fun z : ℂ => (dx : ℂ) * z)
  unfold applyGridHamiltonian
  simp only [Matrix.mulVec_apply_eq_sum, map_sum, map_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← gridHamiltonianMatrix_conj_symm dx V j i]
  ring

/-- The energy quadratic form has zero imaginary part for every interior state. -/
theorem gridHamiltonian_energy_im_eq_zero {n : ℕ} (dx : ℝ) (V : Fin n → ℝ)
    (hdx : 0 < dx) (psi : Fin n → ℂ) :
    (gridInnerProduct dx psi (applyGridHamiltonian dx V psi)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    conj (gridInnerProduct dx psi (applyGridHamiltonian dx V psi)) =
        gridInnerProduct dx (applyGridHamiltonian dx V psi) psi :=
      (gridInnerProduct_conj_symm dx (applyGridHamiltonian dx V psi) psi).symm
    _ = gridInnerProduct dx psi (applyGridHamiltonian dx V psi) :=
      (gridInnerProduct_applyGridHamiltonian dx V hdx psi psi).symm

end PsiZoo
