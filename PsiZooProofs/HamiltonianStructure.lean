module

public import PsiZooProofs.HermitianCayley

set_option linter.style.header false

/-! # Kinetic plus real diagonal potential decomposition

Interior Dirichlet indexing and coefficients are inherited from
`gridHamiltonianMatrix`. The kinetic matrix is obtained by setting V = 0.
-/

@[expose] public section

namespace PsiZoo

noncomputable def realPotentialMatrix {n : ℕ} (V : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (V i : ℂ))

noncomputable def gridKineticMatrix {n : ℕ} (dx : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  gridHamiltonianMatrix dx (fun _ => 0)

theorem realPotentialMatrix_isHermitian {n : ℕ} (V : Fin n → ℝ) :
    (realPotentialMatrix V).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [realPotentialMatrix]
  · simp [realPotentialMatrix, hij, Ne.symm hij]

theorem gridKineticMatrix_isHermitian {n : ℕ} (dx : ℝ) :
    (gridKineticMatrix (n := n) dx).IsHermitian :=
  gridHamiltonianMatrix_isHermitian dx (fun _ => 0)

/-- H = T + diag(V), with the same Dirichlet boundary convention in each term. -/
theorem gridHamiltonianMatrix_decomposition {n : ℕ} (dx : ℝ) (V : Fin n → ℝ) :
    gridHamiltonianMatrix dx V = gridKineticMatrix dx + realPotentialMatrix V := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [gridHamiltonianMatrix, gridKineticMatrix, realPotentialMatrix]
  · simp [gridHamiltonianMatrix, gridKineticMatrix, realPotentialMatrix, hij]

/-- Hermiticity can alternatively be derived compositionally from T and diag(V). -/
theorem gridHamiltonianMatrix_isHermitian_of_decomposition {n : ℕ} (dx : ℝ)
    (V : Fin n → ℝ) : (gridHamiltonianMatrix dx V).IsHermitian := by
  rw [gridHamiltonianMatrix_decomposition]
  exact (gridKineticMatrix_isHermitian dx).add (realPotentialMatrix_isHermitian V)

/-- The real diagonal energy is the density-weighted sum of potential values. -/
theorem realPotentialMatrix_energy {n : ℕ} (dx : ℝ) (V : Fin n → ℝ) (psi : Fin n → ℂ) :
    gridInnerProduct dx psi ((realPotentialMatrix V).mulVec psi) =
      ((dx * ∑ i, V i * Complex.normSq (psi i) : ℝ) : ℂ) := by
  simp only [gridInnerProduct, realPotentialMatrix, Matrix.mulVec_diagonal,
    Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm, conj_mul_self]

/-- Nonnegative barriers have a nonnegative potential-energy contribution. -/
theorem realPotentialMatrix_energy_nonneg {n : ℕ} (dx : ℝ) (V : Fin n → ℝ)
    (psi : Fin n → ℂ) (hdx : 0 ≤ dx) (hV : ∀ i, 0 ≤ V i) :
    0 ≤ (gridInnerProduct dx psi ((realPotentialMatrix V).mulVec psi)).re := by
  rw [realPotentialMatrix_energy]
  exact mul_nonneg hdx (Finset.sum_nonneg (fun i _ => mul_nonneg (hV i) (Complex.normSq_nonneg _)))

end PsiZoo
