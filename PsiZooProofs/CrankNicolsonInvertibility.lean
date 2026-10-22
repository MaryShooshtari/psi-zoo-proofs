module

public import PsiZooProofs.CrankNicolsonConservation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-!
# Invertibility and unique solvability of the implicit Crank–Nicolson step

The left matrix is the existing I + i(dt/2)H on `Fin n` interior Dirichlet
coordinates, with hbar = m = 1 and a fixed real potential. Conservation for a
step from zero proves its kernel is trivial. Finite-dimensional matrix algebra
then gives invertibility and a unique next state for each previous state.

All real time steps are allowed, including zero and negative values. No
nonempty-dimension assumption is needed. These are exact-arithmetic results;
no Cayley-transform unitarity or floating-point solver guarantee is asserted.
-/

@[expose] public section

namespace PsiZoo

/-- A state in the kernel of the left matrix is zero: conservation applied
from the zero state forces its weighted squared norm to vanish. -/
theorem crankNicolsonLeftMatrix_mulVec_eq_zero {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psi : Fin n → ℂ)
    (hkernel : (crankNicolsonLeftMatrix dx dt V).mulVec psi = 0) :
    psi = 0 := by
  have hstep : CrankNicolsonStep dx dt V 0 psi := by
    unfold CrankNicolsonStep
    rw [hkernel, Matrix.mulVec_zero]
  have hnorm := crankNicolsonStep_weightedSquaredNorm dx dt V hdx 0 psi hstep
  have hnormZero : weightedSquaredNorm dx psi = 0 := by
    simpa [weightedSquaredNorm, sumSquaredMagnitudes] using hnorm
  have hself : gridInnerProduct dx psi psi = 0 := by
    rw [gridInnerProduct_self, hnormZero, Complex.ofReal_zero]
  ext i
  exact (gridInnerProduct_self_eq_zero_iff dx psi hdx).mp hself i

/-- The left matrix acts injectively, since the difference of states with
identical images lies in its trivial kernel. -/
theorem crankNicolsonLeftMatrix_mulVec_injective {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    Function.Injective (crankNicolsonLeftMatrix dx dt V).mulVec := by
  intro psi chi heq
  have hkernel : (crankNicolsonLeftMatrix dx dt V).mulVec (psi - chi) = 0 := by
    rw [Matrix.mulVec_sub, heq, sub_self]
  exact sub_eq_zero.mp
    (crankNicolsonLeftMatrix_mulVec_eq_zero dx dt V hdx (psi - chi) hkernel)

/-- The finite square left matrix is a unit for every real time step. -/
theorem crankNicolsonLeftMatrix_isUnit {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    IsUnit (crankNicolsonLeftMatrix dx dt V) := by
  exact Matrix.mulVec_injective_iff_isUnit.mp
    (crankNicolsonLeftMatrix_mulVec_injective dx dt V hdx)

/-- Each previous interior state has exactly one next state satisfying the
implicit equation. This proves solvability, without defining a numerical solver. -/
theorem crankNicolsonStep_existsUnique {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psiPrev : Fin n → ℂ) :
    ∃! psiNext, CrankNicolsonStep dx dt V psiPrev psiNext := by
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr
    (crankNicolsonLeftMatrix_isUnit dx dt V hdx)
  obtain ⟨psiNext, hnext⟩ := hsurj ((crankNicolsonRightMatrix dx dt V).mulVec psiPrev)
  refine ⟨psiNext, hnext, ?_⟩
  intro chi hchi
  apply crankNicolsonLeftMatrix_mulVec_injective dx dt V hdx
  exact hchi.trans hnext.symm

end PsiZoo
