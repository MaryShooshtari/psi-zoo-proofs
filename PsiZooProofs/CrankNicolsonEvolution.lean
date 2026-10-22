module

public import PsiZooProofs.CrankNicolsonInvertibility

set_option linter.style.header false

/-!
# The explicit Crank–Nicolson evolution matrix

On the existing interior Dirichlet state space, define U = A⁻¹ B using
Mathlib's nonsingular matrix inverse. Positive spacing makes A a unit by the
previous milestone, so U gives the unique solution of the implicit equation.
Its exact weighted norm conservation follows from conditional conservation,
not from an assumed or proved matrix unitarity identity.

Every real time step is allowed, including zero and negative values. The
results include dimensions zero and one and make no floating-point claims.
-/

@[expose] public section

namespace PsiZoo

/-- Explicit evolution matrix A⁻¹ B, with the existing left and right matrices. -/
noncomputable def crankNicolsonEvolution {n : ℕ} (dx dt : ℝ) (V : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (crankNicolsonLeftMatrix dx dt V)⁻¹ * crankNicolsonRightMatrix dx dt V

/-- Invertibility of A justifies cancellation in A (A⁻¹ B) = B. -/
theorem crankNicolsonLeftMatrix_mul_evolution {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    crankNicolsonLeftMatrix dx dt V * crankNicolsonEvolution dx dt V =
      crankNicolsonRightMatrix dx dt V := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (crankNicolsonLeftMatrix_isUnit dx dt V hdx)
  unfold crankNicolsonEvolution
  exact Matrix.mul_nonsing_inv_cancel_left _ _ hdet

/-- Applying the evolution matrix produces a solution of the implicit step. -/
theorem crankNicolsonEvolution_step {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psiPrev : Fin n → ℂ) :
    CrankNicolsonStep dx dt V psiPrev
      ((crankNicolsonEvolution dx dt V).mulVec psiPrev) := by
  unfold CrankNicolsonStep
  rw [Matrix.mulVec_mulVec, crankNicolsonLeftMatrix_mul_evolution dx dt V hdx]

/-- Any implicit next state equals the explicit evolution of the previous state. -/
theorem crankNicolsonStep_eq_evolution {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psiPrev psiNext : Fin n → ℂ)
    (hstep : CrankNicolsonStep dx dt V psiPrev psiNext) :
    psiNext = (crankNicolsonEvolution dx dt V).mulVec psiPrev := by
  have hexplicit := crankNicolsonEvolution_step dx dt V hdx psiPrev
  apply crankNicolsonLeftMatrix_mulVec_injective dx dt V hdx
  exact hstep.trans hexplicit.symm

/-- The explicit operator preserves the existing weighted squared norm,
by conditional norm conservation applied to its implicit step. -/
theorem crankNicolsonEvolution_weightedSquaredNorm {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psi : Fin n → ℂ) :
    weightedSquaredNorm dx ((crankNicolsonEvolution dx dt V).mulVec psi) =
      weightedSquaredNorm dx psi := by
  exact crankNicolsonStep_weightedSquaredNorm dx dt V hdx psi
    ((crankNicolsonEvolution dx dt V).mulVec psi)
    (crankNicolsonEvolution_step dx dt V hdx psi)

/-- A unit-normalized state stays unit-normalized under explicit evolution. -/
theorem crankNicolsonEvolution_preserves_normalization {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psi : Fin n → ℂ)
    (hpsi : weightedSquaredNorm dx psi = 1) :
    weightedSquaredNorm dx ((crankNicolsonEvolution dx dt V).mulVec psi) = 1 := by
  rw [crankNicolsonEvolution_weightedSquaredNorm dx dt V hdx psi, hpsi]

/-- At zero time step, both matrices are I and evolution is I.
This identity does not require positive spacing. -/
theorem crankNicolsonEvolution_zero_dt {n : ℕ} (dx : ℝ) (V : Fin n → ℝ) :
    crankNicolsonEvolution dx 0 V = 1 := by
  simp [crankNicolsonEvolution, crankNicolsonLeftMatrix, crankNicolsonRightMatrix]

end PsiZoo
