module

public import PsiZooProofs.GridHamiltonian
public import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

/-!
# Exact norm conservation for an implicit Crank–Nicolson step

States contain only the `Fin n` interior Dirichlet coordinates. The same fixed
real potential occurs on both sides, with hbar = m = 1. The matrix signs match
`crankNicolson.ts`: A = I + i(dt/2)H and B = I - i(dt/2)H.

Conservation is conditional on the implicit equation, for every real time step
(including zero and negative values). No solution existence, matrix inverse,
unitarity, or floating-point conservation is asserted.
-/

@[expose] public section

open scoped ComplexConjugate

namespace PsiZoo

/-- Left matrix of the implicit step: I + i(dt/2)H. -/
noncomputable def crankNicolsonLeftMatrix {n : ℕ} (dx dt : ℝ) (V : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 + (Complex.I * (dt / 2 : ℝ)) • gridHamiltonianMatrix dx V

/-- Right matrix of the implicit step: I - i(dt/2)H. -/
noncomputable def crankNicolsonRightMatrix {n : ℕ} (dx dt : ℝ) (V : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 - (Complex.I * (dt / 2 : ℝ)) • gridHamiltonianMatrix dx V

/-- An implicit step relation, not a solver or an existence assertion. -/
def CrankNicolsonStep {n : ℕ} (dx dt : ℝ) (V : Fin n → ℝ)
    (psiPrev psiNext : Fin n → ℂ) : Prop :=
  (crankNicolsonLeftMatrix dx dt V).mulVec psiNext =
    (crankNicolsonRightMatrix dx dt V).mulVec psiPrev

/-- Moving terms across the implicit equation gives the midpoint difference
formula. Conversely, that formula implies the original matrix equation. -/
theorem crankNicolsonStep_iff {n : ℕ} (dx dt : ℝ) (V : Fin n → ℝ)
    (psiPrev psiNext : Fin n → ℂ) :
    CrankNicolsonStep dx dt V psiPrev psiNext ↔
      psiNext - psiPrev =
        (-Complex.I * (dt / 2 : ℝ)) •
          applyGridHamiltonian dx V (psiNext + psiPrev) := by
  unfold CrankNicolsonStep crankNicolsonLeftMatrix crankNicolsonRightMatrix
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  unfold applyGridHamiltonian
  rw [Matrix.mulVec_add]
  constructor <;> intro h <;> ext i
  · have hi := congrFun h i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  · have hi := congrFun h i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination hi

/-- Subtraction in the linear (second) argument. -/
theorem gridInnerProduct_sub_right {n : ℕ} (dx : ℝ)
    (phi psi chi : Fin n → ℂ) :
    gridInnerProduct dx phi (psi - chi) =
      gridInnerProduct dx phi psi - gridInnerProduct dx phi chi := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ chi, gridInnerProduct_add_right,
    gridInnerProduct_smul_right]
  simp [sub_eq_add_neg]

/-- Real polarization: the mixed terms cancel by conjugate symmetry under
our convention (conjugate-linear first, linear second). -/
theorem weightedSquaredNorm_sub_eq_re_gridInnerProduct {n : ℕ} (dx : ℝ)
    (psiNext psiPrev : Fin n → ℂ) :
    weightedSquaredNorm dx psiNext - weightedSquaredNorm dx psiPrev =
      (gridInnerProduct dx (psiNext + psiPrev) (psiNext - psiPrev)).re := by
  rw [gridInnerProduct_add_left, gridInnerProduct_sub_right,
    gridInnerProduct_sub_right, gridInnerProduct_self, gridInnerProduct_self]
  rw [gridInnerProduct_conj_symm dx psiPrev psiNext]
  simp

/-- Every implicit Crank–Nicolson step conserves the existing dx-weighted
squared norm exactly. No sign restriction is imposed on dt. -/
theorem crankNicolsonStep_weightedSquaredNorm {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psiPrev psiNext : Fin n → ℂ)
    (hstep : CrankNicolsonStep dx dt V psiPrev psiNext) :
    weightedSquaredNorm dx psiNext = weightedSquaredNorm dx psiPrev := by
  have hdiff := (crankNicolsonStep_iff dx dt V psiPrev psiNext).mp hstep
  have henergy := gridHamiltonian_energy_im_eq_zero dx V hdx (psiNext + psiPrev)
  have hzero : weightedSquaredNorm dx psiNext - weightedSquaredNorm dx psiPrev = 0 := by
    rw [weightedSquaredNorm_sub_eq_re_gridInnerProduct, hdiff,
      gridInnerProduct_smul_right]
    simp [Complex.mul_re, Complex.mul_im, henergy]
  exact sub_eq_zero.mp hzero

/-- A unit-normalized initial state stays unit-normalized after any implicit step. -/
theorem crankNicolsonStep_preserves_normalization {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) (psiPrev psiNext : Fin n → ℂ)
    (hstep : CrankNicolsonStep dx dt V psiPrev psiNext)
    (hprev : weightedSquaredNorm dx psiPrev = 1) :
    weightedSquaredNorm dx psiNext = 1 := by
  rw [crankNicolsonStep_weightedSquaredNorm dx dt V hdx psiPrev psiNext hstep, hprev]

end PsiZoo
