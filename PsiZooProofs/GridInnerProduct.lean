module

public import PsiZooProofs.GridNormalization
public import Mathlib.Basic.Complex.BigOperators

set_option linter.style.header false

/-!
# The discrete spatial complex inner product

The first argument is conjugate-linear and the second is linear, matching
`innerProduct(psi1, psi2)` in the simulation. Spacing is explicitly real.
We do not change the default norm or install an inner-product instance on
`Fin n → ℂ`. Algebraic identities hold for all real spacings; positive
definiteness requires positive spacing.
-/

@[expose] public section

open scoped ComplexConjugate

namespace PsiZoo

/-- The uniform-grid inner product, with conjugation in the first argument. -/
noncomputable def gridInnerProduct {n : ℕ} (dx : ℝ)
    (phi psi : Fin n → ℂ) : ℂ :=
  (dx : ℂ) * ∑ i, conj (phi i) * psi i

/-- Conjugate symmetry uses the fact that the spacing is real. -/
theorem gridInnerProduct_conj_symm {n : ℕ} (dx : ℝ) (phi psi : Fin n → ℂ) :
    gridInnerProduct dx phi psi = conj (gridInnerProduct dx psi phi) := by
  simp [gridInnerProduct, map_sum, mul_comm]

/-- Additivity in the second argument. -/
theorem gridInnerProduct_add_right {n : ℕ} (dx : ℝ) (phi psi chi : Fin n → ℂ) :
    gridInnerProduct dx phi (psi + chi) =
      gridInnerProduct dx phi psi + gridInnerProduct dx phi chi := by
  simp [gridInnerProduct, mul_add, Finset.sum_add_distrib]

/-- Complex scalar linearity in the second argument. -/
theorem gridInnerProduct_smul_right {n : ℕ} (dx : ℝ) (phi psi : Fin n → ℂ)
    (c : ℂ) :
    gridInnerProduct dx phi (c • psi) = c * gridInnerProduct dx phi psi := by
  simp only [gridInnerProduct, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (conj (phi _)) c]
  rw [← Finset.mul_sum, mul_left_comm]

/-- Additivity in the conjugate-linear first argument. -/
theorem gridInnerProduct_add_left {n : ℕ} (dx : ℝ) (phi psi chi : Fin n → ℂ) :
    gridInnerProduct dx (phi + psi) chi =
      gridInnerProduct dx phi chi + gridInnerProduct dx psi chi := by
  simp [gridInnerProduct, map_add, add_mul, Finset.sum_add_distrib, mul_add]

/-- Scalars in the first argument are conjugated. -/
theorem gridInnerProduct_smul_left {n : ℕ} (dx : ℝ) (phi psi : Fin n → ℂ)
    (c : ℂ) :
    gridInnerProduct dx (c • phi) psi = conj c * gridInnerProduct dx phi psi := by
  simp only [gridInnerProduct, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  rw [← Finset.mul_sum, mul_left_comm]

/-- The self inner product is the existing real weighted squared norm. -/
theorem gridInnerProduct_self {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ) :
    gridInnerProduct dx psi psi = (weightedSquaredNorm dx psi : ℂ) := by
  simp [gridInnerProduct, weightedSquaredNorm, sumSquaredMagnitudes,
    conj_mul_self, Complex.ofReal_sum]

/-- Nonnegativity of the weighted squared norm for positive spacing. -/
theorem weightedSquaredNorm_nonneg {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (hdx : 0 < dx) : 0 ≤ weightedSquaredNorm dx psi := by
  exact mul_nonneg (le_of_lt hdx) (sumSquaredMagnitudes_nonneg psi)

/-- At positive spacing the self inner product vanishes exactly for the zero state. -/
theorem gridInnerProduct_self_eq_zero_iff {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (hdx : 0 < dx) :
    gridInnerProduct dx psi psi = 0 ↔ ∀ i, psi i = 0 := by
  rw [gridInnerProduct_self]
  simp only [Complex.ofReal_eq_zero, weightedSquaredNorm,
    mul_eq_zero, ne_of_gt hdx, false_or]
  exact sumSquaredMagnitudes_eq_zero_iff psi

/-- Grid normalization produces a unit self inner product. -/
theorem gridInnerProduct_normalizeGridState_self {n : ℕ} (dx : ℝ)
    (psi : Fin n → ℂ) (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) :
    gridInnerProduct dx (normalizeGridState dx psi hdx hpsi)
      (normalizeGridState dx psi hdx hpsi) = 1 := by
  rw [gridInnerProduct_self, weightedSquaredNorm_normalizeGridState dx psi hdx hpsi,
    Complex.ofReal_one]

end PsiZoo
