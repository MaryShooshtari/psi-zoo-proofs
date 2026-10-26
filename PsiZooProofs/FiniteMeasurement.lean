module

public import PsiZooProofs.CoordinateProjection
public import PsiZooProofs.CrankNicolsonUnitarity

set_option linter.style.header false

/-! # Finite diagonal measurements
The first response index is the observed outcome, the second is the input site.
Only interior Dirichlet sites are represented. Probabilities are masses, not densities.
-/

@[expose] public section

open scoped Matrix ComplexConjugate

namespace PsiZoo

/-- A column-stochastic real response, with no assumption of row normalization. -/
structure MeasurementResponse (n : ℕ) where
  kernel : Fin n → Fin n → ℝ
  nonneg : ∀ j i, 0 ≤ kernel j i
  sum_column : ∀ i, ∑ j, kernel j i = 1

namespace MeasurementResponse

variable {n : ℕ} (R : MeasurementResponse n)

/-- Diagonal Kraus operator applied to a state. -/
noncomputable def mask (j : Fin n) (psi : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (Real.sqrt (R.kernel j i) : ℂ) * psi i

noncomputable def matrix (j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (R.kernel j i) : ℂ))

theorem matrix_mulVec (j : Fin n) (psi : Fin n → ℂ) :
    (R.matrix j).mulVec psi = R.mask j psi := by
  ext i
  simp [matrix, mask, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- Born outcome mass; the input norm is not assumed to be one. -/
noncomputable def probability (dx : ℝ) (psi : Fin n → ℂ) (j : Fin n) : ℝ :=
  (dx * ∑ i, R.kernel j i * Complex.normSq (psi i)) / weightedSquaredNorm dx psi

theorem probability_nonneg (dx : ℝ) (psi : Fin n → ℂ) (j : Fin n)
    (hdx : 0 < dx) : 0 ≤ R.probability dx psi j := by
  apply div_nonneg
  · exact mul_nonneg hdx.le (Finset.sum_nonneg fun i _ =>
      mul_nonneg (R.nonneg j i) (Complex.normSq_nonneg _))
  · exact mul_nonneg hdx.le (sumSquaredMagnitudes_nonneg psi)

theorem sum_probability (dx : ℝ) (psi : Fin n → ℂ)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) :
    ∑ j, R.probability dx psi j = 1 := by
  unfold probability
  rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, R.sum_column, one_mul]
  exact div_self (ne_of_gt (weightedSquaredNorm_pos dx psi hdx hpsi))

theorem normSq_mask (j i : Fin n) (psi : Fin n → ℂ) :
    Complex.normSq (R.mask j psi i) = R.kernel j i * Complex.normSq (psi i) := by
  simp [mask, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (R.nonneg j i)]

/-- The probability is precisely the masked squared norm divided by the input norm. -/
theorem probability_eq_norm_ratio (dx : ℝ) (psi : Fin n → ℂ) (j : Fin n) :
    R.probability dx psi j =
      weightedSquaredNorm dx (R.mask j psi) / weightedSquaredNorm dx psi := by
  simp only [probability, weightedSquaredNorm, sumSquaredMagnitudes, R.normSq_mask]

/-- Actual matrix completeness, not merely conservation for a selected state. -/
theorem completeness : ∑ j, (R.matrix j)ᴴ * R.matrix j = 1 := by
  have heach (j : Fin n) : (R.matrix j)ᴴ * R.matrix j =
      Matrix.diagonal (fun i => (R.kernel j i : ℂ)) := by
    simp only [matrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    change conj (Real.sqrt (R.kernel j i) : ℂ) *
      (Real.sqrt (R.kernel j i) : ℂ) = (R.kernel j i : ℂ)
    rw [Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt (R.nonneg j i)
  simp_rw [heach]
  ext i k
  simp only [Matrix.sum_apply]
  by_cases h : i = k
  · subst k
    simpa [Matrix.diagonal_apply] using
      congrArg (fun x : ℝ => (x : ℂ)) (R.sum_column i)
  · simp [h]

/-- The conditional state uses exactly sqrt(N P(j)) in its denominator. -/
noncomputable def conditional (dx : ℝ) (psi : Fin n → ℂ) (j : Fin n) : Fin n → ℂ :=
  fun i => R.mask j psi i /
    (Real.sqrt (weightedSquaredNorm dx psi * R.probability dx psi j) : ℂ)

theorem mass_eq_norm_mul_probability (dx : ℝ) (psi : Fin n → ℂ) (j : Fin n)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) :
    weightedSquaredNorm dx (R.mask j psi) =
      weightedSquaredNorm dx psi * R.probability dx psi j := by
  rw [R.probability_eq_norm_ratio]
  field_simp [ne_of_gt (weightedSquaredNorm_pos dx psi hdx hpsi)]

theorem conditional_normalized (dx : ℝ) (psi : Fin n → ℂ) (j : Fin n)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0)
    (hp : 0 < R.probability dx psi j) :
    weightedSquaredNorm dx (R.conditional dx psi j) = 1 := by
  have hn := weightedSquaredNorm_pos dx psi hdx hpsi
  have hm := R.mass_eq_norm_mul_probability dx psi j hdx hpsi
  have hprod := mul_pos hn hp
  change dx * (∑ i, Complex.normSq (_ / _)) = 1
  simp_rw [Complex.normSq_div, Complex.normSq_ofReal,
    Real.mul_self_sqrt hprod.le]
  rw [← Finset.sum_div, ← mul_div_assoc]
  change weightedSquaredNorm dx (R.mask j psi) / _ = 1
  rw [hm, div_self (ne_of_gt hprod)]

/-- Every surviving component is multiplied by a strictly positive real scalar.
This positive-ray statement preserves complex phase without choosing an argument branch. -/
theorem conditional_positive_ray (dx : ℝ) (psi : Fin n → ℂ) (j i : Fin n)
    (hdx : 0 < dx) (hpsi : ∃ k, psi k ≠ 0)
    (hp : 0 < R.probability dx psi j) (hk : 0 < R.kernel j i) :
    ∃ a : ℝ, 0 < a ∧ R.conditional dx psi j i = (a : ℂ) * psi i := by
  refine ⟨Real.sqrt (R.kernel j i) /
    Real.sqrt (weightedSquaredNorm dx psi * R.probability dx psi j),
    div_pos (Real.sqrt_pos.2 hk) (Real.sqrt_pos.2
      (mul_pos (weightedSquaredNorm_pos dx psi hdx hpsi) hp)), ?_⟩
  simp only [conditional, mask, Complex.ofReal_div]
  ring

/-- Pairwise coherences acquire only the product of the positive real multipliers. -/
theorem relative_phase_algebra (psi : Fin n → ℂ) (j i k : Fin n) :
    R.mask j psi i * conj (R.mask j psi k) =
      ((Real.sqrt (R.kernel j i) * Real.sqrt (R.kernel j k) : ℝ) : ℂ) *
        (psi i * conj (psi k)) := by
  simp [mask, map_mul]
  ring

theorem conditional_cn_normalized (dx dt : ℝ) (V : Fin n → ℝ)
    (psi : Fin n → ℂ) (j : Fin n) (hdx : 0 < dx)
    (hpsi : ∃ i, psi i ≠ 0) (hp : 0 < R.probability dx psi j) :
    weightedSquaredNorm dx
      ((crankNicolsonEvolution dx dt V).mulVec (R.conditional dx psi j)) = 1 := by
  exact crankNicolsonEvolution_preserves_normalization dx dt V hdx _
    (R.conditional_normalized dx psi j hdx hpsi hp)

end MeasurementResponse

/-- Ideal coordinate measurement is a special response, not a finite-width Gaussian. -/
def deltaResponse (n : ℕ) : MeasurementResponse n where
  kernel j i := if j = i then 1 else 0
  nonneg j i := by split <;> norm_num
  sum_column i := by simp

theorem delta_mask_eq_coordinateProjection {n : ℕ} (j : Fin n) (psi : Fin n → ℂ) :
    (deltaResponse n).mask j psi = coordinateProjection {j} psi := by
  ext i
  by_cases h : j = i
  · subst i; simp [MeasurementResponse.mask, deltaResponse, coordinateProjection]
  · simp [MeasurementResponse.mask, deltaResponse, coordinateProjection, h, Ne.symm h]

/-- Reuse the established projection mass theorem. -/
theorem delta_mask_mass {n : ℕ} (j : Fin n) (dx : ℝ) (psi : Fin n → ℂ) :
    weightedSquaredNorm dx ((deltaResponse n).mask j psi) =
      regionProbability dx psi {j} := by
  rw [delta_mask_eq_coordinateProjection, coordinateProjection_mass]

end PsiZoo
