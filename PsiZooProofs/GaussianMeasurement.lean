module

public import PsiZooProofs.FiniteMeasurement
public import Mathlib.Analysis.SpecialFunctions.Exp

set_option linter.style.header false

/-! # The boundary-normalized Gaussian detector
`j` is the observed site and `i` is the input site. The denominator sums over
all allowed outcomes for each fixed input. The physical uniform coordinates
are `x i = x0 + (i.val + 1) * dx`; no endpoint is included in `Fin n`.
-/

@[expose] public section

namespace PsiZoo

/-- Interior index zero corresponds to physical index one. -/
noncomputable def interiorCoordinate {n : ℕ} (x0 dx : ℝ) (i : Fin n) : ℝ :=
  x0 + ((i.val : ℝ) + 1) * dx

theorem interiorCoordinate_sub {n : ℕ} (x0 dx : ℝ) (j i : Fin n) :
    interiorCoordinate x0 dx j - interiorCoordinate x0 dx i =
      ((j.val : ℝ) - (i.val : ℝ)) * dx := by
  unfold interiorCoordinate
  ring

noncomputable def gaussianResponseWeight {n : ℕ} (x : Fin n → ℝ) (sigma : ℝ)
    (j i : Fin n) : ℝ :=
  Real.exp (-((x j - x i) ^ 2) / (2 * sigma ^ 2))

noncomputable def gaussianResponseDenominator {n : ℕ} (x : Fin n → ℝ)
    (sigma : ℝ) (i : Fin n) : ℝ := ∑ j, gaussianResponseWeight x sigma j i

theorem gaussianResponseWeight_pos {n : ℕ} (x : Fin n → ℝ) (sigma : ℝ)
    (j i : Fin n) : 0 < gaussianResponseWeight x sigma j i :=
  Real.exp_pos _

/-- The input site itself supplies a positive summand, so the denominator cannot vanish. -/
theorem gaussianResponseDenominator_pos {n : ℕ} (x : Fin n → ℝ)
    (sigma : ℝ) (i : Fin n) : 0 < gaussianResponseDenominator x sigma i := by
  apply Finset.sum_pos'
  · intro j _; exact (gaussianResponseWeight_pos x sigma j i).le
  · exact ⟨i, Finset.mem_univ i, gaussianResponseWeight_pos x sigma i i⟩

/-- Physical resolution is positive; a nonempty grid is explicit at construction.
The positivity arguments actually work for every real exponent. -/
noncomputable def gaussianResponse {n : ℕ} (_hn : 0 < n) (x : Fin n → ℝ)
    (sigma : ℝ) (_hsigma : 0 < sigma) : MeasurementResponse n where
  kernel j i := gaussianResponseWeight x sigma j i / gaussianResponseDenominator x sigma i
  nonneg j i := (div_pos (gaussianResponseWeight_pos x sigma j i)
    (gaussianResponseDenominator_pos x sigma i)).le
  sum_column i := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (gaussianResponseDenominator_pos x sigma i))

theorem gaussian_kernel_pos {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) (j i : Fin n) :
    0 < (gaussianResponse hn x sigma hsigma).kernel j i :=
  div_pos (gaussianResponseWeight_pos x sigma j i)
    (gaussianResponseDenominator_pos x sigma i)

theorem gaussian_sum_column {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) (i : Fin n) :
    ∑ j, (gaussianResponse hn x sigma hsigma).kernel j i = 1 :=
  (gaussianResponse hn x sigma hsigma).sum_column i

open scoped Matrix in
theorem gaussian_completeness {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    ∑ j, ((gaussianResponse hn x sigma hsigma).matrix j)ᴴ *
      (gaussianResponse hn x sigma hsigma).matrix j = 1 :=
  (gaussianResponse hn x sigma hsigma).completeness

theorem gaussian_sum_probability {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) (dx : ℝ) (psi : Fin n → ℂ)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) :
    ∑ j, (gaussianResponse hn x sigma hsigma).probability dx psi j = 1 :=
  (gaussianResponse hn x sigma hsigma).sum_probability dx psi hdx hpsi

/-- In exact arithmetic every Gaussian outcome has positive mass for a nonzero state. -/
theorem gaussian_probability_pos {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) (dx : ℝ) (psi : Fin n → ℂ)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) (j : Fin n) :
    0 < (gaussianResponse hn x sigma hsigma).probability dx psi j := by
  apply div_pos (mul_pos hdx ?_) (weightedSquaredNorm_pos dx psi hdx hpsi)
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg ((gaussianResponse hn x sigma hsigma).nonneg j i)
      (Complex.normSq_nonneg _)
  · obtain ⟨i, hi⟩ := hpsi
    exact ⟨i, Finset.mem_univ i,
      mul_pos (gaussian_kernel_pos hn x sigma hsigma j i)
        (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm
          (fun h => hi (Complex.normSq_eq_zero.mp h))))⟩

theorem gaussian_conditional_normalized {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) (dx : ℝ) (psi : Fin n → ℂ) (j : Fin n)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0)
    (hp : 0 < (gaussianResponse hn x sigma hsigma).probability dx psi j) :
    weightedSquaredNorm dx
      ((gaussianResponse hn x sigma hsigma).conditional dx psi j) = 1 :=
  (gaussianResponse hn x sigma hsigma).conditional_normalized dx psi j hdx hpsi hp

/-! Small exact examples: no floating-point evaluation is involved. -/
example (i : Fin 3) :
    ∑ j, (gaussianResponse (by norm_num : 0 < 3)
      (fun k : Fin 3 => (k.val : ℝ)) 1 (by norm_num)).kernel j i = 1 := by
  apply gaussian_sum_column

example (i : Fin 2) : ∑ j, (deltaResponse 2).kernel j i = 1 :=
  (deltaResponse 2).sum_column i

example : ∑ j, (deltaResponse 2).probability 1 (fun _ => 1) j = 1 := by
  apply MeasurementResponse.sum_probability
  · norm_num
  · exact ⟨0, by norm_num⟩

example : weightedSquaredNorm 1
    ((gaussianResponse (by norm_num : 0 < 2) (fun k : Fin 2 => (k.val : ℝ))
      1 (by norm_num)).conditional 1 (fun _ => 1) 0) = 1 := by
  apply gaussian_conditional_normalized
  · norm_num
  · exact ⟨0, by norm_num⟩
  · apply gaussian_probability_pos
    · norm_num
    · exact ⟨0, by norm_num⟩

example : weightedSquaredNorm 1
    ((deltaResponse 1).conditional 1 (fun _ => 1) 0) = 1 := by
  apply MeasurementResponse.conditional_normalized
  · norm_num
  · exact ⟨0, by norm_num⟩
  · norm_num [MeasurementResponse.probability, deltaResponse,
      weightedSquaredNorm, sumSquaredMagnitudes, Fin.sum_univ_one]

end PsiZoo
