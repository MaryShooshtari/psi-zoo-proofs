module

public import PsiZooProofs.Normalization

set_option linter.style.header false

/-!
# Normalization on a uniformly spaced finite grid

The discrete spatial squared norm is `dx` times the existing sum of squared
coordinate magnitudes. Normalization requires positive spacing and a nonzero
state. This is an exact finite-dimensional statement, not a quadrature error
estimate or a claim about floating-point execution.
-/

@[expose] public section

namespace PsiZoo

/-- The discrete spatial squared norm for uniform grid spacing `dx`. -/
noncomputable def weightedSquaredNorm {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ) : ℝ :=
  dx * sumSquaredMagnitudes psi

/-- Positive spacing and a nonzero coordinate give a positive weighted norm. -/
theorem weightedSquaredNorm_pos {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) :
    0 < weightedSquaredNorm dx psi := by
  exact mul_pos hdx (sumSquaredMagnitudes_pos psi hpsi)

/-- Normalize with respect to the discrete spatial squared norm.
Both positive spacing and a nonzero state are required. -/
noncomputable def normalizeGridState {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (_hdx : 0 < dx) (_hpsi : ∃ i, psi i ≠ 0) : Fin n → ℂ :=
  fun i => psi i / (Real.sqrt (weightedSquaredNorm dx psi) : ℂ)

/-- The squared magnitude of each normalized grid coordinate. -/
theorem normSq_normalizeGridState_apply {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) (i : Fin n) :
    Complex.normSq (normalizeGridState dx psi hdx hpsi i) =
      Complex.normSq (psi i) / weightedSquaredNorm dx psi := by
  unfold normalizeGridState
  rw [Complex.normSq_div, Complex.normSq_ofReal,
    Real.mul_self_sqrt (le_of_lt (weightedSquaredNorm_pos dx psi hdx hpsi))]

/-- A normalized nonzero grid state has discrete spatial squared norm one. -/
theorem weightedSquaredNorm_normalizeGridState {n : ℕ} (dx : ℝ)
    (psi : Fin n → ℂ) (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0) :
    weightedSquaredNorm dx (normalizeGridState dx psi hdx hpsi) = 1 := by
  have hpos := weightedSquaredNorm_pos dx psi hdx hpsi
  change dx * (∑ i, Complex.normSq (normalizeGridState dx psi hdx hpsi i)) = 1
  simp_rw [normSq_normalizeGridState_apply]
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_self (ne_of_gt hpos)

/-- Zero coordinates, including any prescribed Dirichlet boundary coordinates,
remain zero after grid normalization. -/
theorem normalizeGridState_eq_zero_of_eq_zero {n : ℕ} (dx : ℝ)
    (psi : Fin n → ℂ) (hdx : 0 < dx) (hpsi : ∃ i, psi i ≠ 0)
    (i : Fin n) (hi : psi i = 0) :
    normalizeGridState dx psi hdx hpsi i = 0 := by
  unfold normalizeGridState
  rw [hi, zero_div]

end PsiZoo
