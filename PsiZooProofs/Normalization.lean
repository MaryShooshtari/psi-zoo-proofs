module

public import PsiZooProofs.ComplexBasics
public import Mathlib.Algebra.BigOperators.Field

set_option linter.style.header false

/-!
# Normalization of finite complex states

Normalization uses the unweighted sum of squared coordinate magnitudes, not
an integral or the default norm on the function space. A nonzero coordinate
is required, so the zero state cannot be supplied to `normalizeState`.
-/

@[expose] public section

namespace PsiZoo

/-- A state with a nonzero coordinate has strictly positive squared norm. -/
theorem sumSquaredMagnitudes_pos {n : ℕ} (psi : Fin n → ℂ)
    (hpsi : ∃ i, psi i ≠ 0) : 0 < sumSquaredMagnitudes psi := by
  apply lt_of_le_of_ne (sumSquaredMagnitudes_nonneg psi)
  intro hzero
  obtain ⟨i, hi⟩ := hpsi
  exact hi ((sumSquaredMagnitudes_eq_zero_iff psi).mp hzero.symm i)

/-- Divide every coordinate by the positive real square root of the squared norm.
The witness excludes the zero state (also in dimension zero). -/
noncomputable def normalizeState {n : ℕ} (psi : Fin n → ℂ)
    (_hpsi : ∃ i, psi i ≠ 0) : Fin n → ℂ :=
  fun i => psi i / (Real.sqrt (sumSquaredMagnitudes psi) : ℂ)

/-- Each normalized coordinate has its original squared magnitude divided by
 the total squared magnitude. -/
theorem normSq_normalizeState_apply {n : ℕ} (psi : Fin n → ℂ)
    (hpsi : ∃ i, psi i ≠ 0) (i : Fin n) :
    Complex.normSq (normalizeState psi hpsi i) =
      Complex.normSq (psi i) / sumSquaredMagnitudes psi := by
  unfold normalizeState
  rw [Complex.normSq_div, Complex.normSq_ofReal,
    Real.mul_self_sqrt (sumSquaredMagnitudes_nonneg psi)]

/-- Normalizing a nonzero finite complex state gives squared norm one. -/
theorem sumSquaredMagnitudes_normalizeState {n : ℕ} (psi : Fin n → ℂ)
    (hpsi : ∃ i, psi i ≠ 0) :
    sumSquaredMagnitudes (normalizeState psi hpsi) = 1 := by
  have hpos : 0 < sumSquaredMagnitudes psi := sumSquaredMagnitudes_pos psi hpsi
  unfold sumSquaredMagnitudes
  simp_rw [normSq_normalizeState_apply]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

end PsiZoo
