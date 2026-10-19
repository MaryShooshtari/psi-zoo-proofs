module

public import Mathlib.Analysis.Complex.Norm

-- No author/copyright attribution is asserted for this introductory file.
set_option linter.style.header false

/-!
# Squared magnitudes of finite complex coordinate vectors

`Complex.normSq z` is the real number `z.re * z.re + z.im * z.im`.
We use an explicit finite sum of these quantities as a starting point for
quantum state normalization. We do not identify it with the default norm on
`Fin n → ℂ`, nor establish a Euclidean-space norm instance here.
-/

@[expose] public section

open scoped ComplexConjugate

namespace PsiZoo

/-- Multiplying the conjugate of z by z gives its squared magnitude,
viewed as a complex number with zero imaginary part. -/
theorem conj_mul_self (z : ℂ) : conj z * z = (Complex.normSq z : ℂ) := by
  exact Complex.normSq_eq_conj_mul_self.symm

/-- Conjugation changes the sign of the imaginary part, not the squared magnitude. -/
theorem normSq_conjugate (z : ℂ) : Complex.normSq (conj z) = Complex.normSq z := by
  exact Complex.normSq_conj z

/-- An explicit real-valued sum, not an assertion about the default function-space norm. -/
noncomputable def sumSquaredMagnitudes {n : ℕ} (v : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

/-- The sum of squared coordinate magnitudes is nonnegative because each term is. -/
theorem sumSquaredMagnitudes_nonneg {n : ℕ} (v : Fin n → ℂ) :
    0 ≤ sumSquaredMagnitudes v := by
  apply Finset.sum_nonneg
  intro i _
  exact Complex.normSq_nonneg (v i)

/-- This sum vanishes exactly when every coordinate vanishes:
nonnegative terms cannot cancel one another. This also holds in dimension zero. -/
theorem sumSquaredMagnitudes_eq_zero_iff {n : ℕ} (v : Fin n → ℂ) :
    sumSquaredMagnitudes v = 0 ↔ ∀ i, v i = 0 := by
  unfold sumSquaredMagnitudes
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))]
  simp only [Finset.mem_univ, forall_const, Complex.normSq_eq_zero]

end PsiZoo
