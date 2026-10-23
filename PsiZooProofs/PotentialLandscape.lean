module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-! # Gaussian barriers and maximum painting

Exact real counterparts of `packages/sim-core/src/potential.ts`.
The API checks positive width; the bounds below even hold for Lean's totalized
real division at width zero. No claim is made about floating-point overflow.
-/

@[expose] public section

namespace PsiZoo

/-- A Gaussian barrier with amplitude A, center c, and width sigma. -/
noncomputable def gaussianBarrier (A c sigma x : ℝ) : ℝ :=
  A * Real.exp (-( ((x - c) / sigma) ^ 2) / 2)

theorem gaussianBarrier_nonneg (A c sigma x : ℝ) (hA : 0 ≤ A) :
    0 ≤ gaussianBarrier A c sigma x := by
  exact mul_nonneg hA (Real.exp_pos _).le

theorem gaussianBarrier_le_amplitude (A c sigma x : ℝ) (hA : 0 ≤ A) :
    gaussianBarrier A c sigma x ≤ A := by
  unfold gaussianBarrier
  have hexp : Real.exp (-(((x - c) / sigma) ^ 2) / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
  simpa using mul_le_mul_of_nonneg_left hexp hA

theorem gaussianBarrier_center (A c sigma : ℝ) : gaussianBarrier A c sigma c = A := by
  simp [gaussianBarrier]

/-- This is a continuous-profile maximum; an off-grid center need not be sampled. -/
theorem gaussianBarrier_max_at_center (A c sigma x : ℝ) (hA : 0 ≤ A) :
    gaussianBarrier A c sigma x ≤ gaussianBarrier A c sigma c := by
  rw [gaussianBarrier_center]
  exact gaussianBarrier_le_amplitude A c sigma x hA

/-- Pointwise maximum stamp; it does not add two barriers. -/
noncomputable def stampPotential {ι : Type*} (V W : ι → ℝ) : ι → ℝ :=
  fun i => max (V i) (W i)

theorem stampPotential_increases {ι : Type*} (V W : ι → ℝ) : V ≤ stampPotential V W := by
  intro i
  exact le_max_left _ _

theorem stampPotential_idempotent {ι : Type*} (V W : ι → ℝ) :
    stampPotential (stampPotential V W) W = stampPotential V W := by
  funext i
  exact max_eq_left (le_max_right (V i) (W i))

theorem stampPotential_order_independent {ι : Type*} (V W Z : ι → ℝ) :
    stampPotential (stampPotential V W) Z = stampPotential (stampPotential V Z) W := by
  funext i
  exact max_right_comm _ _ _

/-- The application's validated cap contract: max preserves the interval [0,M]. -/
theorem stampPotential_bounds {ι : Type*} (V W : ι → ℝ) (M : ℝ)
    (hV : ∀ i, 0 ≤ V i ∧ V i ≤ M) (hW : ∀ i, 0 ≤ W i ∧ W i ≤ M) :
    ∀ i, 0 ≤ stampPotential V W i ∧ stampPotential V W i ≤ M := by
  intro i
  exact ⟨(hV i).1.trans (le_max_left _ _), max_le (hV i).2 (hW i).2⟩

/-- Explicit clipping is distinct from the app's reject-invalid-input contract. -/
noncomputable def cappedStampPotential {ι : Type*} (M : ℝ) (V W : ι → ℝ) : ι → ℝ :=
  fun i => min M (max (V i) (W i))

theorem cappedStampPotential_bounds {ι : Type*} (M : ℝ) (V W : ι → ℝ)
    (hM : 0 ≤ M) (hV : ∀ i, 0 ≤ V i) :
    ∀ i, 0 ≤ cappedStampPotential M V W i ∧ cappedStampPotential M V W i ≤ M := by
  intro i
  exact ⟨le_min hM ((hV i).trans (le_max_left _ _)), min_le_left _ _⟩

theorem cappedStampPotential_eq_stamp {ι : Type*} (M : ℝ) (V W : ι → ℝ)
    (hV : ∀ i, V i ≤ M) (hW : ∀ i, W i ≤ M) :
    cappedStampPotential M V W = stampPotential V W := by
  funext i
  exact min_eq_right (max_le (hV i) (hW i))

/-- Folding any finite sequence of bounded stamps preserves the cap contract. -/
theorem stampPotential_fold_bounds {ι : Type*} (profiles : List (ι → ℝ))
    (V : ι → ℝ) (M : ℝ) (hV : ∀ i, 0 ≤ V i ∧ V i ≤ M)
    (hprofiles : ∀ W ∈ profiles, ∀ i, 0 ≤ W i ∧ W i ≤ M) :
    ∀ i, 0 ≤ profiles.foldl stampPotential V i ∧ profiles.foldl stampPotential V i ≤ M := by
  induction profiles generalizing V with
  | nil => exact hV
  | cons W rest ih =>
    apply ih (stampPotential V W)
    · exact stampPotential_bounds V W M hV (hprofiles W (by simp))
    · intro Z hZ
      exact hprofiles Z (by simp [hZ])

end PsiZoo
