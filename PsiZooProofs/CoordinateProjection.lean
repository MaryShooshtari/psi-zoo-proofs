module

public import PsiZooProofs.RegionProbability

set_option linter.style.header false

/-! # Exact coordinate projection

Retain precisely the coordinates in a finite region. This sharp projection
is not a Gaussian localization mask. No measurement outcome is chosen here.
-/

@[expose] public section

namespace PsiZoo

/-- Set coordinates outside s to zero, without automatic renormalization. -/
noncomputable def coordinateProjection {n : ℕ} (s : Finset (Fin n))
    (psi : Fin n → ℂ) : Fin n → ℂ := fun i => if i ∈ s then psi i else 0

theorem coordinateProjection_idempotent {n : ℕ} (s : Finset (Fin n)) (psi : Fin n → ℂ) :
    coordinateProjection s (coordinateProjection s psi) = coordinateProjection s psi := by
  funext i
  by_cases hi : i ∈ s <;> simp [coordinateProjection, hi]

theorem coordinateProjection_selfAdjoint {n : ℕ} (s : Finset (Fin n)) (dx : ℝ)
    (phi psi : Fin n → ℂ) :
    gridInnerProduct dx (coordinateProjection s phi) psi =
      gridInnerProduct dx phi (coordinateProjection s psi) := by
  unfold gridInnerProduct
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [coordinateProjection, hi]

theorem coordinateProjection_mass {n : ℕ} (s : Finset (Fin n)) (dx : ℝ)
    (psi : Fin n → ℂ) :
    weightedSquaredNorm dx (coordinateProjection s psi) = regionProbability dx psi s := by
  unfold weightedSquaredNorm sumSquaredMagnitudes regionProbability
  congr 1
  calc
    _ = ∑ i : Fin n, if i ∈ s then Complex.normSq (psi i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [coordinateProjection, hi]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem coordinateProjection_mass_le {n : ℕ} (s : Finset (Fin n)) (dx : ℝ)
    (psi : Fin n → ℂ) (hdx : 0 ≤ dx) :
    weightedSquaredNorm dx (coordinateProjection s psi) ≤ weightedSquaredNorm dx psi := by
  rw [coordinateProjection_mass]
  exact regionProbability_le_total dx psi s hdx

/-- The retained and discarded coordinates account for all mass exactly. -/
theorem coordinateProjection_pythagoras {n : ℕ} (s : Finset (Fin n)) (dx : ℝ)
    (psi : Fin n → ℂ) :
    weightedSquaredNorm dx (coordinateProjection s psi) +
      weightedSquaredNorm dx (coordinateProjection sᶜ psi) = weightedSquaredNorm dx psi := by
  rw [coordinateProjection_mass, coordinateProjection_mass,
    ← regionProbability_union dx psi s sᶜ disjoint_compl_right,
    Finset.union_compl, regionProbability_univ]

/-- Positive retained probability supplies the nonzero witness required for normalization. -/
theorem coordinateProjection_nonzero_of_mass_pos {n : ℕ} (s : Finset (Fin n)) (dx : ℝ)
    (psi : Fin n → ℂ) (hmass : 0 < regionProbability dx psi s) :
    ∃ i, coordinateProjection s psi i ≠ 0 := by
  by_contra h
  push Not at h
  have hz : weightedSquaredNorm dx (coordinateProjection s psi) = 0 := by
    simp [weightedSquaredNorm, sumSquaredMagnitudes, h]
  rw [coordinateProjection_mass] at hz
  exact (ne_of_gt hmass) hz

/-- Conditional on a nonzero outcome, exact projection followed by normalization
has unit probability. This does not assert a stochastic sampling algorithm. -/
theorem normalize_coordinateProjection {n : ℕ} (s : Finset (Fin n)) (dx : ℝ)
    (psi : Fin n → ℂ) (hdx : 0 < dx) (hmass : 0 < regionProbability dx psi s) :
    weightedSquaredNorm dx
      (normalizeGridState dx (coordinateProjection s psi) hdx
        (coordinateProjection_nonzero_of_mass_pos s dx psi hmass)) = 1 := by
  exact weightedSquaredNorm_normalizeGridState _ _ _ _

end PsiZoo
