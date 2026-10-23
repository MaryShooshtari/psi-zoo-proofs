module

public import PsiZooProofs.GridInnerProduct
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.style.header false

/-! # Exact regional probability

Rectangle-sum masses as in `packages/sim-core/src/regions.ts`. Arbitrary finite
regions can include endpoints. The spatial partition uses the same strict
outer inequalities and inclusive interaction interval as the application.
-/

@[expose] public section

namespace PsiZoo

/-- Raw mass, without normalization or interpretation as a scattering coefficient. -/
noncomputable def regionProbability {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (s : Finset (Fin n)) : ℝ :=
  dx * ∑ i ∈ s, Complex.normSq (psi i)

theorem regionProbability_nonneg {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (s : Finset (Fin n)) (hdx : 0 ≤ dx) : 0 ≤ regionProbability dx psi s := by
  exact mul_nonneg hdx (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (psi i)))

theorem regionProbability_univ {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ) :
    regionProbability dx psi Finset.univ = weightedSquaredNorm dx psi := by
  rfl

theorem regionProbability_mono {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    {s t : Finset (Fin n)} (hdx : 0 ≤ dx) (hst : s ⊆ t) :
    regionProbability dx psi s ≤ regionProbability dx psi t := by
  apply mul_le_mul_of_nonneg_left _ hdx
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => Complex.normSq_nonneg (psi i))

theorem regionProbability_le_total {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (s : Finset (Fin n)) (hdx : 0 ≤ dx) :
    regionProbability dx psi s ≤ weightedSquaredNorm dx psi := by
  exact regionProbability_mono dx psi hdx (Finset.subset_univ s)

theorem regionProbability_union {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (s t : Finset (Fin n)) (h : Disjoint s t) :
    regionProbability dx psi (s ∪ t) =
      regionProbability dx psi s + regionProbability dx psi t := by
  simp only [regionProbability, Finset.sum_union h, mul_add]

/-- Any three disjoint regions covering the grid account for all mass. -/
theorem regionProbability_partition_three {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (s t u : Finset (Fin n)) (hst : Disjoint s t) (hsu : Disjoint s u)
    (htu : Disjoint t u) (hcover : s ∪ t ∪ u = Finset.univ) :
    regionProbability dx psi s + regionProbability dx psi t + regionProbability dx psi u =
      weightedSquaredNorm dx psi := by
  rw [← regionProbability_union dx psi s t hst,
    ← regionProbability_union dx psi (s ∪ t) u (Finset.disjoint_union_left.mpr ⟨hsu, htu⟩),
    hcover, regionProbability_univ]

/-- The three-way accounting identity specialized to normalized states. -/
theorem regionProbability_partition_normalized {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (s t u : Finset (Fin n)) (hst : Disjoint s t) (hsu : Disjoint s u)
    (htu : Disjoint t u) (hcover : s ∪ t ∪ u = Finset.univ)
    (hnorm : weightedSquaredNorm dx psi = 1) :
    regionProbability dx psi s + regionProbability dx psi t + regionProbability dx psi u = 1 := by
  rw [regionProbability_partition_three dx psi s t u hst hsu htu hcover, hnorm]

/-- Ordered cuts induce exactly the application's left / interaction / right partition.
Coordinates need not be uniformly spaced for this accounting theorem. -/
theorem spatial_region_partition {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) (hab : a ≤ b) :
    let s := Finset.univ.filter (fun i => x i < a)
    let t := Finset.univ.filter (fun i => a ≤ x i ∧ x i ≤ b)
    let u := Finset.univ.filter (fun i => b < x i)
    Disjoint s t ∧ Disjoint s u ∧ Disjoint t u ∧ s ∪ t ∪ u = Finset.univ := by
  classical
  dsimp
  simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.ext_iff, Finset.mem_union]
  constructor
  · intro i hi hj
    exact (not_lt_of_ge hj.1) hi
  constructor
  · intro i hi hj
    exact (not_lt_of_ge (hab.trans (le_of_lt hj))) hi
  constructor
  · intro i hi hj
    exact (not_lt_of_ge hi.2) hj
  intro i
  constructor
  · intro _; trivial
  · intro _
    by_cases h : x i < a
    · exact Or.inl (Or.inl h)
    by_cases h' : b < x i
    · exact Or.inr h'
    exact Or.inl (Or.inr ⟨le_of_not_gt h, le_of_not_gt h'⟩)

/-- Direct accounting for the exact strict/inclusive cuts used by regions.ts. -/
theorem spatial_region_probability_sum {n : ℕ} (dx : ℝ) (psi : Fin n → ℂ)
    (x : Fin n → ℝ) (a b : ℝ) (hab : a ≤ b) :
    regionProbability dx psi (Finset.univ.filter (fun i => x i < a)) +
      regionProbability dx psi (Finset.univ.filter (fun i => a ≤ x i ∧ x i ≤ b)) +
      regionProbability dx psi (Finset.univ.filter (fun i => b < x i)) =
        weightedSquaredNorm dx psi := by
  obtain ⟨hst, hsu, htu, hcover⟩ := spatial_region_partition x a b hab
  exact regionProbability_partition_three dx psi _ _ _ hst hsu htu hcover

/-- Arbitrarily many pairwise disjoint regions account for their union's mass. -/
theorem regionProbability_partition {n : ℕ} {κ : Type*}
    (dx : ℝ) (psi : Fin n → ℂ) (labels : Finset κ) (regions : κ → Finset (Fin n))
    (hdisj : (↑labels : Set κ).PairwiseDisjoint regions) :
    ∑ k ∈ labels, regionProbability dx psi (regions k) =
      regionProbability dx psi (labels.biUnion regions) := by
  unfold regionProbability
  rw [← Finset.mul_sum, Finset.sum_biUnion hdisj]

/-- Finite partition accounting for a normalized state. -/
theorem regionProbability_partition_sum_one {n : ℕ} {κ : Type*}
    (dx : ℝ) (psi : Fin n → ℂ) (labels : Finset κ) (regions : κ → Finset (Fin n))
    (hdisj : (↑labels : Set κ).PairwiseDisjoint regions)
    (hcover : labels.biUnion regions = Finset.univ) (hnorm : weightedSquaredNorm dx psi = 1) :
    ∑ k ∈ labels, regionProbability dx psi (regions k) = 1 := by
  rw [regionProbability_partition dx psi labels regions hdisj, hcover,
    regionProbability_univ, hnorm]

end PsiZoo
