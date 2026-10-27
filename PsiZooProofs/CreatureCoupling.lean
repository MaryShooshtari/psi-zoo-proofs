module

public import PsiZooProofs.Qubit
public import PsiZooProofs.HamiltonianStructure
public import PsiZooProofs.CrankNicolsonEvolution

set_option linter.style.header false

/-! Exact mood and frozen-density mean-field potentials. Spatial states are
interior Dirichlet coordinates, not a joint two-creature quantum state. -/
@[expose] public section
namespace PsiZoo

noncomputable def moodForce (F0 rz : ℝ) : ℝ := F0 * rz
noncomputable def moodPotential (F0 rz xRef x : ℝ) : ℝ := -moodForce F0 rz * (x - xRef)

theorem moodPotential_im (F0 rz xRef x : ℝ) :
    (moodPotential F0 rz xRef x : ℂ).im = 0 := by
  exact Complex.ofReal_im _

theorem moodForce_reverse (F0 rz : ℝ) : moodForce F0 (-rz) = -moodForce F0 rz := by
  simp [moodForce]

theorem moodPotential_reverse (F0 rz xRef x : ℝ) :
    moodPotential F0 (-rz) xRef x = -moodPotential F0 rz xRef x := by
  simp [moodPotential, moodForce]

theorem moodPotential_isHermitian {n : ℕ} (F0 rz xRef : ℝ) (x : Fin n → ℝ) :
    (realPotentialMatrix (fun i => moodPotential F0 rz xRef (x i))).IsHermitian := by
  exact realPotentialMatrix_isHermitian _

/-- Terrain is additive; rz may be the Bloch coordinate sampled at any fixed time. -/
theorem mood_cn_norm {n : ℕ} (dx dt F0 rz xRef : ℝ) (hdx : 0 < dx)
    (x terrain : Fin n → ℝ) (ψ : Fin n → ℂ) :
    weightedSquaredNorm dx
      ((crankNicolsonEvolution dx dt
        (fun i => terrain i + moodPotential F0 rz xRef (x i))).mulVec ψ) =
      weightedSquaredNorm dx ψ := by
  exact crankNicolsonEvolution_weightedSquaredNorm dx dt _ hdx ψ

/-- Density, not probability mass: no dx factor. -/
noncomputable def probabilityDensity {n : ℕ} (ψ : Fin n → ℂ) (i : Fin n) : ℝ :=
  Complex.normSq (ψ i)

noncomputable def contactPotential {n : ℕ} (g : ℝ) (partner : Fin n → ℂ) : Fin n → ℝ :=
  fun i => g * probabilityDensity partner i

noncomputable def socialPotentials {n : ℕ} (g : ℝ) (A B : Fin n → ℂ) :
    (Fin n → ℝ) × (Fin n → ℝ) := (contactPotential g B, contactPotential g A)

noncomputable def interactionEnergy {n : ℕ} (g dx : ℝ) (A B : Fin n → ℂ) : ℝ :=
  g * dx * ∑ i, probabilityDensity A i * probabilityDensity B i

theorem probabilityDensity_nonneg {n : ℕ} (ψ : Fin n → ℂ) (i : Fin n) :
    0 ≤ probabilityDensity ψ i := by
  exact Complex.normSq_nonneg _

theorem contactPotential_im {n : ℕ} (g : ℝ) (ψ : Fin n → ℂ) (i : Fin n) :
    (contactPotential g ψ i : ℂ).im = 0 := by
  exact Complex.ofReal_im _

theorem socialPotentials_exchange {n : ℕ} (g : ℝ) (A B : Fin n → ℂ) :
    socialPotentials g B A = (socialPotentials g A B).swap := by
  rfl

theorem interactionEnergy_exchange {n : ℕ} (g dx : ℝ) (A B : Fin n → ℂ) :
    interactionEnergy g dx A B = interactionEnergy g dx B A := by
  simp only [interactionEnergy, mul_comm (probabilityDensity A _) (probabilityDensity B _)]

theorem contactPotential_isHermitian {n : ℕ} (g : ℝ) (ψ : Fin n → ℂ) :
    (realPotentialMatrix (contactPotential g ψ)).IsHermitian := by
  exact realPotentialMatrix_isHermitian _

/-- Both old densities are frozen. The extra real potentials can include terrain
and independently sampled midpoint mood. No nonlinear energy law is asserted. -/
theorem social_cn_norms {n : ℕ} (dx dt g : ℝ) (hdx : 0 < dx)
    (A B : Fin n → ℂ) (extraA extraB : Fin n → ℝ) :
    weightedSquaredNorm dx
      ((crankNicolsonEvolution dx dt (extraA + contactPotential g B)).mulVec A) =
        weightedSquaredNorm dx A ∧
    weightedSquaredNorm dx
      ((crankNicolsonEvolution dx dt (extraB + contactPotential g A)).mulVec B) =
        weightedSquaredNorm dx B := by
  constructor
  · exact crankNicolsonEvolution_weightedSquaredNorm dx dt _ hdx A
  · exact crankNicolsonEvolution_weightedSquaredNorm dx dt _ hdx B

end PsiZoo
