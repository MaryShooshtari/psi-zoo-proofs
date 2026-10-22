module

public import PsiZooProofs.CrankNicolsonEvolution
public import Mathlib.LinearAlgebra.UnitaryGroup

set_option linter.style.header false

/-!
# Unitarity of exact Crank–Nicolson evolution

For the existing Hermitian interior Dirichlet Hamiltonian, Aᴴ = B and Bᴴ = A.
Taking the adjoint of A U = B gives Uᴴ B = A. Together these equations imply
Uᴴ (A + B) U = A + B. Since A + B = 2 I, scalar cancellation gives Uᴴ U = I.
Finite square matrix algebra supplies U Uᴴ = I and unitary-group membership.

The results hold for all real time steps, positive spacing, and fixed real
potentials, including dimensions zero and one. They concern exact complex
matrices, not the floating-point Thomas solver or rounding errors.
-/

@[expose] public section

open scoped Matrix

namespace PsiZoo

/-- Hermiticity of H and reality of dt exchange the two step matrices under adjoint. -/
theorem crankNicolsonLeftMatrix_conjTranspose {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) :
    (crankNicolsonLeftMatrix dx dt V)ᴴ = crankNicolsonRightMatrix dx dt V := by
  simp [crankNicolsonLeftMatrix, crankNicolsonRightMatrix,
    (gridHamiltonianMatrix_isHermitian dx V).eq, sub_eq_add_neg]

/-- The reverse adjoint relation follows by involutivity of conjugate transpose. -/
theorem crankNicolsonRightMatrix_conjTranspose {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) :
    (crankNicolsonRightMatrix dx dt V)ᴴ = crankNicolsonLeftMatrix dx dt V := by
  rw [← crankNicolsonLeftMatrix_conjTranspose dx dt V,
    Matrix.conjTranspose_conjTranspose]

/-- The Hamiltonian terms cancel in the sum A + B = 2 I. -/
theorem crankNicolsonLeftMatrix_add_rightMatrix {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) :
    crankNicolsonLeftMatrix dx dt V + crankNicolsonRightMatrix dx dt V =
      (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [crankNicolsonLeftMatrix, crankNicolsonRightMatrix, two_smul]
  abel

/-- Taking the adjoint of A U = B yields Uᴴ B = A. -/
theorem crankNicolsonEvolution_conjTranspose_mul_rightMatrix {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    (crankNicolsonEvolution dx dt V)ᴴ * crankNicolsonRightMatrix dx dt V =
      crankNicolsonLeftMatrix dx dt V := by
  have hadj := congrArg Matrix.conjTranspose
    (crankNicolsonLeftMatrix_mul_evolution dx dt V hdx)
  simpa only [Matrix.conjTranspose_mul, crankNicolsonLeftMatrix_conjTranspose,
    crankNicolsonRightMatrix_conjTranspose] using hadj

/-- First unitarity identity, obtained by adding the A and B identities and
cancelling the nonzero complex scalar 2. -/
theorem crankNicolsonEvolution_conjTranspose_mul_self {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    (crankNicolsonEvolution dx dt V)ᴴ * crankNicolsonEvolution dx dt V = 1 := by
  have hAU := crankNicolsonLeftMatrix_mul_evolution dx dt V hdx
  have hUB := crankNicolsonEvolution_conjTranspose_mul_rightMatrix dx dt V hdx
  have hA : (crankNicolsonEvolution dx dt V)ᴴ * crankNicolsonLeftMatrix dx dt V *
      crankNicolsonEvolution dx dt V = crankNicolsonLeftMatrix dx dt V := by
    rw [Matrix.mul_assoc, hAU, hUB]
  have hB : (crankNicolsonEvolution dx dt V)ᴴ * crankNicolsonRightMatrix dx dt V *
      crankNicolsonEvolution dx dt V = crankNicolsonRightMatrix dx dt V := by
    rw [hUB, hAU]
  have hsum : (crankNicolsonEvolution dx dt V)ᴴ *
      (crankNicolsonLeftMatrix dx dt V + crankNicolsonRightMatrix dx dt V) *
      crankNicolsonEvolution dx dt V =
        crankNicolsonLeftMatrix dx dt V + crankNicolsonRightMatrix dx dt V := by
    rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
  rw [crankNicolsonLeftMatrix_add_rightMatrix] at hsum
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hsum
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hsum
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hij

/-- For finite square matrices, a left inverse is also a right inverse. -/
theorem crankNicolsonEvolution_mul_conjTranspose_self {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    crankNicolsonEvolution dx dt V * (crankNicolsonEvolution dx dt V)ᴴ = 1 := by
  exact mul_eq_one_comm.mp
    (crankNicolsonEvolution_conjTranspose_mul_self dx dt V hdx)

/-- The exact Crank–Nicolson evolution matrix belongs to the complex unitary group. -/
theorem crankNicolsonEvolution_mem_unitaryGroup {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    crankNicolsonEvolution dx dt V ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  exact crankNicolsonEvolution_conjTranspose_mul_self dx dt V hdx

/-- The nonsingular matrix inverse of evolution is its conjugate transpose. -/
theorem crankNicolsonEvolution_inv_eq_conjTranspose {n : ℕ} (dx dt : ℝ)
    (V : Fin n → ℝ) (hdx : 0 < dx) :
    (crankNicolsonEvolution dx dt V)⁻¹ = (crankNicolsonEvolution dx dt V)ᴴ := by
  exact Matrix.inv_eq_left_inv
    (crankNicolsonEvolution_conjTranspose_mul_self dx dt V hdx)

end PsiZoo
