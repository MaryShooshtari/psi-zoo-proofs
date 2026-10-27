module

public import PsiZooProofs.Qubit
public import PsiZooProofs.HermitianCayley
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option linter.style.header false

/-! Unitarity of the genuine matrix exponential. Its equality to the closed
trigonometric formula in Qubit.lean remains a separate proof obligation. -/
@[expose] public section
namespace PsiZoo
open scoped ComplexConjugate

/-- Exact exponential propagator, not the CN rational approximation. -/
noncomputable def schrodingerExponential {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)

/-- The exponential of -itH is unitary for every finite Hermitian H. -/
theorem schrodingerExponential_adjoint_mul {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (schrodingerExponential H t).conjTranspose * schrodingerExponential H t = 1 := by
  have hskew : ((-Complex.I * (t : ℂ)) • H).conjTranspose =
      -((-Complex.I * (t : ℂ)) • H) := by
    rw [Matrix.conjTranspose_smul, hH.eq]
    simp [neg_smul]
  unfold schrodingerExponential
  rw [← Matrix.exp_conjTranspose, hskew,
    ← Matrix.exp_add_of_commute _ _
      (Commute.refl ((-Complex.I * (t : ℂ)) • H)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

theorem schrodingerExponential_mem_unitaryGroup {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    schrodingerExponential H t ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  exact Matrix.mem_unitaryGroup_iff.mpr
    (mul_eq_one_comm.mp (schrodingerExponential_adjoint_mul H hH t))

theorem schrodingerExponential_norm {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) (ψ : Fin n → ℂ) :
    weightedSquaredNorm 1 ((schrodingerExponential H t).mulVec ψ) =
      weightedSquaredNorm 1 ψ := by
  have h := gridInnerProduct_unitary _ (schrodingerExponential_adjoint_mul H hH t) 1 ψ ψ
  rw [gridInnerProduct_self, gridInnerProduct_self] at h
  exact Complex.ofReal_injective h

/-- The qubit exponential preserves the unweighted sum |α|²+|β|²,
including zero field/time. No normalization hypothesis is needed. -/
theorem qubit_exponential_norm (ax ay az t : ℝ) (α β : ℂ) :
    let q := (schrodingerExponential (qubitHamiltonian ax ay az) t).mulVec ![α, β]
    qubitNorm (q 0) (q 1) = qubitNorm α β := by
  have h := schrodingerExponential_norm _ (qubitHamiltonian_isHermitian ax ay az) t ![α, β]
  simpa [weightedSquaredNorm, sumSquaredMagnitudes, Fin.sum_univ_two, qubitNorm] using h

end PsiZoo
