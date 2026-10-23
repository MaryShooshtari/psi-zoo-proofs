module

public import PsiZooProofs.CrankNicolsonUnitarity

set_option linter.style.header false

/-! # Cayley evolution for an arbitrary finite Hermitian Hamiltonian

No finite-difference, spacing, or potential assumptions enter these results.
`t` is the real half timestep. The coordinate dimension is arbitrary, including zero.
-/

@[expose] public section

open scoped Matrix ComplexConjugate

namespace PsiZoo

/-- Self-adjointness for the explicit grid inner product, for any real weight. -/
theorem hermitian_gridInnerProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (dx : ℝ) (phi psi : Fin n → ℂ) :
    gridInnerProduct dx phi (H.mulVec psi) = gridInnerProduct dx (H.mulVec phi) psi := by
  unfold gridInnerProduct
  apply congrArg (fun z : ℂ => (dx : ℂ) * z)
  simp only [Matrix.mulVec_apply_eq_sum, map_sum, map_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : conj (H i j) = H j i := congrFun (congrFun hH.eq j) i
  rw [hij]
  ring

theorem hermitian_energy_im_eq_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (dx : ℝ) (psi : Fin n → ℂ) :
    (gridInnerProduct dx psi (H.mulVec psi)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← gridInnerProduct_conj_symm, ← hermitian_gridInnerProduct H hH]

noncomputable def cayleyLeft {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
  1 + (Complex.I * (t : ℂ)) • H

noncomputable def cayleyRight {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
  1 - (Complex.I * (t : ℂ)) • H

/-- Exact inverse-based Cayley transform, with invertibility proved below. -/
noncomputable def hermitianCayley {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
  (cayleyLeft H t)⁻¹ * cayleyRight H t

/-- A solution of the implicit Cayley equation preserves the weighted squared norm. -/
theorem cayley_step_norm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t dx : ℝ) (psi chi : Fin n → ℂ)
    (hstep : (cayleyLeft H t).mulVec chi = (cayleyRight H t).mulVec psi) :
    weightedSquaredNorm dx chi = weightedSquaredNorm dx psi := by
  have hdiff : chi - psi = (-Complex.I * (t : ℂ)) • H.mulVec (chi + psi) := by
    simp only [cayleyLeft, cayleyRight, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec] at hstep
    rw [Matrix.mulVec_add]
    ext i
    have hi := congrFun hstep i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  have he := hermitian_energy_im_eq_zero H hH dx (chi + psi)
  apply sub_eq_zero.mp
  rw [weightedSquaredNorm_sub_eq_re_gridInnerProduct, hdiff, gridInnerProduct_smul_right]
  simp [Complex.mul_re, Complex.mul_im, he]

/-- No inverse assumption is needed: Hermiticity forces the left kernel to vanish. -/
theorem cayleyLeft_isUnit {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) : IsUnit (cayleyLeft H t) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro psi chi heq
  have hk : (cayleyLeft H t).mulVec (psi - chi) = (cayleyRight H t).mulVec 0 := by
    rw [Matrix.mulVec_sub, heq, sub_self, Matrix.mulVec_zero]
  have hn := cayley_step_norm H hH t 1 0 (psi - chi) hk
  have hz : weightedSquaredNorm 1 (psi - chi) = 0 := by
    simpa [weightedSquaredNorm, sumSquaredMagnitudes] using hn
  apply sub_eq_zero.mp
  ext i
  exact (sumSquaredMagnitudes_eq_zero_iff (psi - chi)).mp
    (by simpa [weightedSquaredNorm] using hz) i

theorem cayleyLeft_mul_cayley {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) : cayleyLeft H t * hermitianCayley H t = cayleyRight H t := by
  exact Matrix.mul_nonsing_inv_cancel_left _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (cayleyLeft_isUnit H hH t))

theorem cayleyLeft_adjoint {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) : (cayleyLeft H t)ᴴ = cayleyRight H t := by
  simp [cayleyLeft, cayleyRight, hH.eq, sub_eq_add_neg]

theorem hermitianCayley_conjTranspose_mul_self {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) : (hermitianCayley H t)ᴴ * hermitianCayley H t = 1 := by
  have hAU := cayleyLeft_mul_cayley H hH t
  have hBA : (cayleyRight H t)ᴴ = cayleyLeft H t := by
    rw [← cayleyLeft_adjoint H hH t, Matrix.conjTranspose_conjTranspose]
  have hUB : (hermitianCayley H t)ᴴ * cayleyRight H t = cayleyLeft H t := by
    simpa only [Matrix.conjTranspose_mul, cayleyLeft_adjoint H hH t, hBA] using
      congrArg Matrix.conjTranspose hAU
  have hA : (hermitianCayley H t)ᴴ * cayleyLeft H t * hermitianCayley H t = cayleyLeft H t := by
    rw [Matrix.mul_assoc, hAU, hUB]
  have hB : (hermitianCayley H t)ᴴ * cayleyRight H t * hermitianCayley H t = cayleyRight H t := by
    rw [hUB, hAU]
  have hs : cayleyLeft H t + cayleyRight H t = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [cayleyLeft, cayleyRight, two_smul]
    abel
  have he : (hermitianCayley H t)ᴴ * (cayleyLeft H t + cayleyRight H t) * hermitianCayley H t =
      cayleyLeft H t + cayleyRight H t := by
    rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
  rw [hs] at he
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at he
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) he
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hij

/-- The general Hermitian Cayley transform is unitary, with no assumed inverse. -/
theorem hermitianCayley_mem_unitaryGroup {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) : hermitianCayley H t ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  exact Matrix.mem_unitaryGroup_iff'.mpr (hermitianCayley_conjTranspose_mul_self H hH t)

theorem hermitianCayley_weightedSquaredNorm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t dx : ℝ) (psi : Fin n → ℂ) :
    weightedSquaredNorm dx ((hermitianCayley H t).mulVec psi) = weightedSquaredNorm dx psi := by
  apply cayley_step_norm H hH t dx
  rw [Matrix.mulVec_mulVec, cayleyLeft_mul_cayley H hH t]

/-- Moving a matrix across the inner product takes its conjugate transpose. -/
theorem gridInnerProduct_mulVec_adjoint {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (dx : ℝ) (phi psi : Fin n → ℂ) :
    gridInnerProduct dx (M.mulVec phi) psi = gridInnerProduct dx phi (Mᴴ.mulVec psi) := by
  unfold gridInnerProduct
  apply congrArg (fun z : ℂ => (dx : ℂ) * z)
  simp only [Matrix.mulVec_apply_eq_sum, map_sum, map_mul, Matrix.conjTranspose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change conj (M j i) * conj (phi i) * psi j = conj (phi i) * (conj (M j i) * psi j)
  ring

/-- Unitary matrices preserve the entire weighted inner product, not only its diagonal. -/
theorem gridInnerProduct_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (dx : ℝ) (phi psi : Fin n → ℂ) :
    gridInnerProduct dx (U.mulVec phi) (U.mulVec psi) = gridInnerProduct dx phi psi := by
  rw [gridInnerProduct_mulVec_adjoint, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/-- The Cayley transform commutes with the fixed Hamiltonian. -/
theorem hermitianCayley_commute {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    hermitianCayley H t * H = H * hermitianCayley H t := by
  have hA : cayleyLeft H t * H = H * cayleyLeft H t := by
    simp [cayleyLeft, Matrix.add_mul, Matrix.mul_add]
  have hB : cayleyRight H t * H = H * cayleyRight H t := by
    simp [cayleyRight, Matrix.sub_mul, Matrix.mul_sub]
  have he : cayleyLeft H t * (hermitianCayley H t * H) =
      cayleyLeft H t * (H * hermitianCayley H t) := by
    calc
      _ = cayleyRight H t * H := by rw [← Matrix.mul_assoc, cayleyLeft_mul_cayley H hH t]
      _ = H * cayleyRight H t := hB
      _ = _ := by rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc, cayleyLeft_mul_cayley H hH t]
  have hi := congrArg (fun M => (cayleyLeft H t)⁻¹ * M) he
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp (cayleyLeft_isUnit H hH t)
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] using hi

/-- Exact conservation of the complex energy form for a time-independent H.
No normalization is needed; the form is real by `hermitian_energy_im_eq_zero`. -/
theorem hermitianCayley_energy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t dx : ℝ) (psi : Fin n → ℂ) :
    gridInnerProduct dx ((hermitianCayley H t).mulVec psi)
      (H.mulVec ((hermitianCayley H t).mulVec psi)) = gridInnerProduct dx psi (H.mulVec psi) := by
  rw [Matrix.mulVec_mulVec, ← hermitianCayley_commute H hH t, ← Matrix.mulVec_mulVec]
  exact gridInnerProduct_unitary _
    (hermitianCayley_conjTranspose_mul_self H hH t) dx psi (H.mulVec psi)

/-- Every finite number of steps preserves probability. -/
theorem hermitianCayley_iterate_norm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t dx : ℝ) (psi : Fin n → ℂ) (k : ℕ) :
    weightedSquaredNorm dx (((hermitianCayley H t).mulVec)^[k] psi) =
      weightedSquaredNorm dx psi := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', hermitianCayley_weightedSquaredNorm H hH, ih]

theorem hermitianCayley_iterate_normalized {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t dx : ℝ) (psi : Fin n → ℂ) (k : ℕ)
    (hnorm : weightedSquaredNorm dx psi = 1) :
    weightedSquaredNorm dx (((hermitianCayley H t).mulVec)^[k] psi) = 1 := by
  rw [hermitianCayley_iterate_norm H hH, hnorm]

theorem hermitianCayley_iterate_energy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t dx : ℝ) (psi : Fin n → ℂ) (k : ℕ) :
    gridInnerProduct dx (((hermitianCayley H t).mulVec)^[k] psi)
      (H.mulVec (((hermitianCayley H t).mulVec)^[k] psi)) =
        gridInnerProduct dx psi (H.mulVec psi) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', hermitianCayley_energy H hH, ih]

/-- Identifies the pre-existing grid evolution with the general Cayley transform. -/
theorem crankNicolsonEvolution_eq_hermitianCayley {n : ℕ} (dx dt : ℝ) (V : Fin n → ℝ) :
    crankNicolsonEvolution dx dt V = hermitianCayley (gridHamiltonianMatrix dx V) (dt / 2) := by
  rfl

/-- Static-H energy conservation for the actual interior-grid mathematical model. -/
theorem crankNicolsonEvolution_energy {n : ℕ} (dx dt : ℝ) (V : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    gridInnerProduct dx ((crankNicolsonEvolution dx dt V).mulVec psi)
      (applyGridHamiltonian dx V ((crankNicolsonEvolution dx dt V).mulVec psi)) =
        gridInnerProduct dx psi (applyGridHamiltonian dx V psi) := by
  exact hermitianCayley_energy _ (gridHamiltonianMatrix_isHermitian dx V) (dt / 2) dx psi

/-- The right unitarity identity also holds in dimension zero. -/
theorem hermitianCayley_mul_conjTranspose_self {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) : hermitianCayley H t * (hermitianCayley H t)ᴴ = 1 := by
  exact mul_eq_one_comm.mp (hermitianCayley_conjTranspose_mul_self H hH t)

/-- Negating the real timestep reverses exact evolution. -/
theorem hermitianCayley_neg_time {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) : hermitianCayley H (-t) = (hermitianCayley H t)ᴴ := by
  have hnegA : cayleyLeft H (-t) = cayleyRight H t := by
    simp [cayleyLeft, cayleyRight, sub_eq_add_neg]
  have hnegB : cayleyRight H (-t) = cayleyLeft H t := by
    simp [cayleyLeft, cayleyRight, sub_eq_add_neg]
  have he := congrArg (fun M => M * (hermitianCayley H t)ᴴ) (cayleyLeft_mul_cayley H hH t)
  rw [Matrix.mul_assoc, hermitianCayley_mul_conjTranspose_self H hH t, Matrix.mul_one] at he
  have hs : cayleyLeft H (-t) * (hermitianCayley H t)ᴴ = cayleyRight H (-t) := by
    rw [hnegA, hnegB]
    exact he.symm
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp (cayleyLeft_isUnit H hH (-t))
  rw [hermitianCayley, ← hs, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

/-- Any finite sequence of Hermitian steps preserves norm, even if H and t change.
Energy conservation is deliberately not asserted for such changing Hamiltonians. -/
theorem hermitianCayley_sequence_norm {n : ℕ}
    (steps : List (Matrix (Fin n) (Fin n) ℂ × ℝ)) (dx : ℝ) (psi : Fin n → ℂ)
    (hsteps : ∀ s ∈ steps, s.1.IsHermitian) :
    weightedSquaredNorm dx
      (steps.foldl (fun state s => (hermitianCayley s.1 s.2).mulVec state) psi) =
        weightedSquaredNorm dx psi := by
  induction steps generalizing psi with
  | nil => rfl
  | cons s rest ih =>
    rw [List.foldl_cons, ih _ (fun a ha => hsteps a (by simp [ha]))]
    exact hermitianCayley_weightedSquaredNorm _ (hsteps s (by simp)) _ _ _

end PsiZoo
