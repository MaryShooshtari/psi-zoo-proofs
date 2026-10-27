module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-! Exact counterparts of qubit.ts. No dx weight, no floating-point claims.
The propagator is represented by its closed trigonometric formula; identification
with the matrix exponential is not used or asserted in this file. -/
@[expose] public section
namespace PsiZoo

noncomputable def qubitNorm (α β : ℂ) : ℝ := Complex.normSq α + Complex.normSq β
noncomputable def blochX (α β : ℂ) : ℝ := 2 * (α.re * β.re + α.im * β.im)
noncomputable def blochY (α β : ℂ) : ℝ := 2 * (α.re * β.im - α.im * β.re)
noncomputable def blochZ (α β : ℂ) : ℝ := Complex.normSq α - Complex.normSq β

theorem bloch_radius (α β : ℂ) :
    blochX α β ^ 2 + blochY α β ^ 2 + blochZ α β ^ 2 = qubitNorm α β ^ 2 := by
  simp only [blochX, blochY, blochZ, qubitNorm, Complex.normSq_apply]
  ring

theorem bloch_sphere (α β : ℂ) (h : qubitNorm α β = 1) :
    blochX α β ^ 2 + blochY α β ^ 2 + blochZ α β ^ 2 = 1 := by
  rw [bloch_radius, h, one_pow]

theorem bloch_global_phase (α β p : ℂ) (hp : Complex.normSq p = 1) :
    blochX (p * α) (p * β) = blochX α β ∧
    blochY (p * α) (p * β) = blochY α β ∧
    blochZ (p * α) (p * β) = blochZ α β := by
  have hx : blochX (p * α) (p * β) = Complex.normSq p * blochX α β := by
    simp only [blochX, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]; ring
  have hy : blochY (p * α) (p * β) = Complex.normSq p * blochY α β := by
    simp only [blochY, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]; ring
  simp [hx, hy, hp, blochZ, Complex.normSq_mul]

/-- H = ax σx + ay σy + az σz, without a factor 1/2. -/
noncomputable def qubitHamiltonian (ax ay az : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(az : ℂ), (ax : ℂ) - Complex.I * (ay : ℂ);
     (ax : ℂ) + Complex.I * (ay : ℂ), -(az : ℂ)]

theorem qubitHamiltonian_isHermitian (ax ay az : ℝ) :
    (qubitHamiltonian ax ay az).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [qubitHamiltonian, star]

/-- Component form of (c I - i s (n dot sigma)) psi. -/
noncomputable def qubitStep (nx ny nz c s : ℝ) (α β : ℂ) : ℂ × ℂ :=
  ((c : ℂ) * α - Complex.I * (s : ℂ) *
      ((nz : ℂ) * α + ((nx : ℂ) - Complex.I * (ny : ℂ)) * β),
   (c : ℂ) * β - Complex.I * (s : ℂ) *
      (((nx : ℂ) + Complex.I * (ny : ℂ)) * α - (nz : ℂ) * β))

/-- Algebraic norm factor, before imposing any unit-axis or trigonometric hypotheses. -/
theorem qubitStep_norm_factor (nx ny nz c s : ℝ) (α β : ℂ) :
    qubitNorm (qubitStep nx ny nz c s α β).1 (qubitStep nx ny nz c s α β).2 =
      (c ^ 2 + s ^ 2 * (nx ^ 2 + ny ^ 2 + nz ^ 2)) * qubitNorm α β := by
  simp [qubitNorm, qubitStep, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem qubitStep_norm (nx ny nz θ : ℝ) (α β : ℂ)
    (hn : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    qubitNorm (qubitStep nx ny nz (Real.cos θ) (Real.sin θ) α β).1
      (qubitStep nx ny nz (Real.cos θ) (Real.sin θ) α β).2 = qubitNorm α β := by
  rw [qubitStep_norm_factor, hn, mul_one, Real.cos_sq_add_sin_sq, one_mul]

noncomputable def fieldMagnitude (ax ay az : ℝ) : ℝ := Real.sqrt (ax ^ 2 + ay ^ 2 + az ^ 2)

/-- The game's closed-form propagator, including its zero-field branch. -/
noncomputable def evolveQubitExact (ax ay az t : ℝ) (α β : ℂ) : ℂ × ℂ :=
  let w := fieldMagnitude ax ay az
  if w = 0 then (α, β)
  else qubitStep (ax / w) (ay / w) (az / w) (Real.cos (w * t)) (Real.sin (w * t)) α β

theorem field_axis_unit (ax ay az : ℝ) (hw : fieldMagnitude ax ay az ≠ 0) :
    (ax / fieldMagnitude ax ay az) ^ 2 + (ay / fieldMagnitude ax ay az) ^ 2 +
      (az / fieldMagnitude ax ay az) ^ 2 = 1 := by
  have hs : fieldMagnitude ax ay az ^ 2 = ax ^ 2 + ay ^ 2 + az ^ 2 := by
    apply Real.sq_sqrt
    positivity
  field_simp
  nlinarith

theorem evolveQubitExact_norm (ax ay az t : ℝ) (α β : ℂ) :
    qubitNorm (evolveQubitExact ax ay az t α β).1
      (evolveQubitExact ax ay az t α β).2 = qubitNorm α β := by
  unfold evolveQubitExact
  dsimp only
  split_ifs with h
  · rfl
  · exact qubitStep_norm _ _ _ _ _ _ (field_axis_unit ax ay az h)

theorem evolveQubitExact_zero_field (t : ℝ) (α β : ℂ) :
    evolveQubitExact 0 0 0 t α β = (α, β) := by
  simp [evolveQubitExact, fieldMagnitude]

/-- Rodrigues rotation, with the right-handed cross product n × r. -/
noncomputable def blochRotation (nx ny nz θ rx ry rz : ℝ) : ℝ × ℝ × ℝ :=
  let d := nx * rx + ny * ry + nz * rz
  (Real.cos (2 * θ) * rx + (1 - Real.cos (2 * θ)) * nx * d +
      Real.sin (2 * θ) * (ny * rz - nz * ry),
   Real.cos (2 * θ) * ry + (1 - Real.cos (2 * θ)) * ny * d +
      Real.sin (2 * θ) * (nz * rx - nx * rz),
   Real.cos (2 * θ) * rz + (1 - Real.cos (2 * θ)) * nz * d +
      Real.sin (2 * θ) * (nx * ry - ny * rx))

/-- The algebraic Bloch action; no normalization hypotheses are required. -/
theorem qubitStep_bloch_polynomial (nx ny nz c s : ℝ) (α β : ℂ) :
    let q := qubitStep nx ny nz c s α β
    let rx := blochX α β
    let ry := blochY α β
    let rz := blochZ α β
    let d := nx * rx + ny * ry + nz * rz
    let k := c ^ 2 - s ^ 2 * (nx ^ 2 + ny ^ 2 + nz ^ 2)
    (blochX q.1 q.2, blochY q.1 q.2, blochZ q.1 q.2) =
      (k * rx + 2 * s ^ 2 * nx * d + 2 * c * s * (ny * rz - nz * ry),
       k * ry + 2 * s ^ 2 * ny * d + 2 * c * s * (nz * rx - nx * rz),
       k * rz + 2 * s ^ 2 * nz * d + 2 * c * s * (nx * ry - ny * rx)) := by
  dsimp
  simp only [qubitStep, blochX, blochY, blochZ, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ext <;> ring

/-- A unit axis produces angle +2θ, not θ, even for unnormalized amplitudes. -/
theorem qubitStep_bloch_rotation (nx ny nz θ : ℝ) (α β : ℂ)
    (hn : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    let q := qubitStep nx ny nz (Real.cos θ) (Real.sin θ) α β
    (blochX q.1 q.2, blochY q.1 q.2, blochZ q.1 q.2) =
      blochRotation nx ny nz θ (blochX α β) (blochY α β) (blochZ α β) := by
  dsimp only
  rw [qubitStep_bloch_polynomial, hn]
  have hc : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs : 1 - Real.cos (2 * θ) = 2 * Real.sin θ ^ 2 := by
    rw [hc]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  unfold blochRotation
  rw [hs, hc, Real.sin_two_mul]
  ext <;> ring

/-- Constant-field precession about a/|a| at angular speed 2|a|.
Together with the zero-field theorem this covers every field. -/
theorem evolveQubitExact_bloch_rotation (ax ay az t : ℝ) (α β : ℂ)
    (hw : fieldMagnitude ax ay az ≠ 0) :
    let w := fieldMagnitude ax ay az
    let q := evolveQubitExact ax ay az t α β
    (blochX q.1 q.2, blochY q.1 q.2, blochZ q.1 q.2) =
      blochRotation (ax / w) (ay / w) (az / w) (w * t)
        (blochX α β) (blochY α β) (blochZ α β) := by
  dsimp only [evolveQubitExact]
  simp only [hw, ↓reduceIte]
  exact qubitStep_bloch_rotation _ _ _ _ _ _ (field_axis_unit ax ay az hw)

end PsiZoo
