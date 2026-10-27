# Slice 4 proof coverage

## Status and verification boundary

**27 new Lean theorems**, in namespace `PsiZoo`, checked with the existing
`leanprover/lean4:v4.36.0-rc1` and locked Mathlib commit
`9c6a29e8f339d650449067da68001b28a59a3d8c`. No dependency files changed.

Three distinct kinds of evidence must not be conflated:

1. **Lean theorems:** exact real/complex mathematics listed below. These have
   kernel-checked proofs, not numerical evidence.
2. **TypeScript numerical tests:** the app's qubit, creature, and world tests
   check finite-precision results and validation/ownership behavior. Existing
   validation documents report passing runs; those tests were inspected, **not
   rerun in this proof update**. Historical test counts are not current counts.
3. **Implementation correspondence:** the mapping below is based on source
   inspection, not a verified translation, refinement proof, or IEEE-754 model.
   No Lean theorem proves that the JavaScript arrays execute the exact formulas.

Inspected game checkout: `ab29498ceda859b7a310123361b2d091510f6cbe`.
The pre-existing untracked `packages/sim-core/tests/measurement.test.ts` was
left untouched. No game files were edited, and neither repository was committed.

Before this update, real diagonal Hermiticity, finite-grid Hamiltonian
Hermiticity, CN invertibility, unitarity, and norm preservation were already
proved. There were no qubit/Bloch, mood-specific, or social-interaction modules.
All existing proofs are retained; the coupling results specialize them.

## Conventions and exact objects

- Qubit: amplitudes `α β : ℂ`, ordered as `|0>, |1>`. `qubitNorm` is the
  **squared** norm `|α|²+|β|²`, with no spatial `dx` factor.
- `blochX = 2 Re(conj α * β)`, `blochY = 2 Im(conj α * β)`, and
  `blochZ = |α|²-|β|²`. In particular the sign of y is not reversed.
- `qubitHamiltonian ax ay az = [[az, ax-i ay], [ax+i ay, -az]]`.
  Coefficients are real; ℏ = 1 and there is **no factor 1/2**.
- `qubitStep nx ny nz c s` acts as `c I - i s (n dot σ)`.
  `fieldMagnitude a = sqrt(ax²+ay²+az²)`.
  `evolveQubitExact` returns the input pair if this magnitude is zero;
  otherwise it uses `n=a/|a|`, `c=cos(|a|t)`, `s=sin(|a|t)`.
- `schrodingerExponential H t = NormedSpace.exp ((-i*t) • H)` is the
  **genuine matrix exponential**, not the CN Cayley transform.
- Spatial states `Fin n → ℂ` contain only interior Dirichlet sites. Application
  index `j+1` corresponds to Lean index `j`. Endpoints are zero and omitted.
  `weightedSquaredNorm dx ψ = dx * Σ |ψ_i|²`.
- `probabilityDensity ψ i = |ψ_i|²`: density, not site probability mass.
  `contactPotential g partner i = g * |partner_i|²` has **no dx factor**.
  `interactionEnergy g dx A B = g * dx * Σ ρA_i ρB_i`, counted once.

Real-valued potentials are constructed from real arithmetic. The `_im`
theorems explicitly prove their complex embeddings have zero imaginary part;
these are not claims about overflow or finite JavaScript numbers. The algebraic
mood results allow any real F0/rz, hence include the game's F0 ≥ 0 and valid
normalized Bloch coordinates without needing artificial extra hypotheses.

## 4A — qubit theorem inventory

Source for every row in this table: [Qubit.lean](../PsiZooProofs/Qubit.lean).
All amplitude variables are arbitrary complex numbers; other parameters are
real. “None” means no additional hypotheses beyond these types.
The corresponding TypeScript source is
`packages/sim-core/src/qubit.ts`.

| Exact Lean name (`PsiZoo.` prefix) | Assumptions | Proved mathematics / corresponding TS function |
| --- | --- | --- |
| `bloch_radius` | None | `rx²+ry²+rz² = qubitNorm²`; `blochVector`, `qubitNormSquared` |
| `bloch_sphere` | `qubitNorm α β = 1` | `rx²+ry²+rz² = 1`; `blochVector` |
| `bloch_global_phase` | `Complex.normSq p = 1` | All three coordinates unchanged under `(α,β) ↦ (pα,pβ)`; `blochVector` |
| `qubitHamiltonian_isHermitian` | Real ax, ay, az | `Hᴴ=H` for the standard Pauli combination; field used by `evolveQubit` |
| `qubitStep_norm_factor` | None; arbitrary real n,c,s | Output squared norm is `(c²+s²|n|²)` times input squared norm; component arithmetic in `evolveQubit` |
| `qubitStep_norm` | `nx²+ny²+nz²=1` | With c=cos θ, s=sin θ, output squared norm equals input squared norm; `evolveQubit` nonzero-field branch |
| `field_axis_unit` | `fieldMagnitude ax ay az ≠ 0` | The normalized field has squared length one; normalized-axis calculation in `evolveQubit` |
| `evolveQubitExact_norm` | None, including zero/negative t and zero field | The full piecewise closed-form evolution preserves squared norm; `evolveQubit` |
| `evolveQubitExact_zero_field` | Field explicitly (0,0,0) | Evolution is the identity for every t; `evolveQubit` zero-field branch (no storage/alias claim) |
| `qubitStep_bloch_polynomial` | None | Full polynomial action on rx,ry,rz; algebraic helper for `evolveQubit` / `blochVector` correspondence |
| `qubitStep_bloch_rotation` | `nx²+ny²+nz²=1` | Full Rodrigues law at angle +2θ; `evolveQubit` / `blochVector` |
| `evolveQubitExact_bloch_rotation` | `fieldMagnitude ax ay az ≠ 0` | Full constant-field rotation at angle +2|a|t about a/|a|; `evolveQubit` / `blochVector` |

The last two theorems use the explicitly defined `blochRotation`:

```text
r' = cos(2θ) r + (1-cos(2θ)) n (n dot r) + sin(2θ) (n cross r).
```

This proves the finite-time rotation law, with positive right-handed cross
product and angular-velocity vector **2a**. It is not merely a radius-preservation
substitute. It even holds for unnormalized amplitudes. At zero field the
separate zero-field identity gives stationary amplitudes and coordinates.
A derivative statement `dr/dt = 2 a cross r` is not separately formalized.

### Genuine exponential

Source for every row: [QubitExponential.lean](../PsiZooProofs/QubitExponential.lean).
The finite dimension n is arbitrary, including zero. The TS counterpart is the
mathematical exponential described in `evolveQubit`'s specification, **not** an
actual call to a matrix-exponential library in the game.

| Exact Lean name (`PsiZoo.` prefix) | Assumptions | Proved mathematics |
| --- | --- | --- |
| `schrodingerExponential_adjoint_mul` | Finite complex matrix H, `H.IsHermitian`, real t | `exp(-itH)ᴴ exp(-itH) = I` |
| `schrodingerExponential_mem_unitaryGroup` | Same | Membership in Mathlib's matrix unitary group, hence two-sided unitarity |
| `schrodingerExponential_norm` | Same, arbitrary state ψ | Unweighted squared norm (`weightedSquaredNorm 1`) is preserved |
| `qubit_exponential_norm` | Real ax,ay,az,t; arbitrary complex α,β | `exp(-it (a dot σ))` preserves `|α|²+|β|²`, including zero field |

**Remaining exact mathematical bridge:** equality between this exponential's
action and `evolveQubitExact` has not been proved. Both objects have independent
norm-preservation proofs; Rodrigues precession is proved for the closed-form
object. Completing the bridge would require proving the Pauli square identity
`H²=|a|² I` and deriving the exponential's cosine/sine series (or an equivalent
spectral/ODE argument), including the zero-field case. We do not silently use
this missing equality to transfer the rotation theorem to `NormedSpace.exp`.

## 4B/4C — coupling theorem inventory

Source for every row: [CreatureCoupling.lean](../PsiZooProofs/CreatureCoupling.lean).
All scalars are real; n is any natural number; A,B,ψ are arbitrary complex
interior states. No normalization or sign of g is needed. Coordinate and
terrain functions are real. The relevant TS sources are:

- **C:** `packages/web/src/world/creature.ts`, `Creature.composePotential`,
  `Creature.potential`, and `Creature.step`.
- **W:** `packages/web/src/world/twoCreatureWorld.ts`, private `contactPotential`,
  `TwoCreatureWorld.socialPotentials`, and `TwoCreatureWorld.step`.
- **CN:** `packages/sim-core/src/crankNicolson.ts`, `CrankNicolsonStepper.step`.

| Exact Lean name (`PsiZoo.` prefix) | Additional assumptions | Proved mathematics / correspondence |
| --- | --- | --- |
| `moodPotential_im` | None | Complex embedding of `-F0*rz*(x-xRef)` has imaginary part zero; C.composePotential |
| `moodForce_reverse` | None | `F(F0,-rz) = -F(F0,rz)`; C.composePotential |
| `moodPotential_reverse` | None | Reversing rz negates the mood contribution (not terrain); C.composePotential |
| `moodPotential_isHermitian` | Any real coordinate samples x | Diagonal mood contribution is Hermitian; C.composePotential / CN |
| `mood_cn_norm` | `0 < dx`; fixed real terrain and rz during solve | Explicit CN with terrain plus mood preserves spatial squared norm; C.step / CN |
| `probabilityDensity_nonneg` | None | `ρ_i ≥ 0` for each site; W.contactPotential |
| `contactPotential_im` | None, g may have either sign | Complex embedding of `gρ_i` is real; W.contactPotential (applies to either partner) |
| `socialPotentials_exchange` | None | Swapping A,B swaps the ordered pair `(gρB,gρA)`; W.socialPotentials |
| `interactionEnergy_exchange` | None; any real g,dx | `g dx Σ ρAρB = g dx Σ ρBρA`; cross-energy diagnostic in `twoCreatureWorld.test.ts`'s `energy` / `overlap` helpers, described in SOCIAL_INTERACTION_VALIDATION.md |
| `contactPotential_isHermitian` | None | Each real frozen contact potential contributes a Hermitian diagonal; W.step / CN |
| `social_cn_norms` | `0 < dx`; frozen old A,B; arbitrary fixed real extraA,extraB | Both explicit CN solves preserve their respective spatial squared norms; W.step / C.step / CN |

In `social_cn_norms`, extraA/extraB can be terrain plus the independently
sampled midpoint mood potentials. The result constructs the existing explicit
CN evolutions; **invertibility is not an assumption**. Normalized inputs remain
normalized immediately by rewriting these equalities with the input norm one.

The game computes BOTH contact potentials from endpoint densities at t, freezes
them for [t,t+dt], and calls two separate creature steps. Each creature samples
its mood at t+dt/2 for the spatial potential, then updates its endpoint mood to
t+dt. `Creature.potential` instead diagnoses the current endpoint mood. The Lean
results apply to any fixed sampled rz; they do not prove this scheduling code,
its atomic fork/commit behavior, or order of mutation.

### Existing theorems reused, not replaced

| Exact Lean name (`PsiZoo.` prefix) | Source | Assumptions / use |
| --- | --- | --- |
| `realPotentialMatrix_isHermitian` | HamiltonianStructure.lean | Any real V; supplies both new diagonal Hermiticity proofs |
| `crankNicolsonEvolution_weightedSquaredNorm` | CrankNicolsonEvolution.lean | `dx>0`, real V, any real dt; supplies all new spatial norm results |
| `gridInnerProduct_unitary` | HermitianCayley.lean | `UᴴU=I`, any real weight; supplies exponential norm preservation |
| `crankNicolsonEvolution_mem_unitaryGroup` | CrankNicolsonUnitarity.lean | `dx>0`, fixed real V, real dt; already proves full grid CN unitarity |

These proofs ultimately reuse the established finite-grid inner product,
Hermitian Hamiltonian, CN existence/invertibility, and Cayley proof chain. There
is no new inverse axiom and no circular use of conservation to assume unitarity.

## Numerical evidence versus Lean coverage

Inspected tests (read-only):

- `packages/sim-core/tests/qubit.test.ts`: axis signs and double angle,
  independent general-axis Rodrigues comparison, phase cancellation, zero
  field/time, reversal/composition, 10,000-step drift without normalization.
- `packages/web/src/world/creature.test.ts`: real linear potential, opposite
  mood forces, midpoint sampling, 1,000-step norms/radii, temporal refinement,
  static versus time-dependent energy, validation and ownership.
- `packages/web/src/world/twoCreatureWorld.test.ts`: synchronized old densities,
  no self-interaction, label exchange, 1,000-step coupled norms, nonlinear
  first-order refinement and nonzero combined-energy drift.

The game documents historical numerical runs in `docs/QUBIT_VALIDATION.md`,
`docs/CREATURE_VALIDATION.md`, and `docs/SOCIAL_INTERACTION_VALIDATION.md`.
Those tolerance-based experiments are not Lean proofs or universal error
bounds. No new TypeScript test pass is claimed here.

## How the proof tactics express the mathematics

- `unfold` / `dsimp` expose definitions and evaluate tuple projections and
  local `let` bindings. They do not change the modeled equation.
- `simp` / `simp only` use proved rules for real embeddings, complex arithmetic,
  conjugation, and finite sums. `simpa ... using` matches an existing theorem
  after those reductions. In particular, `_im` uses `Complex.ofReal_im`.
- `ring` checks real polynomial identities: the Bloch radius, phase scaling,
  propagator norm factor, and all three components of the Bloch action.
- `have` names intermediate facts. `rw` substitutes proved equalities: unit
  axis, cosine/sine identities, conjugate-transpose of an exponential, and
  the cancellation `(-X)+X=0`. `exact` supplies a previously checked proof.
- `apply` reduces a goal to a known lemma's hypotheses. `ext` reduces a tuple
  or complex equality to its real component equalities;
  `fin_cases` exhausts the two possible matrix indices to check Hermiticity.
- `positivity` proves the sum of three real squares is nonnegative;
  `Real.sq_sqrt` then identifies the squared field magnitude. `field_simp`
  clears denominators with checked nonzero obligations, and `nlinarith`
  finishes using this square identity. It also derives the double-angle
  cosine rearrangements from `sin²+cos²=1`.
- `split_ifs` separates zero and nonzero magnitude; `rfl` proves identity in
  the zero branch by definition. `rfl` also proves the partner-pair exchange
  because exchanging the arguments literally exchanges the two definitions.
- `constructor` splits the pair of spatial conservation conclusions. Each
  is discharged by the existing explicit CN conservation theorem.
- The exponential proof uses Hermiticity to obtain `(-itH)ᴴ=-(-itH)`.
  Mathlib's exponential multiplication theorem for commuting matrices combines
  the two factors to `exp(0)=I`; a matrix and its negative commute. Existing
  unitary inner-product preservation then yields norm preservation. No power
  series or floating-point exponential is evaluated numerically.

## Build and audit

```bash
lake build
lake env lean Slice4Checks.lean
```

Baseline output before edits:

```text
Build completed successfully (4412 jobs).
```

Successful incremental builds after qubit core, rotation/coupling, and genuine
exponential proofs respectively ended with:

```text
Build completed successfully (4432 jobs).
Build completed successfully (4434 jobs).
✔ [5040/5044] Built PsiZooProofs.QubitExponential (6.7s)
✔ [5042/5044] Built PsiZooProofs (137s)
Build completed successfully (5044 jobs).
```

Final verification again reported `Build completed successfully (5044 jobs).`
Both existing audits, `lake env lean Checks.lean` and
`lake env lean MeasurementChecks.lean`, also completed successfully.
`git diff --check` found no whitespace errors (Git emitted only its Windows
LF/CRLF conversion notices). A scan of the three new proof modules found no
forbidden proof placeholders or shortcuts.

An intermediate long-line warning was fixed. `Slice4Checks.lean` prints all
27 theorem types and audits every theorem's axioms. All depend only on the
standard foundations `[propext, Classical.choice, Quot.sound]`; no `sorryAx`,
custom axioms, admitted terms, unsafe proofs, or native-evaluation shortcuts.
The check file is an explicit audit command, not a default Lake target; the
three proof modules are imported by the root library and built by `lake build`.

## Remaining obligations and non-claims

- The closed form / genuine exponential equality described above; a separate
  derivative-form precession theorem if desired.
- Formal correspondence to the scaled TypeScript axis/phase calculation,
  normalization tolerance, zero-time copy branch, array layout, checks,
  transcendental implementation, roundoff, overflow/underflow, and solver.
- A proof of the complete nonlinear multi-step world update, its convergence
  order, or its reported trajectories. Each frozen real CN solve is norm
  preserving; this is not a proof of the entire numerical implementation.
- No exact combined-energy conservation is claimed. Frozen-density feedback
  is generally first order even though an individual fixed-H CN step is
  unitary. Time-varying mood/terrain need not conserve spatial energy.
- Mood and spatial motion are separate states with a classical parameter
  coupling; two creatures are separate mean-field states. No joint tensor
  product, entanglement, coherent inter-creature interference, quantum spatial
  backreaction on mood, or continuum limit is asserted.

This is the Slice 4 proof update only, ready for review.
