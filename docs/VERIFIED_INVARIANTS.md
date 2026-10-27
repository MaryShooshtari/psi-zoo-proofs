# Verified simulation invariants

All names below are in namespace `PsiZoo`. These are Lean kernel-checked exact
mathematical results over ℝ and ℂ, using the pinned Lean/Mathlib installation.
They are not formal verification of TypeScript, floating-point arithmetic, GUI
behavior, or the continuum Schrödinger equation.

## Slice 4 update

See [Slice 4 coverage](SLICE4_COVERAGE.md) for the 27 new qubit, exponential,
mood-drive, and mean-field interaction theorems, their exact assumptions and
TypeScript source mapping. The original invariant inventory below is retained.
Bloch rotation is now proved for the closed trigonometric propagator; equality
of that propagator with the independently proved unitary matrix exponential
remains an explicit obligation.

## Build and inspect

```bash
lake build
lake env lean Checks.lean
```

The first command checks all modules imported by `PsiZooProofs.lean`. The second
prints selected theorem types and their axiom dependencies. Standard Lean/Mathlib
foundations (`propext`, `Classical.choice`, `Quot.sound`) are not custom physical
axioms. No `sorry`, `admit`, `unsafe`, or `native_decide` is used in these proofs.
For a focused check after building its imports, use, for example:

```bash
lake env lean PsiZooProofs/HermitianCayley.lean
```

An editor with Lean support lets you inspect each intermediate goal. On this
Windows machine, serial focused checks are preferable to several concurrent
Lean processes: one parallel attempt exhausted memory, whereas serial checks
and full Lake builds succeeded. No dependency or toolchain change was needed.

## Representation and correspondence

- A state is `Fin n → ℂ`. `Complex.normSq z` is `z.re² + z.im²`.
- `weightedSquaredNorm dx psi = dx * ∑ i, Complex.normSq (psi i)`.
  This is not the default function-space norm on `Fin n → ℂ`.
- `gridInnerProduct dx phi psi = dx * ∑ i, conj (phi i) * psi i`:
  conjugate-linear first argument, linear second argument.
- The Hamiltonian's `n` coordinates are **interior** Dirichlet points. They
  correspond to full-grid positions `j + 1` in an `n + 2` point application grid.
  The omitted endpoints are zero. No wraparound adjacency is introduced.
- Region/projection theorems work on any finite coordinate set, including a full
  grid with endpoints. For Dirichlet states the endpoint contributions vanish.
- Physical spacing is positive. Some algebraic equalities actually hold for all
  real weights, including zero and negative weights; positivity statements have
  explicit nonnegative or positive spacing assumptions.
- Empty and singleton coordinate spaces are allowed. Normalization requires a
  nonzero state and therefore cannot normalize the empty or zero state.

Application sources (read-only during development):

| Application source | Mathematical counterpart |
| --- | --- |
| [`regions.ts`](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/src/regions.ts) | Rectangle-sum masses; strict outer cuts and inclusive middle interval |
| [`potential.ts`](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/src/potential.ts) | Gaussian samples, nearest-segment path profile, maximum painting and validated cap |
| [`hamiltonian.ts`](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/src/hamiltonian.ts) | Interior diagonal `1/dx² + V`, neighbor coefficient `-1/(2 dx²)`, energy form |
| [`crankNicolson.ts`](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/src/crankNicolson.ts) | `A = I + i(dt/2)H`, `B = I - i(dt/2)H`, `U = A⁻¹ B` |

These links describe inspected source correspondence, not a machine-checked
translation. In particular `applyHamiltonian` reads stored endpoint inputs in
its interior rows: Hermiticity is not asserted for arbitrary unrestricted
full-grid inputs. The stepper checks zero endpoints and solves only interiors.

## A. Regional probability — complete

Source: [`RegionProbability.lean`](../PsiZooProofs/RegionProbability.lean).
Define `P_s(psi) = dx * ∑ i ∈ s, normSq (psi i)`.

| Exact theorem names | Statement and assumptions |
| --- | --- |
| `regionProbability_nonneg` | `P_s ≥ 0` if `dx ≥ 0`; squared-magnitude nonnegativity is the existing Mathlib `Complex.normSq_nonneg` |
| `regionProbability_univ` | Full-grid mass is `weightedSquaredNorm`, for any real spacing |
| `regionProbability_mono`, `regionProbability_le_total` | If `dx ≥ 0`, inclusion increases mass, hence every regional mass is at most total mass |
| `regionProbability_union` | Mass of a disjoint union is the sum, for any real spacing |
| `regionProbability_partition_three` | Three pairwise disjoint regions covering the grid account for the entire mass |
| `regionProbability_partition_normalized` | Under the same partition hypotheses and total mass one, the three regional masses sum to one |
| `spatial_region_partition` | For `a ≤ b`, the filters `x < a`, `a ≤ x ∧ x ≤ b`, `b < x` are disjoint and cover every index |
| `spatial_region_probability_sum` | Those exact spatial-cut masses sum to total probability; coordinate map `x` is arbitrary, so `x i = x0 + i * dx` is included |
| `regionProbability_partition` | A finite family of pairwise disjoint regions accounts for the mass of its union |
| `regionProbability_partition_sum_one` | If that union covers the grid and the state is normalized, the indexed mass sum is one |

Total mass nonnegativity was already available as
`weightedSquaredNorm_nonneg` at positive spacing. Combining regional lower and
upper bounds gives `0 ≤ P_s ≤ P_total` and, when normalized, `P_s ≤ 1`.
These are raw masses, not automatically reflection/transmission coefficients.
A low interaction mass alone does not establish scattering or tunnelling.

## B. Potential landscapes — complete core invariants

Source: [`PotentialLandscape.lean`](../PsiZooProofs/PotentialLandscape.lean).

`gaussianBarrier A c sigma x = A * exp(-(((x-c)/sigma)²)/2)`.
The application requires `sigma > 0`. Basic Lean bounds need no width hypothesis
because real division is totalized; the unique-maximum theorem requires
`sigma ≠ 0`. This is not permission to pass width zero to the browser API.

| Exact theorem names | Statement and assumptions |
| --- | --- |
| `gaussianBarrier_nonneg`, `gaussianBarrier_le_amplitude` | For `A ≥ 0`, the barrier lies in `[0,A]` |
| `gaussianBarrier_center`, `gaussianBarrier_max_at_center` | Value at the center is A; for `A ≥ 0`, every other value is at most the center value |
| `gaussianBarrier_pos` | For `A > 0`, the exact Gaussian is strictly positive everywhere; floating-point exponentiation may underflow |
| `gaussianBarrier_eq_amplitude_iff` | For `A > 0` and nonzero width, value equals A iff `x = c` |
| `stampPotential_increases` | Pointwise `max(V,W)` never decreases V |
| `stampPotential_idempotent` | Stamping W twice has the same result as stamping it once |
| `stampPotential_order_independent` | Stamping W then Z equals stamping Z then W |
| `stampPotential_bounds` | If V and W lie pointwise in `[0,M]`, so does their maximum |
| `stampPotential_fold_bounds` | A finite list of such bounded stamps preserves `[0,M]` |
| `cappedStampPotential_bounds` | Explicitly clipped `min M (max V W)` lies in `[0,M]` if `M ≥ 0` and `V ≥ 0` |
| `cappedStampPotential_eq_stamp` | If V and W are already at most M, clipping does nothing |
| `gaussianPathProfile_bounds` | The nearest-segment-center profile lies in `[0,A]` for `A ≥ 0` |
| `gaussianPathProfile_reverse` | Reversing path endpoints leaves the profile unchanged |
| `gaussianPathProfile_on_segment` | At coordinates within the traversed segment, the profile equals A |
| `gaussianPathProfile_point` | A zero-length path is exactly a single Gaussian |

The app **rejects** amplitude/terrain exceeding its cap; it does not silently
truncate. `stampPotential_bounds` models that contract. The explicitly clipped
variant is a separate reusable object. Off-grid centers need not attain A on
the sampled grid. The path profile models the implemented nearest-point formula;
its equality to the supremum of all continuously centered Gaussians and its
subdivision invariance are not separately formalized here.

## C. Discrete Hamiltonian — complete structural goals

Sources: [`GridHamiltonian.lean`](../PsiZooProofs/GridHamiltonian.lean),
[`HamiltonianStructure.lean`](../PsiZooProofs/HamiltonianStructure.lean).
For positive spacing this is the physical interior Dirichlet matrix in units
ℏ = m = 1. The algebraic Hermiticity proofs do not require positive spacing
because their only ingredients are real coefficients and symmetric adjacency.

| Exact theorem names | Statement and assumptions |
| --- | --- |
| `realPotentialMatrix_isHermitian` | The diagonal matrix of any real potential is Hermitian |
| `gridKineticMatrix_isHermitian` | The zero-potential finite-difference kinetic matrix is Hermitian |
| `gridHamiltonianMatrix_decomposition` | `H = T + diag(V)` |
| `gridHamiltonianMatrix_isHermitian_of_decomposition` | The sum is Hermitian, derived compositionally |
| `gridHamiltonianMatrix_isHermitian` (existing) | Direct entrywise Hermiticity of H |
| `gridHamiltonian_energy_im_eq_zero` (existing) | The energy form is real at positive spacing |
| `realPotentialMatrix_energy` | Potential energy is `dx * ∑ i, V i * normSq (psi i)` as a complex real number |
| `realPotentialMatrix_energy_nonneg` | That potential-energy contribution is nonnegative if `dx ≥ 0` and `V ≥ 0` |

**Remaining optional spectral/positivity work:** no new theorem asserts positivity
of the full kinetic Hamiltonian, strict positive definiteness under Dirichlet
conditions, eigenvalue bounds, or a spectral decomposition.

## D. General Crank–Nicolson/Cayley theorem — complete, not conditional on invertibility

Source: [`HermitianCayley.lean`](../PsiZooProofs/HermitianCayley.lean).
Let `H : Matrix (Fin n) (Fin n) ℂ` satisfy `H.IsHermitian`, and let `t : ℝ`.
Here **t is the half timestep**: `t = dt/2`. Set

\[
A=I+itH,\qquad B=I-itH,\qquad U=A^{-1}B.
\]

The central statement is:

```lean
theorem hermitianCayley_mem_unitaryGroup {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    hermitianCayley H t ∈ Matrix.unitaryGroup (Fin n) ℂ
```

This holds in every natural dimension, including zero, with no sign restriction
on t and **no assumed inverse**. H need not be tridiagonal or positive.

| Exact theorem names | Statement |
| --- | --- |
| `hermitian_gridInnerProduct` | An arbitrary Hermitian matrix is self-adjoint for the explicit weighted inner product |
| `hermitian_energy_im_eq_zero` | Its energy form has zero imaginary part for any real weight |
| `cayley_step_norm` | The implicit equation `A chi = B psi` implies equal weighted squared norms; this supporting result is explicitly conditional on being a solution |
| `cayleyLeft_isUnit` | A is invertible, proved from Hermiticity, not assumed |
| `cayleyLeft_mul_cayley` | `AU = B` |
| `cayleyLeft_adjoint` | `Aᴴ = B` |
| `hermitianCayley_conjTranspose_mul_self`, `hermitianCayley_mul_conjTranspose_self` | `Uᴴ U = I` and `U Uᴴ = I` |
| `hermitianCayley_mem_unitaryGroup` | Mathlib unitary-group membership |
| `hermitianCayley_weightedSquaredNorm` | U preserves weighted squared norm for any real weight |
| `gridInnerProduct_mulVec_adjoint`, `gridInnerProduct_unitary` | General matrix-adjoint identity and full inner-product preservation under `Uᴴ U = I` |
| `hermitianCayley_commute` | `UH = HU` |
| `hermitianCayley_energy` | Static-H complex energy form is conserved exactly |
| `hermitianCayley_iterate_norm`, `hermitianCayley_iterate_normalized` | Every natural number of steps preserves mass and normalized states |
| `hermitianCayley_iterate_energy` | Every natural number of fixed-H steps preserves energy |
| `hermitianCayley_neg_time` | `U(-t) = U(t)ᴴ`, hence evolution reverses |
| `hermitianCayley_sequence_norm` | Any finite sequence of Hermitian H / real timestep pairs preserves mass, even when H changes |
| `crankNicolsonEvolution_eq_hermitianCayley` | The pre-existing grid evolution is definitionally the general transform at `t = dt/2` |
| `crankNicolsonEvolution_energy` | Static-H energy conservation specialized to the existing grid model |

The energy form is not divided by mass. For normalized states it is the usual
expectation. The sequence theorem makes **no** energy claim for changing H.
The statements are algebraic over finite matrices; no particular concrete grid
size, nonempty dimension, nonzero timestep, or numerical solver is assumed.

### Mathematical proof chain

1. Hermiticity gives real `⟨psi,H psi⟩`.
2. The implicit equation gives `chi-psi = -it H(chi+psi)`. Real polarization
   expresses the norm difference as `Re ⟨chi+psi,chi-psi⟩`, which is zero.
3. A kernel state is a step from zero, hence has zero sum of nonnegative squared
   magnitudes (use weight one). Thus A has trivial kernel. Finite square matrix
   algebra proves A is a unit and justifies inverse cancellation.
4. Taking the adjoint of `AU=B` gives `UᴴB=A`. These identities imply
   `Uᴴ(A+B)U=A+B`. Since `A+B=2I`, cancel the nonzero scalar 2 to obtain `UᴴU=I`.
   Finite square matrices then give the right-inverse identity.
5. A and B commute with H. Cancel invertible A to show U commutes with H.
   Unitary inner-product preservation gives
   `⟨U psi,H U psi⟩ = ⟨U psi,U H psi⟩ = ⟨psi,H psi⟩`.
6. Induction proves repeated-step results. Negating t swaps A and B; the
   unitary identities show the reverse transform is the adjoint.

## Optional exact projection — complete under the necessary nonzero-outcome condition

Source: [`CoordinateProjection.lean`](../PsiZooProofs/CoordinateProjection.lean).
`coordinateProjection s psi i` keeps `psi i` in s and is zero elsewhere.

| Exact theorem names | Statement |
| --- | --- |
| `coordinateProjection_idempotent` | `P_s(P_s psi) = P_s psi` |
| `coordinateProjection_selfAdjoint` | `⟨P_s phi,psi⟩ = ⟨phi,P_s psi⟩` |
| `coordinateProjection_mass` | Projected squared norm equals regional mass |
| `coordinateProjection_mass_le` | Projection cannot increase mass if `dx ≥ 0` |
| `coordinateProjection_pythagoras` | Retained and complementary projected masses sum to the original mass |
| `coordinateProjection_nonzero_of_mass_pos` | Positive regional mass supplies a nonzero projected coordinate |
| `normalize_coordinateProjection` | At `dx > 0` and positive retained mass, normalization after projection has mass one |

The positivity hypothesis is essential. No theorem normalizes a zero-probability
outcome. There is no stochastic measurement sampler or Gaussian-mask collapse
formalization in this module.

## Reading the Lean tactics

Tactics construct proof terms checked by Lean; they are not numerical tests.
The following covers the tactics used in the new files:

- `intro` introduces a universally quantified object or a hypothesis;
  `constructor` splits a conjunction or equivalence into its logical parts.
  `obtain` unpacks an existing conjunction; `exact` supplies a matching proof.
- `apply` reduces a goal to the hypotheses of a known theorem, for example
  nonnegativity of a product or equality of finite sums term by term.
- `unfold`, `dsimp`, and `change` expose definitions or choose a definitionally
  equal presentation; they do not alter the mathematical object.
- `rfl` proves definitional equality; `rw` rewrites by proved equalities;
  `simp`/`simp only` apply established simplification lemmas. `simp_rw` rewrites
  recursively, including within sum expressions. `simpa ... using` simplifies
  a supplied proof to the goal.
- `ext`/`funext` reduce matrix/function equality to entrywise equality;
  `congr`/`congrArg` reduce or transport equality through a function.
- `by_cases` splits membership/order/equality into exhaustive alternatives;
  `subst` replaces an equal variable. `classical` enables classical decisions
  about real inequalities in finite filters.
- `calc` records an equality chain; `have` names an intermediate proved fact.
  `by_contra` and `push Not` express contradiction and logical negation in
  the nonzero-projection proof.
- `ring` proves commutative polynomial identities after entrywise reduction;
  `abel` cancels additive matrix terms without assuming matrix multiplication
  commutes. `linear_combination` derives the midpoint formula from the implicit
  equation. `linarith` derives that a squared quotient is zero from the zero
  Gaussian exponent; `norm_num` proves elementary numerical inequalities.
- `induction` splits a natural number/list into base and successor/cons cases;
  `generalizing` lets the induction hypothesis apply to the updated state.
  `trivial` supplies a proof of `True` in finite-set membership accounting.

## Verification boundaries and remaining targets

1. **Proved here:** exact mathematical Cayley unitarity, conservation laws,
   regional accounting, barrier/painting invariants, sharp projection properties.
2. **Tested separately in the app:** finite-precision Thomas solves, conservation
   tolerances, scattering scenarios, stationary benchmarks, browser interaction.
   This session did not rerun those tests or assert a new test count.
3. **Not done:** formal verification of TypeScript, array bounds/mutation,
   validation branches, IEEE-754 overflow/roundoff, implementation correspondence,
   continuum convergence, discretization phase error, tunnelling, or benchmark
   correctness. Positive transmitted mass is not itself a tunnelling theorem.

There are no unfinished proof terms in compiled modules. Optional next targets:
Dirichlet kinetic positive definiteness via a boundary-inclusive sum of squared
differences; spectral bounds; the path-profile supremum/subdivision theorems;
normalized Gaussian states; linear-map packaging of sharp projections; and
the exponential/closed-form bridge described in the Slice 4 coverage document.
The qubit/Bloch results themselves have now been added there; the other optional
targets in this list are not presented as already proved.

CI uses the existing lean-action workflow. Documentation deployment was already
disabled; no confirmed workflow defect or remote failure was available to fix.
No remote CI or GitHub Pages success is claimed.
