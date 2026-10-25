# Slice 3: finite-resolution position measurement

All declarations are in `PsiZoo`; general theorems are in
`PsiZoo.MeasurementResponse`. These are exact real/complex mathematical proofs,
not a verified translation of TypeScript. The pinned toolchain is unchanged.

## Implementation correspondence

Inspected sources in the adjacent simulation repository:

- [measurement.ts](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/src/measurement.ts):
  `positionMeasurementProbabilities`, `measurePosition`, and private `prepareMeasurement`.
- [measurement.test.ts](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/tests/measurement.test.ts).
- [grid.ts](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/src/grid.ts): `normSquared`.
- [observer notebook](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/web/src/content/notebook/observer.md).

For `count = n + 2`, Lean index `i : Fin n` corresponds to TypeScript site
`i.val + 1`. Both fixed zero Dirichlet endpoints are omitted, so their norm
contributions and outcome masses are zero. `interiorCoordinate x0 dx i` is
`x0 + (i.val + 1) * dx`; `interiorCoordinate_sub` proves that differences are
`(j.val - i.val) * dx` (the subtraction is in the reals).

Let `N = weightedSquaredNorm dx psi = dx * sum_i normSq (psi i)` with `dx > 0`.
`MeasurementResponse.kernel j i` means **K(j|i)**: observed output first,
input second. Nonnegativity and `sum_j K(j|i) = 1` are the general response
structure's fields. Rows need not sum to one, and the normalized Gaussian
need not be symmetric near boundaries even though its raw weights are symmetric.

The actual Gaussian constructor, rather than an assumed stochastic Gaussian, is

```
G(j,i) = exp(-(x_j - x_i)^2 / (2 sigma^2))
Z(i)   = sum_k G(k,i)
K(j|i) = G(j,i) / Z(i).
```

It requires `0 < n` and `sigma > 0`. The elementary exponential-positivity
lemmas hold even without positive sigma, but the physical constructor imposes
it explicitly. Each input site itself supplies a positive summand in `Z(i)`.
No continuum normalization constant and no extra outcome `dx` are used.
The resolution is the untruncated detector width, not the posterior width.

The general definitions match the API's exact arithmetic formulas:

```
P(j)       = (dx * sum_i K(j|i) * |psi_i|^2) / N
M_j psi_i  = sqrt(K(j|i)) * psi_i
psi'_i     = (M_j psi)_i / sqrt(N * P(j)).
```

`matrix j` is Mathlib's complex diagonal matrix of these square roots;
`matrix_mulVec` proves its action is `mask j`. TypeScript divides by `sqrt N`
and `sqrt P` separately; these equal division by `sqrt(N*P)` for positive
`N,P` in exact real arithmetic. The final API renormalization is then the
identity mathematically. This correspondence is editorial; it does not certify
execution of the JavaScript code.

## Exact theorem inventory

In [FiniteMeasurement.lean](../PsiZooProofs/FiniteMeasurement.lean), write `R`
for any `MeasurementResponse n`. Unless noted, `n` may even be zero.

| Name (under `MeasurementResponse`) | Statement and hypotheses |
| --- | --- |
| `matrix_mulVec` | `(R.matrix j).mulVec psi = R.mask j psi` |
| `probability_nonneg` | `dx > 0` implies `0 ≤ R.probability dx psi j`; zero states are permitted for this inequality only |
| `sum_probability` | `dx > 0` and `∃ i, psi i ≠ 0` imply `sum_j R.probability dx psi j = 1` |
| `normSq_mask` | `normSq (R.mask j psi i) = R.kernel j i * normSq (psi i)` |
| `probability_eq_norm_ratio` | `P(j) = weightedSquaredNorm dx (R.mask j psi) / weightedSquaredNorm dx psi` |
| `completeness` | `sum_j (R.matrix j)ᴴ * R.matrix j = 1` as complex matrices |
| `mass_eq_norm_mul_probability` | Positive `dx`, nonzero `psi`: masked norm equals `N * P(j)` |
| `conditional_normalized` | Positive `dx`, nonzero `psi`, `P(j) > 0`: `weightedSquaredNorm dx (R.conditional dx psi j) = 1` |
| `conditional_positive_ray` | Under the same hypotheses and `K(j|i) > 0`, there exists `a : ℝ`, `a > 0`, with `psi'_i = (a : ℂ) * psi_i` |
| `relative_phase_algebra` | `(M_j psi)_i * conj((M_j psi)_k) = (sqrt K(j|i) * sqrt K(j|k) : ℂ) * (psi_i * conj(psi_k))` |
| `conditional_cn_normalized` | The conditional state above remains weighted-unit-normalized after `crankNicolsonEvolution dx dt V`, for any real `dt` and real `V` |

The positive-ray result applies in particular to nonzero surviving components:
no branch-dependent complex `arg` is needed. The pairwise coherence identity
makes relative phase preservation algebraic. Zero multipliers erase a component;
no phase is asserted for a zero component. For the Gaussian every multiplier is
strictly positive. The totalized Lean definitions exist at zero denominators,
but there is **no** claim of physical normalization or valid conditioning there.

In [GaussianMeasurement.lean](../PsiZooProofs/GaussianMeasurement.lean):

- `gaussianResponseWeight_pos`: `G(j,i) > 0`.
- `gaussianResponseDenominator_pos`: `Z(i) > 0` for every input site.
- `gaussianResponse`: constructs the general response with proved nonnegativity
  and column normalization; these are not additional Gaussian assumptions.
- `gaussian_kernel_pos`: `K(j|i) > 0` (hence nonnegative).
- `gaussian_sum_column`: `sum_j K(j|i) = 1`.
- `gaussian_completeness`: the Gaussian matrices satisfy `sum_j M_jᴴ M_j = I`.
- `gaussian_sum_probability`: `sum_j P(j) = 1` for positive `dx`, nonzero input.
- `gaussian_probability_pos`: every outcome has `P(j) > 0` under those hypotheses.
- `gaussian_conditional_normalized`: positive-probability Gaussian conditional
  states have weighted squared norm one.

The module contains checked examples on two- and three-site grids: Gaussian
column normalization, delta column normalization, a nonzero state's normalized
outcome probabilities, and both Gaussian and delta normalized conditional states.

## Existing proof reuse

`deltaResponse n` has `K(j|i) = if j = i then 1 else 0`.
`delta_mask_eq_coordinateProjection` identifies its mask with the existing
`coordinateProjection {j}`. `delta_mask_mass` then **reuses**
`coordinateProjection_mass`, rather than reproving the regional mass result.
All general measurement theorems apply to this delta response as well.
A finite-width Gaussian is a diagonal POVM, **not an exact projection**.
There is no sigma-to-zero limit theorem in this work.

`conditional_cn_normalized` reuses
`crankNicolsonEvolution_preserves_normalization`. Its operator is the same
one proved unitary in `CrankNicolsonUnitarity.lean`; no CN unitarity proof is
duplicated. This does not say measurement conserves energy, nor prove
post-measurement spreading or variance claims.

## How the proof tactics express the mathematics

- `apply` reduces a claim to an existing lemma's hypotheses; `exact` supplies
  an already checked proof. Structure fields package the two stochastic laws.
- `Finset.sum_nonneg` proves each finite sum nonnegative term by term;
  `Finset.sum_pos'` adds a strictly positive witness summand.
- `rw` rewrites by equalities. `Finset.sum_comm`, `sum_mul`, `mul_sum`, and
  `sum_div` interchange finite sums and factor constants. Column normalization
  leaves exactly the original norm; `div_self` cancels its nonzero value.
- `simp`/`simp_rw` expand definitions and use proved identities, including
  `normSq` of products/divisions and `sqrt a * sqrt a = a` for `a ≥ 0`.
- `ext`/`funext` prove matrix/function equality entrywise; `by_cases` separates
  diagonal from off-diagonal entries. Matrix multiplication of diagonals proves
  completeness, with conjugation fixing the real square roots.
- `congr`/`congrArg` transport equality through functions; `exact_mod_cast`
  transports a real square-root identity to complex numbers.
- `field_simp` clears the explicitly nonzero input norm; `ring` checks polynomial
  rearrangements in the coordinate difference and complex phase formulas.
- `refine` constructs the explicit positive scalar; `obtain` extracts the
  nonzero coordinate witness. `norm_num` proves small exact numerical facts in
  examples, not floating-point approximations or a native computation shortcut.

## Outside the formal model

Not proved: IEEE-754 accuracy or error budgets; exponential/square-root library
implementation; extreme resolutions; underflowed Gaussian tails (exact G is
strictly positive); overflow/underflow of norms; safe-integer and finite-value
validation; storage length/interleaving; input immutability; final roundoff
renormalizations of probabilities and posterior; RNG correctness, consumption,
CDF sampling, last-positive-bin fallback, or empirical frequencies. There is no
verified compiler/translation connection, continuum/quadrature/convergence
claim, variance/localization bound, energy-conservation claim for measurement,
or proof of notebook rendering. The simulation tests cover these separately.

## Reproduce

```
lake build
lake env lean PsiZooProofs/FiniteMeasurement.lean
lake env lean PsiZooProofs/GaussianMeasurement.lean
lake env lean MeasurementChecks.lean
git diff --check
```

`MeasurementChecks.lean` prints central theorem types and axiom dependencies.
Standard Lean/Mathlib foundations (`propext`, `Classical.choice`, `Quot.sound`)
are allowed; no additional axiom or proof placeholder is introduced.
