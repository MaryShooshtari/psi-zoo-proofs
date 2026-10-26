# Psi Zoo proofs

Lean 4 + Mathlib companion to [Psi Zoo](https://github.com/MaryShooshtari/psi-zoo),
a browser simulation of Schrödinger wave-packet dynamics. This independent
repository proves selected **exact mathematical statements**, not correctness
of the TypeScript implementation or the entire application.

## Start here

- **Watch and run:** [simulation and local setup](https://github.com/MaryShooshtari/psi-zoo#local-development).
- **Understand:** [lab notebook: why the wave packet keeps its probability](https://github.com/MaryShooshtari/psi-zoo/blob/main/docs/notebook/crank-nicolson.md).
  Starts with a general-reader explanation, then gives the derivation and exact
  mathematical statement-to-Lean map.
- **Compare with experiment:** [Gaussian spreading and numerical conservation results](https://github.com/MaryShooshtari/psi-zoo/blob/main/docs/FREE_GAUSSIAN_VALIDATION.md).
- **Check the proofs:** follow the source map below and run `lake build`.
- **Inspect Slice 2 and general Cayley results:** [verified invariants, assumptions,
  theorem inventory, and proof explanations](docs/VERIFIED_INVARIANTS.md).

## Completed Crank–Nicolson proof chain

Assume positive real spacing `dx`, any real `dt` (including zero and negative),
and a fixed real potential `V : Fin n → ℝ`. States `Fin n → ℂ` contain only
interior Dirichlet grid points; omitted endpoint values are zero. Units are
hbar = m = 1. All natural dimensions are allowed, including `n = 0` and `n = 1`.

Write `H = gridHamiltonianMatrix dx V`, `A = I + i(dt/2)H`,
`B = I - i(dt/2)H`, and `U = A⁻¹ * B`. The existing probability quantity is
`P(psi) = weightedSquaredNorm dx psi = dx * ∑ j, |psi j|²`, not the default
function-space norm. The inner product conjugates its first argument.

All declarations below are in namespace `PsiZoo`.

| Source | Exact result and principal declarations |
| --- | --- |
| [ComplexBasics.lean](PsiZooProofs/ComplexBasics.lean), [GridNormalization.lean](PsiZooProofs/GridNormalization.lean) | Finite sums of squared magnitudes and the existing `weightedSquaredNorm`; normalization of nonzero states |
| [GridInnerProduct.lean](PsiZooProofs/GridInnerProduct.lean) | `gridInnerProduct_self`: self inner product equals the real weighted squared norm; positive definiteness at positive spacing |
| [GridHamiltonian.lean](PsiZooProofs/GridHamiltonian.lean) | `gridHamiltonianMatrix_isHermitian`: Hᴴ = H; `gridHamiltonian_energy_im_eq_zero`: Im ⟨psi,H psi⟩ = 0 |
| [CrankNicolsonConservation.lean](PsiZooProofs/CrankNicolsonConservation.lean) | `crankNicolsonStep_weightedSquaredNorm`: A psiNext = B psiPrev implies P(psiNext) = P(psiPrev) |
| [CrankNicolsonInvertibility.lean](PsiZooProofs/CrankNicolsonInvertibility.lean) | `crankNicolsonLeftMatrix_isUnit`: A is invertible; `crankNicolsonStep_existsUnique`: every previous state has exactly one implicit next state |
| [CrankNicolsonEvolution.lean](PsiZooProofs/CrankNicolsonEvolution.lean) | `crankNicolsonEvolution`: U = A⁻¹ B; `crankNicolsonLeftMatrix_mul_evolution`: AU = B; explicit solution, uniqueness, norm preservation, and U(dx,0,V) = I |
| [CrankNicolsonUnitarity.lean](PsiZooProofs/CrankNicolsonUnitarity.lean) | `crankNicolsonEvolution_conjTranspose_mul_self`: Uᴴ U = I; `crankNicolsonEvolution_mul_conjTranspose_self`: U Uᴴ = I; `crankNicolsonEvolution_mem_unitaryGroup`: U ∈ Matrix.unitaryGroup (Fin n) ℂ; `crankNicolsonEvolution_inv_eq_conjTranspose`: U⁻¹ = Uᴴ |

The proof order is deliberate: conditional conservation proves trivial kernel;
finite-dimensional algebra gives invertibility; inverse cancellation constructs
the explicit evolution; adjoint algebra then proves matrix unitarity. Unitarity
is not an assumption used to bootstrap its own proof.

The [notebook entry](https://github.com/MaryShooshtari/psi-zoo/blob/main/docs/notebook/crank-nicolson.md)
contains the polarization argument, adjoint derivation, complete CN theorem map,
and measured TypeScript conservation results. Links between the repositories are
editorial, not a mechanically verified implementation correspondence.

## Slice 2 invariants and general Hermitian evolution

The following additions are fully proved under their explicit mathematical
hypotheses; in particular, general Cayley unitarity does **not** assume
invertibility. All names are in namespace `PsiZoo`.

| Application property | Lean module | Principal theorem names |
| --- | --- | --- |
| Regional masses are nonnegative and bounded by total mass | [RegionProbability](PsiZooProofs/RegionProbability.lean) | `regionProbability_nonneg`, `regionProbability_le_total` |
| Ordered left/interaction/right cuts account for all mass; normalized partitions sum to one | [RegionProbability](PsiZooProofs/RegionProbability.lean) | `spatial_region_probability_sum`, `regionProbability_partition_normalized`, `regionProbability_partition_sum_one` |
| Gaussian barriers lie in `[0,A]` and peak at their center | [PotentialLandscape](PsiZooProofs/PotentialLandscape.lean) | `gaussianBarrier_nonneg`, `gaussianBarrier_le_amplitude`, `gaussianBarrier_eq_amplitude_iff` |
| Maximum painting is monotone, idempotent, order-independent, and cap-preserving | [PotentialLandscape](PsiZooProofs/PotentialLandscape.lean) | `stampPotential_increases`, `stampPotential_idempotent`, `stampPotential_order_independent`, `stampPotential_fold_bounds` |
| Swept Gaussian profile is bounded and direction-independent | [PotentialLandscape](PsiZooProofs/PotentialLandscape.lean) | `gaussianPathProfile_bounds`, `gaussianPathProfile_reverse` |
| Hamiltonian is kinetic plus real diagonal potential | [HamiltonianStructure](PsiZooProofs/HamiltonianStructure.lean) | `realPotentialMatrix_isHermitian`, `gridKineticMatrix_isHermitian`, `gridHamiltonianMatrix_decomposition` |
| Cayley evolution for any finite Hermitian H has an inverse and is unitary | [HermitianCayley](PsiZooProofs/HermitianCayley.lean) | `cayleyLeft_isUnit`, `hermitianCayley_mem_unitaryGroup` |
| Repeated evolution preserves normalization; negative time reverses evolution | [HermitianCayley](PsiZooProofs/HermitianCayley.lean) | `hermitianCayley_iterate_normalized`, `hermitianCayley_neg_time` |
| Static-H energy is conserved | [HermitianCayley](PsiZooProofs/HermitianCayley.lean) | `hermitianCayley_energy`, `hermitianCayley_iterate_energy`, `crankNicolsonEvolution_energy` |
| Exact sharp projection has regional mass and can be normalized after a nonzero outcome | [CoordinateProjection](PsiZooProofs/CoordinateProjection.lean) | `coordinateProjection_mass`, `coordinateProjection_pythagoras`, `normalize_coordinateProjection` |

The general theorem uses `H : Matrix (Fin n) (Fin n) ℂ` for arbitrary n and a
real **half timestep** `t = dt/2`. It allows zero/negative timesteps and empty
spaces. Probability bounds require nonnegative spacing; physical normalization
requires positive spacing and a nonzero state. Static energy conservation uses
the same H throughout. A sequence of changing Hermitian Hamiltonians still
preserves mass (`hermitianCayley_sequence_norm`), but no energy conservation
is asserted for changing H.

The [detailed guide](docs/VERIFIED_INVARIANTS.md) explains every theorem group,
assumption, tactic, TypeScript source correspondence, and remaining limitation.
Regional mass is not automatically a reflection/transmission coefficient.
Painting uses maximum rather than addition, and validates its cap rather than
silently clipping terrain. Exact projection is not a Gaussian measurement mask.

## Slice 3: finite-resolution Gaussian measurement

[GaussianMeasurement.lean](PsiZooProofs/GaussianMeasurement.lean) and
[FiniteMeasurement.lean](PsiZooProofs/FiniteMeasurement.lean) formalize the exact
finite measurement model behind the simulation's
[`positionMeasurementProbabilities` and `measurePosition`](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/sim-core/src/measurement.ts).
The [observer notebook](https://github.com/MaryShooshtari/psi-zoo/blob/main/packages/web/src/content/notebook/observer.md)
explains the Born-rule experiment.

On interior sites `Fin n`, the detector uses
`G(j,i) = exp(-(x_j-x_i)^2/(2 sigma^2))` and
`K(j|i) = G(j,i) / sum_k G(k,i)`: normalization is over observed outcomes
for **each input position**, including near walls. States have squared norm
`N = dx * sum_i |psi_i|^2`. Outcome masses are
`P(j) = dx * sum_i K(j|i)|psi_i|^2 / N`, and the conditional update is
`sqrt(K(j|i))*psi_i / sqrt(N*P(j))`.

Principal checked results are `MeasurementResponse.probability_nonneg`,
`MeasurementResponse.sum_probability`, `MeasurementResponse.completeness`
(the actual matrix identity `sum_j M_jᴴ M_j = I`),
`MeasurementResponse.probability_eq_norm_ratio`,
`MeasurementResponse.conditional_normalized`,
`MeasurementResponse.conditional_positive_ray`, and
`MeasurementResponse.relative_phase_algebra`.
`gaussianResponseDenominator_pos`, `gaussian_sum_column`,
`gaussian_completeness`, `gaussian_sum_probability`, and
`gaussian_conditional_normalized` establish the normalized Gaussian instance.
Positive spacing, nonzero input, positive resolution and dimension, and
positive conditioning probability are explicit where required.

`delta_mask_eq_coordinateProjection` connects the ideal delta detector to the
existing sharp projection proof. A Gaussian POVM is **not** an exact coordinate
projection. `MeasurementResponse.conditional_cn_normalized` reuses existing
CN norm preservation; it makes no measurement energy-conservation claim.
See the [complete theorem inventory, implementation map, tactic explanations,
and numerical exclusions](docs/GAUSSIAN_MEASUREMENT.md).

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and use the versions already
pinned by `lean-toolchain` and `lake-manifest.json`; do not substitute a newer
Lean or Mathlib version. From this repository:

```bash
lake exe cache get
lake build
lake env lean Checks.lean  # display central theorem types and axiom dependencies
```

The cache command downloads available Mathlib build artifacts; `lake build`
checks the project modules imported by [PsiZooProofs.lean](PsiZooProofs.lean).
No npm packages are needed here. Keep the app's `node_modules` and this repo's
`.lake` cache separate and out of version control.

## What is not formally verified

- The TypeScript coefficient construction, Thomas solver, memory mutation,
  input-validation paths, or their correspondence to these Lean definitions.
- IEEE-754 rounding-error bounds or success at extreme numerical scales.
- Approximation of the continuum PDE, Gaussian spreading, or convergence rates.
- Tunnelling, stationary benchmark correctness, or interpretation of raw regional
  mass as asymptotic scattering coefficients.
- Kinetic positive definiteness, spectral bounds, or a Gaussian path-envelope
  supremum/subdivision theorem (the implemented nearest-point profile has
  formal bounds and direction symmetry).
- Rendering, playback, floating-point measurement execution or sampling, Bloch
  dynamics, or entanglement. The exact finite Gaussian POVM is proved above.

The application tests supply separate numerical evidence, with stated
conservation budgets and continuum comparison tolerances. Exact unitarity does
not eliminate spatial dispersion or time-discretization phase error. A Gaussian
localization mask and an exact coordinate projection are different objects.
