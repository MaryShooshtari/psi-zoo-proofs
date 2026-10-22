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

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and use the versions already
pinned by `lean-toolchain` and `lake-manifest.json`; do not substitute a newer
Lean or Mathlib version. From this repository:

```bash
lake exe cache get
lake build
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
- Static-H energy conservation over time (numerically tested in the app);
  the current formal Hamiltonian result proves reality of the energy form.
- Rendering, playback, general measurement updates, Bloch dynamics, or entanglement.

The application tests supply separate numerical evidence, with stated
conservation budgets and continuum comparison tolerances. Exact unitarity does
not eliminate spatial dispersion or time-discretization phase error. A Gaussian
localization mask and an exact coordinate projection are different objects.
