# Autonomous proof development log

## Audit

- Started on clean `master`, commit `8b7233c`; created `feat/slice2-formal-invariants`.
- Read all existing Lean modules, README, toolchain/Lake configuration, and all three workflows.
- Baseline: `lake build` → `Build completed successfully (4092 jobs).`
- Existing infrastructure already proves concrete Dirichlet Hamiltonian Hermiticity, reality of energy, CN unique solvability, norm preservation and unitarity.
- Inspected sim-core `regions.ts`, `potential.ts`, `hamiltonian.ts`, `crankNicolson.ts` in the application repository (read-only).
- Region code includes endpoints; interior-state proofs omit the known zero endpoints. Gaussian painting uses maximum, not addition, and validates a cap rather than truncating terrain.
- CI runs lean-action; docgen is explicitly disabled. No observed remote failure or confirmed configuration defect; no workflow change warranted. Remote CI/deployment not checked.

## Plan

1. Regional probability finite-set invariants and ordered spatial partition.
2. Gaussian bounds and reusable pointwise-maximum painting algebra.
3. Extend Hamiltonian/CN infrastructure, prioritizing general Hermitian Cayley algebra and repeated evolution/static energy.
4. Optional exact coordinate projection, documentation, final validation and local commits.

Each milestone must compile independently and via `lake build`. No toolchain/cache changes or application edits.

## Milestones A and B

- Added `RegionProbability.lean`: nonnegative masses, monotonicity/bounds, disjoint-union accounting, normalized three-part partitions, and ordered spatial-cut partition.
- Added `PotentialLandscape.lean`: Gaussian bounds/center maximum; maximum stamp monotonicity, idempotence, order independence, validated and explicitly clipped cap contracts, finite-list bound preservation.
- Both modules checked independently with `lake env lean` (exit 0, no diagnostics).
- Full build: `Build completed successfully (4782 jobs).` No Lean warnings.
- Proof techniques: existing nonnegative norm-square and finite-sum lemmas; ordered-real cases for spatial cuts; exponential monotonicity; lattice identities for maximum; induction for a list of stamps.
