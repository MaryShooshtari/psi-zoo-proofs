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

## Milestones C and D, and projection extension

- Added `HermitianCayley.lean`: arbitrary Hermitian H on `Fin n`, arbitrary real half timestep; implicit norm conservation, proved invertibility, unconditional unitary-group membership, full inner-product preservation, commutation with H, static energy conservation and repeated-step norm/energy conservation. The grid evolution is definitionally this general transform.
- Added `HamiltonianStructure.lean`: explicit kinetic + real-diagonal potential decomposition, separate Hermiticity proofs, potential-energy formula and nonnegativity for nonnegative V.
- Added `CoordinateProjection.lean`: exact sharp coordinate projection, idempotence, self-adjointness, mass identity/bound, complementary mass decomposition, and normalization after positive-probability projection.
- Debugging: normalized two equivalent complex conjugation spellings before ring algebra; checked actual matrix diagonal-action lemma name; replaced deprecated `push_neg`; removed unused simp arguments and split long lines. No validation was disabled.
- Full build after these additions: `Build completed successfully (4788 jobs).` No Lean warnings.
- Energy proof uses commutation and preservation of inner products, not floating-point evidence. Repeated-step proofs use induction. Positive projection mass is a necessary stated outcome condition, not an assumed inverse or a proof shortcut.

## Further invariants

- Added arbitrary finite disjoint probability partitions and direct spatial-cut accounting.
- Added Cayley right unitarity, negative-time adjoint/reversal, and norm conservation for a finite sequence of changing Hermitian Hamiltonians/timesteps (not energy conservation for changing H).
- Added strict Gaussian positivity, unique peak for positive amplitude/nonzero width, and nearest-segment path-profile bounds, reversal symmetry, on-segment amplitude, and point-path identity.
- One attempt to run three Lean checks in parallel hit `std::bad_alloc`; serial reruns succeeded. No cache/toolchain changes or deletions. Prefer serial checks on this machine.
- Replaced the unnecessary exponential-derivative import with basic exponential + linear-arithmetic imports. This reduced the full dependency job count from 4788 to 4116 without weakening proofs.
- All extensions checked; full build: `Build completed successfully (4116 jobs).` No Lean warnings.

## Documentation and final audit

- Updated README with concise application-to-module/theorem map and removed the outdated statement that static-H energy conservation was unproved.
- Added `docs/VERIFIED_INVARIANTS.md`: complete theorem inventory, explicit assumptions, source links, mathematical proof chain, explanation of every tactic used, and verification boundaries/remaining optional work.
- Added `Checks.lean` to print central statements and axiom dependencies after a build.
- `lake env lean Checks.lean` succeeded. Each of the ten audited central declarations depends only on `[propext, Classical.choice, Quot.sound]`; no custom axioms or `sorryAx`.
- Search of all proof modules found no `sorry`, `admit`, `unsafe`, custom `axiom`, or `native_decide` occurrences. (The search returning no matches naturally exits 1; this was not a Lean build failure.)
- Added 62 theorems across five new subject modules. All are complete under their displayed mathematical hypotheses. The only conditional conservation helper takes the actual implicit step equation; general Cayley invertibility/unitarity is fully discharged.
- Final full build: `Build completed successfully (4116 jobs).` No Lean warnings. `git diff --check` passed; Git only reports its usual Windows LF/CRLF conversion notices.
- No existing theorem was removed or weakened. Toolchain, manifest, dependencies, workflows, and application repository were not modified. No remote CI/deployment claim, push, merge, or PR.
- Core milestones A–E are complete. Optional kinetic positivity/spectral results, path supremum/subdivision, continuum and floating-point verification remain explicitly out of scope and unclaimed.
