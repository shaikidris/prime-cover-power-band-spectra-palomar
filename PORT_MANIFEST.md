# Declaration-level port manifest

## Current admission map — D31, 9 September 2026

The D31 rebase in `PALOMAR_RELEASE_CONE.md` controls new ports. Historical
builds below certify their literal statements, not automatic compatibility
with the repaired paper or new global estimates. No code was ported in this
planning pass.

| Planned owner / R-task | Reuse candidate already located | Required check or new assembly |
|---|---|---|
| `FirstExitTarget`, `FullSpectrumTransfer` / R2 | `exactPrincipalMoleculeSupport`, `exactPrincipalMoleculeMatrix`, S1 and S2 roots already here | full-star/singleton support, principal matrix, normalization, positivity and exact target/ordered-index match; fresh build |
| `AlmostAllSpectralBudget` / R3 | historical `sum_sq_hermitianEigenvalues₀_sub_le_matrixFrobeniusNorm_sq`, `abs_hermitianEigenvalues₀_add_sub_le_matrixL2OperatorNorm` | finite Lemma 5.4 with low complement, positivity, and unchanged index; weak sorting contraction |
| same owner / R4 | `ExactProjectedMolecules` identities and `exactOneExitNormalizedMoleculeFamilyFrame_isometry`, `exactOneExitNormalizedMoleculeFamilyResidual_frobenius_sq_le` | port only consumed declarations; prove actual near-Gram, global HS and corrected operator estimates rather than retaining their premises |
| same owner / R5 | pinned PNT and spectral/compression primitives | energy-weighted full-prefix complement estimate; no BHP rank offset or internal-core capacity |
| `AlmostAllAssembly` / R6--R7 | finite Markov/dyadic/scalar facts from historical consumers where their types match | actual ordered mean-square/tail, terminal exception rate, initial-segment accounting, and public D31 assembly |

The old `ExactMoleculeTargetTransport` conclusion uses an inverse sorting
permutation. It is not the same-index bridge required by D31; reuse scalar
helpers only, then prove the complete-prefix value comparison.

Before each port, record exact source declaration, file hash/commit, minimal
dependencies and destination. These are reuse candidates, not a closure
certificate or permission to import a complete historical module. Shared
proofs are extracted once. `AlmostAllArithmetic` is no longer admitted.

## Historical extraction provenance

The historical repository is a proof laboratory, not a dependency of this
release.  Rows enter this manifest before proof code enters the Palomar cone.
`FILE-SHA256` denotes an exact working-tree source snapshot when the source
declaration is newer than the last immutable source commit.

Historical source repository:
`shaikidris/prime-cover-power-band-spectra-formalization`.

Last immutable source commit:
`a6f8efa91346a6401ba9191d1b12f8552727e380`.

| Release owner | Extracted object | Historical source | Provenance | Port status |
|---|---|---|---|---|
| `Core` | shared vertex and allowed-prime definitions | `PrimeCoverPowerBand/Basic.lean` | commit `a6f8efa91346a6401ba9191d1b12f8552727e380`; file `61d0f78c4ea075d99ccab4153abfafbf8405da92035c7a31f5438735d6529cae` | ported |
| `Core` | power-band and D26' scale definitions | `PrimeCoverPowerBand/PowerBands.lean` | `FILE-SHA256 a8b8998bdf52ad0fa65a5f7eb917eaa1a04380ef5390b0aad83f4a16cc65b6f6`; immutable checkpoint pending | ported definitions only |
| `Core` | exact first-exit target definitions | `PrimeCoverPowerBand/TargetEnergies.lean` | commit `a6f8efa91346a6401ba9191d1b12f8552727e380`; file `ab50140ad4cf62ad9c2578397f4525e5d91446558adfed43a7e2190ab82ef569` | ported |
| `Core` | exceptional-set definitions | `PrimeCoverPowerBand/HeadlineAssembly.lean` | commit `a6f8efa91346a6401ba9191d1b12f8552727e380`; file `098c5ff4e8bc07c3c82e7cf9a13613070095a363653b64f724ab92a9f6346c9d` | ported definitions only |
| `FirstExitTarget` | `eventually_powerRange_exactPrincipalMoleculeRoot_targetDefect_le` | `PrimeCoverPowerBand/ExactMoleculeFiniteCorrection.lean` | `FILE-SHA256 e5b0843763e44eae3ffb3d4e6228a3838e9595fe2680efb061e4c60806cdbfab`; immutable checkpoint pending | ported; builds; standard axioms; provenance promotion pending |
| `FullSpectrumTransfer` | `eventually_powerRange_fullAdjacency_oneExit_sq_comparison` | `PrimeCoverPowerBand/FullSpectrumTargetTransport.lean` | `FILE-SHA256 643a547933859474b18e8c76e88664c5499d5bd4fc1452e37c53db1695ad5066`; immutable checkpoint pending | ported; builds; standard axioms; provenance promotion pending |
| `TerminalSchur` | finite coherent reduction plus `eventually_powerRange_exactOneExitLocalCoherentCompressionResidual_bound` | selected historical declarations plus the checked replacement in `/private/tmp/ReverseCoreResearch.lean` | clean owner `FILE-SHA256 0c1a7c81c898e1c5f9b487127a157da984ac5e769370c1cb5095594b161ef159`; research file `e17408db6c55089c6df0aa5a86797e6ea8f3c632f17e7a524eae91ae39adc617` | ported; builds; all three power-range budgets closed; standard axioms |

## First-layer source slices

These lists are migration inventories, not imports approved for the release.
They identify the first project-local layer beneath the two shared producers.
Each owner receives the checked root proof and only the declarations from
these files that the proof term actually consumes.

### S1: exact first-exit target

Historical direct imports:

- `ExactPrincipalMoleculeGraphBridge.lean`
- `ExactBoundarySignedResponse.lean`
- `ExactBoundaryKernelReturn.lean`
- `ExactMoleculeInteriorMass.lean`
- `PowerBandDegreeRatios.lean`
- `BoundaryLeafSquareSum.lean`
- `TargetEnergies.lean`

The historical file also imports three Paper I modules.  Those remain pinned
dependencies and are not copied: `ActualFiniteCorrection`,
`FixedCenterCorrectionBridge`, and `LogarithmicWindowFeshbachRemainder`.

### S2: full-adjacency to one-exit transfer

Historical direct imports:

- `ExactMoleculeTargetTransport.lean`
- `ThresholdCounting.lean`
- `RCLikeOrderedCompressionInterlacing.lean`
- `LargePrimePositiveProjectionCommute.lean`
- `OneExitCoreNonpositive.lean`
- `RealTwoStageSchurComparison.lean`
- `PowerBandDegreeRatios.lean`

The two lists contain 8,202 historical source lines before transitive imports.
Their historical module-level union reaches roughly 30,000 lines because the
proof laboratory imports broad neighboring developments.  That module cone is
explicitly rejected.  Porting is declaration-level and build-driven.

## Migration rule

For each root, migration proceeds in this order:

1. copy the checked root declaration without changing its theorem statement;
2. copy a missing project-local helper only when Lean reports it as consumed;
3. place that helper in the root's preapproved owner rather than reproducing
   the historical file layout;
4. reuse a pinned Paper I declaration whenever it already owns the result;
5. record any newly written adapter separately from transplanted proof code;
6. stop when the owner and selected root compile, then remove unused imports
   and declarations before opening the next owner.

No historical umbrella module, audit module, alternate proof route, or unused
coordinate implementation may be migrated.

## S1 extraction result

- Owner: `PrimeCoverPowerBand/FirstExitTarget.lean`.
- Root: `eventually_powerRange_exactPrincipalMoleculeRoot_targetDefect_le`.
- Historical textual closure: 272 named declarations across 34 files, 9,399
  declaration-span lines.
- Clean owner: 9,956 lines including imports, owner documentation, retained
  local instances, and the checked proof bodies.
- Boundary adapters: one general private `symmetricEigenvalues_cast` helper
  shared by the merged slices, and `ε := eps` changed to `eps := eps` to match
  the pinned Paper I declaration.
- Build: `lake build PrimeCoverPowerBand.FirstExitTarget`, 4,184 jobs, exit 0.
- Root axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Promotion status: proof closed in this repository; immutable source
  checkpoint remains a provenance gate.

The four dirty-source files above are jointly covered by working-tree patch
SHA-256
`033edc9968703d142f9fbee055495c8b60138065364a85f8a3af6ac5b6851997`.
This content hash prevents accidental drift during extraction, but it does not
replace the required immutable source checkpoint before theorem promotion.

## S2 extraction result

- Owner: `PrimeCoverPowerBand/FullSpectrumTransfer.lean`.
- Root: `eventually_powerRange_fullAdjacency_oneExit_sq_comparison`.
- Clean owner: 4,529 lines before the statement-surface amendment; the owner
  contains the declaration-level closure of the checked transfer proof and no
  local `sorry`.
- Boundary repair: the extractor had omitted the source `[simp]` attributes on
  `rclikeShiftedEndomorphism_apply` and the two inverse-application lemmas.
  Restoring those three source attributes repaired four elaboration mismatches
  without changing theorem statements or proof bodies.
- Build: `lake build PrimeCoverPowerBand.FullSpectrumTransfer`, 4,217 jobs,
  exit 0.
- Source snapshot: historical root file SHA-256
  `643a547933859474b18e8c76e88664c5499d5bd4fc1452e37c53db1695ad5066`;
  clean owner SHA-256
  `6370dc511d20f83d36b5fbe0a3c6177be971a0aa0fe2e68241b16fa97bd6bee3`
  before the documentation-only S2 label correction.
- Promotion status: proof closed in this repository; immutable historical
  source checkpoint and selected-root axiom audit remain release gates.

## TerminalSchur extraction result

- Owner: `PrimeCoverPowerBand/TerminalSchur.lean`.
- Root:
  `exactOneExitLocalCoherentCompressionResidual_frobenius_sq_le_core_kernel`.
- Clean owner: 4,203 lines. It imports only `FullSpectrumTransfer` plus the
  Mathlib interval-finset module needed by the selected finite closure.
- The historical slices were taken from the following dirty-tree snapshots:

  | Historical file | SHA-256 | Principal consumed ranges |
  |---|---|---|
  | `OrderedThresholdBracketing.lean` | `0a153e59e2be1f77ef9b67523afc983ccc035a147f784e5d01e487185a58cf39` | selected coherent residual and Frobenius assembly |
  | `ExactMoleculeProjectionTail.lean` | `c57257ce3642d70958aea17f466807dacbde9d3b0569c1ba2cbb01d8e4141010` | lines 24--80 |
  | `ExactMoleculeExteriorResidual.lean` | `a1663ff738de71105218d260bde0cb9baccfb5b2698ce00e3f387798c7a8ff5e` | lines 23--198 |
  | `CollisionBudget.lean` | `7ce4371eccdc17904961aedb1f9d12e41d2dc5ad5d8a40f71df83424fdf58e68` | lines 21--447 |
  | `SignedStarCoupling.lean` | `ae7736534abd7602eed3eb751b37dfb674d04911fe797f06ae0320cc9670098e` | lines 19--236 |
  | `BoundaryTargetResolvent.lean` | `54db9a4bad06d7ae04d0c883355a43211b3fb7f1cab7b607b56ef152468d4c8a` | down-star resolvent identities, principally lines 78--229 and 295--456 |
  | `ExactBoundarySignedResponse.lean` | `e3730a0cfaceef7e037b3b3e367de65bebdf631af86906014554f2b0341dca14` | signed response and canonical target identities, principally lines 550--902 and 1362--1404 |

- Boundary repairs: the two historical nonnegativity failures were repaired
  with explicit `zero_mul` simplification before applying square/product
  nonnegativity. One missing canonical down-target evaluation was ported from
  the historical validated slice.
- Build: `lake build PrimeCoverPowerBand.TerminalSchur`, 4,218 jobs, exit 0
  for the finite root; the same target later rebuilt at 4,218 jobs, exit 0,
  637s after the boundary-kernel producer was added.
- Local trust scan: no `sorry`, `admit`, project `axiom`, `native_decide`, or
  `Lean.ofReduceBool` in the owner.
- Clean owner SHA-256 after the boundary-kernel producer:
  `bab6c5b9114223ca2f85237cbded1d45d429ef4e8f83e0ac388b14bdc3a785e6`.
- Logical boundary: the finite theorem takes `coreBudget`,
  `boundaryKernelBudget`, and `residualBudget` as premises. The summed
  theorems
  `eventually_powerRange_sum_exactPrincipalMoleculeBoundaryKernel_sq_le`
  and `eventually_powerRange_sum_exactPrincipalMoleculeResidual_sq_le`
  instantiate `boundaryKernelBudget` and `residualBudget` on every fixed
  power range `theta < 1/2`.
- Clean owner SHA-256 after the residual-energy producer:
  `4e151cb7d8eb4ab59ce496e6a75c59cf4d03b27557dd5cbca38e04a6b1b61301`.
- Axiom print of both summed producers: `propext`, `Classical.choice`,
  `Quot.sound`.
- The final checked replacement avoids the failed reverse-Gram charge. It
  proves a direct bound in both orientations and sums the reciprocal output
  mass harmonically. The resulting
  `eventually_powerRange_sum_coherent_core_entry_sq_le` closes `coreBudget`.
- `eventually_powerRange_exactOneExitLocalCoherentCompressionResidual_bound`
  now instantiates all three budgets in the finite coherent reduction.
- Final clean owner SHA-256:
  `0c1a7c81c898e1c5f9b487127a157da984ac5e769370c1cb5095594b161ef159`.
  Targeted owner build: 4,218 jobs, exit 0. Submission-audit build: 4,220
  jobs, exit 0. Both new axiom prints contain only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Historical next-migration table (superseded for D31)

The following historical declarations were checked adapters or finite
consumers.  They are not themselves proofs of the analytic inputs and must not
be ported until the corresponding input was closed. The BHP rows still apply
to the later sharp route; the Guth--Maynard row is retired from the D31 plan.

| Future owner | Candidate historical declarations | Gate before migration |
|---|---|---|
| `TerminalArithmetic` | `BakerHarmanPintzAllowedShortIntervalInput.reciprocal`, `.terminalReciprocal`, `.eventually_targetClusterCount_lower`, `.eventually_sortingClusterCount_lower`, `.eventually_targetEnergy_strictAnti_of_sortingGap`, `.eventually_realDyadicTargetSort_position_bounds`, and `BakerHarmanPintzShortIntervalInput.allowed` | a compiled BHP `21/40` input theorem |
| `TerminalAssembly` | terminal-scale producers for the three `TerminalSchur` budgets and the minimal buffered threshold-count consumers | BHP input plus explicit asymptotic bounds for the compiled finite interface |
| `AlmostAllArithmetic` | real-to-natural/power-band adapters for Guth--Maynard Corollary 1.4 and the checked reciprocal-tiling/excision chain | a compiled direct exceptional-set input theorem |

The historical public `PrimeCoverPowerBandSolution.lean` does not supply any
of these gates: its prescribed-rank and terminal-density roots are deliberate
`sorry` holes.  It remains a statement/assembly map only.

The `TerminalSchur` historical sources remain an uncommitted working-tree
batch and are therefore provenance rather than a dependency. Their selected
closure has now been repaired and checked in the clean owner recorded above.
