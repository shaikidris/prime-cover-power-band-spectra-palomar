# Declaration-level port manifest

## Current admission map — D31, 9 September 2026

The D31 rebase in `PALOMAR_RELEASE_CONE.md` controls new ports. Historical
builds below certify their literal statements, not automatic compatibility
with the repaired paper or new global estimates. R1--R8 are validated locally.
The 10 September continuation first matched the R5 source hashes to its saved
final validation. R6's separate fresh build, axiom and control evidence is
recorded below. R7's fresh exit evidence is recorded after its admission.
D31 is 8/8 (100%), MG4 2/2 COMPLETE, selected public proofs 2/4.
R8 scoped verification is closed; Palomar submission readiness is PARTIAL.

### R1 statement amendment: interface brief

Consumer: revised Theorem 1.3 and Corollary 1.4, not a new density API.
Keep the existing finite allowed-vertex count divided by `X^theta` and the
standard `Tendsto ... atTop (nhds 0)` convention. Mathlib's `Finset.card`
and filter operations suffice; `Finset.dens` uses the ambient finite cardinality
instead and is not the manuscript normalization. No measure-space, arbitrary
filter, or bundled exceptional-set abstraction is introduced.

- Required: transparent D31 error scale, actual failure sets on the full and
  terminal power ranges, terminal `O(X^theta/log(X)^R)` for every fixed `R>0`,
  global density zero with the SAME error constant/exponent, and the sub-block
  margin `min(theta/2,1/2-theta)`.
- Calibration: a regular centre with zero defect is good once `X>1` and the
  comparison constant is positive. An irregular centre is bad even when Lean's
  totalized division makes its numerical correction finite. Empty vertex sets
  cause no asymptotic assertion; `X` tends to infinity, with `theta>0` fixed.
- Deferred: set-union/monotonicity lemmas, quantitative density calculus, and
  endpoint generalizations until a named assembly consumer needs them.
- Not valid: a single `D` working for every `R`, or a terminal exception rate
  silently covering the omitted initial segment. The quantifier order is
  `S, theta, R`, then `D, C, Cexc`, then eventual `X`.
- Scope: synchronize Core, Challenge, Solution, both selection accounts and
  metadata without changing the sharp theorem pair. Four deliberate Solution
  holes remain; statement alignment is not proof completion.

| Planned owner / R-task | Reuse candidate already located | Required check or new assembly |
|---|---|---|
| `FirstExitTarget`, `FullSpectrumTransfer` / R2 | `exactPrincipalMoleculeSupport`, `exactPrincipalMoleculeMatrix`, S1 and S2 roots already here | full-star/singleton support, principal matrix, normalization, positivity and exact target/ordered-index match; fresh build |
| `AlmostAllSpectralBudget` / R3 | historical complex linear-map Hoffman--Wielandt and RCLike ordered Weyl | CLOSED finite Lemma 5.4 with low complement, positivity, and unchanged index; weak sorting contraction |
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

### R3 finite API brief and admitted slices

Consumer: native Lemma 5.4 and (5.12), then R6's SAME-index mean-square
comparison. The new preapproved owner is `AlmostAllSpectralBudget`, imported
by Solution. Use mathlib's antitone `IsSymmetric.eigenvalues` and existing
isometries/submodules; no bespoke spectral index or inverse sorting map.

- Required finite families: complex Hermitian Hoffman--Wielandt, ordered
  Weyl, isometric compression/interlacing, low-complement Schur comparison,
  positive-root squaring, and weak-order sorting contraction including ties.
- Exact historical slices: the first two transport inequalities in
  `OrderedEigenvalueHilbertSchmidt.lean` (SHA-256
  `04d14e8ab8c0e5ff193d8af30b41800f9bececb138664b7e3946e422bbbe2eb6`);
  complex overlap/HS declarations through linear-map Hoffman--Wielandt in
  `HermitianMatrixHilbertSchmidt.lean` (SHA-256
  `3758bcb9ca1b2092fc32e489734822c35657344578ab161a562d6e91c3495158`).
- Reuse the existing private min--max implementation in
  `FullSpectrumTransfer`: extract only the missing ordered Weyl helpers and
  isometric interlacing from `RCLikeOrderedCompressionInterlacing.lean`
  (SHA-256 `af52aab6a30e71a2852f87141bd2109b27cbbf1df65f40c99e563e84ba441e29`)
  into that owner. Do not copy its private prefix/suffix machinery again.
- Existing matrix norm definitions remain owned by TerminalSchur /
  FullSpectrumTransfer. Direct new library imports are rearrangement and
  Birkhoff; no pins change. Only consumed declarations are extracted.
- Tests: zero residual/reducing frame; tied and reversed input tuples;
  same-index lifting by dimension, not an eigenvalue relabelling. A high
  complement must be excluded explicitly, and positive-root hypotheses
  must remain in the squared estimate. Finite conditional-on-norms lemmas
  close only R3; actual graph budgets are R4, not hidden premises of closure.
- Deferred: generic infinite-dimensional HS spaces, new frame coordinates,
  capacity/exception-set libraries, and empty-spectrum generalization.

R3 CLOSED: `ordered_residual_squaredEnergy_comparison` proves Lemma 5.4
with the literal isometry Q, residual TQ-QD, low-complement form inequality,
and the SAME index lifted by dimension. It gives HW mass, ordered Weyl,
the one-sided Schur shift and the squared-energy sum with explicit constants
32 C0^2 and 512 (C0/c0)^2. The rectangular HS/basis identity connects its
basis-sum premise to a matrix Frobenius budget. Weak sorting contraction
allows repeated values and never bounds an inverse sorting permutation.

Thirteen finite declarations were extracted from the three hashed source
slices above; eight new theorems assemble the finite consumer and its norm /
sorting bridges. Existing private min--max machinery was not duplicated.
The matrix-specific HW/Weyl wrappers and their two auxiliary bridges were
not consumed by the final linear-map assembly and were removed before the
checkpoint. The existing private matrix norm helper was not made public.
The preapproved owner has 639 lines; total local Lean is 21,352 (+811).
Five finite controls passed: plateaus, reversed input, zero residual with
low complement, high-complement obstruction, and the positivity requirement
for squaring. New audited roots have only propext / Classical.choice /
Quot.sound. Full build passed (4,238 jobs); the four selected public proofs
still have sorryAx. Logs/controls for this iteration are in
`/private/tmp/prime-cover-r3-check.PDIy1q`; they are local checks, not
permanent provenance or official Palomar verification.

### R4: repaired projection, not the historical charged-tail premise

Read-only source inspection identifies two literal differences that must
be resolved before porting the old normalization wrappers:

1. `ExactProjectedMolecules.exactOneExitMoleculeFamilyFrame` is the raw
   projection P_R Vtilde, without the paper's diagonal column normalization
   N_B or phase convention. Do not silently identify it with V_B.
2. `ExactMoleculeProjectionTail` assumes that the full signed charged branch
   lies in R. The repaired paper retains the separate zero-mode term
   -2 alpha_minus/nu (I-P_R) D_a. Its tail bound, including that term, is the
   required producer; the old `hcharged` implication is not a discharge.

R4 subproducts, one at a time in this same owner:
- R4a: actual projected, phase-aligned unit columns and the exact normalized
  residual/Gram identities (6.8c), with eventual nonzero normalization.
- R4b: corrected zero-mode tail and raw one-source continuation counts;
  upgrade the old O(B^2/L) sum to the consumed O(B L^C) budget.
- R4c: global near-Gram and residual operator row bounds, retaining the
  coherent B^2/sqrt(X) term and both orientations.
- R4d: instantiate symmetric reorthonormalization and both budgets on the
  actual complete prefix, then export Q as the isometry R3 consumes.

The initial read-only alignment check closed none of these subproducts.
The implementation result below records the later R4a progress. Do not add
modules or count a conditional norm-budget wrapper as R4 closure.

R4a implementation admission: use the existing actual principal eigenvector,
its proved positive-mode overlap, and the actual one-exit projection. Choose
a real sign (negative coefficient gets -1, otherwise +1), project, and
normalize by the projected norm. The norm is eventually at least 1/2 on the
power range; zero fallback outside that range is not asserted to be unit.
Keep the complete `MoleculeCenter` prefix, including inactive target spaces
already contained in each principal molecule. No new ambient type or module.
Consumers are the R4b tail and R4c normalized Gram/residual estimates.

Required R4a API: unit raw phase columns, eventual positive overlap/nonzero
projected norm, unit projected columns, exact normalized Gram subtraction and
projected residual identity. Empty prefixes are valid empty matrices; zero
overlap is excluded only in the eventual theorem. No near-Gram or analytic
budget assumptions may replace these assertions. Reuse the finite algebra of
historical `MoleculeProjectionTail` only where it has this literal object;
matrix-star and normalization laws use the pinned Mathlib API. Inverse-square
root reorthonormalization is deferred to R4d, not duplicated here.

R4a implementation result: the complete-prefix projected columns are
eventually unit and positively phase-aligned with their designated star
modes (`eventually_powerRange_projectedFullStarFrame_columns`). The actual
projected norms lie in [1/2,1] without assumed tail, gap or nonvanishing
certificates. The exact Pythagorean identity identifies their normalizers
with the manuscript's inverse square roots. `projectedFullStarFrame_gram_eq`
retains the full tail Gram and both diagonal normalizers.
`projectedFullStarFrameResidual_eq` retains **A Z**, not **H Z**: replacing
these requires R4b's actual L Z = 0 theorem and is not silently assumed.
Thus R4a's finite normalized projection is closed; the zero-mode specialization
of (6.8c) is explicitly assigned to R4b. R4 as a whole remains OPEN.

Two finite matrix proof bodies were adapted from
`MoleculeProjectionTail.projectedFrame_gram_eq_sub_tailGram` and
`.projectedFrameResidual_eq` (file SHA-256
`4f32bf523a41ad178aa532122f4eac33a0f3df1178325ca3255954beacf0c25e`).
No historical module or extra dependency was imported. Existing actual
overlap, projection and unit-vector producers are called directly.
Nine concrete definitions and seventeen theorem/bridge declarations live
in the existing owner; no new module. Local Lean 21,352 -> 21,704 (+352,
including four audit lines). Full build: 4,238 jobs, exit 0; the four new
audit roots use propext / Classical.choice / Quot.sound only. Both papers
and all pins are unchanged; selected public holes remain four.

Five exact finite controls passed: raw projection has Gram 9/25; normalized
projection has Gram 1; the discarded tail has Gram 16/25; omitting A Z changes
the residual (-2 versus -2/3); zero-denominator normalization is zero rather
than unit. They are local checks in
`/private/tmp/prime-cover-r4-controls.H3nbxG/Controls.lean` (exit 0), not a
proof of the asymptotic budgets. Semantic lint via `lake exe runLinter`
reported inherited missing-doc/unused-argument/simp-normal-form findings in
FirstExitTarget, FullSpectrumTransfer and TerminalSchur, with no finding
located in AlmostAllSpectralBudget. It is not a clean package-lint result.
The direct `lake lint` command has no configured driver; no configuration
or historical declaration was changed to silence these findings.
Text style lint via `lake exe lint-style
PrimeCoverPowerBand.AlmostAllSpectralBudget` passed (exit 0); the checker
warned that the optional `scripts/nolints-style.txt` file is absent and
treated it as empty. No root module or suppression file was added.

R4b reuse check: the existing boundary-kernel producer already proves
O(a log(X)^3 / X^(3/2)), which is sufficient with the allowed logarithmic
slack. Historical `NegativeStarCyclicCapture` requires uniqueness against
ALL other star degrees. It does not prove the repaired paper's source-local
capture or its equal-degree target aggregation. Reuse the finite spectral
algebra only after matching this distinction; do not substitute global
degree isolation or the old `hcharged` premise. The next literal deliverable
is the actual discarded signed/kernel decomposition, retaining the
-2 alpha_minus/nu (I-P_R) D_a term.

R4b admission (next finite slice): use Mathlib eigenspaces and orthogonal
projections to prove that the actual one-exit projection captures each
spectral component of a vector it already captures. This replaces global
simple-eigenvalue capture only for this literal interface; arithmetic
identification of an individual negative mode remains open. Consumers are
the boundary/target negative-mode capture and the zero-mode C_a+D_a capture.
Define only the forest zero projection and the half-difference zero source
needed for the signed identity; prove that its uncharged negative source is
exactly -2 times that half-difference. Do not assert its omega(a) estimate or
its down-target identification before they are proved. Also reuse the pinned
star-data action to prove that the actual boundary kernel is killed by L.
All declarations stay in AlmostAllSpectralBudget, without new imports.
Calibration: repeated eigenvalues allow capture of the charged combination,
not arbitrary vectors in that eigenspace; a zero charged source captures
nothing. At zero eigenvalue the projection is the ordinary kernel projection,
with no inverse or simplicity premise. Required: capture, signed cancellation,
and boundary zero-mode laws. Deferred: arithmetic capture/identification,
source norms, and complete tail estimate. No new abstract operator class or
generalization beyond the finite complex inner-product interface is admitted.

R4b implementation result: `oneExitProjection_fixes_spectralComponent`
uses actual commuting projections and captures a charged spectral component,
not every vector of a repeated eigenspace. The actual positive zero source is
captured. `oneExitComplement_negativeZeroSource_eq` retains exactly -2 times
the projected half-difference zero source. Its identification with the
arithmetic down-target sum and the omega(a) norm estimate remain OPEN.
`eventually_powerRange_discardedBoundaryKernel_zero_and_sq_le` proves, on the
actual power range, that the discarded boundary-kernel component is killed
by L and has squared norm at most C a log(X)^3 / X^(3/2). It reuses the
existing quantitative producer and contraction of the actual projection;
it is not the corresponding theorem for the complete discarded molecule Z.

Two finite proof bodies were reused from the read-only historical files:
- `StarKernelVariance.lean`,
  `largePrime_apply_actualStarMeanZeroLeafVector`, source SHA-256
  `50d63356e7abfd94402da0f805f2bfe69a8bbcbf6c7123cc6689abee34b7da89`;
- `ExactBoundaryDecomposition.lean`,
  `largePrime_apply_exactPrincipalMoleculeBoundaryKernel`, source SHA-256
  `b9abf85deec29659777eddade7a1ed264aebc6f82b3a047324204892e69283f5`.
No historical module was imported. All additions stay in the admitted owner,
with four selected audit additions. Local Lean 21,704 -> 21,962 (+258),
eight local modules and five proof owners unchanged. The checked full build
passed with 4,238 jobs; the four added audit roots use only propext,
Classical.choice and Quot.sound. All four public Solution holes remain.
The manuscript hashes and dependency pins are unchanged. No commit or push.

Four exact finite controls passed (local `Controls.lean` in
`/private/tmp/prime-cover-r4b-controls.vH2PbH`, exit 0): repeated-eigenvalue
capture does not capture an arbitrary vector; a zero charged source gives
no such capture; C+D can be captured while F(C-D)=-2FD is nonzero; and a
mean-zero leaf vector is killed by the literal three-vertex star. These
calibrate the finite identities, not the asymptotic estimates.
Semantic lint reported inherited findings plus one missing docstring on the
new local adjacency instance; that docstring was added without changing a
theorem. The final rerun has 93 inherited findings, all outside the changed
owner, so package lint is still not clean. The final full build passes with
4,238 jobs. Final owner SHA-256:
`92c279df5d41d8a23e8b3a45c67f84b2e7b83551d371e6daff20c15517e100a7`.
Style lint passed, with the same optional nolints-file warning.
No unrelated declaration or suppression configuration was changed.

At the previous checkpoint, the pointwise obligations before the full R4b
tail were to identify the down-target kernel sum and prove its divisor bound,
and capture the required negative-mode
responses using source-local, not global, isolation. Then assemble the full
discarded signed/kernel formula and one-source continuation bounds. R4c
global budgets and R4d isometry are still later consumers. This checkpoint
does not change 3/8, MG2 1/2 or public 0/4.

R4b next admission: specialize the existing forest kernel projection to actual
star-data vectors. A uniform leaf vector is in the forest range, so its kernel
projection is zero; a partial leaf vector projects to its mean-zero part.
These are the up/down block consumers of the already-defined signed source,
not a new operator abstraction. Reuse `largePrime_toEuclideanLin_starDataVector`,
the exact canonical signed-source partition and the finite variance inequality.
The positive control is a full leaf set (zero variance); a proper nonempty
subset has nonzero variance. Retain the empty/zero-degree case separately.
Only the existing owner/audit may change; global frame estimates are not
assumed or declared closed by this finite projection step.

R4b down-target result: `largePrimeZeroModeProjection_leafData_eq_meanZero`
identifies the actual forest-kernel projection of leaf data. Uniform leaves
are in the forest range and hence project to zero. The explicit
`canonicalDownZeroSource` uses the actual canonical target and leaf set;
each summand pays at most 1/2 in squared norm and different down-primes lie
in disjoint stars. `norm_sq_sum_canonicalDownZeroSource_le` therefore pays
omega(a)/2, not omega(a)^2. The source identity
`signedZeroModeSourceDifference_eq_sum_downKernels` uses the existing exact
signed canonical partition, cancels up-targets (including inactive ones),
and gives `norm_sq_signedZeroModeSourceDifference_le` without an extra
identification premise. No global degree uniqueness is used.

Reuse: existing star action, canonical source partition/disjointness,
variance inequality, and real-to-complex subtraction/sum APIs. Four public
audit additions; owner 1,241 -> 1,605 lines and local Lean 21,962 -> 22,330
(+368 including audit). Eight modules/five proof owners remain unchanged.
Full `lake build`: 4,238 jobs, exit 0; the four new roots use only propext,
Classical.choice and Quot.sound. Four deliberate Solution holes remain;
none are hidden by the local proof checks. Five exact rational controls in
`/private/tmp/prime-cover-down-kernel-controls.m7N1sj/Controls.lean` pass:
full-leaf zero projection, partial-leaf nonzero projection and mass, and
scalar mass calibrations. Actual orthogonality is proved in Lean, not
inferred from these controls. Style lint passes with the optional missing
nolints-file warning. Owner SHA-256:
`31008979ba9ae94dde66e4a9067747779258cfe875077294eb2f6e4bdadf0fa0`.
Semantic lint finishes with the same 93 inherited findings, all outside
`AlmostAllSpectralBudget`; no new owner finding. Package lint is therefore
not globally clean. `git diff --check` passes.

Remaining R4b: source-local negative-response capture, full discarded
signed/kernel formula and rates, then one-source continuation bounds.
R4c global budgets and R4d isometry remain open. This closes one recorded
subtask, not another R-row: checklist 3/8, MG2 1/2, public roots 0/4.
Manuscripts and pins unchanged; no stage, commit or push in this iteration.

R4b source-local capture admission: the historical negative-star capture
requires global degree uniqueness and is not reusable as this consumer.
Use the actual star-data identity L^3 x = d L x and eigenspace projection
to remove only nonresonant source blocks. The selected block is retained
at its signed eigenvalue; equal-degree stars outside the source support
must not be excluded by a new hypothesis. Reuse the existing star action,
projection commutation, and canonical source partition in this owner.
Controls: a repeated eigenvalue outside the source support is harmless;
two charged equal-degree blocks cannot be separated by this certificate.
The finite extraction is a prerequisite, not eventual arithmetic isolation
or the full R4 tail. No new owner, dependency, or manuscript change.

R4b source-local implementation: `largePrime_starData_cubic` specializes the
existing star action to L^3 x = d L x, including degree zero.
`largePrime_eigenprojection_starData_eq_zero` kills exactly the nonresonant
source blocks. `largePrime_eigenprojection_starData_eq_quadratic` and
`largePrime_eigenprojection_starData_eq_smul_signedData` retain the chosen
signed block and its exact coefficient. The private isolated-target adapter
uses the existing isolated-support annihilation theorem. Finally,
`oneExitProjection_fixes_downSource_spectralComponent` consumes the actual
canonical signed-source partition and previously proved source capture.
Its premises compare lambda^2 only with the other canonical up/down degrees;
there is no global degree-uniqueness or eigenspace-simplicity premise.
It proves capture of the selected spectral component, not yet capture of
the normalized negative star: its coefficient can be zero without the
remaining arithmetic nonvanishing proof.

Next literal consumer: take the source at ell*a for the smallest prime ell
outside S and select the down-prime ell. Supply the source-local separation
with uniform PNT and show the displayed coefficient is nonzero using the
exact down-leaf count and distinct source/target degrees. Then derive actual
negative-mode capture. Equal-degree negative responses to the boundary
kernel still require the paper's equal-initial-segment argument; do not
replace it by global uniqueness. Full tail/continuations and R4c/d remain.

Source-local implementation size: owner 1,605 -> 1,893 (+288), four audit
additions, local Lean 22,330 -> 22,622 (+292). No new module/import/pin.
Targeted build passed, 4,234 jobs. Owner SHA-256:
`64678b51bc6f91e81770486d7cda6f0e83660eba93b691f7454dbe260390b631`.
The R4 row remains open: checklist 3/8, MG2 1/2, public proofs 0/4.
Six exact rational controls pass in
`/private/tmp/prime-cover-source-local-controls.HwjccR/Controls.lean`:
the cubic identity, idempotent negative projection, its signed eigenvalue,
one charged block with a repeated uncharged eigendirection, two charged
blocks, and rejection of falsely isolating just one of those charged blocks.
Style lint passes (optional nolints-file warning); semantic lint finishes
with 93 inherited findings, none in this owner. No global lint-clean claim.
Final full build passes, 4,238 jobs, exit 0. All four new audited roots use
only propext, Classical.choice and Quot.sound. The four selected Solution
roots still report sorryAx, as expected; no public closure was promoted.
Both frozen manuscript hashes and dependency pins match; git diff --check
passes. No stage, commit or push.

R4b next admission: discharge the selected canonical down-block's signed
coefficient using its exact boundary leaf count, normalized centre amplitude,
and distinct source/target degrees. Feed that coefficient to the existing
source-local extraction to obtain the actual normalized negative mode.
Then instantiate source-local arithmetic via a smallest allowed prime and
the pinned fixed-denominator PNT gap. These are the recorded capture inputs,
not a new resolvent or global-simplicity theorem. Keep the existing owner.

R4b negative-mode implementation: three new roots in the existing owner.
`canonicalDown_negativeSpectralCoefficient_ne_zero` uses the exact partial
leaf count and boundary centre mass to remove the free coefficient premise.
`oneExitProjection_fixes_negativeDownMode_of_sourceLocalDegrees` then
captures the normalized negative target, still assuming separation only
from the other canonical source blocks and the source itself.
`eventually_allowedPrimeCount_mul_lt_succ_mul` adapts pinned
`eventually_allowedPrimeCount_fixedDenominator_gap_ge` by evaluating at
k*(k+1)*n. The multiplier k is fixed; this is not a moving-label result.
No new short-interval input or global simplicity premise is introduced.

Targeted owner build passes (4,234 jobs). Owner 1,893 -> 2,093 (+200),
three audit roots, total local Lean 22,825 (+203). Six controls pass in
`/private/tmp/prime-cover-negative-coefficient-controls.lean`: both signs
of a nonzero coefficient, equal-degree and zero-amplitude degeneracies,
explicit nonvanishing, and the elementary integer interval enclosure for
the next arithmetic specialization. The negative-mode theorem's remaining
consumer is the actual source ell*a with ell the least allowed prime;
local degree hypotheses are not yet instantiated there. Full negative
responses, full tail/continuations, global budgets and isometry stay open.
No checklist unit or public-root closure is claimed.
Final gate: full build 4,238 jobs passes; all three new audit roots use only
propext, Classical.choice and Quot.sound. The four selected proofs still
report sorryAx. Style lint passes with the existing optional nolints-file
warning. Root `lake lint` has no configured driver, so the pinned Batteries
`lake exe runLinter --no-build --trace PrimeCoverPowerBand.AlmostAllSpectralBudget`
was used instead. Its 93 inherited findings are byte-identical to the prior
run, with none in this owner. Both manuscript hashes and pins match;
placeholder scan and diff check pass. Final owner SHA-256:
`e5b202b5749576de4d5d1384ec5ca9906a5c757a7a172263e2919ce7aa1a279e`.
No stage, commit or push.

R4b least-prime specialization: the preceding finite capture has now been
instantiated on the actual graph. `allowedPrimeCount_divisorTarget_lt`
pays floor errors using the fixed k=2*ell prime interval. The public
`eventually_powerRange_leastPrime_downDegree_separated` handles every other
down-prime at once. Existing power-range up/down ratio bounds feed
`eventually_powerRange_oneExitProjection_fixes_leastPrimeDownMode`.
Finally `eventually_powerRange_oneExitProjection_fixes_negativeStarMode`
constructs the least prime outside S, the allowed source a*ell and its
canonical down-index; the target is exactly a. Its only mathematical
assumptions are a fixed finite prime deletion set and theta < 1/2, with the
stated eventual allowed-vertex power window. It is NOT conditional on local
degree separation and does not require global star-degree uniqueness.

Literal native consumer: the paragraph beginning "If ell is the smallest
prime outside S" in the frozen full-star proof. Next: negative target
response capture with equal-degree targets, then the full discarded tail
and one-source continuation. Do not infer the full molecule tail is a zero
mode from capture of the boundary mode alone.
Targeted build: 4,234 jobs passed. Owner +218 lines, three audit roots,
local Lean 22,825 -> 23,046 (+221), no new module/import/dependency.
Owner SHA-256: `48224924ad3a06ef4bb67e3b31e603eb59509036536fc61197f9dd6f038a8730`.
Checklist remains 3/8, MG2 1/2, public roots 0/4. No publication action.
Final verification: full build 4,238 jobs passed, standard axioms only for
the three new roots, all four selected Solution holes still explicit.
`/private/tmp/prime-cover-leastprime-controls.lean` passes four exact
prime-count controls (two positive, two negative); its maxRecDepth setting
only permits kernel-reduced finite counting, not native/trusted evaluation.
Style lint passes with the existing optional nolints-file warning. Semantic
lint has the same 93 inherited findings; only inspected-declaration counts
changed. Placeholder scan and diff check pass; both manuscript hashes and
all dependency pins match. No new module, import, stage, commit or push.

R4b signed-target response checkpoint (same approved owner):

- `largePrimeLabels_eq_of_degree_eq` and
  `canonicalUp_boundaryLeafSegments_eq_of_degree_eq` prove exact equality
  of the active initial segments for equal-degree targets. No false strict
  degree-monotonicity premise is used.
- `largePrime_eigenprojection_upSource_neg` and
  `largePrime_eigenprojection_downSource_neg` expose the different exact
  signed coefficients on actual graph star blocks.
- `oneExitProjection_fixes_negativeSource_spectralComponent` sums those
  identities using the up/down straddle of the boundary degree, with
  repeated degrees permitted. Its eventual power-range specialization
  discharges both degree families from existing PNT ratio bounds.
- `oneExitProjection_fixes_response_spectralComponent` consumes an existing
  shifted forest equation. Its actual consumer is
  `eventually_powerRange_oneExitProjection_fixes_negativeResponse_spectralComponent`:
  every negative forest spectral component of the actual negative signed
  first-exit response is captured. Root positivity/nonresonance and source
  support are supplied, not new hypotheses of this eventual theorem.

Before: only negative boundary-mode capture was eventual. After: negative
signed target responses are also captured, with repeated degrees allowed.
Still open: kernel-driven target response, then the full discarded molecule
tail and one-source continuation, followed by R4c/d. Equal initial segments
alone do not close the kernel-source identification. No theorem status
above this local substep changes; checklist 3/8, MG2 1/2, public 0/4.

Validation: target 4,234 and full 4,238 jobs pass; eight new audit roots
have only standard axioms, four selected Solution roots still have sorryAx.
Seven exact controls pass in `/private/tmp/prime-cover-targetresponse-controls.lean`;
the log is `/private/tmp/prime-cover-targetresponse-controls.log`.
Build/audit log: `/private/tmp/prime-cover-targetresponse-full.log`.
Style lint passes with the optional nolints-file warning. Semantic log
`/private/tmp/prime-cover-targetresponse-lint.log` differs from the preceding
run only in inspected-declaration counts: 93 inherited findings, none new.
Owner 2,311 -> 2,675 (+364); total local Lean 23,046 -> 23,418 (+372),
including eight new audit lines. No new module/import/pin. Owner SHA-256:
`7b813edf16c392313751b2c6c7af3efb05ace66cc0e273cfd5174fb7baf3a5b7`.
Both frozen manuscripts and dependency pins unchanged; owner placeholder
scan and diff check pass. No stage, commit or push.

R4b kernel-source coefficient checkpoint (existing approved owner):

- `exactPrincipalMoleculeKernelInteriorSource_eq_smallPrime` removes the
  first-exit projection on H*zeta using actual graph support.
- `real_inner_starMode_kernelSource_eq_reverseRestriction` uses symmetry
  of H and the boundary support of zeta, rather than another vertexwise
  adjacency enumeration.
- `real_inner_upTargetMode_kernelSource` is the exact partial-leaf-sum
  formula on each active canonical up-target.
- `real_inner_downTargetMode_kernelSource_eq_zero` pays the whole mean-zero
  boundary segment on each active down-target.
- `real_inner_upTargetMode_kernelSource_eq_of_degree_eq` combines the exact
  initial-segment equality with equal normalization and energy. It proves
  equality of coefficients even for distinct targets of the same degree.

Before: equal prime segments were known but their actual kernel-source
coefficients were not identified. After: both up/down coefficient formulas
and equal-degree compatibility are compiled. Next: sum the actual source
block spectral projections and use the captured positive source, then the
already-proved response transfer. Coefficient equality is not by itself
kernel-source capture; no full-tail or R4c/d promotion is made.

Targeted build 4,234 and full build 4,238 jobs pass. Five new public roots
have only propext, Classical.choice and Quot.sound. Five exact arithmetic
controls pass in `/private/tmp/prime-cover-kernelcoeff-controls.lean`,
including nonzero equal up-segment sums, whole-segment cancellation and
negative controls for truncation and missing mean-zero. These finite sums
are diagnostics; the graph formulas are proved by the Lean declarations.
The first linter pass found one new local-instance docstring omission; it
was fixed before the final verification gate.
Owner 2,675 -> 2,861 (+186), audit +5, local Lean 23,418 -> 23,609 (+191).
Final owner SHA-256:
`e53e60625bd3789f6e798d2643c0363c9d16a86f626e40ea1b5bec9c4c8ce8d2`.
Final build/audit log `/private/tmp/prime-cover-kernelcoeff-final.log`
passes all 4,238 jobs. The final semantic-lint log
`/private/tmp/prime-cover-kernelcoeff-lint-final.log` differs from the prior
snapshot only in declaration counts: the same 93 inherited findings, none
in the changed owner. Style passes with the existing optional nolints-file
warning. Owner placeholder/trusted-evaluation scan and diff check pass.
Eight modules/five proof owners unchanged; no new import/pin. Both frozen
manuscript hashes match. Checklist 3/8, MG2 1/2, public Solution proofs 0/4.
No stage, commit or push.

R4b kernel spectral assembly checkpoint (same approved owner):

- `eventually_powerRange_canonicalTargetDegrees_straddle` factors the
  existing actual power-range up/down inequalities into one reusable producer.
- `largePrime_negativeEigenprojection_boundary_eq_inner_smul` identifies
  a single boundary's negative spectral projection without global simplicity.
- `real_inner_negativeUpTargetMode_positiveSource` gives the exact positive
  source coefficient (1 - mu_target/mu_source)/2.
- `oneExitProjection_fixes_kernelSource_negativeSpectralComponent` groups
  matching canonical blocks. Equal-degree up coefficients agree; matching
  down coefficients vanish. The resulting vector is proportional to the
  already-captured positive-source component, or is zero.
- `eventually_powerRange_oneExitProjection_fixes_kernelSource_negativeSpectralComponent`
  discharges the finite straddle premises on the actual power range.
- `eventually_powerRange_oneExitProjection_fixes_kernelResponse_negativeSpectralComponent`
  uses the pinned first-exit resolvent equation and existing response-transfer
  theorem. No new resolvent is constructed.

Literal delta: exact local kernel coefficients now imply capture of the
whole actual negative kernel-source AND response spectral components,
for every fixed theta < 1/2, allowing repeated target degrees. The full
discarded-tail identity L z_a = 0, its quantitative bound, continuations,
and R4c/d global estimates/isometry are still open. No public root closes.

Full build/audit `/private/tmp/prime-cover-kernelcapture-full.log`: 4,238 jobs,
six new roots use only propext, Classical.choice, Quot.sound. Targeted build:
4,234 jobs. Five exact controls in
`/private/tmp/prime-cover-kernelcapture-controls.lean` pass, including the
negative control that equal degrees alone do not imply compatible source
coefficients. Semantic lint retains the same 93 inherited findings (none
in this owner); style passes with the existing optional nolints-file warning.
Owner placeholder scan, diff check, manuscript hashes and pins pass.
Owner 2,861 -> 3,269 (+408); audit +6; total local Lean 23,609 -> 24,023 (+414).
Owner SHA-256:
`4ce7156923a7ec0cc6a55917695963e3460c1fa58b06bcb194ddaf1cd2f6ac24`.
Eight modules/five owners unchanged. Checklist 3/8, MG2 1/2, public proofs
0/4 unchanged. No stage, commit or push.

R4b full-tail implementation (same owner, no new imports or coordinates):

- `largePrime_apply_oneExitComplement_eq_zero_of_negativeCapture` uses
  the pinned orthonormal eigenbasis to prove that captured negative
  components, together with the existing positive-star projection, leave
  only a forest zero mode outside the one-exit space.
- `eventually_powerRange_largePrime_discardedFullMolecule_eq_zero` consumes
  the actual boundary decomposition, signed interior synthesis and
  kernel-response capture. All source, gap and nonresonance producers are
  instantiated on each fixed power range theta < 1/2.
- `eventually_powerRange_fullStarFrameTail_largePrime_zero` transfers the
  vector identity to every complete actual prefix K <= X^theta, including
  the phase factors, and proves A Z = H Z from the exact large/small split.

Before: actual negative-component capture was available, but R4a still
retained A Z without a proved replacement. After: the actual full tail has
L Z = 0 and A Z = H Z, not only the boundary kernel. The full quantitative
tail (including the signed down-kernel term), continuation counts and R4c/d
global frame budgets/isometry remain open. No new research question or
manuscript change; no public Solution hole closes.

Targeted build `/private/tmp/prime-cover-fulltail6.log`: 4,234 jobs. Full
build/audit `/private/tmp/prime-cover-fulltail-full.log`: 4,238 jobs, three
new roots use only propext, Classical.choice and Quot.sound. All four
selected Solution roots still contain sorryAx. Semantic lint via the pinned
Batteries runLinter retains exactly the prior 93 inherited findings; the
root package has no lake lint driver, so the direct driver was used.
Style passes with module-name arguments and the existing optional nolints
warning. Owner placeholder scan, diff check and manuscript/pin checks pass.
Owner 3,269 -> 3,465 (+196), audit +3, total local Lean 24,023 -> 24,222 (+199).
Owner SHA-256:
`ade72c0949404f7cc9ad13dc170f27f4af7952d46fbc90f700574ab86e6b838b`.
All four exact rational-matrix controls pass in
`/private/tmp/prime-cover-fulltail-controls5.log`: full nonzero-mode capture,
failure when the negative mode is omitted, a nonzero discarded kernel vector,
and the surviving minus-two down-kernel correction. Earlier control attempts
failed only on Fin-3 identity/vector notation elaboration; explicit pinned
notation lemmas resolved them, with no trusted evaluation added.
Next reuse: `exactPrincipalMolecule_negativeMode_scalarEquation` and
`gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_smallPrime` supply
the negative coefficient estimate; the discarded response must be identified
with its inverse-root zero-mode source before applying the down-kernel bound.
Eight modules/five owners unchanged. D31 3/8, MG2 1/2, public proofs 0/4.
Nothing staged, committed or pushed.

### R4b quantitative full-tail closure

The preceding inverse-root reuse obligation is now discharged in the same
`AlmostAllSpectralBudget` owner, without imports, new modules or dependency
changes. Exact public additions:

- `oneExitComplement_response_eq_zeroModeSource`: project the actual shifted
  forest equation onto the discarded zero eigenspace before estimating it.
- `eventually_powerRange_discardedSignedResponses_eq`: Q response-plus = 0;
  Q response-minus = (-2/nu) Q D. D is the actual signed down-kernel source.
- `gap_mul_energy_mul_abs_negativeBoundaryCoefficient_le`: the finite
  negative-mode equation gives gamma mu |alpha-minus| <= eta^2.
- `eventually_powerRange_negativeCoefficient_and_kernelResponse_bound`:
  instantiate gamma = mu/100, the root window and residual scale. Obtain
  |alpha-minus| <= 100 eta^2/mu^2 and norm(kernel-response) <= norm(zeta).
- `eventually_powerRange_discardedFullMolecule_sq_le`: the whole discarded
  molecule satisfies norm squared <= 8 norm(zeta)^2 +
  8 (|alpha-minus|/nu)^2 omega(a). The down-kernel term is not dropped.
- `eventually_powerRange_discardedFullMolecule_sq_le_scale`: for fixed S,
  theta < 1/2, eventually every actual allowed a <= X^theta satisfies

      norm(Q f_a)^2 <= C (a log^3(X)/X^(3/2) + a^3 omega(a) log(X)/X^2).

No gap, capture or source-norm premise remains in the final rate. The first
log-cubed term is inherited from the existing boundary-kernel producer;
the manuscript's sharper log-squared rate is NOT asserted. R4's global
fixed-log-power consumer tolerates this loss. This closes the quantitative
tail exit test, not one-source continuation counts or the global frame.

Reuse: the existing negative-mode scalar equation, first-exit gap and
kernel-source bound supply the coefficient/response control; the existing
degree/residual scale bundle supplies the final a-cubed rate. No new PNT,
resolvent construction or graph coordinate was introduced.

Validation: full `lake build` 4,238/4,238, exit 0, log
`/private/tmp/prime-cover-tailquant-full.log`. All six new audit roots use
only propext, Classical.choice and Quot.sound; all four selected Solution
roots still expose sorryAx. The scoped owner has no sorry/admit/axiom or
native_decide. Semantic linter has the identical 93 inherited findings,
none in this owner, compared against the preceding full-tail lint baseline.
Style passes with the unchanged optional nolints-file warning. Four exact
rational matrix controls replay successfully against the rebuilt owner
(`/private/tmp/prime-cover-tailquant-controls.log`). The scalar rate lemma
was checked independently before integration; failed intermediate builds
were local elaboration/order-API fixes, not a changed mathematical target.

Owner 3,465 -> 3,875 (+410), audit +6, total local Lean 24,222 -> 24,638
(+416), still eight modules/five owners. Owner SHA-256:
`121f232743ac9e20db3570c01a87659fa44749cdc920d413ce8c8ee0727ba022`.
Manuscripts and pins unchanged; YAML parse and diff checks pass.

Next bounded product: the raw one-source continuation estimate in the
four rows following manuscript (4.17b), retaining down-star weights and
removing returns to the whole boundary before counting multiplicities.
Consumer: the actual raw residual squared norm bounded by a fixed power
of log X, then R4c's sum over the complete prefix. Do not replace this
with the global H-norm estimate. R4c/d budgets/isometry remain open.
D31 stays 3/8 (37.5%), MG2 1/2, selected public proofs 0/4.
No stage, commit or push.

### R4b source-continuation multiplicity closure

Same approved owner, no new module/import/coordinate. Four finite roots:

- `prime_dvd_source_of_upward_exterior_firstExit_step`: if v*r is in
  the actual first-exit support, r is a small prime, and v is outside the
  original boundary star, then r divides a. The proof splits canonical
  target centres, target leaves and isolated exits; it retains boundary
  exclusion explicitly.
- `card_exterior_firstExit_neighbors_le_primeFactors`: the incoming
  neighbors in U inject into the union of v*r for r dividing a and v/r
  for r dividing v. Their count is at most omega(a)+omega(v).
- `exterior_firstExit_apply_sq_le_weighted_neighbors`: apply finite
  Cauchy--Schwarz to the actual supported response with that multiplicity.
- `exactPrincipalMoleculeResidual_sq_le_degreeWeightedInterior`: for
  X >= 2, a <= sqrtCutoff X and prime deletion set S,

      norm(g_a)^2 <= (2 log(X)/log(2)) sum_w degree_H(w) |i_a(w)|^2.

Here g_a and i_a are the actual full-molecule residual and full interior.
There is no abstract multiplicity, gap, residual or coefficient premise.
Swapping the finite symmetric neighbor sums produces the degree weight.
The fixed-log-power consumer permits the logarithmic multiplicity cost;
this does not assert the manuscript's sharper individual collision counts.

Exact finite diagnostic: S empty, X=50/100/200/500. Upward exterior
steps checked: 36/100/248/874 (1,258 total), zero failures. Incoming-card
checks: 324/936/2,684/10,695 (14,639 total), zero failures. Omitting the
boundary exclusion produces 28/57/122/328 counterexamples (535 total).
These are bounded controls, not an asymptotic proof; the general assertions
are the compiled roots above.

Validation: targeted build 4,234 jobs and full build 4,238 jobs, exit 0,
`/private/tmp/prime-cover-continuation4.log` and
`/private/tmp/prime-cover-continuation-full.log`. All four new roots have
only propext, Classical.choice and Quot.sound. Four selected Solution roots
still have sorryAx. No scoped sorry/admit/axiom/native_decide. Semantic
linter retains the identical 93 inherited findings, with none in this
owner (`/private/tmp/prime-cover-continuation-lint.log`); style passes with
the unchanged optional nolints warning. Elaboration fixes were the explicit
neighborFinset arguments, the toLp coordinate reduction, and finite-sum
symmetry; no mathematical hypothesis was weakened.
The four existing exact rational matrix controls also replay with exit 0
(`/private/tmp/prime-cover-continuation-controls.log`). YAML parsing and
`git diff --check` pass; both manuscript hashes and all three dependency
pins were rechecked unchanged.

Owner 3,875 -> 4,084 (+209), audit +4, total local Lean 24,638 -> 24,851
(+213). Eight modules/five owners unchanged. Owner SHA-256:
`5f1fa79a67a0ed66a3cdd42f1c65367ec241d3a1d6e692879af60b170f75ae92`.

Remaining one-source consumer: evaluate the displayed weighted interior
sum to a fixed power of log(X). Reuse the signed-plus-kernel decomposition
and target coefficient formulas, retaining the down-centre 1/q factor.
The kernel contribution can use the existing quantitative boundary-kernel
bound; do not substitute a global H-norm bound for the signed continuation.
This is not yet the polylogarithmic raw residual estimate, nor the global
HS/operator/isometry result. D31 remains 3/8, MG2 1/2, public proofs 0/4.
Manuscripts/pins unchanged. No stage, commit or push.

### R4b down-centre weight and kernel-sum closure

Classification: CLOSURE in the same `AlmostAllSpectralBudget` owner.
The remaining weighted response is not replaced by a global H-norm bound.
No new module, import, spectral model or analytic dependency.

New public roots, all on every fixed theta < 1/2 power prefix:

- `eventually_powerRange_downStarDegree_mul_prime_le`: q d_a <= 48 d_(a/q).
  Reuses uniform arithmetic-degree bounds and logarithm comparison on
  [sqrt(X),X]. Since floor(X/a) = floor(X/(a/q))/q, the prime factor is
  retained before division. Exact graph-degree identities close the bridge.
- `eventually_powerRange_signedDownCenter_abs_le`: the actual signed
  response at a/q is at most 10000/(q mu_a). The root window and
  d_(a/q)/d_a >= 17/16 imply the normalized denominator is at least q/1536.
  The existing exact down-star formula supplies the numerator. The prime
  q is allowed to vary with a and X; no fixed-label limiting argument.
- `eventually_powerRange_degreeWeightedKernel_le_logCube`: the actual
  kernel response has sum degree_H(w) |k_a(w)|^2 <= C log^3 X. Degree <= X,
  norm(k_a) <= norm(zeta_a), the existing log-cubed kernel rate, and
  a <= sqrt(X) close this whole sum.
- `eventually_powerRange_residual_sq_le_signedWeighted_add_logFourth`:
  the signed-plus-kernel identity and finite weighted Cauchy bound give

      norm(g_a)^2 <= (4 log(X)/log(2)) sum_w degree_H(w) |i_signed(w)|^2
                    + C log^4 X.

No gap, kernel, multiplicity or arbitrary coefficient premise is left in
the final reduction. The one-source signed weighted sum is still OPEN;
this is not the desired polylog raw residual, global residual operator/HS
bound, or frame isometry. R4 and all four selected proofs remain open.

Calibration before scalar integration: at z=101/100, s=17/16, mu=1 and
alpha=beta=2, the bound holds at q=51=48s. Keeping the same response but
dropping q<=48s and setting q=10^6 violates it. Both exact rational
controls and the real scalar lemma compile without native computation in
`/private/tmp/prime-cover-downweight-scalar.lean`; validation log
`/private/tmp/prime-cover-downweight-scalar2.log`. This checks the literal
scalar dependency, not an asymptotic or actual-graph numerical claim.

Validation: targeted build 4,234 jobs and full build 4,238 jobs, exit 0
(`/private/tmp/prime-cover-downweight4.log`,
`/private/tmp/prime-cover-downweight-full.log`). Four new audit roots use
only propext, Classical.choice and Quot.sound; all four selected Solution
roots retain sorryAx. No scoped sorry/admit/axiom/native_decide. Semantic
lint has the identical 93 inherited findings, none in this owner; style
passes with the unchanged optional nolints warning. Four existing exact
matrix controls replay with exit 0. Local fixes were a Filter opening,
explicit coercion types and use of the literal arithmetic-ratio API; no
mathematical hypothesis was weakened to obtain compilation.

Owner 4,084 -> 4,386 (+302), audit +4, local Lean 24,851 -> 25,157 (+306).
Eight modules/five owners; owner SHA-256:
`0aefb739ec35edafa2cfa582dbe5281ad99f86c102332a534da6a2a3df860c78`.
Paper I/Paper II hashes and pins unchanged. No stage, commit or push.

Next: sum the signed response over actual up/down target centres and
leaves, using the proved reciprocal-prime down-centre bound and existing
local response formulas. A finite degree majorant X/w+omega(w) and harmonic
sums can pay this fixed-log-power consumer; do not optimize logarithms or
reopen the already discharged kernel term. R4c/d remains afterward.
Tracking remains D31 3/8 (37.5%), MG2 1/2, selected public proofs 0/4.

### R4b complete weighted down-centre sum

Classification: CLOSURE; same owner, no new module/import/analytic input.
Literal target: for each fixed finite prime S and theta<1/2, eventually
uniformly over allowed a<=X^theta, sum over every q in primeFactors(a) of
degree_H(a/q) times the actual signed response squared is <= C log^2 X.
The constant is explicit and independent of moving a,q,X. It is not a
fixed-label limit or a pointwise theorem with an unproved summation premise.

Proved public roots:
- `smallPrimeGraph_degree_le_div_add_primeFactors`: degree_H(w)<=floor(X/w)
  +omega(w), at any actual vertex and prime cutoff. Neighbor labels inject
  into upward multiples and downward prime quotients.
- `smallPrimeGraph_degree_le_div_add_log`: the real-valued majorant
  X/w+log(X)/log(2), consumed immediately by the next root.
- `eventually_powerRange_degreeWeightedDownCenters_le_logSq`: the literal
  whole-row bound. Degree at a/q is <=Xq/a+log(X)/log(2); the compiled
  response 10000/(q mu_a), mu_a^2>=X/(8a log(X)), and mu_a^2>=1 give an
  O(log X) bound per prime. The existing omega(a)<=log(X)/log(2) closes
  the row. No free degree, gap, root-window or coefficient hypothesis.

Target sanity: FEASIBLE, polynomial degree growth is canceled by the
reciprocal-prime response before summation. a=1 gives an empty down row.
Exact scalar calibration fixes x=8a, mu=ell=h=1. q=1,2,10^6 obey the
weighted bound; dropping 1/q fails already at q=2. Four norm_num controls
in `/private/tmp/prime-cover-downsum-controls.lean` pass with no native
computation. They check the scalar payment, not the asymptotic theorem.

Validation: targeted 4,234/full 4,238 jobs pass, logs
`/private/tmp/prime-cover-downsum-target.log` and
`/private/tmp/prime-cover-downsum-full.log`. Three new public roots use only
propext, Classical.choice and Quot.sound. All four selected Solution roots
retain sorryAx. No owner sorry/admit/axiom/native_decide. Semantic lint
`/private/tmp/prime-cover-downsum-lint.log` has exactly the same 93 inherited
error lines as the prior downweight baseline, none in this owner. Style
passes with the existing optional nolints warning. Scalar controls exit 0.
Scratch repairs concerned explicit log(2) typing, additive inequality
orientation and field normalization; no target/hypothesis was weakened.

Owner 4,386 -> 4,548 (+162), audit +3; local Lean 25,157 -> 25,322 (+165).
Owner SHA-256: `7faa0928b3b061d6346a062fdcd29a2565604d5e8961b53751d19ab78eaf802b`.
Both manuscript hashes and all pins unchanged. No stage, commit or push.

Strict narrowing: down-centre weighted sum CLOSED. The signed up-centre
and leaf sums and support-sum assembly remain OPEN. R4c global residual
HS/operator/Gram and R4d isometry remain OPEN. This does not close R4 or
any public Solution. D31 3/8 (37.5%), MG2 1/2, selected proofs 0/4.
Resume with the actual weighted up-centre sum, retaining the reciprocal
target degree weight; reuse the isolated-up formula and selected-star
resolvent formulas. Do not reopen the kernel or down-centre rows.

### R4b complete weighted up-centre sum

Classification: CLOSURE in the existing owner. Literal target: for every
fixed finite prime S and theta<1/2, eventually uniformly over allowed
a<=X^theta, the sum over all canonical up-primes of degree_H(aq) times
the actual signed response squared is at most C log^2 X. Inactive targets
are included, not removed from the source family. No new analytic input.

New public roots:
- `shiftedActualUpStarResolvent_apply_center`: exact centre formula for
  the literal star inverse; the centre counterpart of the existing leaf API.
- `exactPrincipalMoleculeSignedInteriorVector_apply_canonicalUpTarget`:
  numerator nu*(alphaPlus+alphaMinus)+(d_up/mu)*(alphaPlus-alphaMinus),
  denominator nu^2-d_up. Existing canonical lower/isolated decomposition
  and signed synthesis prove both cases, including d_up=0.
- `eventually_powerRange_signedUpCenter_abs_le`: all actual up-centre
  coefficients are <=600/mu. The compiled root window, ratio margin and
  amplitude bounds discharge every premise of the scalar estimate.
- `eventually_powerRange_degreeWeightedUpCenters_le_logSq`: sums the
  actual degree-weighted row, not just a coefficient envelope. Reuses the
  previous finite degree majorant, harmonic prime sum and canonical labels.
  Sum 1/q<=2 log(X), card(up)<=Y, X/a<=8 log(X) mu^2 and
  Y<=8 log(X) mu^2 give C=600^2*(16+8/log(2)).

Target sanity: FEASIBLE. Reciprocal target weights, not an unweighted
prime-count factor, pay the row. Before integration four exact rational
controls checked the isolated d=0 case, both signs at d=99/100, and the
failure on d=999999/1000000 when the denominator margin is dropped
(mu=nu=1). File `/private/tmp/prime-cover-upsum-controls.lean`, log with
the same stem: exit 0, no native computation. These are scalar controls,
not evidence for untested graph sizes or an asymptotic promotion.

Validation: target 4,234/full 4,238 jobs, exit 0, logs
`/private/tmp/prime-cover-upsum-target.log` and
`/private/tmp/prime-cover-upsum-full.log`. Four new roots use propext,
Classical.choice, Quot.sound only. Selected Solution roots still use
sorryAx. No owner placeholders or trusted-computation escapes. Semantic
lint has exactly the same 93 error lines as the prior downsum baseline,
none in this owner; style passes with the unchanged optional nolints warning.
Scratch API repairs replaced an inaccessible private helper by existing
public selected/isolated formulas, made the source-degree rewrite explicit,
and supplied the explicit summand in sum_coe_sort. No assumptions weakened.

Owner 4,548 -> 4,786 (+238), audit +4; local Lean 25,322 -> 25,564 (+242).
Owner SHA-256 `ff92df96305484bc7618a7e10f61cbade4e274a2a7cf6f802908d19070b1d241`.
Eight modules/five owners. Both manuscripts/pins unchanged, no commit/push.
Strict narrowing: both weighted centre rows CLOSED. Only leaf rows and
the exact support-sum assembly remain for the signed one-source estimate;
R4c global Gram/HS/operator estimates and R4d isometry remain open.
Tracking D31 3/8 (37.5%), MG2 1/2, selected proofs 0/4 unchanged.

Next: bound the actual up/down leaf coefficients by C/mu^2, sum their
degree weights using harmonic prime multipliers, and assemble all support
rows. Do not replace the harmonic sum by minimum-leaf times leaf count:
that loses the needed down-star reciprocal weight. Do not reopen centre
or kernel rows or claim a global operator bound from the one-source sum.

### R4b complete one-source continuation closure

Classification: CLOSURE, existing AlmostAllSpectralBudget owner. Literal
exit theorem: eventually, for every allowed moving a<=X^theta with fixed
finite prime S and theta<1/2, the actual full-star molecule residual satisfies
`norm(residual)^2 <= C log(X)^5`. No assumed response coefficients, support
enumeration, denominator gap or collision bound remains. The exponent five
is a sufficient fixed logarithmic power for D31, not a sharp exponent claim.

New roots and their consumers:
- `exactPrincipalMoleculeSignedInteriorVector_apply_canonicalUpLeaf` and
  `eventually_powerRange_signedCanonicalLeaf_abs_le`: the actual up response
  and selected/unselected down response give the uniform bound 2000/mu^2.
  Reuses the existing exact two-mode synthesis and power-window producers.
- `sum_smallPrimeDegree_largePrimeLeaves_le` and
  `sum_smallPrimeDegree_canonicalLeaves_le`: write a leaf as c*p and retain
  its reciprocal multiplier before summing. The sum of leaf degrees is
  at most (2+1/log(2))*(X/c)*log(X). Isolated targets have no leaves.
- `sum_canonicalExitTarget_reciprocal_le_log`: total canonical reciprocal
  target mass is at most (2+1/log(2))*log(X). Up-labels use the harmonic
  reciprocal-prime sum; down-targets use omega(a), not a fixed-cardinality
  assumption.
- `eventually_powerRange_degreeWeightedCanonicalLeaves_le_logFourth`:
  the entire actual leaf row is at most
  2000^2*64*(2+1/log(2))^2*log(X)^4. The scale input
  mu^2 >= X/(8*a*log(X)) and a^2<=X absorb X/mu^4.
- `exists_canonicalExitIndex_of_mem_compression` and
  `signedInterior_degreeWeighted_le_canonicalRows`: every coordinate in
  the full compression, not just the first-exit source, is covered by a
  canonical star. Nonnegative overcounting assembles centres and leaves.
- `eventually_powerRange_signedDegreeWeighted_le_logFourth`: sums both
  previously closed centre rows and the complete leaf row.
- `eventually_powerRange_exactPrincipalMoleculeResidual_sq_le_logFifth`:
  consumes that sum and the already proved degree-weighted kernel and
  exterior-multiplicity estimate. This is the R4b exit theorem.

Target sanity: the discarded minimum-leaf times leaf-count estimate loses
a power for down-stars. Keeping 1/p and 1/c is essential. No new prime
estimate, molecule definition, normalization or module was introduced.
The scratch proof passed at `/private/tmp/prime-cover-leafsum-check9.log`;
API repairs only addressed sum-type definitional equality, looplessness and
already-solved tactic goals. No mathematical hypothesis was weakened.

Validation: target 4,234/full 4,238 jobs, exit 0, at
`/private/tmp/prime-cover-leafsum-target.log` and
`/private/tmp/prime-cover-leafsum-full.log`. All ten new Audit roots use only
propext, Classical.choice and Quot.sound. All four selected Solution roots
still use sorryAx. No owner sorry/admit/axiom/native_decide/ofReduceBool.
Semantic lint has exactly the same 93 error lines as the prior upsum log,
none in this owner; style passes with the existing optional nolints warning.
The manuscript hashes and all three dependency pins are unchanged.

Owner 4,786 -> 5,308 (+522); audit +10. Local Lean including lakefile
25,564 -> 26,096 (+532), still eight modules/five owners.
Owner SHA-256 `e47a316e3dbbd466d067fee85942c64d07da9ef5f2404518468f5ac704f42642`.
No commit/push; unrelated staged and unstaged work is preserved.

Progress: R4a CLOSED, R4b CLOSED, R4c/d OPEN. D31 checklist remains
3/8 (37.5%), MG2 1/2, selected public roots 0/4. Unlike the preceding
row checkpoints, this iteration closes the entire one-source product.

Next bounded product: prove the actual complete-prefix projected residual
HS budget from `projectedFullStarFrameResidual_eq`, the new one-source
bound, the existing full-tail rate/LZ=0 identity and the bounded actual
normalization. Then the collective operator/Gram estimates, followed by
isometry. The operator estimate is not supplied by a per-column or HS bound.
Do not reopen centre/leaf coefficient rows or optimize the log exponent.

### R4c actual projected-prefix Hilbert--Schmidt closure

Classification: CLOSURE in the existing approved owner. Literal theorem:
eventually for fixed finite prime S and theta<1/2, for every complete prefix
K<=X^theta, including K=0,
`matrixFrobeniusNorm(projectedFullStarFrameResidual S X K)^2
 <= C K log(X)^5`.
The matrix is the actual projected, column-normalized synthesis against
its actual diagonal molecule roots. It is not a free matrix or the raw
unprojected family; final symmetric whitening remains R4d.

Seven new audited roots:
- `eventually_oneExitSmallPrime_apply_sq_le_sqrt`: the pinned real Schur
  estimate controls the complex H action by 16*C_res^2*sqrt(X)*norm(x)^2.
  The logarithmic denominator is safely discarded for this consumer only.
- `eventually_powerRange_adjacency_discardedFullMolecule_sq_le_logCube`:
  actual A on the phase-fixed discarded vector equals H on that vector
  because the forest action is zero. The quantitative tail rate, a<=sqrt(X),
  and omega(a)<=log(X)/log(2) give O(log^3 X).
- `norm_phasedFullStarMolecule_residual`: phase fixing and complexification
  preserve the literal raw residual norm.
- `normalizedProjectedFullStarMolecule_residual_sq_le`: finite bound by
  eight times the sum of raw residual squared and adjacency-on-tail squared.
  The only normalization premise is norm(P f)>=1/2; projection is the
  actual one-exit projection, not an arbitrary assumed contraction.
- `eventually_powerRange_projectedFullStarMolecule_residual_sq_le_logFifth`:
  supplies that normalization and both response producers, with constant
  8*(C_raw+C_tail). No abstract quantitative hypotheses remain.
- `card_moleculeCenter_le`: the actual positive allowed prefix has at most
  K elements, including its empty boundary case.
- `eventually_powerRange_projectedFullStarFrameResidual_hsSq_le`: exact
  residual-column identification, Frobenius column sum, and actual prefix
  cardinality assemble the entire projected HS bound.

Precedent/reuse: existing matrix Frobenius definition and norm-square API,
actual projected frame/residual definitions, exact LZ=0, complex Schur
bound, actual normalization, R4b raw residual and quantitative tail. No
new definition, imported module, analytic premise, or molecule coordinate.
The formerly private complexification/application calculations were
specialized directly to their concrete consumer, not ported as whole files.

Validation: scratch check4 and target 4,234/full 4,238 jobs pass, logs
`/private/tmp/prime-cover-prefix-hs-check4.log`,
`/private/tmp/prime-cover-prefix-hs-target.log`,
`/private/tmp/prime-cover-prefix-hs-full.log`. All seven new roots use only
propext, Classical.choice and Quot.sound. The four selected Solution roots
still contain sorryAx. No owner placeholders or trusted computation.
Semantic lint is byte-identical on its 93 inherited error lines to the
leafsum baseline; none in this owner. Style passes with the existing
optional nolints warning. Git diff whitespace and YAML checks pass.

Controls in `/private/tmp/prime-cover-prefix-hs-controls.lean` pass with
an empty log: the K=0 prefix has cardinality zero, and N identical unit
columns have operator norm squared at least N. The latter is an all-N
finite-dimensional guard against treating a per-column/HS estimate as
the desired collective operator estimate. No native computation is used.

Owner 5,308 -> 5,620 (+312); audit +7. Local Lean including lakefile
26,096 -> 26,415 (+319), same eight modules/five owners.
Owner SHA-256 `853fb758ffeb3fc0e978962df3a5385b07ac57467688be31fd4bb8b9475391ef`.
The previous owner is preserved byte-for-byte before the appended section.
Both manuscripts and dependency pins unchanged. No commit/push.

Strict progress: R4c projected HS CLOSED. R4c operator/Gram and R4d are
OPEN. Checklist D31 3/8 (37.5%), MG2 1/2, selected proofs 0/4.
Next named consumer is the residual-Gram Schur bound in (6.8a)--(6.8b),
including the coherent B^2/sqrt(X) term, then raw/projected Gram smallness.
Do not replace it by the weaker HS bound or reopen the completed source
coefficient rows. Keep final symmetric reorthonormalization and its
residual transfer explicitly separate until verified.

### R2 admitted correction reuse

Destination: existing `FirstExitTarget`; no new owner or module. Port only
the five finite helpers
`abs_upStarCorrection_le_sixtyfour_mul`,
`abs_downStarCorrection_le_sixtyfive`,
`sum_allowedPrime_reciprocal_le_one_add_log`,
`primeFactors_card_le_log_div_log_two`,
`abs_firstExitCorrection_le_of_power_ratio_bounds`,
and the constant, positivity and
`eventually_powerRange_firstExitCorrection_le_log` declarations.

Exact historical working snapshots:
- `PowerBandFirstExitCorrection.lean`:
  `9857c917fdb75b3b9182a1ec8eaa36e4638bf03ea1bd2951af792e2c1534bd47`.
- `PowerBandDegreeRatios.lean`:
  `b95b77492baed0ba03c0052052613050e0668feba538f112c799c98954d5b206`.

Consumer: R2 regularity and `|M| <= C log X`, then the complete-prefix
sorting comparison in R3/R6. Existing power-range ratio bounds are reused.
The only additional direct import is Mathlib's harmonic bounds. Do not
import the historical BHP/sorting consumers. These are recorded file
snapshots, not claims of immutable provenance or Palomar completion.

The eight declarations above were transplanted verbatim (217 proof/source
lines). Two new adapters are admitted on the same existing owners:
`eventually_powerRange_exactPrincipalMoleculeRoot_pos` extracts positivity
from the checked root window; and
`fullAdjacencyEigenvalueAtArithmeticRank_eq_lambdaAtArithmeticRank` is
`rfl`, exposing the public ordered index without a permutation. No new
definition, abstraction, module, analytic dependency or toolchain is needed.

### R2 literal consumer audit

| Native object / input | Existing Lean producer and exact scope |
|---|---|
| Full boundary plus targets, including inactive singleton exits | `exactPrincipalMoleculeSupport` is the entire star support union `firstExitCompressionSupport`; the pinned latter explicitly includes `firstExitIsolatedVertices` |
| Literal principal adjacency | `exactPrincipalMoleculeMatrix_apply_eq_primeCover`, for prime deletion sets and centre at most the square-root cutoff; the power-range root-window producer supplies this cutoff condition eventually |
| Unit ambient vector and both boundary modes/kernel | `norm_exactPrincipalMoleculeAmbientVector`, `exactPrincipalMolecule_boundary_eq_signedModes_add_kernel`, and the exact eigenvector equation; no one-mode substitution |
| Positive continuation root | `eventually_powerRange_exactPrincipalMoleculeRoot_pos`, from the existing 1/100 root window |
| Scalar S1 | `eventually_powerRange_exactPrincipalMoleculeRoot_targetDefect_le`: actual `pi + M`, error `C a/log X`; not the stronger native intermediate `o(1)` |
| Regular correction and logarithmic size | `eventually_powerRange_firstExitCorrection_le_log`: all denominators nonzero and `abs M <= (6144 + 65/log 2) log X`, uniformly on each fixed power range below one half |
| S2 at the prescribed full-graph rank | `eventually_powerRange_fullAdjacency_oneExit_sq_comparison` and the new definitional rank bridge: nonnegative squared discrepancy at most `57344 * sqrtCutoffResidualConstant^4 * a/log X` |

All eventual producers fix `S` and the exponent before the threshold and
quantify over every allowed centre in that power range. To cover a complete
prefix `c <= C_star B`, the later consumer must choose an exponent strictly
between the retained exponent and one half; this is not permission to use
fixed-centre asymptotics for a moving centre.

The chosen unit vector has arbitrary spectral-basis sign. The existing
absolute positive-mode coefficient bound is at least one half eventually,
so a positive-overlap phase can be chosen. The projected, phase-aligned
collective synthesis and its near-Gram/actual residual bounds belong to R4;
neither unit normalization nor this audit discharges them. The local
`TerminalSchur` core budget is not counted as a global D31 estimate.

R2 validation: `lake build` passed (4,222 jobs); the expanded submission
audit distinguishes the reusable standard-axiom inputs from the four public
`sorryAx` roots. The local rank equality and positivity calibrations passed.
Proof-owner placeholder/trusted-computation scans and `git diff --check`
passed. Both manuscript hashes and all dependency pins are unchanged.
R2 is CLOSED for these scalar/structural inputs, not for R4--R7.

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

### R4c signed exterior leaf-Gram row closure

Classification: CLOSURE; existing AlmostAllSpectralBudget owner, no new
module, definition, analytic premise, or coordinate family. This closes
the leaf contribution in manuscript (6.8b), not the complete operator norm.

For the actual signed exterior responses g_a, the new theorem proves,
eventually and uniformly on every complete power prefix K <= X^theta,

  sum_b sum_{v with a prime divisor > sqrtCutoff X} |g_a(v) g_b(v)|
    <= 128 (4000/log 2)^2 K^3 (log X)^4 / X.

The source a and every partner b are literal MoleculeCenter vertices.
The result includes diagonal pairs; the earlier one-source estimate is
still used for the sharper diagonal part of the complete Schur row.
The empty-prefix case has no source. theta < 1/2 is fixed; no moving
cutoff, degree, response, or collision hypothesis remains.

Six public roots, in dependency order:
- `largePrime_dvd_of_smallPrimeAdj`: a prime above Y is preserved by
  every actual small-prime edge, in either orientation.
- `largePrime_not_dvd_canonicalExitTarget`: all canonical centres are
  Y-smooth, including inactive up-centres above Y.
- `eventually_powerRange_signedLargePrimeCoordinate_abs_le`: every
  nonzero large-prime response coordinate is a canonical leaf, so the
  existing 2000/mu^2 bound applies.
- `eventually_powerRange_signedExteriorLeaf_abs_le`: restrict the actual
  neighbor sum to first-exit support and use omega(a)+omega(v), giving
  (4000/log 2) log X / mu_a^2 per exterior output.
- `eventually_powerRange_signedExteriorLeaf_pair_sum_le`: sum products
  over actual graph vertices, at most 2X; obtain
  2 (4000/log 2)^2 X log^2 X / (mu_a^2 mu_b^2).
- `eventually_powerRange_signedExteriorLeaf_gramRow_le`: the existing
  actual degree lower bound and prefix cardinality give the displayed row.

Reuse: R4b canonical leaf coefficients, full compression-support cover,
exterior incoming multiplicity, prime-factor logarithmic bound, PNT degree
scale, and R4c prefix cardinality. No four-prime collision classification
is needed on this leaf component: the graph-coordinate count suffices.
The centre-output family cannot use that count and remains open.

Validation: scratch check3, target 4234 and full 4238 jobs pass. Six new
roots print only propext, Classical.choice, Quot.sound. Four selected
Solution roots still use sorryAx. Owner placeholder/trusted-computation
scan is empty. Semantic lint retains precisely the same 93 inherited
error lines, none in this owner. Style passes with the existing optional
nolints-file warning. Exact controls pass for the empty prefix, the actual
2->1 edge showing why p>Y is necessary, and all-N coherent rank-one columns.
Logs: /private/tmp/prime-cover-leaf-gram-{target,full,lint,style,controls}.log.
git diff --check passes; both manuscript hashes and all pins are unchanged.

Owner 5620 -> 5894 (+274), audit +6; local Lean 26415 -> 26695 (+280).
Eight modules/five owners, no new production files. Preexisting owner text
is byte-for-byte preserved. Owner SHA-256:
418ddafad02d1448c8593f133f42e2663ac6cbd515b4ccc8c78f178e6ed4e3fe.
No commit/push. Checklist 3/8 (37.5%), MG2 1/2, public proofs 0/4 unchanged.

Next: for DISTINCT sources, bound common centre-type two-step outputs by
O(Y log^C X), retaining the one free common prime; then consume the actual
centre coefficients to obtain (6.8a). The diagonal has a separate producer.
After that, assemble operator transfer, raw/projected Gram smallness,
and symmetric reorthonormalization. Do not reopen the leaf count or promote
this component bound to a complete-frame estimate.

### R4c signed off-diagonal centre-Gram row closure

Classification: CLOSURE in the existing approved owner. This completes
the actual signed centre-output row (6.8a), with the coherent contribution
retained. The preceding leaf row (6.8b) is unchanged. Neither component
alone is the complete projected operator theorem.

Literal result, with g_a the actual signed exterior response:

  sum_{b in prefix K, b != a} sum_{v without a prime divisor > Y}
    |g_a(v) g_b(v)|
      <= (128/log 2) (20000/log 2)^2 K^2 log^4 X / sqrt X.

S is a fixed finite prime deletion set, theta<1/2, and eventually all
K<=X^theta and actual prefix sources a are covered. K=0 is vacuous.
No collision, coefficient, support or PNT-scale premise remains in this
row theorem. The diagonal is intentionally excluded; the R4b signed
degree-weighted bound is its next input, not a distinct-source argument.

The finite count is stronger and simpler than a general four-word divisor
enumeration. For distinct sources a,b, a nonreturning collision
a -> t -> v <- u <- b forces at least one prime on the first path to
divide a or b. Otherwise both steps are upward, and cancellation against
the other two prime steps forces a=b. One prime remains free up to Y.
Eight oriented natural-number values per anchored/free pair therefore give

  #common two-step outputs, excluding a <= 8Y(omega(a)+omega(b)).

This counts actual output vertices, not representations or an averaged
divisor sum. The actual signed residual support supplies the two paths.
Canonical centres, including inactive up-targets, are Y-smooth; small-prime
edges preserve large-prime divisibility. Thus a smooth nonzero interior
response is a genuine centre and its established coefficient is <=10000/mu.
Incoming multiplicity gives <=(20000/log 2) log X/mu per exterior output.
The count yields the pair bound with numerator
(16/log 2)(20000/log 2)^2 Y log^3 X. PNT gives
1/(mu_a mu_b)<=8K log X/X; prefix cardinality and Y<=sqrt X close the row.

Eight new public roots:
- `prime_dvd_endpoints_of_twoStep_collision`
- `card_common_twoStep_outputs_le`
- `exists_canonicalCenter_of_signedInterior_ne_zero`
- `eventually_powerRange_signedSmallPrimeCoordinate_abs_le`
- `eventually_powerRange_signedExteriorCentre_abs_le`
- `exists_twoStep_of_signedExteriorCentre_ne_zero`
- `eventually_powerRange_signedExteriorCentre_pair_sum_le`
- `eventually_powerRange_signedExteriorCentre_gramRow_le`

Three elementary helpers are private. No new definition, import, module,
analytic input or coordinate family. Existing source/support/degree APIs
and the prior large-prime-preservation lemma are reused.

Validation: scratch check7 and target 4234/full 4238 jobs pass. All eight
new audit roots use only propext, Classical.choice, Quot.sound; the four
selected Solution roots still have sorryAx. Owner placeholder/native scan
is empty. Semantic lint has the identical 93 inherited error lines, none
in this owner. Style passes with the existing optional nolints warning.
Controls pass: empty prefix; endpoint-anchor failure on a returning path;
an actual graph counterexample when distinct sources are omitted; and the
actual family 2->6->6q<-6<-3 for every prime q>=7 at X=q^2, Y=q.
Logs: /private/tmp/prime-cover-centre-gram-{target,full,lint,style,controls}.log.

Owner 5894 -> 6448 (+554), audit +8. Local Lean 26695 -> 27257 (+562).
Eight modules/five owners; no new production files. Prior owner text is
byte-for-byte preserved. Owner SHA-256:
c45e08a8b5d3efaffda05b0ceab7dab6bd9e1193a3677a2a9ce5e6d94b3b0c7e.
Both manuscript hashes and dependency pins remain unchanged; diff-check
passes. Nothing staged, committed or pushed by this iteration.

Progress stays 3/8 (37.5%), MG2 1/2, public proofs 0/4.
Next bounded product: assemble the signed residual diagonal and the two
off-diagonal rows into its Schur operator estimate. Then retain the
quantitative kernel/tail and normalization costs when transferring to the
actual projected frame. Raw/projected Gram smallness and R4d isometry
remain separate exits. Do not reopen the two-step count or discard the
coherent K^2/sqrt X term.

### R4c complete signed residual operator closure

Classification: CLOSURE in the existing approved owner. The previous
leaf and centre rows now have their literal collective consumer:

  ||J_signed||_op^2 <= C log^5 X (1 + K^2/sqrt X),

uniformly for every complete prefix K<=X^theta, with S fixed and
theta<1/2. Each column is the actual coordinate-complement projection
of H applied to the signed full-interior response. There is no free
collision bound, coefficient bound, row-sum hypothesis or PNT-scale
certificate in this eventual theorem. This is still BEFORE kernel
restoration, phase/projection/normalization and symmetric whitening.

The diagonal is not obtained from the full residual, where signed and
kernel contributions could cancel. Its proof instead uses the established
compression support, incoming multiplicity omega(a)+omega(v), adjacency
sum interchange and signed degree-weighted response. It gives C log^5 X.
For distinct columns, split the output coordinates exactly into those
with and without a large-prime divisor. The two previously proved rows
give C K^3 log^4 X/X and C K^2 log^4 X/sqrt X. Since K<=sqrt X, the first
is absorbed by the second. Summing with the diagonal proves the complete
absolute-product row bound.

The finite matrix step reuses Paper I's weighted Schur quadratic-form
theorem and Mathlib's Hermitian Rayleigh quotient and C-star norm identity.
A private helper handles signed symmetric matrices by absolute-entry
majorization. The actual Gram is not assumed entrywise nonnegative.
Mathlib's ||J* J||=||J||^2 then gives the displayed operator estimate.
The matrix is explicitly typed before taking its Euclidean operator norm;
it is not the entrywise function norm.

Four new public roots:
- `signedExterior_sq_le_degreeWeightedInterior`
- `eventually_powerRange_signedExterior_sq_le_logFifth`
- `eventually_powerRange_signedExterior_absoluteGramRow_le`
- `eventually_powerRange_signedExterior_operatorNorm_sq_le`

One private finite Schur helper; no new definition, module, import or
analytic input. Existing source, coefficient, diagonal and two row
producers are consumed rather than restated as assumptions.

Validation: scratch check5 passed; integration adds explicit Filter and
Classical scopes. Final target 4234/full 4238 jobs pass. All four new
audit roots use only propext, Classical.choice, Quot.sound; the four
selected Solution roots still have sorryAx. Owner placeholder/native scan
is empty. Semantic lint has exactly the same 93 inherited error lines,
none in this owner. Style passes with the existing optional nolints warning.
Exact controls pass: empty prefix, zero matrix, nonzero diagonal with no
off-diagonal partners, a negative Gram entry, and coherent columns whose
operator norm grows with the number of sources. No finite computation
is used as an asymptotic proof.
Logs: /private/tmp/prime-cover-signed-operator-{target,full,lint,style,controls}.log.

Owner 6448 -> 6717 (+269), audit +4. Total local Lean 27257 -> 27530 (+273).
Eight modules/five owners. Prior owner text reconstructs byte-for-byte
to c45e08a8b5d3efaffda05b0ceab7dab6bd9e1193a3677a2a9ce5e6d94b3b0c7e.
New owner SHA-256:
3455e9052a261e2f90ebfe36a8967e14dc6b9df5545189a96a77424014c0361a.
Both manuscript hashes and all dependency pins are unchanged. Diff-check
and YAML parse pass. Nothing staged, committed or pushed this iteration.

Progress remains 3/8 (37.5%), MG2 1/2, public proofs 0/4.
Next bounded product: restore the kernel response and transfer the
quantitative tail and normalization costs to the actual projected
complete-prefix residual operator. Do not weaken a per-column kernel or
tail estimate before summing if that would lose the consumed K^2/sqrt X
scale. Raw/projected Gram smallness and R4d whitening remain separate.
The signed operator theorem closes its component, not the R4 exit test.

### R4c actual projected residual operator closure

Classification: CLOSURE in the existing approved owner. Kernel restoration,
phase, the full discarded tail, projection and column normalization now
transfer the signed operator bound to the actual projected frame:

  ||projectedFullStarFrameResidual||_op^2
    <= C log^5 X (1 + K^2/sqrt X),

eventually for all complete prefixes K<=X^theta, with S fixed and theta<1/2.
Together with the earlier actual projected Hilbert--Schmidt bound
C K log^5 X, both residual budgets are closed BEFORE symmetric whitening.
This is not yet an isometric frame theorem or an R4 exit.

The quantitative costs retained before summing are
||g_kernel,a||^2 <= C a log^3 X/X and
||A z_a||^2 <= C a log^3 X/sqrt X. The latter uses the full discarded
molecule tail, including down-star kernel terms. Operator norm squared
is bounded by the sum of column squared norms, giving K^2 rather than
discarding the centre dependence. The exact projected residual identity
is (P R - P A Z) N, with P contractive and ||N||<=2. Real-to-complex
transfer has a dimension-independent factor 2; phases have norm at most 1.

Seven new public roots:
- `eventually_powerRange_kernelExterior_sq_le_scale`
- `eventually_powerRange_adjacency_discardedFullMolecule_sq_le_scale`
- `eventually_powerRange_kernelExterior_operatorNorm_sq_le`
- `eventually_powerRange_fullMoleculeResidual_operatorNorm_sq_le`
- `eventually_powerRange_adjacency_fullStarFrameTail_operatorNorm_sq_le`
- `eventually_powerRange_phasedFullStarFrameResidual_operatorNorm_sq_le`
- `eventually_powerRange_projectedFullStarFrameResidual_operatorNorm_sq_le`

Two private finite rectangular-matrix norm helpers; no new production
definition, module, import or analytic input. Actual root, gap and
nonresonance producers discharge the decomposition hypotheses.

Validation: scratch check6 and integrated target pass; target 4234/full
4238 jobs, exit 0. All seven new audit roots use only propext,
Classical.choice, Quot.sound. The four selected Solution roots still
contain sorryAx. Owner placeholder/native scan is empty. Semantic lint
has exactly the same 93 inherited error lines, none new or in this owner.
Style passes with the existing optional nolints warning. Exact controls
pass for an empty prefix, unit negative phases, a nonunit normalization
diagonal of norm 2, and coherent columns with growing operator norm.
Logs: /private/tmp/prime-cover-projected-operator-{target,full,lint,style,controls}.log.

Owner 6717 -> 7246 (+529), audit 141 -> 148 (+7). Total local Lean
27530 -> 28066 (+536); eight modules/five owners. Prior owner text
reconstructs byte-for-byte to
3455e9052a261e2f90ebfe36a8967e14dc6b9df5545189a96a77424014c0361a.
New owner SHA-256:
2d6d83d3ed9cf4443a6c6ab8a0bad5355caa336c42d770ac9cbf34738fee05cd.
Both manuscripts and all dependency pins are unchanged. Nothing staged,
committed or pushed by this iteration.

Progress remains 3/8 (37.5%), MG2 1/2, public proofs 0/4.
Next bounded product: prove raw/projected Gram smallness for the actual
complete-prefix columns. Then construct symmetric whitening, prove the
isometry, and transfer both residual bounds through the commutator
estimate. Do not reopen the now-closed projected residual estimates or
count column normalization as orthonormality.

### R4c actual Gram projection and normalization transfer

Classification: CLOSURE. The actual discarded complete prefix now satisfies

  ||Z||_HS^2 <= C log^3 X K^2/X = o(1),

uniformly over K<=X^theta, S fixed and theta<1/2. This consumes the
previous full-tail estimate, including its down-star kernel contribution.
The per-column term a^3 omega(a) log X/X^2 is bounded using a^2<=X
and omega(a)<=log X/log 2 before summing over at most K centres.
The power/log comparison is proved using the existing asymptotic lemma;
it is not an assumed Gram or independence property.

Pythagoras for the actual projection gives n_a^2+||z_a||^2=1.
With the produced n_a>=1/2, n_a^(-2)-1<=4||z_a||^2. Consequently
||N* N-I||<=4||Z||_HS^2 and ||N||<=2. The exact Gram subtraction
already in the owner then gives the literal unconditional comparison

  ||Gamma_projected-I|| <= 4||Gamma_raw-I|| + 8||Z||_HS^2.

The remaining right-hand raw Gram error has NOT been bounded in this
iteration. This closes projection/normalization costs, not Gram smallness
or the R4 exit. Next is the raw adjacent/shared-target overlap estimate,
followed by symmetric whitening and transfer of the two residual budgets.

Five new public roots:
- `eventually_powerRange_fullStarFrameTail_hsSq_le`
- `eventually_powerRange_fullStarFrameTail_hsSq_lt`
- `eventually_powerRange_projectedFullStarNormalization_gram_sub_one_le`
- `eventually_powerRange_projectedFullStarNormalization_norm_le_two`
- `eventually_powerRange_projectedFullStarFrame_gram_error_le`

One private column-to-HS comparison; existing rectangular norm helper reused.
No new production module, definition, import, analytic input or proof hole.
Scratch check5 and integrated target pass. Full build: 4238 jobs, exit 0.
All five new audit roots use only propext, Classical.choice, Quot.sound;
the four selected Solution roots still contain sorryAx. Semantic lint:
exactly the previous 93 inherited error lines, no new owner finding.
Style passes with the existing optional nolints warning. The initial style
invocation used file paths and failed; rerun with module names passed.
Exact controls pass: actual empty prefix, normalization endpoint 1/2,
failure of factor 4 below that endpoint, zero tail, and repeated unit
columns whose Gram is not the identity. These are not asymptotic evidence.
Logs: /private/tmp/prime-cover-gram-transfer-{target,full,lint,style,controls}.log.

Owner 7246 -> 7512 (+266), audit 148 -> 153 (+5); total local Lean
28066 -> 28337 (+271), eight modules/five owners. The earlier owner text
reconstructs byte-for-byte to
2d6d83d3ed9cf4443a6c6ab8a0bad5355caa336c42d770ac9cbf34738fee05cd.
New owner SHA-256:
c4cd064a92980435fe0bff09d8175115eef1e1d01e41f24ce1ed4e5d3c1b6b3c.
Both manuscript hashes and all pins are unchanged. No commit or push.
Overall stays 3/8 (37.5%), MG2 1/2, selected public proofs 0/4.

### R4c actual adjacent-molecule overlap

Classification: CLOSURE of the adjacent pointwise overlap, not of R4.
For fixed finite prime set S and theta<1/2, eventually all actual allowed
small-prime-adjacent centres in the power range satisfy

  mu_a mu_b |inner(f_b,f_a)| <= C eta_X log^3 X.

Here f is the actual unit full-star principal molecule, not its one-mode
replacement. The complete closed star at an adjacent centre lies in the
first-exit compression, so its boundary pairs to zero with the residual.
Self-adjointness gives the exact signed root-difference overlap identity.
The produced interior estimate is mu_a ||interior_a|| <= 100 eta_X.
The up-degree ratio <=15/16 and both 1/100 root windows give a relative
adjacent root gap >=max(mu_a,mu_b)/100 in both orientations. Together with
the existing residual bound this proves the displayed actual overlap;
no gap, overlap, residual or interior estimate is left as a hypothesis.
This gap is for prime-adjacent centres, not consecutive arithmetic ranks.

Seven new public roots, all in the existing owner:
- `adjacent_starSupport_subset_firstExitCompression`
- `real_inner_boundary_residual_eq_zero_of_adjacent`
- `roots_sub_mul_inner_fullMolecules_eq_residual_pairings`
- `abs_roots_sub_mul_abs_inner_fullMolecules_le_of_adjacent`
- `eventually_powerRange_energy_mul_norm_fullInterior_le`
- `eventually_powerRange_adjacent_fullMoleculeRoots_gap`
- `eventually_powerRange_adjacent_fullMoleculeOverlap_energyProduct_le`

One private scalar cancellation helper; no new module, definition, import
or dependency. Scratch check4, target 4234 and full 4238-job builds pass.
Seven new audit roots use only propext, Classical.choice, Quot.sound;
the four selected public proofs still contain sorryAx. Semantic lint exits
1 with exactly the previous 93 inherited error lines, none new in the owner.
Style passes with the existing optional nolints warning. Exact controls
pass: equal centres cannot satisfy the positive relative gap, the diagonal
residual identity is zero without division, both rational gap constants
close, and the actual 1--2 edge at X=16 activates full-star containment.
Logs: /private/tmp/prime-cover-adjacent-overlap-{target,full,lint,style,controls}.log.

Owner 7512 -> 7772 (+260), audit 153 -> 160 (+7); local Lean
28337 -> 28604 (+267), eight modules/five owners. Earlier owner source
reconstructs byte-for-byte to
c4cd064a92980435fe0bff09d8175115eef1e1d01e41f24ce1ed4e5d3c1b6b3c.
Current owner SHA-256:
7f70a3c137c847527d0e104747d7c6a6108e6396615be7b799b886241a20ee46.
Frozen manuscripts, pins and HEAD unchanged; no stage, commit or push.

Next single product: the non-adjacent shared-target overlap bound. Then
sum both overlap classes to raw Gram smallness, apply the already-proved
projection transfer, and whiten with both residual budgets retained.
Progress stays 3/8 (37.5%), MG2 1/2, selected public proofs 0/4.

### R4c non-adjacent support and shared-target count

Classification: CLOSURE of the finite support/counting input, not of the
quantitative non-adjacent overlap or R4. Actual full molecules satisfy:
- distinct non-adjacent boundary cross terms vanish;
- an intersecting interior coordinate belongs to one target star adjacent
  to both sources, also for isolated inactive up-targets;
- the number of shared target centres is at most 2(omega(a)+omega(b)),
  hence at most 4 log X/log 2 on actual graph vertices;
- with no common target the full molecules are exactly orthogonal.

The endpoint-divisor proof retains intermediate divisor targets (e.g. 1
and 6 share 2), not only gcd/lcm targets. The logarithmic count is weaker
than the manuscript's at-most-two count but pays only a fixed log power
in the same R4 Gram consumer; no final target or error scale changes.
`exists_neighboringStar_of_mem_firstExitCompression` adapts the existing
private `exists_targetCenter_of_mem_firstExitCompressionSupport` in
TerminalSchur.lean:2285, dropping its unused equality from the isolated
case. All other inputs are existing public support, symmetry and divisor
lemmas. No coordinate definition, module, import or analytic input added.

Nine public roots:
- `prime_dvd_endpoint_of_commonTarget`
- `card_common_smallPrimeTargets_le`
- `exists_neighboringStar_of_mem_firstExitCompression`
- `targetCenters_eq_of_starSupport_inter`
- `exists_commonTarget_of_mem_firstExitCompressions`
- `disjoint_boundary_firstExitCompression_of_not_adjacent`
- `inner_fullMolecules_eq_inner_interiors_of_not_adjacent`
- `card_common_smallPrimeTargets_le_log`
- `inner_fullMolecules_eq_zero_of_no_commonTarget`

Scratch check5, target 4234 and full 4238-job builds pass. Nine new roots
use only propext, Classical.choice, Quot.sound. Exact controls cover the
failure at equal sources, sibling and intermediate divisor targets, an
actual common graph target, and unit self-overlap. Style passes (existing
optional nolints warning). Semantic lint exits 1 with the identical 93
inherited findings; none new in the owner. Owner placeholder/native scan,
YAML and diff checks pass. Logs:
/private/tmp/prime-cover-shared-targets-{target,full,lint,style,controls}.log.

Owner 7772 -> 8022 (+250), audit 160 -> 169 (+9), total local Lean
28604 -> 28863 (+259). Eight modules/five owners unchanged. Previous
owner reconstructs to 7f70a3c137c847527d0e104747d7c6a6108e6396615be7b799b886241a20ee46;
new owner is 13c061f483ada7fb7f2b978c93c279642c6ae882f936ca436a11708d9f858c4f.
Both manuscripts, pins and HEAD unchanged. No stage, commit or push.

Next quantitative input: on each actual canonical target, prove
mu_a ||P_target interior_a|| <= C, using
`PrimeStar.unique_smallPrime_neighbor_in_largePrimeStar` in both directions
(or the isolated singleton case) for the coupling contraction, then the
already-produced first-exit gap. Combine that bound with the finite
shared-target reduction before summing the complete-prefix Gram.
Progress stays 3/8 (37.5%), MG2 1/2, selected public proofs 0/4.

### R4c full one-target response and non-adjacent overlap

Classification: CLOSURE of the remaining pointwise overlap input.
The actual source-star/target-star coupling is a partial coordinate
matching: `unique_smallPrime_neighbor_in_largePrimeStar` supplies both
orientations, with the isolated target treated as a singleton. A finite
Cauchy--Schwarz/counting argument proves coupling norm <=1. Coordinate
projection onto a target component commutes with L. Projecting the actual
full interior equation and using the produced compression gap therefore
gives, uniformly over every canonical target in the fixed power range,

  mu_a ||P_target interior_a|| <= 100.

This is the full principal molecule, including both signed modes and
kernel components. No norm of H, assumed per-target source bound, or
assumed overlap is used in the eventual conclusion. Canonical target
identification is supplied for every actual small-prime neighbour.
Finite Cauchy--Schwarz on the shared-target cover, followed by the previous
logarithmic common-target count, closes

  mu_a mu_b |inner(f_a,f_b)| <= (40000/log 2) log X

for distinct non-adjacent centres. No pairwise root separation is needed
in this case. The adjacent case remains the previously compiled producer.

Five new public roots:
- `norm_targetProjection_smallPrime_boundaryProjection_le`
- `gamma_mul_norm_fullInterior_on_canonicalTarget_le_one`
- `eventually_powerRange_energy_mul_norm_fullInterior_on_target_le`
- `exists_canonicalExitTarget_eq_of_smallPrimeAdj`
- `eventually_powerRange_nonadjacent_fullMoleculeOverlap_energyProduct_le`

Four private finite helpers; no new definition, module, import or analytic
dependency. Scratch check7, targeted 4234/full 4238-job builds pass. All
five new roots use propext, Classical.choice, Quot.sound only; four
selected public proofs remain sorryAx-dependent. Exact controls pass:
one-to-many coupling is not contractive, zero gap does not control the
response, actual lower-target contraction, and canonical up/down centres
including an up-target above the cutoff. Style passes with the existing
optional nolints warning. Semantic lint exits 1 with the same 93 inherited
findings and none new in the owner. Placeholder/native, YAML and diff
checks pass. Logs:
/private/tmp/prime-cover-one-target-response-{target,full,lint,style,controls}.log.

Owner 8022 -> 8358 (+336), audit 169 -> 174 (+5), total local Lean
28863 -> 29204 (+341). Eight modules/five owners unchanged. Earlier owner
reconstructs to 13c061f483ada7fb7f2b978c93c279642c6ae882f936ca436a11708d9f858c4f;
current owner f8dab39a714572393367277431cf566c4bfc659cbb6745fbf8c58a242788ea3f.
Both manuscript hashes, all pins and HEAD unchanged. No stage/commit/push.

Next exit product: complete-prefix Gram smallness using BOTH proved overlap
classes. Use energy weights or the manuscript Schur weights, retain the
restricted up-neighbour count K/a and down-divisor count, then apply the
already-proved projection/normalization transfer. Do not reopen individual
target responses. Symmetric whitening and transfer of both residual
budgets remain afterward. Progress stays 3/8 (37.5%), MG2 1/2, proofs 0/4.

## R4c collective Gram smallness — exit test CLOSED

This checkpoint supersedes the preceding next-exit paragraph. Both overlap
classes are now consumed, not merely recorded. For the actual phase-fixed
raw synthesis W and the actual normalized projected synthesis V:

  norm(W* W - I) <= C log^5(X) (eta_X K/X + K^2/X),
  norm(W* W - I) -> 0 and norm(V* V - I) -> 0,

uniformly for K <= X^theta with fixed theta < 1/2. Here * denotes adjoint.
The finite neighbour count retains K/a + omega(a), not X/a + omega(a).
The Schur weights are the actual star energies. The finite norm estimate
retains eta_X; its limit uses a deliberately weaker eta_X <= C sqrt(X),
which already suffices for this exit test. The phase is handled exactly.

Five new public roots in the existing owner:
- `card_prefix_smallPrimeNeighbors_le`
- `eventually_powerRange_fullMoleculeGram_weightedRow_le`
- `eventually_powerRange_phasedFullStarFrame_gram_error_le`
- `eventually_powerRange_phasedFullStarFrame_gram_error_lt`
- `eventually_powerRange_projectedFullStarFrame_gram_error_lt`

Provenance: adapt the existing finite degree proof to the restricted prefix;
generalize the existing private signed absolute-row Schur proof to positive
weights and retain its old constant-weight entry as a wrapper. Reuse pinned
Paper I weighted Schur, existing local overlap/energy producers, the existing
complexification bound and projection/normalization transfer. No new
definition, module, import or analytic dependency. One private scalar helper.

Scratch check7 PASS. Targeted 4234/full 4238-job builds PASS. All five new
roots use propext, Classical.choice, Quot.sound only; the four selected roots
remain sorryAx-dependent. Controls PASS: empty prefix, literal K cutoff,
down-prime neighbour, coherent accumulation despite small pointwise entries,
orthonormal Gram, actual eventual whitening threshold, and endpoint exclusion.
Style PASS with existing optional nolints warning. Semantic lint exits 1
with the exact same 93 inherited findings, no additions or removals.
Logs: /private/tmp/prime-cover-collective-gram-{target,full,controls,lint,style}.log.

Owner 8358 -> 8732 (+374), audit 174 -> 179 (+5), total local Lean
29204 -> 29583 (+379). Eight modules/five owners unchanged. Owner SHA-256:
4df0667f4eebf34a56269ba6c7307ed899839b65a09e9786a5f89298dc4a6290.
Both manuscript hashes, all pins and HEAD unchanged. No stage/commit/push.

Progress: R4a/R4b/R4c CLOSED, R4d OPEN; R4 subtasks 3/4. Overall 3/8
(37.5%), MG2 1/2, public proofs 0/4. The sole next R4 product is symmetric
whitening of the actual projected frame and transfer of both HS and operator
residual bounds. Reuse the checked finite inverse-square-root commutator
and reorthonormalization declarations in the read-only sister provenance;
do not restart pointwise overlaps or refine the already sufficient Gram rate.

## R4d actual whitening — MG2 completion checkpoint

This checkpoint supersedes the preceding next-exit paragraph. The existing
owner `AlmostAllSpectralBudget` now defines the actual complete-prefix
Q = V(V*V)^(-1/2), with V the normalized projected full-star synthesis,
and E = GQ-QD for the original exact-molecule root diagonal D. No relabelled
or arbitrary isometry substitutes for this matrix. On every fixed power
prefix K <= X^theta, theta < 1/2, eventually Q*Q = I and P Q = Q, and

  norm(E)_HS^2 <= C K log^5 X,
  norm(E)_op^2 <= C log^5 X (1 + K^2/sqrt X).

The finite transfer bounds both norms by 34 times the corresponding
pre-whitening residual. Gram smallness and injectivity are discharged by
R4c, not new premises. The final linear-isometry export identifies its
underlying map exactly with Matrix.toEuclideanLin Q, the type consumed by R3.

### Checked reuse and minimal adaptations

All source modules below are read-only provenance from
`../prime-cover-power-band-spectra-formalization/PrimeCoverPowerBand/`.
The source Apache-2.0 license and selected proof bodies were inspected.
No source module or umbrella import was added as a dependency.

- `SignedFrames`: frameGram, normalizedFrame, inverseSqrtNormalizer,
  positive-definite Gram from injectivity, normalization/isometry,
  frame commutator and normalized residual identity.
- `FrameOperatorCommutator`: square-root/inverse commutator, spectral
  near-identity square-root bound, unitary-conjugation norm facts.
- `FrameReorthonormalization`: frame norm/injectivity from near Gram,
  Gram commutator and constant-34 operator residual transfer.
- `MixedMatrixNorms`: only missing conjugate-transpose, subtraction,
  scalar, and mixed operator/HS multiplication wrappers. Existing local
  norm definitions and sum-of-squares bridge were reused.
- `FrameHilbertSchmidt`: Gram commutator and HS residual transfer, adapted
  to the same near-Gram square-root argument as the operator proof.

Two bounded adaptations avoid importing unused spectral infrastructure:
the inverse norm follows from S W = I and norm(S-I) <= 1/2; the HS
commutator uses the same square-root Sylvester identity with operator norms
on the multipliers. Neither incurs a dimension factor. Actual graph
specializations consume R4c and the existing Hermitian compression/root
diagonal. No new mathematical research interface was opened.

### Requirement-by-requirement completion audit

| MG2 requirement | Compiled evidence | Boundary |
|---|---|---|
| R3 weak sorting | `abs_descendingSort_sub_le_of_antitone` | Weak order and ties, no strict spacing assumed |
| R3 same-index comparison | `ordered_residual_squaredEnergy_comparison` | Literal lifted ordered index; complement/smallness hypotheses are R5, not claimed discharged here |
| R4 actual one-exit membership | `oneExitProjection_mul_whitenedProjectedFullStarFrame` | Every finite cutoff/prefix, no eventual hypothesis |
| R4 actual isometry | `eventually_powerRange_whitenedProjectedFullStarFrame_isometry_and_residuals` | Complete prefix, actual Gram, fixed theta < 1/2 |
| R4 HS budget | `eventually_powerRange_whitenedProjectedFullStarFrameResidual_hsSq_le` | C K log^5 X, constant independent of moving K |
| R4 operator budget | `eventually_powerRange_whitenedProjectedFullStarFrameResidual_operatorNorm_sq_le` | Coherent K^2/sqrt X term retained |
| R4 to R3 map | `eventually_powerRange_whitenedProjectedFullStarFrame_linearIsometry` | Exact matrix synthesis as a Euclidean linear isometry |
| HS basis conversion | `sum_norm_toEuclideanLin_sq_eq_matrixFrobeniusNorm_sq` | R3 eigenbasis sum equals the matrix Frobenius budget |

### Validation and progress

Scratch7, targeted 4234-job build, full 4238-job build all PASS.
Ten new audit roots use only propext, Classical.choice and Quot.sound.
All 179 printed audit declarations were checked: only the four selected
unfinished Solution roots contain sorryAx. No owner sorry/admit/project
axiom/native_decide. Seven exact controls PASS: identity, singular zero
Gram, unit columns with nonzero cross Gram, noncommuting normalizer/model,
dimension-sensitive HS identity, empty prefix, actual one-exit membership.
Scratch control type annotations and complex numeral simplification were
repaired; no production theorem was changed to make a control pass.
Style PASS (existing optional nolints-file warning); semantic lint exit 1,
with exactly 93 inherited findings, no additions/removals. Diff check PASS.
Logs: `/private/tmp/prime-cover-whitening-{target,full,controls,lint,style}.log`.

Owner 8732 -> 9612 (+880), audit 179 -> 189 (+10), total local Lean
29583 -> 30473 (+890, including lakefile). Eight modules/five proof owners;
all eight are import-reachable from Challenge/Solution/SubmissionAudit,
30441 module lines, zero unreachable modules. This is import reachability,
not a claim that unfinished Solution proof terms already use the new lemmas.
No new module/import/dependency. Owner SHA-256:
1902d8f0758f0ae2088e2c65f07872e124113ebd3b43b12014e70e7f3801e52a.
Both manuscript hashes, HEAD and pins unchanged. No stage/commit/push.

MG2 COMPLETE: R3 and all four R4 exit products closed. Checklist
3/8 -> **4/8 (50%)**; public proofs **0/4**, unchanged. This is checklist
completion, not elapsed-effort estimation or a Palomar-ready claim.
Next mini-goal MG3: R5 energy-weighted complement and absorptions, then
R6 actual ordered mean-square/tail assembly. Do not reopen Gram estimates
or import the BHP/local-capacity route into these D31 products.

## R5 iteration 1 — direct weighted complement consumer

Literal narrowing: for an isometric positive-star prefix U and a raw
frame F, F* x = 0 implies U* x = -(F-U)* x. If L U = U W*W,
the forest top outside U is beta >= 0, and
norm(W(F-U)* x) <= tau norm(x), then

  re inner(x,(L+H)x) <= (beta + tau^2 + eta) norm(x)^2.

Here H has pointwise norm bound eta. This is the complement inequality
needed by R3, using the energy-weighted discrepancy from native (6.14).
It avoids the auxiliary graph-map inverse and conjugation (6.17)--(6.18)
for this particular consumer; it does not prove those separate graph-map
statements or promote the actual complement gap.

New declarations in the existing owner:
- `re_inner_le_of_weighted_frame_error`
- `re_inner_add_le_of_weighted_frame_error`
- `normalizedFrame_inverseSqrt_adjoint_eq_zero_iff`
- `eventually_powerRange_whitenedFrame_adjoint_eq_zero_iff`

The last root is an actual-graph theorem on every complete sub-square-root
power prefix. Its positive-definite Gram premise is discharged by R4c.
The finite consumer reuses R3's isometric orthogonal decomposition and
bounded-perturbation quadratic estimate; the range bridge reuses R4d's
inverse-square-root formula and Mathlib nonsingular-inverse/adjoint algebra.
Sister search found frame compression/residual bounds, not this weighted
complement statement. No new graph coordinate, owner, import or dependency.

Validation: scratch4 PASS, targeted 4234/full 4238 builds PASS. Four new
audit roots have only propext, Classical.choice and Quot.sound. Four exact
controls PASS: tilted two-coordinate frame, failure without energy weights,
failure without the complement-top hypothesis, empty prefix. The scratch
controls have only deprecated-API warnings; no admitted proofs. The first
semantic-lint run found one unnecessary DecidableEq n parameter; it was
removed. Final semantic lint has the same 93 inherited findings, no additions
or removals. Style PASS with the inherited optional nolints warning.
Logs: `/private/tmp/prime-cover-energy-complement-{target,full2,controls,lint2,style2}.log`.

Owner 9612 -> 9745 (+133), audit 189 -> 193 (+4), total Lean including
lakefile 30473 -> 30610 (+137). Eight modules/five owners; no new module.
Owner SHA-256:
e39fb87d4d78f792e7dc09c50fc47f6032aed31270a35536e09f020225760702.
Both manuscript hashes and all pins unchanged. No stage/commit/push.

R5 remains OPEN: the actual energy-weighted V-U operator estimate, forest
prefix top and the two asymptotic absorptions still need producers. An
unweighted frame estimate times the largest energy would not suffice near
the square-root boundary. R6 is not started. MG3 0/2; D31 4/8 (50%);
selected public proofs 0/4. Next iteration should retain the column energy
weight in the existing full-star coefficient estimates.

## R5 iteration 2 — actual weighted full-interior synthesis

Reuse: the existing full-target norm estimate, exact shared-target support
and logarithmic common-target count imply the full-interior overlap bound
for ALL distinct sources. The former non-adjacent full-molecule proof is
now a short consumer of that stronger interior lemma, not duplicated code.
A private weighted Gram/Schur helper uses weights sqrt(mu_a). Its diagonal
is paid by the existing source norm; its off-diagonal terms by shared
targets. Consequently the actual weighted interior matrix J satisfies

  norm(J)^2 <= (10000 eta^2 + (40000/log 2) K log X)
                / sqrt(X/(8 K log X))
             <= C log(X)^2 sqrt(K/log X).

The three public roots are `eventually_powerRange_fullInteriorOverlap_energyProduct_le`,
`eventually_powerRange_energyWeightedFullInterior_operatorNorm_sq_le`, and
`eventually_powerRange_energyWeightedFullInterior_operatorNorm_sq_le_scale`.
They quantify over every positive complete prefix K <= X^theta, theta < 1/2,
and have no abstract gap, residual, or overlap premise. The norm is explicitly
the matrix Euclidean operator norm; typed matrix lets prevent accidental
Pi-norm elaboration. This is the interior part of native (6.14), not yet V-U.

Target 4234 and full 4238 builds PASS. Three new audit roots use only
propext, Classical.choice and Quot.sound. Four finite controls PASS:
unequal source weights, coherent-column off-diagonal mass, empty prefix,
and the necessity of a diagonal term. Semantic lint has exactly the same
93 inherited findings, no additions/removals. Style PASS with only the
existing optional nolints-file warning. Logs in /private/tmp:
prime-cover-weighted-interior-{target6,full,controls2,lint,style}.log.

Owner 9745 -> 9962 (+217), audit 193 -> 196 (+3), total local Lean including
lakefile 30610 -> 30830 (+220). Eight modules/five owners, no new import/pin.
Owner SHA-256: 7789cf98ca31f691e1c650bd082794c203070f66f7a3f352e5c7eb7d4e4bd617.
Both frozen manuscript hashes match. No staging, commit or push.

R5 remains OPEN; MG3 0/2, D31 4/8 (50%), public proofs 0/4. Next:
phase-aligned boundary discrepancy on disjoint star supports, followed by
projection/normalization transfer. Forest prefix top and both absorptions
still precede R6. The weighted interior bound does not itself prove a
low-complement spectral gap or the ordered mean-square result.

## R5 iteration 3 — actual boundary and projected weighted discrepancy

The exact signed boundary decomposition, unit normalization, negative-mode
bound and boundary-kernel feedback equation give
mu_a norm(phase_a boundary_a - u_a) <= 700 eta. Distinct source-star supports
are disjoint, so their weighted Gram has zero off-diagonal entries. Reusing
the existing weighted-family helper gives 490000 eta^2/min(mu), not a
cardinality multiple. Combining with the interior gives the actual raw
weighted bound C log(X)^2 sqrt(K/log X); its complex projection obeys the
same scale. All source energies remain inside their respective columns.

The direct consumer is
`eventually_powerRange_projectedRaw_weightedError_operatorNorm_sq_le_scale`.
`eventually_powerRange_whitenedFrame_adjoint_eq_zero_iff_projectedRaw`
removes both actual normalizers from the complement condition; their
invertibility is proved using the existing actual column norm bounds.
Thus the normalization-error estimate previously scheduled for R5 is not
needed, just as the inverse graph-map is not needed by the finite consumer.

Target 4234/full 4238 PASS. Nine new audited declarations have only propext,
Classical.choice and Quot.sound. Six exact controls PASS: phase alignment,
unequal source energies, overlapping-support negative control, phase-matrix
contraction, zero-normalizer negative control and projection-fixes-U negative
control. Semantic lint: unchanged 93 inherited findings, no additions or
removals. Style and diff checks PASS. Evidence:
`/private/tmp/prime-cover-weighted-boundary-{target3,full,controls3,lint,style}.log`
and `/private/tmp/prime-cover-projected-raw-weighted-target.log`.

Owner 9962 -> 10395 (+433), audit 196 -> 205 (+9), local Lean 30830 -> 31272.
Eight modules/five owners, no new imports, dependencies or pins. Owner SHA:
bac6b73a0f6980cbbff1e89fa30f0cb4c35f8a44ae16a8ba36c5d0b8155c2ce0.
Both manuscripts and HEAD remain unchanged. No staging, commit or push.
R5 remains OPEN: next is the actual forest-prefix top, then the fixed-fraction
gap and both absorptions. R6 is not started. MG3 0/2; D31 4/8 (50%); public
proofs 0/4. The weighted input is closed, not the whole complement theorem.

## R5 iteration 4 — actual prefix gap and residual absorptions

The actual complete-prefix forest form is bounded by
sqrt(pi_S(X/(K+1))) after removing its positive prefix modes. Negative and
zero forest modes remain in the complement. Combining that bound with the
already-checked energy-weighted projected discrepancy proves, for the actual
whitened frame Q on K=12288 B,

    Q* x=0 ==> Re <x,A x> <= (mu_B/16) ||x||^2,
    mu_B = sqrt(X/(B log X)).

The literal one-exit operator G satisfies the same bound because P Q=Q,
<x,Gx>=<Px,A Px>, and P contracts norm. Both actual residual absorptions
are proved uniformly on X^theta/log X <= B <= X^theta: for each fixed
positive epsilon and fixed prefix factor P, the squared operator norm of
GQ-QD is smaller than both epsilon B/log X and epsilon mu_B^2.
The coherent K^2/sqrt X term is retained; no free gap or residual premise.

Reuse: `PowerBands.lean` in the read-only sibling, declarations
`tendsto_terminalBufferedSchurMajorant_zero` and
`eventually_terminalScale_polylog_schurFactor_lt` (lines 241--341),
SHA-256 a8b8998bdf52ad0fa65a5f7eb917eaa1a04380ef5390b0aad83f4a16cc65b6f6.
No sibling module was imported. All other inputs use existing owners/pins.

Integrated validation passed: the saved final full build completed 4238
jobs, including the final one-exit corollary. The earlier targeted build
passed 4236 jobs; seven exact controls and the corollary check separately
passed. All ten new audit roots use only propext, Classical.choice and
Quot.sound. All four selected Solution roots still use sorryAx.
Semantic lint exits 1 with the historical 93 inherited findings, none in
the new R5 section; style passes with only the optional missing nolints file
warning. The handoff records passing diff/JSON/YAML and owner placeholder
checks. The continuation freshly verified source hashes and read the logs;
these build, lint and control results are inherited, not fresh replays.
Owner SHA-256: 76599df27c70e7cb5a3fa96c996b7fa51ccb0ab91d568c6d74cd00103107b4a2.
Audit SHA-256: da79bf044735565cd0e61193951c5ed03b6247810f5f5ef6f62bdd1dc898a6e0.
Logs and exact controls: `.lake/d31-r5/` (ignored build evidence, not a new
proof owner). Owner 10395 -> 11048 (+653), audit 205 -> 215 (+10), total
local Lean 31272 -> 31935; eight modules/five owners, no new imports/pins.
R5 CLOSED: D31 5/8 (62.5%), MG3 1/2, public roots 0/4. No commit/push.

Next R6 subproducts: complete-prefix arithmetic-rank
dictionary and weak-order VALUE sorting (including ties); actual ordered
mean-square comparison; tail bound with the A-to-G transfer. These are
subpoints of R6, not extra checklist units or new theorem campaigns.

## R6 admission and iteration 1 — complete-prefix arithmetic ordering

Mode: CLOSURE, new lemmas in the established finite spectral/arithmetic API.
Admit the preapproved `PrimeCoverPowerBand/AlmostAllAssembly.lean`, importing
`AlmostAllSpectralBudget`. Consumer path: `PrimeCoverPowerBandSolution` imports
this owner; `PrimeCoverPowerBandSubmissionAudit` imports Solution. R6 supplies
the literal ordered mean-square/tail input of R7's two almost-all roots.
The new owner separates application assembly from R3--R5's finite comparison
and actual frame estimates; no other module is admitted.

First obligation: complete-prefix enumeration agrees with the global
arithmetic rank; diagonal-root eigenvalues satisfy weak VALUE sorting against
the antitone prime-count tuple, allowing ties. Reuse Mathlib's
`Fintype.orderIsoFinOfCardEq` and existing
`abs_comp_perm_sub_le_of_antitone`; introduce no alternative order API.
Extract only `eigenvalues₀_diagonal_eq_descendingTupleSort` from historical
`DiagonalEigenvalueSorting.lean:158--211` (SHA-256
d7aea2514b5b65e080bfa9efd6ba26ccd39c0a0e676d155d8fffc1ea2d832148),
inlining the small descending-sort wrapper. The Hermitian/diagonal adapter
matches `ExactOrderedMoleculeCompression.lean:23--46,211--223` (SHA-256
7e9441e4c1e019471ea731d6bbe8e7bd4c103537a5c8afe0f85fda6b678838f4),
with the CURRENT R4 root matrix. No historical frame, budget premise,
inverse sorting label, or source module is imported.

Acceptance: owner/Solution/audit Lake build, standard-axiom audit, empty
prefix and tied/reversed-value controls, semantic/style and source checks.
The finite rank and VALUE-sorting roots passed the owner/Solution/Audit build
(4237 jobs), with only propext, Classical.choice and Quot.sound. All four
selected Solution roots still use sorryAx. Evidence: `.lake/d31-r6/target-order.log`.
At that finite checkpoint, owner +200 and audit +2 gave 31935 -> 32137
local Lean lines including lakefile, in nine modules/six proof owners.
No new asymptotic theorem was credited at that checkpoint.

The application index adapters reuse the exact private
`symmetricEigenvalues_cast` proof from `FullSpectrumTransfer.lean:19--27`
(current source SHA-256
804178f0d34c51a3594b76ecf7eda1172ad6ee479b53493adfd37121c02c2e39)
as private `assemblyEigenvalues_cast`, because the original is private.
No alternate frame coordinate is introduced. The final assembly reuses
`eventually_powerRange_fullAdjacency_oneExit_sq_comparison`, its existing
public-rank bridge, and Mathlib's `Finset.card_nsmul_le_sum` for Markov.
All proof work stays in the single admitted owner.

### R6 acceptance — 10 September 2026

R6 is CLOSED. Its literal consumer is native Theorem 10.1, equations
(10.1)--(10.2), via the deterministic/noise estimate (10.9).

| Checked export | Exact change from the previous conditional consumer |
|---|---|
| `moleculeCenterRankIndex_val` and `abs_orderedPrefixMoleculeRoot_sq_sub_primeCount_le` | Complete-prefix positions equal global arithmetic positions. Weak VALUE sorting preserves uniform squared error, including plateaus; no inverse sorting label appears in the conclusion. |
| `eventually_terminalScale_prefixMolecule_primeCount_error` | Actual S1, positive roots and correction size give C B/log X uniformly on K=12288 B. Only S1's existing O(a/log X) result is used; the stronger native o(1) intermediate is not claimed. |
| `eventually_terminalScale_orderedPrefixMoleculeRoot_bounds` | Actual sorted squared roots remain within C B/log X of the literal prime count, and the dyadic sorted roots lie in [mu_B/8, 8 mu_B]. |
| `oneExit_eigenvalues_lift_moleculeCenterEigenEquiv_eq` | Lifting the prefix spectral position gives the actual G eigenvalue at the same global arithmetic rank. |
| `eventually_terminalScale_oneExit_ordered_comparison` | Actual R4--R5 producers discharge the isometry, HS/operator bounds and complement premise. The nonnegative noise has sum eps_a^2 <= H B log^5 X, and squared G-to-model error <= 32 mu_B eps_a + B/log X. |
| `eventually_terminalScale_arithmeticRank_noise_bound` | S2 transfers to the actual A eigenvalue at that same rank. Every band centre has a regular finite correction and literal defect <= C B/log X + 32 mu_B eps_a. |
| `eventually_terminalScale_ordered_meanSquare` | Literal defect square sum <= C X log^5 X + C B^3/log^2 X on the actual dyadic band. |
| `eventually_terminalScale_ordered_tail` | For every t>0, the actual defect failure set above C0 B/log X + C1 t mu_B has cardinality <= C2 B log^5 X/t^2. |

Statement audit: S is a fixed finite set of primes and 0 < theta < 1/2.
The constants precede the eventual X threshold, which is uniform over
natural scales X^theta/log X <= B <= X^theta. The tail's t>0 is quantified
after that threshold and each B, so the threshold is independent of t.
`dyadicBandCenters` retains both B/2 and B. Its vertices are the actual
allowed graph vertices; in the eventual range B <= X^theta < X, this is
the paper's entire allowed band. The target is exactly
`abs (lambdaAtArithmeticRank a ^ 2 - pi_S(X/a) - firstExitCorrection S X a)`.
Regularity is proved by the noise export, not assumed or lost through
totalized division. There is no arbitrary exceptional-set witness and no
free frame, gap, residual-budget or arithmetic-separation premise.

Numerical application audit: K=12288 B is eventually inside the larger
power prefix at theta'=(theta+1/2)/2. The model window is [mu_B/8,8 mu_B],
the G complement is at most mu_B/16, and the actual residual squared norm
is below both mu_B^2/1024 and (B/log X)/1024. These imply R3's residual
smallness and absorb its 1024 e_B^2 cost into B/log X. The HS budget is
O(B log^5 X). Squaring the final deterministic/noise bound uses at most
B centres, giving B^3/log^2 X and X log^4 X; log X>=1 permits the displayed
X log^5 X bound. Markov is applied only to the noise squares.

Fresh validation against the final source:

| Check | Result / evidence |
|---|---|
| Owner + Solution + Audit | PASS, 4237 jobs, `.lake/d31-r6/target-final.log`. |
| Full Lake build | PASS, 4239 jobs, `.lake/d31-r6/full.log`. |
| Axiom audit | All 15 new R6 roots use only propext, Classical.choice and Quot.sound. All four selected Solution roots still use sorryAx. `.lake/d31-r6/axiom-audit.json`. |
| Exact controls | PASS, eight examples: empty prefix, ordinary/deleted-prime global ranks, tied/reversed-value sorting, negative-square and deterministic-term controls, and closed dyadic endpoints with adjacent labels excluded. `.lake/d31-r6/Controls.lean`, `controls-final.log`, `controls-result.json`. Earlier failed control scripts are retained in the diagnostic logs; their repairs changed no production proof. |
| Semantic lint | Exit 1 with exactly the same 93 inherited diagnostics, zero R6 findings. `.lake/d31-r6/lint-final.log`, `lint-comparison.json`. |
| Style | Exit 1: the unchanged R5 owner has U+141F in its line-9340 docstring; no R6 style finding. `.lake/d31-r6/style-final.log`. This fresh result supersedes any inference of a clean current style run from the saved R5 pass. |
| New-module check | Read-only `mk_all --check --lib PrimeCoverPowerBand` reports the intentionally absent umbrella module. None is created: the package uses explicit module globs, and all nine modules are reached from the declared Challenge/Audit roots. `.lake/d31-r6/mk-all-check.log`, `source-audit.json`. Import reachability does not certify R8's declaration-level minimality. |

Final source inventory: owner 884 lines, audit 230 lines. Relative to R5,
the owner adds 884 and Audit adds 15, so 31935 -> 32834 local Lean lines
including lakefile (net +899). There are nine modules/six proof owners,
with zero unreachable modules from the declared roots. The only added
production module is the preapproved `AlmostAllAssembly`; Solution's only
R6 change is its import. Existing proof owners, all four Solution holes,
the manuscripts and dependency pins are unchanged by this batch.

- Final owner SHA-256:
  aef8600d0dd15f29f36c7c9ac118ae48172f344be7944b1a55e594dad5f451fa.
- Final Audit SHA-256:
  f2d3f1375b657b00f2c1743a10239dcd2c78b4e62ac4eb92ae88966fcbf66c11.
- R5 owner SHA-256 remains
  76599df27c70e7cb5a3fa96c996b7fa51ccb0ab91d568c6d74cd00103107b4a2.
- Lean 4.32.0 and all three pinned package revisions match the inherited
  environment; exact values and source/import checks are in `source-audit.json`.
- Owner scan: no sorry/admit/project axiom/opaque assumption,
  native_decide or ofReduceBool. JSON/YAML and `git diff --check` pass.

Completion marker: **D31 6/8 (75%), MG3 2/2 COMPLETE, public proofs 0/4**.
Next is R7's terminal exception bound and dyadic/global accounting, followed
by its public and internal corollaries. R8 remains the separate release
verification stage. No official Comparator/independent-kernel or Palomar-ready
claim is made here. No commit, push, manuscript change or publication.

## R7 admission — public and internal consequences

Admission snapshot; superseded by the acceptance record below.

Mode: CLOSURE; proof-only implementations and lemmas in the existing finite
counting/asymptotic API. The user authorized R7 on 10 September. Keep the
current checkout and all existing owners. R7 remains OPEN until all four
consumers below and their local validation gates close; D31 stays 6/8, MG4
0/2, public roots 0/4 during implementation. R8 is separate.

Frozen outputs: the exact current types of `palomar_almostAll_powerBand`
(Theorem 1.3) and `palomar_almostAll_subBlock` (Corollary 1.4), plus named
internal exports for Corollary 10.2's quantitative sharp dyadic tail and
global density-zero sharp failures, and Corollary 10.3's every-centre
deterministic/operator error bound. All failure sets use the actual global
arithmetic-rank adjacency eigenvalue and regular finite correction. Constants
follow S, theta and any requested exponent; the terminal/global distinction
and the sub-block margin remain unchanged.

Finite assembly: split a cutoff N into its lower half and the closed dyadic
band [N/2,N], then induct on N. The count budget u B on every dyadic band
gives at most 2 u N on the prefix. This is the paper's geometric summation
with exact natural endpoints and no new dyadic coordinate API. The omitted
initial segment is counted separately through floor(X^theta/log X)+1.
At each split N/2<N for N>0; N=0 is empty because vertices are positive.
All retained centres are covered, including midpoint ties and deleted primes.

Reuse: `HeadlineAssembly.lean:101--119`, SHA-256
098c5ff4e8bc07c3c82e7cf9a13613070095a363653b64f724ab92a9f6346c9d,
supplies the finite initial-segment injection. Adapt the split/count proof
of `AlmostAllInitialSegment.lean:31--107`, SHA-256
4b2275c981aaa444c65443c94fa59f6bddab2a96959a214feb1ded0658e3dcd6,
to the CURRENT closed terminal band and D31 scale. The old D26' quadratic
certificate and scale are not imported. Use existing Mathlib real-power/log
limits and the current `tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero`.
The R6 comparison's already-proved max-noise conclusion will be retained
alongside its HS mass for the every-centre operator consumer; no R4/R5 proof
is repeated. Keep all new proofs in `AlmostAllAssembly`, with only the two
almost-all Solution bodies and their audit/metadata consumers changed.

Acceptance: targeted/full Lake, literal statement and dependency/axiom audit,
finite cutoff/endpoint and exponent-margin controls, semantic/style comparison,
source/pin checks, and metadata synchronization. Baseline hashes and proof
snapshots are in `.lake/d31-r7/baseline.json`; diagnostic scripts/logs stay
under that ignored evidence directory. No manuscript, pin, commit, push,
publication, or official R8 verification action is included.

### R7 acceptance — 10 September 2026

Status: CLOSED. The user-authorized row closes Theorem 1.3, Corollary 1.4,
and internal Corollaries 10.2--10.3. No new proof owner/import is admitted.
The following R7 exports supply the two public proofs and the named
internal corollaries:

| Export in `AlmostAllAssembly` | Literal consumer / proof delta |
|---|---|
| `eventually_terminalPowerBand_badCenters_le` | For each R, choose natural D; R6 Markov tail with t=log(X)^D gives the actual terminal failure count <= Cexc X^theta/log(X)^R. |
| `tendsto_powerBandBadDensity_zero_of_terminal_bound` | SAME C,D; total count <= X^theta/log X + 1 + terminal count. No terminal rate is claimed for the full initial segment. |
| `almostAll_subBlock_of_ordered_tail` | Actual squared-error failures have density zero for every strict margin below min(theta/2,1/2-theta). |
| `eventually_terminalScale_sharp_tail` | Threshold (C0+C1) B/log X has explicit budget C2 X log^6(X)/B^2. |
| `almostAll_sharpPowerBand` | Actual sharp failures, including irregular corrections, have density zero when 1/3 < theta < 1/2. Uniform tail ratio is controlled by C X log^9(X)/X^(3 theta). |
| `eventually_terminalPowerBand_everyCenter_bound` | Every terminal centre is regular and has error <= C [a/log X + log^5(X)(sqrt(X/(a log X)) + X^(1/4) sqrt(a/log X))]. |
| `eventually_terminalPowerBand_everyCenter_subBlock` | For every delta < min(theta/2,(1-2 theta)/4), every terminal centre has error <= C X^(1/2-delta)/log X. This proves a positive power gain relative to sqrt(X)/log X. |

Eight supporting finite/logarithmic exports give the exact initial-segment
injection, finite geometric summation, threshold containment and strict-power
absorption. The actual failure predicates are retained throughout. All global
counts are normalized by X^theta, not the ambient graph cardinality.

Reuse: historical initial-segment injection/split adapted as recorded in the
admission; no historical module imported. R6's two noise producers now retain
the already-proved eps <= actual whitened residual operator norm. The R6
mean-square/tail consumers ignore that extra conclusion; their types are
unchanged. R4/R5 owners are byte-identical to the baseline. Corollary 10.3
uses K=12288 a and absorbs this prefix factor into a strictly larger exponent
below 1/2; its coherent operator term is never discarded. No BHP, local
capacity, free frame, gap or residual-budget premise is introduced.

Validation: fresh target `lake build PrimeCoverPowerBand.AlmostAllAssembly
PrimeCoverPowerBandSolution PrimeCoverPowerBandSubmissionAudit` PASS, 4,237
jobs; full `lake build` PASS, 4,239 jobs. Fifteen new internal audit roots
and the two public almost-all roots have only propext, Classical.choice and
Quot.sound. Of 235 audited roots, only the two sharp public roots contain
sorryAx. Local proof-owner scans find no placeholder, project axiom or
trusted-computation command. Fifteen exact controls PASS: the eight R6
rank/tie/band controls plus zero cutoff, odd cutoff with deleted primes,
strict integral cutoff, sufficient and insufficient logarithmic exponent,
sharp theta=1/3 endpoint and the coherent every-centre margin. Two scratch
zero-cutoff rewrite attempts failed on cast/division normalization; the
final control reuses the actual band-cardinality theorem. Production proofs
were not changed for these control failures.

Owner semantic lint exits 1 with exactly the same 93 inherited diagnostics,
none in `AlmostAllAssembly`. Separate Solution semantic lint PASS, exit 0.
Style exits 1 with the byte-identical inherited U+141F finding at unchanged
`AlmostAllSpectralBudget.lean:9340`; there are no R7 style findings. No lint
suppression or cosmetic change to another owner. All four public type texts
match both the frozen Solution baseline and Challenge; Core/Challenge hashes
are unchanged. This local check is not official Comparator or independent
kernel verification. No import changed, so R6's intentional missing-umbrella
`mk_all --check` limitation persists; fresh reachability covers all nine
modules from the declared Challenge/Audit roots.

Growth: owner 884 -> 1584 (+700), Solution 72 -> 82 (+10), audit 230 -> 245
(+15); total local Lean including lakefile 32834 -> 33559 (+725). Nine modules,
six proof owners, zero unreachable modules. SHA-256:

- Owner: 01ff14ea6d7c6e29750917a64ea14230466ddb985cc4295862ea5fcf6566a5dc.
- Solution: 0d61f9dbcacacaa21bd12893a2ef73908b2a85b78587f5c25187d9cdc3038510.
- Audit: a5548088a99e0f3959b25c5efe6902b59c73fc1632e1fdcd305107f3b90505f9.

Evidence directory: `.lake/d31-r7/`; authoritative results are
`target-final.log`, `full.log`, `axiom-audit.json`, `controls-result.json`,
`controls-final-pass.log`, `lint-comparison.json`, `lint-solution.log`,
`style-final.log`, `statement-audit.json`, `source-audit.json`, and
`validation-summary.json`. Both manuscripts, HEAD, SSH remote and all
build/dependency pins are unchanged. All preexisting work is preserved;
no staging, commit, push, publication or submission was performed.

D31 **6/8 -> 7/8 (87.5%)**, MG4 **0/2 -> 1/2**, public proofs **0/4 -> 2/4**.
R8 scoped release verification is next. The two sharp proofs stay open;
this is not a combined four-root Palomar-ready claim.

## R8 admission — scoped D31 verification and final readiness

Admitted on 10 September 2026 under the user's R8 instruction. This is a
maintenance and verification batch, with no new proof owner or mathematical
claim. Freeze the nine R7 Lean modules and all dependency pins, preserve the
real Git index, and audit the two D31 public roots plus the named R6--R7
manuscript exports. R8's frozen exit test is the selected-root build, axioms,
exact statement match, declaration reachability/provenance and documentation,
with no conditional analytic premise in D31. D31 remains 7/8 during the audit.

Official Palomar preflight, protected Linux Comparator/NanoDa replay and an
immutable authorized source checkpoint are separate submission-readiness
gates. The two sharp Solution holes continue to block the combined four-root
release. No commit, push, dependency change or publication is included.
Baseline hashes, source/index state and verification outputs are retained in
`.lake/d31-r8/`; the upstream verifier is pinned there for this audit.

### R8 exit — scoped verification, 10 September 2026

R8 is CLOSED for the frozen D31 checklist; D31 is **8/8 (100%)**, MG4
**2/2 COMPLETE**, and public proofs remain **2/4**. This closes a bounded
local proof audit. Final Palomar submission readiness is **PARTIAL**.

Fresh selected/full Lake invocations passed 4,238/4,239 jobs. Lake reused
unchanged compiled artifacts and replayed the 235-root axiom report, with
only the two sharp public holes on sorryAx. A separate fresh type/proof audit of
the two D31 public roots and six named R6--R7 exports found 71,747 constants
in their union, with only propext, Classical.choice and Quot.sound and no
short-interval input or extra trust constant.

The public D31 union uses 1,231 of 1,820 local constants; the named internal
exports add 13. Source .ilean references add complexifyRealMatrix_apply.
The remaining 573 owner-support constants and two sharp public holes are
listed separately, including 120 source-level support declarations. They
are preserved as existing shared APIs and the planned sharp route, not
claimed as needed for D31. This is a declaration inventory, not a claim
that the combined four-root tree is declaration-minimal for D31 alone.
The complete candidate has nine import-reachable modules and six owners.

Local Lean comparison passes for all 34 shared declaration types and
26 definition values, covering all 20 distinct Comparator selections.
The Challenge was copied under an isolated namespace in an ignored audit
file, then compared by Lean definitional equality in the Solution environment.
The initial direct cross-environment probe could not resolve a Challenge-only
generated Fintype instance; the isolated copy resolves that audit limitation.
Only its four deliberate Challenge holes warn. This is local comparison
evidence, not official Comparator or independent-kernel replay.

Current upstream metadata-schema and Palomar-contract validation pass.
The required AI-assistance disclosure is present; no separate human
line-by-line review is asserted. Source-provenance roles distinguish this
substantive development, the historical laboratory, native mathematics,
pinned dependencies, and the verifier. Historical port hashes are file-level
provenance; an immutable substantive source checkpoint is still pending.
The source editorial audit confirms explicit graph/rank/correction formulas,
actual failure sets and normalization, denominator regularity, strict
endpoints, identical terminal/global error parameters and the initial segment.
All four selected theorems have attached English documentation; the helper
reports 2/2 renderable docstrings for each entry. An official render and
editorial review have not been run.

Lean 4.32.0 has an exact published lean4export tag at
4e7915201d3f9f04470d9eae002fa695f7cdc589. Mathlib's pinned revision is an
ancestor of its canonical branch under PalomarSubmission
ef2fa1eadcb246c2346ddba39b52eaa53d4bb763.
Metadata was checked against upstream schema commit
99c678e569c7c4c0772db297c5ddd5e4c9b6322e and that exact verifier. Template,
licence-path, manifest, artifact, LFS and submodule checks pass.
A disposable candidate Git index let the strict module audit include all
four untracked owners; the real Git index was unchanged. The audit's only
error is the two admitted sharp obligations in the shared Solution. Its
commit-role warnings are heuristic: this substantive repository needs an
intake commit, not a self-referential revision in its metadata.

**Remaining release gates:** an explicitly authorized complete source
checkpoint; exact current Palomar preflight and protected Linux full replay,
including Comparator, NanoDa and rendered Challenge; and both sharp proofs
before a combined four-root release. This macOS host has no supported Linux
runner available. No official mechanical or registration result is claimed.
The earlier 93 semantic-lint findings and one Unicode-style finding remain
inherited evidence on byte-identical proof files; lint was not rerun here.

R8 changes no Lean source, theorem type, manuscript, import, toolchain or
dependency pin: **+0 Lean lines**, total 33,559 including lakefile. All R7
source hashes, HEAD, SSH remote and the real staged index are preserved.
No commit, push, publication or submission occurred. Evidence is in
`.lake/d31-r8/`: baseline, fresh build/axiom logs, kernel and source closure
inventories, the local statement comparison, metadata/provenance checks,
candidate audits, editorial assessment and validation-summary.json.

## Authorized development checkpoint — 10 September 2026

After the R8 exit above, the user explicitly authorized committing and pushing
the D31 batch and requested a Palomar submission analysis. This checkpoint
includes every file in R8's complete candidate inventory, including all four
formerly untracked proof owners. Every Lean and dependency/configuration hash
was freshly matched to the R8 evidence before staging. Only the checkpoint
account in existing documentation/metadata was updated; no theorem, proof,
import, paper or pin changed.

The configured Git author is Shaik Idris Ali, and Git uses the existing
`git@github.com:shaikidris/prime-cover-power-band-spectra-palomar.git` remote.
The authorized SSH branch and the prior local planning HEAD matched. The
anonymous GitHub repository API returned 404, so public source access remains
a submission gate. No visibility change or Palomar state change is included.

Use the immutable Git commit containing this record as the source checkpoint;
the post-push receipt records its full hash without creating a self-reference
inside that commit. R8's earlier no-commit/no-push and untracked-file statements
are historical audit facts, superseded for this development checkpoint.
Exact current Palomar replay and the two sharp proofs remain open.

## Post-push submission analysis — 10 September 2026

The full R1--R8 source checkpoint is
`0e23075e18eb2569f1b95217ceee955de7554345`. SSH push succeeded; a subsequent
independent SSH branch read returned the same hash, with a clean worktree.
This section and `PALOMAR_SUBMISSION_ANALYSIS.md` record the analysis requested
in that same authorization. They change no Lean source, selection, manuscript
or pin, and do not repair or promote any theorem.

Freshly inspecting pinned Comparator
`575674928e239f5bc452aab72d1dd7b0f1326494` revealed that non-selected reachable
constants require structural equality. A compiled-environment diagnostic
using its equality instances confirms a blocker: the selected
`powerBandBadCenters` type reaches `Vertex`, which is an explicit subtype
in Challenge but a Paper I abbreviation in Core. Both public D31 theorem
types match structurally. Additional rank/operator definitions and a generated
Fintype instance reference differ. R8's local definitional-equality pass was
valid for its stated method but did not test this stricter contract. No
official protected Comparator run or mathematical proof failure is claimed.

The first proposed entry remains the existing almost-all pair. Repair the
shared statement surface, isolate an admission-free D31 Solution, verify
public source access, then complete exact protected preflight/full replay and
the editorial account. The sharp holes are outside D31's audited proof
closure; separating their Solution surface satisfies the local release rule
without making the sharp theorem a new D31 proof prerequisite. The source
API remains anonymously unavailable (404), and visibility was not changed.
No supported Linux runner, official replay or registry action is recorded.

The report freezes current policy, verifier, schema and kernel-tool revisions;
native source files were also matched to their cited mathematical-source
commit. Detailed evidence is retained in
`.lake/palomar-submission-analysis-2026-09-10/`. R8 remains **8/8 local**,
public proofs **2/4**, and submission readiness **PARTIAL**.

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
