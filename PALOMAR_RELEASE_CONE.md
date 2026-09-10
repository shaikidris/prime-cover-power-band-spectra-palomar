# Paper II Palomar release-cone contract

## Resumed pre-submission goal — publication last

This is the continuation of the source-freeze board on the separate audit
branch `palomar-readiness-2026-09-10`. The immutable D31 source is
`454743470f6aff2e7f7f8ac79a7a2a7279e60ada` on `main`; verification and handoff
must use that commit, never this later receipt commit. The user authorized
analysis and the before-submission goal. No Palomar state change is included.

The user clarified: **making the repository public is the last step before
Palomar**. P6 therefore runs privately, P7 prepares the final assessment and
packet, and P5 is the final publication/access gate. The source SHA and full
verification requirements are unchanged. Earlier blocked records below are
historical and are superseded by this sequencing correction.

**Current sequencing decision (10 September):** the user confirmed that phase 1
contains exactly Theorem 1.3 and Corollary 1.4, then changed the order to
**SSRN Paper II first**, so the Palomar metadata can cite its actual reference.
The scope question is resolved. Prepare and submit the distinct Paper II
preprint, capture its receipt and public reference, update the Palomar YAML,
and revalidate the resulting immutable source before final publication. Never
substitute Paper I's SSRN identifier or invent a Paper II DOI.

**Dashboard:** P0--P4, P6 and P7 remain VERIFIED at source `4547434` for the
two-result D31 entry. P5 now awaits the SSRN prerequisite and the resulting
metadata/source reconciliation before publication. A future metadata commit
does not inherit the exact-source status of these receipts.
**7/8 tasks verified** counts release tasks, not equal effort or mathematical
proof percentage. R1--R8 remains 8/8 local; both sharp proofs remain open on
the preserved `sharp-development` branch.

| ID | Output / existing owner | Depends on | Status | Exit test / evidence |
|---|---|---|---|---|
| P0 | Source-faithful theorem comparison | frozen manuscript and Lean | VERIFIED | Squared-error scales, literal quantifiers/ranges, strict gains and unchanged BHP route reconciled in the source analysis. |
| P1 | Structural Challenge/Core compatibility | P0 | VERIFIED | Explicit shared Vertex/instances; 16,491 constants pass strict comparison. |
| P2 | Admission-free D31 tree; preserved sharp development | P1 | VERIFIED | Final full build 4239 jobs; zero Solution admissions and zero snapshot errors; sharp revision `11e71d0cec4f2e8de8e2542bb0b7a4888782607f`. |
| P3 | Mathematical account, Challenge prose and metadata | P0, P2 | VERIFIED | Source semantics/current metadata contract pass; 2/2 selected English docstrings present. Render is P6. |
| P4 | Local release audit of exact source | P1--P3 | VERIFIED | Strict statement/definition comparison, eight standard-axiom closures, 15 controls, zero unreachable modules; inherited lint disclosed. See `readiness/p4-final-validation.json`. |
| P5 | Final authorized publication and anonymous source check | SSRN reference, P4, P6, P7 | WAITING_FOR_SSRN_REFERENCE | Two-result scope confirmed. Submit Paper II to SSRN first, capture its verified reference, then align/revalidate Palomar metadata. No visibility change performed. |
| P6 | Current protected Linux preflight/full and Challenge render, privately | P4 | VERIFIED | Actual full report pass/complete, both kernels accept, all source/config/tool/dependency bindings match; actual render and reader inspection pass. See `readiness/p6b-mechanical-validation.json` and `readiness/p6c-render-inspection.json`. |
| P7 | Advisory assessment and exact handoff packet | P0--P4, P6 | VERIFIED | Actual protected report/render reconcile with the frozen source, mathematical account and exact intake fields; advisory limits disclosed. See `readiness/p7-reconciliation.json` and `PALOMAR_HANDOFF.md`. |

P6 substeps remain individually tracked without changing the eight-task denominator:

| Substep | Status | Evidence required |
|---|---|---|
| P6a private preflight | VERIFIED (34465598832) | Current unmodified preparation code reports `pending` at `prepared`, with no errors and exact source binding. |
| P6b private full protected replay | VERIFIED (34465598832) | Actual pass/complete report; protected 4236-job selected build, NanoDa and Lean kernel acceptance. Exact source and all pins match. |
| P6c private Challenge render | VERIFIED (34465135183) | Actual report `pass`; 18 file hashes match. Static module overview and 2/2 selected docstrings visually inspected; upstream interactive declaration isolation disclosed. |


### SSRN-first prerequisite tasks

| ID | Task | Status | Evidence / next exit test |
|---|---|---|---|
| S0 | Confirm sequence and two-result formal scope | VERIFIED | User explicitly selected two proved results and SSRN first. |
| S1 | Freeze Paper II identity and prepare PDF/metadata | DRAFT_PREPARED | Separate `prime-orthant-geometry/submission/ssrn-paper2/` packet: 34-page PDF SHA-256 `d9c4e05c2d9f67d0973798601ed5078630f2d2406416af73533658a68a273e5e`, copy-safe abstract, metadata and exact build/packet manifests. Mathematical body unchanged. |
| S2 | Check source fidelity, SSRN compliance and final render | IN_PROGRESS | Source/render checks pass; all 137 equation tags present. Official SSRN guidelines and AI policy checked 10 September. Author details and live portal checks remain pending; no new independent whole-paper proof audit claimed. |
| S3 | Submit exact PDF; capture actual SSRN receipt/reference | WAITING_FOR_SIGN_IN | SSRN authentication page identified the correct author/email; user sign-in requested. No new submission exists in this preparation record. |
| S4 | Insert actual Paper II reference in Palomar metadata | WAITING_FOR_S3 | Keep two selected declarations; preserve sharp-route open status. |
| S5 | Reconcile and verify resulting immutable Palomar source | WAITING_FOR_S4 | Refresh affected metadata/build/render bindings before P5. |

These prerequisites do not silently enlarge the original eight-task denominator;
the historical 7/8 is an exact-source result, not current end-to-end readiness.

Full delivery scope remains: Theorem 1.3 and Corollary 1.4 are the first entry;
Theorem 10.1 and Corollaries 10.2--10.3 are already compiled internal exports;
Theorem 1.1 and Corollary 1.2 are open sharp-route declarations. BHP and the
sharp assembly remain visible but are not new obligations of this D31 goal.

The initial P2 plan admitted exactly one additional **entry surface**,
`PrimeCoverPowerBandSharpSolution.lean`, consumed by the sharp Comparator and
the existing submission audit. It relocated the two existing sharp obligations
without adding proof owners or declarations. The expected inventory becomes
ten local modules, six proof owners and zero unreachable modules across the
two configurations and genuine audit root. The D31 Solution keeps its existing
module name. No other new Lean module is admitted. Production code growth is
limited to the explicit shared Vertex/instance repair and entry boilerplate;
the ceiling is 33,659 Lean lines including lakefile (at most +100 from R8).
No new theorem family or proof infrastructure is authorized by this split.

P4 refinement: a separate file still fails the required whole-repository
admission scan. The ten-module two-entry development is therefore preserved
on branch `sharp-development`; the D31 submission tree returns to nine
modules/six owners, with zero Solution admissions. Its selected D31 theorem
types and configuration remain unchanged. The four Challenge statement types
remain available; the open sharp Solution and its configuration live on the
preserved branch. This is a release-boundary change, not a change to Theorem
1.1, BHP, or the mathematical task denominator.

### Goal iteration P0 — theorem comparison verified

Native manuscript SHA-256:
`b145e0a4ed2078fca969ed127d00c73d8758a76b559971988501693c1b60cfa3`.
Checked its Theorems 1.1/1.3/10.1, Corollaries 1.2/1.4/10.2/10.3 and
Proposition 2.4 against the current Solution and named `AlmostAllAssembly`
exports. The supplied distinction is correct: the sharp every-terminal-centre
law and its BHP/Brun--Titchmarsh input are unchanged, while the newer route
improves the block baseline throughout each fixed `0 < theta < 1/2`.

All quoted errors concern squared eigenvalues. The density-one power margin
is strictly below `min(theta/2, 1/2-theta)`; the every-centre operator margin
is strictly below `min(theta/2, (1-2 theta)/4)`. Both vanish at a boundary;
there is no uniform positive margin over the open interval. BHP is an input
of the current sharp proof, not a proved logical necessity for all proofs.
The internal sharp density-one corollary has `1/3 < theta < 1/2` and remains
outside the selected entry. Terminal exception rates do not silently extend
to the full initial segment.

No theorem was promoted and no proof build was rerun for P0. Elapsed analysis
time was not separately measured. Repair lesson: compare squared-error powers
against the positive-star baseline before comparing ranges or inputs. Next-use
test: P3 must retain these same powers, strict margins and quantifiers in all
public prose. Baseline/evidence: `.lake/palomar-readiness-2026-09-10/`.

### Goal iteration P1 — shared identity repaired

P1 IN_PROGRESS -> VERIFIED. Core now spells the same concrete `Vertex` subtype
and derived instances as Challenge. It remains definitionally equal to the
Paper I type; no Challenge formula, theorem signature or definition selection
was relaxed. `lake build PrimeCoverPowerBand.Core` passed (2,731 jobs; 87s
reported for Core). A fresh comparison of all constants reached from the two
Challenge theorem types and the sixteen configured definitions checked 16,491
constants with zero failures, using the pinned Comparator's equality rule.
This checks the shared statement dependencies against compiled Core, not the
complete Solution proof or protected export; those remain P4/P6.

Consumer obligation removed: the explicit-type/abbreviation and generated
instance mismatch. There were no failed production builds. Repair signature:
definitionally equal aliases do not satisfy a structural statement contract;
match the concrete definition and its generated instance identities. The
bounded sibling/operator/rank dependencies all passed the same traversal.
Evidence: `p1-core-build.log`, `p1-core-comparison.log` and
`p1-core-comparison.json` in the goal evidence directory. Next-use test: rebuild
the actual Paper I-consuming proof owners after the P2 entry split; any
instance-transport regression keeps P4 open.

### Goal iteration P2a — split preserved; one consumer rewrite under repair

Source checks preserve both sharp declarations and both D31 declarations
verbatim. The D31 Solution has zero admissions; the separate sharp surface
has the same two. After the split, the initial selected build rebuilt Core's
consumers through `AlmostAllSpectralBudget`, then failed at
`AlmostAllAssembly.lean:477`: ordinary rewriting could not match the lifted
rank cast under instance-level transparency after `Vertex` became an explicit
definition. The public theorem types and arithmetic rank are unchanged.

The repair supplies the existing lemma's arguments and uses `erw` to allow
definitional reduction. P2 remains IN_PROGRESS until the selected build passes.
Initial failure log: `p2-selected-build.log`. Only this proof step in the
existing assembly owner changes; no new lemma or hypothesis is introduced.

### Goal iteration P2b/P3 — selected build and public account verified

P2 and P3 IN_PROGRESS -> VERIFIED. The retry passed all 4,238 selected jobs.
Assembly and D31 Solution rebuilt in reported times of 126s and 100s; the audit
rebuilt in 55s. These compiler durations are not a summed wall-clock timing.
All public declarations and their existing proof bodies remain verbatim in
their designated surfaces. The only non-Core proof edit is the explicit
`erw` at the existing lifted-rank bridge. The expected Paper I instance
transport regression was repaired locally; no new mathematical obligation was
discovered. The separate sharp surface retains its two admissions.

README and Challenge prose now state the actual squared-error comparison,
block baseline, fixed-parameter dependence, strict margins, initial segment,
unchanged BHP-dependent sharp theorem and internal-only corollaries. The
pinned Paper I surface has a logarithmic window, correcting the earlier
fixed-centre shorthand. Metadata records the sufficient weaker intermediate
molecule estimate, inaccessible native source limitation, AI involvement and
unestablished novelty. Both selected formulas remain visible and assessable;
zero-operator, arbitrary-bound and zero-denominator substitutions do not
preserve the advertised interpretation. These are source checks, not a render
or official editorial decision.

Evidence: `p2-validation.json`, `p2-selected-build-final.log`,
`p3-metadata-draft-check.json`, `p3-semantic-review.json`. Next: P4 fresh full
build and trust/statement/source audit. The P0 prose-retention experiment is
SUPPORTED; the P1 transport test found and repaired exactly one consumer step.

### Goal iteration P4a — stricter admission gate reopens P2/P3

The full build passed 4,240 jobs. Fresh comparison of both public signatures,
all sixteen selected definition values and all 16,491 reached constants passed.
Eight fresh public/internal proof closures have 71,752 union constants and
only the three standard axioms. Source inventory passes with ten modules,
zero unreachable modules and unchanged manuscripts/dependency pins.

However, the strict snapshot helper scans every tracked Lean file and still
reports two admissions in `PrimeCoverPowerBandSharpSolution.lean`. The
repository's zero-Solution-admission release rule therefore requires a branch
boundary, not only a module boundary. P2 and the packaging portion of P3 are
reopened; verified-task count is honestly reduced from 4/8 to 2/8. No proved
theorem is demoted. Preserve the complete compatible sharp development before
removing its admitted Solution/configuration from the D31 snapshot. Audit
declaration removals are PACKAGING, with their new branch location recorded.
Do not suppress the helper's finding or weaken the repository rule.

### Goal iteration P2c — sharp development preserved before tree separation

The complete compatible two-entry development is preserved locally on
`sharp-development` at `11e71d0cec4f2e8de8e2542bb0b7a4888782607f`.
Its sharp Solution and configuration were checked byte-for-byte against the
working files before removal from the D31 tree. Main HEAD remained unchanged.
This preserves the two original sharp theorem texts, their BHP dependency
status and the repaired shared implementation; no sharp proof is claimed.

The D31 tree now contains only `almost-all-comparator.json` and its two
admission-free Solution declarations. The four Challenge statement types are
unchanged. The sharp Solution/configuration and two sharp audit rows are
PACKAGING moves to the preserved branch. Their eight generated build artifacts
were invalidated so a stale import cannot mask an omitted source. Metadata now
lists exactly the two selected results with zero Solution admissions. Its
schema/current-contract check passes. Rebuild and strict snapshot audit of this
final branch boundary are pending, so P2/P3 are not yet reclosed.

### Goal iteration P4b — final D31 tree passes local gates

P2/P3 are reclosed and P4 is VERIFIED: **5/8 release tasks verified**.
The final D31-only full build passed 4,239 jobs. The strict snapshot audit
reports zero errors, zero Solution admissions and two attached selected
English docstrings. It inventories nine modules / six owners, 33,517 Lean
lines (33,549 including lakefile), zero new modules and zero unreachable
modules. This is -10 Lean lines from the R8 total; the +100 ceiling is met.

Both selected types, all sixteen selected definition values and all 16,491
shared constants pass the strict local comparison. Eight fresh public/internal
proof closures have 71,752 union constants and only the three standard axioms.
Their proof source is unchanged by the later branch separation; the final
full build independently prints the same axiom results. Fifteen existing
adversarial controls pass. The semantic-lint rerun reproduces exactly 93
inherited owner findings with no new diagnostic. One inherited Unicode-style
finding at `AlmostAllSpectralBudget.lean:9340` remains; neither lint is claimed
clean. No broad cosmetic edit is included.

All five changed Lean files match the reviewed scope: concrete Core identity,
one Assembly `erw` repair, Challenge prose, removal of the two sharp Solution
obligations, and movement of their two audit rows (PACKAGING). The D31 selected
formulas/proof bodies, manuscripts, toolchain, dependency pins, lakefile and
selection configuration remain unchanged. There are no LFS pointers,
submodules or compiled artifacts in the candidate. Metadata scope and branch
links are reconciled against the current schema/contract.

The snapshot helper's three warnings are accounted for: committing removes
candidate dirtiness; selected definition meaning was assessed under P0/P3;
and the commit-role heuristic is superseded by the explicit provenance table
and substantive-repository authority rule. Embedding the current commit in
itself would create an invalid self-reference, so the exact source SHA belongs
in the post-freeze audit receipt. No warning is silently counted as a pass.

Evidence: `p4-d31-only-full-build.log`, `p4-statement-comparison.json`,
`p4-kernel-closure.json`, `p4-controls.log`, `p4-lint-comparison.json`,
`source-inventory.json`, `snapshot-d31-candidate.json` and final metadata/diff
checks in the goal evidence directory. The earlier failed same-tree admission
scan is retained as `p4-initial-split-snapshot-d31-candidate.json`.
Repair lesson: a clean selected proof closure does not satisfy a repository-wide
admission gate; preserve alternate admitted development on a branch before
freezing the submission tree. Next-use test: exact protected Linux replay and
the actual render must agree with this local account before P6/P7 can close.

## Current plan — D31 rebase, 9 September 2026

This section supersedes the execution order, almost-all dependency map, and
progress denominator in the historical contract below. MG1 (R1--R2),
MG2 (R3--R4), MG3 (R5--R6), and MG4 (R7--R8) are validated locally.
D31 is 8/8; final Palomar submission readiness is PARTIAL.
The [10 September post-push analysis](PALOMAR_SUBMISSION_ANALYSIS.md) records
a confirmed structural Comparator incompatibility in the shared definitions.
That release blocker is separate from the completed D31 proof checklist.
Both D31 public proofs are closed; the sharp pair remains open. The
10 September R5 reconciliation below uses saved validation evidence,
freshly matched to the unchanged source hashes.

Repository mode remains `PALOMAR-FIRST`. Keep this repository and reuse its
checked code; do not create another repository or restart formalization.
The 139-module sibling is read-only proof provenance, not a dependency.

### Authoritative mathematical source

- Title: *Prescribed Eigenvalues in Power Bands of Finite Prime-Cover Graphs*.
- Manuscript: `../prime-orthant-geometry/draft/prescribed-eigenvalues-in-prime-cover-power-bands.md`.
- Source SHA-256: `b145e0a4ed2078fca969ed127d00c73d8758a76b559971988501693c1b60cfa3`.
- Native proof record: `../prime-orthant-geometry/analysis/paper2-ordered-comparison-strengthening-2026-09-09.md`.
- Historical `almost-all-prescribed-spectra-prime-cover-graphs.md` is the
  former filename, not a second live manuscript.

The title needs no change: it covers every-centre and density-one conclusions
at prescribed ranks. Paper I, dependency pins, and the short-interval
formalization project are outside this revision.

### Two proof routes, in this execution order

1. **D31 first.** Lemma 5.4 and Section 10 give ordered mean-square/tail,
   density-one, and weaker every-centre bounds on every fixed
   `0 < theta < 1/2`. Inputs: global PNT, the exact full-star family, global
   frame estimates, and an energy-weighted complement gap. No BHP,
   Guth--Maynard, reciprocal tiling, or local internal-core capacity estimate
   is an input to this route.
2. **Sharp terminal ranks afterward.** Theorem 1.1 still has
   `21/61 < theta < 1/2` and error `O(a/log X)` at every terminal centre.
   It retains BHP, buffered/internal capacity, and `TerminalSchur`.
   D31 does not discharge those obligations. BHP work remains a separate
   dependency project; it is not a prerequisite of the first route.

Challenge/Core/Solution, Comparator names and metadata now encode D31:
lower endpoint `0`, error `a/L + L^D sqrt(X/(a L))`, quantitative terminal
exceptions and a sub-block margin. R7 closes the two almost-all Solution
holes with unchanged public types; the two sharp holes remain. Formal
completion is supported by the R7 proof/build/axiom evidence below.

### Validated statement-surface amendment (R1)

Keep four selected declarations across the two existing Comparator entries.
The sharp pair remains unchanged. Amend the almost-all pair together with
Core definitions, Solution types, audit names, README and formalization.yaml:

| Current declaration | Planned statement / paper consumer |
|---|---|
| `palomar_terminalBand_prescribedRanks` | unchanged Theorem 1.1 |
| `palomar_terminalBand_primeCounting` | unchanged Corollary 1.2 |
| `palomar_almostAll_variableWidth` | replace by `palomar_almostAll_powerBand`: Theorem 1.3, `0 < theta < 1/2`, error `a/L + L^D sqrt(X/(a L))`; include the terminal exception rate for each fixed `R > 0`, and the global density-zero consequence |
| `palomar_almostAll_subWeyl` | replace by `palomar_almostAll_subBlock`: Corollary 1.4, `0 < delta < min(theta/2, 1/2-theta)`, global density-zero failure set at squared error `C X^(1/2-delta)` |

Here `L=log X`; `S,theta,R` are fixed before `D`, the comparison constants,
and the eventual threshold. The terminal exceptional count is
`O(X^theta/L^R)`; a statement counting all centres below `X^theta` also omits
the initial `O(X^theta/L)` segment. Failure sets must be defined from the
literal ordered adjacency eigenvalue and finite correction, not chosen as
arbitrary witnesses. Retain denominator regularity and positivity conditions.

Theorem 10.1's mean-square/tail and Corollaries 10.2--10.3 are named internal
proof exports on the same cone. They do not silently become extra Comparator
selections. Their finite/asymptotic statements are part of R6--R7.

### Reuse and exact scope

`FirstExitTarget.exactPrincipalMoleculeSupport` already contains the entire
boundary star and `firstExitCompressionSupport`; the latter includes isolated
targets. Its matrix retains boundary--target small-prime edges. Thus there is
no reason to recreate the molecule. R2 has checked the normalized vector,
principal-submatrix identification, and source/target maps against the repair.
Projected collective synthesis remains R4, not an R2 completion claim.

The existing S1 theorem gives only `O(a/L)`, not the stronger native `o(1)`
molecule defect. That is sufficient for this consumer if its objects match:
on a complete prefix `c <= C_star B`, S1 plus `M_c=O(L)` gives uniform
`|nu_c^2-pi_S(X/c)|=O(B/L)`. Sorting contraction preserves that bound, which
is already the deterministic term in (10.9). Do not strengthen S1 merely to
imitate the stronger intermediate estimate in (10.3).

Do not transplant `ExactMoleculeTargetTransport`'s permutation-labelled
conclusion as a prescribed-rank theorem: it explicitly contains the inverse
sorting permutation. D31 needs sorting contraction in VALUE at the complete
prefix index, including plateaus. The global complement gap, not a band-local
reindexing or arithmetic descent margin, then preserves `j_S(a)`.

The previously compiled coherent `coreBudget` is a local compression budget.
It is not the global residual operator/HS estimate required by D31. Likewise
the old summed residual `O(B^2/L)` is not a producer for `O(B L^C)`.

### R4 completion snapshot

| Subtask | Status / next literal consumer |
|---|---|
| R4a actual projected columns and exact identities | CLOSED |
| R4b quantitative tail and one-source continuation | CLOSED: actual residual squared norm <= C log^5 X, uniformly in the power window |
| R4c complete-prefix HS/operator/Gram estimates | CLOSED: actual projected HS/operator residual bounds and collective raw/projected Gram smallness. The energy-weighted Schur sum retains K/a + omega(a), giving raw Gram error <= C log^5(X) (eta_X K/X + K^2/X), uniformly tending to zero on K <= X^theta, theta < 1/2. |
| R4d reorthonormalized isometry | CLOSED: Q = V(V*V)^(-1/2) is the actual complete-prefix isometry, remains in the one-exit space, and retains BOTH residual bounds. Its exact Euclidean linear-isometry map is exposed for R3. |

R4c exit verification: targeted 4,234/full 4,238-job builds pass. Five new
public roots have standard axioms only. Empty-prefix, restricted-neighbour,
down-divisor, coherent-row, orthonormal and endpoint controls pass. Semantic
lint has the same 93 inherited findings and no additions; style passes.
R4d exit verification: targeted 4,234/full 4,238-job builds pass. Ten new
audit roots have standard axioms only; seven exact controls pass. Semantic
lint has the same 93 inherited findings, no additions; style passes. The
actual whitened residual has HS squared bound C K log^5 X and operator
squared bound C log^5 X (1+K^2/sqrt X), uniformly for K <= X^theta,
fixed theta < 1/2. No free Gram, injectivity or residual-budget premise.

All four R4 exit products are now closed, so R4 earns one checklist unit.
At that exit, D31 was **4/8 (50%)**, MG2 **2/2 COMPLETE**, selected Solution roots **0/4**.
The completion audit and exact port provenance are in `PORT_MANIFEST.md`.
No R5 complement hypothesis or later public theorem is credited here.

### R5 exit reconciliation — 10 September 2026

R5 is CLOSED. The unchanged owner/audit hashes match the handoff, and
`.lake/d31-r5/full.log` records the final 4,238-job build including the
one-exit corollary. Ten new roots have standard axioms only; the four selected
Solution roots still use sorryAx. Saved controls/style pass; semantic lint
has 93 inherited findings, none in the new R5 section. These are inherited
validation results, freshly inspected here, not a build replay.
The actual A/G complement gap is mu_B/16 at K=12288 B, and the actual
residual squared norm is eventually below both epsilon B/log X and
epsilon mu_B^2. At this R5 checkpoint D31 was 5/8, MG3 1/2; R6 was next.

### R6 exit — 10 September 2026

R6 is CLOSED. `AlmostAllAssembly` identifies the complete-prefix index with
the global arithmetic rank and applies weak VALUE sorting, including ties.
S1 and correction regularity supply the required uniform C B/log X model
error; PNT puts sorted dyadic roots in [mu_B/8, 8 mu_B]. The actual R4--R5
isometry, HS/operator bounds and mu_B/16 complement gap discharge every
premise of R3. S2 transfers to A at that same global rank.

For the literal defect d_a = |lambda_{j_S(a)}(A)^2 - pi_S(X/a) - M_a|,
the new exports prove, uniformly on X^theta/log X <= B <= X^theta for
each fixed 0 < theta < 1/2:

- sum over the actual closed dyadic band of d_a^2 is at most
  C X log^5 X + C B^3/log^2 X;
- for every t>0, the number of band centres with
  d_a > C0 B/log X + C1 t mu_B is at most C2 B log^5 X/t^2.

These are actual graph conclusions, with no free frame, gap or residual
budget hypotheses. The deterministic term remains outside the Markov noise.
Fresh targeted/full builds pass 4,237/4,239 jobs; all fifteen new audit roots
use standard axioms only and eight exact controls pass. Semantic lint has
the same 93 inherited findings. Fresh style reports one inherited Unicode
issue at unchanged `AlmostAllSpectralBudget.lean:9340`, no R6 findings.
The nine modules are reachable from the declared Challenge/Audit roots;
`mk_all --check` reports the intentionally absent umbrella module.
Exact source hashes, growth, statement audit and logs are in `PORT_MANIFEST.md`.
At the R6 exit D31 was **6/8 (75%)**, MG3 **2/2 COMPLETE**, public roots **0/4**.
The following R7 exit supersedes that progress snapshot.

### R7 exit — 10 September 2026

R7 is CLOSED. The unchanged public types of `palomar_almostAll_powerBand`
and `palomar_almostAll_subBlock` now have proofs. The terminal failure count
is at most Cexc X^theta/log(X)^R for every fixed R>0 after choosing D; the
same C,D give global density zero, with initial count X^theta/log X + 1
retained. Finite dyadic induction handles natural endpoints and prime deletions.

Internal Corollary 10.2 has tail C X log^6(X)/B^2 and full sharp-error density
zero for 1/3 < theta < 1/2. Corollary 10.3 retains both operator scales,
sqrt(X/(a log X)) and X^(1/4) sqrt(a/log X), with logarithmic exponent 5.
It also proves error <= C X^(1/2-delta)/log X for every strict
delta < min(theta/2, (1-2 theta)/4). The latter margin is positive on
0 < theta < 1/2. The R6 noise producer now exposes its already-proved maximum
bound; the R4 and R5 proofs are unchanged.

Fresh targeted/full builds pass 4,237/4,239 jobs. Fifteen new internal roots
and both almost-all public roots have only propext, Classical.choice and
Quot.sound; only the sharp pair retains sorryAx. Fifteen exact controls pass.
Owner semantic lint has the identical 93 inherited findings, Solution lint
passes, and style has the same inherited Unicode finding. Public statement
text matches the frozen Challenge, with Core, papers and pins unchanged.
There are nine modules / six owners / 33,559 Lean lines including lakefile;
all modules are reachable from Challenge/Audit. R7 adds 725 Lean lines total.
Exact provenance, hashes, control repair and evidence are in `PORT_MANIFEST.md`.
D31 is **7/8 (87.5%)**, MG4 **1/2**, public proofs **2/4**.
R8 official release verification and the separate sharp route remain open.

### R8 exit — 10 September 2026

R8 is CLOSED for the frozen local D31 audit. Fresh selected/full builds pass
4,238/4,239 jobs; the 235-root axiom report leaves only the sharp pair on
sorryAx. The transitive closure of two public and six named internal roots
contains 71,747 constants, with standard axioms only and no conditional
short-interval input. Local Lean comparison checks 34 shared types and
26 definition values, covering all 20 distinct Comparator selections.
The declaration/source-reference inventory, provenance, metadata and source
editorial checks are complete; all nine modules are reachable. No Lean,
manuscript or pin changed. See `PORT_MANIFEST.md` for the exact scope,
retained non-D31 support and evidence in `.lake/d31-r8/`.

D31 **8/8 (100%)**, MG4 **2/2 COMPLETE**, public proofs **2/4**. This is not
a Palomar-ready snapshot: an authorized complete source checkpoint and exact
current Linux preflight/full Comparator/NanoDa/render replay remain pending.
The two sharp proofs additionally block the combined four-root release.

### Frozen D31 obligation checklist

Each row has one exit test. Stages have two rows each; close them in order.
R1--R8 are CLOSED for the scoped D31 checklist. No percentage credit is inferred
from inspection, native proofs, or historical builds.

| Stage / task | Exact obligation and exit test | Owner / reuse |
|---|---|---|
| A / R1 | Synchronized revised almost-all statements, explicit scale/failure-set definitions, and four selected names; type/definition alignment and statement-module builds pass, with deliberate proof holes still reported | `Core` plus existing statement/metadata surfaces |
| A / R2 | Full-star identity and normalization match; S1, correction regularity/size, and S2 supply the literal D31 inputs; targeted roots freshly build and pass axiom audit | `FirstExitTarget`, `FullSpectrumTransfer`; reuse rather than re-prove |
| B / R3 | Finite Lemma 5.4 plus weak-order sorting contraction, with the SAME eigenvalue index, low-complement and positivity hypotheses | `AlmostAllSpectralBudget`; extract existing Hermitian HW/Weyl and Schur facts |
| B / R4 | Actual complete-prefix Q is an isometry; `||E||_HS^2 <= B L^C`, `||E||^2 <= L^C(1+B^2/sqrt X)` and the repaired projected synthesis are proved, not bundled as assumptions | `AlmostAllSpectralBudget`; exact-frame sources only |
| C / R5 | Energy-weighted complement top is below the retained roots by a fixed fraction of `mu_B`; both smallness absorptions in (10.5),(10.8) hold uniformly in retained B | `AlmostAllSpectralBudget`; reuse PNT and weighted graph/compression facts |
| C / R6 | Native ordered Theorem 10.1 and tail (10.2), including the full-prefix arithmetic-rank dictionary and A-to-G transfer, with no free frame/gap/budget premises | `AlmostAllAssembly` consumes R2--R5 |
| D / R7 | Theorem 1.3, Corollary 1.4, and internal Corollaries 10.2--10.3 assemble with correct terminal/global exception counts; both revised almost-all Solution holes close | `AlmostAllAssembly` plus Solution/audit |
| D / R8 | Selected-root build, axioms, exact statement match, declaration reachability/provenance and documentation checked; no conditional analytic input remains in D31 | existing audit/Comparator surfaces; release checks scoped separately |

Current revised checklist: **8/8 validated (100%)**. This is eight bounded
consumer checks, not a claim that no reusable Lean work exists. Historical
progress remains **15/28**, measured against the superseded D26' contract;
do not add or compare those percentages. Public theorem closure is **2/4**.
R1 evidence: full build 4,222 jobs, exit 0; local Lean definitional comparison
of 28 declaration types and 24 definition values passed. JSON/YAML parse and
four-name selection checks passed. The sharp pair is byte-for-byte unchanged.
Boundary checks cover the zero and half endpoints, terminal-set inclusion,
and irregular denominators. The local comparison is not an official
Comparator or independent-kernel proof certificate.

R2 evidence: final full build 4,222 jobs, exit 0. The full-star principal
matrix, unit vector, two-mode/kernel decomposition, root positivity, S1,
correction regularity/logarithmic size and S2 ordered-index bridge are on
the expanded axiom surface. Reused inputs and adapters have standard axioms
only; all four selected proofs still contain `sorryAx`. Eight declarations
(217 source lines) were reused verbatim; two small bridge lemmas were added.
No new proof module. Total Lean source including lakefile is 20,541 lines,
net +298 from the 20,243-line planning snapshot. Proof-owner files have no
`sorry`, `admit`, project `axiom` or trusted-computation escape.

R1 is a statement-alignment gate, not successful verification of an admitted
Solution. Official selected-proof Comparator and independent-kernel evidence
must wait for the relevant holes to close and the release stage to begin.

R4b continuation checkpoint: exterior incoming multiplicity is now proved
as omega(a)+omega(v) on the actual full first-exit support. The resulting
raw residual bound is `(2 log(X)/log(2)) sum degree_H |interior|^2`, with
no assumed collision bound. The remaining one-source obligation is its
weighted coefficient sum, followed by R4c/d global budgets/isometry.
Full build 4,238 jobs, four new standard-axiom roots; no checklist unit
closes. That checkpoint used 24,851 local Lean lines.

R4b weighted-response checkpoint: actual down-star degree growth preserves
q, giving the moving-label coefficient bound 10000/(q mu_a). The entire
degree-weighted kernel contribution is O(log^3 X). After integrating it,
the actual residual squared norm is at most `(4 log(X)/log(2))` times the
signed weighted response sum plus O(log^4 X). The next obligation is ONLY
that signed sum, then R4c/d. Full build 4,238 jobs; four new standard-axiom
roots. That checkpoint used 25,157 local Lean lines, in the
same eight modules/five owners. Checklist 3/8, MG2 1/2, public 0/4.
Exact evidence is in `PORT_MANIFEST.md`.

R4b next row CLOSED: `eventually_powerRange_degreeWeightedDownCenters_le_logSq`
proves the entire actual down-centre weighted sum is O(log^2 X), uniformly
in moving a and q. The new finite degree majorant X/w+omega(w) is already
consumed by this sum. Up-centre/leaf rows and their support assembly remain
OPEN, followed by R4c/d. Targeted 4,234/full 4,238 jobs pass; three new roots
have standard axioms only. The 93 semantic-lint findings are identical to
the previous baseline; none in this owner. Four exact scalar controls pass.
That checkpoint used 25,322 local Lean lines; same eight modules/five owners. Checklist
3/8 (37.5%), MG2 1/2, selected proofs 0/4. No commit/push or paper change.

R4b up-centre row CLOSED: `eventually_powerRange_degreeWeightedUpCenters_le_logSq`
now proves the complete actual up-centre weighted sum is O(log^2 X).
The centre resolvent identity includes zero-degree/isolated targets, and
the actual power-window bound is 600/mu_a. The harmonic reciprocal-prime
sum is retained before bounding the number of up-labels by sqrt(X).
Only leaf rows and their support-sum assembly remain in the signed weighted
response. R4c/d global estimates/isometry remain open. Targeted 4,234/full
4,238 jobs pass, four new roots use standard axioms, four exact scalar
controls pass. Semantic lint has the same 93 inherited errors; style passes.
Current local Lean 25,564 (+242); eight modules/five owners. D31 3/8,
MG2 1/2, selected proofs 0/4. Manuscripts/pins unchanged; no commit/push.

### Four mini-goals and iteration markers

Use this table and the R-rows above as the single live task list. No additional
tracker or per-iteration file is needed. Keep only one R-row active; reuse
existing proofs before writing new ones.

| Mini-goal | Tasks | Exit | Current completion |
|---|---|---|---|
| MG1 — align and reuse | R1, R2 | revised statements and audited full-star/S1/S2 inputs agree with D31 | 2/2 COMPLETE |
| MG2 — finite comparison and actual frame | R3, R4 | same-index finite comparison and graph-specific global residual estimates | 2/2 COMPLETE |
| MG3 — close the spectral estimate | R5, R6 | actual complement gap and ordered mean-square/tail theorem | 2/2 COMPLETE |
| MG4 — public consequences and verification | R7, R8 | two D31 public proofs and their scoped verification | 2/2 COMPLETE |

One closed R-row earns one of eight checklist units. Mini-goal boundaries
are therefore 25%, 50%, 75%, and 100% of this D31 checklist; these are not
estimates of elapsed effort, code completion, or the combined four-root release.
Native paper proofs, this Git checkpoint, and code growth earn no units.

At the end of every iteration, report this compact marker, followed by the
literal theorem or hypothesis change and its verification evidence:

```text
D31 | R8 CLOSED locally | MG4 2/2 | checklist 8/8 (100%) | public roots 2/4
Delta: [closed row, strictly reduced hypothesis, or no mathematical change]
Evidence: [target build; axiom result; statement/consumer match]
Reuse/growth: [reused declarations; owner; line delta; new modules]
Next: [one R-row and its smallest remaining obligation]
```

Update counts only when the row's exit test passes. A narrowed row remains
open, with the eliminated and remaining hypotheses named explicitly. After
two code-growing iterations without closure or strict hypothesis reduction,
stop that route and review the same row; do not open another helper module.
Current local checklist: **8/8**, R8 CLOSED. Release readiness is PARTIAL.
The historical `e887e0b` checkpoint contains planning documents only. This
substantive development checkpoint includes all R1--R8 sources; the user
authorized commit and push on 10 September. Match the exact clean HEAD and
pushed canonical branch before handoff, and separately verify public access.

MG3 is complete. All three subpoints below are CLOSED; they do not add
checklist units beyond R5 and R6:

1. R5 recovered the native energy-weighted complement inequality and matched
   its producers to the actual whitened prefix Q.
2. R5 instantiated the fixed-fraction complement gap and both smallness
   absorptions uniformly on retained bands.
3. R6 fed R2--R5 into the finite same-index comparison, identified the global
   arithmetic rank, transferred G to A, and proved the mean-square/tail outputs.

MG3 closed at 6/8; R7 public Solution assembly takes MG4 to 1/2 and the
checklist to 7/8. R8 then closes scoped verification at 8/8 and MG4 at 2/2.
Exact submission replay remains separate. No new BHP task,
manuscript edit, or publication action is authorized.

R5 iteration 1 — finite complement consumer CLOSED, actual gap still OPEN.
`re_inner_add_le_of_weighted_frame_error` proves the complement form bound
beta + tau^2 + eta from the forest prefix energy and weighted discrepancy
W(F-U)*. For x orthogonal to F, U*x = -(F-U)*x; orthogonal decomposition
therefore pays the prefix energy directly. No graph-map inverse or inverse
energy conjugation is required for this consumer. The compiled
`eventually_powerRange_whitenedFrame_adjoint_eq_zero_iff` identifies the
actual whitened and raw projected complements. Thus the remaining literal
inputs are the energy-weighted actual V-U operator bound, the forest prefix
top, and power-range absorptions. Pointwise column estimates or an unweighted
frame norm are not substitutes for that operator bound.
Four new roots have standard axioms, targeted/full builds and four exact
controls pass. Semantic lint remains 93 inherited findings, with none added.
Owner +133 lines, audit +4; local Lean 30,610, still eight modules/five owners.
No checklist unit closes: MG3 0/2, D31 4/8 (50%), public proofs 0/4.
Next: actual energy-weighted projected-frame discrepancy, not R6 assembly.

R5 iteration 2 — actual energy-weighted INTERIOR operator estimate CLOSED.
The full-interior shared-target proof now covers all distinct centres,
including adjacent ones; the old non-adjacent molecule theorem reuses it.
For J with column sqrt(mu_a) times the actual full interior, the compiled
bound is norm(J)^2 <= C log(X)^2 sqrt(K/log(X)), uniformly on every positive
complete prefix K <= X^theta, theta < 1/2. The Schur weights sqrt(mu_a)
retain the source energies; no maximum-energy substitution is used.
Boundary alignment, projection/normalization transfer, forest prefix top
and absorptions remain open. R5 and R6 earn no checklist units yet.
Target/full builds pass; three new roots use standard axioms. Semantic
lint remains the identical 93 inherited findings; style passes.
Owner +217 lines, audit +3, total local Lean 30,830; no new module/import.
Next: bound the phase-aligned boundary discrepancy using disjoint source
star supports, then combine it with the now-closed interior estimate.

R5 iteration 3 — actual weighted projected discrepancy CLOSED.
The phase-aligned boundary error obeys mu_a norm(error_a) <= 700 eta;
disjoint source-star supports give a diagonal weighted Gram estimate with
no prefix-cardinality loss. Combining the full boundary and interior gives
norm((F_raw-U) sqrt(Lambda))^2 <= C log(X)^2 sqrt(K/log X).
Projection contracts this bound because it fixes U. Both actual column
normalization and actual whitening preserve the orthogonal complement;
therefore the finite R5 consumer can use the unnormalized projected frame.
No separate normalization-error estimate or inverse graph-map is required.
The actual weighted input and complement identification are now CLOSED.
Forest-prefix top, fixed-fraction gap and both smallness absorptions remain
OPEN. Next is the forest-prefix top using the existing nonpositive forest
core and positive-star energy matrix; do not start R6 yet.
Target/full builds 4234/4238 pass. Nine new roots use only standard axioms;
six exact controls pass. Semantic lint remains the identical 93 inherited
findings; style passes. Owner +433, audit +9, local Lean 31,272; no new
module/import. MG3 0/2, D31 4/8 (50%), selected public proofs 0/4.

R3 iteration: finite Lemma 5.4 and weak sorting contraction CLOSED. The
same ordered index survives the low-complement Schur comparison; the new
root `ordered_residual_squaredEnergy_comparison` includes the positive-root
window, actual TQ-QD residual and the mean-square conclusion. Target build:
4,234 jobs; full build 4,238 jobs. Five finite controls pass, including ties and the high-complement
negative control. New public audit inputs use standard axioms only; the
four selected proof holes remain explicit. Thirteen declarations reused,
eight finite assembly/bridge theorems added, four unused reuse candidates
pruned, one preapproved owner; local Lean 20,541 -> 21,352 (+811).
Both manuscript hashes and all pins unchanged.

R4a now proves actual complete-prefix phase alignment and unit columns, with
projected norm in [1/2,1], exact normalized Gram subtraction and the residual
identity retaining A Z. Its Pythagorean identity identifies the normalization
with the manuscript formula. The specialization A Z = H Z remains R4b, along
with the repaired down-kernel term and per-source continuation bounds.
Then come R4c global Gram/operator estimates and R4d reorthonormalization.
Only R4 is active; do not start R5 or another owner. This strictly narrows R4
but earns no additional checklist unit: 3/8, MG2 1/2, public roots 0/4.
R4a full build: 4,238 jobs; new audit roots use standard axioms only.
Local Lean 21,352 -> 21,704 (+352); no new module or dependency.

R4b checkpoint: the actual one-exit projection captures spectral components
of already captured sources, including repeated eigenspaces without assuming
global degree uniqueness. The positive zero source is captured; the negative
zero source retains exactly minus twice the projected half-difference source.
The actual discarded boundary kernel is annihilated by
L and has squared norm O(a log(X)^3 / X^(3/2)). This concerns one component,
not the full molecule tail Z. Negative-response capture and the full
tail/continuation bounds remain R4b; global budgets and isometry remain R4c/d.
Full build: 4,238 jobs, exit 0; four additional audit roots use standard
axioms only. Local Lean 21,704 -> 21,962 (+258); no new module/import/pin.
Checklist remains 3/8, MG2 1/2, public proofs 0/4. No publication action.

R4b down-target checkpoint: `signedZeroModeSourceDifference_eq_sum_downKernels`
identifies the actual half-difference with the canonical down-target kernels.
`norm_sq_signedZeroModeSourceDifference_le` bounds its squared norm by
omega(a)/2, using disjoint stars and the exact boundary leaf count. Uniform
up-leaf data has zero kernel projection, including inactive up-targets.
This closes the down-target/divisor subtask, not negative-response capture or
the full molecule tail. Full build: 4,238 jobs, exit 0; four new audit roots
use standard axioms only. Five exact rational controls pass. Local Lean
21,962 -> 22,330 (+368); no new module/import/pin. Checklist remains 3/8,
MG2 1/2, public proofs 0/4. Next: source-local negative-mode capture, then
the full tail and one-source continuation bounds; R4c/d remain open.

R4b source-local checkpoint: the actual canonical down-source spectral
component is captured under degree separation from the other source blocks.
Its exact signed coefficient is compiled, including arbitrary leaf data;
isolated up-targets are removed exactly. This replaces the unsuitable
historical global-simplicity certificate at the finite level. The remaining
eventual specialization chooses the source ell*a and down-prime ell, proves
local separation and nonvanishing, and obtains the normalized negative mode.
Negative target responses/kernel responses and full tail estimates are not
closed by the finite extraction. Owner +288 lines, audit +4; total 22,622,
eight modules. Targeted build passed (4,234 jobs). Progress remains 3/8,
MG2 1/2 and public 0/4. No manuscript or publication change.
Final source-local gate: full build 4,238 jobs, exit 0; four new audit roots
have standard axioms only. Six finite controls pass. Semantic lint retains
93 inherited findings outside this owner; no new owner finding.

R4b negative-mode checkpoint: the exact canonical down coefficient is
nonzero when source and target degrees differ. Combined with the preceding
source-local extraction, this captures the actual normalized negative
down-star mode without global degree uniqueness or a free nonzero-coefficient
premise. The remaining local degree premises are explicit. Pinned global PNT
now also supplies strict allowed-prime count growth from k*n to (k+1)*n
for each fixed positive k. Its use at the smallest-prime source ell*a,
including graph-degree identification and all other down-targets, remains
the next obligation. Full negative responses, full tail/continuations and
R4c/d remain open. Targeted build: 4,234 jobs, exit 0. Six exact rational
and integer controls pass, including the zero coefficient at equal degrees.
Owner +200 lines; audit +3; local Lean 22,622 -> 22,825 (+203), no new
module/import/pin. Checklist remains 3/8 (37.5%), MG2 1/2, public proofs 0/4.
Final gate: full build 4,238 jobs passed; the three new roots have only
propext, Classical.choice and Quot.sound. Six controls and style lint pass.
The pinned semantic linter reports the same 93 inherited findings, none
in this owner; only the inspected-declaration counts changed. Both manuscripts and all pins
remain unchanged; diff check passes. No stage, commit or push.

R4b smallest-prime checkpoint: eventual negative BOUNDARY-mode capture is
CLOSED on every fixed theta < 1/2 power range. The theorem constructs the
least allowed prime ell, separates its down-target from every other down
target by a fixed-multiple PNT interval, and uses the existing up/down ratios
for the remaining source-local inequalities. The source ell*a is placed in
a slightly larger fixed power range below 1/2. No prime choice, coefficient,
degree separation or spectral gap remains as a theorem premise.
Negative TARGET responses, especially repeated target degrees, still need
the equal-initial-segment argument; this does not prove LZ=0 for the entire
molecule. Full tail/continuations, R4c/d remain open. Targeted build 4,234
jobs passed. Owner 2,093 -> 2,311 (+218), audit +3; total 23,046 (+221),
no new module/import/pin. Checklist 3/8 (37.5%), MG2 1/2, public 0/4.
Final gate: full build 4,238 jobs passed. All three new public audit inputs
use only propext, Classical.choice and Quot.sound; selected Solution roots
still report sorryAx. Four exact prime-count controls pass, including a
deleted-prime example and the nonleast-prime/repeated-label negative cases.
Style lint passes; semantic lint retains exactly the previous 93 inherited
findings, none in this owner. Both manuscripts and all pins match; no
placeholder/trusted-computation escape in the owner. No stage/commit/push.

R4b signed-target-response checkpoint: CLOSED for the actual negative
signed first-exit response, not yet for the boundary-kernel-driven response.
The finite up/down sign factors depend only on the spectral parameter;
actual up/down ratio bounds keep the two families on opposite sides of
the boundary degree. Repeated target degrees are allowed. Existing forest
resolvent equations transfer captured sources to captured responses.
Separately, equal-degree up-targets have identical boundary-leaf segments,
the compatibility input still needed by the kernel-driven response.
No full-molecule LZ=0 or global frame budget is claimed.

Exit evidence: targeted 4,234 and full 4,238 jobs pass; eight new public
audit inputs use only propext, Classical.choice and Quot.sound. Seven exact
controls pass, including distinct equal-degree targets, wrong-factor and
resonance negative controls. Style lint passes (existing optional nolints
file warning); semantic lint has the identical 93 inherited findings, none
in this owner. Owner 2,311 -> 2,675 (+364), audit +8; local Lean
23,046 -> 23,418 (+372). Eight modules/five proof owners unchanged; no new
import or pin. Both manuscript hashes match. Checklist remains 3/8 (37.5%),
MG2 1/2, public proofs 0/4. No stage, commit or push.

R4b kernel-coefficient checkpoint: the actual kernel source equals H*zeta.
Symmetry and the existing reverse canonical source restrictions give its
exact signed-mode coefficients: the up contribution is a partial kernel
leaf sum times the target normalization/energy; every down contribution is
zero because it uses the whole mean-zero leaf segment. Equal-degree active
up-targets have exactly equal coefficients. This closes the coefficient
calculation, NOT the spectral-projection assembly. The next exit test is
capture of the whole negative spectral component, permitting repeated
degrees, followed by the existing resolvent transfer. Only then can the
full discarded-tail identity be assembled. No alternate coordinates or
new resolvent construction were added.
Owner 2,675 -> 2,861 (+186); audit +5; local Lean 23,418 -> 23,609 (+191).
Checklist remains 3/8 (37.5%), MG2 1/2, public proofs 0/4. No new module,
import, dependency, manuscript change, stage, commit or push.
Final gate: full 4,238-job build passes, five new roots use standard axioms
only, all five controls pass. Style passes; semantic lint has exactly the
previous 93 inherited findings after the docstring fix, with no owner
findings. Both manuscripts/pins match and diff/owner-placeholder checks pass.

R4b kernel-spectral checkpoint: CLOSED for the actual negative kernel-source
and kernel-response components on every fixed power range theta < 1/2.
The proof groups equal-degree canonical blocks, identifies their common
coefficient ratio to the captured positive source, and transfers capture
through the existing first-exit equation. No global degree uniqueness is
assumed. The eventual target-degree straddle producer discharges the finite
up/down inequalities. This closes the preceding coefficient checkpoint's
spectral assembly, not the full discarded-tail theorem.

Next exit test: assemble L z_a = 0 for the full molecule, retaining the
negative signed down-kernel correction in the quantitative tail bound;
then price one-source continuations. R4c/d global budgets/isometry remain
open. Checklist 3/8 (37.5%), MG2 1/2, public Solution proofs 0/4 unchanged.
Owner 2,861 -> 3,269 (+408); audit +6; local Lean 23,609 -> 24,023 (+414).
Targeted build 4,234 and full build 4,238 jobs pass. Six new audit roots use
only standard axioms; five exact controls pass, including equal-degree
incompatible-coefficient rejection. Style passes; semantic lint retains
exactly 93 inherited findings and no owner findings. Frozen manuscripts,
pins and eight-module/five-owner inventory unchanged. No stage/commit/push.

R4b full-tail checkpoint: `eventually_powerRange_largePrime_discardedFullMolecule_eq_zero`
assembles the actual boundary, signed response and kernel response. The
finite spectral criterion uses the existing positive-star capture and the
proved negative-component capture; only the zero eigenspace can remain.
`eventually_powerRange_fullStarFrameTail_largePrime_zero` supplies L Z = 0
and A Z = H Z uniformly for all complete prefixes K <= X^theta, theta < 1/2.
This is the literal zero-mode specialization previously deferred by R4a.
It does not say Z = 0 or discard the signed down-kernel correction.

Next exit test: the full quantitative tail estimate retaining that correction,
then raw one-source continuation counts. R4c/d budgets/isometry remain OPEN.
Three new audit roots use standard axioms only; targeted 4,234 and full
4,238-job builds pass. Semantic lint has the identical 93 inherited findings,
none in this owner; style passes with the existing optional nolints warning.
Owner 3,269 -> 3,465 (+196), audit +3, total local Lean 24,023 -> 24,222 (+199).
Four exact matrix controls pass, including omitted-negative-mode failure
and a nonzero zero-mode tail. YAML parse and diff checks pass.
Eight modules/five owners, manuscript hashes and pins unchanged.
Checklist 3/8 (37.5%), MG2 1/2, public proofs 0/4 unchanged. No commit/push.

R4b quantitative-tail checkpoint: CLOSED for the actual full molecule.
`eventually_powerRange_discardedSignedResponses_eq` gives Q response-plus = 0
and Q response-minus = (-2/nu) Q D, with D the actual down-kernel source.
The negative-mode scalar equation and existing first-exit gap give
|alpha-minus| <= 100 eta^2/mu^2 and norm(kernel-response) <= norm(zeta).
`eventually_powerRange_discardedFullMolecule_sq_le_scale` then proves

    norm(Q f_a)^2 <= C (a log^3(X)/X^(3/2) + a^3 omega(a) log(X)/X^2).

Quantifiers: fixed S and theta < 1/2, eventually all actual allowed a <= X^theta;
no capture, gap or residual-norm premise is left. The first log-cubed term
is the compiled producer's rate, not the paper's sharper log-squared rate.
This is sufficient for R4's fixed-log-power budget; it is not a claim that
the sharper rate has been formalized. Six new audited roots use standard
axioms; full build 4,238 passes. Owner +410 lines, audit +6; no new module,
import, coordinate or analytic dependency. Total local Lean 24,638.
Next exit test: raw one-source continuation count, then R4c/d global
budgets/isometry. Checklist stays 3/8 (37.5%), MG2 1/2, public proofs 0/4.
Both manuscripts and pins remain unchanged. No commit/push.

After R8, resume the separate sharp track: audited BHP input, remaining
buffered/internal alignment and rank assembly, then its two public roots.
Completing D31 does not make the combined Solution ready while sharp holes
remain. An earlier D31-only registry release requires an explicitly scoped
Solution/audit surface without those holes; do not silently weaken the
repository's zero-admission release gate.

### Owner and growth control

- Existing owners: `Core`, `FirstExitTarget`, `FullSpectrumTransfer`,
  `TerminalSchur`, `AlmostAllSpectralBudget`, and `AlmostAllAssembly`.
  Keep them; the two D31 owners were admitted under this plan. No separate
  file for Lemma 5.4, sorting, or a corollary.
- `AlmostAllArithmetic` is retired before creation: no Guth--Maynard or
  reciprocal-tiling implementation belongs to D31.
- Later sharp owners remain `TerminalArithmetic` and `TerminalAssembly`.
  This reduces the possible proof-owner set from nine to eight.
- Read-only count at replan: seven source modules, four proof owners,
  20,243 Lean lines including lakefile; four Solution holes. No files added
  to the Lean cone. Existing module-import reachability is unchanged; it is
  not a declaration-level minimality certificate.
- The user's 20,000-line figure is a planning target, not a mathematical stop.
  Report line deltas and justify necessary growth by an R-row; do not invent
  a higher fixed ceiling or copy whole historical modules. Maintain at most
  the approved eight proof owners and zero unexplained release-only modules.
- Before admitting any further preapproved owner, record exact source declarations and
  dependencies in `PORT_MANIFEST.md`; shared facts are extracted once.
- Two successive code-growing batches without closure or a strict reduction
  of the active row's hypotheses trigger replanning, not another helper file.

Per iteration report: active R-row; before/after status and changed theorem
type; stage completion; 0--8 total; actual public holes; owner/new-module and
line deltas; targeted build/axiom results; next single task. Do not count a
successful build alone as a discharged mathematical obligation.

R8 scoped D31 verification is complete. This complete source checkpoint and
push were explicitly authorized. The next release gates are public source
access and exact current Palomar preflight/full replay on Linux. The separate sharp proof route remains
open. This plan does not authorize publication, dependency changes, or
resumption of unrelated analytic research.

## Historical contract through 8 September 2026

The sections below preserve the old snapshots and iteration evidence. Their
D26' surface, BHP-first execution order, Guth--Maynard dependency and 28-item
dashboard are historical, not the current instructions.

## 1. Repository mode

Mode: `PALOMAR-FIRST`.

This repository is the prospective submission cone from its first substantive
commit. Mathematical discovery, diagnostics, alternate proof routes, and
historical modules remain in
`prime-cover-power-band-spectra-formalization`. Only checked declarations on a
selected-root dependency path may be ported here.

## 2. Frozen advertised surface

The surface is frozen at the strengthened D26' manuscript statement recorded
in the amendment below.

| Challenge declaration | Result | Solution status |
|---|---|---|
| `palomar_terminalBand_prescribedRanks` | every terminal-band centre, `21/61 < theta < 1/2`, explicit first-exit correction, `O(a/log X)` | open primary root |
| `palomar_terminalBand_primeCounting` | prime-counting corollary | open derivation |
| `palomar_almostAll_variableWidth` | D26' density-one variable-width theorem, `1/6 < theta < 1/2` | open primary root |
| `palomar_almostAll_subWeyl` | density-one sub-Weyl corollary | open derivation |

Nonclaims: no endpoint `theta = 1/2`, no every-centre result below `21/61`,
no removal of the almost-all exceptional set, and no RH, Möbius, random-matrix,
or bulk-statistics consequence.

## 3. Reverse dependency plan

Do not formalize the manuscript section by section. Work backward from the two
primary Solution roots.

| Owner module | Obligation | Selected-root consumer | Admission status |
|---|---|---|---|
| `Core` | minimal Paper I bridge and shared power-band objects | both roots | preapproved |
| `FirstExitTarget` | exact molecule root to explicit target, S1 | both roots | preapproved |
| `FullSpectrumTransfer` | full adjacency to one-exit squared spectrum, S2 | both roots | preapproved |
| `TerminalArithmetic` | BHP finite deletion, reciprocal sorting, capacity | prescribed root | preapproved |
| `TerminalSchur` | finite coherent-compression decomposition and Hilbert--Schmidt reduction to explicit arithmetic budgets | prescribed root | admitted; finite owner and all three budgets closed |
| `TerminalAssembly` | prescribed ordered-rank assembly | prescribed root | preapproved |
| `AlmostAllArithmetic` | direct Guth--Maynard exceptional-set input and reciprocal tiling | almost-all root | preapproved |
| `AlmostAllSpectralBudget` | normalized exact-frame collision/tail budget | almost-all root | preapproved |
| `AlmostAllAssembly` | terminal density and initial-segment assembly | almost-all root | preapproved |

Modules are created only when their obligation becomes active. A helper lemma
does not earn another file. Any tenth proof owner requires explicit replanning.

### Port, do not re-prove

The historical development contains substantial checked code. For every
preapproved owner:

1. inventory the exact source declarations consumed by the selected root;
2. reuse Paper I declarations through the pinned dependency;
3. transplant already-checked Paper II declarations, proof bodies, and only
   their necessary project-local helpers into the assigned owner;
4. record the source file, declaration name, and immutable source commit for
   every transplanted public theorem; and
5. rebuild the owner after removing broad or umbrella imports.

Do not rewrite a checked proof merely to make it look new. A source theorem is
re-proved only when its proof cannot survive the minimal dependency boundary,
and that failure must be recorded as the active obligation. Do not copy an
entire historical file when only a subset of its declarations is consumed.

## 4. Stage order and exit tests

| Stage | Product | Exit test |
|---|---|---|
| 0 | statement surface | Challenge/Solution types match; four deliberate holes only |
| 1 | shared finite core | S1 and S2 compile from `Core`, `FirstExitTarget`, and `FullSpectrumTransfer` |
| 2 | prescribed ranks | BHP input is audited; `TerminalSchur`'s finite reduction and its arithmetic budgets close; prescribed primary root has no `sorry` |
| 3 | almost all | direct Guth--Maynard Corollary 1.4 input is audited; reciprocal tiling and collision budget close; almost-all primary root has no `sorry` |
| 4 | corollaries | both corollaries are derived from the primary roots; Solution has zero holes |
| 5 | release | strict-cone, Comparator, independent-kernel, axiom, metadata, licence, and provenance gates pass |

### Progress dashboard

Percentages below count a frozen set of 28 release obligations.  They measure
completed obligations, not lines written or estimated proof difficulty.  The
denominator changes only after an explicit architecture revision.

| Major track | Completed / total | Progress | Remaining named obligations |
|---|---:|---:|---|
| Architecture and statement surface | 6 / 6 | 100% | none |
| Shared trusted producer cone | 3 / 3 | 100% | none |
| Prescribed-rank primary theorem | 3 / 6 | 50% | BHP input; terminal rank assembly; public root |
| Almost-all primary theorem | 0 / 5 | 0% | Guth--Maynard input; reciprocal tiling; normalized collision/tail budget; density assembly; public root |
| Public corollaries | 0 / 2 | 0% | prime-counting consequence; sub-Weyl consequence |
| Final release gates | 3 / 6 | 50% | zero Solution holes; clean public-root axiom surface; final Comparator/metadata/provenance pass |
| **Whole release checklist** | **15 / 28** | **54%** | **13 obligations** |

The public theorem surface is tracked separately: `0 / 4` Solution
declarations are closed.  The three completed producer roots are internal
dependencies and are not counted as public theorem completion.

Closed `coreBudget` micro-dashboard (diagnostic only; it does not change the
28-obligation denominator):

| Substep | Status |
|---|---|
| common-core coefficient majorant | closed |
| restricted response to full signed interior | closed |
| coherent pair to two-orientation `q,r` data | closed |
| power-range root and down-star windows | closed |
| direct denominator-safe bound in both orientations | closed |
| harmonic reciprocal-centre sum | closed |
| final `hcore` assembly | closed |

Thus the chain is **7/7 = 100%** and its release obligation is closed. The
next batch must choose another named dashboard row; it must not reopen the
superseded commutator/Gram route.

Iteration history against the same 28-obligation denominator:

| Iteration | Newly closed obligation | Cumulative progress |
|---|---|---:|
| 0 | release architecture and four-declaration surface | 6 / 28 = 21% |
| 1 | exact first-exit target producer (S1) | 7 / 28 = 25% |
| 2 | full-adjacency/one-exit transfer producer (S2) | 8 / 28 = 29% |
| 3 | finite coherent-compression reduction (`TerminalSchur`) | 9 / 28 = 32% |
| 4 | reachability, full-build, and producer-axiom interim gates | 12 / 28 = 43% |
| 5 | terminal-scale summed boundary-kernel budget in `TerminalSchur` | 13 / 28 = 46% |
| 6 | terminal-scale summed residual-energy budget in `TerminalSchur` | 14 / 28 = 50% |
| 7 | common-core coefficient majorant lifted to the signed-boundary pairing; summed `coreBudget` still open | 14 / 28 = 50% |
| 8 | signed-boundary majorant lifted from the restricted response to the full signed interior | 14 / 28 = 50% |
| 9 | oriented coherent pairs supply `q,r` and consume the full-interior majorant | 14 / 28 = 50% |
| 10 | power-range root/down-star windows instantiate `z,s,tau,delta` for the oriented coherent bound; reverse orientation and summation remain | 14 / 28 = 50% |
| 11 | exact residual commutator transfers reverse orientation to the safe entry plus a root-difference–Gram term; only the summed `coreBudget` remains | 14 / 28 = 50% |
| 12 | denominator-safe coherent entries are summed at `C (K+1)^3 log X / X`; the reverse root-difference–Gram charge is the sole remaining part of `coreBudget` | 14 / 28 = 50% |
| 13 | architecture review replaces the reverse-Gram route by a checked direct two-orientation coefficient estimate; no release obligation is counted yet | 14 / 28 = 50% |
| 14 | two-orientation estimate, harmonic summation, and final `hcore` assembly close `coreBudget` | 15 / 28 = 54% |
| 15 | refreshed dependency audit confirms that BHP `21/40` is not present in Mathlib, the pinned PNT package, Tau Ceti, CSLib, or another located public Lean proof; no code is admitted | 15 / 28 = 54% |

Every later batch must name one row above, report its before/after count, and
either close one obligation or strictly narrow its theorem type.  Merely
adding a module, helper declaration, or diagnostic does not increase the
percentage.

Iteration 15 is an intentional external-boundary stop. It adds no proof code
and does not count as closure. Resuming the BHP row requires either a pinned
unconditional Lean dependency or explicit authorization to open a separate
Harman-sieve formalization project; a local `Prop`, axiom, or conditional
adapter is not progress on the frozen Challenge.

Do not start a later stage to avoid a difficult earlier obligation. Two
consecutive batches that add code without closing or strictly narrowing the
active obligation trigger a stop and architecture review.

### Stage 0 baseline (2026-09-05)

- `lake exe cache get`: completed successfully at the pinned dependency set.
- `lake build`: completed successfully, 2732 jobs.
- Local release surface: 3 Lean modules, 518 lines, 4 selected declarations.
- Release-cone reachability: 3 reachable modules, 0 unreachable modules.
- Expected temporary axiom surface: the standard axioms plus `sorryAx` on the
  four deliberately open Solution declarations.
- No proof-owner module has been admitted yet.

### Stage 1 representation boundary (2026-09-05)

- `Core` is the first admitted proof owner and replaces the duplicated
  Solution implementation; it does not add a parallel graph API.
- The Challenge remains unchanged and Mathlib-only.
- The Solution now uses Paper I's definitionally identical vertex type through
  the pinned dependency while retaining transparent Paper II formulas.
- Targeted build of `Core`, Solution, and submission audit: 2733 jobs, exit 0.
- Solution holes remain 4; the strict narrowing is that S1 and S2 may now be
  ported on their native Paper I type without graph/type conversion lemmas.
- Exact source files and declarations are recorded in `PORT_MANIFEST.md`.

### Reuse decision (2026-09-05)

- Paper II is not being formalized again from mathematical prose.
- The two shared producers S1 and S2 already have checked proof bodies in the
  historical repository; those proof bodies are the authoritative migration
  inputs, subject to the immutable-checkpoint gate.
- Historical file boundaries are not authoritative.  Their first import layer
  alone contains 8,202 lines and their module-level union reaches about 30,000
  lines, largely because exploratory modules import neighboring routes.
- The clean repository therefore ports declarations into the nine frozen
  owners.  New Lean is limited to boundary adapters or a specifically recorded
  obligation that the checked proof cannot discharge at the reduced boundary.
- A batch that adds a parallel implementation of an already checked theorem is
  rejected even if it compiles.

### Stage 1 S1 extraction (2026-09-05)

- `FirstExitTarget` now owns the declaration-level extraction of the checked
  exact-molecule first-exit target theorem.
- The owner builds independently of the historical Paper II repository.
- The selected theorem has only `propext`, `Classical.choice`, and `Quot.sound`
  on its axiom surface.
- No local proof hole was introduced. The four Solution holes are unchanged;
  S1 is a shared internal producer rather than one of the public statements.
- Local source is now 10,483 Lean lines across five modules, with zero intended
  historical umbrella imports. The 20,000-line ceiling remains in force.
- The remaining Stage 1 obligation is S2, the full-adjacency to one-exit
  squared-spectrum comparison.

### Statement-surface amendment (2026-09-05)

- Paper II Theorem 1.3 was strengthened after the Stage 0 freeze by replacing
  its pointwise short-interval branch with a tiled mean-square argument.
- The Challenge and `Core` now use the simplified error
  `a / log X + log(X)^D * (X / a^2 + sqrt (X / (a log X)))`; the coherent
  `a^2 / sqrt X` term is absorbed by `a / log X` on every fixed
  sub-square-root power range.
- The sub-Weyl margin is the manuscript minimum of the three remaining
  exponent gaps. The formerly listed fourth gap was redundant and belonged
  to the absorbed coherent term.
- This is a deliberate pre-proof contract amendment, not a fifth Challenge
  declaration. The advertised surface is frozen again at this version.

### Stage 1 S2 extraction (2026-09-05)

- `FullSpectrumTransfer` owns the declaration-level extraction of the checked
  full-adjacency to one-exit squared-spectrum comparison.
- The selected theorem gives a nonnegative squared-eigenvalue displacement
  bounded by an explicit constant times `a / log X`, uniformly on every fixed
  power range below `1/2`.
- The extractor dropped three source `[simp]` attributes; restoring exactly
  those attributes closed the only four elaboration mismatches.
- Targeted owner build: 4,217 jobs, exit 0; no local proof hole.
- Stage 1's two shared producers S1 and S2 are now present. Stage 2 must begin
  with the prescribed-rank arithmetic/Schur obligation rather than another
  shared spectral module.

### Stage 2/3 input audit (2026-09-05)

- The clean repository is migration-first: it will not re-formalize checked
  Paper II finite algebra from the manuscript.
- The historical BHP and Guth--Maynard interfaces are conditional `Prop`
  inputs. Their adapters are checked, but the input propositions themselves
  are not theorems in the historical repository, pinned Mathlib, or the pinned
  `PrimeNumberTheoremAnd` dependency. The almost-all manuscript now consumes
  Guth--Maynard Corollary 1.4 directly; no separate continuum mean-square
  theorem is part of the release plan.
- `TerminalSchur` now compiles the finite full coherent-entry
  Hilbert--Schmidt reduction. It replaces the monolithic coherent obligation
  by three explicit premises: the common-core quadratic budget, the summed
  boundary-kernel mass, and the summed residual energy. Those arithmetic
  estimates and the terminal-scale assembly remain open; the finite graph and
  matrix decomposition no longer do.
- These are release blockers, not invitations to add broad analytic or
  exploratory modules.  The exact theorem-level matrix and admission rule are
  frozen in `PALOMAR_BLOCKERS.md`.
- `TerminalSchur` is the fourth proof owner. No fifth owner may be admitted
  until it closes one of the remaining named analytic or terminal-scale
  budgets. The four unconditional Challenge declarations remain unchanged.

### Stage 2 finite coherent-compression owner (2026-09-05)

- `TerminalSchur` owns
  `exactOneExitLocalCoherentCompressionResidual_frobenius_sq_le_core_kernel`.
- The theorem decomposes the literal coherent compression residual into its
  signed-interior, boundary-kernel/interior, and boundary-kernel/residual
  pieces, then proves the combined Frobenius-square bound from explicit
  `coreBudget`, `boundaryKernelBudget`, and `residualBudget` premises.
- Targeted build: 4,218 jobs, exit 0; full repository build: 4,222 jobs,
  exit 0. The owner contains no `sorry`, `admit`,
  project `axiom`, `native_decide`, or `Lean.ofReduceBool`.
- The owner is reachable from `PrimeCoverPowerBandSolution` and its selected
  theorem is on the submission axiom-audit surface. Its printed axioms are
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Local source is 18,864 Lean lines across seven reachable modules. Only 1,136
  lines remain under the 20,000-line ceiling. Consequently BHP and
  Guth--Maynard must be supplied by pinned dependencies or very small
  theorem-level adapters; their analytic proofs cannot be developed inside
  this release repository.

### Stage 2 boundary-kernel budget (2026-09-06)

- `TerminalSchur` now also owns the terminal-scale producer
  `eventually_powerRange_sum_exactPrincipalMoleculeBoundaryKernel_sq_le`.
- On every fixed power range `theta < 1/2`, the summed boundary-kernel mass
  over centres `a ≤ K ≤ X^theta` is
  `O((K+1)^2 (log X)^3 / X^{3/2})`. This is the explicit
  `boundaryKernelBudget` consumed by the finite coherent Schur theorem.
- The pointwise source-weighted bound
  `eventually_powerRange_exactPrincipalMoleculeBoundaryKernel_sq_le_scale`
  is an in-owner lemma used only to assemble that sum.
- Targeted owner build: 4,218 jobs, exit 0, 637s for `TerminalSchur`.
  Submission-audit rebuild: 4,220 jobs, exit 0.
- Both new theorems print exactly `propext`, `Classical.choice`, and
  `Quot.sound`. No local `sorry`, `admit`, project `axiom`, `native_decide`,
  or `Lean.ofReduceBool`.
- Local source is 19,043 Lean lines across seven reachable modules. Only 957
  lines remain under the 20,000-line ceiling. The next admissible
  `TerminalSchur` obligations are the common-core and residual-energy
  budgets; no fifth owner is admitted.

### Stage 2 residual-energy budget (2026-09-06)

- `TerminalSchur` now also owns
  `eventually_powerRange_sum_exactPrincipalMoleculeResidual_sq_le`.
- On every fixed power range `theta < 1/2`, the summed residual energy over
  centres `a ≤ K ≤ X^theta` is `O((K+1)^2 / log X)`. This is the explicit
  `residualBudget` consumed by the finite coherent Schur theorem.
- The pointwise bound uses the already-checked exterior residual identity,
  the first-exit interior gap `mu/100`, and the existing residual-scale
  bundle `eta^4 / mu^2 ≪ a / log X`.
- Targeted owner build: 4,218 jobs, exit 0, 241s for `TerminalSchur`.
- Both new theorems print exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- Local source is 19,222 Lean lines across seven reachable modules. Only 778
  lines remain under the 20,000-line ceiling. The remaining `TerminalSchur`
  arithmetic obligation is the common-core budget; no fifth owner is
  admitted.

### Stage 2 reverse-orientation bridge (2026-09-06)

- `TerminalSchur` now proves the exact commutator identity relating one local
  compression-residual entry to its reverse.  The only correction is the
  difference of the two molecule roots times their real Gram overlap.
- Its norm consequence is on the selected-root axiom audit and prints exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- Targeted owner build: 4,218 jobs, exit 0. Submission-audit build: 4,220
  jobs, exit 0. No implementation owner contains `sorry`, `admit`, or a
  project `axiom`.
- Local source was 19,358 Lean lines across seven reachable modules before
  Iteration 12. The iteration adds the summed denominator-safe theorem without
  a new module; the current total is 19,493 lines, leaving 507 under the
  20,000-line ceiling. The root-difference–Gram charge is now the only
  unproved part of the common-core budget.

### Stage 2 oriented common-core sum (2026-09-06)

- `eventually_powerRange_sum_oriented_coherent_core_entry_sq_le` sums every
  coherent entry in the denominator-safe orientation and proves the explicit
  bound `C (K+1)^3 log X / X`.
- Targeted owner build: 4,218 jobs, exit 0. Submission-audit build: 4,220
  jobs, exit 0. The new theorem uses only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Solution holes remain 4 and the overall obligation count remains 14/28:
  this is a strict narrowing of `coreBudget`, not closure of that obligation.
- The remaining reverse root-difference--Gram estimate is new mathematical
  proof work. Under the Palomar-first contract it returns to the historical
  research repository; only a checked final theorem may be ported back into
  this owner. No Iteration 13 code starts here before that source theorem
  exists.

### Stage 2 common-core budget closure (2026-09-08)

- Research first closed the reverse-orientation obstruction in
  `/private/tmp/ReverseCoreResearch.lean`, SHA-256
  `e17408db6c55089c6df0aa5a86797e6ea8f3c632f17e7a524eae91ae39adc617`.
- The checked replacement bounds both orientations directly by
  `a log X / X + a^2 (log X)^2 / (b X)` and sums the second term using
  `sum_{b <= K} 1 / b <= 1 + log K`.
- `eventually_powerRange_sum_coherent_core_entry_sq_le` supplies the complete
  `coreBudget`. The theorem
  `eventually_powerRange_exactOneExitLocalCoherentCompressionResidual_bound`
  combines it with the previously closed boundary-kernel and residual-energy
  budgets.
- The old one-sided theorem and reverse root-difference--Gram commutator route
  were deleted rather than retained as parallel infrastructure.
- Targeted owner build: 4,218/4,218. Selected Solution/audit build:
  4,220/4,220. Both new audited roots use exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Local source is 20,243 Lean lines across seven reachable modules, with no
  new owner or unreachable module. The four public Solution holes are
  unchanged.

## 5. Size budget

| Metric | Initial | Current | Approved ceiling |
|---|---:|---:|---:|
| Local Lean modules | 3 | 7 | 12 |
| Proof-owner modules | 0 | 4 | 9 |
| Challenge declarations | 4 | 4 | 4 |
| Challenge lines | 253 | 252 | 300 |
| Total local Lean lines | 518 | 20,243 | 20,500 |
| Unreachable local modules | 0 | 0 | 0 |

No historical audit umbrella, alternate coordinate, speculative theorem, or
unused module may enter this repository.

The user clarified on 2026-09-08 that 20,000 lines was a planning target, not
a strict ceiling. The reviewed ceiling is therefore 20,500. This revision
admits the necessary replacement proof only: it creates no module or theorem
family and deletes the obsolete one-sided commutator/Gram route.

## 6. Per-batch report

Every implementation batch reports:

```text
Solution holes before / after:
Active obligation and theorem-type delta:
Owner modules changed:
New modules:
Reachable / unreachable local modules:
Local Lean lines before / after:
Owner and selected-root build evidence:
Axiom evidence:
```

## 7. Source boundary

Paper I dependency:
`shaikidris/prime-star-spectra-formalization@59176e4ce57e7d6578cafd1de0029fed6fc13ccf`.

Historical Paper II proof source:
`shaikidris/prime-cover-power-band-spectra-formalization` at committed parent
`a6f8efa91346a6401ba9191d1b12f8552727e380`, plus an uncommitted working batch
that must receive an immutable checkpoint before any of its declarations are
ported as authoritative proof source.

## Post-freeze iteration — source pushed; publication approval pending

Both canonical source `454743470f6aff2e7f7f8ac79a7a2a7279e60ada` and preserved
sharp branch `11e71d0cec4f2e8de8e2542bb0b7a4888782607f` were pushed through
the configured personal SSH remote; an independent readback matched both.
The source worktree is clean. The exact current verifier was fast-forwarded
without modification into the existing public rehearsal fork. Inputs for
preflight/full/render are prepared but not dispatched. The source visibility
has not been changed while the explicit approval question is pending.
P7's source/account advisory and draft handoff are prepared independently;
its mechanical/render evidence gates remain open. Progress remains 5/8.

## Continuation — dependency availability verified

The previous goal turn made concrete progress by committing/pushing the source
freeze and audit receipts. This continuation rechecked the clean source at
`454743470f6aff2e7f7f8ac79a7a2a7279e60ada` and confirmed that GitHub still
reports the source repository as private. No publication approval has arrived.

An independent P5 requirement is now verified: unauthenticated GitHub reads
returned the exact commit and a tree for all 15 pinned Lake dependencies.
The first Python request attempt hit a local certificate-store error; the
system curl retry retained TLS verification and passed all 15. This is source
availability evidence, not a protected build. Receipt:
`readiness/p5-anonymous-dependencies.json`. No source or dependency was changed.
Progress remains **5/8**, with P5 awaiting the same public-visibility approval,
P6 not dispatched and P7's final reconciliation pending those results.

## Blocked audit — publication decision required

The same pending-publication condition has remained across three consecutive
goal turns. The previous turn made concrete progress by verifying all 15
pinned dependency commits anonymously. This turn rechecked the source and
receipt worktrees and the GitHub visibility: both worktrees are clean, source
HEAD equals `origin/main`, and the source repository remains private. No
public-visibility approval or source-specific workflow run has arrived.
The goal is therefore marked **BLOCKED**, not complete. P0--P4 remain verified;
P5 needs approval/public source access, P6 needs protected replay/render and
P7 needs final reconciliation. There is no remaining independent action that
can satisfy those gates while the publication decision is pending.

Resume from the frozen source `454743470f6aff2e7f7f8ac79a7a2a7279e60ada`:
record explicit approval, establish and check anonymous source access, refresh
current verifier pins, dispatch the prepared preflight/full/render workflows,
and inspect their exact receipts before completing the manual handoff.
No new mathematical proof work or Palomar state change is included.
Receipt: `readiness/blocked-goal.json`.

## User sequencing correction — private readiness before publication

The user made publication the last pre-Palomar step. The earlier assumption
that P6 must wait for public source was too restrictive. The unchanged current
verifier's trusted `clone_commit` accepts a repository-scoped Git authentication
header through its process environment. That permits an exact private source
fetch on GitHub-hosted Linux without modifying the verifier or its proof checks.
The initial transport header is discarded before protected execution; both
source checkouts are checked for persistent credential configuration. Neither
Lean nor the renderer execution receives that private source token.

The private workflow lives only on this audit branch. It fetches
PalomarSubmission `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763` separately;
upstream Comparator/NanoDa/exporter/Landrun build and execute commands are
retained unchanged. Renderer code is likewise pinned and unchanged. Source
remains `454743470f6aff2e7f7f8ac79a7a2a7279e60ada`. Reports and render artifacts
stay inside this private repository. This is a private Linux rehearsal, not
anonymous availability evidence or a Palomar submission. P5 retains that final
public-access obligation. Current verifier and policy heads were refreshed and
still match the frozen pins. Workflow syntax, every shell block, wrapper syntax,
credential-step scope and exact retained protected commands were reviewed.
Private Actions is enabled. No new Lean module, theorem, source change or
visibility change is included. P6 results remain unclaimed until the run ends
and its bounded reports and rendering have been inspected.

## Private rehearsal iteration — root-path intake repair

Run `34465135183` started privately from orchestration `0ce5069`. Its verify
job completed with a preflight input failure before any proof build: current
intake rejects literal `project_path: "."`; a root project must omit that
field. Both preflight/full packets and the exact handoff value are corrected.
The current request parser confirms both now carry an empty root field and the
same frozen source SHA. No source revision or theorem change is needed.
The final job-status guard now preserves that actual preflight error instead
of adding a missing-full-report traceback. This is reporting only; a full
`status: pass` report remains required.

The independent render job successfully fetched private source, installed the
exact toolchain and Landrun, and passed the credential-free execution guard.
It is still running protected rendering. Keep that run; the next push retries
verification only and does not restart or narrow the render obligation.
Both final receipts must bind the same source and tool revisions. Publication
remains deferred until P6/P7 complete. Evidence: `readiness/p6-private-runs.json`
and `readiness/p6a-first-preflight-failure.json`. Progress remains 5/8.

## P6a verified — exact private preflight receipt

The corrected private preflight in run `34465598832` reports `pending` at
`prepared`, the successful preflight condition, with no errors or warnings.
The downloaded receipt binds source `454743470f6aff2e7f7f8ac79a7a2a7279e60ada`,
Lean v4.32.0, exporter `4e7915201d3f9f04470d9eae002fa695f7cdc589`, the two D31
roots and sixteen definition selections. Comparator, formalization, lakefile
and manifest hashes all match the frozen source; wrapper-recorded verifier and
renderer hashes match the unchanged pinned upstream checkout. No credential
was persisted in the source Git configuration. The official classification
labels agree with the mathematical account.

P6a is VERIFIED; P6b is running in this second run, while P6c retains the
original live render run. Overall progress remains 5/8 until all P6 substeps
finish. Receipts: `readiness/p6a-preflight-report.json` and
`readiness/p6a-preflight-report.transport.json`. Public availability has not
been asserted and publication remains the final P5 step.

## P6c verified — exact render and reader inspection

The original render job completed successfully despite its sibling's earlier
intake-input failure. Its actual report has `status: pass`, `stage: complete`,
no errors, the frozen source and Challenge hash, and the pinned renderer/Lean/
Landrun revisions. Recomputed all 18 artifact file hashes and the canonical
tree hash; they match `0c7542a512ededb34cafc21a5d8a90aefb546be2fe04f43428d94e9fa7dbdc1d`.
No renderer or artifact bytes were modified.

Browser inspection confirmed both selected English docstrings and their
statements in the normal view. Current upstream `isolateComparedDeclarations`
intentionally narrows that view to configured declarations, so it omits the
module overview there. The overview remains in the sanitized HTML and metadata.
It was visually inspected in that exact static HTML with script execution
temporarily disabled, then normal execution was restored. Its BHP distinction,
full range, squared-error comparison and endpoint exclusions are intact. This
explains the display difference; it does not assert that the intake UI displays
the overview. Literal dollar-delimited math in the Corollary prose remains
readable. No candidate documentation regression was found.

P6a and P6c are VERIFIED; P6b is still running its protected Comparator and
challenge provenance audit after successful pinned tool builds. The local
watch process lost its API connection, but a fresh job snapshot confirms the
same remote job is alive. It was not restarted. Overall progress remains 5/8.
Receipts: `readiness/p6c-render-report.json`, its transport sidecar,
`readiness/p6c-render-artifact-manifest.json` and
`readiness/p6c-render-inspection.json`.

## P6b/P6 verified — protected D31 proof replay

Run `34465598832` completed successfully. The downloaded full report has
`status: pass`, `stage: complete`, no report errors or warnings, and the same
frozen source as preflight and render. All seven reported file hashes, both
theorem selections, sixteen definition selections, three permitted axioms,
fifteen dependency pins and pinned tool revisions match. The protected
Challenge provenance has `trust_level: high`, eight audited sources and no
untrusted sources. Its canonical olean hash is
`d948cba519633e60bda7a35bffb55f238b80e0e84ef26fcd7761ea3cef74080e`.

The actual Comparator log records a successful 4236-job selected build,
`nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`
and `Your solution is okay!`. Comparator returned zero after 1955.37 seconds,
with reported maximum RSS 5,642,096 KiB. This duration includes its selected
build and checks; it is not a kernel-only timing. The full protected step ran
from 10:26:09 to 11:02:38 UTC. Inherited build lint/info messages remain; the
empty top-level warning array does not assert a warning-free Lean build.

P6a, P6b and P6c are now VERIFIED, closing P6. Overall progress is 6/8.
P7 must reconcile the advisory and exact handoff before the final P5 publication
and anonymous-fetch gate. No Palomar record was created. Receipts:
`readiness/p6b-mechanical-report.json`, its transport sidecar and
`readiness/p6b-mechanical-validation.json`.

## P7 verified — final packet reconciled before publication

The source/account assessment and exact handoff now consume the actual
protected mechanical and render receipts at source `4547434`. Both selected
D31 results, all sixteen definitions, all fifteen dependency pins, the current
classification labels and source/proof provenance are consistent. The packet
explicitly preserves the sharp open targets and separates the proved internal
Section 10 exports from the two-result selection. The source's existing review
status is supplemented by these audit receipts without rewriting the frozen
source to embed later evidence.

No affirmative blocker was found in this bounded preparer review. Novelty and
a separate human review remain unestablished; inherited lint and the upstream
render presentation limits are disclosed. The successful private rehearsal is
not a Palomar submission and does not itself prove anonymous source access.
P7 is VERIFIED; overall progress is 7/8. All private preparation is finished.
P5 is now the final publication and exact anonymous-fetch step, honoring the
user's sequencing instruction. Evidence: `readiness/p7-reconciliation.json`,
`readiness/advisory-review.md` and `PALOMAR_HANDOFF.md`.

## Scope clarification — certified D31 pair versus open sharp targets

The user asked whether the stronger headline statements remain in Challenge,
and then how Palomar could accept them while their Lean proofs are open.
All four statements remain, but the successful protected receipt selects only
Theorem 1.3 and Corollary 1.4. Theorem 1.1 and Corollary 1.2 are not certified
by that receipt. Palomar's current policy explicitly fixes the verified claims
through the selected Comparator configuration and allows deliberate Challenge
holes; this does not permit representing open targets as proved results.

An explicit scope question is pending: proceed with the two proved D31
results, or hold publication until all four headline results have proofs.
Publication remains on hold while that material scope question is answered.
This is not a failed mechanical check. P0--P4, P6 and P7 remain verified for
the D31-only packet, at 7/8 tasks; a four-result entry would reopen the proof
and submission-scope work. No public visibility or Palomar state changed.
The protected verification job has completed successfully.
Policy: https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#23-comparator-configuration
