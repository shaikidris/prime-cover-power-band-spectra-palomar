# Paper II Palomar release-cone contract

## Current plan — D31 rebase, 9 September 2026

This section supersedes the execution order, almost-all dependency map, and
progress denominator in the historical contract below. This is a planning
revision, not a Lean implementation or a new theorem-completion claim.

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

The current Challenge/Solution files still encode D26': lower endpoint
`1/6`, an extra `X/a^2` error, and a sub-Weyl rather than sub-block margin.
They do NOT yet encode the revised paper. All four Solution holes remain.
Do not change their types piecemeal or report the native 4/4 proof products
as formal completion.

### Next statement-surface amendment (R1)

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
no reason to recreate the molecule. R2 must still check the normalized vector,
principal-submatrix identification, and source/target maps against the repair.

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

### Frozen D31 obligation checklist

Each row has one exit test. Stages have two rows each; close them in order.
All rows are OPEN / NOT REVALIDATED for the revised consumer. No percentage
credit is inferred from inspection, native proofs, or historical builds.

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

Current revised checklist: **0/8 validated (0%)**. This is eight remaining
consumer checks, not a claim that no reusable Lean work exists. Historical
progress remains **15/28**, measured against the superseded D26' contract;
do not add or compare those percentages. Public theorem closure is **0/4**.
No code or build was performed during this planning revision.

R1 is a statement-alignment gate, not successful verification of an admitted
Solution. Official selected-proof Comparator and independent-kernel evidence
must wait for the relevant holes to close and the release stage to begin.

### Four mini-goals and iteration markers

Use this table and the R-rows above as the single live task list. No additional
tracker or per-iteration file is needed. Keep only one R-row active; reuse
existing proofs before writing new ones.

| Mini-goal | Tasks | Exit | Current completion |
|---|---|---|---|
| MG1 — align and reuse | R1, R2 | revised statements and audited full-star/S1/S2 inputs agree with D31 | 0/2; R1 NEXT |
| MG2 — finite comparison and actual frame | R3, R4 | same-index finite comparison and graph-specific global residual estimates | 0/2 |
| MG3 — close the spectral estimate | R5, R6 | actual complement gap and ordered mean-square/tail theorem | 0/2 |
| MG4 — public consequences and verification | R7, R8 | two D31 public proofs and their scoped verification | 0/2 |

One closed R-row earns one of eight checklist units. Mini-goal boundaries
are therefore 25%, 50%, 75%, and 100% of this D31 checklist; these are not
estimates of elapsed effort, code completion, or the combined four-root release.
Native paper proofs, this Git checkpoint, and code growth earn no units.

At the end of every iteration, report this compact marker, followed by the
literal theorem or hypothesis change and its verification evidence:

```text
D31 | active R1 | MG1 0/2 | checklist 0/8 (0%) | public roots 0/4
Delta: [closed row, strictly reduced hypothesis, or no mathematical change]
Evidence: [target build; axiom result; statement/consumer match]
Reuse/growth: [reused declarations; owner; line delta; new modules]
Next: [one R-row and its smallest remaining obligation]
```

Update counts only when the row's exit test passes. A narrowed row remains
open, with the eliminated and remaining hypotheses named explicitly. After
two code-growing iterations without closure or strict hypothesis reduction,
stop that route and review the same row; do not open another helper module.
The present checkpoint freezes the plan only: **0/8**, next **R1**.

After R8, resume the separate sharp track: audited BHP input, remaining
buffered/internal alignment and rank assembly, then its two public roots.
Completing D31 does not make the combined Solution ready while sharp holes
remain. An earlier D31-only registry release requires an explicitly scoped
Solution/audit surface without those holes; do not silently weaken the
repository's zero-admission release gate.

### Owner and growth control

- Existing owners: `Core`, `FirstExitTarget`, `FullSpectrumTransfer`,
  `TerminalSchur`. Keep them; delete no historical proof in this planning pass.
- Next preapproved owners: `AlmostAllSpectralBudget` and
  `AlmostAllAssembly`. No separate file for Lemma 5.4, sorting, or a corollary.
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
- Before admitting either next owner, record exact source declarations and
  dependencies in `PORT_MANIFEST.md`; shared facts are extracted once.
- Two successive code-growing batches without closure or a strict reduction
  of the active row's hypotheses trigger replanning, not another helper file.

Per iteration report: active R-row; before/after status and changed theorem
type; stage completion; 0--8 total; actual public holes; owner/new-module and
line deltas; targeted build/axiom results; next single task. Do not count a
successful build alone as a discharged mathematical obligation.

The next task is R1, followed by R2. This plan does not authorize publication,
dependency changes, or resumption of unrelated analytic research.

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
