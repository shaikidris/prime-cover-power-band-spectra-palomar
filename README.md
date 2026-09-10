# Prescribed eigenvalues in prime-cover power bands

This is the Palomar-first formalization repository for Paper II,
*Prescribed Eigenvalues in Power Bands of Finite Prime-Cover Graphs*.
Paper I is reused through its pinned public dependency. The broad historical
Paper II Lean repository supplies proof provenance, not umbrella imports.

This development checkpoint includes the D31 Lean implementation, its
statement surfaces, and pinned dependencies. The D31 local checklist is
complete. The two sharp proofs and official submission verification remain
open; this is not a Palomar-ready release.

## Current plan: D31 first

The controlling plan is the **9 September D31 rebase** in
[PALOMAR_RELEASE_CONE.md](PALOMAR_RELEASE_CONE.md). Its source is
[the canonical manuscript](../prime-orthant-geometry/draft/prescribed-eigenvalues-in-prime-cover-power-bands.md).

The two proof routes are now separated:

1. **Ordered mean-square / density one**, for every fixed
   `0 < theta < 1/2`, with error
   `a/log X + log(X)^D sqrt(X/(a log X))`.
   This uses global PNT and full-star frame/complement estimates, but no BHP,
   Guth--Maynard, reciprocal tiling, or local internal-core capacity.
2. **Sharp every-centre terminal ranks**, for `21/61 < theta < 1/2`,
   with error `O(a/log X)`. BHP and buffered capacity remain necessary
   inputs to this proof route.

The two D31 public almost-all theorems now have compiled proofs with standard
axioms only. Their frozen Challenge types are unchanged. The two sharp
terminal-band proofs remain open. R8 scoped D31 verification is complete;
final Palomar submission readiness is **PARTIAL**.

The [10 September submission analysis](PALOMAR_SUBMISSION_ANALYSIS.md)
confirms a strict Comparator identity blocker in the shared Challenge/Core
definitions, despite the passing local definitional-equality check. The source
checkpoint is pushed. An admission-free D31 Solution surface, public source
access and exact protected verification remain release gates.

## Progress and reuse

- Existing code after R8 (unchanged from R7): nine local modules, six proof owners, 33,559 Lean lines
  including lakefile. Reuse it; no restart or new repository.
- Previous evidence: S1, S2 and local coherent producers have recorded builds
  and axiom checks in [PORT_MANIFEST.md](PORT_MANIFEST.md).
- Current public Solution holes: **2**; completed public declarations: **2/4**.
- Revised D31 checklist: **8/8 validated (100%)**; MG4 **2/2 COMPLETE**. This measures bounded checks
  against the new consumer, not the fraction of reusable code.
- Historical **15/28** belongs to the old contract and is not current progress.
- R1: full build passed, 4,222 jobs; 28 declaration types and 24 definition
  values match locally. This verifies statements, not the admitted proofs.
- R2: full-star/S1/S2 inputs, correction regularity/logarithmic size and the
  exact public-rank bridge freshly audited; final full build 4,222 jobs.
  Eight declarations reused verbatim, two small adapters, no new module.
- R3: same-index low-complement comparison, Hermitian HW/Weyl, weak sorting
  with ties, and the squared-energy mean-square bound compile. Five finite
  controls passed; full build 4,238 jobs; new audited roots use standard axioms only.
- R4a: actual phase-aligned, normalized projected prefix columns, exact Gram
  subtraction and residual with adjacency-on-tail compile. Full build 4,238
  jobs; new audited roots use standard axioms only. This narrows R4 but does
  not close the global budgets or change the 3/8 count.
- R4b narrowed: actual spectral-component capture, the signed zero-source
  identity, and the discarded boundary-kernel zero mode and quantitative
  rate compile. Full build 4,238 jobs; new audited roots use standard axioms
  only. The actual signed source is now identified with the orthogonal sum
  of canonical down-star leaf kernels; its squared norm is at most omega(a)/2.
  The complete tail/continuation estimates remain open; signed-response
  and kernel-response capture are closed in the checkpoints below.
- R4b source-local extraction now compiles: the actual canonical down-source
  spectral component is captured under separation from the other blocks of
  that source only, without global degree uniqueness. Its signed coefficient
  is explicit. The coefficient is now proved nonzero when source and target
  degrees differ, and the actual normalized negative down-mode is captured
  under source-local degree separation. A fixed-multiple allowed-prime gap
  is proved from pinned global PNT. The smallest-prime source construction
  now discharges all those premises: every allowed negative boundary mode
  in a fixed power range below exponent 1/2 is eventually captured.
  Equal-degree up-targets now have proved identical boundary-leaf segments.
  The actual negative signed source and its first-exit response have captured
  negative spectral components, uniformly on that power range, including
  repeated target degrees. Full build 4,238 jobs; eight new roots use only
  standard axioms; seven exact controls pass.
- R4b kernel coefficients now compile on the actual graph: the first-exit
  projection fixes H*zeta, adjointness identifies the reverse source, active
  up-targets use the exact partial kernel sum, down-targets have zero
  coefficient, and equal-degree up-target coefficients agree exactly.
  The whole negative kernel-source spectral component and its actual
  first-exit response are now captured on every fixed power range below
  exponent 1/2, including repeated target degrees. Full build 4,238 jobs;
  six new audit roots use standard axioms only; five exact controls pass.
- R4b full-tail identity now compiles: on every complete prefix K <= X^theta,
  theta < 1/2, the actual discarded molecule matrix satisfies L Z = 0 and
  hence A Z = H Z. This discharges the forest-zero premise of the projected
  residual identity, not its norm bound. Full build 4,238 jobs; three new
  audit roots use only standard axioms. Quantitative tail and one-source
  continuation bounds remain open, followed by the global frame estimates.
- R4b quantitative-tail checkpoint: the actual positive response is retained,
  while the discarded negative response is exactly -2/nu times the discarded
  down-kernel source. The scalar equation and existing first-exit gap give
  |alpha-minus| <= 100 eta^2/mu^2 and bound the kernel response by its boundary
  kernel. These now prove the full tail squared norm is at most
  C (a log^3(X)/X^(3/2) + a^3 omega(a) log(X)/X^2), uniformly on the fixed
  sub-square-root power range, with no gap/capture/norm premises.
  The log-cubed term is the existing Lean producer, not the manuscript's
  sharper log-squared term; the global log-power consumer permits it.
  Full build 4,238 jobs; six new audit roots use only standard axioms.
  The quantitative-tail exit test is CLOSED. Continuation counts remain OPEN.
- R4b continuation multiplicity is now CLOSED on the actual first-exit
  support: outside the original boundary star, an incoming upward prime
  divides the source. The incoming count is at most omega(a)+omega(v).
  Consequently the actual raw residual squared norm is at most
  `(2 log(X)/log(2)) sum_w degree_H(w) |interior(w)|^2` for X >= 2.
  This is a proved finite graph estimate, not an assumed collision budget.
  The remaining one-source obligation is to bound that degree-weighted
  response sum by a fixed power of log(X), retaining the down-centre weights.
  Full build 4,238 jobs; all four new audit roots use standard axioms only.
  No global residual, isometry or public theorem is promoted.
- R4b weighted-response checkpoint: the actual moving down-star degrees
  satisfy `q d_a <= 48 d_(a/q)`, and the signed response at the down-centre
  is at most `10000/(q mu_a)`. The prime q varies with a; this is not a
  fixed-label limit. The degree-weighted kernel response is O(log^3 X).
  Integrated into the raw residual, it leaves only the signed weighted
  sum plus O(log^4 X), with no remaining kernel/gap premise. Full build
  4,238 jobs; four new standard-axiom roots; no new module.
  The signed up/down response sum and R4c/d global estimates remain OPEN.

- R4b down-centre sum CLOSED: the finite degree bound is `degree_H(w) <=
  X/w + omega(w)`. Combined with the compiled `10000/(q mu_a)` response,
  it gives the whole moving-prime down-centre weighted sum `<= C log^2 X`.
  Targeted 4,234/full 4,238 jobs pass; three new standard-axiom roots.
  The up-centre/leaf rows and their support-sum assembly remain OPEN;
  R4c/d are unchanged. Checklist 3/8, public proofs 0/4.

- R4b up-centre sum CLOSED: exact two-mode synthesis includes active and
  isolated targets. The actual response is at most `600/mu_a`; summing with
  `X/(a q)+log(X)/log(2)` gives the whole up-centre row `<= C log^2 X`.
  Both centre rows are now closed. Leaf rows and their exact support-sum
  assembly remain, before R4c/d. Full 4,238-job build passes; four new roots
  use standard axioms. Checklist 3/8, public proofs 0/4; no new module.

- R4b one-source continuation CLOSED: all actual canonical leaf rows and
  the complete compression-support sum are now assembled. Uniformly for
  allowed moving centres below every fixed sub-square-root power,
  `eventually_powerRange_exactPrincipalMoleculeResidual_sq_le_logFifth`
  proves the actual residual squared norm is `<= C log^5 X`. No response,
  support, gap or collision premise remains. Full 4,238-job build passes;
  ten new roots have standard axioms only. Semantic lint retains exactly
  the same 93 inherited findings, none in this owner. No new module.

- R4c projected HS estimate CLOSED: the actual normalized projected prefix
  residual has `matrixFrobeniusNorm(J_K)^2 <= C K log^5 X`, including K=0.
  Adjacency on the discarded phase-fixed tail is bounded by C log^3 X
  using LZ=0. Seven new standard-axiom roots; target 4,234/full 4,238 jobs
  pass. Empty-prefix and coherent-column controls pass; no new semantic
  lint findings. This is the projected normalized frame, before final
  symmetric reorthonormalization. At that checkpoint the operator and
  Gram estimates were still open; the operator transfer is now closed below.

- R4c signed residual leaf-Gram row CLOSED: on each complete prefix K,
  the sum over all partner sources and all large-prime output coordinates
  of absolute entry products is at most C K^3 log^4 X / X. The proof uses
  actual signed exterior responses, cutoff-preserving edges, the canonical
  leaf bound, incoming divisor multiplicity, and the actual PNT degree
  lower bound. Six new standard-axiom roots; full build 4,238 passes.
  No centre-output collision bound is assumed or discharged by this result.

- R4c signed residual centre-Gram row CLOSED: for each source, summing
  all distinct partner sources and all centre-type outputs gives
  <= C K^2 log^4 X / sqrt X. The actual common-output count is bounded by
  8Y(omega(a)+omega(b)), retaining one free common small prime. The proof
  supplies the nonreturning paths, coefficients and PNT degree scales.
  Eight new standard-axiom roots; full 4,238-job build and exact controls
  pass, with the same 93 inherited lint findings. No new module.

- R4c signed collective operator CLOSED: the actual signed exterior
  prefix matrix has squared Euclidean operator norm
  `<= C log^5 X (1 + K^2/sqrt X)`. The diagonal consumes the proved
  signed degree-weighted response; leaf and centre rows retain the
  coherent term. A signed Gram comparison uses absolute entries, not a
  positivity assumption on the Gram itself. Four new standard-axiom
  roots; target 4,234/full 4,238 jobs pass, with no new semantic lint
  findings. Kernel restoration and projection/normalization remain separate.

- R4c actual projected operator CLOSED: the existing
  `projectedFullStarFrameResidual` has squared Euclidean operator norm
  `<= C log^5 X (1 + K^2/sqrt X)`. Kernel restoration, unit phases,
  adjacency on the discarded tail, projection and column normalization
  are all included. The kernel/tail proofs retain a/X and a/sqrt X
  before summing; no new collision estimate or module is used.
  Seven new standard-axiom roots; target 4,234/full 4,238 jobs and
  exact controls pass, with the same 93 inherited semantic-lint findings.
  This is before symmetric whitening, not yet the isometric frame.

- R4c Gram projection/normalization transfer CLOSED: the actual discarded
  prefix has `||Z||_HS^2 <= C log^3 X K^2/X`, uniformly tending to zero.
  Actual normalization gives `||N* N-I|| <= 4||Z||_HS^2`, and
  `||Gamma_projected-I|| <= 4||Gamma_raw-I|| + 8||Z||_HS^2`.
  No raw-Gram estimate is assumed in these inequalities. Five new
  standard-axiom roots; full 4,238-job build and boundary controls pass.
  Raw molecule overlaps were the next obligation, supplied below.

- R4c adjacent raw-molecule overlap CLOSED: uniformly on each fixed
  sub-square-root power range, actual small-prime-adjacent centres obey
  `mu_a mu_b |inner(f_b,f_a)| <= C eta_X log^3 X`.
  Full-star support cancellation and a produced relative root gap remove
  boundary mass from the residual pairing. Seven new standard-axiom roots;
  full 4,238-job build and exact controls pass. Non-adjacent overlap is
  closed by the later checkpoints below, including collective Gram smallness.

- R4c non-adjacent support/counting CLOSED: boundary cross terms vanish;
  full interiors overlap only on shared target stars. Their count is at
  most `2 (omega(a)+omega(b)) <= 4 log X/log 2`. With no shared target,
  the actual full molecules are exactly orthogonal. This includes kernel
  components and isolated up-targets. Nine new standard-axiom roots;
  full 4,238-job build and exact controls pass. The next checkpoint supplies
  the response norm and quantitative non-adjacent overlap.

- R4c full one-target response and non-adjacent overlap CLOSED: actual
  target coupling is a partial coordinate matching, of norm at most one.
  The produced gap gives `mu_a ||P_target interior_a|| <= 100`, retaining
  signed modes and the kernel. Consequently, for distinct non-adjacent
  centres, `mu_a mu_b |inner(f_a,f_b)| <= (40000/log 2) log X`.
  Five new standard-axiom roots; full 4,238-job build and exact controls
  pass, with no new lint findings. Both pointwise overlap cases are closed.

- R4c collective Gram smallness CLOSED: on every complete prefix K, the
  restricted neighbour count is K/a + omega(a). Energy-weighted Schur
  summation gives raw Gram error at most
  `C log^5(X) (eta_X K/X + K^2/X)`. It tends uniformly to zero for
  K <= X^theta, theta < 1/2. The actual projection/normalization transfer
  then proves the same smallness for the projected frame. Five new roots
  use standard axioms only; full 4,238-job build and finite controls pass.
  Semantic lint has the same 93 inherited findings; no new module or import.

- R4d symmetric whitening CLOSED: Q = V(V*V)^(-1/2) is the actual isometry,
  P Q = Q, and E = GQ-QD uses the original exact-molecule root diagonal.
  Both residual norms are at most 34 times their pre-whitening values.
  Thus HS squared <= C K log^5 X and operator squared <=
  C log^5 X (1+K^2/sqrt X), uniformly on K <= X^theta, theta < 1/2.
  The exact linear-isometry map consumed by R3 is also compiled. Full build
  4,238 jobs and seven exact controls pass; ten new audit roots have only
  standard axioms. Semantic lint retains 93 inherited findings, no additions.
  No new module/import or manuscript/pin change.

- R5 weighted input checkpoint (superseded by the R5 exit below): the actual phase-aligned full-star frame,
  including boundary and interior, satisfies
  norm((F_raw-U) sqrt(Lambda))^2 <= C log(X)^2 sqrt(K/log X).
  Projection contracts this bound, and invertible column normalization and
  whitening preserve the exact orthogonal complement. The finite consumer
  therefore bounds the complement by beta + tau^2 + eta without an inverse
  graph-map or a separate normalization-error estimate.
  Forest-prefix top, fixed-fraction gap and asymptotic absorptions remain
  OPEN; no checklist unit closes. Full build 4,238, nine new standard-axiom
  roots and six exact controls pass. Semantic lint retains exactly the same
  93 inherited findings; no new module/import or manuscript/pin change.

The four mini-goals are **align/reuse**, **comparison/frame**,
**spectral estimate**, and **public consequences/verification**, with two
R-tasks each. Each iteration reports the active task, closed tasks out of
eight, public roots out of four, and the exact proof delta. The live table
and exit tests are in the release contract. **MG1, MG2 and MG3 are complete**.
R1--R8 are CLOSED for the local D31 checklist. **MG4 is 2/2 COMPLETE**.
R5 supplies the actual A/G complement gap at mu_B/16 and both residual
absorptions on K=12288 B. Its saved final full build passed 4,238 jobs;
ten new audit roots use standard axioms, seven exact controls and style pass,
and semantic lint retains 93 inherited findings, none in the R5 section.
The 10 September continuation freshly matched the owner/audit hashes and
read this inherited evidence; it did not replay the R5 build.
R6 now proves the literal ordered mean-square and tail estimates in
`AlmostAllAssembly`: quadratic defect sum at most
`C X log^5 X + C B^3/log^2 X`, and, for every `t>0`, tail count at most
`C2 B log^5 X/t^2` above `C0 B/log X + C1 t sqrt(X/(B log X))`.
The complete-prefix index is the global arithmetic rank, including tied
prime-count values. Actual R2--R5 producers discharge all frame, residual
and complement premises; S2 transfers to the actual adjacency eigenvalue
at the same rank. The regular finite correction is retained.
Fresh targeted/full builds pass 4,237/4,239 jobs; fifteen new audit roots
use standard axioms only, and eight exact controls pass. Semantic lint has
the same 93 inherited findings, none in R6. Fresh style finds one inherited
Unicode issue at `AlmostAllSpectralBudget.lean:9340`, none in the new owner;
this is recorded separately from the saved R5 style-pass result.
All nine modules are reachable from the declared Challenge/Audit roots.
R7 closes Theorem 1.3 and Corollary 1.4 with the same constants and exponent
in the terminal count and global density limit; the initial segment remains
explicit. Internal Corollary 10.2 has sharp tail C X log^6(X)/B^2 and sharp
full-range density zero for 1/3 < theta < 1/2. Corollary 10.3 retains the coherent
operator term and proves every strict margin below
min(theta/2, (1-2 theta)/4), relative to sqrt(X)/log X.
Fresh targeted/full builds pass 4,237/4,239 jobs. Fifteen new internal roots
and both public almost-all roots use only standard axioms; fifteen exact
controls pass. Owner semantic lint retains the same 93 inherited findings;
Solution semantic lint passes. Style retains the same one inherited Unicode
issue. All four public statement types still match the frozen Challenge.
R8 closes the scoped D31 audit: fresh selected/full builds pass 4,238/4,239
jobs, and eight public/internal roots have only standard axioms throughout
their 71,747-constant union. Local Lean comparison passes 34 shared types and
26 definition values, covering all selected declarations. The complete
module/declaration/source-reference inventory, source-provenance account,
current metadata schema/Palomar contract and source editorial audit pass
their scoped checks. No proof source, paper or dependency changed.

Final submission readiness is **PARTIAL**. Public source access and current
Linux preflight/full replay, Comparator, NanoDa and the official rendered
Challenge remain pending. Before intake, verify that the selected immutable
commit equals clean checked-out HEAD and the pushed canonical branch.
Both sharp public proofs must also close before a combined four-root release.
The local comparison is not an official Comparator certificate. The
declaration inventory preserves existing shared/sharp support; it does not
claim that the combined tree is minimal for D31 alone.
Full evidence and limits are in `PORT_MANIFEST.md`. This development
checkpoint includes all R1--R8 sources, including the four owners that were
untracked during R8. The R8 record describes its earlier local audit state;
commit and push were subsequently authorized on 10 September 2026. Repository
visibility and Palomar submission state are separate from that authorization.

See [PALOMAR_BLOCKERS.md](PALOMAR_BLOCKERS.md) for exact project-local versus
external obligations. A successful internal paper proof is not formal closure.
All admitted obligations and relevant statement/provenance checks must be
discharged before a Palomar-ready claim.

## Build

```text
lake exe cache get
lake build
```

Preserve the pinned toolchain and dependencies. Rebuild the active owner and
its selected consumer after each proof batch, and report R-row closure or the
literal hypothesis reduction before module/line counts.
