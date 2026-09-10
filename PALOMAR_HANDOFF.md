# D31 handoff packet — final publication gate pending

**Preparation: 5/8 tasks verified for the current SSRN-linked source.**
Theorem 1.3 and Corollary 1.4 are the phase-1 selection. The author submitted
Paper II as [SSRN 7441718](https://papers.ssrn.com/abstract=7441718); its
confirmed dashboard status is `PRELIMINARY_UPLOAD`, not public approval.
Metadata/local checks pass. Refreshed private protected verification and
render (P6) and their final reconciliation (P7) are pending. Publish the
repository and verify anonymous access (P5) only after those pass.

The previous source `454743470f6aff2e7f7f8ac79a7a2a7279e60ada` has passed receipts below;
those are historical proof evidence, not exact-source certification of the
new metadata commit. No Palomar submission or registration has been performed.

| Field | Exact value |
|---|---|
| Repository | `shaikidris/prime-cover-power-band-spectra-palomar` |
| Source commit | `72288e1f32ba491a873e63647023b70d195f7139` |
| Project directory | leave blank / omit `project_path` (repository root) |
| Comparator configuration | `almost-all-comparator.json` |
| Challenge | `PrimeCoverPowerBandChallenge.lean` |
| Solution | `PrimeCoverPowerBandSolution.lean` |
| Selected results | `PrimeCoverPowerBand.palomar_almostAll_powerBand`; `PrimeCoverPowerBand.palomar_almostAll_subBlock` |
| Relationship | responsible author or maintainer |
| Existing entry ID | omitted for this first D31 entry |
| Sharp development | `11e71d0cec4f2e8de8e2542bb0b7a4888782607f` on `sharp-development` |

Use the immutable source commit above, not a later audit-branch commit.
Challenge SHA-256 is
`d2e99fd97cf315102f5d3918e4aa5ee403f2e4be41217dfec88f98d8cbc0ec96`;
configuration SHA-256 is
`4d5e30bf1d9895f8b9d433d6a694528a350d013385ddec4ce3a5ae975ecb2838`.

## Mathematical scope

The selected pair is Theorem 1.3 and Corollary 1.4: the global-PNT density-one
law for each fixed `0 < theta < 1/2`, with terminal exception control and a
strict power improvement over the positive-star squared-error baseline.
Constants are fixed before the limit; the full-range density retains the
initial segment. Neither endpoint is included.

Challenge also retains Theorem 1.1 and Corollary 1.2. Their sharp every-centre
`O(a/log X)` squared-error law still has `21/61 < theta < 1/2`; its current
mathematical route uses BHP and Brun--Titchmarsh. Their Lean Solution obligations
remain open on `sharp-development`. Challenge holes are deliberate statement
holes, not a proof-status claim. Theorem 10.1 and Corollaries 10.2--10.3 are
proved internal exports, outside this two-result Comparator selection.

## Historical exact verification evidence for 4547434

| Check | Result / receipt |
|---|---|
| Local full repository build | PASS, 4239 jobs; `readiness/p4-final-validation.json` |
| Local structural and trust audits | 2 theorem types, 16 definitions, 16,491 reached constants; eight standard-axiom closures; 15 controls; zero Solution admissions/unreachable modules |
| Private preflight | VERIFIED, prepared with no errors/warnings; `readiness/p6a-preflight-report.json` |
| Private protected full verification | PASS/complete; 4236-job selected build; NanoDa and Lean default kernels accept; `readiness/p6b-mechanical-report.json` and `readiness/p6b-mechanical-validation.json` |
| Private protected render | PASS; 18 artifact file hashes match; `readiness/p6c-render-report.json` |
| Reader inspection | Static module overview and 2/2 selected English docstrings inspected; `readiness/p6c-render-inspection.json` |
| Advisory review | Reconciled preparer assessment; `readiness/advisory-review.md` |
| Anonymous dependencies | All 15 exact manifest pins accessible; `readiness/p5-anonymous-dependencies.json` |
| Anonymous submitted source | Final P5 gate, pending publication |

[Protected verification job](https://github.com/shaikidris/prime-cover-power-band-spectra-palomar/actions/runs/34465598832/job/102833318097)
completed successfully. The
[render job](https://github.com/shaikidris/prime-cover-power-band-spectra-palomar/actions/runs/34465135183/job/102831818269)
also succeeded. Its original sibling verify job failed on the root-path intake
option before proof checking; verification was corrected and passed in the
second run. No source change or render restart was needed.

The private rehearsal used unchanged verifier/renderer
`ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`, Comparator
`575674928e239f5bc452aab72d1dd7b0f1326494`, NanoDa
`68d5ca9db226849b41a6fff59d796ff19d0a8840`, Landrun
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, and toolchain-matched exporter
`4e7915201d3f9f04470d9eae002fa695f7cdc589`. Lean is v4.32.0. Source transport
used a temporary repository-scoped Actions read token during trusted
preparation only; protected build/kernel and renderer execution received no
private source credential. This proves the recorded private replay, while P5
separately establishes anonymous source access. Rehearsal request identifiers
in reports are not Palomar entry or live submission identifiers.

The 93 inherited semantic-lint findings and one style finding remain
disclosed; successful Lean build logs also retain lint/info messages. Native
mathematical sources are privately identified. Novelty, a separate human proof
review, a nonblocking Palomar editorial outcome, and registration are not
established. The current renderer's
interactive view isolates selected declarations; its unchanged static HTML
and metadata retain the module overview. Literal dollar-delimited math in the
Corollary prose remains readable. No candidate prose regression was found.

## Manual intake boundary

After P5 passes, the user performs actual intake and the ownership step at the
[Palomar submission site](https://submit.palomar-registry.org/), using its
[current instructions](https://submit.palomar-registry.org/llms.txt). The
preparer's workflow is handoff-only in this environment: no intake API,
ownership tag/gist, bearer status URL, submission or registration action is
performed here. The source/configuration/relationship fields above are the
concrete packet to review at intake.
