# Palomar submission analysis — 10 September 2026

**Decision: D31 is proved locally, but this checkpoint is not submission-ready.**
Submit the two D31 results first after repairing statement compatibility and
completing the release checks below. The sharp every-centre route remains a
separate mathematical obligation.

## Frozen source and completed push

This analysis assesses the complete R1--R8 development checkpoint
`0e23075e18eb2569f1b95217ceee955de7554345`, committed and pushed to `main` through
the configured personal SSH remote. A separate SSH `ls-remote` returned that
same commit, and the worktree was clean after the push. This report and its
ledger updates are a subsequent documentation-only batch; they change no Lean
source, dependency, theorem selection, or manuscript.

The source tree contains all nine local Lean modules and six proof owners.
The R8 selected/full Lake invocations passed 4,238/4,239 jobs using unchanged
cached artifacts where available. A fresh audit of eight public/internal D31
roots found only `propext`, `Classical.choice`, and `Quot.sound` in their
71,747-constant transitive union. Both public D31 proofs are complete. The two
sharp public proofs still contain `sorry`.

R8's **8/8 local checklist** remains the record of that bounded audit. It is
not a protected Comparator result, independent-kernel replay, or registry
acceptance. The new structural-identity finding below supersedes any inference
that its local definitional-equality comparison established Comparator
compatibility.

## First entry to prepare

Use project `.` and the existing `almost-all-comparator.json`:

| Role | Selection |
|---|---|
| Challenge | `PrimeCoverPowerBandChallenge` |
| Solution currently configured | `PrimeCoverPowerBandSolution` |
| Theorem 1.3 | `PrimeCoverPowerBand.palomar_almostAll_powerBand` |
| Corollary 1.4 | `PrimeCoverPowerBand.palomar_almostAll_subBlock` |

This is the density-one route for every fixed `0 < theta < 1/2`, with the
literal ordered-rank failure predicates, correction regularity, terminal
exception bounds, and full-range density limit. Its proof uses global PNT;
BHP and the unresolved sharp terminal theorem are not proof inputs.

## Confirmed statement-identity blocker

The pinned Comparator requires structural equality of reachable declarations
that are not configured theorem or definition targets. For selected targets
it permits the intended proof/definition replacement but checks their types
and traverses the constants in those types. This follows directly from
[`Compare.lean` at the pinned revision](https://github.com/leanprover/comparator/blob/575674928e239f5bc452aab72d1dd7b0f1326494/Comparator/Compare.lean).

The existing D31 selection reaches this concrete mismatch:

```text
powerBandBadCenters (selected definition)
  -> its type uses PrimeCoverPowerBand.Vertex
  -> Vertex is not a selected definition
```

In `PrimeCoverPowerBandChallenge.lean:24`, `Vertex` is the explicit subtype of
positive integers at most `X` avoiding the primes in `S`, with locally derived
instances. In `PrimeCoverPowerBand/Core.lean:27`, it is
`abbrev Vertex := PrimeStar.Vertex`. The two are definitionally equal in Lean,
but their declaration values are structurally different.

A fresh diagnostic imported the compiled Challenge and Solution into separate
Lean environments and used the same `ConstantInfo` equality instances as the
pinned Comparator. It exited 0 and recorded:

| Declaration | Type structurally equal | Whole constant structurally equal |
|---|---|---|
| `palomar_almostAll_powerBand` | yes | no; different selected proof bodies are expected |
| `palomar_almostAll_subBlock` | yes | no; different selected proof bodies are expected |
| `Vertex` | yes | **no; required equality fails** |
| `arithmeticRankIndex` | yes | no |
| `adjacency` | yes | no |
| `adjacency_isSymmetric` | **no** | no |
| `lambdaAtArithmeticRank` | yes | no |

The symmetry theorem's types also expose different generated instance names:
the Challenge uses `PrimeCoverPowerBand.instFintypeVertex`, while the Solution
uses `PrimeStar.instFintypeVertex`. Fixing the first abbreviation alone is not
evidence that the remaining dependency comparison will pass.

This is a confirmed compiled-declaration incompatibility with the pinned
comparison rule. It is **not** a run of the official protected Comparator and
does not invalidate the D31 Lean proofs. R8's namespace-isolated check used
Lean definitional equality and therefore could not detect this stricter
packaging requirement.

Repair the concrete Challenge/Core definitions and generated instances while
preserving the stated mathematical objects and Mathlib-only Challenge imports.
Keep Paper I as the pinned proof dependency. Do not weaken the Challenge or
widen definition holes merely to suppress equality failures. Rebuild the
affected owners and verify the complete comparison after the repair.

## Other release gates

| Gate | Current evidence | Required completion |
|---|---|---|
| Admission-free D31 Solution surface | The shared Solution still contains two sharp `sorry` declarations. Neither is in the audited D31 proof closure. | Separate the D31 Solution surface from the open sharp entry, preserving the latter's explicit development status. |
| Public source access | Anonymous GitHub repository API returned 404; authorized SSH access and push succeeded. | Make an explicitly authorized public source arrangement and verify anonymous access to the selected immutable source and proof dependencies. Visibility was not changed by this task. |
| Exact protected verification | Metadata/schema, local builds, source/provenance and axiom checks pass. Current Linux preflight, full Comparator/NanoDa replay and official Challenge rendering have not run. | Run the supported pinned verification against the repaired immutable source and retain receipts. This macOS host has no usable Linux runner; no project CI currently supplies one. |
| Editorial account | Selected theorem docstrings and source formulas exist; the README is dominated by development logs. | Add a concise mathematical account of the improvement, relevant audience, source relationship and limitations before editorial handoff. |

The admission-free Solution gate needs a precise distinction. The upstream
Comparator exports selected roots and checks their dependencies; an unrelated
sharp `sorry` does not automatically contaminate D31. Its
[`Main.lean`](https://github.com/leanprover/comparator/blob/575674928e239f5bc452aab72d1dd7b0f1326494/Main.lean)
and [`Axioms.lean`](https://github.com/leanprover/comparator/blob/575674928e239f5bc452aab72d1dd7b0f1326494/Comparator/Axioms.lean)
establish that scope. Nevertheless, this repository's `AGENTS.md` requires
Solution holes to be zero before a Palomar-ready claim, and the local snapshot
audit flags both holes in the configured shared Solution. Isolating the D31
surface addresses that release constraint without requiring the sharp proof.

Public GitHub source and public proof dependencies are current intake
requirements; source visibility is therefore a separate gate from a successful
SSH push. See the pinned
[submission specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/docs/specification.md).

## Editorial assessment

The plausible audience is researchers in spectral graph theory and analytic
number theory. The candidate studies a natural divisibility-cover graph and
controls eigenvalues at prescribed moving ranks through polynomially growing
bands. The sub-block consequence gives a positive power improvement on a
density-one set. These are reasons to prepare an entry, not predictions of
acceptance.

The public account should compare this result with Paper I's fixed-centre
regime, state the baseline and exact improvement, and explain which claims are
formalized here. It should identify the native manuscript and proof record with
stable source references; the README's sibling filesystem link alone is not
usable by a reader of this repository on GitHub. Keep any inaccessible-source
limitation explicit. This audit did not establish novelty or complete a
literature search, so novelty remains unknown.

Current policy asks for research interest and an assessable informal account;
proof size is not evidence of significance. It allows accurately labelled
additional project results in the abstract and does not require every
mathematical source to be archivable. See the pinned
[contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/CONTRIBUTING.md).

## Audit identities and evidence

| Authority | Exact revision |
|---|---|
| PalomarPolicy | `e9c8c238f5695b10f75db7175648a1d0195352c1` |
| PalomarSubmission | `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763` |
| formalization.yaml schema | `99c678e569c7c4c0772db297c5ddd5e4c9b6322e` |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| lean4export, exact `v4.32.0` tag | `4e7915201d3f9f04470d9eae002fa695f7cdc589` |

Lean remains `leanprover/lean4:v4.32.0`. Dependency pins and the full nine-module
source inventory match `.lake/d31-r8/baseline.json`. The native manuscript and
D31 proof record were independently matched to mathematical-source commit
`df32cafb021c0ed90f14f045858525882d50ab9e`; this identifies mathematical
provenance, not this repository's Lean source commit.

Local evidence is under `.lake/palomar-submission-analysis-2026-09-10/`:
`push-receipt.json`, `committed-snapshot-audit.json`,
`analysis-authorities.json`, `native-source-provenance.json`,
`StructuralComparison.lean`, `structural-comparison.json`,
`structural-comparison.log`, and `strict-identity-finding.json`.
The diagnostic command was:

```sh
lake env lean --run .lake/palomar-submission-analysis-2026-09-10/StructuralComparison.lean
```

These ignored local files are retained audit evidence, not publicly shipped
verification receipts. The immutable source, exact discrepancy and pinned
comparison algorithm above make the finding independently inspectable. No
official replay, Palomar submission, acceptance or registry-state change is
claimed.
