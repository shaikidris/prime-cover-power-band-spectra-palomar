# Source provenance

| Role | Repository or source | Commit |
|---|---|---|
| Authoritative substantive Lean development | this repository, `shaikidris/prime-cover-power-band-spectra-palomar` | the exact immutable commit selected at intake; require clean HEAD and the pushed canonical branch to match it |
| Historical planning checkpoint; not the substantive proof source | this repository | `e887e0b6fc2d46eb7cec3921dd7898c9f1335d25` |
| Historical Paper II Lean laboratory | `shaikidris/prime-cover-power-band-spectra-formalization` | parent `a6f8efa91346a6401ba9191d1b12f8552727e380`; dirty batch not yet checkpointed |
| Paper II mathematical source (native paper, not Lean evidence) | `shaikidris/prime-orthant-geometry` | `df32cafb021c0ed90f14f045858525882d50ab9e` |
| Paper I Lean dependency | `shaikidris/prime-star-spectra-formalization` | `59176e4ce57e7d6578cafd1de0029fed6fc13ccf` |
| Prime-number dependency | `AlexKontorovich/PrimeNumberTheoremAnd` | `7715064f690d0689f30889846f4e2c5e7ec0c47e` |
| Mathlib | `leanprover-community/mathlib4` | `3dffaf2f18b47d11948f6390838ea6f2ae662aaf` |
| R8 verification policy/tool source; not a proof dependency | `PalomarRegistry/PalomarSubmission` | `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763` |

This repository contains the substantive D31 implementation and the checked
ports. It is not a thin wrapper around the historical laboratory, and that
laboratory is not a Lake dependency. The authoritative submission source will
be the exact immutable commit selected at intake; no current self-referential
commit is embedded in `formalization.yaml`.

The historical working batch is not an immutable source revision. Its port
records in `PORT_MANIFEST.md` identify declarations and source-file hashes;
those are file-level provenance, not evidence of a public immutable upstream
checkout. Do not port unchecked declarations from it. This development
checkpoint contains all nine R8-audited Lean modules, including the four
owners that were untracked at the R8 audit. Its complete Git tree is the
reproducible source inventory; local audit outputs remain in `.lake/d31-r8/`.
The user authorized commit and push on 10 September 2026. That checkpoint
does not establish public source availability or independent Palomar replay.
The D31 manuscript is `draft/prescribed-eigenvalues-in-prime-cover-power-bands.md`
at SHA-256 `b145e0a4ed2078fca969ed127d00c73d8758a76b559971988501693c1b60cfa3`.
The paper commit above fixes native mathematical provenance only. Paper I,
PNTA and Mathlib revisions identify dependencies, not this project's source
commit. The D31 paper is source-derived mathematics; it is not an original
proof invented by the formalization agent. The current Mathlib pin passed the
canonical-branch ancestry check against PalomarSubmission
`ef2fa1eadcb246c2346ddba39b52eaa53d4bb763` on 10 September 2026.
