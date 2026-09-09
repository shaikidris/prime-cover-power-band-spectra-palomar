# Prescribed eigenvalues in prime-cover power bands

This is the Palomar-first formalization repository for Paper II,
*Prescribed Eigenvalues in Power Bands of Finite Prime-Cover Graphs*.
Paper I is reused through its pinned public dependency. The broad historical
Paper II Lean repository supplies proof provenance, not umbrella imports.

This initial Git checkpoint versions the planning documents only. The
existing local Lean code is deliberately excluded from this checkpoint;
it is not a buildable or Palomar-ready release.

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

The new paper proof is NOT yet the compiled public theorem. Challenge,
Solution, Comparator and formalization.yaml still describe the previous D26'
surface. The next task R1 is their synchronized amendment; metadata alone
must not be updated to advertise the new result.

## Progress and reuse

- Existing code: seven local modules, four proof owners, 20,243 Lean lines
  including lakefile. Reuse it; no restart or new repository.
- Previous evidence: S1, S2 and local coherent producers have recorded builds
  and axiom checks in [PORT_MANIFEST.md](PORT_MANIFEST.md).
- Current public Solution holes: **4**; completed public declarations: **0/4**.
- Revised D31 checklist: **0/8 validated**. This measures outstanding checks
  against the new consumer, not the fraction of reusable code.
- Historical **15/28** belongs to the old contract and is not current progress.
- No Lean code or build changed in the planning revision.

The four mini-goals are **align/reuse**, **comparison/frame**,
**spectral estimate**, and **public consequences/verification**, with two
R-tasks each. Each iteration reports the active task, closed tasks out of
eight, public roots out of four, and the exact proof delta. The live table
and exit tests are in the release contract; the next task is **R1**.

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
