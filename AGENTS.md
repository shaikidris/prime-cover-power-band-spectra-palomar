# Paper II Palomar-first repository

- The current execution plan is the 9 September D31 rebase at the top of
  `PALOMAR_RELEASE_CONE.md`; later sections retain historical evidence only.
  D31 uses global PNT, not BHP/Guth--Maynard or local core capacity. Its
  Challenge synchronization and full-star reuse audit precede proof ports.
- This repository formalizes the prescribed-rank and almost-all power-band
  theorems of Paper II.  Preserve the exact Challenge quantifiers, endpoint
  inequalities, exceptional-set semantics, and error scales.
- Repository mode is `PALOMAR-FIRST`.  Reverse-plan from the four Challenge
  declarations; do not copy the manuscript section-by-section or use this tree
  for theorem discovery.
- Reuse Paper I only through its pinned public Git dependency.  Do not copy or
  modify the Paper I proof cone here.
- Treat `prime-cover-power-band-spectra-formalization` as read-only proof
  provenance. Port checked declarations, not whole files or umbrella imports.
- Do not formalize checked Paper II lemmas again. Transplant their existing
  proof bodies into the predeclared owner, minimize imports, and record source
  declaration provenance. Reserve new proof work for an obligation explicitly
  marked open in `PALOMAR_RELEASE_CONE.md`.
- `PALOMAR_RELEASE_CONE.md` now freezes eight possible proof owners, retiring
  `AlmostAllArithmetic` before creation. Do not create a ninth proof owner or
  any unplanned theorem family without explicit
  replanning.
- Keep zero unreachable local modules from the first substantive commit.
- Keep Palomar Challenge imports Mathlib-only.  Put all proofs and external
  analytic dependencies in the Solution or `PrimeCoverPowerBand/` modules.
- A kernel proof of `ShortIntervalPrimeInput -> T` is conditional.  Do not
  promote `T` until the short-interval input is itself present and audited.
- Project axioms, opaque assumption constants, `native_decide`, and untracked
  trusted computation are forbidden from public theorem cones.
- Challenge `sorry` declarations are deliberate statement holes.  Solution
  `sorry` declarations are development blockers and must be zero before any
  Palomar-ready claim.
- Do not commit, push, publish, submit, or register a completed batch without
  explicit user authorization for that action.
