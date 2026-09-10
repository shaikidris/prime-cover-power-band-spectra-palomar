import Lake

open Lake DSL

package primeCoverPowerBandPalomar where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/- Paper I is the only project-specific proof dependency. -/
require primeStarFormalization from git
  "https://github.com/shaikidris/prime-star-spectra-formalization.git" @
    "59176e4ce57e7d6578cafd1de0029fed6fc13ccf"

require PrimeNumberTheoremAnd from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @
    "7715064f690d0689f30889846f4e2c5e7ec0c47e"

-- Keep the root Mathlib pin last so its transitive revision wins.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "3dffaf2f18b47d11948f6390838ea6f2ae662aaf"

@[default_target]
lean_lib PrimeCoverPowerBandPalomar where
  globs := #[
    .submodules `PrimeCoverPowerBand,
    .one `PrimeCoverPowerBandChallenge,
    .one `PrimeCoverPowerBandSolution,
    .one `PrimeCoverPowerBandSubmissionAudit
  ]
