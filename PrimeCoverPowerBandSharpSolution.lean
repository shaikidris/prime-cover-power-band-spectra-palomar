import PrimeCoverPowerBand.Core

/-!
# Open sharp terminal-band Solution surface

Theorem 1.1 and Corollary 1.2 retain their frozen sharp statements and two
explicit proof obligations. Their BHP-dependent route is tracked separately
from the admission-free D31 Solution in `PALOMAR_RELEASE_CONE.md`.
-/

namespace PrimeCoverPowerBand

open Filter Topology

/-- Every prescribed rank in a terminal power band. -/
theorem palomar_terminalBand_prescribedRanks
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθlow : (21 : ℝ) / 61 < θ) (hθhigh : θ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
        InTerminalPowerBand θ X (a : ℕ) →
          FirstExitCorrectionRegular S X a ∧
            |(lambdaAtArithmeticRank a) ^ 2
              - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)
              - firstExitCorrection S X a| ≤
                C * (a : ℝ) / Real.log (X : ℝ) := by
  sorry

/-- Terminal-band prime-counting consequence. -/
theorem palomar_terminalBand_primeCounting
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθlow : (21 : ℝ) / 61 < θ) (hθhigh : θ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
        InTerminalPowerBand θ X (a : ℕ) →
          |(lambdaAtArithmeticRank a) ^ 2
            - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)| ≤
              C * (a : ℝ) / Real.log (X : ℝ) := by
  sorry

end PrimeCoverPowerBand
