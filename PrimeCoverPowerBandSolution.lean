import PrimeCoverPowerBand.AlmostAllAssembly

/-!
# Solution surface for prescribed power-band spectra

The two declarations below match the frozen D31 Challenge statements and
assemble their proofs from the checked owners. The open sharp terminal-band
entry is preserved on the `sharp-development` branch of this repository.
-/

namespace PrimeCoverPowerBand

open Filter Topology

/-- Manuscript Theorem 1.3 (D31). For each fixed positive terminal exception
exponent, there are a logarithmic error exponent and positive constants such
that the terminal failure count is at most a constant times the power scale
divided by that power of the logarithm. With the SAME error parameters, the
full-range failure count is little-o of the power scale. The global limit
allows the omitted initial segment; it does not inherit the terminal rate. -/
theorem palomar_almostAll_powerBand
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθlow : 0 < θ) (hθhigh : θ < 1 / 2) :
    ∀ R : ℝ, 0 < R →
      ∃ D : ℕ, ∃ C Cexc : ℝ, 0 < C ∧ 0 < Cexc ∧
        (∀ᶠ X : ℕ in atTop,
          ((terminalPowerBandBadCenters S θ C D X).card : ℝ) ≤
            Cexc * powerScale θ X / Real.log (X : ℝ) ^ R) ∧
        Tendsto (powerBandBadDensity S θ C D) atTop (𝓝 0) := by
  intro R hR
  obtain ⟨D, C, Cexc, hC, hCexc, hterminal⟩ :=
    eventually_terminalPowerBand_badCenters_le S hS hθlow hθhigh R
  exact ⟨D, C, Cexc, hC, hCexc, hterminal,
    tendsto_powerBandBadDensity_zero_of_terminal_bound S D hθlow hR hterminal⟩

/-- Manuscript Corollary 1.4. For every fixed power band below the square-root
boundary and every positive improvement smaller than the displayed margin,
the actual failures of squared error at most a constant times
$X^{1/2-δ}$ have cardinality $o(X^θ)$. This improves the positive-star block
baseline on a density-one set, not at every centre. -/
theorem palomar_almostAll_subBlock
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθlow : 0 < θ) (hθhigh : θ < 1 / 2) :
    0 < subBlockMargin θ ∧
      ∀ δ : ℝ, 0 < δ → δ < subBlockMargin θ →
        ∃ C : ℝ, 0 < C ∧
          Tendsto (subBlockBadDensity S θ δ C) atTop (𝓝 0) := by
  constructor
  · exact lt_min (by linarith) (by linarith)
  · intro δ hδ hmargin
    have hθpos : 0 < θ := by
      have h := (lt_min_iff.mp hmargin).1
      linarith
    exact almostAll_subBlock_of_ordered_tail S hS hθpos hθhigh hmargin

end PrimeCoverPowerBand
