import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Prescribed power-band spectra of finite prime-cover graphs

This Mathlib-only Challenge surface states the two principal Paper II
theorem families and their immediate prime-counting and sub-block consequences.  The terminal
band and almost-all families are selected by separate Comparator
configurations, hence become separate Palomar entries.

The almost-all entry covers every fixed `0 < theta < 1/2`. Its squared-error
estimate improves the positive-star block baseline `O(sqrt(X)/log X)` on a
density-one set of prescribed arithmetic ranks. Theorem 1.3 also controls
terminal-band exception counts; its full-range density conclusion uses the
same error parameters and retains the initial segment. Corollary 1.4 states
the strict positive power improvement. The underlying comparison sorts values
on a complete prefix, including plateaus, and uses global PNT.

The sharp every-terminal-centre family retains `21/61 < theta < 1/2` and
error `O(a/log X)`. Its current proof uses BHP and Brun--Titchmarsh; its two
Solution obligations remain open in a separate entry surface. The weaker
every-centre operator corollary is an internal result, not a selection here.
All these errors concern squared eigenvalues. Neither endpoint is included.
-/

namespace PrimeCoverPowerBand

open Filter Topology
open scoped BigOperators Classical InnerProductSpace

/-- Positive integers at most `X` avoiding every prime in `S`. -/
def Vertex (S : Finset ℕ) (X : ℕ) :=
  {n : Fin (X + 1) // 0 < n.1 ∧ ∀ p ∈ S, ¬p ∣ n.1}
  deriving DecidableEq, Fintype

namespace Vertex

instance (S : Finset ℕ) (X : ℕ) : CoeOut (Vertex S X) ℕ :=
  ⟨fun n ↦ n.1.1⟩

theorem coe_pos {S : Finset ℕ} {X : ℕ} (n : Vertex S X) : 0 < (n : ℕ) :=
  n.2.1

end Vertex

/-- Two allowed vertices differ by multiplication by one allowed prime. -/
def PrimeCoverAdj {S : Finset ℕ} {X : ℕ} (m n : Vertex S X) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
    (((m : ℕ) * p = (n : ℕ)) ∨ ((n : ℕ) * p = (m : ℕ)))

theorem primeCoverAdj_symm {S : Finset ℕ} {X : ℕ} {m n : Vertex S X} :
    PrimeCoverAdj m n → PrimeCoverAdj n m := by
  rintro ⟨p, hp, hpS, h | h⟩
  · exact ⟨p, hp, hpS, Or.inr h⟩
  · exact ⟨p, hp, hpS, Or.inl h⟩

theorem not_primeCoverAdj_self {S : Finset ℕ} {X : ℕ} (m : Vertex S X) :
    ¬PrimeCoverAdj m m := by
  rintro ⟨p, hp, _hpS, h | h⟩
  all_goals
    have hmul : (m : ℕ) * p = (m : ℕ) * 1 := by simpa using h
    have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_left (Vertex.coe_pos m) hmul
    exact hp.ne_one hp1

/-- The finite prime-cover graph. -/
def primeCoverGraph (S : Finset ℕ) (X : ℕ) : SimpleGraph (Vertex S X) where
  Adj := PrimeCoverAdj
  symm := ⟨fun _ _ h ↦ primeCoverAdj_symm (S := S) (X := X) h⟩
  loopless := ⟨fun m ↦ not_primeCoverAdj_self (S := S) (X := X) m⟩

noncomputable instance palomarPrimeCoverDecidableRel (S : Finset ℕ) (X : ℕ) :
    DecidableRel (primeCoverGraph S X).Adj := Classical.decRel _

/-- `π_S(N)`, the number of primes at most `N` not deleted by `S`. -/
def allowedPrimeCount (S : Finset ℕ) (N : ℕ) : ℕ :=
  ((Nat.primesLE N).filter fun p ↦ p ∉ S).card

/-- The square-root-cutoff star degree at an arithmetic centre. -/
noncomputable def arithmeticStarDegree
    (S : Finset ℕ) (c X : ℕ) : ℝ :=
  (allowedPrimeCount S (X / c) : ℝ) -
    (allowedPrimeCount S (Nat.sqrt X) : ℝ)

/-- Ratio of the up-star degree at `c*q` to the degree at `c`.  The ratio is
zero once `c*q` lies beyond the square-root boundary. -/
noncomputable def actualUpStarRatio
    (S : Finset ℕ) (c X q : ℕ) : ℝ :=
  if c * q ≤ Nat.sqrt X then
    arithmeticStarDegree S (c * q) X / arithmeticStarDegree S c X
  else 0

/-- Local up-star correction. -/
noncomputable def upStarCorrection (r : ℝ) : ℝ :=
  4 * r / (1 - r)

/-- Local down-star correction. -/
noncomputable def downStarCorrection (s : ℝ) : ℝ :=
  (5 - s) / (1 - s)

/-- One-based rank `j_S(a)` of `a` among the allowed vertices. -/
def arithmeticCenterRank {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℕ :=
  (Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a : ℕ)).card + 1

/-- Zero-based spectral index corresponding to the one-based rank `j_S(a)`. -/
def arithmeticRankIndex {S : Finset ℕ} {X : ℕ} (a : Vertex S X) :
    Fin (Module.finrank ℝ (EuclideanSpace ℝ (Vertex S X))) := by
  let T := Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a : ℕ)
  refine ⟨T.card, ?_⟩
  have hproper : T ⊂ (Finset.univ : Finset (Vertex S X)) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, ?_⟩
    intro hEq
    have ha : a ∈ T := by simp [hEq]
    simp [T] at ha
  simpa using Finset.card_lt_card hproper

/-- Adjacency operator of the finite prime-cover graph. -/
noncomputable def adjacency (S : Finset ℕ) (X : ℕ) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ] EuclideanSpace ℝ (Vertex S X) :=
  Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)

/-- The adjacency operator is symmetric. -/
theorem adjacency_isSymmetric (S : Finset ℕ) (X : ℕ) :
    (adjacency S X).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))

/-- The ordered adjacency eigenvalue at arithmetic rank `j_S(a)`. -/
noncomputable def lambdaAtArithmeticRank
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℝ :=
  (adjacency_isSymmetric S X).eigenvalues rfl (arithmeticRankIndex a)

/-- The real power scale `X^θ`. -/
noncomputable def powerScale (θ : ℝ) (X : ℕ) : ℝ :=
  (X : ℝ) ^ θ

/-- The terminal power band `X^θ / log X ≤ a ≤ X^θ`. -/
def InTerminalPowerBand (θ : ℝ) (X a : ℕ) : Prop :=
  0 < a ∧
    powerScale θ X / Real.log (X : ℝ) ≤ (a : ℝ) ∧
    (a : ℝ) ≤ powerScale θ X

/-- The full power range `a ≤ X^θ` used by the almost-all theorem. -/
def InPowerRange (θ : ℝ) (X a : ℕ) : Prop :=
  0 < a ∧ (a : ℝ) ≤ powerScale θ X

/-- The exact finite first-exit correction `M_{S,a,X}` from the manuscript. -/
noncomputable def firstExitCorrection
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) : ℝ :=
  ∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
      upStarCorrection (actualUpStarRatio S (a : ℕ) X q) +
    ∑ q ∈ (a : ℕ).primeFactors,
      downStarCorrection
        (arithmeticStarDegree S ((a : ℕ) / q) X /
          arithmeticStarDegree S (a : ℕ) X)

/-- Every denominator in `firstExitCorrection` is nonzero. -/
def FirstExitCorrectionRegular
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) : Prop :=
  0 < arithmeticStarDegree S (a : ℕ) X ∧
    (∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
      actualUpStarRatio S (a : ℕ) X q ≠ 1) ∧
    (∀ q ∈ (a : ℕ).primeFactors,
      arithmeticStarDegree S ((a : ℕ) / q) X /
          arithmeticStarDegree S (a : ℕ) X ≠ 1)

/-- D31 squared-error scale: the deterministic term plus the logarithmic
multiple of the root-energy scale. -/
noncomputable def powerBandErrorScale (D X a : ℕ) : ℝ :=
  (a : ℝ) / Real.log (X : ℝ) +
    Real.log (X : ℝ) ^ D *
      Real.sqrt ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ)))

/-- Actual failures of the D31 estimate among all allowed centres at most
the power scale. Irregular correction denominators count as failures. -/
noncomputable def powerBandBadCenters
    (S : Finset ℕ) (θ C : ℝ) (D X : ℕ) : Finset (Vertex S X) :=
  Finset.univ.filter fun a ↦
    InPowerRange θ X (a : ℕ) ∧
      (¬FirstExitCorrectionRegular S X a ∨
        C * powerBandErrorScale D X (a : ℕ) <
          |(lambdaAtArithmeticRank a) ^ 2
            - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)
            - firstExitCorrection S X a|)

/-- D31 failures restricted to the terminal band. This set does not include
the omitted initial segment below the power scale divided by the logarithm. -/
noncomputable def terminalPowerBandBadCenters
    (S : Finset ℕ) (θ C : ℝ) (D X : ℕ) : Finset (Vertex S X) :=
  (powerBandBadCenters S θ C D X).filter fun a ↦
    InTerminalPowerBand θ X (a : ℕ)

/-- Full-range exceptional count divided by the power scale, not by the
ambient graph size or the terminal-band cardinality. -/
noncomputable def powerBandBadDensity
    (S : Finset ℕ) (θ C : ℝ) (D X : ℕ) : ℝ :=
  ((powerBandBadCenters S θ C D X).card : ℝ) / powerScale θ X

/-- Admissible power improvement over the squared-error block exponent. -/
noncomputable def subBlockMargin (θ : ℝ) : ℝ :=
  min (θ / 2) (1 / 2 - θ)

/-- Actual failures of the density-one sub-block bound, including irregular
correction denominators. -/
noncomputable def subBlockBadCenters
    (S : Finset ℕ) (θ δ C : ℝ) (X : ℕ) : Finset (Vertex S X) :=
  Finset.univ.filter fun a ↦
    InPowerRange θ X (a : ℕ) ∧
      (¬FirstExitCorrectionRegular S X a ∨
        C * (X : ℝ) ^ (1 / 2 - δ) <
          |(lambdaAtArithmeticRank a) ^ 2
            - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)
            - firstExitCorrection S X a|)

/-- Full-range exceptional count for the sub-block estimate, normalized by
the power scale. -/
noncomputable def subBlockBadDensity
    (S : Finset ℕ) (θ δ C : ℝ) (X : ℕ) : ℝ :=
  ((subBlockBadCenters S θ δ C X).card : ℝ) / powerScale θ X

/-- Manuscript Theorem 1.1: every prescribed rank in a terminal power band. -/
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

/-- Manuscript Corollary 1.2: the terminal-band formula after absorbing `M`. -/
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
  sorry

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
  sorry

end PrimeCoverPowerBand
