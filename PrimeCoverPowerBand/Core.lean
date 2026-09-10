import PrimeStar.Basic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Shared statement implementation for Paper II

This module is the only shared owner of the objects appearing in both Palomar
entries. Its explicit vertex definition and derived instances match the
Mathlib-only Challenge surface. The type remains definitionally equal to
the pinned Paper I vertex type used by the proof owners.

Source provenance: the definitions are extracted from `Basic.lean`,
`PowerBands.lean`, `TargetEnergies.lean`, `HeadlineAssembly.lean`, and the
Solution surface of the Paper II proof laboratory.
-/

namespace PrimeCoverPowerBand

open Filter Topology
open scoped BigOperators Classical InnerProductSpace

noncomputable section

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
def arithmeticStarDegree (S : Finset ℕ) (c X : ℕ) : ℝ :=
  (allowedPrimeCount S (X / c) : ℝ) -
    (allowedPrimeCount S (Nat.sqrt X) : ℝ)

/-- Ratio of the up-star degree at `c*q` to the degree at `c`. -/
def actualUpStarRatio (S : Finset ℕ) (c X q : ℕ) : ℝ :=
  if c * q ≤ Nat.sqrt X then
    arithmeticStarDegree S (c * q) X / arithmeticStarDegree S c X
  else 0

/-- Local up-star correction. -/
def upStarCorrection (r : ℝ) : ℝ :=
  4 * r / (1 - r)

/-- Local down-star correction. -/
def downStarCorrection (s : ℝ) : ℝ :=
  (5 - s) / (1 - s)

/-- One-based rank of `a` among allowed vertices. -/
def arithmeticCenterRank {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℕ :=
  (Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a : ℕ)).card + 1

/-- Zero-based spectral index corresponding to the arithmetic rank. -/
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
def adjacency (S : Finset ℕ) (X : ℕ) :
    EuclideanSpace ℝ (Vertex S X) →ₗ[ℝ] EuclideanSpace ℝ (Vertex S X) :=
  Matrix.toEuclideanLin ((primeCoverGraph S X).adjMatrix ℝ)

/-- The adjacency operator is symmetric. -/
theorem adjacency_isSymmetric (S : Finset ℕ) (X : ℕ) :
    (adjacency S X).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))

/-- Ordered adjacency eigenvalue at arithmetic rank. -/
def lambdaAtArithmeticRank {S : Finset ℕ} {X : ℕ} (a : Vertex S X) : ℝ :=
  (adjacency_isSymmetric S X).eigenvalues rfl (arithmeticRankIndex a)

/-- The real power scale `X^θ`. -/
def powerScale (θ : ℝ) (X : ℕ) : ℝ :=
  (X : ℝ) ^ θ

/-- The terminal power band `X^θ / log X ≤ a ≤ X^θ`. -/
def InTerminalPowerBand (θ : ℝ) (X a : ℕ) : Prop :=
  0 < a ∧
    powerScale θ X / Real.log (X : ℝ) ≤ (a : ℝ) ∧
    (a : ℝ) ≤ powerScale θ X

/-- The full power range `a ≤ X^θ`. -/
def InPowerRange (θ : ℝ) (X a : ℕ) : Prop :=
  0 < a ∧ (a : ℝ) ≤ powerScale θ X

/-- The exact finite first-exit correction from Paper II. -/
def firstExitCorrection (S : Finset ℕ) (X : ℕ) (a : Vertex S X) : ℝ :=
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
def powerBandErrorScale (D X a : ℕ) : ℝ :=
  (a : ℝ) / Real.log (X : ℝ) +
    Real.log (X : ℝ) ^ D *
      Real.sqrt ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ)))

/-- Actual failures of the D31 estimate among all allowed centres at most
the power scale. Irregular correction denominators count as failures. -/
def powerBandBadCenters
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
def terminalPowerBandBadCenters
    (S : Finset ℕ) (θ C : ℝ) (D X : ℕ) : Finset (Vertex S X) :=
  (powerBandBadCenters S θ C D X).filter fun a ↦
    InTerminalPowerBand θ X (a : ℕ)

/-- Full-range exceptional count divided by the power scale, not by the
ambient graph size or the terminal-band cardinality. -/
def powerBandBadDensity
    (S : Finset ℕ) (θ C : ℝ) (D X : ℕ) : ℝ :=
  ((powerBandBadCenters S θ C D X).card : ℝ) / powerScale θ X

/-- Admissible power improvement over the squared-error block exponent. -/
def subBlockMargin (θ : ℝ) : ℝ :=
  min (θ / 2) (1 / 2 - θ)

/-- Actual failures of the density-one sub-block bound, including irregular
correction denominators. -/
def subBlockBadCenters
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
def subBlockBadDensity
    (S : Finset ℕ) (θ δ C : ℝ) (X : ℕ) : ℝ :=
  ((subBlockBadCenters S θ δ C X).card : ℝ) / powerScale θ X

end

end PrimeCoverPowerBand
