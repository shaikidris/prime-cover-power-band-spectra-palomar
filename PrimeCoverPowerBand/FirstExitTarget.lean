import PrimeCoverPowerBand.Core
import PrimeStar.ActualFiniteCorrection
import PrimeStar.AdjacencyEvolution
import PrimeStar.BipartiteSymmetry
import PrimeStar.CanonicalFirstExitBlocks
import PrimeStar.FiniteRemainderAssembly
import PrimeStar.FixedCenterConstantLayer
import PrimeStar.FixedCenterCorrectionBridge
import PrimeStar.FixedCenterIsolation
import PrimeStar.IsolatedMode
import PrimeStar.LogarithmicWindowFeshbachRemainder
import PrimeStar.OrderedEigenvaluePerturbation
import PrimeStar.PrimeLogIncrement
import PrimeStar.SmallPrimeRow
import PrimeStar.SqrtCutoff
import PrimeStar.TunedPrimeSumBounds
import PrimeStar.WeightedSchur
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Fin

/-!
# Exact first-exit target producer

This owner contains the declaration-level extraction needed for the checked
Paper II theorem
`eventually_powerRange_exactPrincipalMoleculeRoot_targetDefect_le`.
It deliberately collapses the historical exploratory file layout while
preserving the checked proof bodies. Paper I results are reused through the
pinned dependency.

The exact source declarations and working-snapshot hashes are recorded in
`PORT_MANIFEST.md`. The only boundary adaptation is the `eps` named-argument
spelling used by the pinned Paper I API.
-/
namespace PrimeCoverPowerBand

open Filter Finset MeasureTheory Topology
open Matrix
open scoped BigOperators Classical InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι]

private theorem symmetricEigenvalues_cast
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) (j : Fin n) :
    hT.eigenvalues rfl (Fin.cast hn.symm j) = hT.eigenvalues hn j := by
  subst n
  rfl


/- Source slice: PowerBands.lean -/

theorem tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero
    (D : ℝ) {lower upper : ℝ} (hlu : lower < upper) :
    Filter.Tendsto
      (fun X : ℕ ↦
        Real.log (X : ℝ) ^ D * (X : ℝ) ^ lower /
          (X : ℝ) ^ upper)
      Filter.atTop (nhds 0) := by
  have hgap : 0 < upper - lower := sub_pos.mpr hlu
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop D hgap).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  refine hnat.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with X hX
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  simp only [Function.comp_apply]
  rw [Real.rpow_sub hx]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hx lower),
    ne_of_gt (Real.rpow_pos_of_pos hx upper)]

/-- Every fixed power range strictly below the square-root boundary is
negligible relative to `sqrt X`. -/

theorem tendsto_powerScale_div_sqrt_zero
    {theta : ℝ} (htheta : theta < (1 : ℝ) / 2) :
    Filter.Tendsto (fun X : ℕ ↦ powerScale theta X / Real.sqrt (X : ℝ))
      Filter.atTop (nhds 0) := by
  have h := tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero
    (0 : ℝ) htheta
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with X hX
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  rw [powerScale, Real.sqrt_eq_rpow]
  simp

/-- The scalar factor left after buffered exterior Schur elimination tends to
zero on every fixed sub-square-root power band.  The first summand pays for
the smallest terminal centre `X^theta / log X`; the second pays for the
largest centre `X^theta`. -/


/- Source slice: TargetEnergies.lean -/

theorem firstExitCorrection_eq_paperOne
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) :
    firstExitCorrection S X a =
      PrimeStar.fixedCenterActualCorrection S (a : ℕ) X := by
  rfl

/-- The exact labelled squared-energy target `π_S(X/a) + M_{S,a,X}`. -/

noncomputable def targetEnergy
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) : ℝ :=
  (PrimeStar.allowedPrimeCount S (X / (a : ℕ)) : ℝ) +
    firstExitCorrection S X a

/-- The absolute difference between a squared spectral value and its target. -/

noncomputable def targetDefect
    (S : Finset ℕ) (X : ℕ) (a : Vertex S X) (lam : ℝ) : ℝ :=
  |lam ^ 2 - targetEnergy S X a|

@[simp]

theorem targetDefect_eq (S : Finset ℕ) (X : ℕ)
    (a : Vertex S X) (lam : ℝ) :
    targetDefect S X a lam =
      |lam ^ 2 - (PrimeStar.allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
        firstExitCorrection S X a| := by
  rw [targetDefect, targetEnergy]
  congr 1
  ring


/- Source slice: FirstExitMolecules.lean -/

abbrev squareRootCutoff (X : ℕ) : ℕ := Nat.sqrt X

local instance firstExitLargePrimeDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X (Nat.sqrt X)).Adj :=
  Classical.decRel _

/-- Ambient real Euclidean space of the finite prime-cover graph. -/

abbrev MoleculeAmbient (S : Finset ℕ) (X : ℕ) :=
  EuclideanSpace ℝ (PrimeStar.Vertex S X)

/-- The positive forest energy attached to a centre `a`. -/

def moleculeStarEnergy (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : ℝ :=
  Real.sqrt (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ)

/-- The normalized positive star mode at the centre `a`. -/

def moleculePositiveStarMode (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : MoleculeAmbient S X :=
  PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a 1

/-- The exact normalized first-exit source generated by the positive star
mode.  This is the `h_a \oplus k_a` source used to build the raw molecule. -/

theorem moleculeStarEnergy_nonneg
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    0 ≤ moleculeStarEnergy S X a :=
  Real.sqrt_nonneg _

/-- Squaring the forest energy recovers the exact large-prime star degree. -/

theorem moleculeStarEnergy_sq
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    moleculeStarEnergy S X a ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) := by
  exact Real.sq_sqrt (Nat.cast_nonneg _)

/-- A nonempty positive star mode has unit norm. -/

theorem norm_moleculePositiveStarMode
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ‖moleculePositiveStarMode S X a‖ = 1 :=
  PrimeStar.norm_largePrimeNormalizedStarMode hd

/-- The positive mode is an exact eigenvector of the large-prime forest at
the literal square-root cutoff. -/


/- Source slice: PrincipalMolecule.lean -/

abbrev FirstExitCoordinate (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :=
  {v : PrimeStar.Vertex S X //
    v ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a}

local instance principalMoleculeLargePrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X (Nat.sqrt X)).Adj :=
  Classical.decRel _

/-- Restriction of the large-prime adjacency to the canonical first-exit
coordinates. -/

def moleculeInteriorMatrix (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    Matrix (FirstExitCoordinate S X a) (FirstExitCoordinate S X a) ℝ :=
  fun v w ↦
    (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1

/-- Restriction of the exact first-exit source to its canonical coordinates. -/

theorem moleculeInteriorMatrix_isHermitian
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    (moleculeInteriorMatrix S X a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro v w
  exact ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix
    (R := ℝ)).apply v.1 w.1

/-- The one-hub bordered molecule is Hermitian. -/

noncomputable def borderedContinuationRank
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : ℝ) (C : Matrix ι ι ℝ) (hC : C.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i : Fin (Fintype.card ι) ↦
    mu < hC.eigenvalues₀ i).card

/-- The continuation rank fits in the bordered space: there is always one
additional hub coordinate beyond all interior eigenvalues above `mu`. -/


/- Source slice: ExactPrincipalMolecule.lean -/

local instance exactPrincipalMoleculePrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance exactPrincipalMoleculeLargePrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

local instance exactPrincipalMoleculeSmallPrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

/-- Literal support `B_a ∪ U_a` of the exact Paper II molecule. -/

def exactPrincipalMoleculeSupport (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : Finset (PrimeStar.Vertex S X) :=
  PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a ∪
    PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a

/-- Coordinate type of the exact Paper II molecule. -/

abbrev ExactPrincipalMoleculeCoordinate (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :=
  {v : PrimeStar.Vertex S X // v ∈ exactPrincipalMoleculeSupport S X a}

/-- The original boundary star is disjoint from the first-exit compression. -/

theorem exactPrincipalMolecule_support_disjoint
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    Disjoint
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
      (PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a) := by
  simpa [squareRootCutoff] using
    (PrimeStar.disjoint_firstExitCompressionSupport_largePrimeStarSupport
      (S := S) (X := X) (Y := Nat.sqrt X) (c := a)
      (PrimeStar.sqrtCutoff_condition X) ha).symm

/-- The exact molecule has strictly more coordinates than its first-exit
interior: the original centre supplies a boundary coordinate outside `U_a`. -/

theorem card_firstExitCoordinate_lt_exactPrincipalMoleculeCoordinate
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    Fintype.card (FirstExitCoordinate S X a) <
      Fintype.card (ExactPrincipalMoleculeCoordinate S X a) := by
  classical
  let B := PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a
  let U := PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
  have hdisj : Disjoint B U := by
    simpa [B, U] using exactPrincipalMolecule_support_disjoint S X a ha
  have haB : a ∈ B := by
    simp [B, PrimeStar.mem_largePrimeStarSupport]
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨a, haB⟩
  have hcard : U.card < (B ∪ U).card := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  simpa [FirstExitCoordinate, exactPrincipalMoleculeSupport, B, U] using hcard

/-- The exact molecule support is always nonempty because it contains its
centre. -/

theorem exactPrincipalMoleculeCoordinate_card_pos
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    0 < Fintype.card (ExactPrincipalMoleculeCoordinate S X a) := by
  classical
  rw [Fintype.card_pos_iff]
  exact ⟨⟨a, by
    apply Finset.mem_union_left
    simp [PrimeStar.mem_largePrimeStarSupport]⟩⟩

/-- Predicate selecting the two boundary--first-exit off-diagonal blocks. -/

def exactPrincipalMoleculeCrossPair (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X)
    (v w : ExactPrincipalMoleculeCoordinate S X a) : Prop :=
  (v.1 ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a ∧
      w.1 ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a) ∨
    (v.1 ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a ∧
      w.1 ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)

local instance exactPrincipalMoleculeCrossPairDecidable
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    DecidableRel (exactPrincipalMoleculeCrossPair S X a) :=
  Classical.decRel _

/-- Exact Paper II molecule on `B_a ∪ U_a`: the large-prime forest on both
blocks plus only the small-prime boundary--target exits.  Small-prime edges
inside `U_a` are absent by the first-exit arithmetic. -/

def exactPrincipalMoleculeMatrix (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    Matrix (ExactPrincipalMoleculeCoordinate S X a)
      (ExactPrincipalMoleculeCoordinate S X a) ℝ :=
  fun v w ↦
    (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 +
      if exactPrincipalMoleculeCrossPair S X a v w then
        (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1
      else 0

/-- The exact principal molecule is Hermitian. -/

theorem exactPrincipalMoleculeMatrix_isHermitian
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    (exactPrincipalMoleculeMatrix S X a).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro v w
  have hL := ((PrimeStar.largePrimeGraph S X
    (squareRootCutoff X)).isHermitian_adjMatrix (R := ℝ)).apply v.1 w.1
  have hH := ((PrimeStar.smallPrimeGraph S X
    (squareRootCutoff X)).isHermitian_adjMatrix (R := ℝ)).apply v.1 w.1
  have hL' :
      (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ w.1 v.1 =
        (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 := by
    simpa only [star_trivial] using hL
  have hH' :
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ w.1 v.1 =
        (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 := by
    simpa only [star_trivial] using hH
  have hcross : exactPrincipalMoleculeCrossPair S X a v w ↔
      exactPrincipalMoleculeCrossPair S X a w v := by
    simp only [exactPrincipalMoleculeCrossPair]
    tauto
  simp only [exactPrincipalMoleculeMatrix, star_trivial]
  rw [hL']
  by_cases hvw : exactPrincipalMoleculeCrossPair S X a v w
  · rw [if_pos (hcross.mp hvw), if_pos hvw, hH']
  · have hwv : ¬ exactPrincipalMoleculeCrossPair S X a w v :=
      fun h ↦ hvw (hcross.mpr h)
    rw [if_neg hwv, if_neg hvw]

/-- Ordered continuation index of the exact molecule.  Adding the original
boundary star adds only one positive unperturbed level, namely the distinguished
level `mu_a`; the levels strictly above it are still counted by the first-exit
interior continuation rank. -/

noncomputable def exactPrincipalMoleculeIndex
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    Fin (Fintype.card (ExactPrincipalMoleculeCoordinate S X a)) :=
  ⟨borderedContinuationRank (moleculeStarEnergy S X a)
      (moleculeInteriorMatrix S X a)
      (moleculeInteriorMatrix_isHermitian S X a) %
        Fintype.card (ExactPrincipalMoleculeCoordinate S X a),
    Nat.mod_lt _ (exactPrincipalMoleculeCoordinate_card_pos S X a)⟩

/-- On the active square-root range the total definition above does not wrap:
its value is the literal continuation rank. -/

theorem exactPrincipalMoleculeIndex_val
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    (exactPrincipalMoleculeIndex S X a).1 =
      borderedContinuationRank (moleculeStarEnergy S X a)
        (moleculeInteriorMatrix S X a)
        (moleculeInteriorMatrix_isHermitian S X a) := by
  change borderedContinuationRank (moleculeStarEnergy S X a)
      (moleculeInteriorMatrix S X a)
      (moleculeInteriorMatrix_isHermitian S X a) %
        Fintype.card (ExactPrincipalMoleculeCoordinate S X a) =
    borderedContinuationRank (moleculeStarEnergy S X a)
      (moleculeInteriorMatrix S X a)
      (moleculeInteriorMatrix_isHermitian S X a)
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt
    (by
      unfold borderedContinuationRank
      exact (Finset.card_filter_le _ _).trans_eq (by simp))
    (card_firstExitCoordinate_lt_exactPrincipalMoleculeCoordinate S X a ha)

private abbrev exactPrincipalMoleculeBoundaryCoordinate (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :=
  {v : PrimeStar.Vertex S X //
    v ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a}

private def exactPrincipalMoleculeBoundaryMatrix (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    Matrix (exactPrincipalMoleculeBoundaryCoordinate S X a)
      (exactPrincipalMoleculeBoundaryCoordinate S X a) ℝ :=
  fun v w ↦
    (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1

/-- Large-prime part of the exact molecule, before its boundary--first-exit
coupling is added. -/

def exactPrincipalMoleculeLargePrimeMatrix (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    Matrix (ExactPrincipalMoleculeCoordinate S X a)
      (ExactPrincipalMoleculeCoordinate S X a) ℝ :=
  fun v w ↦
    (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1

private theorem exactPrincipalMoleculeBoundaryMatrix_isHermitian
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    (exactPrincipalMoleculeBoundaryMatrix S X a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro v w
  exact ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix
    (R := ℝ)).apply v.1 w.1

theorem exactPrincipalMoleculeLargePrimeMatrix_isHermitian
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    (exactPrincipalMoleculeLargePrimeMatrix S X a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro v w
  exact ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix
    (R := ℝ)).apply v.1 w.1

private def exactPrincipalMoleculeBoundaryPositiveVector (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : exactPrincipalMoleculeBoundaryCoordinate S X a → ℝ :=
  fun v ↦ PrimeStar.largePrimeSignedStarVector S X (squareRootCutoff X) a 1 v.1

private theorem exactPrincipalMoleculeBoundaryMatrix_mulVec_positive
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    (exactPrincipalMoleculeBoundaryMatrix S X a).mulVec
        (exactPrincipalMoleculeBoundaryPositiveVector S X a) =
      moleculeStarEnergy S X a • exactPrincipalMoleculeBoundaryPositiveVector S X a := by
  funext v
  simp only [Matrix.mulVec_apply_eq_sum, exactPrincipalMoleculeBoundaryMatrix,
    exactPrincipalMoleculeBoundaryPositiveVector, Pi.smul_apply, smul_eq_mul]
  have hamb := congrFun
    (PrimeStar.largePrime_adjMatrix_mulVec_signedStarVector
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
      (PrimeStar.sqrtCutoff_condition X) ha
      (by norm_num : (1 : ℝ) ^ 2 = 1)) v.1
  let f := fun w : PrimeStar.Vertex S X ↦
    (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ
        v.1 w *
      PrimeStar.largePrimeSignedStarVector S X
        (squareRootCutoff X) a 1 w
  have hsum :
      ∑ w : exactPrincipalMoleculeBoundaryCoordinate S X a, f w.1 =
        ∑ w : PrimeStar.Vertex S X, f w := by
    calc
      (∑ w : exactPrincipalMoleculeBoundaryCoordinate S X a, f w.1) =
          ∑ w ∈ PrimeStar.largePrimeStarSupport S X
            (squareRootCutoff X) a, f w := by
              symm
              exact Finset.sum_subtype _ (fun _ ↦ Iff.rfl) f
      _ = ∑ w ∈ (Finset.univ : Finset (PrimeStar.Vertex S X)), f w := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _hw hnot
        simp [f, PrimeStar.largePrimeSignedStarVector_eq_zero_of_not_mem hnot]
      _ = ∑ w : PrimeStar.Vertex S X, f w := by simp
  change (∑ w : exactPrincipalMoleculeBoundaryCoordinate S X a, f w.1) = _
  rw [hsum]
  simpa [f, moleculeStarEnergy, Matrix.mulVec_apply_eq_sum] using hamb

private theorem exactPrincipalMoleculeBoundaryMatrix_l2_opNorm_le_starEnergy
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ‖exactPrincipalMoleculeBoundaryMatrix S X a‖ ≤ moleculeStarEnergy S X a := by
  apply PrimeStar.weightedSchur_l2_opNorm_le
    (exactPrincipalMoleculeBoundaryMatrix S X a)
    (exactPrincipalMoleculeBoundaryPositiveVector S X a)
    (moleculeStarEnergy S X a)
  · exact moleculeStarEnergy_nonneg S X a
  · intro v w
    simp only [exactPrincipalMoleculeBoundaryMatrix, SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  · intro v w
    have h := ((PrimeStar.largePrimeGraph S X
      (squareRootCutoff X)).isHermitian_adjMatrix (R := ℝ)).apply v.1 w.1
    simpa [exactPrincipalMoleculeBoundaryMatrix] using h.symm
  · intro v
    have hv := PrimeStar.mem_largePrimeStarSupport.mp v.property
    rcases hv with hv | hv
    · rw [exactPrincipalMoleculeBoundaryPositiveVector, hv,
        PrimeStar.largePrimeSignedStarVector_center]
      exact Real.sqrt_pos.2 (by exact_mod_cast hd)
    · rw [exactPrincipalMoleculeBoundaryPositiveVector,
        PrimeStar.largePrimeSignedStarVector_leaf
          (PrimeStar.mem_largePrimeLeaves.mpr hv)]
      norm_num
  · intro v
    have h := congrFun (exactPrincipalMoleculeBoundaryMatrix_mulVec_positive S X a ha) v
    simpa [Matrix.mulVec_apply_eq_sum] using h.le

private theorem exactPrincipalMoleculeBoundaryMatrix_eigenvalue_le_starEnergy
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (i : exactPrincipalMoleculeBoundaryCoordinate S X a) :
    (exactPrincipalMoleculeBoundaryMatrix_isHermitian S X a).eigenvalues i ≤
      moleculeStarEnergy S X a := by
  let B := exactPrincipalMoleculeBoundaryMatrix S X a
  let hB : B.IsHermitian := exactPrincipalMoleculeBoundaryMatrix_isHermitian S X a
  let x := hB.eigenvectorBasis i
  have heig : B *ᵥ ⇑x = (hB.eigenvalues i) • ⇑x := by
    simpa [B, hB, x] using hB.mulVec_eigenvectorBasis i
  have hxnorm : ‖x‖ = 1 := hB.eigenvectorBasis.orthonormal.norm_eq_one i
  have hop := B.l2_opNorm_mulVec x
  rw [heig] at hop
  have habs : |hB.eigenvalues i| ≤ ‖B‖ := by
    simpa [map_smul, hxnorm, norm_smul, Real.norm_eq_abs] using hop
  calc
    hB.eigenvalues i ≤ |hB.eigenvalues i| := le_abs_self _
    _ ≤ ‖B‖ := habs
    _ ≤ moleculeStarEnergy S X a := by
      simpa [B] using exactPrincipalMoleculeBoundaryMatrix_l2_opNorm_le_starEnergy S X a ha hd

private theorem exactPrincipalMoleculeBoundaryMatrix_eigenvalues₀_le_starEnergy
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (i : Fin (Fintype.card (exactPrincipalMoleculeBoundaryCoordinate S X a))) :
    (exactPrincipalMoleculeBoundaryMatrix_isHermitian S X a).eigenvalues₀ i ≤
      moleculeStarEnergy S X a := by
  let e : Fin (Fintype.card (exactPrincipalMoleculeBoundaryCoordinate S X a)) ≃
      exactPrincipalMoleculeBoundaryCoordinate S X a :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := exactPrincipalMoleculeBoundaryMatrix_eigenvalue_le_starEnergy S X a ha hd (e i)
  simpa [Matrix.IsHermitian.eigenvalues, e] using h

private theorem exactPrincipalMoleculeBoundaryMatrix_hasEigenvalue_starEnergy
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (exactPrincipalMoleculeBoundaryMatrix S X a))
      (moleculeStarEnergy S X a) := by
  let B := exactPrincipalMoleculeBoundaryMatrix S X a
  let T := Matrix.toEuclideanLin B
  let x : EuclideanSpace ℝ (exactPrincipalMoleculeBoundaryCoordinate S X a) :=
    (EuclideanSpace.equiv _ _).symm (exactPrincipalMoleculeBoundaryPositiveVector S X a)
  have hxeq : T x = moleculeStarEnergy S X a • x := by
    change (EuclideanSpace.equiv _ _).symm
        (B *ᵥ exactPrincipalMoleculeBoundaryPositiveVector S X a) =
      moleculeStarEnergy S X a •
        (EuclideanSpace.equiv _ _).symm
          (exactPrincipalMoleculeBoundaryPositiveVector S X a)
    rw [exactPrincipalMoleculeBoundaryMatrix_mulVec_positive S X a ha]
    exact map_smul _ _ _
  have hxne : x ≠ 0 := by
    intro hx
    let c : exactPrincipalMoleculeBoundaryCoordinate S X a :=
      ⟨a, by simp [PrimeStar.largePrimeStarSupport]⟩
    have hzero : x c = 0 := by rw [hx]; rfl
    have hpos : 0 < x c := by
      change 0 < PrimeStar.largePrimeSignedStarVector S X
        (squareRootCutoff X) a 1 a
      rw [PrimeStar.largePrimeSignedStarVector_center]
      exact Real.sqrt_pos.2 (by exact_mod_cast hd)
    linarith
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hxeq, hxne⟩)

private theorem exactPrincipalMolecule_card_eigenvaluesAbove_eq_card_rootsAbove
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (mu : ℝ) :
    (Finset.univ.filter fun i : Fin (Fintype.card n) ↦
      mu < hA.eigenvalues₀ i).card =
      (A.charpoly.roots.filter fun x ↦ mu < x).card := by
  have h := congrArg
    (fun s : Multiset ℝ ↦ (s.filter fun x ↦ mu < x).card)
    hA.roots_charpoly_eq_eigenvalues₀
  have hofReal (x : ℝ) : (RCLike.ofReal x : ℝ) = x := rfl
  simpa only [Finset.card, Finset.filter_val, Multiset.filter_map,
    Multiset.card_map, Function.comp_apply, hofReal] using h.symm

private theorem exactPrincipalMolecule_reindex_largePrime_eq_fromBlocks
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    Matrix.reindex
      (Equiv.Finset.union
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
        (PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a)
        (exactPrincipalMolecule_support_disjoint S X a ha)).symm
      (Equiv.Finset.union
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
        (PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a)
        (exactPrincipalMolecule_support_disjoint S X a ha)).symm
      (exactPrincipalMoleculeLargePrimeMatrix S X a) =
    Matrix.fromBlocks (exactPrincipalMoleculeBoundaryMatrix S X a) 0 0
      (moleculeInteriorMatrix S X a) := by
  ext v w
  rcases v with v | v <;> rcases w with w | w
  · rfl

  · change _ = 0
    simp only [Matrix.reindex_apply]
    have hdisj := exactPrincipalMolecule_support_disjoint S X a ha
    have hnot : ¬ PrimeStar.LargePrimeAdj S (squareRootCutoff X) v.1 w.1 := by
      intro hadj
      have hclosed := PrimeStar.largePrimeStarSupport_closed
        (PrimeStar.sqrtCutoff_condition X) ha v.2 hadj
      exact (Finset.disjoint_left.mp hdisj) hclosed w.2
    simp [exactPrincipalMoleculeLargePrimeMatrix, SimpleGraph.adjMatrix, hnot]
  · change _ = 0
    simp only [Matrix.reindex_apply]
    have hdisj := exactPrincipalMolecule_support_disjoint S X a ha
    have hnot : ¬ PrimeStar.LargePrimeAdj S (squareRootCutoff X) w.1 v.1 := by
      intro hadj
      have hclosed := PrimeStar.largePrimeStarSupport_closed
        (PrimeStar.sqrtCutoff_condition X) ha w.2 hadj
      exact (Finset.disjoint_left.mp hdisj) hclosed v.2
    have hnot' : ¬ PrimeStar.LargePrimeAdj S (squareRootCutoff X) v.1 w.1 :=
      fun hadj ↦ hnot (PrimeStar.largePrimeAdj_symm hadj)
    simp [exactPrincipalMoleculeLargePrimeMatrix, SimpleGraph.adjMatrix, hnot']
  · rfl

private theorem exactPrincipalMoleculeLargePrimeMatrix_charpoly
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    (exactPrincipalMoleculeLargePrimeMatrix S X a).charpoly =
      (exactPrincipalMoleculeBoundaryMatrix S X a).charpoly *
        (moleculeInteriorMatrix S X a).charpoly := by
  let e := Equiv.Finset.union
    (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
    (PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a)
    (exactPrincipalMolecule_support_disjoint S X a ha)
  calc
    (exactPrincipalMoleculeLargePrimeMatrix S X a).charpoly =
        (Matrix.reindex e.symm e.symm
          (exactPrincipalMoleculeLargePrimeMatrix S X a)).charpoly := by
            symm
            exact Matrix.charpoly_reindex e.symm _
    _ = (Matrix.fromBlocks (exactPrincipalMoleculeBoundaryMatrix S X a) 0 0
          (moleculeInteriorMatrix S X a)).charpoly := by
            rw [exactPrincipalMolecule_reindex_largePrime_eq_fromBlocks S X a ha]
    _ = (exactPrincipalMoleculeBoundaryMatrix S X a).charpoly *
          (moleculeInteriorMatrix S X a).charpoly := by simp

private theorem exactPrincipalMoleculeLargePrimeMatrix_card_above_eq_interior
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    (Finset.univ.filter fun i : Fin (Fintype.card
        (ExactPrincipalMoleculeCoordinate S X a)) ↦
      moleculeStarEnergy S X a <
        (exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a).eigenvalues₀ i).card =
      borderedContinuationRank (moleculeStarEnergy S X a)
        (moleculeInteriorMatrix S X a)
        (moleculeInteriorMatrix_isHermitian S X a) := by
  let mu := moleculeStarEnergy S X a
  let L := exactPrincipalMoleculeLargePrimeMatrix S X a
  let B := exactPrincipalMoleculeBoundaryMatrix S X a
  let C := moleculeInteriorMatrix S X a
  let hL : L.IsHermitian := exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a
  let hB : B.IsHermitian := exactPrincipalMoleculeBoundaryMatrix_isHermitian S X a
  let hC : C.IsHermitian := moleculeInteriorMatrix_isHermitian S X a
  have hBcount :
      (Finset.univ.filter fun i : Fin (Fintype.card
          (exactPrincipalMoleculeBoundaryCoordinate S X a)) ↦
        mu < hB.eigenvalues₀ i).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _hi
    exact not_lt_of_ge
      (exactPrincipalMoleculeBoundaryMatrix_eigenvalues₀_le_starEnergy S X a ha hd i)
  have hBroots : (B.charpoly.roots.filter fun x ↦ mu < x).card = 0 := by
    rw [← exactPrincipalMolecule_card_eigenvaluesAbove_eq_card_rootsAbove B hB mu]
    exact hBcount
  have hprod : B.charpoly * C.charpoly ≠ 0 :=
    mul_ne_zero (Matrix.charpoly_monic B).ne_zero
      (Matrix.charpoly_monic C).ne_zero
  calc
    (Finset.univ.filter fun i : Fin (Fintype.card
        (ExactPrincipalMoleculeCoordinate S X a)) ↦
      moleculeStarEnergy S X a <
        (exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a).eigenvalues₀ i).card =
        (L.charpoly.roots.filter fun x ↦ mu < x).card := by
          exact exactPrincipalMolecule_card_eigenvaluesAbove_eq_card_rootsAbove L hL mu
    _ = ((B.charpoly * C.charpoly).roots.filter fun x ↦ mu < x).card := by
      rw [exactPrincipalMoleculeLargePrimeMatrix_charpoly S X a ha]
    _ = ((B.charpoly.roots + C.charpoly.roots).filter fun x ↦ mu < x).card := by
      rw [Polynomial.roots_mul hprod]
    _ = (B.charpoly.roots.filter fun x ↦ mu < x).card +
        (C.charpoly.roots.filter fun x ↦ mu < x).card := by simp
    _ = (C.charpoly.roots.filter fun x ↦ mu < x).card := by rw [hBroots, zero_add]
    _ = borderedContinuationRank (moleculeStarEnergy S X a)
        (moleculeInteriorMatrix S X a)
        (moleculeInteriorMatrix_isHermitian S X a) := by
      symm
      exact exactPrincipalMolecule_card_eigenvaluesAbove_eq_card_rootsAbove C hC mu

private theorem exactPrincipalMoleculeLargePrimeMatrix_exists_eigenvalues₀_eq_starEnergy
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ∃ i : Fin (Fintype.card (ExactPrincipalMoleculeCoordinate S X a)),
      (exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a).eigenvalues₀ i =
        moleculeStarEnergy S X a := by
  let mu := moleculeStarEnergy S X a
  let L := exactPrincipalMoleculeLargePrimeMatrix S X a
  let B := exactPrincipalMoleculeBoundaryMatrix S X a
  let C := moleculeInteriorMatrix S X a
  let hL : L.IsHermitian := exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a
  let hB : B.IsHermitian := exactPrincipalMoleculeBoundaryMatrix_isHermitian S X a
  let TB := Matrix.toEuclideanLin B
  let hTB : TB.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  obtain ⟨i : Fin (Fintype.card (exactPrincipalMoleculeBoundaryCoordinate S X a)), hi⟩ :=
    hTB.exists_eigenvalues_eq finrank_euclideanSpace
      (exactPrincipalMoleculeBoundaryMatrix_hasEigenvalue_starEnergy S X a ha hd)
  have hi₀ : hB.eigenvalues₀ i = mu := by
    simpa [Matrix.IsHermitian.eigenvalues₀, hB, TB, hTB] using hi
  have hofReal (x : ℝ) : (RCLike.ofReal x : ℝ) = x := rfl
  have hrootB : mu ∈ B.charpoly.roots := by
    rw [hB.roots_charpoly_eq_eigenvalues₀]
    refine Multiset.mem_map.mpr ⟨i, ?_, ?_⟩
    · exact Finset.mem_univ i
    · simpa only [Function.comp_apply, hofReal] using hi₀
  have hprod : B.charpoly * C.charpoly ≠ 0 :=
    mul_ne_zero (Matrix.charpoly_monic B).ne_zero
      (Matrix.charpoly_monic C).ne_zero
  have hrootL : mu ∈ L.charpoly.roots := by
    rw [exactPrincipalMoleculeLargePrimeMatrix_charpoly S X a ha,
      Polynomial.roots_mul hprod]
    exact Multiset.mem_add.mpr (Or.inl hrootB)
  rw [hL.roots_charpoly_eq_eigenvalues₀] at hrootL
  obtain ⟨i, _hiuniv, hi⟩ := Multiset.mem_map.mp hrootL
  refine ⟨i, ?_⟩
  simpa only [Function.comp_apply, hofReal] using hi

private theorem exactPrincipalMolecule_antitone_value_at_strictAboveRank
    {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (mu : ℝ)
    (hmu : ∃ k, f k = mu) (i : Fin n)
    (hi : i.1 = (Finset.univ.filter fun j ↦ mu < f j).card) :
    f i = mu := by
  obtain ⟨k, hk⟩ := hmu
  have hsubset :
      (Finset.univ.filter fun j : Fin n ↦ mu < f j) ⊆ Finset.Iio k := by
    intro j hj
    have hjgt : mu < f j := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_Iio]
    by_contra hnot
    have hkj : k ≤ j := le_of_not_gt hnot
    have hle : f j ≤ f k := hf hkj
    rw [hk] at hle
    exact (not_lt_of_ge hle) hjgt
  have hcard := Finset.card_le_card hsubset
  have hirank : i ≤ k := by
    rw [Fin.le_iff_val_le_val, hi]
    simpa using hcard
  have hmu_le : mu ≤ f i := by
    rw [← hk]
    exact hf hirank
  have hnot_gt : ¬ mu < f i := by
    intro hgt
    let p : Fin n → Prop := fun j ↦ mu < f j
    have hp : ∀ x y, y ≤ x → p x → p y := by
      intro x y hyx hx
      exact hx.trans_le (hf hyx)
    have hilow : i.1 < (Finset.univ.filter p).card :=
      (Fin.lt_card_filter_univ_iff_apply_of_imp p hp).2 hgt
    rw [hi] at hilow
    exact (Nat.lt_irrefl _ hilow)
  exact le_antisymm (le_of_not_gt hnot_gt) hmu_le

/-- At the continuation rank, the unperturbed exact molecule has precisely
the positive boundary-star energy. -/

theorem exactPrincipalMoleculeLargePrime_eigenvalueAtIndex_eq_starEnergy
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    (exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a).eigenvalues₀
        (exactPrincipalMoleculeIndex S X a) = moleculeStarEnergy S X a := by
  let hL := exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a
  apply exactPrincipalMolecule_antitone_value_at_strictAboveRank
    hL.eigenvalues₀ hL.eigenvalues₀_antitone (moleculeStarEnergy S X a)
  · exact exactPrincipalMoleculeLargePrimeMatrix_exists_eigenvalues₀_eq_starEnergy S X a ha hd
  · exact (exactPrincipalMoleculeIndex_val S X a ha).trans
      (exactPrincipalMoleculeLargePrimeMatrix_card_above_eq_interior S X a ha hd).symm

/-- Eigenvalue of the exact principal molecule at the arithmetic continuation
rank. -/

noncomputable def exactPrincipalMoleculeRoot
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) : ℝ :=
  (exactPrincipalMoleculeMatrix_isHermitian S X a).eigenvalues₀
    (exactPrincipalMoleculeIndex S X a)

theorem exactPrincipalMoleculeRoot_sub_starEnergy_abs_le_of_cross_bound
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (eta : ℝ)
    (hcross : ∀ x : EuclideanSpace ℝ (ExactPrincipalMoleculeCoordinate S X a),
      ‖(Matrix.toEuclideanLin (exactPrincipalMoleculeMatrix S X a) -
          Matrix.toEuclideanLin (exactPrincipalMoleculeLargePrimeMatrix S X a)) x‖ ≤
        eta * ‖x‖) :
    |exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a| ≤ eta := by
  let A := Matrix.toEuclideanLin (exactPrincipalMoleculeMatrix S X a)
  let L := Matrix.toEuclideanLin (exactPrincipalMoleculeLargePrimeMatrix S X a)
  let H := A - L
  let hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (exactPrincipalMoleculeMatrix_isHermitian S X a)
  let hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (exactPrincipalMoleculeLargePrimeMatrix_isHermitian S X a)
  let hH : H.IsSymmetric := hA.sub hL
  let i : Fin (Module.finrank ℝ
      (EuclideanSpace ℝ (ExactPrincipalMoleculeCoordinate S X a))) :=
    Fin.cast finrank_euclideanSpace.symm (exactPrincipalMoleculeIndex S X a)
  have hsum : L + H = A := by
    dsimp [H]
    abel
  have hweyl := PrimeStar.abs_orderedEigenvalue_add_sub_le
    L H hL hH i eta (by simpa [A, L, H] using hcross)
  have heigenvalues :
      (hL.add hH).eigenvalues rfl = hA.eigenvalues rfl := by
    apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      (hL.add hH) rfl hA rfl).2
    rw [hsum]
  have hfull :
      (hL.add hH).eigenvalues rfl i = exactPrincipalMoleculeRoot S X a := by
    rw [heigenvalues]
    rw [show i = Fin.cast finrank_euclideanSpace.symm
        (exactPrincipalMoleculeIndex S X a) by rfl]
    rw [symmetricEigenvalues_cast A hA finrank_euclideanSpace]
    rfl
  have hlarge :
      hL.eigenvalues rfl i = moleculeStarEnergy S X a := by
    rw [show i = Fin.cast finrank_euclideanSpace.symm
        (exactPrincipalMoleculeIndex S X a) by rfl]
    rw [symmetricEigenvalues_cast L hL finrank_euclideanSpace]
    exact exactPrincipalMoleculeLargePrime_eigenvalueAtIndex_eq_starEnergy
      S X a ha hd
  rw [hfull, hlarge] at hweyl
  exact hweyl

/-- Unit eigenvector of the exact principal molecule at the continuation
rank. -/

noncomputable def exactPrincipalMoleculeEigenvector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    EuclideanSpace ℝ (ExactPrincipalMoleculeCoordinate S X a) :=
  let hM := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (exactPrincipalMoleculeMatrix_isHermitian S X a)
  hM.eigenvectorBasis finrank_euclideanSpace
    (exactPrincipalMoleculeIndex S X a)

/-- The exact continuation vector is normalized. -/

theorem norm_exactPrincipalMoleculeEigenvector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    ‖exactPrincipalMoleculeEigenvector S X a‖ = 1 := by
  let hM := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (exactPrincipalMoleculeMatrix_isHermitian S X a)
  exact (hM.eigenvectorBasis finrank_euclideanSpace).orthonormal.norm_eq_one
    (exactPrincipalMoleculeIndex S X a)

/-- Exact eigenvector equation for the full `B_a ∪ U_a` molecule. -/

theorem exactPrincipalMoleculeMatrix_apply_eigenvector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    Matrix.toEuclideanLin (exactPrincipalMoleculeMatrix S X a)
        (exactPrincipalMoleculeEigenvector S X a) =
      exactPrincipalMoleculeRoot S X a •
        exactPrincipalMoleculeEigenvector S X a := by
  let hM := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (exactPrincipalMoleculeMatrix_isHermitian S X a)
  simpa [exactPrincipalMoleculeEigenvector, exactPrincipalMoleculeRoot,
    Matrix.IsHermitian.eigenvalues₀, hM] using
    (hM.apply_eigenvectorBasis finrank_euclideanSpace
      (exactPrincipalMoleculeIndex S X a))


/- Source slice: MoleculeEmbedding.lean -/

local instance moleculeEmbeddingPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Matrix whose hub column is the normalized positive star mode and whose
other columns are the literal first-exit coordinate vectors. -/

def primeCoverAdjacencyOperator (S : Finset ℕ) (X : ℕ) :
    MoleculeAmbient S X →ₗ[ℝ] MoleculeAmbient S X :=
  Matrix.toEuclideanLin ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ)

/-- Exact ambient residual of a principal molecule.  CollisionBudget will
bound the squared norms of these vectors over a growing centre family. -/


/- Source slice: ExactMoleculeEmbedding.lean -/

local instance exactMoleculeEmbeddingPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Coordinate inclusion of the exact molecule into the full graph. -/

def exactMoleculeEmbeddingMatrix (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    Matrix (PrimeStar.Vertex S X)
      (ExactPrincipalMoleculeCoordinate S X a) ℝ :=
  fun v w ↦ if v = w.1 then 1 else 0

/-- Linear coordinate embedding of the exact molecule. -/

def exactMoleculeEmbeddingOperator (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    EuclideanSpace ℝ (ExactPrincipalMoleculeCoordinate S X a) →ₗ[ℝ]
      MoleculeAmbient S X :=
  Matrix.toEuclideanLin (exactMoleculeEmbeddingMatrix S X a)

/-- The exact coordinate embedding has orthonormal columns. -/

theorem exactMoleculeEmbeddingMatrix_transpose_mul_self
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    (exactMoleculeEmbeddingMatrix S X a).transpose *
        exactMoleculeEmbeddingMatrix S X a = 1 := by
  classical
  ext v w
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    exactMoleculeEmbeddingMatrix, Matrix.one_apply]
  by_cases hvw : v = w
  · subst w
    simp
  · simp [hvw, Ne.symm hvw]

/-- Adjoint followed by the exact coordinate embedding is the identity. -/

theorem exactMoleculeEmbeddingOperator_adjoint_comp_self
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    (exactMoleculeEmbeddingOperator S X a).adjoint.comp
        (exactMoleculeEmbeddingOperator S X a) = LinearMap.id := by
  change
    (Matrix.toEuclideanLin (exactMoleculeEmbeddingMatrix S X a)).adjoint.comp
        (Matrix.toEuclideanLin (exactMoleculeEmbeddingMatrix S X a)) =
      LinearMap.id
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [← Matrix.toLpLin_mul_same]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,
    exactMoleculeEmbeddingMatrix_transpose_mul_self]
  exact Matrix.toLpLin_one (R := ℝ) (p := (2 : ENNReal))

/-- The exact coordinate embedding preserves Euclidean norm. -/

theorem norm_exactMoleculeEmbeddingOperator
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (x : EuclideanSpace ℝ (ExactPrincipalMoleculeCoordinate S X a)) :
    ‖exactMoleculeEmbeddingOperator S X a x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  calc
    inner ℝ (exactMoleculeEmbeddingOperator S X a x)
        (exactMoleculeEmbeddingOperator S X a x) =
        inner ℝ x ((exactMoleculeEmbeddingOperator S X a).adjoint
          (exactMoleculeEmbeddingOperator S X a x)) := by
            exact (LinearMap.adjoint_inner_right
              (exactMoleculeEmbeddingOperator S X a) x
              (exactMoleculeEmbeddingOperator S X a x)).symm
    _ = inner ℝ x x := by
      rw [← LinearMap.comp_apply,
        exactMoleculeEmbeddingOperator_adjoint_comp_self]
      rfl

/-- Ambient unit vector of the exact principal molecule. -/

def exactPrincipalMoleculeAmbientVector (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : MoleculeAmbient S X :=
  exactMoleculeEmbeddingOperator S X a
    (exactPrincipalMoleculeEigenvector S X a)

/-- The embedded exact molecule vector is normalized. -/

theorem norm_exactPrincipalMoleculeAmbientVector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    ‖exactPrincipalMoleculeAmbientVector S X a‖ = 1 := by
  rw [exactPrincipalMoleculeAmbientVector,
    norm_exactMoleculeEmbeddingOperator,
    norm_exactPrincipalMoleculeEigenvector]

/-- Exact matrix defect `A E - E M` of the full principal molecule. -/

def exactMoleculeIntertwiningResidualMatrix (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    Matrix (PrimeStar.Vertex S X)
      (ExactPrincipalMoleculeCoordinate S X a) ℝ :=
  ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ) *
      exactMoleculeEmbeddingMatrix S X a -
    exactMoleculeEmbeddingMatrix S X a *
      exactPrincipalMoleculeMatrix S X a

/-- Operator form of the exact full-molecule intertwining defect. -/

def exactMoleculeIntertwiningResidualOperator (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    EuclideanSpace ℝ (ExactPrincipalMoleculeCoordinate S X a) →ₗ[ℝ]
      MoleculeAmbient S X :=
  primeCoverAdjacencyOperator S X ∘ₗ exactMoleculeEmbeddingOperator S X a -
    exactMoleculeEmbeddingOperator S X a ∘ₗ
      Matrix.toEuclideanLin (exactPrincipalMoleculeMatrix S X a)

/-- The operator defect is represented by the literal matrix defect. -/

theorem exactMoleculeIntertwiningResidualOperator_eq_matrix
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    exactMoleculeIntertwiningResidualOperator S X a =
      Matrix.toEuclideanLin (exactMoleculeIntertwiningResidualMatrix S X a) := by
  simp [exactMoleculeIntertwiningResidualOperator,
    exactMoleculeIntertwiningResidualMatrix, primeCoverAdjacencyOperator,
    exactMoleculeEmbeddingOperator, Matrix.toLpLin_mul_same]

/-- Full-graph residual of the embedded exact continuation eigenvector. -/

def exactPrincipalMoleculeResidual (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : MoleculeAmbient S X :=
  primeCoverAdjacencyOperator S X
      (exactPrincipalMoleculeAmbientVector S X a) -
    exactPrincipalMoleculeRoot S X a •
      exactPrincipalMoleculeAmbientVector S X a

/-- The full-graph residual is the exact intertwining defect applied to the
exact molecule eigenvector. -/

theorem exactPrincipalMoleculeResidual_eq_intertwiningOperator
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    exactPrincipalMoleculeResidual S X a =
      exactMoleculeIntertwiningResidualOperator S X a
        (exactPrincipalMoleculeEigenvector S X a) := by
  rw [exactPrincipalMoleculeResidual]
  simp only [exactMoleculeIntertwiningResidualOperator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  rw [exactPrincipalMoleculeMatrix_apply_eigenvector]
  rw [map_smul]
  rfl

/-- The full-graph residual is the exact matrix defect applied to the
exact molecule eigenvector. -/

theorem exactPrincipalMoleculeResidual_eq_intertwiningMatrix
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    exactPrincipalMoleculeResidual S X a =
      Matrix.toEuclideanLin (exactMoleculeIntertwiningResidualMatrix S X a)
        (exactPrincipalMoleculeEigenvector S X a) := by
  rw [exactPrincipalMoleculeResidual_eq_intertwiningOperator]
  rw [exactMoleculeIntertwiningResidualOperator_eq_matrix]


/- Source slice: ExactPrincipalMoleculeGraphBridge.lean -/

local instance exactGraphBridgePrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance exactGraphBridgeLargePrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

local instance exactGraphBridgeSmallPrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

/-- Entrywise, the exact principal molecule is the full adjacency restricted
to its literal support. -/

theorem exactPrincipalMoleculeMatrix_apply_eq_primeCover
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (v w : ExactPrincipalMoleculeCoordinate S X a) :
    exactPrincipalMoleculeMatrix S X a v w =
      (PrimeStar.primeCoverGraph S X).adjMatrix ℝ v.1 w.1 := by
  classical
  let B := PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a
  let U := PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
  have hdisj : Disjoint B U := by
    simpa [B, U] using exactPrincipalMolecule_support_disjoint S X a ha
  have hv : v.1 ∈ B ∪ U := by
    simpa [B, U, exactPrincipalMoleculeSupport] using v.property
  have hw : w.1 ∈ B ∪ U := by
    simpa [B, U, exactPrincipalMoleculeSupport] using w.property
  have hdecomp :
      (PrimeStar.primeCoverGraph S X).adjMatrix ℝ v.1 w.1 =
        (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 +
          (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 := by
    exact congrArg (fun M : Matrix (PrimeStar.Vertex S X)
        (PrimeStar.Vertex S X) ℝ ↦ M v.1 w.1)
      (PrimeStar.primeCover_adjMatrix_eq_large_add_small
        S X (squareRootCutoff X))
  rcases Finset.mem_union.mp hv with hvB | hvU <;>
    rcases Finset.mem_union.mp hw with hwB | hwU
  · have hvNotU : v.1 ∉ U := fun hvU ↦
      (Finset.disjoint_left.mp hdisj) hvB hvU
    have hwNotU : w.1 ∉ U := fun hwU ↦
      (Finset.disjoint_left.mp hdisj) hwB hwU
    have hcross : ¬exactPrincipalMoleculeCrossPair S X a v w := by
      simp only [exactPrincipalMoleculeCrossPair]
      tauto
    have hsmall :
        ¬(PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj v.1 w.1 :=
      PrimeStar.not_smallPrimeGraph_adj_on_largePrimeStarSupport ha hvB hwB
    have hsmallEntry :
        (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ
          v.1 w.1 = 0 := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hsmall]
    rw [exactPrincipalMoleculeMatrix, if_neg hcross, hdecomp,
      hsmallEntry, add_zero]
  · have hcross : exactPrincipalMoleculeCrossPair S X a v w :=
      Or.inl ⟨hvB, hwU⟩
    rw [exactPrincipalMoleculeMatrix, if_pos hcross, hdecomp]
  · have hcross : exactPrincipalMoleculeCrossPair S X a v w :=
      Or.inr ⟨hvU, hwB⟩
    rw [exactPrincipalMoleculeMatrix, if_pos hcross, hdecomp]
  · have hvNotB : v.1 ∉ B := fun hvB ↦
      (Finset.disjoint_left.mp hdisj) hvB hvU
    have hwNotB : w.1 ∉ B := fun hwB ↦
      (Finset.disjoint_left.mp hdisj) hwB hwU
    have hcross : ¬exactPrincipalMoleculeCrossPair S X a v w := by
      simp only [exactPrincipalMoleculeCrossPair]
      tauto
    have hsmall :
        ¬(PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj v.1 w.1 :=
      PrimeStar.not_smallPrimeAdj_on_firstExitCompressionSupport hS
        (PrimeStar.sqrtCutoff_condition X) ha hvU hwU
    have hsmallEntry :
        (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ
          v.1 w.1 = 0 := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hsmall]
    rw [exactPrincipalMoleculeMatrix, if_neg hcross, hdecomp,
      hsmallEntry, add_zero]

/-- Matrix form: the exact molecule is the submatrix of the full adjacency
under the coordinate inclusion. -/

private theorem exactMoleculeEmbedding_compress_smallPrime
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    (exactMoleculeEmbeddingMatrix S X a).transpose *
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) *
        exactMoleculeEmbeddingMatrix S X a =
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ).submatrix
        (fun v : ExactPrincipalMoleculeCoordinate S X a ↦ v.1)
        (fun v : ExactPrincipalMoleculeCoordinate S X a ↦ v.1) := by
  classical
  ext v w
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    exactMoleculeEmbeddingMatrix, Matrix.submatrix_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single w.1]
  · rw [Finset.sum_eq_single v.1]
    · simp
    · intro x _hx hxv
      simp [hxv]
    · simp
  · intro x _hx hxw
    simp [hxw]
  · simp

private theorem exactPrincipalMolecule_crossMatrix_eq_smallPrime_submatrix
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    exactPrincipalMoleculeMatrix S X a -
        exactPrincipalMoleculeLargePrimeMatrix S X a =
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ).submatrix
        (fun v : ExactPrincipalMoleculeCoordinate S X a ↦ v.1)
        (fun v : ExactPrincipalMoleculeCoordinate S X a ↦ v.1) := by
  ext v w
  rw [Matrix.sub_apply, exactPrincipalMoleculeMatrix_apply_eq_primeCover hS ha]
  change (PrimeStar.primeCoverGraph S X).adjMatrix ℝ v.1 w.1 -
      (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 =
    (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1
  have h := congrArg (fun M : Matrix (PrimeStar.Vertex S X)
      (PrimeStar.Vertex S X) ℝ ↦ M v.1 w.1)
    (PrimeStar.primeCover_adjMatrix_eq_large_add_small S X (squareRootCutoff X))
  have h' :
      (PrimeStar.primeCoverGraph S X).adjMatrix ℝ v.1 w.1 =
        (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 +
          (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ v.1 w.1 := by
    simpa only [Matrix.add_apply] using h
  rw [h']
  ring

private theorem norm_exactMoleculeEmbeddingOperator_adjoint_le
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (y : MoleculeAmbient S X) :
    ‖(exactMoleculeEmbeddingOperator S X a).adjoint y‖ ≤ ‖y‖ := by
  let E := exactMoleculeEmbeddingOperator S X a
  let z := E.adjoint y
  by_cases hz : z = 0
  · simp [z, E, hz]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hinner : ⟪z, z⟫_ℝ = ⟪E z, y⟫_ℝ := by
    dsimp [z]
    exact LinearMap.adjoint_inner_right E (E.adjoint y) y
  have hle : ‖z‖ ^ 2 ≤ ‖z‖ * ‖y‖ := by
    calc
      ‖z‖ ^ 2 = ⟪z, z⟫_ℝ := (real_inner_self_eq_norm_sq z).symm
      _ = ⟪E z, y⟫_ℝ := hinner
      _ ≤ |⟪E z, y⟫_ℝ| := le_abs_self _
      _ ≤ ‖E z‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ = ‖z‖ * ‖y‖ := by
        rw [norm_exactMoleculeEmbeddingOperator]
  nlinarith

set_option maxHeartbeats 800000 in

private theorem exactMolecule_smallPrimeCompressionOperator
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    Matrix.toEuclideanLin
        (((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ).submatrix
          (fun v : ExactPrincipalMoleculeCoordinate S X a ↦ v.1)
          (fun v : ExactPrincipalMoleculeCoordinate S X a ↦ v.1)) =
      (exactMoleculeEmbeddingOperator S X a).adjoint.comp
        ((Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)).comp
            (exactMoleculeEmbeddingOperator S X a)) := by
  rw [← exactMoleculeEmbedding_compress_smallPrime]
  change Matrix.toEuclideanLin
      ((exactMoleculeEmbeddingMatrix S X a).transpose *
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) *
        exactMoleculeEmbeddingMatrix S X a) =
      (Matrix.toEuclideanLin (exactMoleculeEmbeddingMatrix S X a)).adjoint.comp
        ((Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)).comp
            (Matrix.toEuclideanLin (exactMoleculeEmbeddingMatrix S X a)))
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
  rw [Matrix.mul_assoc]

private theorem exactPrincipalMolecule_cross_apply_le_smallPrime
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) (eta : ℝ)
    (hH : ∀ y : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) y‖ ≤
        eta * ‖y‖)
    (x : EuclideanSpace ℝ (ExactPrincipalMoleculeCoordinate S X a)) :
    ‖(Matrix.toEuclideanLin (exactPrincipalMoleculeMatrix S X a) -
        Matrix.toEuclideanLin (exactPrincipalMoleculeLargePrimeMatrix S X a)) x‖ ≤
      eta * ‖x‖ := by
  let E := exactMoleculeEmbeddingOperator S X a
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  have hcross := exactPrincipalMolecule_crossMatrix_eq_smallPrime_submatrix hS ha
  have hop :
      Matrix.toEuclideanLin (exactPrincipalMoleculeMatrix S X a) -
          Matrix.toEuclideanLin (exactPrincipalMoleculeLargePrimeMatrix S X a) =
        E.adjoint.comp (H.comp E) := by
    rw [← map_sub]
    rw [hcross]
    exact exactMolecule_smallPrimeCompressionOperator S X a
  rw [hop, LinearMap.comp_apply, LinearMap.comp_apply]
  calc
    ‖E.adjoint (H (E x))‖ ≤ ‖H (E x)‖ :=
      norm_exactMoleculeEmbeddingOperator_adjoint_le _
    _ ≤ eta * ‖E x‖ := hH _
    _ = eta * ‖x‖ := by rw [norm_exactMoleculeEmbeddingOperator]

/-- A global small-prime operator bound controls the continuation-ranked
exact-molecule root at the same scale. -/

theorem exactPrincipalMoleculeRoot_sub_starEnergy_abs_le_smallPrime
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (eta : ℝ)
    (hH : ∀ y : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) y‖ ≤
        eta * ‖y‖) :
    |exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a| ≤ eta := by
  apply exactPrincipalMoleculeRoot_sub_starEnergy_abs_le_of_cross_bound ha hd eta
  exact exactPrincipalMolecule_cross_apply_le_smallPrime hS ha eta hH

/-- Coordinate form of the exact eigenvector equation with the literal full
graph adjacency entries. -/


/- Source slice: ExactMoleculeSupportEquation.lean -/

theorem exactMoleculeIntertwiningResidualMatrix_apply_coordinate_eq_zero
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (v w : ExactPrincipalMoleculeCoordinate S X a) :
    exactMoleculeIntertwiningResidualMatrix S X a v.1 w = 0 := by
  classical
  rw [exactMoleculeIntertwiningResidualMatrix, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.mul_apply]
  have hleft :
      (∑ x : PrimeStar.Vertex S X,
          (PrimeStar.primeCoverGraph S X).adjMatrix ℝ v.1 x *
            exactMoleculeEmbeddingMatrix S X a x w) =
        (PrimeStar.primeCoverGraph S X).adjMatrix ℝ v.1 w.1 := by
    simp [exactMoleculeEmbeddingMatrix]
  have hright :
      (∑ x : ExactPrincipalMoleculeCoordinate S X a,
          exactMoleculeEmbeddingMatrix S X a v.1 x *
            exactPrincipalMoleculeMatrix S X a x w) =
        exactPrincipalMoleculeMatrix S X a v w := by
    simp [exactMoleculeEmbeddingMatrix]
  rw [hleft, hright,
    exactPrincipalMoleculeMatrix_apply_eq_primeCover hS ha]
  ring

/-- The full ambient residual vanishes at every retained coordinate. -/

theorem exactPrincipalMoleculeResidual_apply_coordinate_eq_zero
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (v : ExactPrincipalMoleculeCoordinate S X a) :
    exactPrincipalMoleculeResidual S X a v.1 = 0 := by
  rw [exactPrincipalMoleculeResidual_eq_intertwiningMatrix]
  change (Matrix.mulVec (exactMoleculeIntertwiningResidualMatrix S X a)
    (exactPrincipalMoleculeEigenvector S X a)) v.1 = 0
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro w _hw
  rw [exactMoleculeIntertwiningResidualMatrix_apply_coordinate_eq_zero
    hS ha v w]
  simp

/-- Consequently, the embedded exact molecule vector satisfies the literal
full-graph eigenvector equation at every vertex of its support. -/

theorem primeCover_apply_exactPrincipalMoleculeAmbientVector_on_coordinate
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (v : ExactPrincipalMoleculeCoordinate S X a) :
    primeCoverAdjacencyOperator S X
        (exactPrincipalMoleculeAmbientVector S X a) v.1 =
      exactPrincipalMoleculeRoot S X a *
        exactPrincipalMoleculeAmbientVector S X a v.1 := by
  have hzero := exactPrincipalMoleculeResidual_apply_coordinate_eq_zero
    hS ha v
  simpa [exactPrincipalMoleculeResidual, sub_eq_zero] using hzero


/- Source slice: ExactTargetStarResolvent.lean -/

local instance exactTargetStarLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance exactTargetStarSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The ambient exact molecule vector vanishes away from its literal support. -/

theorem exactPrincipalMoleculeAmbientVector_eq_zero_of_not_mem_support
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    {v : PrimeStar.Vertex S X}
    (hv : v ∉ exactPrincipalMoleculeSupport S X a) :
    exactPrincipalMoleculeAmbientVector S X a v = 0 := by
  classical
  simp only [exactPrincipalMoleculeAmbientVector,
    exactMoleculeEmbeddingOperator, Matrix.toLpLin_apply,
    Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hvw : v ≠ w.1 := by
    intro h
    apply hv
    rw [h]
    exact w.2
  simp [exactMoleculeEmbeddingMatrix, hvw]

/-- Boundary part of the exact principal molecule. -/

def exactPrincipalMoleculeBoundaryVector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) a
    (exactPrincipalMoleculeAmbientVector S X a)

/-- First-exit interior part of the exact principal molecule. -/

def exactPrincipalMoleculeInteriorVector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
    (exactPrincipalMoleculeAmbientVector S X a)

/-- Boundary-to-first-exit source of the exact principal molecule. -/

def exactPrincipalMoleculeInteriorSource
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
      (exactPrincipalMoleculeBoundaryVector S X a))

/-- The exact molecule has no component outside its boundary and first-exit
coordinate blocks. -/

theorem exactPrincipalMolecule_boundary_add_interior
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    exactPrincipalMoleculeBoundaryVector S X a +
        exactPrincipalMoleculeInteriorVector S X a =
      exactPrincipalMoleculeAmbientVector S X a := by
  classical
  ext v
  by_cases hvB : v ∈ PrimeStar.largePrimeStarSupport S X
      (squareRootCutoff X) a
  · have hvU : v ∉ PrimeStar.firstExitCompressionSupport S X
        (squareRootCutoff X) a := by
      intro hvU
      exact (Finset.disjoint_left.mp
        (exactPrincipalMolecule_support_disjoint S X a ha)) hvB hvU
    simp [exactPrincipalMoleculeBoundaryVector,
      exactPrincipalMoleculeInteriorVector, hvB, hvU]
  · by_cases hvU : v ∈ PrimeStar.firstExitCompressionSupport S X
        (squareRootCutoff X) a
    · simp [exactPrincipalMoleculeBoundaryVector,
        exactPrincipalMoleculeInteriorVector, hvB, hvU]
    · have hv : v ∉ exactPrincipalMoleculeSupport S X a := by
        simp [exactPrincipalMoleculeSupport, hvB, hvU]
      rw [exactPrincipalMoleculeAmbientVector_eq_zero_of_not_mem_support hv]
      simp [exactPrincipalMoleculeBoundaryVector,
        exactPrincipalMoleculeInteriorVector, hvB, hvU]

/-- Projecting the exact support equation onto the first-exit coordinates. -/

theorem firstExitProjection_primeCover_exactPrincipalMolecule
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
        (primeCoverAdjacencyOperator S X
          (exactPrincipalMoleculeAmbientVector S X a)) =
      exactPrincipalMoleculeRoot S X a •
        exactPrincipalMoleculeInteriorVector S X a := by
  classical
  ext v
  by_cases hvU : v ∈ PrimeStar.firstExitCompressionSupport S X
      (squareRootCutoff X) a
  · let w : ExactPrincipalMoleculeCoordinate S X a :=
      ⟨v, Finset.mem_union_right _ hvU⟩
    have heq := primeCover_apply_exactPrincipalMoleculeAmbientVector_on_coordinate
      hS ha w
    simpa [exactPrincipalMoleculeInteriorVector, hvU, w,
      PrimeStar.firstExitCompressionProjection_apply] using heq
  · simp [exactPrincipalMoleculeInteriorVector, hvU,
      PrimeStar.firstExitCompressionProjection_apply]

/-- The first-exit part of the exact molecule solves the literal shifted
large-prime equation with boundary source. -/

theorem exactPrincipalMoleculeInterior_shift_largePrime
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    exactPrincipalMoleculeRoot S X a •
        exactPrincipalMoleculeInteriorVector S X a -
      Matrix.toEuclideanLin
          ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeInteriorVector S X a) =
      exactPrincipalMoleculeInteriorSource S X a := by
  let P := PrimeStar.firstExitCompressionProjection S X
    (squareRootCutoff X) a
  let A := primeCoverAdjacencyOperator S X
  let L := Matrix.toEuclideanLin
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let xB := exactPrincipalMoleculeBoundaryVector S X a
  let xU := exactPrincipalMoleculeInteriorVector S X a
  have hx : xB + xU = exactPrincipalMoleculeAmbientVector S X a :=
    exactPrincipalMolecule_boundary_add_interior ha
  have hfull : P (A (xB + xU)) =
      exactPrincipalMoleculeRoot S X a • xU := by
    rw [hx]
    exact firstExitProjection_primeCover_exactPrincipalMolecule hS ha
  have hU : P (A xU) = P (L xU) := by
    simpa [P, A, L, xU, primeCoverAdjacencyOperator,
      exactPrincipalMoleculeInteriorVector] using
      (PrimeStar.firstExitCompression_primeCover_eq_largePrime
        (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
        hS (PrimeStar.sqrtCutoff_condition X) ha
        (exactPrincipalMoleculeAmbientVector S X a))
  have hxU_support : ∀ v,
      v ∉ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a →
        xU v = 0 := by
    intro v hv
    simp [xU, exactPrincipalMoleculeInteriorVector,
      PrimeStar.firstExitCompressionProjection_apply, hv]
  have hPL : P (L xU) = L xU := by
    apply PrimeStar.firstExitCompressionProjection_eq_of_supported
    intro v hv
    simpa [L, squareRootCutoff] using
      (PrimeStar.largePrime_toEuclideanLin_eq_zero_outside_firstExitCompression
        (S := S) (X := X) (Y := Nat.sqrt X) (c := a)
        (PrimeStar.sqrtCutoff_condition X) xU hxU_support hv)
  have hxB_complement :
      PrimeStar.euclideanCoordinateComplementProjection
          (PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a)
          xB = xB := by
    ext v
    by_cases hvU : v ∈ PrimeStar.firstExitCompressionSupport S X
        (squareRootCutoff X) a
    · have hvB : v ∉ PrimeStar.largePrimeStarSupport S X
          (squareRootCutoff X) a := by
        intro hvB
        exact (Finset.disjoint_left.mp
          (exactPrincipalMolecule_support_disjoint S X a ha)) hvB hvU
      simp [PrimeStar.euclideanCoordinateComplementProjection_apply,
        xB, exactPrincipalMoleculeBoundaryVector,
        PrimeStar.primeStarBoundaryProjection_apply, hvU, hvB]
    · simp [PrimeStar.euclideanCoordinateComplementProjection_apply, hvU]
  have hB : P (A xB) = P (H xB) := by
    have h := PrimeStar.firstExitCompression_boundary_primeCover_eq_smallPrime
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
      (PrimeStar.sqrtCutoff_condition X) xB
    simpa [P, A, H, primeCoverAdjacencyOperator, hxB_complement] using h
  change exactPrincipalMoleculeRoot S X a • xU - L xU = P (H xB)
  simp only [map_add] at hfull
  rw [hB, hU, hPL] at hfull
  exact sub_eq_iff_eq_add.mpr hfull.symm

/-- The boundary source is supported on the canonical first-exit compression. -/

theorem exactPrincipalMoleculeInteriorSource_eq_zero_of_not_mem
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    {v : PrimeStar.Vertex S X}
    (hv : v ∉ PrimeStar.smallPrimeFirstExitSupport S X
      (squareRootCutoff X) a) :
    exactPrincipalMoleculeInteriorSource S X a v = 0 := by
  classical
  rw [exactPrincipalMoleculeInteriorSource,
    PrimeStar.firstExitCompressionProjection_apply]
  split
  next hvU =>
    rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
    apply PrimeStar.smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
      (fun w ↦ exactPrincipalMoleculeBoundaryVector S X a w)
    · intro w hw
      rw [exactPrincipalMoleculeBoundaryVector,
        PrimeStar.primeStarBoundaryProjection_apply, if_neg hw]
    · exact hv
  next _ => rfl

/-- Under the literal nonresonance hypotheses, the complete first-exit part
of the exact molecule is the direct sum of the actual target-star resolvents. -/

theorem exactPrincipalMoleculeInterior_eq_firstExitStarResolventVector
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    exactPrincipalMoleculeInteriorVector S X a =
      PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeRoot S X a)
        (exactPrincipalMoleculeInteriorSource S X a) := by
  let x := exactPrincipalMoleculeInteriorVector S X a
  let b := exactPrincipalMoleculeInteriorSource S X a
  have hxSupport : ∀ v,
      v ∉ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a →
        x v = 0 := by
    intro v hv
    simp [x, exactPrincipalMoleculeInteriorVector,
      PrimeStar.firstExitCompressionProjection_apply, hv]
  have hcompression :
      PrimeStar.firstExitLargePrimeCompressionOperator S X
          (squareRootCutoff X) a x =
        Matrix.toEuclideanLin
            ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x := by
    exact PrimeStar.firstExitLargePrimeCompressionOperator_eq_of_supported
      (PrimeStar.sqrtCutoff_condition X) x hxSupport
  have hsolve :
      exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x = b := by
    rw [hcompression]
    exact exactPrincipalMoleculeInterior_shift_largePrime hS ha
  have hb : ∀ v,
      v ∉ PrimeStar.smallPrimeFirstExitSupport S X (squareRootCutoff X) a →
        b v = 0 := by
    intro v hv
    exact exactPrincipalMoleculeInteriorSource_eq_zero_of_not_mem hv
  have hgapExplicit :=
    PrimeStar.firstExitLargePrimeResolventOfGap_apply_eq_firstExitStarResolventVector
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
      (mu := exactPrincipalMoleculeRoot S X a) (gamma := gamma)
      b (PrimeStar.sqrtCutoff_condition X) hroot hden hb hgamma hgap
  change x = PrimeStar.firstExitStarResolventVector S X
      (squareRootCutoff X) a (exactPrincipalMoleculeRoot S X a) b
  rw [← hgapExplicit]
  rw [← hsolve]
  exact (PrimeStar.firstExitLargePrimeResolventOfGap_shift_apply
    S X (squareRootCutoff X) a (exactPrincipalMoleculeRoot S X a)
      gamma hgamma hgap x).symm

/-- On one selected first-exit star, the direct-sum inverse is exactly its
single actual-star inverse. -/

theorem firstExitStarResolventVector_apply_of_mem_selectedStar
    {S : Finset ℕ} {X Y : ℕ} {a k v : PrimeStar.Vertex S X} {mu : ℝ}
    (b : MoleculeAmbient S X)
    (hcut : X < (Y + 1) * (Y + 1))
    (hk : k ∈ PrimeStar.firstExitLowerCenters S X Y a)
    (hv : v ∈ PrimeStar.largePrimeStarSupport S X Y k) :
    PrimeStar.firstExitStarResolventVector S X Y a mu b v =
      PrimeStar.largePrimeStarResolventOfVector S X Y k mu
        (PrimeStar.restrictEuclideanToFinset
          (PrimeStar.largePrimeStarSupport S X Y k) b) v := by
  classical
  let C := PrimeStar.firstExitLowerCenters S X Y a
  let R := fun j : PrimeStar.Vertex S X ↦
    PrimeStar.largePrimeStarResolventOfVector S X Y j mu
      (PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X Y j) b)
  have hsum : (∑ j ∈ C, R j) v = R k v := by
    change EuclideanSpace.projₗ v (∑ j ∈ C, R j) = R k v
    simp only [map_sum]
    change (∑ j ∈ C, R j v) = R k v
    apply Finset.sum_eq_single k
    · intro j hj hne
      have hjY := (PrimeStar.mem_firstExitLowerCenters.mp hj).1
      have hkY := (PrimeStar.mem_firstExitLowerCenters.mp hk).1
      have hdisj := PrimeStar.disjoint_largePrimeStarSupport
        hcut hkY hjY hne.symm
      have hvout : v ∉ PrimeStar.largePrimeStarSupport S X Y j := by
        intro hvj
        exact (Finset.disjoint_left.mp hdisj) hv hvj
      have hvj : v ≠ j := by
        intro h
        apply hvout
        simp [h, PrimeStar.largePrimeStarSupport]
      have hvleaf : v ∉ PrimeStar.largePrimeLeaves S X Y j := by
        intro h
        apply hvout
        simp [PrimeStar.largePrimeStarSupport, h]
      exact PrimeStar.largePrimeStarDataVector_outside _ _ hvj hvleaf
    · intro hnot
      exact False.elim (hnot hk)
  have hvIso : v ∉ PrimeStar.firstExitIsolatedVertices S X Y a := by
    intro hvI
    exact PrimeStar.not_isolated_of_mem_selected_largePrimeStarSupport hk hv
      (PrimeStar.mem_firstExitIsolatedVertices.mp hvI).2
  unfold PrimeStar.firstExitStarResolventVector
  change (∑ j ∈ C, R j) v +
      (mu⁻¹ • PrimeStar.restrictEuclideanToFinset
        (PrimeStar.firstExitIsolatedVertices S X Y a) b) v = R k v
  rw [hsum]
  simp [PrimeStar.restrictEuclideanToFinset_apply, hvIso]

/-- Exact centre coordinate on every selected target star. -/


/- Source slice: BoundaryLeafCounts.lean -/

abbrev boundaryLeafExitPrimeLabels
    (S : Finset ℕ) (X Y : ℕ) (leaf : PrimeStar.Vertex S X) : Finset ℕ :=
  PrimeStar.canonicalUpPrimeLabels S X Y leaf

/-- The boundary-leaf exit labels are exactly the allowed primes up to the
smaller of the geometric cutoff `Y` and the arithmetic cutoff `X / leaf`.
-/

theorem boundaryLeafExitPrimeLabels_eq
    (S : Finset ℕ) (X Y : ℕ) (leaf : PrimeStar.Vertex S X) :
    boundaryLeafExitPrimeLabels S X Y leaf =
      (Nat.primesLE (min Y (X / (leaf : ℕ)))).filter fun q ↦ q ∉ S := by
  ext q
  simp only [boundaryLeafExitPrimeLabels, PrimeStar.canonicalUpPrimeLabels,
    Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hqY, hqPrime⟩, hqS, hqBound⟩
    have hqDiv : q ≤ X / (leaf : ℕ) := by
      apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos leaf)).2
      simpa [Nat.mul_comm] using hqBound
    exact ⟨⟨le_min hqY hqDiv, hqPrime⟩, hqS⟩
  · rintro ⟨⟨hqMin, hqPrime⟩, hqS⟩
    have hqY : q ≤ Y := hqMin.trans (min_le_left _ _)
    have hqDiv : q ≤ X / (leaf : ℕ) := hqMin.trans (min_le_right _ _)
    have hqBound : (leaf : ℕ) * q ≤ X := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos leaf)).1 hqDiv
    exact ⟨⟨hqY, hqPrime⟩, hqS, hqBound⟩

/-- Exact cardinality formula for the manuscript's boundary-leaf count
`n_a(p)`.
-/

theorem card_boundaryLeafExitPrimeLabels
    (S : Finset ℕ) (X Y : ℕ) (leaf : PrimeStar.Vertex S X) :
    (boundaryLeafExitPrimeLabels S X Y leaf).card =
      PrimeStar.allowedPrimeCount S (min Y (X / (leaf : ℕ))) := by
  rw [boundaryLeafExitPrimeLabels_eq]
  rfl

/-- Numeric form of the boundary-leaf exit count. -/

def boundaryLeafExitCount
    (S : Finset ℕ) (X Y : ℕ) (leaf : PrimeStar.Vertex S X) : ℕ :=
  (boundaryLeafExitPrimeLabels S X Y leaf).card

theorem boundaryLeafExitCount_eq_allowedPrimeCount
    (S : Finset ℕ) (X Y : ℕ) (leaf : PrimeStar.Vertex S X) :
    boundaryLeafExitCount S X Y leaf =
      PrimeStar.allowedPrimeCount S (min Y (X / (leaf : ℕ))) :=
  card_boundaryLeafExitPrimeLabels S X Y leaf

/-- Boundary leaf `a*p` indexed by its unique large-prime label. -/

def arithmeticBoundaryLeaf
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : PrimeStar.Vertex S X) (p : ℕ)
    (hp : p ∈ PrimeStar.largePrimeLabels S X Y a) : PrimeStar.Vertex S X :=
  PrimeStar.vertexMulPrimeOfMemLargePrimeLabels hS a p hp

@[simp]

theorem arithmeticBoundaryLeaf_coe
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : PrimeStar.Vertex S X) (p : ℕ)
    (hp : p ∈ PrimeStar.largePrimeLabels S X Y a) :
    (arithmeticBoundaryLeaf hS a p hp : ℕ) = (a : ℕ) * p :=
  rfl

/-- Exact arithmetic formula for `n_a(p)` at a large-prime boundary leaf.
-/

theorem boundaryLeafExitCount_arithmeticBoundaryLeaf
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : PrimeStar.Vertex S X) (p : ℕ)
    (hp : p ∈ PrimeStar.largePrimeLabels S X Y a) :
    boundaryLeafExitCount S X Y (arithmeticBoundaryLeaf hS a p hp) =
      PrimeStar.allowedPrimeCount S (min Y (X / ((a : ℕ) * p))) := by
  rw [boundaryLeafExitCount_eq_allowedPrimeCount, arithmeticBoundaryLeaf_coe]

/-- Large-prime labels of the boundary leaves of `a`. -/


/- Source slice: StarKernelVariance.lean -/

local instance starKernelLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Adjacency matrix of an abstract star with one hub and leaf set `ι`. -/

def finsetMean {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x

/-- Deviations from the mean over a nonempty finset sum to zero. -/

theorem sum_sub_finsetMean_eq_zero
    {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    (f : α → ℝ) :
    ∑ x ∈ s, (f x - finsetMean s f) = 0 := by
  have hcardNat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hcardNat
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [nsmul_eq_mul, finsetMean]
  field_simp
  ring

/-- Finite bias--variance decomposition around zero, written directly over a
finset. -/

theorem sum_sq_eq_sum_sq_sub_finsetMean_add
    {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    (f : α → ℝ) :
    (∑ x ∈ s, f x ^ 2) =
      (∑ x ∈ s, (f x - finsetMean s f) ^ 2) +
        (s.card : ℝ) * (finsetMean s f) ^ 2 := by
  have hzero := sum_sub_finsetMean_eq_zero hs f
  have hcross :
      (∑ x ∈ s, 2 * (f x - finsetMean s f) * finsetMean s f) = 0 := by
    calc
      (∑ x ∈ s, 2 * (f x - finsetMean s f) * finsetMean s f) =
          2 * finsetMean s f *
            (∑ x ∈ s, (f x - finsetMean s f)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _hx
              ring
      _ = 0 := by rw [hzero, mul_zero]
  calc
    (∑ x ∈ s, f x ^ 2) =
        ∑ x ∈ s,
          ((f x - finsetMean s f) ^ 2 +
            2 * (f x - finsetMean s f) * finsetMean s f +
            (finsetMean s f) ^ 2) := by
              apply Finset.sum_congr rfl
              intro x _hx
              ring
    _ = (∑ x ∈ s, (f x - finsetMean s f) ^ 2) +
          (∑ x ∈ s,
            2 * (f x - finsetMean s f) * finsetMean s f) +
          (s.card : ℝ) * (finsetMean s f) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            simp only [Finset.sum_const, nsmul_eq_mul]
    _ = (∑ x ∈ s, (f x - finsetMean s f) ^ 2) +
          (s.card : ℝ) * (finsetMean s f) ^ 2 := by rw [hcross]; ring

/-- Subtracting the arithmetic mean cannot increase squared mass. -/

theorem sum_sq_sub_finsetMean_le_sum_sq
    {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    (f : α → ℝ) :
    (∑ x ∈ s, (f x - finsetMean s f) ^ 2) ≤ ∑ x ∈ s, f x ^ 2 := by
  rw [sum_sq_eq_sum_sq_sub_finsetMean_add hs f]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Mean-zero vector on the leaves of an actual large-prime star. -/

def actualStarMeanZeroLeafVector
    (S : Finset ℕ) (X Y : ℕ) (c : PrimeStar.Vertex S X)
    (f : PrimeStar.Vertex S X → ℝ) : MoleculeAmbient S X :=
  PrimeStar.largePrimeStarDataVector S X Y c 0
    (fun v ↦ f v - finsetMean (PrimeStar.largePrimeLeaves S X Y c) f)

/-- The large-prime forest kills the actual mean-zero leaf vector.  This is
the graph-level form of `L z = 0` used in manuscript (4.10). -/


/- Source slice: BoundaryLeafKernel.lean -/

local instance boundaryLeafKernelLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Literal boundary-leaf square sum, indexed directly by the leaves of one
large-prime star. -/

def boundaryLeafCountSquareSumOnStar
    (S : Finset ℕ) (X Y : ℕ) (a : PrimeStar.Vertex S X) : ℕ :=
  ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a,
    boundaryLeafExitCount S X Y v ^ 2

/-- Arithmetic form of the same square sum, with no graph-neighbor count
remaining. -/


/- Source slice: ExactBoundaryDecomposition.lean -/

local instance exactBoundaryLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Coefficient of the positive unnormalized signed mode in the constant-leaf
part of a star vector. -/

def starPositiveCoefficient (d : ℕ) (center leafMean : ℝ) : ℝ :=
  (center / Real.sqrt d + leafMean) / 2

/-- Coefficient of the negative unnormalized signed mode in the constant-leaf
part of a star vector. -/

def starNegativeCoefficient (d : ℕ) (center leafMean : ℝ) : ℝ :=
  (center / Real.sqrt d - leafMean) / 2

/-- Exact positive/negative/kernel decomposition of an arbitrary vector on a
nonempty actual large-prime star. -/

theorem largePrimeStarDataVector_eq_signedModes_add_kernel
    {S : Finset ℕ} {X Y : ℕ} {c : PrimeStar.Vertex S X}
    (center : ℝ) (leaf : PrimeStar.Vertex S X → ℝ)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y c) :
    PrimeStar.largePrimeStarDataVector S X Y c center leaf =
      starPositiveCoefficient (PrimeStar.largePrimeStarDegree S X Y c)
          center (finsetMean (PrimeStar.largePrimeLeaves S X Y c) leaf) •
        PrimeStar.largePrimeEuclideanStarVector S X Y c 1 +
      starNegativeCoefficient (PrimeStar.largePrimeStarDegree S X Y c)
          center (finsetMean (PrimeStar.largePrimeLeaves S X Y c) leaf) •
        PrimeStar.largePrimeEuclideanStarVector S X Y c (-1) +
      actualStarMeanZeroLeafVector S X Y c leaf := by
  classical
  let d := PrimeStar.largePrimeStarDegree S X Y c
  let m := finsetMean (PrimeStar.largePrimeLeaves S X Y c) leaf
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hsqrt0 : Real.sqrt (d : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hsqrtSq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg d)
  ext v
  by_cases hvc : v = c
  · subst v
    simp only [PrimeStar.largePrimeStarDataVector_center, PiLp.add_apply,
      PiLp.smul_apply, actualStarMeanZeroLeafVector,
      PrimeStar.largePrimeEuclideanStarVector,
      PrimeStar.largePrimeSignedStarVector_center,
      smul_eq_mul, add_zero]
    change center =
      starPositiveCoefficient d center m * Real.sqrt d +
        starNegativeCoefficient d center m * Real.sqrt d
    rw [starPositiveCoefficient, starNegativeCoefficient]
    field_simp [hsqrt0]
    ring
  · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X Y c
    · rw [PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
      simp only [PiLp.add_apply, PiLp.smul_apply,
        PrimeStar.largePrimeEuclideanStarVector,
        PrimeStar.largePrimeSignedStarVector_leaf hvleaf, smul_eq_mul,
        mul_neg, mul_one, actualStarMeanZeroLeafVector]
      rw [PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
      change leaf v =
        starPositiveCoefficient d center m -
          starNegativeCoefficient d center m + (leaf v - m)
      rw [starPositiveCoefficient, starNegativeCoefficient]
      ring
    · have hvout : v ∉ PrimeStar.largePrimeStarSupport S X Y c := by
        simp [PrimeStar.largePrimeStarSupport, hvc, hvleaf]
      rw [PrimeStar.largePrimeStarDataVector_outside _ _ hvc hvleaf]
      simp only [PiLp.add_apply, PiLp.smul_apply,
        PrimeStar.largePrimeEuclideanStarVector,
        PrimeStar.largePrimeSignedStarVector_eq_zero_of_not_mem hvout,
        smul_eq_mul, mul_zero, zero_add, actualStarMeanZeroLeafVector]
      rw [PrimeStar.largePrimeStarDataVector_outside _ _ hvc hvleaf]

/-- Coordinate projection onto one star is the corresponding literal star
data vector. -/

theorem primeStarBoundaryProjection_eq_largePrimeStarDataVector
    {S : Finset ℕ} {X Y : ℕ} {c : PrimeStar.Vertex S X}
    (x : MoleculeAmbient S X) :
    PrimeStar.primeStarBoundaryProjection S X Y c x =
      PrimeStar.largePrimeStarDataVector S X Y c (x c) x := by
  ext v
  rw [PrimeStar.primeStarBoundaryProjection_apply]
  by_cases hvc : v = c
  · subst v
    simp
  · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X Y c
    · have hvsupp : v ∈ PrimeStar.largePrimeStarSupport S X Y c := by
        simp [PrimeStar.largePrimeStarSupport, hvleaf]
      rw [if_pos hvsupp,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
    · have hvout : v ∉ PrimeStar.largePrimeStarSupport S X Y c := by
        simp [PrimeStar.largePrimeStarSupport, hvc, hvleaf]
      rw [if_neg hvout,
        PrimeStar.largePrimeStarDataVector_outside _ _ hvc hvleaf]

/-- Mean-zero boundary component of the literal exact molecule eigenvector. -/

def exactPrincipalMoleculeBoundaryKernel
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
    (exactPrincipalMoleculeAmbientVector S X a)

/-- The boundary part of the exact molecule splits into its two signed modes
and the mean-zero kernel component. -/

theorem exactPrincipalMolecule_boundary_eq_signedModes_add_kernel
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) a
        (exactPrincipalMoleculeAmbientVector S X a) =
      starPositiveCoefficient
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
          (exactPrincipalMoleculeAmbientVector S X a a)
          (finsetMean (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
            (exactPrincipalMoleculeAmbientVector S X a)) •
        PrimeStar.largePrimeEuclideanStarVector S X (squareRootCutoff X) a 1 +
      starNegativeCoefficient
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
          (exactPrincipalMoleculeAmbientVector S X a a)
          (finsetMean (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
            (exactPrincipalMoleculeAmbientVector S X a)) •
        PrimeStar.largePrimeEuclideanStarVector S X (squareRootCutoff X) a (-1) +
      exactPrincipalMoleculeBoundaryKernel S X a := by
  rw [primeStarBoundaryProjection_eq_largePrimeStarDataVector]
  exact largePrimeStarDataVector_eq_signedModes_add_kernel
    (exactPrincipalMoleculeAmbientVector S X a a)
    (exactPrincipalMoleculeAmbientVector S X a) hd

/-- The boundary-kernel component of the exact molecule is an exact zero mode
of the large-prime forest. -/


/- Source slice: ExactBoundarySchurEquation.lean -/

local instance exactBoundarySchurPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance exactBoundarySchurLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance exactBoundarySchurSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Small-prime return from the exact first-exit interior to the original
boundary star. -/

def exactPrincipalMoleculeBoundaryFeedback
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) a
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
      (exactPrincipalMoleculeInteriorVector S X a))

/-- Projecting the literal exact-molecule equation onto the original star
gives the complementary half of the boundary/interior Schur system. -/

theorem exactPrincipalMoleculeBoundary_shift_largePrime
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    exactPrincipalMoleculeRoot S X a •
        exactPrincipalMoleculeBoundaryVector S X a -
      Matrix.toEuclideanLin
          ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeBoundaryVector S X a) =
      exactPrincipalMoleculeBoundaryFeedback S X a := by
  let PB := PrimeStar.primeStarBoundaryProjection S X
    (squareRootCutoff X) a
  let PI := PrimeStar.primeStarInteriorProjection S X
    (squareRootCutoff X) a
  let A := Matrix.toEuclideanLin
    ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ)
  let L := Matrix.toEuclideanLin
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let xB := exactPrincipalMoleculeBoundaryVector S X a
  let xU := exactPrincipalMoleculeInteriorVector S X a
  have hx : xB + xU = exactPrincipalMoleculeAmbientVector S X a :=
    exactPrincipalMolecule_boundary_add_interior ha
  have hfull : PB (A (xB + xU)) =
      exactPrincipalMoleculeRoot S X a • xB := by
    rw [hx]
    ext v
    by_cases hvB : v ∈ PrimeStar.largePrimeStarSupport S X
        (squareRootCutoff X) a
    · let w : ExactPrincipalMoleculeCoordinate S X a :=
        ⟨v, Finset.mem_union_left _ hvB⟩
      have heq :=
        primeCover_apply_exactPrincipalMoleculeAmbientVector_on_coordinate
          hS ha w
      simpa [PB, A, primeCoverAdjacencyOperator, xB,
        exactPrincipalMoleculeBoundaryVector,
        PrimeStar.primeStarBoundaryProjection_apply, hvB, w] using heq
    · simp [PB, xB, exactPrincipalMoleculeBoundaryVector,
        PrimeStar.primeStarBoundaryProjection_apply, hvB]
  have hPBxB : PB xB = xB := by
    exact PrimeStar.primeStarBoundaryProjection_idem
      (exactPrincipalMoleculeAmbientVector S X a)
  have hB : PB (A xB) = L xB := by
    have h :=
      PrimeStar.primeStarBoundaryPrimeCoverOperator_eq_largePrime_of_supported
        (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
        (PrimeStar.sqrtCutoff_condition X) ha xB hPBxB
    simpa [PrimeStar.primeStarBoundaryPrimeCoverOperator, PB, A, L,
      hPBxB] using h
  have hPBxU : PB xU = 0 := by
    simpa [PB, xU, exactPrincipalMoleculeInteriorVector] using
      (PrimeStar.primeStarBoundaryProjection_firstExit_eq_zero
        (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
        (PrimeStar.sqrtCutoff_condition X) ha
        (exactPrincipalMoleculeAmbientVector S X a))
  have hPIxU : PI xU = xU := by
    exact PrimeStar.primeStarInteriorProjection_eq_of_boundary_eq_zero hPBxU
  have hU : PB (A xU) = PB (H xU) := by
    have h := PrimeStar.primeStarFromInteriorPrimeCoverOperator_eq_smallPrime
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
      (PrimeStar.sqrtCutoff_condition X) ha xU
    simpa [PrimeStar.primeStarFromInteriorPrimeCoverOperator, PB, PI, A, H,
      hPIxU] using h
  change exactPrincipalMoleculeRoot S X a • xB - L xB = PB (H xU)
  simp only [map_add] at hfull
  rw [hB, hU] at hfull
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using hfull.symm

/-- After the target resolvent is inserted, the previous identity is the exact
finite Feshbach equation on the complete boundary star. -/

theorem largePrime_apply_exactPrincipalMoleculeBoundaryVector_leaf
    {S : Finset ℕ} {X : ℕ} {a v : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hv : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin
        ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeBoundaryVector S X a) v =
      exactPrincipalMoleculeBoundaryVector S X a a := by
  rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
  change Matrix.mulVec
      ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (fun w ↦ exactPrincipalMoleculeBoundaryVector S X a w) v =
    exactPrincipalMoleculeBoundaryVector S X a a
  rw [SimpleGraph.adjMatrix_mulVec_apply,
    PrimeStar.sqrtCutoff_largePrime_neighborFinset_leaf ha hv]
  simp

/-- The mean-zero part of the exact boundary vector is forced exactly by the
mean-zero part of the first-exit return.  This is the finite identity to which
the leaf-count coefficient estimate is applied. -/

theorem exactPrincipalMoleculeRoot_smul_boundaryKernel_eq_feedbackKernel
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeRoot S X a •
        exactPrincipalMoleculeBoundaryKernel S X a =
      actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeBoundaryFeedback S X a) := by
  classical
  let D := PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a
  let lambda := exactPrincipalMoleculeRoot S X a
  let xB := exactPrincipalMoleculeBoundaryVector S X a
  let F := exactPrincipalMoleculeBoundaryFeedback S X a
  let L := Matrix.toEuclideanLin
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  have hEq : lambda • xB - L xB = F := by
    exact exactPrincipalMoleculeBoundary_shift_largePrime hS ha
  have hleafEq : ∀ v ∈ D, lambda * xB v - xB a = F v := by
    intro v hv
    have hvEq := congrFun (congrArg WithLp.ofLp hEq) v
    have hLv := largePrime_apply_exactPrincipalMoleculeBoundaryVector_leaf
      ha hv
    simpa [lambda, xB, F, L, PiLp.smul_apply, smul_eq_mul, hLv] using hvEq
  have hD : D.Nonempty := Finset.card_pos.mp (by
    simpa [D, PrimeStar.largePrimeStarDegree] using hd)
  have hcardNat : D.card ≠ 0 := Finset.card_ne_zero.mpr hD
  have hcard : (D.card : ℝ) ≠ 0 := by exact_mod_cast hcardNat
  have hsum :
      ∑ v ∈ D, (lambda * xB v - xB a) = ∑ v ∈ D, F v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact hleafEq v hv
  have hmean :
      lambda * finsetMean D xB - xB a = finsetMean D F := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum] at hsum
    unfold finsetMean
    field_simp [hcard]
    nlinarith
  have hcentered : ∀ v ∈ D,
      lambda * (xB v - finsetMean D xB) =
        F v - finsetMean D F := by
    intro v hv
    have hvEq := hleafEq v hv
    nlinarith [hmean]
  have hxBLeaf : ∀ v ∈ D,
      xB v = exactPrincipalMoleculeAmbientVector S X a v := by
    intro v hv
    have hvB : v ∈ PrimeStar.largePrimeStarSupport S X
        (squareRootCutoff X) a := Finset.mem_insert_of_mem hv
    simp [xB, exactPrincipalMoleculeBoundaryVector,
      PrimeStar.primeStarBoundaryProjection_apply, hvB]
  have hmeanBoundary :
      finsetMean D xB =
        finsetMean D (exactPrincipalMoleculeAmbientVector S X a) := by
    unfold finsetMean
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    exact hxBLeaf v hv
  have hkernelEq :
      exactPrincipalMoleculeBoundaryKernel S X a =
        actualStarMeanZeroLeafVector S X (squareRootCutoff X) a xB := by
    ext v
    by_cases hva : v = a
    · subst v
      simp [exactPrincipalMoleculeBoundaryKernel,
        actualStarMeanZeroLeafVector]
    · by_cases hvD : v ∈ D
      · simp only [exactPrincipalMoleculeBoundaryKernel,
          actualStarMeanZeroLeafVector,
          PrimeStar.largePrimeStarDataVector_leaf _ _ hvD]
        rw [hxBLeaf v hvD, hmeanBoundary]
      · simp only [exactPrincipalMoleculeBoundaryKernel,
          actualStarMeanZeroLeafVector,
          PrimeStar.largePrimeStarDataVector_outside _ _ hva hvD]
  rw [hkernelEq]
  ext v
  by_cases hva : v = a
  · subst v
    simp [actualStarMeanZeroLeafVector]
  · by_cases hvD : v ∈ D
    · simp only [actualStarMeanZeroLeafVector, PiLp.smul_apply, smul_eq_mul,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hvD]
      exact hcentered v hvD
    · simp only [actualStarMeanZeroLeafVector,
        PrimeStar.largePrimeStarDataVector_outside _ _ hva hvD,
        PiLp.smul_apply, smul_eq_mul, mul_zero]


/- Source slice: ExactBoundarySignedModes.lean -/

def exactPrincipalMoleculeBoundaryModeCoefficient
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) (eps : ℝ) : ℝ :=
  ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a eps,
    exactPrincipalMoleculeAmbientVector S X a⟫_ℝ

/-- Centre amplitude with which one signed mode generates a first-exit
source. -/

def exactPrincipalMoleculeBoundarySourceAmplitude
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) (eps : ℝ) : ℝ :=
  exactPrincipalMoleculeBoundaryModeCoefficient S X a eps / Real.sqrt 2

/-- A unit exact molecule has signed boundary Fourier coefficients of
absolute value at most one. -/

theorem abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X} {eps : ℝ}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1) :
    |exactPrincipalMoleculeBoundaryModeCoefficient S X a eps| ≤ 1 := by
  unfold exactPrincipalMoleculeBoundaryModeCoefficient
  calc
    |⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a eps,
      exactPrincipalMoleculeAmbientVector S X a⟫_ℝ| ≤
        ‖PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps‖ *
        ‖exactPrincipalMoleculeAmbientVector S X a‖ :=
      abs_real_inner_le_norm _ _
    _ = 1 := by
      rw [PrimeStar.norm_largePrimeNormalizedStarMode hd,
        norm_exactPrincipalMoleculeAmbientVector]
      norm_num

/-- The positive and negative source amplitudes separately have absolute
value at most one. -/

theorem abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X} {eps : ℝ}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1) :
    |exactPrincipalMoleculeBoundarySourceAmplitude S X a eps| ≤ 1 := by
  have hcoeff :=
    abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one
      (S := S) (X := X) (a := a) hd heps
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [exactPrincipalMoleculeBoundarySourceAmplitude, abs_div,
    abs_of_pos hsqrtPos]
  calc
    |exactPrincipalMoleculeBoundaryModeCoefficient S X a eps| /
        Real.sqrt 2 ≤ 1 / Real.sqrt 2 := by
      exact div_le_div_of_nonneg_right hcoeff hsqrtPos.le
    _ ≤ 1 := (div_le_one hsqrtPos).2 hsqrt


/- Source slice: ExactBoundaryFeedbackSplit.lean -/

local instance exactBoundaryFeedbackSplitSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The inverse on one actual large-prime star is additive in its source. -/

theorem largePrimeStarResolventOfVector_add
    {S : Finset ℕ} {X Y : ℕ} (target : PrimeStar.Vertex S X)
    (lambda : ℝ) (b₁ b₂ : MoleculeAmbient S X) :
    PrimeStar.largePrimeStarResolventOfVector S X Y target lambda (b₁ + b₂) =
      PrimeStar.largePrimeStarResolventOfVector S X Y target lambda b₁ +
        PrimeStar.largePrimeStarResolventOfVector S X Y target lambda b₂ := by
  classical
  unfold PrimeStar.largePrimeStarResolventOfVector
  ext v
  by_cases hvt : v = target
  · subst v
    simp only [PrimeStar.largePrimeStarDataVector_center, PiLp.add_apply,
      Finset.sum_add_distrib]
    ring
  · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X Y target
    · simp only [PrimeStar.largePrimeStarDataVector_leaf _ _ hv,
        PiLp.add_apply, Finset.sum_add_distrib]
      ring
    · simp [PrimeStar.largePrimeStarDataVector_outside _ _ hvt hv]

/-- The complete first-exit direct-sum inverse is additive in its source. -/

theorem firstExitStarResolventVector_add
    {S : Finset ℕ} {X Y : ℕ} (a : PrimeStar.Vertex S X)
    (lambda : ℝ) (b₁ b₂ : MoleculeAmbient S X) :
    PrimeStar.firstExitStarResolventVector S X Y a lambda (b₁ + b₂) =
      PrimeStar.firstExitStarResolventVector S X Y a lambda b₁ +
        PrimeStar.firstExitStarResolventVector S X Y a lambda b₂ := by
  classical
  unfold PrimeStar.firstExitStarResolventVector
  have hstar :
      (∑ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
        PrimeStar.largePrimeStarResolventOfVector S X Y k lambda
          (PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) (b₁ + b₂))) =
        (∑ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
          PrimeStar.largePrimeStarResolventOfVector S X Y k lambda
            (PrimeStar.restrictEuclideanToFinset
              (PrimeStar.largePrimeStarSupport S X Y k) b₁)) +
        ∑ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
          PrimeStar.largePrimeStarResolventOfVector S X Y k lambda
            (PrimeStar.restrictEuclideanToFinset
              (PrimeStar.largePrimeStarSupport S X Y k) b₂) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hrestrict :
        PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) (b₁ + b₂) =
          PrimeStar.restrictEuclideanToFinset
              (PrimeStar.largePrimeStarSupport S X Y k) b₁ +
            PrimeStar.restrictEuclideanToFinset
              (PrimeStar.largePrimeStarSupport S X Y k) b₂ := by
      ext v
      by_cases hv : v ∈ PrimeStar.largePrimeStarSupport S X Y k <;>
        simp [PrimeStar.restrictEuclideanToFinset_apply, hv]
    rw [hrestrict, largePrimeStarResolventOfVector_add]
  have hisolated :
      PrimeStar.restrictEuclideanToFinset
          (PrimeStar.firstExitIsolatedVertices S X Y a) (b₁ + b₂) =
        PrimeStar.restrictEuclideanToFinset
            (PrimeStar.firstExitIsolatedVertices S X Y a) b₁ +
          PrimeStar.restrictEuclideanToFinset
            (PrimeStar.firstExitIsolatedVertices S X Y a) b₂ := by
    ext v
    by_cases hv : v ∈ PrimeStar.firstExitIsolatedVertices S X Y a <;>
      simp [PrimeStar.restrictEuclideanToFinset_apply, hv]
  rw [hstar, hisolated, smul_add]
  abel

/-- Boundary vector with its mean-zero kernel removed. -/

def exactPrincipalMoleculeSignedBoundaryVector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  exactPrincipalMoleculeBoundaryVector S X a -
    exactPrincipalMoleculeBoundaryKernel S X a

/-- First-exit source generated by the signed two-mode boundary part. -/

def exactPrincipalMoleculeSignedInteriorSource
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
      (exactPrincipalMoleculeSignedBoundaryVector S X a))

/-- First-exit source generated by the boundary mean-zero component. -/

def exactPrincipalMoleculeKernelInteriorSource
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
      (exactPrincipalMoleculeBoundaryKernel S X a))

/-- Exact source decomposition before applying the target-star inverse. -/

theorem exactPrincipalMoleculeInteriorSource_eq_signed_add_kernel
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    exactPrincipalMoleculeInteriorSource S X a =
      exactPrincipalMoleculeSignedInteriorSource S X a +
        exactPrincipalMoleculeKernelInteriorSource S X a := by
  have hboundary :
      exactPrincipalMoleculeBoundaryVector S X a =
        exactPrincipalMoleculeSignedBoundaryVector S X a +
          exactPrincipalMoleculeBoundaryKernel S X a := by
    simp [exactPrincipalMoleculeSignedBoundaryVector]
  rw [exactPrincipalMoleculeInteriorSource, hboundary, map_add, map_add]
  change exactPrincipalMoleculeSignedInteriorSource S X a +
      exactPrincipalMoleculeKernelInteriorSource S X a = _
  rfl

/-- First-exit vector generated by the signed boundary modes. -/

def exactPrincipalMoleculeSignedInteriorVector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
    (exactPrincipalMoleculeRoot S X a)
    (exactPrincipalMoleculeSignedInteriorSource S X a)

/-- First-exit vector generated by the boundary mean-zero component. -/

def exactPrincipalMoleculeKernelInteriorVector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
    (exactPrincipalMoleculeRoot S X a)
    (exactPrincipalMoleculeKernelInteriorSource S X a)

/-- Once the exact target-star inverse is available, the full interior splits
into the signed main vector and the kernel-return vector. -/

theorem exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    exactPrincipalMoleculeInteriorVector S X a =
      exactPrincipalMoleculeSignedInteriorVector S X a +
        exactPrincipalMoleculeKernelInteriorVector S X a := by
  rw [exactPrincipalMoleculeInterior_eq_firstExitStarResolventVector
    hS ha hroot gamma hgamma hgap hden,
    exactPrincipalMoleculeInteriorSource_eq_signed_add_kernel,
    firstExitStarResolventVector_add]
  rfl

/-- Boundary return generated by the signed two-mode interior. -/

def exactPrincipalMoleculeSignedBoundaryFeedback
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) a
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
      (exactPrincipalMoleculeSignedInteriorVector S X a))

/-- Boundary self-return generated by the mean-zero boundary component. -/

def exactPrincipalMoleculeKernelBoundaryReturn
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) a
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
      (exactPrincipalMoleculeKernelInteriorVector S X a))

/-- Exact split of the boundary feedback into its signed main term and its
kernel-generated self-return. -/

theorem exactPrincipalMoleculeBoundaryFeedback_eq_signed_add_kernelReturn
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    exactPrincipalMoleculeBoundaryFeedback S X a =
      exactPrincipalMoleculeSignedBoundaryFeedback S X a +
        exactPrincipalMoleculeKernelBoundaryReturn S X a := by
  rw [exactPrincipalMoleculeBoundaryFeedback,
    exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel
      hS ha hroot gamma hgamma hgap hden,
    map_add, map_add]
  rfl

/-- The mean-zero leaf projection is additive. -/

theorem actualStarMeanZeroLeafVector_add
    {S : Finset ℕ} {X Y : ℕ} (a : PrimeStar.Vertex S X)
    (f g : PrimeStar.Vertex S X → ℝ) :
    actualStarMeanZeroLeafVector S X Y a (f + g) =
      actualStarMeanZeroLeafVector S X Y a f +
        actualStarMeanZeroLeafVector S X Y a g := by
  classical
  ext v
  by_cases hva : v = a
  · subst v
    simp [actualStarMeanZeroLeafVector]
  · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X Y a
    · simp only [actualStarMeanZeroLeafVector, Pi.add_apply,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hv,
        PiLp.add_apply, finsetMean, Finset.sum_add_distrib]
      ring
    · simp only [actualStarMeanZeroLeafVector, PiLp.add_apply]
      rw [PrimeStar.largePrimeStarDataVector_outside _ _ hva hv,
        PrimeStar.largePrimeStarDataVector_outside _ _ hva hv,
        PrimeStar.largePrimeStarDataVector_outside _ _ hva hv]
      simp

/-- Mean-zero form of the exact signed/self-return split. -/

theorem exactPrincipalMoleculeFeedbackKernel_eq_signed_add_kernelReturn
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeBoundaryFeedback S X a) =
      actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (exactPrincipalMoleculeSignedBoundaryFeedback S X a) +
        actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (exactPrincipalMoleculeKernelBoundaryReturn S X a) := by
  rw [exactPrincipalMoleculeBoundaryFeedback_eq_signed_add_kernelReturn
      hS ha hroot gamma hgamma hgap hden]
  change actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
      ((exactPrincipalMoleculeSignedBoundaryFeedback S X a).ofLp +
        (exactPrincipalMoleculeKernelBoundaryReturn S X a).ofLp) = _
  exact actualStarMeanZeroLeafVector_add a _ _


/- Source slice: ExactBoundarySignedSynthesis.lean -/

local instance exactBoundarySignedSynthesisLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- A normalized signed star mode is orthogonal to every mean-zero vector on
the leaves of the same nonempty star. -/

theorem real_inner_largePrimeNormalizedStarMode_actualStarMeanZeroLeafVector_eq_zero
    {S : Finset ℕ} {X Y : ℕ} {a : PrimeStar.Vertex S X}
    (eps : ℝ) (f : PrimeStar.Vertex S X → ℝ)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X Y a eps,
      actualStarMeanZeroLeafVector S X Y a f⟫_ℝ = 0 := by
  let u := PrimeStar.largePrimeEuclideanStarVector S X Y a eps
  have hleaves : (PrimeStar.largePrimeLeaves S X Y a).Nonempty :=
    Finset.card_pos.mp (by
      simpa [PrimeStar.largePrimeStarDegree] using hd)
  rw [PrimeStar.largePrimeNormalizedStarMode, NormedSpace.normalize]
  change ⟪‖u‖⁻¹ • u, actualStarMeanZeroLeafVector S X Y a f⟫_ℝ = 0
  rw [real_inner_smul_left]
  suffices ⟪u, actualStarMeanZeroLeafVector S X Y a f⟫_ℝ = 0 by
    rw [this, mul_zero]
  dsimp [u]
  rw [PrimeStar.largePrimeEuclideanStarVector_eq_starDataVector,
    actualStarMeanZeroLeafVector,
    PrimeStar.largePrimeStarDataVector_inner]
  simp only [mul_zero, zero_add]
  rw [← Finset.mul_sum, sum_sub_finsetMean_eq_zero hleaves, mul_zero]

/-- A signed star mode sees only the boundary projection of an ambient
vector. -/

theorem real_inner_largePrimeNormalizedStarMode_boundaryProjection
    {S : Finset ℕ} {X Y : ℕ} {a : PrimeStar.Vertex S X}
    (eps : ℝ) (x : MoleculeAmbient S X) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X Y a eps,
      PrimeStar.primeStarBoundaryProjection S X Y a x⟫_ℝ =
      ⟪PrimeStar.largePrimeNormalizedStarMode S X Y a eps, x⟫_ℝ := by
  classical
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hvs : v ∈ PrimeStar.largePrimeStarSupport S X Y a
  · rw [PrimeStar.primeStarBoundaryProjection_apply, if_pos hvs]
  · have hu := PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem
      (S := S) (X := X) (Y := Y) (c := a) (eps := eps) hvs
    rw [PrimeStar.primeStarBoundaryProjection_apply, if_neg hvs, hu]
    simp

/-- The exact signed boundary is its literal positive/negative Fourier
synthesis. -/

theorem exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeSignedBoundaryVector S X a =
      exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 •
          PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a 1 +
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) •
          PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a (-1) := by
  let up := PrimeStar.largePrimeNormalizedStarMode S X
    (squareRootCutoff X) a 1
  let um := PrimeStar.largePrimeNormalizedStarMode S X
    (squareRootCutoff X) a (-1)
  let vp := PrimeStar.largePrimeEuclideanStarVector S X
    (squareRootCutoff X) a 1
  let vm := PrimeStar.largePrimeEuclideanStarVector S X
    (squareRootCutoff X) a (-1)
  let alpha := starPositiveCoefficient
    (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (exactPrincipalMoleculeAmbientVector S X a a)
    (finsetMean (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
      (exactPrincipalMoleculeAmbientVector S X a)) * ‖vp‖
  let beta := starNegativeCoefficient
    (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (exactPrincipalMoleculeAmbientVector S X a a)
    (finsetMean (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
      (exactPrincipalMoleculeAmbientVector S X a)) * ‖vm‖
  have hvp : ‖vp‖ • up = vp := by
    simpa [up, vp, PrimeStar.largePrimeNormalizedStarMode] using
      (NormedSpace.norm_smul_normalize vp)
  have hvm : ‖vm‖ • um = vm := by
    simpa [um, vm, PrimeStar.largePrimeNormalizedStarMode] using
      (NormedSpace.norm_smul_normalize vm)
  have hspan : exactPrincipalMoleculeSignedBoundaryVector S X a =
      alpha • up + beta • um := by
    have hdecomp :=
      exactPrincipalMolecule_boundary_eq_signedModes_add_kernel
        (S := S) (X := X) (a := a) hd
    change exactPrincipalMoleculeBoundaryVector S X a = _ at hdecomp
    rw [exactPrincipalMoleculeSignedBoundaryVector, hdecomp]
    rw [add_sub_cancel_right]
    change _ • vp + _ • vm = alpha • up + beta • um
    rw [← hvp, ← hvm]
    simp only [smul_smul]
    dsimp [alpha, beta]
  have hupNorm : ‖up‖ = 1 := by
    exact PrimeStar.norm_largePrimeNormalizedStarMode hd
  have humNorm : ‖um‖ = 1 := by
    exact PrimeStar.norm_largePrimeNormalizedStarMode hd
  have horth : ⟪up, um⟫_ℝ = 0 := by
    exact PrimeStar.real_inner_largePrimeNormalizedStarMode_pos_neg_eq_zero hd
  have hkPlus : ⟪up, exactPrincipalMoleculeBoundaryKernel S X a⟫_ℝ = 0 := by
    exact real_inner_largePrimeNormalizedStarMode_actualStarMeanZeroLeafVector_eq_zero
      1 (exactPrincipalMoleculeAmbientVector S X a) hd
  have hkMinus : ⟪um, exactPrincipalMoleculeBoundaryKernel S X a⟫_ℝ = 0 := by
    exact real_inner_largePrimeNormalizedStarMode_actualStarMeanZeroLeafVector_eq_zero
      (-1) (exactPrincipalMoleculeAmbientVector S X a) hd
  have hboundary : exactPrincipalMoleculeBoundaryVector S X a =
      exactPrincipalMoleculeSignedBoundaryVector S X a +
        exactPrincipalMoleculeBoundaryKernel S X a := by
    simp [exactPrincipalMoleculeSignedBoundaryVector]
  have hAlpha :
      exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 = alpha := by
    rw [exactPrincipalMoleculeBoundaryModeCoefficient]
    rw [← real_inner_largePrimeNormalizedStarMode_boundaryProjection
      (1 : ℝ) (exactPrincipalMoleculeAmbientVector S X a)]
    change ⟪up, exactPrincipalMoleculeBoundaryVector S X a⟫_ℝ = alpha
    rw [hboundary, inner_add_right, hkPlus, add_zero, hspan,
      inner_add_right, real_inner_smul_right, real_inner_smul_right,
      horth, mul_zero, add_zero, real_inner_self_eq_norm_sq, hupNorm]
    simp
  have hBeta :
      exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) = beta := by
    rw [exactPrincipalMoleculeBoundaryModeCoefficient]
    rw [← real_inner_largePrimeNormalizedStarMode_boundaryProjection
      (-1 : ℝ) (exactPrincipalMoleculeAmbientVector S X a)]
    change ⟪um, exactPrincipalMoleculeBoundaryVector S X a⟫_ℝ = beta
    have horth' : ⟪um, up⟫_ℝ = 0 := by
      rw [real_inner_comm, horth]
    rw [hboundary, inner_add_right, hkMinus, add_zero, hspan,
      inner_add_right, real_inner_smul_right, real_inner_smul_right,
      horth', mul_zero, zero_add, real_inner_self_eq_norm_sq, humNorm]
    simp
  rw [hAlpha, hBeta]
  exact hspan

/-- Projecting the exact boundary Schur equation onto either signed star mode
gives the corresponding scalar displacement identity.  Together the two
choices `eps = 1` and `eps = -1` are the exact two-mode boundary system used
by the molecule analysis. -/

theorem exactPrincipalMolecule_signedMode_scalarEquation
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (eps : ℝ) (heps : eps ^ 2 = 1) :
    (exactPrincipalMoleculeRoot S X a -
        eps * moleculeStarEnergy S X a) *
        exactPrincipalMoleculeBoundaryModeCoefficient S X a eps =
      ⟪PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps,
        exactPrincipalMoleculeBoundaryFeedback S X a⟫_ℝ := by
  let L := Matrix.toEuclideanLin
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let u := PrimeStar.largePrimeNormalizedStarMode S X
    (squareRootCutoff X) a eps
  let xB := exactPrincipalMoleculeBoundaryVector S X a
  let F := exactPrincipalMoleculeBoundaryFeedback S X a
  let lambda := exactPrincipalMoleculeRoot S X a
  let signedMu := eps * moleculeStarEnergy S X a
  have hEq : lambda • xB - L xB = F := by
    simpa [lambda, xB, L, F] using
      (exactPrincipalMoleculeBoundary_shift_largePrime hS ha)
  have hLsymm : L.IsSymmetric := by
    dsimp [L]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((PrimeStar.largePrimeGraph S X
        (squareRootCutoff X)).isHermitian_adjMatrix (R := ℝ))
  have hLu : L u = signedMu • u := by
    simpa [L, u, signedMu, moleculeStarEnergy] using
      (PrimeStar.largePrime_toEuclideanLin_normalizedStarMode
        (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
        (PrimeStar.sqrtCutoff_condition X) ha heps)
  have hcoeff :
      ⟪u, xB⟫_ℝ =
        exactPrincipalMoleculeBoundaryModeCoefficient S X a eps := by
    simpa [u, xB,
      exactPrincipalMoleculeBoundaryVector,
      exactPrincipalMoleculeBoundaryModeCoefficient] using
      (real_inner_largePrimeNormalizedStarMode_boundaryProjection
        (S := S) (X := X) (Y := squareRootCutoff X) (a := a)
        eps (exactPrincipalMoleculeAmbientVector S X a))
  have hLinner : ⟪u, L xB⟫_ℝ = signedMu * ⟪u, xB⟫_ℝ := by
    rw [← hLsymm u xB, hLu, real_inner_smul_left]
  have hEqInner := congrArg (fun y : MoleculeAmbient S X ↦ ⟪u, y⟫_ℝ) hEq
  rw [inner_sub_right, real_inner_smul_right, hLinner, hcoeff] at hEqInner
  change (lambda - signedMu) *
      exactPrincipalMoleculeBoundaryModeCoefficient S X a eps =
    ⟪u, F⟫_ℝ
  calc
    (lambda - signedMu) *
        exactPrincipalMoleculeBoundaryModeCoefficient S X a eps =
      lambda * exactPrincipalMoleculeBoundaryModeCoefficient S X a eps -
        signedMu * exactPrincipalMoleculeBoundaryModeCoefficient S X a eps := by ring
    _ = ⟪u, F⟫_ℝ := hEqInner

/-- Positive-mode specialization of the exact signed boundary equation. -/

theorem exactPrincipalMolecule_negativeMode_scalarEquation
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    (exactPrincipalMoleculeRoot S X a + moleculeStarEnergy S X a) *
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) =
      ⟪PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a (-1),
        exactPrincipalMoleculeBoundaryFeedback S X a⟫_ℝ := by
  simpa only [neg_one_mul, sub_neg_eq_add] using
    (exactPrincipalMolecule_signedMode_scalarEquation hS ha (-1 : ℝ)
      (by norm_num))


/- Source slice: ExactBoundarySignedSource.lean -/

local instance exactBoundarySignedSourceSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Every normalized nonempty signed star mode has the same positive centre
coordinate, independently of its sign. -/

theorem largePrimeNormalizedStarMode_center_eq_inv_sqrt_two
    {S : Finset ℕ} {X Y : ℕ} {a : PrimeStar.Vertex S X} {eps : ℝ}
    (heps : eps ^ 2 = 1)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a) :
    PrimeStar.largePrimeNormalizedStarMode S X Y a eps a =
      (Real.sqrt 2)⁻¹ := by
  have hsq := PrimeStar.sq_largePrimeNormalizedStarMode_center heps hd
  have hcoord : 0 ≤
      PrimeStar.largePrimeNormalizedStarMode S X Y a eps a := by
    rw [PrimeStar.largePrimeNormalizedStarMode, NormedSpace.normalize]
    rw [PiLp.smul_apply, smul_eq_mul]
    have hcenter :
        PrimeStar.largePrimeEuclideanStarVector S X Y a eps a =
          Real.sqrt (PrimeStar.largePrimeStarDegree S X Y a : ℝ) := by
      simp [PrimeStar.largePrimeEuclideanStarVector]
    rw [hcenter]
    positivity
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hinvSq : ((Real.sqrt 2)⁻¹) ^ 2 = (1 : ℝ) / 2 := by
    field_simp [hsqrtPos.ne']
    nlinarith
  have hinvNonneg : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  nlinarith

/-- On a leaf, a signed normalized star mode equals its centre coordinate
divided by the signed star energy. -/

theorem largePrimeNormalizedStarMode_leaf_eq_center_div_signedEnergy
    {S : Finset ℕ} {X Y : ℕ} {a v : PrimeStar.Vertex S X} {eps : ℝ}
    (heps : eps ^ 2 = 1)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a)
    (hv : v ∈ PrimeStar.largePrimeLeaves S X Y a) :
    PrimeStar.largePrimeNormalizedStarMode S X Y a eps v =
      PrimeStar.largePrimeNormalizedStarMode S X Y a eps a /
        (eps * Real.sqrt
          (PrimeStar.largePrimeStarDegree S X Y a : ℝ)) := by
  let u := PrimeStar.largePrimeEuclideanStarVector S X Y a eps
  have heps0 : eps ≠ 0 := by
    intro hepsZero
    rw [hepsZero] at heps
    norm_num at heps
  have hsqrt0 :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X Y a : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  rw [PrimeStar.largePrimeNormalizedStarMode, NormedSpace.normalize]
  rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul]
  have hleaf : u v = eps := by
    simp [u, PrimeStar.largePrimeEuclideanStarVector,
      PrimeStar.largePrimeSignedStarVector_leaf hv]
  have hcenter : u a =
      Real.sqrt (PrimeStar.largePrimeStarDegree S X Y a : ℝ) := by
    simp [u, PrimeStar.largePrimeEuclideanStarVector]
  rw [hleaf, hcenter]
  change ‖u‖⁻¹ * eps =
    (‖u‖⁻¹ *
      Real.sqrt (PrimeStar.largePrimeStarDegree S X Y a : ℝ)) /
        (eps * Real.sqrt
          (PrimeStar.largePrimeStarDegree S X Y a : ℝ))
  apply (eq_div_iff (mul_ne_zero heps0 hsqrt0)).2
  calc
    (‖u‖⁻¹ * eps) *
        (eps * Real.sqrt
          (PrimeStar.largePrimeStarDegree S X Y a : ℝ)) =
      ‖u‖⁻¹ * eps ^ 2 *
        Real.sqrt (PrimeStar.largePrimeStarDegree S X Y a : ℝ) := by ring
    _ = ‖u‖⁻¹ *
        Real.sqrt (PrimeStar.largePrimeStarDegree S X Y a : ℝ) := by
      rw [heps]
      ring

/-- First-exit source generated by one normalized signed boundary-star mode. -/

def exactBoundaryModeInteriorSource
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) (eps : ℝ) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
      (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a eps))

/-- At the square-root cutoff, the small-prime image of a signed star mode is
already supported on the canonical first-exit compression. -/

theorem exactBoundaryModeInteriorSource_eq_smallPrime
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X} (eps : ℝ) :
    exactBoundaryModeInteriorSource S X a eps =
      Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps) := by
  classical
  ext v
  rw [exactBoundaryModeInteriorSource,
    PrimeStar.firstExitCompressionProjection_apply]
  by_cases hv : v ∈ PrimeStar.firstExitCompressionSupport S X
      (squareRootCutoff X) a
  · simp [hv]
  · have hvExit : v ∉ PrimeStar.smallPrimeFirstExitSupport S X
        (squareRootCutoff X) a := by
      intro hvExit
      exact hv
        (PrimeStar.smallPrimeFirstExitSupport_subset_firstExitCompressionSupport
          (PrimeStar.sqrtCutoff_condition X) hvExit)
    rw [if_neg hv, Matrix.toLpLin_toLp 2 2]
    exact (PrimeStar.smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
      (fun w ↦ PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a eps w)
      (fun w hw ↦
        PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hw)
      hvExit).symm

/-- At a first-exit coordinate, a signed mode source equals the mode
coordinate at its unique residual neighbour in the original star. -/

theorem exactBoundaryModeInteriorSource_apply_eq_starMode_neighbor
    {S : Finset ℕ} {X : ℕ} {a v w : PrimeStar.Vertex S X} {eps : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hw : w ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
    (hwv : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj w v) :
    exactBoundaryModeInteriorSource S X a eps v =
      PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a eps w := by
  rw [exactBoundaryModeInteriorSource_eq_smallPrime,
    Matrix.toLpLin_toLp 2 2]
  change ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ).mulVec
      (fun z ↦ PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a eps z) v = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_single w
  · intro z hz hzw
    by_cases hzStar : z ∈ PrimeStar.largePrimeStarSupport S X
        (squareRootCutoff X) a
    · have hzv : (PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).Adj z v := by
        exact (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adj_comm z v
          |>.mpr (by simpa using hz)
      have hEq := PrimeStar.unique_smallPrime_neighbor_in_largePrimeStar
        (PrimeStar.sqrtCutoff_condition X) ha hzStar hw hzv hwv
      exact False.elim (hzw hEq)
    · exact PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hzStar
  · intro hwNot
    exact False.elim (hwNot (by
      simpa using ((PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).adj_comm v w |>.mpr hwv)))

/-- Outside the literal first-exit support of the original star, a signed
mode source vanishes. -/

theorem exactBoundaryModeInteriorSource_eq_zero_of_not_mem
    {S : Finset ℕ} {X : ℕ} {a v : PrimeStar.Vertex S X} {eps : ℝ}
    (hv : v ∉ PrimeStar.smallPrimeFirstExitSupport S X
      (squareRootCutoff X) a) :
    exactBoundaryModeInteriorSource S X a eps v = 0 := by
  rw [exactBoundaryModeInteriorSource_eq_smallPrime,
    Matrix.toLpLin_toLp 2 2]
  exact PrimeStar.smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
    (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
    (fun w ↦ PrimeStar.largePrimeNormalizedStarMode S X
      (squareRootCutoff X) a eps w)
    (fun w hw ↦
      PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hw)
    hv

/-- The exact signed first-exit source is the literal Fourier synthesis of
the positive and negative normalized mode sources. -/

theorem exactPrincipalMoleculeSignedInteriorSource_eq_modeSynthesis
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeSignedInteriorSource S X a =
      exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 •
          exactBoundaryModeInteriorSource S X a 1 +
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) •
          exactBoundaryModeInteriorSource S X a (-1) := by
  rw [exactPrincipalMoleculeSignedInteriorSource,
    exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hd,
    map_add, map_smul, map_smul, map_add, map_smul, map_smul]
  simp only [exactBoundaryModeInteriorSource]


/- Source slice: ExactBoundarySignedCanonicalBlocks.lean -/

theorem restrict_exactBoundaryModeInteriorSource_eq_actualUpStar
    {S : Finset ℕ} {X q : ℕ} {a target : PrimeStar.Vertex S X}
    {eps : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (htarget : (target : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ squareRootCutoff X)
    (hup : (a : ℕ) * q = (target : ℕ)) :
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) target)
        (exactBoundaryModeInteriorSource S X a eps) =
      PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X) target
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a) := by
  classical
  ext v
  by_cases hvt : v = target
  · subst v
    have hAdj : (PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).Adj a target :=
      PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        ⟨q, hq, hqS, hqY, Or.inl hup⟩
    have hb := exactBoundaryModeInteriorSource_apply_eq_starMode_neighbor
      (eps := eps) ha (by simp [PrimeStar.largePrimeStarSupport]) hAdj
    rw [PrimeStar.restrictEuclideanToFinset_apply,
      if_pos (by simp [PrimeStar.largePrimeStarSupport]), hb]
    simp [PrimeStar.actualUpStarFirstExit]
  · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X
        (squareRootCutoff X) target
    · obtain ⟨p, hp, hpS, hYp, htp⟩ :=
        (PrimeStar.mem_largePrimeLeaves_iff_child htarget).mp hvleaf
      have hapX : (a : ℕ) * p ≤ X := by
        have hle : (a : ℕ) * p ≤ ((a : ℕ) * p) * q :=
          Nat.le_mul_of_pos_right _ hq.pos
        apply hle.trans
        calc
          ((a : ℕ) * p) * q = ((a : ℕ) * q) * p := by ac_rfl
          _ = (target : ℕ) * p := by rw [hup]
          _ = (v : ℕ) := htp
          _ ≤ X := PrimeStar.Vertex.coe_le v
      let w : PrimeStar.Vertex S X :=
        PrimeStar.vertexMulAllowedPrimeOfBound hS a p hp hpS hapX
      have hwleaf : w ∈ PrimeStar.largePrimeLeaves S X
          (squareRootCutoff X) a := by
        rw [PrimeStar.mem_largePrimeLeaves_iff_child ha]
        exact ⟨p, hp, hpS, hYp, rfl⟩
      have hwv : (PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).Adj w v := by
        apply PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        refine ⟨q, hq, hqS, hqY, Or.inl ?_⟩
        change ((a : ℕ) * p) * q = (v : ℕ)
        calc
          ((a : ℕ) * p) * q = ((a : ℕ) * q) * p := by ac_rfl
          _ = (target : ℕ) * p := by rw [hup]
          _ = (v : ℕ) := htp
      have hb := exactBoundaryModeInteriorSource_apply_eq_starMode_neighbor
        (eps := eps) ha (by simp [PrimeStar.largePrimeStarSupport, hwleaf]) hwv
      have hwcoord :=
        largePrimeNormalizedStarMode_leaf_eq_center_div_signedEnergy
          heps hd hwleaf
      rw [PrimeStar.restrictEuclideanToFinset_apply,
        if_pos (by simp [PrimeStar.largePrimeStarSupport, hvleaf]), hb,
        hwcoord, moleculeStarEnergy]
      rw [PrimeStar.actualUpStarFirstExit,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
    · have hvout : v ∉ PrimeStar.largePrimeStarSupport S X
          (squareRootCutoff X) target := by
        simp [PrimeStar.largePrimeStarSupport, hvt, hvleaf]
      rw [PrimeStar.restrictEuclideanToFinset_apply, if_neg hvout]
      exact (PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf).symm

/-- Above the cutoff, the canonical up-target is isolated and the same
signed source identity holds. -/

theorem restrict_exactBoundaryModeInteriorSource_eq_actualUpStar_isolated
    {S : Finset ℕ} {X q : ℕ} {a target : PrimeStar.Vertex S X}
    {eps : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hYtarget : squareRootCutoff X < (target : ℕ))
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ squareRootCutoff X)
    (hup : (a : ℕ) * q = (target : ℕ)) :
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) target)
        (exactBoundaryModeInteriorSource S X a eps) =
      PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X) target
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a) := by
  have hIso := PrimeStar.canonicalUpTarget_isIsolated_of_cutoff_lt
    ha (PrimeStar.sqrtCutoff_condition X) hq hqY hup hYtarget
  ext v
  by_cases hvt : v = target
  · subst v
    have hAdj : (PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).Adj a target :=
      PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        ⟨q, hq, hqS, hqY, Or.inl hup⟩
    have hb := exactBoundaryModeInteriorSource_apply_eq_starMode_neighbor
      (eps := eps) ha (by simp [PrimeStar.largePrimeStarSupport]) hAdj
    rw [PrimeStar.restrictEuclideanToFinset_apply,
      if_pos (by simp [PrimeStar.largePrimeStarSupport]), hb]
    simp [PrimeStar.actualUpStarFirstExit]
  · have hvleaf : v ∉ PrimeStar.largePrimeLeaves S X
        (squareRootCutoff X) target := by
      intro hvleaf
      exact hIso v (PrimeStar.mem_largePrimeLeaves.mp hvleaf)
    have hvout : v ∉ PrimeStar.largePrimeStarSupport S X
        (squareRootCutoff X) target := by
      simp [PrimeStar.largePrimeStarSupport, hvt, hvleaf]
    rw [PrimeStar.restrictEuclideanToFinset_apply, if_neg hvout]
    exact (PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf).symm

/-- Uniform canonical up-target identity for one signed boundary mode. -/

theorem restrict_exactBoundaryModeInteriorSource_eq_canonicalUpStar
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X} {eps : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a) :
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q))
        (exactBoundaryModeInteriorSource S X a eps) =
      PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a) := by
  have hqdata := Finset.mem_filter.mp q.property
  have hq : (q : ℕ).Prime := (Nat.mem_primesLE.mp hqdata.1).2
  have hqY : (q : ℕ) ≤ squareRootCutoff X :=
    (Nat.mem_primesLE.mp hqdata.1).1
  have hqS : (q : ℕ) ∉ S := hqdata.2.1
  by_cases htarget :
      (PrimeStar.canonicalUpTarget hS a q : ℕ) ≤ squareRootCutoff X
  · exact restrict_exactBoundaryModeInteriorSource_eq_actualUpStar
      hS ha htarget hd heps hq hqS hqY
        (PrimeStar.canonicalUpTarget_coe hS a q)
  · exact restrict_exactBoundaryModeInteriorSource_eq_actualUpStar_isolated
      ha (Nat.lt_of_not_ge htarget) hq hqS hqY
        (PrimeStar.canonicalUpTarget_coe hS a q)

/-- A down-target star carries the signed partial-leaf first-exit vector. -/

theorem restrict_exactBoundaryModeInteriorSource_eq_actualDownStar
    {S : Finset ℕ} {X q : ℕ} {a target : PrimeStar.Vertex S X}
    {eps : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (htarget : (target : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ squareRootCutoff X)
    (hdown : (target : ℕ) * q = (a : ℕ)) :
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) target)
        (exactBoundaryModeInteriorSource S X a eps) =
      PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X) target
        (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) target q)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a) := by
  classical
  ext v
  by_cases hvt : v = target
  · subst v
    have hAdj : (PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).Adj a target :=
      PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        ⟨q, hq, hqS, hqY, Or.inr hdown⟩
    have hb := exactBoundaryModeInteriorSource_apply_eq_starMode_neighbor
      (eps := eps) ha (by simp [PrimeStar.largePrimeStarSupport]) hAdj
    rw [PrimeStar.restrictEuclideanToFinset_apply,
      if_pos (by simp [PrimeStar.largePrimeStarSupport]), hb]
    simp [PrimeStar.actualDownStarFirstExit]
  · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X
        (squareRootCutoff X) target
    · obtain ⟨p, hp, hpS, hYp, htp⟩ :=
        (PrimeStar.mem_largePrimeLeaves_iff_child htarget).mp hvleaf
      by_cases hvP : v ∈ PrimeStar.canonicalDownLeaves S X
          (squareRootCutoff X) target q
      · have hvqX : (v : ℕ) * q ≤ X :=
          (Finset.mem_filter.mp hvP).2
        let w : PrimeStar.Vertex S X :=
          PrimeStar.vertexMulAllowedPrimeOfBound hS v q hq hqS hvqX
        have hwleaf : w ∈ PrimeStar.largePrimeLeaves S X
            (squareRootCutoff X) a := by
          rw [PrimeStar.mem_largePrimeLeaves_iff_child ha]
          refine ⟨p, hp, hpS, hYp, ?_⟩
          change (a : ℕ) * p = (v : ℕ) * q
          calc
            (a : ℕ) * p = ((target : ℕ) * q) * p := by rw [hdown]
            _ = ((target : ℕ) * p) * q := by ac_rfl
            _ = (v : ℕ) * q := by rw [htp]
        have hwv : (PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).Adj w v := by
          apply PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
          exact ⟨q, hq, hqS, hqY, Or.inr rfl⟩
        have hb := exactBoundaryModeInteriorSource_apply_eq_starMode_neighbor
          (eps := eps) ha
            (by simp [PrimeStar.largePrimeStarSupport, hwleaf]) hwv
        have hwcoord :=
          largePrimeNormalizedStarMode_leaf_eq_center_div_signedEnergy
            heps hd hwleaf
        rw [PrimeStar.restrictEuclideanToFinset_apply,
          if_pos (by simp [PrimeStar.largePrimeStarSupport, hvleaf]), hb,
          hwcoord, moleculeStarEnergy]
        rw [PrimeStar.actualDownStarFirstExit,
          PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf, if_pos hvP]
      · have hvNotExit : v ∉ PrimeStar.smallPrimeFirstExitSupport S X
            (squareRootCutoff X) a := by
          intro hvExit
          obtain ⟨w, hwStar, hwv⟩ :=
            PrimeStar.mem_smallPrimeFirstExitSupport.mp hvExit
          rw [PrimeStar.mem_largePrimeStarSupport] at hwStar
          rcases hwStar with hwc | hcw
          · obtain ⟨ell, hell, _hellS, _hellY, hEdge⟩ :=
              PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hwv
            exact PrimeStar.no_prime_step_between_primeStepNeighbors
              (PrimeStar.Vertex.coe_pos target) (PrimeStar.Vertex.coe_pos a)
              (PrimeStar.Vertex.coe_pos v) hq hp hell
              (Or.inl hdown) (Or.inl htp) (by simpa [hwc] using hEdge)
          · obtain ⟨r, hr, _hrS, hYr, hcr, hrv⟩ :=
              PrimeStar.exists_largePrimeLabel_dvd_of_smallPrimeAdj_child
                (PrimeStar.isLargePrimeChild_of_largePrimeAdj_of_le ha hcw) hwv
            have hpv : p ∣ (v : ℕ) :=
              ⟨(target : ℕ), by simpa [Nat.mul_comm] using htp.symm⟩
            have hrp : r = p := PrimeStar.largePrime_dvd_unique
              (PrimeStar.Vertex.coe_pos v) (PrimeStar.Vertex.coe_le v)
              (PrimeStar.sqrtCutoff_condition X) hr hp hYr hYp hrv hpv
            have hvqX : (v : ℕ) * q ≤ X := by
              calc
                (v : ℕ) * q = ((target : ℕ) * p) * q := by rw [htp]
                _ = ((target : ℕ) * q) * p := by ac_rfl
                _ = (a : ℕ) * p := by rw [hdown]
                _ = (a : ℕ) * r := by rw [hrp]
                _ = (w : ℕ) := hcr
                _ ≤ X := PrimeStar.Vertex.coe_le w
            exact hvP (Finset.mem_filter.mpr ⟨hvleaf, hvqX⟩)
        have hb0 :=
          exactBoundaryModeInteriorSource_eq_zero_of_not_mem
            (eps := eps) hvNotExit
        rw [PrimeStar.restrictEuclideanToFinset_apply,
          if_pos (by simp [PrimeStar.largePrimeStarSupport, hvleaf]), hb0]
        rw [PrimeStar.actualDownStarFirstExit,
          PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf, if_neg hvP]
    · have hvout : v ∉ PrimeStar.largePrimeStarSupport S X
          (squareRootCutoff X) target := by
        simp [PrimeStar.largePrimeStarSupport, hvt, hvleaf]
      rw [PrimeStar.restrictEuclideanToFinset_apply, if_neg hvout]
      exact (PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf).symm

/-- Uniform signed canonical down-target identity. -/

theorem restrict_exactBoundaryModeInteriorSource_eq_canonicalDownStar
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X} {eps : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1)
    (q : PrimeStar.CanonicalDownIndex a) :
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q))
        (exactBoundaryModeInteriorSource S X a eps) =
      PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q)
        (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) q)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a) := by
  have hq : (q : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors q.property
  have hqDvd : (q : ℕ) ∣ (a : ℕ) :=
    Nat.dvd_of_mem_primeFactors q.property
  have hqS : (q : ℕ) ∉ S := by
    intro hqMem
    exact PrimeStar.Vertex.not_dvd_of_mem a hqMem hqDvd
  have hqY : (q : ℕ) ≤ squareRootCutoff X :=
    (Nat.le_of_mem_primeFactors q.property).trans ha
  have htarget :
      (PrimeStar.canonicalDownTarget a q : ℕ) ≤ squareRootCutoff X := by
    change (a : ℕ) / q ≤ squareRootCutoff X
    exact (Nat.div_le_self _ _).trans ha
  exact restrict_exactBoundaryModeInteriorSource_eq_actualDownStar
    hS ha htarget hd heps hq hqS hqY
      (PrimeStar.canonicalDownTarget_mul_coe a q)

/-- A signed boundary-mode source is exactly the direct sum of its canonical
arithmetic up-target and down-target blocks. -/

theorem exactBoundaryModeInteriorSource_eq_sum_canonicalBlocks
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X} {eps : ℝ}
    (hS : ∀ p ∈ S, p.Prime)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1) :
    exactBoundaryModeInteriorSource S X a eps =
      (∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
        PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q)
          (eps * moleculeStarEnergy S X a)
          (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a eps a)) +
      (∑ q : PrimeStar.CanonicalDownIndex a,
        PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q)
          (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q) q)
          (eps * moleculeStarEnergy S X a)
          (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a eps a)) := by
  calc
    exactBoundaryModeInteriorSource S X a eps =
        ∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
          PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
              (PrimeStar.canonicalExitTarget hS a i))
            (exactBoundaryModeInteriorSource S X a eps) :=
      PrimeStar.euclidean_eq_sum_canonicalExitStarBlocks hS
        (PrimeStar.sqrtCutoff_condition X) ha hd _
          (fun v hv ↦
            exactBoundaryModeInteriorSource_eq_zero_of_not_mem
              (eps := eps) hv)
    _ =
        (∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
          PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
              (PrimeStar.canonicalUpTarget hS a q))
            (exactBoundaryModeInteriorSource S X a eps)) +
        (∑ q : PrimeStar.CanonicalDownIndex a,
          PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
              (PrimeStar.canonicalDownTarget a q))
            (exactBoundaryModeInteriorSource S X a eps)) := by
      exact Fintype.sum_sum_type _
    _ = _ := by
      congr 1
      · apply Finset.sum_congr rfl
        intro q _hq
        exact restrict_exactBoundaryModeInteriorSource_eq_canonicalUpStar
          hS ha hd heps q
      · apply Finset.sum_congr rfl
        intro q _hq
        exact restrict_exactBoundaryModeInteriorSource_eq_canonicalDownStar
          hS ha hd heps q


/- Source slice: PrimeInverseSquareTail.lean -/

def allowedPrimeInverseSquareInterval
    (S : Finset ℕ) (Y Z : ℕ) : ℝ :=
  ∑ p ∈ PrimeStar.allowedPrimeInterval S Y Z, (p : ℝ) ^ (-2 : ℝ)

/-- Deleting prime labels can only reduce inverse-square mass. -/

theorem allowedPrimeInverseSquareInterval_le_all
    (S : Finset ℕ) (Y Z : ℕ) :
    allowedPrimeInverseSquareInterval S Y Z ≤
      ∑ p ∈ PrimeStar.allowedPrimeInterval ∅ Y Z,
        (p : ℝ) ^ (-2 : ℝ) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [PrimeStar.allowedPrimeInterval, Finset.mem_filter,
      Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1, by simp, hp.2.2⟩
  · intro p _hp _hpnot
    positivity

/-- The full prime interval is a difference of the two outgoing prime-power
prefix sums. -/

theorem sum_allowedPrimeInterval_empty_inv_sq_eq_sub
    {Y Z : ℕ} (hYZ : Y ≤ Z) :
    (∑ p ∈ PrimeStar.allowedPrimeInterval ∅ Y Z,
        (p : ℝ) ^ (-2 : ℝ)) =
      PrimeStar.outgoingPrimePowerSum Z 2 -
        PrimeStar.outgoingPrimePowerSum Y 2 := by
  rw [PrimeStar.outgoingPrimePowerSum, PrimeStar.outgoingPrimePowerSum]
  have hsubset : Nat.primesLE Y ⊆ Nat.primesLE Z := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_mem_primesLE hp).trans hYZ, Nat.prime_of_mem_primesLE hp⟩
  rw [← Finset.sum_sdiff hsubset]
  have hfin : PrimeStar.allowedPrimeInterval ∅ Y Z =
      Nat.primesLE Z \ Nat.primesLE Y := by
    ext p
    simp only [PrimeStar.allowedPrimeInterval, Finset.mem_filter,
      Nat.mem_primesLE, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hpZ, hpPrime⟩, _hpEmpty, hpY⟩
      exact ⟨⟨hpZ, hpPrime⟩, fun hp ↦ (Nat.not_lt_of_ge hp.1) hpY⟩
    · rintro ⟨⟨hpZ, hpPrime⟩, hpnot⟩
      exact ⟨⟨hpZ, hpPrime⟩, by simp,
        Nat.lt_of_not_ge fun h ↦ hpnot ⟨h, hpPrime⟩⟩
  rw [hfin]
  ring

/-- Exact Abel formula for a full inverse-square prime interval. -/

theorem sum_allowedPrimeInterval_empty_inv_sq_eq_abel
    {Y Z : ℕ} (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    (∑ p ∈ PrimeStar.allowedPrimeInterval ∅ Y Z,
        (p : ℝ) ^ (-2 : ℝ)) =
      (Z : ℝ) ^ (-2 : ℝ) * Nat.primeCounting Z -
        (Y : ℝ) ^ (-2 : ℝ) * Nat.primeCounting Y +
        2 * ∫ t in (Y : ℝ)..Z,
          t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊ := by
  rw [sum_allowedPrimeInterval_empty_inv_sq_eq_sub hYZ,
    PrimeStar.outgoingPrimePowerSum_eq_abel (hY.trans hYZ) 2,
    PrimeStar.outgoingPrimePowerSum_eq_abel hY 2]
  have hYreal : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hYZreal : (Y : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hYZ
  let f : ℝ → ℝ := fun t ↦
    t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊
  have hpiMeas : Measurable
      (fun t : ℝ ↦ (Nat.primeCounting ⌊t⌋₊ : ℝ)) :=
    (measurable_of_countable
      (fun n : ℕ ↦ (Nat.primeCounting n : ℝ))).comp
        measurable_id.nat_floor
  have hfIntegrableOnIcc (U : ℝ) (hU : 2 ≤ U) :
      MeasureTheory.IntegrableOn f (Set.Icc 2 U) := by
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const
        (C := U + 1) measure_Icc_lt_top.ne)
    · apply AEStronglyMeasurable.mul
      · exact (continuousOn_of_forall_continuousAt (fun t ht ↦
          Real.continuousAt_rpow_const t (-3 : ℝ)
            (Or.inl (by linarith [ht.1])))).aestronglyMeasurable
          measurableSet_Icc
      · exact hpiMeas.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have htpos : 0 < t := by linarith [ht.1]
      have hpowNonneg : 0 ≤ t ^ (-3 : ℝ) := Real.rpow_nonneg htpos.le _
      have hpowLe : t ^ (-3 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by norm_num)
      have hpi := PrimeStar.primeCounting_floor_le_add_one t htpos.le
      have hpiU : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ U + 1 :=
        hpi.trans (by linarith [ht.2])
      have hpiNonneg : 0 ≤ (Nat.primeCounting ⌊t⌋₊ : ℝ) := Nat.cast_nonneg _
      change |t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊| ≤ U + 1
      rw [abs_of_nonneg (mul_nonneg hpowNonneg hpiNonneg)]
      exact (mul_le_mul_of_nonneg_right hpowLe hpiNonneg).trans
        (by simpa using hpiU)
  have hIntY : IntervalIntegrable
      f
      MeasureTheory.volume 2 Y := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hYreal]
    exact (hfIntegrableOnIcc Y hYreal).mono_set Set.Ioc_subset_Icc_self
  have hIntYZ : IntervalIntegrable f MeasureTheory.volume Y Z := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hYZreal]
    exact (hfIntegrableOnIcc Z (hYreal.trans hYZreal)).mono_set (by
      intro t ht
      exact ⟨hYreal.trans ht.1.le, ht.2⟩)
  have hsetY :
      (∫ t in Set.Ioc (2 : ℝ) Y, f t) = ∫ t in (2 : ℝ)..Y, f t := by
    symm
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      if_pos hYreal, Set.uIoc_of_le hYreal]
    simp
  have hsetZ :
      (∫ t in Set.Ioc (2 : ℝ) Z, f t) = ∫ t in (2 : ℝ)..Z, f t := by
    have h2Z : (2 : ℝ) ≤ (Z : ℝ) := hYreal.trans hYZreal
    symm
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      if_pos h2Z, Set.uIoc_of_le h2Z]
    simp
  rw [show -(2 : ℝ) = (-2 : ℝ) by norm_num,
    show -(2 : ℝ) - 1 = (-3 : ℝ) by norm_num]
  change
    (Z : ℝ) ^ (-2 : ℝ) * Nat.primeCounting Z +
          2 * (∫ t in Set.Ioc (2 : ℝ) Z, f t) -
        ((Y : ℝ) ^ (-2 : ℝ) * Nat.primeCounting Y +
          2 * ∫ t in Set.Ioc (2 : ℝ) Y, f t) = _
  rw [hsetY, hsetZ,
    ← intervalIntegral.integral_add_adjacent_intervals hIntY hIntYZ]
  ring

/-- Chebyshev pointwise majorant for the inverse-square Abel integrand on
`[Y,∞)`. -/

theorem inverseSquareAbelIntegrand_le
    {Y t : ℝ} (hY : 1 < Y) (hYt : Y ≤ t) :
    t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊ ≤
      (2 * Real.log 4 / Real.log Y) * t ^ (-2 : ℝ) +
        t ^ (-(5 / 2 : ℝ)) := by
  have hYpos : 0 < Y := zero_lt_one.trans hY
  have htpos : 0 < t := hYpos.trans_le hYt
  have hbase : 1 < Y ^ 2 := by nlinarith
  have hsqrt : √(Y ^ 2) ≤ t := by
    rw [Real.sqrt_sq hYpos.le]
    exact hYt
  have hpi := PrimeStar.primeCounting_floor_le_on_sqrt_interval hbase hsqrt
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hcoef : 4 * Real.log 4 / Real.log (Y ^ 2) =
      2 * Real.log 4 / Real.log Y := by
    rw [Real.log_pow]
    norm_num
    field_simp
    ring
  rw [hcoef] at hpi
  have hpow : 0 ≤ t ^ (-3 : ℝ) := Real.rpow_nonneg htpos.le _
  have hmul := mul_le_mul_of_nonneg_left hpi hpow
  calc
    t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊ ≤
        t ^ (-3 : ℝ) *
          ((2 * Real.log 4 / Real.log Y) * t + √t) := hmul
    _ = (2 * Real.log 4 / Real.log Y) * t ^ (-2 : ℝ) +
        t ^ (-(5 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      have hmain : t ^ (-3 : ℝ) * t = t ^ (-2 : ℝ) := by
        calc
          t ^ (-3 : ℝ) * t = t ^ (-3 : ℝ) * t ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = t ^ ((-3 : ℝ) + 1) := by rw [Real.rpow_add htpos]
          _ = t ^ (-2 : ℝ) := by norm_num
      have herr : t ^ (-3 : ℝ) * t ^ (1 / 2 : ℝ) =
          t ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add htpos]
        congr 1
        norm_num
      rw [mul_add, herr]
      congr 1
      calc
        t ^ (-3 : ℝ) * ((2 * Real.log 4 / Real.log Y) * t) =
            (2 * Real.log 4 / Real.log Y) *
              (t ^ (-3 : ℝ) * t) := by ring
        _ = (2 * Real.log 4 / Real.log Y) * t ^ (-2 : ℝ) := by rw [hmain]

/-- Integral of `t^{-2}` over a positive finite tail. -/

theorem integral_rpow_neg_two_le
    {Y Z : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z) :
    (∫ t in Y..Z, t ^ (-2 : ℝ)) ≤ Y ^ (-1 : ℝ) := by
  rw [integral_rpow (Or.inr ⟨by norm_num,
    by simp [Set.uIcc_of_le hYZ, not_le.mpr hY]⟩)]
  have hZnonneg : 0 ≤ Z ^ (-1 : ℝ) :=
    Real.rpow_nonneg (hY.le.trans hYZ) _
  norm_num
  linarith

/-- Integral of `t^{-5/2}` over a positive finite tail. -/

theorem integral_rpow_neg_five_halves_le
    {Y Z : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z) :
    (∫ t in Y..Z, t ^ (-(5 / 2 : ℝ))) ≤
      2 * Y ^ (-(3 / 2 : ℝ)) := by
  rw [integral_rpow (Or.inr ⟨by norm_num,
    by simp [Set.uIcc_of_le hYZ, not_le.mpr hY]⟩)]
  norm_num
  have hZnonneg : 0 ≤ Z ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg (hY.le.trans hYZ) _
  have hYnonneg : 0 ≤ Y ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hY.le _
  calc
    (Z ^ (-(3 / 2 : ℝ)) - Y ^ (-(3 / 2 : ℝ))) /
          (-(3 / 2 : ℝ)) =
        (2 / 3 : ℝ) *
          (Y ^ (-(3 / 2 : ℝ)) - Z ^ (-(3 / 2 : ℝ))) := by ring
    _ ≤ (2 / 3 : ℝ) * Y ^ (-(3 / 2 : ℝ)) := by nlinarith
    _ ≤ 2 * Y ^ (-(3 / 2 : ℝ)) := by nlinarith

/-- The inverse-square Abel integrand is integrable on every positive compact
interval. -/

theorem inverseSquareAbelIntegrand_intervalIntegrable
    {Y Z : ℝ} (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    IntervalIntegrable
      (fun t : ℝ ↦ t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊)
      MeasureTheory.volume Y Z := by
  let f : ℝ → ℝ := fun t ↦
    t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊
  have hpiMeas : Measurable
      (fun t : ℝ ↦ (Nat.primeCounting ⌊t⌋₊ : ℝ)) :=
    (measurable_of_countable
      (fun n : ℕ ↦ (Nat.primeCounting n : ℝ))).comp
        measurable_id.nat_floor
  rw [intervalIntegrable_iff, Set.uIoc_of_le hYZ]
  apply MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const
      (C := Z + 1) measure_Ioc_lt_top.ne)
  · apply AEStronglyMeasurable.mul
    · exact (continuousOn_of_forall_continuousAt (fun t ht ↦
        Real.continuousAt_rpow_const t (-3 : ℝ)
          (Or.inl (by linarith [ht.1])))).aestronglyMeasurable
        measurableSet_Ioc
    · exact hpiMeas.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := zero_lt_one.trans_le hY |>.trans ht.1
    have hpowNonneg : 0 ≤ t ^ (-3 : ℝ) := Real.rpow_nonneg htpos.le _
    have hpowLe : t ^ (-3 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hY.trans ht.1.le) (by norm_num)
    have hpi := PrimeStar.primeCounting_floor_le_add_one t htpos.le
    have hpiZ : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ Z + 1 :=
      hpi.trans (by linarith [ht.2])
    have hpiNonneg : 0 ≤ (Nat.primeCounting ⌊t⌋₊ : ℝ) := Nat.cast_nonneg _
    change |t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊| ≤ Z + 1
    rw [abs_of_nonneg (mul_nonneg hpowNonneg hpiNonneg)]
    exact (mul_le_mul_of_nonneg_right hpowLe hpiNonneg).trans
      (by simpa using hpiZ)

/-- A uniform finite Chebyshev bound for inverse-square allowed-prime tails.
The second term is lower order and is kept explicit so that no asymptotic
absorption is hidden in the finite statement. -/

theorem allowedPrimeInverseSquareInterval_le_chebyshev
    {S : Finset ℕ} {Y Z : ℕ} (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    allowedPrimeInverseSquareInterval S Y Z ≤
      (6 * Real.log 4 / Real.log (Y : ℝ)) * (Y : ℝ) ^ (-1 : ℝ) +
        5 * (Y : ℝ) ^ (-(3 / 2 : ℝ)) := by
  let y : ℝ := Y
  let z : ℝ := Z
  have hyNat : 1 < Y := by omega
  have hy : (1 : ℝ) < y := by
    change (1 : ℝ) < (Y : ℝ)
    exact_mod_cast hyNat
  have hypos : 0 < y := zero_lt_one.trans hy
  have hyz : y ≤ z := by
    change (Y : ℝ) ≤ (Z : ℝ)
    exact_mod_cast hYZ
  have hzpos : 0 < z := hypos.trans_le hyz
  let f : ℝ → ℝ := fun t ↦
    t ^ (-3 : ℝ) * Nat.primeCounting ⌊t⌋₊
  let g : ℝ → ℝ := fun t ↦
    (2 * Real.log 4 / Real.log y) * t ^ (-2 : ℝ) +
      t ^ (-(5 / 2 : ℝ))
  have hf : IntervalIntegrable f MeasureTheory.volume y z :=
    inverseSquareAbelIntegrand_intervalIntegrable hy.le hyz
  have hg : IntervalIntegrable g MeasureTheory.volume y z := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      exact continuousOn_of_forall_continuousAt fun t ht ↦
        Real.continuousAt_rpow_const t (-2 : ℝ)
          (Or.inl (by
            have ht' : t ∈ Set.Icc y z := by
              simpa only [Set.uIcc_of_le hyz] using ht
            have htpos : 0 < t := hypos.trans_le ht'.1
            exact htpos.ne'))
    · exact continuousOn_of_forall_continuousAt fun t ht ↦
        Real.continuousAt_rpow_const t (-(5 / 2 : ℝ))
          (Or.inl (by
            have ht' : t ∈ Set.Icc y z := by
              simpa only [Set.uIcc_of_le hyz] using ht
            have htpos : 0 < t := hypos.trans_le ht'.1
            exact htpos.ne'))
  have hInt : (∫ t in y..z, f t) ≤ ∫ t in y..z, g t := by
    apply intervalIntegral.integral_mono_on hyz hf hg
    intro t ht
    have ht' : t ∈ Set.Icc y z := by
      simpa only [Set.uIcc_of_le hyz] using ht
    exact inverseSquareAbelIntegrand_le hy ht'.1
  have hcoef : 0 ≤ 2 * Real.log 4 / Real.log y := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
      (Real.log_pos hy).le
  have hIntBound :
      (∫ t in y..z, f t) ≤
        (2 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) +
          2 * y ^ (-(3 / 2 : ℝ)) := by
    have hpowTwoInt : IntervalIntegrable (fun t : ℝ ↦ t ^ (-2 : ℝ))
        MeasureTheory.volume y z :=
      (continuousOn_of_forall_continuousAt fun t ht ↦
        Real.continuousAt_rpow_const t (-2 : ℝ)
          (Or.inl (by
            have ht' : t ∈ Set.Icc y z := by
              simpa only [Set.uIcc_of_le hyz] using ht
            exact (hypos.trans_le ht'.1).ne'))).intervalIntegrable
    have hpowFiveInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (-(5 / 2 : ℝ)))
          MeasureTheory.volume y z :=
      (continuousOn_of_forall_continuousAt fun t ht ↦
        Real.continuousAt_rpow_const t (-(5 / 2 : ℝ))
          (Or.inl (by
            have ht' : t ∈ Set.Icc y z := by
              simpa only [Set.uIcc_of_le hyz] using ht
            exact (hypos.trans_le ht'.1).ne'))).intervalIntegrable
    have hmainInt : IntervalIntegrable
        (fun t : ℝ ↦ (2 * Real.log 4 / Real.log y) * t ^ (-2 : ℝ))
        MeasureTheory.volume y z :=
      (continuousOn_const.mul
        (continuousOn_of_forall_continuousAt fun t ht ↦
          Real.continuousAt_rpow_const t (-2 : ℝ)
            (Or.inl (by
              have ht' : t ∈ Set.Icc y z := by
                simpa only [Set.uIcc_of_le hyz] using ht
              exact (hypos.trans_le ht'.1).ne')))).intervalIntegrable
    calc
      (∫ t in y..z, f t) ≤ ∫ t in y..z, g t := hInt
      _ = (2 * Real.log 4 / Real.log y) *
            (∫ t in y..z, t ^ (-2 : ℝ)) +
          ∫ t in y..z, t ^ (-(5 / 2 : ℝ)) := by
            rw [intervalIntegral.integral_add,
              intervalIntegral.integral_const_mul]
            · exact hmainInt
            · exact hpowFiveInt
      _ ≤ (2 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) +
          2 * y ^ (-(3 / 2 : ℝ)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (integral_rpow_neg_two_le hypos hyz) hcoef)
              (integral_rpow_neg_five_halves_le hypos hyz)
  have hpointZ := inverseSquareAbelIntegrand_le hy hyz
  have hendpoint :
      z ^ (-2 : ℝ) * Nat.primeCounting Z ≤
        (2 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) +
          y ^ (-(3 / 2 : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hpointZ hzpos.le
    rw [Nat.floor_natCast] at hmul
    have hzMain : z * z ^ (-3 : ℝ) = z ^ (-2 : ℝ) := by
      calc
        z * z ^ (-3 : ℝ) = z ^ (1 : ℝ) * z ^ (-3 : ℝ) := by
          rw [Real.rpow_one]
        _ = z ^ ((1 : ℝ) + (-3)) := by rw [Real.rpow_add hzpos]
        _ = z ^ (-2 : ℝ) := by norm_num
    have hzErr : z * z ^ (-(5 / 2 : ℝ)) = z ^ (-(3 / 2 : ℝ)) := by
      calc
        z * z ^ (-(5 / 2 : ℝ)) = z ^ (1 : ℝ) * z ^ (-(5 / 2 : ℝ)) := by
          rw [Real.rpow_one]
        _ = z ^ ((1 : ℝ) + (-(5 / 2 : ℝ))) := by rw [Real.rpow_add hzpos]
        _ = z ^ (-(3 / 2 : ℝ)) := by norm_num
    have hmul' :
        z ^ (-2 : ℝ) * Nat.primeCounting Z ≤
          (2 * Real.log 4 / Real.log y) * z ^ (-1 : ℝ) +
            z ^ (-(3 / 2 : ℝ)) := by
      calc
        z ^ (-2 : ℝ) * Nat.primeCounting Z =
            z * (z ^ (-3 : ℝ) * Nat.primeCounting Z) := by
              rw [← mul_assoc, hzMain]
        _ ≤ z * ((2 * Real.log 4 / Real.log y) * z ^ (-2 : ℝ) +
              z ^ (-(5 / 2 : ℝ))) := hmul
        _ = (2 * Real.log 4 / Real.log y) * z ^ (-1 : ℝ) +
              z ^ (-(3 / 2 : ℝ)) := by
                rw [mul_add, hzErr]
                have hzInv : z * z ^ (-2 : ℝ) = z ^ (-1 : ℝ) := by
                  calc
                    z * z ^ (-2 : ℝ) = z ^ (1 : ℝ) * z ^ (-2 : ℝ) := by
                      rw [Real.rpow_one]
                    _ = z ^ ((1 : ℝ) + (-2)) := by rw [Real.rpow_add hzpos]
                    _ = z ^ (-1 : ℝ) := by norm_num
                rw [← hzInv]
                ring
    exact hmul'.trans (add_le_add
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hypos hyz (by norm_num)) hcoef)
      (Real.rpow_le_rpow_of_nonpos hypos hyz (by norm_num)))
  calc
    allowedPrimeInverseSquareInterval S Y Z ≤
        ∑ p ∈ PrimeStar.allowedPrimeInterval ∅ Y Z,
          (p : ℝ) ^ (-2 : ℝ) :=
      allowedPrimeInverseSquareInterval_le_all S Y Z
    _ = z ^ (-2 : ℝ) * Nat.primeCounting Z -
        y ^ (-2 : ℝ) * Nat.primeCounting Y +
          2 * ∫ t in y..z, f t := by
      simpa [y, z, f] using
        sum_allowedPrimeInterval_empty_inv_sq_eq_abel hY hYZ
    _ ≤ z ^ (-2 : ℝ) * Nat.primeCounting Z +
          2 * ∫ t in y..z, f t := by
      have hboundary : 0 ≤ y ^ (-2 : ℝ) * Nat.primeCounting Y :=
        mul_nonneg (Real.rpow_nonneg hypos.le _) (Nat.cast_nonneg _)
      linarith
    _ ≤ ((2 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) +
          y ^ (-(3 / 2 : ℝ))) +
        2 * ((2 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) +
          2 * y ^ (-(3 / 2 : ℝ))) := by
      gcongr
    _ = (6 * Real.log 4 / Real.log (Y : ℝ)) * (Y : ℝ) ^ (-1 : ℝ) +
        5 * (Y : ℝ) ^ (-(3 / 2 : ℝ)) := by
      simp only [y]
      ring


/- Source slice: BoundaryTargetResolvent.lean -/

def shiftedActualUpStarResolvent
    (S : Finset ℕ) (X Y : ℕ) (target : PrimeStar.Vertex S X)
    (lambda mu c0 : ℝ) : MoleculeAmbient S X :=
  PrimeStar.largePrimeStarResolventOfVector S X Y target lambda
    (PrimeStar.actualUpStarFirstExit S X Y target mu c0)

/-- Every leaf of an up-target star has the same shifted-resolvent value.
The displayed coefficient is the exact algebraic form used in the
two-mode/kernel calculation. -/

theorem shiftedActualUpStarResolvent_apply_leaf
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {lambda mu c0 : ℝ} {v : PrimeStar.Vertex S X}
    (hv : v ∈ PrimeStar.largePrimeLeaves S X Y target)
    (hlambda : lambda ≠ 0) (hmu : mu ≠ 0)
    (hden : lambda ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) :
    shiftedActualUpStarResolvent S X Y target lambda mu c0 v =
      c0 * (lambda + mu) /
        (mu * (lambda ^ 2 -
          (PrimeStar.largePrimeStarDegree S X Y target : ℝ))) := by
  classical
  let d : ℝ := PrimeStar.largePrimeStarDegree S X Y target
  have hsum :
      (∑ w ∈ PrimeStar.largePrimeLeaves S X Y target,
          PrimeStar.actualUpStarFirstExit S X Y target mu c0 w) =
        d * (c0 / mu) := by
    calc
      _ = ∑ _w ∈ PrimeStar.largePrimeLeaves S X Y target, c0 / mu := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [PrimeStar.actualUpStarFirstExit,
          PrimeStar.largePrimeStarDataVector_leaf _ _ hw]
      _ = d * (c0 / mu) := by
        simp [d, PrimeStar.largePrimeStarDegree]
  have hsourceCenter :
      PrimeStar.actualUpStarFirstExit S X Y target mu c0 target = c0 := by
    rw [PrimeStar.actualUpStarFirstExit,
      PrimeStar.largePrimeStarDataVector_center]
  have hsourceLeaf :
      PrimeStar.actualUpStarFirstExit S X Y target mu c0 v = c0 / mu := by
    rw [PrimeStar.actualUpStarFirstExit,
      PrimeStar.largePrimeStarDataVector_leaf _ _ hv]
  rw [shiftedActualUpStarResolvent,
    PrimeStar.largePrimeStarResolventOfVector,
    PrimeStar.largePrimeStarDataVector_leaf _ _ hv]
  rw [hsum, hsourceCenter, hsourceLeaf]
  change (c0 / mu + (lambda * c0 + d * (c0 / mu)) /
      (lambda ^ 2 - d)) / lambda =
    c0 * (lambda + mu) / (mu * (lambda ^ 2 - d))
  have hden0 : lambda ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
  field_simp [hlambda, hmu, hden0]
  ring

/-- Inverse at `lambda` of a partial-leaf down-star first-exit vector generated
with boundary energy `mu`. -/

def shiftedActualDownStarResolvent
    (S : Finset ℕ) (X Y : ℕ) (target : PrimeStar.Vertex S X)
    (P : Finset (PrimeStar.Vertex S X)) (lambda mu c0 : ℝ) :
    MoleculeAmbient S X :=
  PrimeStar.largePrimeStarResolventOfVector S X Y target lambda
    (PrimeStar.actualDownStarFirstExit S X Y target P mu c0)

/-- Exact centre value of the shifted down-star resolvent.  Together with
`shiftedActualDownStarResolvent_apply_mem`, this supplies the two coordinates
that are projected onto a coherent output star in manuscript Lemma 9.2. -/

theorem shiftedActualDownStarResolvent_apply_mem
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {lambda mu c0 : ℝ}
    {v : PrimeStar.Vertex S X}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target)
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y target)
    (hvP : v ∈ P) :
    shiftedActualDownStarResolvent S X Y target P lambda mu c0 v =
      (c0 / mu +
          (lambda * c0 + (P.card : ℝ) * (c0 / mu)) /
            (lambda ^ 2 -
              (PrimeStar.largePrimeStarDegree S X Y target : ℝ))) /
        lambda := by
  classical
  let source := PrimeStar.actualDownStarFirstExit S X Y target P mu c0
  have hsourceCenter : source target = c0 := by
    simp [source, PrimeStar.actualDownStarFirstExit]
  have hsourceLeaf : source v = c0 / mu := by
    simp [source, PrimeStar.actualDownStarFirstExit,
      PrimeStar.largePrimeStarDataVector_leaf _ _ hvLeaf, hvP]
  have hPfilter :
      (PrimeStar.largePrimeLeaves S X Y target).filter (fun w ↦ w ∈ P) = P := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · intro hw
      exact ⟨hP hw, hw⟩
  have hsumSource :
      (∑ w ∈ PrimeStar.largePrimeLeaves S X Y target, source w) =
        (P.card : ℝ) * (c0 / mu) := by
    calc
      _ = ∑ w ∈ PrimeStar.largePrimeLeaves S X Y target,
          if w ∈ P then c0 / mu else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        simp [source, PrimeStar.actualDownStarFirstExit,
          PrimeStar.largePrimeStarDataVector_leaf _ _ hw]
      _ = _ := by
        rw [Finset.sum_ite, hPfilter]
        simp
  rw [shiftedActualDownStarResolvent,
    PrimeStar.largePrimeStarResolventOfVector,
    PrimeStar.largePrimeStarDataVector_leaf _ _ hvLeaf,
    hsourceLeaf, hsourceCenter, hsumSource]

/-- Dimensionless form of the selected-leaf response.  Here `mu` is the
source star energy, `z * mu` is the spectral parameter, and `s * mu^2` is
the degree of the down-target star.  Thus the only target-star denominator
is `z^2 - s`; a ratio belonging to a later output star is not inverted. -/

theorem shiftedActualDownStarResolvent_apply_eq_of_mem
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {lambda mu c0 : ℝ}
    {v w : PrimeStar.Vertex S X}
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y target)
    (hwLeaf : w ∈ PrimeStar.largePrimeLeaves S X Y target)
    (hvP : v ∈ P) (hwP : w ∈ P) :
    shiftedActualDownStarResolvent S X Y target P lambda mu c0 v =
      shiftedActualDownStarResolvent S X Y target P lambda mu c0 w := by
  classical
  simp only [shiftedActualDownStarResolvent,
    PrimeStar.largePrimeStarResolventOfVector]
  rw [PrimeStar.largePrimeStarDataVector_leaf _ _ hvLeaf,
    PrimeStar.largePrimeStarDataVector_leaf _ _ hwLeaf]
  have hvSource :
      PrimeStar.actualDownStarFirstExit S X Y target P mu c0 v = c0 / mu := by
    rw [PrimeStar.actualDownStarFirstExit,
      PrimeStar.largePrimeStarDataVector_leaf _ _ hvLeaf]
    simp [hvP]
  have hwSource :
      PrimeStar.actualDownStarFirstExit S X Y target P mu c0 w = c0 / mu := by
    rw [PrimeStar.actualDownStarFirstExit,
      PrimeStar.largePrimeStarDataVector_leaf _ _ hwLeaf]
    simp [hwP]
  rw [hvSource, hwSource]


/- Source slice: BoundaryIncidenceResponse.lean -/

theorem boundaryLeafExitPrimeLabels_subset_canonicalUpPrimeLabels
    {S : Finset ℕ} {X Y : ℕ} {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y) (hYY : Y * Y ≤ X) :
    boundaryLeafExitPrimeLabels S X Y leaf ⊆
      PrimeStar.canonicalUpPrimeLabels S X Y a := by
  intro q hq
  have hqData := Finset.mem_filter.mp hq
  have hqY : q ≤ Y := (Nat.mem_primesLE.mp hqData.1).1
  have haqX : (a : ℕ) * q ≤ X :=
    (Nat.mul_le_mul ha hqY).trans hYY
  exact Finset.mem_filter.mpr
    ⟨hqData.1, hqData.2.1, haqX⟩

/-- Regard an active label at one boundary leaf as the corresponding
canonical up-target index of the original centre. -/

def boundaryLeafCanonicalUpIndex
    {S : Finset ℕ} {X Y : ℕ} {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y) (hYY : Y * Y ≤ X)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf}) :
    PrimeStar.CanonicalUpIndex S X Y a :=
  ⟨q, boundaryLeafExitPrimeLabels_subset_canonicalUpPrimeLabels ha hYY q.property⟩

/-- Exact leaf coefficient contributed by one shifted canonical up-target
resolvent. -/

def shiftedCanonicalUpLeafCoefficient
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X) (lambda mu c0 : ℝ)
    (q : PrimeStar.CanonicalUpIndex S X Y a) : ℝ :=
  c0 * (lambda + mu) /
    (mu * (lambda ^ 2 -
      (PrimeStar.largePrimeStarDegree S X Y
        (PrimeStar.canonicalUpTarget hS a q) : ℝ)))

/-- A concrete molecule-window denominator gap gives the uniform
`O(mu⁻²)` coefficient scale.  The constants are deliberately generous and
are chosen only to make the later graph-specific adapter simple. -/

theorem abs_shiftedCanonicalUpLeafCoefficient_le
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X) (lambda mu c0 : ℝ)
    (q : PrimeStar.CanonicalUpIndex S X Y a)
    (hmu : 0 < mu) (hc0 : |c0| ≤ 1)
    (hlambda : |lambda| ≤ 2 * mu)
    (hgap : mu ^ 2 / 100 ≤
      |lambda ^ 2 -
        (PrimeStar.largePrimeStarDegree S X Y
          (PrimeStar.canonicalUpTarget hS a q) : ℝ)|) :
    |shiftedCanonicalUpLeafCoefficient hS a lambda mu c0 q| ≤
      300 / mu ^ 2 := by
  let gap : ℝ := lambda ^ 2 -
    (PrimeStar.largePrimeStarDegree S X Y
      (PrimeStar.canonicalUpTarget hS a q) : ℝ)
  have hmuSq : 0 < mu ^ 2 := sq_pos_of_pos hmu
  have hgapPos : 0 < |gap| := by
    have : 0 < mu ^ 2 / 100 := by positivity
    exact this.trans_le hgap
  have hsum : |lambda + mu| ≤ 3 * mu := by
    calc
      |lambda + mu| ≤ |lambda| + |mu| := abs_add_le _ _
      _ ≤ 2 * mu + mu := by
        rw [abs_of_pos hmu]
        gcongr
      _ = 3 * mu := by ring
  have hnum : |c0| * |lambda + mu| ≤ 3 * mu := by
    calc
      |c0| * |lambda + mu| ≤ 1 * (3 * mu) := by
        gcongr
      _ = 3 * mu := by ring
  have hdenPos : 0 < mu * |gap| := mul_pos hmu hgapPos
  rw [shiftedCanonicalUpLeafCoefficient, abs_div, abs_mul, abs_mul,
    abs_of_pos hmu]
  change |c0| * |lambda + mu| / (mu * |gap|) ≤ 300 / mu ^ 2
  apply (div_le_iff₀ hdenPos).2
  calc
    |c0| * |lambda + mu| ≤ 3 * mu := hnum
    _ = (300 / mu ^ 2) * (mu * (mu ^ 2 / 100)) := by
      field_simp [hmu.ne', hmuSq.ne']
      ring
    _ ≤ (300 / mu ^ 2) * (mu * |gap|) := by
      gcongr

/-- The same coefficient estimate for the negative boundary-star mode.  The
identity is the positive estimate with both spectral signs reversed. -/

theorem abs_shiftedCanonicalUpLeafCoefficient_neg_le
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X) (lambda mu c0 : ℝ)
    (q : PrimeStar.CanonicalUpIndex S X Y a)
    (hmu : 0 < mu) (hc0 : |c0| ≤ 1)
    (hlambda : |lambda| ≤ 2 * mu)
    (hgap : mu ^ 2 / 100 ≤
      |lambda ^ 2 -
        (PrimeStar.largePrimeStarDegree S X Y
          (PrimeStar.canonicalUpTarget hS a q) : ℝ)|) :
    |shiftedCanonicalUpLeafCoefficient hS a lambda (-mu) c0 q| ≤
      300 / mu ^ 2 := by
  have hneg := abs_shiftedCanonicalUpLeafCoefficient_le
    hS a (-lambda) mu c0 q hmu hc0 (by simpa using hlambda) (by
      simpa only [neg_sq] using hgap)
  have heq :
      shiftedCanonicalUpLeafCoefficient hS a lambda (-mu) c0 q =
        shiftedCanonicalUpLeafCoefficient hS a (-lambda) mu c0 q := by
    unfold shiftedCanonicalUpLeafCoefficient
    simp only [neg_sq, div_eq_mul_inv, neg_mul, inv_neg]
    ring
  simpa [heq] using hneg

/-- Leaf coefficient obtained by retaining both signed modes of the original
boundary star. -/

def shiftedCanonicalTwoModeUpLeafCoefficient
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X) (lambda mu cPlus cMinus : ℝ)
    (q : PrimeStar.CanonicalUpIndex S X Y a) : ℝ :=
  shiftedCanonicalUpLeafCoefficient hS a lambda mu cPlus q +
    shiftedCanonicalUpLeafCoefficient hS a lambda (-mu) cMinus q

/-- Uniform coefficient bound for the complete signed two-mode response. -/

theorem abs_shiftedCanonicalTwoModeUpLeafCoefficient_le
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X) (lambda mu cPlus cMinus : ℝ)
    (q : PrimeStar.CanonicalUpIndex S X Y a)
    (hmu : 0 < mu) (hcPlus : |cPlus| ≤ 1) (hcMinus : |cMinus| ≤ 1)
    (hlambda : |lambda| ≤ 2 * mu)
    (hgap : mu ^ 2 / 100 ≤
      |lambda ^ 2 -
        (PrimeStar.largePrimeStarDegree S X Y
          (PrimeStar.canonicalUpTarget hS a q) : ℝ)|) :
    |shiftedCanonicalTwoModeUpLeafCoefficient hS a lambda mu
        cPlus cMinus q| ≤ 600 / mu ^ 2 := by
  rw [shiftedCanonicalTwoModeUpLeafCoefficient]
  calc
    |shiftedCanonicalUpLeafCoefficient hS a lambda mu cPlus q +
        shiftedCanonicalUpLeafCoefficient hS a lambda (-mu) cMinus q| ≤
        |shiftedCanonicalUpLeafCoefficient hS a lambda mu cPlus q| +
          |shiftedCanonicalUpLeafCoefficient hS a lambda (-mu) cMinus q| :=
      abs_add_le _ _
    _ ≤ 300 / mu ^ 2 + 300 / mu ^ 2 := by
      gcongr
      · exact abs_shiftedCanonicalUpLeafCoefficient_le
          hS a lambda mu cPlus q hmu hcPlus hlambda hgap
      · exact abs_shiftedCanonicalUpLeafCoefficient_neg_le
          hS a lambda mu cMinus q hmu hcMinus hlambda hgap
    _ = 600 / mu ^ 2 := by ring

/-- Sum of the signed two-mode coefficients active at one boundary leaf. -/

def boundaryLeafTwoModeUpResponse
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a leaf : PrimeStar.Vertex S X) (ha : (a : ℕ) ≤ Y)
    (hYY : Y * Y ≤ X) (lambda mu cPlus cMinus : ℝ) : ℝ :=
  ∑ q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf},
    shiftedCanonicalTwoModeUpLeafCoefficient hS a lambda mu cPlus cMinus
      (boundaryLeafCanonicalUpIndex ha hYY q)

/-- Pointwise exit-count bound for the signed two-mode response. -/

theorem abs_boundaryLeafTwoModeUpResponse_le
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a leaf : PrimeStar.Vertex S X) (ha : (a : ℕ) ≤ Y)
    (hYY : Y * Y ≤ X) (lambda mu cPlus cMinus L : ℝ)
    (hcoeff : ∀ q : PrimeStar.CanonicalUpIndex S X Y a,
      |shiftedCanonicalTwoModeUpLeafCoefficient hS a lambda mu
          cPlus cMinus q| ≤ L) :
    |boundaryLeafTwoModeUpResponse hS a leaf ha hYY lambda mu
        cPlus cMinus| ≤ L * boundaryLeafExitCount S X Y leaf := by
  rw [boundaryLeafTwoModeUpResponse]
  calc
    |∑ q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf},
        shiftedCanonicalTwoModeUpLeafCoefficient hS a lambda mu
          cPlus cMinus (boundaryLeafCanonicalUpIndex ha hYY q)| ≤
        ∑ q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf},
          |shiftedCanonicalTwoModeUpLeafCoefficient hS a lambda mu
            cPlus cMinus (boundaryLeafCanonicalUpIndex ha hYY q)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf}, L := by
      exact Finset.sum_le_sum fun q _hq ↦
        hcoeff (boundaryLeafCanonicalUpIndex ha hYY q)
    _ = L * boundaryLeafExitCount S X Y leaf := by
      simp [boundaryLeafExitCount, mul_comm]

/-- A constant leaf contribution disappears after projection to the mean-zero
kernel of the boundary star. -/

theorem actualStarMeanZeroLeafVector_add_const
    {S : Finset ℕ} {X Y : ℕ} (a : PrimeStar.Vertex S X)
    (f : PrimeStar.Vertex S X → ℝ) (C : ℝ) :
    actualStarMeanZeroLeafVector S X Y a (fun v ↦ f v + C) =
      actualStarMeanZeroLeafVector S X Y a f := by
  classical
  ext v
  by_cases hvc : v = a
  · subst v
    simp [actualStarMeanZeroLeafVector]
  · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X Y a
    · simp only [actualStarMeanZeroLeafVector,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
      simp only [finsetMean, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul]
      have hcard : (PrimeStar.largePrimeLeaves S X Y a).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨v, hvleaf⟩
      have hcardReal :
          ((PrimeStar.largePrimeLeaves S X Y a).card : ℝ) ≠ 0 := by
        exact_mod_cast hcard
      field_simp [hcardReal]
      ring
    · simp only [actualStarMeanZeroLeafVector,
        PrimeStar.largePrimeStarDataVector_outside _ _ hvc hvleaf]

/-- Sum of the exact up-target leaf coefficients active at one boundary
leaf. -/

theorem norm_sq_actualStarMeanZeroLeafVector_le_of_abs_le_count
    {S : Finset ℕ} {X Y : ℕ} {a : PrimeStar.Vertex S X}
    (f : PrimeStar.Vertex S X → ℝ) (n : PrimeStar.Vertex S X → ℕ)
    (L : ℝ)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a)
    (hL : 0 ≤ L)
    (hpoint : ∀ v ∈ PrimeStar.largePrimeLeaves S X Y a,
      |f v| ≤ L * n v) :
    ‖actualStarMeanZeroLeafVector S X Y a f‖ ^ 2 ≤
      L ^ 2 * ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a, (n v : ℝ) ^ 2 := by
  have hleaves : (PrimeStar.largePrimeLeaves S X Y a).Nonempty :=
    Finset.card_pos.mp (by
      simpa [PrimeStar.largePrimeStarDegree] using hd)
  rw [← real_inner_self_eq_norm_sq]
  simp only [actualStarMeanZeroLeafVector,
    PrimeStar.largePrimeStarDataVector_inner, zero_mul, zero_add]
  have hvariance :
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y a,
          (f v - finsetMean (PrimeStar.largePrimeLeaves S X Y a) f) ^ 2) ≤
        ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a, f v ^ 2 :=
    sum_sq_sub_finsetMean_le_sum_sq hleaves f
  calc
    (∑ v ∈ PrimeStar.largePrimeLeaves S X Y a,
        (f v - finsetMean (PrimeStar.largePrimeLeaves S X Y a) f) *
          (f v - finsetMean (PrimeStar.largePrimeLeaves S X Y a) f)) ≤
        ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a, f v ^ 2 := by
      simpa only [pow_two] using hvariance
    _ ≤ ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a,
          (L * (n v : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      have hrhs : 0 ≤ L * (n v : ℝ) :=
        mul_nonneg hL (Nat.cast_nonneg _)
      have habs := hpoint v hv
      simpa only [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg (f v)) hrhs).2 habs)
    _ = L ^ 2 * ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a,
          (n v : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      ring

/-- Boundary-kernel mass of the complete signed two-mode response. -/

theorem norm_sq_boundaryLeafTwoModeUpResponseKernel_le
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X) (ha : (a : ℕ) ≤ Y)
    (hYY : Y * Y ≤ X) (lambda mu cPlus cMinus L C : ℝ)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a)
    (hL : 0 ≤ L)
    (hcoeff : ∀ q : PrimeStar.CanonicalUpIndex S X Y a,
      |shiftedCanonicalTwoModeUpLeafCoefficient hS a lambda mu
          cPlus cMinus q| ≤ L) :
    ‖actualStarMeanZeroLeafVector S X Y a (fun v ↦
        boundaryLeafTwoModeUpResponse hS a v ha hYY lambda mu
          cPlus cMinus + C)‖ ^ 2 ≤
      L ^ 2 * (boundaryLeafCountSquareSumOnStar S X Y a : ℝ) := by
  rw [actualStarMeanZeroLeafVector_add_const]
  have hbound := norm_sq_actualStarMeanZeroLeafVector_le_of_abs_le_count
    (a := a)
    (fun v ↦ boundaryLeafTwoModeUpResponse hS a v ha hYY lambda mu
      cPlus cMinus)
    (boundaryLeafExitCount S X Y) L hd hL
    (fun v _hv ↦ abs_boundaryLeafTwoModeUpResponse_le
      hS a v ha hYY lambda mu cPlus cMinus L hcoeff)
  simpa only [boundaryLeafCountSquareSumOnStar, Nat.cast_sum, Nat.cast_pow]
    using hbound

/-- The assembled up-target response has boundary-kernel mass controlled by
the literal boundary-leaf square-count budget.  An arbitrary constant may be
added, so the theorem also absorbs the down-target contribution once its
leaf constancy is identified. -/


/- Source slice: BoundaryIncidenceBridge.lean -/

local instance boundaryIncidenceSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The endpoint obtained by following one active small-prime label from a
boundary leaf. -/

def boundaryLeafExitVertex
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (leaf : PrimeStar.Vertex S X)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf}) :
    PrimeStar.Vertex S X := by
  have hqData := Finset.mem_filter.mp q.property
  exact PrimeStar.vertexMulAllowedPrimeOfBound hS leaf q
    ((Nat.mem_primesLE.mp hqData.1).2) hqData.2.1 hqData.2.2

@[simp]

theorem boundaryLeafExitVertex_coe
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (leaf : PrimeStar.Vertex S X)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf}) :
    (boundaryLeafExitVertex hS leaf q : ℕ) = (leaf : ℕ) * (q : ℕ) :=
  rfl

/-- The arithmetic exit endpoint is joined to its boundary leaf by the active
small-prime label. -/

theorem boundaryLeafExitVertex_smallPrimeAdj
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (leaf : PrimeStar.Vertex S X)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf}) :
    (PrimeStar.smallPrimeGraph S X Y).Adj leaf
      (boundaryLeafExitVertex hS leaf q) := by
  have hqData := Finset.mem_filter.mp q.property
  apply PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
  exact ⟨q, (Nat.mem_primesLE.mp hqData.1).2, hqData.2.1,
    (Nat.mem_primesLE.mp hqData.1).1, Or.inl rfl⟩

/-- At a genuine square-root cutoff, an active exit from a boundary leaf
forces the corresponding up-target `a*q` to remain below the cutoff. -/

theorem boundaryLeafCanonicalUpTarget_le_cutoff
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y) (hYY : Y * Y ≤ X)
    (hcut : X < (Y + 1) * (Y + 1))
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf}) :
    (PrimeStar.canonicalUpTarget hS a
      (boundaryLeafCanonicalUpIndex ha hYY q) : ℕ) ≤ Y := by
  obtain ⟨p, hpPrime, hpS, hYp, hap⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hleaf
  have hqData := Finset.mem_filter.mp q.property
  have hexitBound : (leaf : ℕ) * (q : ℕ) ≤ X := hqData.2.2
  by_contra hnot
  have htargetSucc : Y + 1 ≤
      (PrimeStar.canonicalUpTarget hS a
        (boundaryLeafCanonicalUpIndex ha hYY q) : ℕ) := by
    omega
  have hpSucc : Y + 1 ≤ p := by omega
  have hsq : (Y + 1) * (Y + 1) ≤
      (PrimeStar.canonicalUpTarget hS a
        (boundaryLeafCanonicalUpIndex ha hYY q) : ℕ) * p :=
    Nat.mul_le_mul htargetSucc hpSucc
  have hproduct :
      (PrimeStar.canonicalUpTarget hS a
        (boundaryLeafCanonicalUpIndex ha hYY q) : ℕ) * p =
        (leaf : ℕ) * (q : ℕ) := by
    rw [PrimeStar.canonicalUpTarget_coe]
    change (a : ℕ) * (q : ℕ) * p = (leaf : ℕ) * (q : ℕ)
    rw [← hap]
    ac_rfl
  exact (Nat.not_lt_of_ge (hsq.trans (hproduct ▸ hexitBound))) hcut

/-- The endpoint of an active boundary exit is literally a large-prime leaf
of the corresponding canonical up-target. -/

theorem boundaryLeafExitVertex_mem_canonicalUpLeaves
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y) (hYY : Y * Y ≤ X)
    (hcut : X < (Y + 1) * (Y + 1))
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf}) :
    boundaryLeafExitVertex hS leaf q ∈
      PrimeStar.largePrimeLeaves S X Y
        (PrimeStar.canonicalUpTarget hS a
          (boundaryLeafCanonicalUpIndex ha hYY q)) := by
  obtain ⟨p, hpPrime, hpS, hYp, hap⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hleaf
  have htargetY := boundaryLeafCanonicalUpTarget_le_cutoff
    hS ha hYY hcut hleaf q
  rw [PrimeStar.mem_largePrimeLeaves_iff_child htargetY]
  refine ⟨p, hpPrime, hpS, hYp, ?_⟩
  rw [PrimeStar.canonicalUpTarget_coe, boundaryLeafExitVertex_coe]
  change (a : ℕ) * (q : ℕ) * p = (leaf : ℕ) * (q : ℕ)
  rw [← hap]
  ac_rfl

/-- Hence the literal exit endpoint belongs to the canonical first-exit
compression of the original boundary star. -/


/- Source slice: ExactBoundaryFeedbackRow.lean -/

local instance exactBoundaryFeedbackSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Literal outgoing/incoming decomposition of the exact first-exit feedback
at a boundary leaf. -/

theorem sum_outgoingSmallPrimeNeighbors_eq_boundaryLeafExitVertices
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (leaf : PrimeStar.Vertex S X) (f : PrimeStar.Vertex S X → ℝ) :
    (∑ v ∈ PrimeStar.outgoingSmallPrimeNeighbors (Y := Y) leaf, f v) =
      ∑ q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf},
        f (boundaryLeafExitVertex hS leaf q) := by
  classical
  symm
  apply Finset.sum_bij
      (fun q _hq ↦ boundaryLeafExitVertex hS leaf q)
  · intro q _hq
    rw [PrimeStar.outgoingSmallPrimeNeighbors, Finset.mem_filter]
    constructor
    · simpa using boundaryLeafExitVertex_smallPrimeAdj hS leaf q
    · have hqPrime : (q : ℕ).Prime :=
        (Nat.mem_primesLE.mp (Finset.mem_filter.mp q.property).1).2
      simpa [boundaryLeafExitVertex_coe] using
        (Nat.mul_lt_mul_left (PrimeStar.Vertex.coe_pos leaf)).mpr
          hqPrime.one_lt
  · intro q _hq r _hr hqr
    have hmul : (leaf : ℕ) * (q : ℕ) = (leaf : ℕ) * (r : ℕ) := by
      simpa [boundaryLeafExitVertex_coe] using
        congrArg (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) hqr
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left
      (PrimeStar.Vertex.coe_pos leaf) hmul)
  · intro v hv
    have hvData := Finset.mem_filter.mp hv
    have hvAdj : (PrimeStar.smallPrimeGraph S X Y).Adj leaf v := by
      simpa using hvData.1
    obtain ⟨p, hpPrime, hpS, hpY, hpv⟩ :=
      PrimeStar.smallPrimeAdj_of_lt hvData.2
        (PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hvAdj)
    have hpBound : (leaf : ℕ) * p ≤ X := by
      rw [hpv]
      exact PrimeStar.Vertex.coe_le v
    have hpLabels : p ∈ boundaryLeafExitPrimeLabels S X Y leaf := by
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hpY, hpPrime⟩, hpS, hpBound⟩
    let q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X Y leaf} :=
      ⟨p, hpLabels⟩
    refine ⟨q, Finset.mem_univ q, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    simpa [q, boundaryLeafExitVertex_coe] using hpv
  · intro q _hq
    rfl

/-- The exact feedback row with its outgoing half written in the canonical
up-target coordinates.  The remaining incoming sum is precisely the finite
down-target contribution. -/

def boundaryLeafDownVertex
    {S : Finset ℕ} {X Y : ℕ} {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y)
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (q : PrimeStar.CanonicalDownIndex a) : PrimeStar.Vertex S X := by
  have hqDvdA : (q : ℕ) ∣ (a : ℕ) :=
    Nat.dvd_of_mem_primeFactors q.property
  have haDvdLeaf : (a : ℕ) ∣ (leaf : ℕ) := by
    obtain ⟨p, _hpPrime, _hpS, _hYp, hap⟩ :=
      (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hleaf
    exact ⟨p, hap.symm⟩
  have hqDvdLeaf : (q : ℕ) ∣ (leaf : ℕ) := dvd_trans hqDvdA haDvdLeaf
  have hqPos : 0 < (q : ℕ) := Nat.pos_of_mem_primeFactors q.property
  have hqLeLeaf : (q : ℕ) ≤ (leaf : ℕ) :=
    Nat.le_of_dvd (PrimeStar.Vertex.coe_pos leaf) hqDvdLeaf
  exact PrimeStar.vertexDivisorOfDvd leaf (Nat.div_pos hqLeLeaf hqPos)
    (Nat.div_dvd_of_dvd hqDvdLeaf)

@[simp]

theorem boundaryLeafDownVertex_coe
    {S : Finset ℕ} {X Y : ℕ} {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y)
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (q : PrimeStar.CanonicalDownIndex a) :
    (boundaryLeafDownVertex ha hleaf q : ℕ) = (leaf : ℕ) / (q : ℕ) := by
  unfold boundaryLeafDownVertex
  rw [PrimeStar.vertexDivisorOfDvd_coe]

@[simp]

theorem boundaryLeafDownVertex_mul_coe
    {S : Finset ℕ} {X Y : ℕ} {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y)
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (q : PrimeStar.CanonicalDownIndex a) :
    (boundaryLeafDownVertex ha hleaf q : ℕ) * (q : ℕ) = (leaf : ℕ) := by
  rw [boundaryLeafDownVertex_coe]
  apply Nat.div_mul_cancel
  have hqDvdA : (q : ℕ) ∣ (a : ℕ) :=
    Nat.dvd_of_mem_primeFactors q.property
  obtain ⟨p, _hpPrime, _hpS, _hYp, hap⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hleaf
  exact dvd_trans hqDvdA ⟨p, hap.symm⟩

/-- The canonical down vertex is literally an incoming small-prime neighbour
of the boundary leaf. -/

theorem boundaryLeafDownVertex_mem_incomingSmallPrimeNeighbors
    {S : Finset ℕ} {X Y : ℕ}
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y)
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (q : PrimeStar.CanonicalDownIndex a) :
    boundaryLeafDownVertex ha hleaf q ∈
      PrimeStar.incomingSmallPrimeNeighbors (Y := Y) leaf := by
  have hqPrime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
  have hqDvdA : (q : ℕ) ∣ (a : ℕ) :=
    Nat.dvd_of_mem_primeFactors q.property
  have hqS : (q : ℕ) ∉ S := by
    intro hqMem
    exact a.2.2 q hqMem hqDvdA
  have hqY : (q : ℕ) ≤ Y :=
    (Nat.le_of_mem_primeFactors q.property).trans ha
  have hadj : (PrimeStar.smallPrimeGraph S X Y).Adj leaf
      (boundaryLeafDownVertex ha hleaf q) := by
    apply PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
    exact ⟨q, hqPrime, hqS, hqY,
      Or.inr (boundaryLeafDownVertex_mul_coe ha hleaf q)⟩
  have hlt : (boundaryLeafDownVertex ha hleaf q : ℕ) < (leaf : ℕ) := by
    have hpos := PrimeStar.Vertex.coe_pos
      (boundaryLeafDownVertex ha hleaf q)
    have hmul := (Nat.mul_lt_mul_left hpos).mpr hqPrime.one_lt
    calc
      (boundaryLeafDownVertex ha hleaf q : ℕ) <
          (boundaryLeafDownVertex ha hleaf q : ℕ) * (q : ℕ) := by
        simpa using hmul
      _ = (leaf : ℕ) := boundaryLeafDownVertex_mul_coe ha hleaf q
  exact Finset.mem_filter.mpr ⟨by simpa using hadj, hlt⟩

/-- The same incoming neighbour is a selected leaf of the canonical down-star
at `a/q`. -/

theorem boundaryLeafDownVertex_mem_canonicalDownLeaves
    {S : Finset ℕ} {X Y : ℕ}
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y)
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (q : PrimeStar.CanonicalDownIndex a) :
    boundaryLeafDownVertex ha hleaf q ∈
      PrimeStar.canonicalDownLeaves S X Y
        (PrimeStar.canonicalDownTarget a q) q := by
  obtain ⟨p, hpPrime, hpS, hYp, hap⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hleaf
  have htargetY : (PrimeStar.canonicalDownTarget a q : ℕ) ≤ Y := by
    exact (Nat.div_le_self _ _).trans ha
  have hchildEq :
      (PrimeStar.canonicalDownTarget a q : ℕ) * p =
        (boundaryLeafDownVertex ha hleaf q : ℕ) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_mem_primeFactors q.property)
    calc
      (PrimeStar.canonicalDownTarget a q : ℕ) * p * (q : ℕ) =
          ((PrimeStar.canonicalDownTarget a q : ℕ) * (q : ℕ)) * p := by
        ac_rfl
      _ = (a : ℕ) * p := by rw [PrimeStar.canonicalDownTarget_mul_coe]
      _ = (leaf : ℕ) := hap
      _ = (boundaryLeafDownVertex ha hleaf q : ℕ) * (q : ℕ) :=
        (boundaryLeafDownVertex_mul_coe ha hleaf q).symm
  apply Finset.mem_filter.mpr
  constructor
  · rw [PrimeStar.mem_largePrimeLeaves_iff_child htargetY]
    exact ⟨p, hpPrime, hpS, hYp, hchildEq⟩
  · rw [boundaryLeafDownVertex_mul_coe]
    exact PrimeStar.Vertex.coe_le leaf

/-- Reindex the incoming half of a boundary-leaf row by the distinct prime
divisors of the original centre. -/

theorem sum_incomingSmallPrimeNeighbors_eq_boundaryLeafDownVertices
    {S : Finset ℕ} {X Y : ℕ}
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ Y)
    (hleaf : leaf ∈ PrimeStar.largePrimeLeaves S X Y a)
    (f : PrimeStar.Vertex S X → ℝ) :
    (∑ v ∈ PrimeStar.incomingSmallPrimeNeighbors (Y := Y) leaf, f v) =
      ∑ q : PrimeStar.CanonicalDownIndex a,
        f (boundaryLeafDownVertex ha hleaf q) := by
  classical
  symm
  apply Finset.sum_bij (fun q _hq ↦ boundaryLeafDownVertex ha hleaf q)
  · intro q _hq
    exact boundaryLeafDownVertex_mem_incomingSmallPrimeNeighbors ha hleaf q
  · intro q _hq r _hr hqr
    have hmul :
        (boundaryLeafDownVertex ha hleaf q : ℕ) * (q : ℕ) =
          (boundaryLeafDownVertex ha hleaf r : ℕ) * (r : ℕ) := by
      rw [boundaryLeafDownVertex_mul_coe, boundaryLeafDownVertex_mul_coe]
    have hbase : boundaryLeafDownVertex ha hleaf q =
        boundaryLeafDownVertex ha hleaf r := hqr
    have hbaseCoe : (boundaryLeafDownVertex ha hleaf q : ℕ) =
        (boundaryLeafDownVertex ha hleaf r : ℕ) :=
      congrArg (fun z : PrimeStar.Vertex S X ↦ (z : ℕ)) hbase
    rw [hbaseCoe] at hmul
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left
      (PrimeStar.Vertex.coe_pos (boundaryLeafDownVertex ha hleaf r)) hmul)
  · intro v hv
    have hvData := Finset.mem_filter.mp hv
    have hvAdj : (PrimeStar.smallPrimeGraph S X Y).Adj leaf v := by
      simpa using hvData.1
    obtain ⟨p, hpPrime, _hpS, hpY, hpv⟩ :=
      PrimeStar.smallPrimeAdj_of_gt hvData.2
        (PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hvAdj)
    obtain ⟨r, hrPrime, _hrS, hYr, har⟩ :=
      (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hleaf
    have hpDvdProd : p ∣ (a : ℕ) * r := by
      refine ⟨(v : ℕ), ?_⟩
      calc
        (a : ℕ) * r = (leaf : ℕ) := har
        _ = (v : ℕ) * p := hpv.symm
        _ = p * (v : ℕ) := Nat.mul_comm _ _
    have hpDvdA : p ∣ (a : ℕ) := by
      rcases hpPrime.dvd_mul.mp hpDvdProd with hpa | hpr
      · exact hpa
      · have hprEq : p = r :=
          (Nat.prime_dvd_prime_iff_eq hpPrime hrPrime).mp hpr
        have : r ≤ Y := hprEq ▸ hpY
        exact False.elim ((not_le_of_gt hYr) this)
    have hpFactors : p ∈ (a : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpDvdA, (PrimeStar.Vertex.coe_pos a).ne'⟩
    let q : PrimeStar.CanonicalDownIndex a := ⟨p, hpFactors⟩
    refine ⟨q, Finset.mem_univ q, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    apply Nat.eq_of_mul_eq_mul_right hpPrime.pos
    calc
      (boundaryLeafDownVertex ha hleaf q : ℕ) * p = (leaf : ℕ) := by
        simpa [q] using boundaryLeafDownVertex_mul_coe ha hleaf q
      _ = (v : ℕ) * p := hpv.symm
  · intro q _hq
    rfl

/-- Fully canonical up/down reindexing of the exact boundary feedback row. -/


/- Source slice: ExactBoundaryKernelEstimate.lean -/

theorem actualStarMeanZeroLeafVector_congr_on_leaves
    {S : Finset ℕ} {X Y : ℕ} {a : PrimeStar.Vertex S X}
    {f g : PrimeStar.Vertex S X → ℝ}
    (hfg : ∀ v ∈ PrimeStar.largePrimeLeaves S X Y a, f v = g v) :
    actualStarMeanZeroLeafVector S X Y a f =
      actualStarMeanZeroLeafVector S X Y a g := by
  classical
  have hmean :
      finsetMean (PrimeStar.largePrimeLeaves S X Y a) f =
        finsetMean (PrimeStar.largePrimeLeaves S X Y a) g := by
    unfold finsetMean
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    exact hfg v hv
  ext v
  by_cases hva : v = a
  · subst v
    simp [actualStarMeanZeroLeafVector]
  · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X Y a
    · simp only [actualStarMeanZeroLeafVector,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hv]
      rw [hfg v hv, hmean]
    · simp only [actualStarMeanZeroLeafVector]
      rw [PrimeStar.largePrimeStarDataVector_outside _ _ hva hv,
        PrimeStar.largePrimeStarDataVector_outside _ _ hva hv]

/-- Exact squared-norm form of the boundary-kernel estimate.  The scalar on
the left is the literal continuation root, not an assumed star energy. -/

theorem scalar_smul_norm_sq_le_four_main_of_half_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lambda : ℝ) (k main err : E)
    (heq : lambda • k = main + err)
    (herr : ‖err‖ ≤ |lambda| / 2 * ‖k‖) :
    lambda ^ 2 * ‖k‖ ^ 2 ≤ 4 * ‖main‖ ^ 2 := by
  have hsum : |lambda| * ‖k‖ ≤ ‖main‖ + ‖err‖ := by
    calc
      |lambda| * ‖k‖ = ‖lambda • k‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ = ‖main + err‖ := by rw [heq]
      _ ≤ ‖main‖ + ‖err‖ := norm_add_le _ _
  have hx : |lambda| * ‖k‖ ≤ 2 * ‖main‖ := by
    nlinarith [norm_nonneg k, norm_nonneg main, norm_nonneg err,
      abs_nonneg lambda]
  have hsq := (sq_le_sq₀
    (mul_nonneg (abs_nonneg lambda) (norm_nonneg k))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg main))).2 hx
  calc
    lambda ^ 2 * ‖k‖ ^ 2 = (|lambda| * ‖k‖) ^ 2 := by
      rw [mul_pow, sq_abs]
    _ ≤ (2 * ‖main‖) ^ 2 := hsq
    _ = 4 * ‖main‖ ^ 2 := by ring

/-- Full signed boundary-kernel estimate with a self-consistent error return.
The main term is the explicit two-mode response, while `err` is the response
generated by the boundary mean-zero component itself. -/

theorem exactPrincipalMoleculeRoot_sq_mul_norm_sq_boundaryKernel_twoMode_le_of_half_error
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (mu cPlus cMinus L C : ℝ) (hL : 0 ≤ L)
    (err : MoleculeAmbient S X)
    (hcoeff : ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      |shiftedCanonicalTwoModeUpLeafCoefficient hS a
          (exactPrincipalMoleculeRoot S X a) mu cPlus cMinus q| ≤ L)
    (hfeedback :
      actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (exactPrincipalMoleculeBoundaryFeedback S X a) =
        actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (fun v ↦ boundaryLeafTwoModeUpResponse hS a v ha (Nat.sqrt_le X)
            (exactPrincipalMoleculeRoot S X a) mu cPlus cMinus + C) + err)
    (herr : ‖err‖ ≤ |exactPrincipalMoleculeRoot S X a| / 2 *
      ‖exactPrincipalMoleculeBoundaryKernel S X a‖) :
    exactPrincipalMoleculeRoot S X a ^ 2 *
        ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 ≤
      4 * L ^ 2 * (boundaryLeafCountSquareSumOnStar S X
        (squareRootCutoff X) a : ℝ) := by
  let main : MoleculeAmbient S X :=
    actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
      (fun v ↦ boundaryLeafTwoModeUpResponse hS a v ha (Nat.sqrt_le X)
        (exactPrincipalMoleculeRoot S X a) mu cPlus cMinus + C)
  have hschur :=
    exactPrincipalMoleculeRoot_smul_boundaryKernel_eq_feedbackKernel
      hS ha hd
  have heq : exactPrincipalMoleculeRoot S X a •
        exactPrincipalMoleculeBoundaryKernel S X a = main + err := by
    rw [hschur, hfeedback]
  have habsorb := scalar_smul_norm_sq_le_four_main_of_half_error
    (exactPrincipalMoleculeRoot S X a)
    (exactPrincipalMoleculeBoundaryKernel S X a) main err heq herr
  have hmain := norm_sq_boundaryLeafTwoModeUpResponseKernel_le
    hS a ha (Nat.sqrt_le X)
    (exactPrincipalMoleculeRoot S X a) mu cPlus cMinus L C hd hL hcoeff
  calc
    exactPrincipalMoleculeRoot S X a ^ 2 *
        ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 ≤
      4 * ‖main‖ ^ 2 := habsorb
    _ ≤ 4 * (L ^ 2 * (boundaryLeafCountSquareSumOnStar S X
        (squareRootCutoff X) a : ℝ)) := by gcongr
    _ = 4 * L ^ 2 * (boundaryLeafCountSquareSumOnStar S X
        (squareRootCutoff X) a : ℝ) := by ring


/- Source slice: ExactBoundarySignedResponse.lean -/

local instance exactBoundarySignedResponseSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance exactBoundarySignedResponseLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Coordinate copy of the normalized positive mode on the original boundary
star.  The exact molecule contains that entire star, so this is the reference
mode for its continuation-ranked root. -/

def exactBoundaryModeInteriorVector
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) (eps : ℝ) :
    MoleculeAmbient S X :=
  PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
    (exactPrincipalMoleculeRoot S X a)
    (exactBoundaryModeInteriorSource S X a eps)

/-- One normalized signed boundary mode pays at most one application of the
small-prime operator when it enters the first-exit sector. -/

theorem norm_exactBoundaryModeInteriorSource_le_smallPrime
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X} {eps eta : ℝ}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1) (heta : 0 ≤ eta)
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖) :
    ‖exactBoundaryModeInteriorSource S X a eps‖ ≤ eta := by
  rw [exactBoundaryModeInteriorSource_eq_smallPrime]
  calc
    ‖Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps)‖ ≤
      eta * ‖PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a eps‖ := hH _
    _ = eta := by
      rw [PrimeStar.norm_largePrimeNormalizedStarMode hd, mul_one]

/-- The explicit first-exit inverse of one signed source pays the common
shifted compression gap. -/

theorem gamma_mul_norm_exactBoundaryModeInteriorVector_le_source
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} {eps gamma : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    gamma * ‖exactBoundaryModeInteriorVector S X a eps‖ ≤
      ‖exactBoundaryModeInteriorSource S X a eps‖ := by
  let b := exactBoundaryModeInteriorSource S X a eps
  have hb : ∀ v, v ∉ PrimeStar.smallPrimeFirstExitSupport S X
      (squareRootCutoff X) a → b v = 0 := by
    intro v hv
    exact exactBoundaryModeInteriorSource_eq_zero_of_not_mem hv
  have hsolve := PrimeStar.firstExitStar_shift_resolventVector
    b (PrimeStar.sqrtCutoff_condition X) hroot hden hb
  have hxSupport : ∀ v,
      v ∉ PrimeStar.firstExitCompressionSupport S X
          (squareRootCutoff X) a →
        exactBoundaryModeInteriorVector S X a eps v = 0 := by
    intro v hv
    exact PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem b hv
  have hcompression :
      PrimeStar.firstExitLargePrimeCompressionOperator S X
          (squareRootCutoff X) a
          (exactBoundaryModeInteriorVector S X a eps) =
        Matrix.toEuclideanLin
          ((PrimeStar.largePrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactBoundaryModeInteriorVector S X a eps) :=
    PrimeStar.firstExitLargePrimeCompressionOperator_eq_of_supported
      (PrimeStar.sqrtCutoff_condition X)
      (exactBoundaryModeInteriorVector S X a eps) hxSupport
  calc
    gamma * ‖exactBoundaryModeInteriorVector S X a eps‖ ≤
        ‖exactPrincipalMoleculeRoot S X a •
            exactBoundaryModeInteriorVector S X a eps -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a
            (exactBoundaryModeInteriorVector S X a eps)‖ := hgap _
    _ = ‖b‖ := by
      rw [hcompression]
      rw [exactBoundaryModeInteriorVector]
      exact congrArg norm hsolve

/-- Every entry of the signed first-exit response matrix is bounded at the
source-weighted scale `eta^2 / gamma`. -/

theorem abs_exactBoundaryMode_sourceResponse_le_smallPrime
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} {eps tau gamma eta : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1) (htau : tau ^ 2 = 1)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖) :
    |⟪exactBoundaryModeInteriorSource S X a eps,
        exactBoundaryModeInteriorVector S X a tau⟫_ℝ| ≤
      eta ^ 2 / gamma := by
  have hsourceEps := norm_exactBoundaryModeInteriorSource_le_smallPrime
    hd heps heta hH
  have hsourceTau := norm_exactBoundaryModeInteriorSource_le_smallPrime
    hd htau heta hH
  have hvector := gamma_mul_norm_exactBoundaryModeInteriorVector_le_source
    hS ha hroot hgap hden (eps := tau)
  have hvector' : ‖exactBoundaryModeInteriorVector S X a tau‖ ≤
      eta / gamma := by
    apply (le_div_iff₀ hgamma).2
    simpa [mul_comm] using hvector.trans hsourceTau
  calc
    |⟪exactBoundaryModeInteriorSource S X a eps,
        exactBoundaryModeInteriorVector S X a tau⟫_ℝ| ≤
      ‖exactBoundaryModeInteriorSource S X a eps‖ *
        ‖exactBoundaryModeInteriorVector S X a tau‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ eta * (eta / gamma) := by gcongr
    _ = eta ^ 2 / gamma := by ring

/-- Source-weighted first-resolvent comparison for the positive signed
boundary source.  Both inverses are the literal first-exit direct-sum
resolvents; the estimate is therefore ready to compare the shifted molecule
response with the unshifted arithmetic correction. -/

theorem abs_boundaryMode_positiveResponse_sub_le_smallPrime
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} {lambda mu gammaLambda gammaMu eta : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hlambda : lambda ≠ 0) (hmu : mu ≠ 0)
    (hgammaLambda : 0 < gammaLambda) (hgammaMu : 0 < gammaMu)
    (heta : 0 ≤ eta)
    (hgapLambda : ∀ x : MoleculeAmbient S X,
      gammaLambda * ‖x‖ ≤
        ‖lambda • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hgapMu : ∀ x : MoleculeAmbient S X,
      gammaMu * ‖x‖ ≤
        ‖mu • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hdenLambda : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      lambda ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (hdenMu : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      mu ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖) :
    |⟪exactBoundaryModeInteriorSource S X a 1,
        PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          lambda (exactBoundaryModeInteriorSource S X a 1)⟫_ℝ -
      ⟪exactBoundaryModeInteriorSource S X a 1,
        PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          mu (exactBoundaryModeInteriorSource S X a 1)⟫_ℝ| ≤
      |lambda - mu| * (eta / gammaLambda) * (eta / gammaMu) := by
  let C := PrimeStar.firstExitLargePrimeCompressionOperator S X
    (squareRootCutoff X) a
  let b := exactBoundaryModeInteriorSource S X a 1
  let Rlambda := PrimeStar.firstExitLargePrimeResolventOfGap S X
    (squareRootCutoff X) a lambda gammaLambda hgammaLambda hgapLambda
  let Rmu := PrimeStar.firstExitLargePrimeResolventOfGap S X
    (squareRootCutoff X) a mu gammaMu hgammaMu hgapMu
  have hbSupport : ∀ v, v ∉ PrimeStar.smallPrimeFirstExitSupport S X
      (squareRootCutoff X) a → b v = 0 := by
    intro v hv
    exact exactBoundaryModeInteriorSource_eq_zero_of_not_mem hv
  have hRlambda : Rlambda b =
      PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
        lambda b := by
    dsimp [Rlambda]
    exact PrimeStar.firstExitLargePrimeResolventOfGap_apply_eq_firstExitStarResolventVector
      b (PrimeStar.sqrtCutoff_condition X) hlambda hdenLambda hbSupport
        hgammaLambda hgapLambda
  have hRmu : Rmu b =
      PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
        mu b := by
    dsimp [Rmu]
    exact PrimeStar.firstExitLargePrimeResolventOfGap_apply_eq_firstExitStarResolventVector
      b (PrimeStar.sqrtCutoff_condition X) hmu hdenMu hbSupport
        hgammaMu hgapMu
  have hbNorm : ‖b‖ ≤ eta := by
    dsimp [b]
    exact norm_exactBoundaryModeInteriorSource_le_smallPrime
      hd (by norm_num) heta hH
  have hRlambdaNorm : ‖Rlambda b‖ ≤ eta / gammaLambda := by
    have hnorm := PrimeStar.norm_finiteResolventOfGap_apply_le
      C lambda gammaLambda hgammaLambda hgapLambda b
    change ‖Rlambda b‖ ≤ gammaLambda⁻¹ * ‖b‖ at hnorm
    calc
      ‖Rlambda b‖ ≤ gammaLambda⁻¹ * ‖b‖ := hnorm
      _ ≤ gammaLambda⁻¹ * eta := by gcongr
      _ = eta / gammaLambda := by field_simp
  have hRmuNorm : ‖Rmu b‖ ≤ eta / gammaMu := by
    have hnorm := PrimeStar.norm_finiteResolventOfGap_apply_le
      C mu gammaMu hgammaMu hgapMu b
    change ‖Rmu b‖ ≤ gammaMu⁻¹ * ‖b‖ at hnorm
    calc
      ‖Rmu b‖ ≤ gammaMu⁻¹ * ‖b‖ := hnorm
      _ ≤ gammaMu⁻¹ * eta := by gcongr
      _ = eta / gammaMu := by field_simp
  have hdiff := PrimeStar.abs_inner_finiteResolventOfGap_sub_le
    C lambda mu gammaLambda gammaMu hgammaLambda hgammaMu
      hgapLambda hgapMu
      (PrimeStar.firstExitLargePrimeCompressionOperator_isSymmetric
        S X (squareRootCutoff X) a) b
  rw [show PrimeStar.finiteResolventOfGap C lambda gammaLambda
      hgammaLambda hgapLambda b = Rlambda b by rfl,
    show PrimeStar.finiteResolventOfGap C mu gammaMu
      hgammaMu hgapMu b = Rmu b by rfl,
    hRlambda, hRmu] at hdiff
  have hvectorLambda :
      ‖PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          lambda b‖ ≤ eta / gammaLambda := by
    rw [← hRlambda]
    exact hRlambdaNorm
  have hvectorMu :
      ‖PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          mu b‖ ≤ eta / gammaMu := by
    rw [← hRmu]
    exact hRmuNorm
  exact hdiff.trans (by gcongr)

/-- The complete first-exit direct-sum inverse is homogeneous in its source. -/

theorem largePrimeStarResolventOfVector_smul
    {S : Finset ℕ} {X Y : ℕ} (target : PrimeStar.Vertex S X)
    (lambda c : ℝ) (b : MoleculeAmbient S X) :
    PrimeStar.largePrimeStarResolventOfVector S X Y target lambda (c • b) =
      c • PrimeStar.largePrimeStarResolventOfVector S X Y target lambda b := by
  classical
  unfold PrimeStar.largePrimeStarResolventOfVector
  dsimp
  ext v
  have hsum :
      (∑ x ∈ PrimeStar.largePrimeLeaves S X Y target, c * b x) =
        c * ∑ x ∈ PrimeStar.largePrimeLeaves S X Y target, b x := by
    rw [Finset.mul_sum]
  by_cases hvt : v = target
  · subst v
    simp only [PrimeStar.largePrimeStarDataVector_center, PiLp.smul_apply,
      smul_eq_mul]
    rw [hsum]
    ring
  · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X Y target
    · simp only [PrimeStar.largePrimeStarDataVector_leaf _ _ hv,
        PiLp.smul_apply, smul_eq_mul]
      rw [hsum]
      ring
    · simp only [PiLp.smul_apply, smul_eq_mul]
      rw [PrimeStar.largePrimeStarDataVector_outside _ _ hvt hv,
        PrimeStar.largePrimeStarDataVector_outside _ _ hvt hv]
      simp

/-- The complete first-exit direct-sum inverse is homogeneous in its source. -/

theorem firstExitStarResolventVector_smul
    {S : Finset ℕ} {X Y : ℕ} (a : PrimeStar.Vertex S X)
    (lambda c : ℝ) (b : MoleculeAmbient S X) :
    PrimeStar.firstExitStarResolventVector S X Y a lambda (c • b) =
      c • PrimeStar.firstExitStarResolventVector S X Y a lambda b := by
  classical
  unfold PrimeStar.firstExitStarResolventVector
  have hstar :
      (∑ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
        PrimeStar.largePrimeStarResolventOfVector S X Y k lambda
          (PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) (c • b))) =
        c • (∑ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
          PrimeStar.largePrimeStarResolventOfVector S X Y k lambda
            (PrimeStar.restrictEuclideanToFinset
              (PrimeStar.largePrimeStarSupport S X Y k) b)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    have hrestrict :
        PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) (c • b) =
          c • PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) b := by
      ext v
      by_cases hv : v ∈ PrimeStar.largePrimeStarSupport S X Y k <;>
        simp [PrimeStar.restrictEuclideanToFinset_apply, hv]
    rw [hrestrict, largePrimeStarResolventOfVector_smul]
  have hisolated :
      PrimeStar.restrictEuclideanToFinset
          (PrimeStar.firstExitIsolatedVertices S X Y a) (c • b) =
        c • PrimeStar.restrictEuclideanToFinset
          (PrimeStar.firstExitIsolatedVertices S X Y a) b := by
    ext v
    by_cases hv : v ∈ PrimeStar.firstExitIsolatedVertices S X Y a <;>
      simp [PrimeStar.restrictEuclideanToFinset_apply, hv]
  rw [hstar, hisolated, smul_smul]
  module

private theorem firstExitStarResolventVector_apply_of_mem_isolated
    {S : Finset ℕ} {X Y : ℕ} {a v : PrimeStar.Vertex S X} {mu : ℝ}
    (b : MoleculeAmbient S X)
    (hv : v ∈ PrimeStar.firstExitIsolatedVertices S X Y a) :
    PrimeStar.firstExitStarResolventVector S X Y a mu b v = mu⁻¹ * b v := by
  classical
  have hblock : ∀ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
      PrimeStar.largePrimeStarResolventOfVector S X Y k mu
          (PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) b) v = 0 := by
    intro k hk
    have hvout : v ∉ PrimeStar.largePrimeStarSupport S X Y k := by
      intro hvk
      exact PrimeStar.not_isolated_of_mem_selected_largePrimeStarSupport hk hvk
        (PrimeStar.mem_firstExitIsolatedVertices.mp hv).2
    have hvk : v ≠ k := by
      intro h
      subst v
      exact hvout (by simp [PrimeStar.largePrimeStarSupport])
    have hvleaf : v ∉ PrimeStar.largePrimeLeaves S X Y k := by
      intro h
      exact hvout (by simp [PrimeStar.largePrimeStarSupport, h])
    unfold PrimeStar.largePrimeStarResolventOfVector
    exact PrimeStar.largePrimeStarDataVector_outside _ _ hvk hvleaf
  have hsum :
      ((∑ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
        PrimeStar.largePrimeStarResolventOfVector S X Y k mu
          (PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) b)) :
          MoleculeAmbient S X) v = 0 := by
    change EuclideanSpace.projₗ v
      (∑ k ∈ PrimeStar.firstExitLowerCenters S X Y a,
        PrimeStar.largePrimeStarResolventOfVector S X Y k mu
          (PrimeStar.restrictEuclideanToFinset
            (PrimeStar.largePrimeStarSupport S X Y k) b)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun k hk ↦ hblock k hk
  unfold PrimeStar.firstExitStarResolventVector
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hsum, zero_add]
  simp [PrimeStar.restrictEuclideanToFinset_apply, hv]

/-- One canonical target sees exactly its own local star inverse.  This
private adapter also covers an isolated up-target, whose inverse is scalar. -/

private theorem restrict_firstExitStarResolventVector_eq_canonicalLocal
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} {mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (ha : (a : ℕ) ≤ Y)
    (hmu : mu ≠ 0) (b : MoleculeAmbient S X)
    (i : PrimeStar.CanonicalExitIndex S X Y a) :
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X Y
          (PrimeStar.canonicalExitTarget hS a i))
        (PrimeStar.firstExitStarResolventVector S X Y a mu b) =
      PrimeStar.largePrimeStarResolventOfVector S X Y
        (PrimeStar.canonicalExitTarget hS a i) mu
        (PrimeStar.restrictEuclideanToFinset
          (PrimeStar.largePrimeStarSupport S X Y
            (PrimeStar.canonicalExitTarget hS a i)) b) := by
  classical
  let target := PrimeStar.canonicalExitTarget hS a i
  let F := PrimeStar.largePrimeStarSupport S X Y target
  rcases PrimeStar.canonicalExitTarget_mem_lower_or_isolated hS hcut ha i with
      hlower | hisolated
  · ext v
    by_cases hv : v ∈ F
    · rw [PrimeStar.restrictEuclideanToFinset_apply, if_pos hv]
      exact firstExitStarResolventVector_apply_of_mem_selectedStar
        b hcut hlower hv
    · rw [PrimeStar.restrictEuclideanToFinset_apply, if_neg hv]
      have hvt : v ≠ target := by
        intro h
        apply hv
        simp [F, target, h, PrimeStar.largePrimeStarSupport]
      have hvleaf : v ∉ PrimeStar.largePrimeLeaves S X Y target := by
        intro h
        apply hv
        simp [F, PrimeStar.largePrimeStarSupport, h]
      exact (PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf).symm
  · have htiso := (PrimeStar.mem_firstExitIsolatedVertices.mp hisolated).2
    have hd0 : PrimeStar.largePrimeStarDegree S X Y target = 0 :=
      PrimeStar.largePrimeStarDegree_eq_zero_iff.mpr htiso
    ext v
    by_cases hvt : v = target
    · subst v
      have hvI : target ∈ PrimeStar.firstExitIsolatedVertices S X Y a := by
        simpa [target] using hisolated
      have htF : target ∈ F := by
        dsimp [F]
        exact PrimeStar.mem_largePrimeStarSupport.mpr (Or.inl rfl)
      rw [PrimeStar.restrictEuclideanToFinset_apply, if_pos htF,
        firstExitStarResolventVector_apply_of_mem_isolated b hvI]
      unfold PrimeStar.largePrimeStarResolventOfVector
      rw [PrimeStar.largePrimeStarDataVector_center, hd0, Nat.cast_zero]
      have hsum :
          (∑ w ∈ PrimeStar.largePrimeLeaves S X Y target,
            PrimeStar.restrictEuclideanToFinset F b w) = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        exact False.elim (htiso w (PrimeStar.mem_largePrimeLeaves.mp hw))
      rw [hsum, add_zero, sub_zero]
      rw [PrimeStar.restrictEuclideanToFinset_apply, if_pos htF]
      change mu⁻¹ * b target = (mu * b target) / mu ^ 2
      field_simp [hmu]
    · have hvF : v ∉ F := by
        intro hv
        rw [PrimeStar.mem_largePrimeStarSupport] at hv
        exact hv.elim hvt (fun hvAdj ↦ htiso v hvAdj)
      rw [PrimeStar.restrictEuclideanToFinset_apply, if_neg hvF]
      have hvleaf : v ∉ PrimeStar.largePrimeLeaves S X Y target := by
        intro hv
        exact htiso v (PrimeStar.mem_largePrimeLeaves.mp hv)
      exact (PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf).symm

/-- The signed exact interior is the Fourier synthesis of the two signed-mode
first-exit responses. -/

theorem exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeSignedInteriorVector S X a =
      exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 •
          exactBoundaryModeInteriorVector S X a 1 +
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) •
          exactBoundaryModeInteriorVector S X a (-1) := by
  rw [exactPrincipalMoleculeSignedInteriorVector,
    exactPrincipalMoleculeSignedInteriorSource_eq_modeSynthesis hd,
    firstExitStarResolventVector_add,
    firstExitStarResolventVector_smul,
    firstExitStarResolventVector_smul]
  rfl

/-- Restricting one signed boundary response to a canonical down-star gives
the literal shifted partial-leaf resolvent on that star.  This is the
graph-facing adapter needed before the centre and leaf formulas in
`BoundaryTargetResolvent` can be used in a coherent common-core entry. -/

private theorem canonicalExitFirstExit_eq_zero_of_not_mem_starSupport
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X) (mu c0 : ℝ)
    (i : PrimeStar.CanonicalExitIndex S X Y a) {v : PrimeStar.Vertex S X}
    (hv : v ∉ PrimeStar.largePrimeStarSupport S X Y
      (PrimeStar.canonicalExitTarget hS a i)) :
    PrimeStar.canonicalExitFirstExit hS a mu c0 i v = 0 := by
  have hvt : v ≠ PrimeStar.canonicalExitTarget hS a i := by
    intro h
    apply hv
    simp [h, PrimeStar.largePrimeStarSupport]
  have hvleaf : v ∉ PrimeStar.largePrimeLeaves S X Y
      (PrimeStar.canonicalExitTarget hS a i) := by
    intro h
    apply hv
    simp [PrimeStar.largePrimeStarSupport, h]
  rcases i with q | q <;>
    exact PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf

/-- At any nonresonant spectral parameter, the signed source-response entry
is exactly the sum of the local up/down target-star responses.  Isolated
up-targets are included.  This parameterized form is used both at the exact
molecule root and at the reference star energy. -/

theorem boundaryMode_sourceResponse_eq_sum_local_at
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} {eps tau lambda : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1) (htau : tau ^ 2 = 1)
    (hroot : lambda ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖lambda • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      lambda ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    ⟪exactBoundaryModeInteriorSource S X a eps,
      PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
        lambda (exactBoundaryModeInteriorSource S X a tau)⟫_ℝ =
      ∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
        ⟪PrimeStar.largePrimeStarResolventOfVector S X (squareRootCutoff X)
            (PrimeStar.canonicalExitTarget hS a i)
            lambda
            (PrimeStar.canonicalExitFirstExit hS a
              (eps * moleculeStarEnergy S X a)
              (PrimeStar.largePrimeNormalizedStarMode S X
                (squareRootCutoff X) a eps a) i),
          PrimeStar.canonicalExitFirstExit hS a
            (tau * moleculeStarEnergy S X a)
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a tau a) i⟫_ℝ := by
  let R := PrimeStar.firstExitLargePrimeResolventOfGap S X
    (squareRootCutoff X) a lambda gamma hgamma hgap
  have hsource (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
      exactBoundaryModeInteriorSource S X a sigma =
        ∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
          PrimeStar.canonicalExitFirstExit hS a
            (sigma * moleculeStarEnergy S X a)
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a sigma a) i := by
    rw [exactBoundaryModeInteriorSource_eq_sum_canonicalBlocks
      hS ha hd hsigma]
    simp only [Fintype.sum_sum_type, PrimeStar.canonicalExitFirstExit]
  have hsupp (sigma : ℝ) (v : PrimeStar.Vertex S X)
      (hv : v ∉ PrimeStar.smallPrimeFirstExitSupport S X
        (squareRootCutoff X) a) :
      exactBoundaryModeInteriorSource S X a sigma v = 0 :=
    exactBoundaryModeInteriorSource_eq_zero_of_not_mem hv
  have hR (sigma : ℝ) :
      R (exactBoundaryModeInteriorSource S X a sigma) =
        PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          lambda (exactBoundaryModeInteriorSource S X a sigma) := by
    dsimp [R]
    exact PrimeStar.firstExitLargePrimeResolventOfGap_apply_eq_firstExitStarResolventVector
      (exactBoundaryModeInteriorSource S X a sigma)
      (PrimeStar.sqrtCutoff_condition X) hroot hden (hsupp sigma)
        hgamma hgap
  have hRsymm : R.IsSymmetric := by
    dsimp [R]
    exact PrimeStar.firstExitLargePrimeResolventOfGap_isSymmetric
      S X (squareRootCutoff X) a _ _ hgamma hgap
  calc
    ⟪exactBoundaryModeInteriorSource S X a eps,
        PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          lambda (exactBoundaryModeInteriorSource S X a tau)⟫_ℝ =
      ⟪exactBoundaryModeInteriorSource S X a eps,
        R (exactBoundaryModeInteriorSource S X a tau)⟫_ℝ := by rw [hR]
    _ = ⟪R (exactBoundaryModeInteriorSource S X a eps),
        exactBoundaryModeInteriorSource S X a tau⟫_ℝ :=
      (hRsymm _ _).symm
    _ = ⟪PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          lambda (exactBoundaryModeInteriorSource S X a eps),
        exactBoundaryModeInteriorSource S X a tau⟫_ℝ := by rw [hR]
    _ = ⟪PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          lambda (exactBoundaryModeInteriorSource S X a eps),
        ∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
          PrimeStar.canonicalExitFirstExit hS a
            (tau * moleculeStarEnergy S X a)
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a tau a) i⟫_ℝ := by rw [hsource tau htau]
    _ = ∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
        ⟪PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
            lambda (exactBoundaryModeInteriorSource S X a eps),
          PrimeStar.canonicalExitFirstExit hS a
            (tau * moleculeStarEnergy S X a)
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a tau a) i⟫_ℝ := by rw [inner_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      let F := PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
        (PrimeStar.canonicalExitTarget hS a i)
      let bt := PrimeStar.canonicalExitFirstExit hS a
        (tau * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a tau a) i
      have hbt : ∀ v, v ∉ F → bt v = 0 := by
        intro v hv
        exact canonicalExitFirstExit_eq_zero_of_not_mem_starSupport
          hS a _ _ i hv
      calc
        ⟪PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
              lambda (exactBoundaryModeInteriorSource S X a eps), bt⟫_ℝ =
            ⟪bt, PrimeStar.firstExitStarResolventVector S X
              (squareRootCutoff X) a lambda
              (exactBoundaryModeInteriorSource S X a eps)⟫_ℝ :=
          real_inner_comm _ _
        _ = ⟪bt, PrimeStar.restrictEuclideanToFinset F
            (PrimeStar.firstExitStarResolventVector S X
              (squareRootCutoff X) a lambda
              (exactBoundaryModeInteriorSource S X a eps))⟫_ℝ := by
          symm
          exact PrimeStar.inner_restrictEuclideanToFinset_right_of_supported
            F bt _ hbt
        _ = ⟪bt,
            PrimeStar.largePrimeStarResolventOfVector S X
              (squareRootCutoff X) (PrimeStar.canonicalExitTarget hS a i)
              lambda
              (PrimeStar.restrictEuclideanToFinset F
                (exactBoundaryModeInteriorSource S X a eps))⟫_ℝ := by
          change ⟪bt, PrimeStar.restrictEuclideanToFinset F
              (PrimeStar.firstExitStarResolventVector S X
                (squareRootCutoff X) a lambda
                (exactBoundaryModeInteriorSource S X a eps))⟫_ℝ = _
          rw [restrict_firstExitStarResolventVector_eq_canonicalLocal
            hS (PrimeStar.sqrtCutoff_condition X) ha hroot
            (exactBoundaryModeInteriorSource S X a eps) i]
        _ = ⟪PrimeStar.largePrimeStarResolventOfVector S X
              (squareRootCutoff X) (PrimeStar.canonicalExitTarget hS a i)
              lambda
              (PrimeStar.restrictEuclideanToFinset F
                (exactBoundaryModeInteriorSource S X a eps)), bt⟫_ℝ :=
          real_inner_comm _ _
        _ = _ := by
          rcases i with q | q
          · dsimp [F, bt, PrimeStar.canonicalExitTarget,
              PrimeStar.canonicalExitFirstExit]
            rw [restrict_exactBoundaryModeInteriorSource_eq_canonicalUpStar
              hS ha hd heps q]
          · dsimp [F, bt, PrimeStar.canonicalExitTarget,
              PrimeStar.canonicalExitFirstExit]
            rw [restrict_exactBoundaryModeInteriorSource_eq_canonicalDownStar
              hS ha hd heps q]

/-- The full signed source-response entry at the exact molecule root is the
sum of its local up/down target-star responses. -/

theorem actualUpStar_signedResponse
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {lambda mu c0 eps tau : ℝ}
    (heps : eps ^ 2 = 1) (htau : tau ^ 2 = 1)
    (hmu : mu ≠ 0) (hlambda : lambda ≠ 0)
    (hden : lambda ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    2 * mu *
        ⟪PrimeStar.actualUpStarFirstExit S X Y target (eps * mu) c0,
          PrimeStar.largePrimeStarResolventOfVector S X Y target lambda
            (PrimeStar.actualUpStarFirstExit S X Y target (tau * mu) c0)⟫_ℝ =
      (mu * lambda + (tau + eps) *
          (PrimeStar.largePrimeStarDegree S X Y target : ℝ) +
        eps * tau * (PrimeStar.largePrimeStarDegree S X Y target : ℝ) *
          lambda / mu) /
        (lambda ^ 2 -
          (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) := by
  let d : ℝ := PrimeStar.largePrimeStarDegree S X Y target
  rw [PrimeStar.actualUpStarFirstExit,
    PrimeStar.largePrimeStarResolventOfVector,
    PrimeStar.largePrimeStarDataVector_inner]
  let source := PrimeStar.largePrimeStarDataVector S X Y target c0
    (fun _ ↦ c0 / (tau * mu))
  have hsourceCenter : source target = c0 := by
    simp [source]
  have hsourceLeaf (v : PrimeStar.Vertex S X)
      (hv : v ∈ PrimeStar.largePrimeLeaves S X Y target) :
      source v = c0 / (tau * mu) := by
    exact PrimeStar.largePrimeStarDataVector_leaf _ _ hv
  have hsumSource :
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y target, source v) =
        d * (c0 / (tau * mu)) := by
    calc
      _ = ∑ _v ∈ PrimeStar.largePrimeLeaves S X Y target,
          c0 / (tau * mu) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hsourceLeaf v hv
      _ = _ := by simp [d, PrimeStar.largePrimeStarDegree]
  change 2 * mu *
      (c0 * ((lambda * source target +
          ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target, source v) /
            (lambda ^ 2 - d)) +
        ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          c0 / (eps * mu) *
            ((source v +
              (lambda * source target +
                ∑ w ∈ PrimeStar.largePrimeLeaves S X Y target, source w) /
                  (lambda ^ 2 - d)) / lambda)) = _
  rw [hsourceCenter, hsumSource]
  let zc := (lambda * c0 + d * (c0 / (tau * mu))) /
    (lambda ^ 2 - d)
  have hsumInner :
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
        c0 / (eps * mu) * ((source v + zc) / lambda)) =
      d * (c0 / (eps * mu) *
        ((c0 / (tau * mu) + zc) / lambda)) := by
    calc
      _ = ∑ _v ∈ PrimeStar.largePrimeLeaves S X Y target,
          c0 / (eps * mu) *
            ((c0 / (tau * mu) + zc) / lambda) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hsourceLeaf v hv]
      _ = _ := by simp [d, PrimeStar.largePrimeStarDegree]
  change 2 * mu * (c0 * zc +
      ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
        c0 / (eps * mu) * ((source v + zc) / lambda)) = _
  rw [hsumInner]
  dsimp [zc]
  change 2 * mu *
      (c0 * ((lambda * c0 + d * (c0 / (tau * mu))) /
          (lambda ^ 2 - d)) +
        d * (c0 / (eps * mu) *
          ((c0 / (tau * mu) +
            (lambda * c0 + d * (c0 / (tau * mu))) /
              (lambda ^ 2 - d)) / lambda))) =
    (mu * lambda + (tau + eps) * d +
      eps * tau * d * lambda / mu) / (lambda ^ 2 - d)
  have hden0 : lambda ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
  have heps0 : eps ≠ 0 := by nlinarith
  have htau0 : tau ≠ 0 := by nlinarith
  field_simp [hmu, hlambda, hden0, heps0, htau0]
  ring_nf at heps htau hc0 ⊢
  rw [heps, htau, hc0]
  ring

/-- The response of one up-target is a universal rank-one entry
`1 / (2 * lambda)` plus an explicit rational deviation.  Summing the first
term over the up-targets gives the common matrix part removed by
`twoMode_responseRemainder_eq_rankOne`. -/

theorem actualDownStar_signedResponse
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)}
    {lambda mu c0 eps tau : ℝ}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (heps : eps ^ 2 = 1) (htau : tau ^ 2 = 1)
    (hmu : mu ≠ 0) (hlambda : lambda ≠ 0)
    (hden : lambda ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    2 * mu *
        ⟪PrimeStar.actualDownStarFirstExit S X Y target P (eps * mu) c0,
          PrimeStar.largePrimeStarResolventOfVector S X Y target lambda
            (PrimeStar.actualDownStarFirstExit S X Y target P (tau * mu) c0)⟫_ℝ =
      mu *
        (lambda ^ 2 * (1 + eps * tau) +
          lambda * mu * (eps + tau) +
          eps * tau *
            (mu ^ 2 -
              (PrimeStar.largePrimeStarDegree S X Y target : ℝ))) /
        (lambda *
          (lambda ^ 2 -
            (PrimeStar.largePrimeStarDegree S X Y target : ℝ))) := by
  let d : ℝ := PrimeStar.largePrimeStarDegree S X Y target
  rw [PrimeStar.actualDownStarFirstExit,
    PrimeStar.largePrimeStarResolventOfVector,
    PrimeStar.largePrimeStarDataVector_inner]
  let source := PrimeStar.largePrimeStarDataVector S X Y target c0
    (fun v ↦ if v ∈ P then c0 / (tau * mu) else 0)
  have hsourceCenter : source target = c0 := by
    simp [source]
  have hsourceLeaf (v : PrimeStar.Vertex S X)
      (hv : v ∈ PrimeStar.largePrimeLeaves S X Y target) :
      source v = if v ∈ P then c0 / (tau * mu) else 0 := by
    exact PrimeStar.largePrimeStarDataVector_leaf _ _ hv
  have hPfilter :
      (PrimeStar.largePrimeLeaves S X Y target).filter (fun v ↦ v ∈ P) = P := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · intro hv
      exact ⟨hP hv, hv⟩
  have hsumSource :
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y target, source v) =
        mu ^ 2 * (c0 / (tau * mu)) := by
    calc
      _ = ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          if v ∈ P then c0 / (tau * mu) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hsourceLeaf v hv
      _ = _ := by
        rw [Finset.sum_ite, hPfilter]
        simp [hcard]
  change 2 * mu *
      (c0 * ((lambda * source target +
          ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target, source v) /
            (lambda ^ 2 - d)) +
        ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          (if v ∈ P then c0 / (eps * mu) else 0) *
            ((source v +
              (lambda * source target +
                ∑ w ∈ PrimeStar.largePrimeLeaves S X Y target, source w) /
                  (lambda ^ 2 - d)) / lambda)) = _
  rw [hsourceCenter, hsumSource]
  let zc := (lambda * c0 + mu ^ 2 * (c0 / (tau * mu))) /
    (lambda ^ 2 - d)
  have hsumInner :
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
        (if v ∈ P then c0 / (eps * mu) else 0) *
          ((source v + zc) / lambda)) =
      mu ^ 2 *
        ((c0 / (eps * mu)) *
          ((c0 / (tau * mu) + zc) / lambda)) := by
    calc
      _ = ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          if v ∈ P then
            (c0 / (eps * mu)) *
              ((c0 / (tau * mu) + zc) / lambda) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hsourceLeaf v hv]
        by_cases hvP : v ∈ P <;> simp [hvP]
      _ = _ := by
        rw [Finset.sum_ite, hPfilter]
        simp [hcard]
  change 2 * mu * (c0 * zc +
      ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
        (if v ∈ P then c0 / (eps * mu) else 0) *
          ((source v + zc) / lambda)) = _
  rw [hsumInner]
  dsimp [zc]
  change 2 * mu *
      (c0 * ((lambda * c0 + mu ^ 2 * (c0 / (tau * mu))) /
          (lambda ^ 2 - d)) +
        mu ^ 2 *
          ((c0 / (eps * mu)) *
            ((c0 / (tau * mu) +
              (lambda * c0 + mu ^ 2 * (c0 / (tau * mu))) /
                (lambda ^ 2 - d)) / lambda))) =
    mu *
      (lambda ^ 2 * (1 + eps * tau) +
        lambda * mu * (eps + tau) + eps * tau * (mu ^ 2 - d)) /
      (lambda * (lambda ^ 2 - d))
  have hden0 : lambda ^ 2 - d ≠ 0 := sub_ne_zero.mpr hden
  have heps0 : eps ≠ 0 := by nlinarith
  have htau0 : tau ≠ 0 := by nlinarith
  field_simp [hmu, hlambda, hden0, heps0, htau0]
  ring_nf at heps htau hc0 ⊢
  rw [heps, htau, hc0]
  ring

/-- At an isolated canonical up-target, the signed exact interior has the
literal scalar response used by the coherent common-core calculation.  The
two boundary-mode coefficients enter only through the sum of their centre
amplitudes; no target-star degree or additional denominator is present. -/

theorem real_inner_signedBoundaryFeedback_eq_sourceResponses
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (eps : ℝ) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps,
        exactPrincipalMoleculeSignedBoundaryFeedback S X a⟫_ℝ =
      exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 *
          ⟪exactBoundaryModeInteriorSource S X a eps,
            exactBoundaryModeInteriorVector S X a 1⟫_ℝ +
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) *
          ⟪exactBoundaryModeInteriorSource S X a eps,
            exactBoundaryModeInteriorVector S X a (-1)⟫_ℝ := by
  classical
  letI : DecidableRel
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
    Classical.decRel _
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let u := PrimeStar.largePrimeNormalizedStarMode S X
    (squareRootCutoff X) a eps
  have hHsymm : H.IsSymmetric := by
    dsimp [H]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).isHermitian_adjMatrix (R := ℝ))
  calc
    ⟪u, exactPrincipalMoleculeSignedBoundaryFeedback S X a⟫_ℝ =
        ⟪u, H (exactPrincipalMoleculeSignedInteriorVector S X a)⟫_ℝ := by
      rw [exactPrincipalMoleculeSignedBoundaryFeedback,
        real_inner_largePrimeNormalizedStarMode_boundaryProjection]
    _ = ⟪H u, exactPrincipalMoleculeSignedInteriorVector S X a⟫_ℝ := by
      exact (hHsymm u
        (exactPrincipalMoleculeSignedInteriorVector S X a)).symm
    _ = ⟪exactBoundaryModeInteriorSource S X a eps,
        exactPrincipalMoleculeSignedInteriorVector S X a⟫_ℝ := by
      have hsource : H u = exactBoundaryModeInteriorSource S X a eps := by
        simpa [H, u] using
          (exactBoundaryModeInteriorSource_eq_smallPrime
            (S := S) (X := X) (a := a) eps).symm
      rw [hsource]
    _ = exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 *
          ⟪exactBoundaryModeInteriorSource S X a eps,
            exactBoundaryModeInteriorVector S X a 1⟫_ℝ +
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) *
          ⟪exactBoundaryModeInteriorSource S X a eps,
            exactBoundaryModeInteriorVector S X a (-1)⟫_ℝ := by
      rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd,
        inner_add_right, real_inner_smul_right, real_inner_smul_right]

/-- The exact signed scalar equation with the two source-response entries and
the boundary-kernel return separated.  This is the literal `2 by 2` system
before estimating its negative-mode and kernel terms. -/

theorem exactPrincipalMolecule_signedMode_sourceResponseEquation
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (eps : ℝ) (heps : eps ^ 2 = 1) :
    (exactPrincipalMoleculeRoot S X a -
        eps * moleculeStarEnergy S X a) *
        exactPrincipalMoleculeBoundaryModeCoefficient S X a eps =
      exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 *
          ⟪exactBoundaryModeInteriorSource S X a eps,
            exactBoundaryModeInteriorVector S X a 1⟫_ℝ +
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) *
          ⟪exactBoundaryModeInteriorSource S X a eps,
            exactBoundaryModeInteriorVector S X a (-1)⟫_ℝ +
        ⟪PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a eps,
          exactPrincipalMoleculeKernelBoundaryReturn S X a⟫_ℝ := by
  rw [exactPrincipalMolecule_signedMode_scalarEquation hS ha eps heps,
    exactPrincipalMoleculeBoundaryFeedback_eq_signed_add_kernelReturn
      hS ha hroot gamma hgamma hgap hden,
    inner_add_right,
    real_inner_signedBoundaryFeedback_eq_sourceResponses hd]

/-- Eliminating the negative coefficient from a scalar two-mode response
system gives the cancellation-preserving squared-displacement identity.  The
identity is multiplied by the positive coefficient, so it does not assume an
overlap estimate. -/

theorem twoMode_balancedSquaredDisplacement_mul
    {lambda mu alpha beta rpp rpm rmp rmm kp km rho : ℝ}
    (hplus : (lambda - mu) * alpha = alpha * rpp + beta * rpm + kp)
    (hminus : (lambda + mu) * beta = alpha * rmp + beta * rmm + km) :
    alpha * (2 * mu * ((lambda - mu) - rho) + (lambda - mu) ^ 2) =
      kp * (lambda + mu - rmm) + rpm * km +
        alpha * (2 * mu * (rpp - rho) +
          (lambda - mu) * (rpp + rmm) + rpm * rmp - rpp * rmm) := by
  linear_combination (lambda + mu - rmm) * hplus + rpm * hminus

/-- After the common rank-one part of a two-mode response matrix is removed,
the determinant remainder contains only deviations from that common part.
This is the exact whole-form cancellation behind the molecule estimate: in
particular, no square of the common response survives. -/

theorem twoMode_responseRemainder_eq_of_rankOneBaseline
    {lambda mu u v epp epm emp emm erho : ℝ}
    (hbaseline :
      2 * mu * (u - v) + 2 * u * (lambda - mu) = 0) :
    2 * mu * ((u + epp) - (v + erho)) +
        (lambda - mu) * ((u + epp) + (u + emm)) +
        (u + epm) * (u + emp) - (u + epp) * (u + emm) =
      2 * mu * (epp - erho) +
        (lambda - mu) * (epp + emm) +
        u * (epm + emp - epp - emm) +
        epm * emp - epp * emm := by
  calc
    _ = (2 * mu * (u - v) + 2 * u * (lambda - mu)) +
        (2 * mu * (epp - erho) +
          (lambda - mu) * (epp + emm) +
          u * (epm + emp - epp - emm) +
          epm * emp - epp * emm) := by ring
    _ = _ := by rw [hbaseline]; ring

/-- The universal up-star rank-one response has value `P / (2 * lambda)` at
the shifted root and `P / (2 * mu)` at the unshifted star energy.  Its two
linear contributions cancel exactly. -/

theorem twoMode_rankOneBaseline_cancels
    {lambda mu P : ℝ} (hlambda : lambda ≠ 0) (hmu : mu ≠ 0) :
    2 * mu * (P / (2 * lambda) - P / (2 * mu)) +
        2 * (P / (2 * lambda)) * (lambda - mu) = 0 := by
  field_simp [hlambda, hmu]
  ring

/-- Specialized rank-one cancellation in the normalization used by the
signed molecule response.  All down-star terms and all non-universal up-star
terms may be placed in the five deviation variables. -/

theorem twoMode_responseRemainder_eq_rankOne
    {lambda mu P epp epm emp emm erho : ℝ}
    (hlambda : lambda ≠ 0) (hmu : mu ≠ 0) :
    2 * mu *
          ((P / (2 * lambda) + epp) - (P / (2 * mu) + erho)) +
        (lambda - mu) *
          ((P / (2 * lambda) + epp) + (P / (2 * lambda) + emm)) +
        (P / (2 * lambda) + epm) * (P / (2 * lambda) + emp) -
          (P / (2 * lambda) + epp) * (P / (2 * lambda) + emm) =
      2 * mu * (epp - erho) +
        (lambda - mu) * (epp + emm) +
        (P / (2 * lambda)) * (epm + emp - epp - emm) +
        epm * emp - epp * emm := by
  exact twoMode_responseRemainder_eq_of_rankOneBaseline
    (twoMode_rankOneBaseline_cancels hlambda hmu)

/-- The exact signed source-response equations imply the multiplied two-mode
determinant identity.  This is the algebraic joint before the separate
positive-overlap and response-remainder estimates: no division by the
positive mode coefficient and no termwise norm bound occurs here. -/

theorem exactPrincipalMolecule_balancedSquaredDisplacement_mul
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (rho : ℝ) :
    let lambda := exactPrincipalMoleculeRoot S X a
    let mu := moleculeStarEnergy S X a
    let alpha := exactPrincipalMoleculeBoundaryModeCoefficient S X a 1
    let rpp := ⟪exactBoundaryModeInteriorSource S X a 1,
      exactBoundaryModeInteriorVector S X a 1⟫_ℝ
    let rpm := ⟪exactBoundaryModeInteriorSource S X a 1,
      exactBoundaryModeInteriorVector S X a (-1)⟫_ℝ
    let rmp := ⟪exactBoundaryModeInteriorSource S X a (-1),
      exactBoundaryModeInteriorVector S X a 1⟫_ℝ
    let rmm := ⟪exactBoundaryModeInteriorSource S X a (-1),
      exactBoundaryModeInteriorVector S X a (-1)⟫_ℝ
    let kp := ⟪moleculePositiveStarMode S X a,
      exactPrincipalMoleculeKernelBoundaryReturn S X a⟫_ℝ
    let km := ⟪PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a (-1),
      exactPrincipalMoleculeKernelBoundaryReturn S X a⟫_ℝ
    alpha * (2 * mu * ((lambda - mu) - rho) + (lambda - mu) ^ 2) =
      kp * (lambda + mu - rmm) + rpm * km +
        alpha * (2 * mu * (rpp - rho) +
          (lambda - mu) * (rpp + rmm) + rpm * rmp - rpp * rmm) := by
  dsimp only
  apply twoMode_balancedSquaredDisplacement_mul
  · simpa [moleculePositiveStarMode] using
      exactPrincipalMolecule_signedMode_sourceResponseEquation
        hS ha hd hroot gamma hgamma hgap hden (1 : ℝ) (by norm_num)
  · simpa only [neg_one_mul, sub_neg_eq_add] using
      exactPrincipalMolecule_signedMode_sourceResponseEquation
        hS ha hd hroot gamma hgamma hgap hden (-1 : ℝ) (by norm_num)

/-- An active up-target reached from a boundary leaf is one of the selected
non-isolated lower stars in the first-exit compression. -/

theorem boundaryLeafCanonicalUpTarget_mem_firstExitLowerCenters
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hleaf : leaf ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X
      (squareRootCutoff X) leaf}) :
    PrimeStar.canonicalUpTarget hS a
        (boundaryLeafCanonicalUpIndex ha (Nat.sqrt_le X) q) ∈
      PrimeStar.firstExitLowerCenters S X (squareRootCutoff X) a := by
  let qi : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a :=
    boundaryLeafCanonicalUpIndex ha (Nat.sqrt_le X) q
  let target := PrimeStar.canonicalUpTarget hS a qi
  have htargetY : (target : ℕ) ≤ squareRootCutoff X := by
    exact boundaryLeafCanonicalUpTarget_le_cutoff hS ha (Nat.sqrt_le X)
      (PrimeStar.sqrtCutoff_condition X) hleaf q
  have hexit : target ∈
      PrimeStar.smallPrimeFirstExitSupport S X (squareRootCutoff X) a := by
    simpa [target, qi, PrimeStar.canonicalExitTarget] using
      (PrimeStar.canonicalExitTarget_mem_smallPrimeFirstExitSupport
        (Y := squareRootCutoff X) hS ha
          (Sum.inl qi : PrimeStar.CanonicalExitIndex S X
            (squareRootCutoff X) a))
  have hexitLeaf : boundaryLeafExitVertex hS leaf q ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target := by
    simpa [target, qi] using boundaryLeafExitVertex_mem_canonicalUpLeaves
      hS ha (Nat.sqrt_le X) (PrimeStar.sqrtCutoff_condition X) hleaf q
  have hnotIso :
      ¬(PrimeStar.largePrimeGraph S X (squareRootCutoff X)).IsIsolated
        target := by
    intro hiso
    exact hiso (boundaryLeafExitVertex hS leaf q)
      (PrimeStar.mem_largePrimeLeaves.mp hexitLeaf)
  exact PrimeStar.mem_firstExitLowerCenters.mpr
    ⟨htargetY, target, hexit, hnotIso,
      PrimeStar.mem_largePrimeStarSupport.mpr (Or.inl rfl)⟩

/-- One signed boundary mode has exactly the shifted canonical up-target
coefficient at a literal boundary exit. -/

theorem exactBoundaryModeInteriorVector_apply_boundaryExit
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X} {eps : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1)
    (hleaf : leaf ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X
      (squareRootCutoff X) leaf})
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (hden : exactPrincipalMoleculeRoot S X a ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a
          (boundaryLeafCanonicalUpIndex ha (Nat.sqrt_le X) q)) : ℝ)) :
    exactBoundaryModeInteriorVector S X a eps
        (boundaryLeafExitVertex hS leaf q) =
      shiftedCanonicalUpLeafCoefficient hS a
        (exactPrincipalMoleculeRoot S X a)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a)
        (boundaryLeafCanonicalUpIndex ha (Nat.sqrt_le X) q) := by
  let qi : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a :=
    boundaryLeafCanonicalUpIndex ha (Nat.sqrt_le X) q
  let target := PrimeStar.canonicalUpTarget hS a qi
  have hk : target ∈ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a := by
    simpa [target, qi] using
      boundaryLeafCanonicalUpTarget_mem_firstExitLowerCenters
        hS ha hleaf q
  have hv : boundaryLeafExitVertex hS leaf q ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target := by
    simpa [target, qi] using boundaryLeafExitVertex_mem_canonicalUpLeaves
      hS ha (Nat.sqrt_le X) (PrimeStar.sqrtCutoff_condition X) hleaf q
  have hmu : eps * moleculeStarEnergy S X a ≠ 0 := by
    have heps0 : eps ≠ 0 := by
      intro h
      rw [h] at heps
      norm_num at heps
    have henergy : moleculeStarEnergy S X a ≠ 0 := by
      rw [moleculeStarEnergy]
      exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
    exact mul_ne_zero heps0 henergy
  rw [exactBoundaryModeInteriorVector,
    firstExitStarResolventVector_apply_of_mem_selectedStar
      (exactBoundaryModeInteriorSource S X a eps)
      (PrimeStar.sqrtCutoff_condition X) hk
      (Finset.mem_insert_of_mem hv)]
  rw [restrict_exactBoundaryModeInteriorSource_eq_canonicalUpStar
    hS ha hd heps qi]
  change shiftedActualUpStarResolvent S X (squareRootCutoff X) target
      (exactPrincipalMoleculeRoot S X a)
      (eps * moleculeStarEnergy S X a)
      (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a eps a)
      (boundaryLeafExitVertex hS leaf q) = _
  rw [shiftedActualUpStarResolvent_apply_leaf hv hroot hmu]
  · rfl
  · simpa [target, qi] using hden

/-- After the two signed modes are recombined, one literal outgoing exit has
exactly the advertised two-mode up-target coefficient. -/

theorem exactPrincipalMoleculeSignedInteriorVector_apply_boundaryExit
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hleaf : leaf ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X
      (squareRootCutoff X) leaf})
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (hden : exactPrincipalMoleculeRoot S X a ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a
          (boundaryLeafCanonicalUpIndex ha (Nat.sqrt_le X) q)) : ℝ)) :
    exactPrincipalMoleculeSignedInteriorVector S X a
        (boundaryLeafExitVertex hS leaf q) =
      shiftedCanonicalTwoModeUpLeafCoefficient hS a
        (exactPrincipalMoleculeRoot S X a) (moleculeStarEnergy S X a)
        (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
        (exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))
        (boundaryLeafCanonicalUpIndex ha (Nat.sqrt_le X) q) := by
  rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [exactBoundaryModeInteriorVector_apply_boundaryExit hS ha hd
      (by norm_num) hleaf q hroot hden,
    exactBoundaryModeInteriorVector_apply_boundaryExit hS ha hd
      (by norm_num) hleaf q hroot hden]
  rw [largePrimeNormalizedStarMode_center_eq_inv_sqrt_two
      (by norm_num) hd,
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two
      (by norm_num) hd]
  unfold shiftedCanonicalTwoModeUpLeafCoefficient
  unfold exactPrincipalMoleculeBoundarySourceAmplitude
  unfold shiftedCanonicalUpLeafCoefficient
  simp only [one_mul, neg_mul, one_mul, neg_one_mul, div_eq_mul_inv]
  ring

/-- A canonical down-target reached from a boundary leaf is one of the
selected non-isolated lower stars in the first-exit compression. -/

theorem boundaryLeafCanonicalDownTarget_mem_firstExitLowerCenters
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hleaf : leaf ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a) :
    PrimeStar.canonicalDownTarget a q ∈
      PrimeStar.firstExitLowerCenters S X (squareRootCutoff X) a := by
  let target := PrimeStar.canonicalDownTarget a q
  have htargetY : (target : ℕ) ≤ squareRootCutoff X := by
    exact (Nat.div_le_self _ _).trans ha
  have hexit : target ∈
      PrimeStar.smallPrimeFirstExitSupport S X (squareRootCutoff X) a := by
    simpa [target, PrimeStar.canonicalExitTarget] using
      (PrimeStar.canonicalExitTarget_mem_smallPrimeFirstExitSupport
        (Y := squareRootCutoff X) hS ha
          (Sum.inr q : PrimeStar.CanonicalExitIndex S X
            (squareRootCutoff X) a))
  have hdownLeaf : boundaryLeafDownVertex ha hleaf q ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target := by
    exact (Finset.mem_filter.mp
      (boundaryLeafDownVertex_mem_canonicalDownLeaves ha hleaf q)).1
  have hnotIso :
      ¬(PrimeStar.largePrimeGraph S X (squareRootCutoff X)).IsIsolated
        target := by
    intro hiso
    exact hiso (boundaryLeafDownVertex ha hleaf q)
      (PrimeStar.mem_largePrimeLeaves.mp hdownLeaf)
  exact PrimeStar.mem_firstExitLowerCenters.mpr
    ⟨htargetY, target, hexit, hnotIso, by
      simp [target, PrimeStar.largePrimeStarSupport]⟩

/-- For a fixed down label, one signed-mode response takes the same value at
the corresponding incoming vertex of every original boundary leaf. -/

theorem exactBoundaryModeInteriorVector_apply_boundaryDown_eq
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf₁ leaf₂ : PrimeStar.Vertex S X} {eps : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1)
    (hleaf₁ : leaf₁ ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (hleaf₂ : leaf₂ ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a) :
    exactBoundaryModeInteriorVector S X a eps
        (boundaryLeafDownVertex ha hleaf₁ q) =
      exactBoundaryModeInteriorVector S X a eps
        (boundaryLeafDownVertex ha hleaf₂ q) := by
  let target := PrimeStar.canonicalDownTarget a q
  let P := PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) target q
  have hk : target ∈ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a := by
    simpa [target] using
      boundaryLeafCanonicalDownTarget_mem_firstExitLowerCenters
        hS ha hleaf₁ q
  have hv₁P : boundaryLeafDownVertex ha hleaf₁ q ∈ P := by
    simpa [P, target] using
      boundaryLeafDownVertex_mem_canonicalDownLeaves ha hleaf₁ q
  have hv₂P : boundaryLeafDownVertex ha hleaf₂ q ∈ P := by
    simpa [P, target] using
      boundaryLeafDownVertex_mem_canonicalDownLeaves ha hleaf₂ q
  have hv₁Leaf : boundaryLeafDownVertex ha hleaf₁ q ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target :=
    (Finset.mem_filter.mp hv₁P).1
  have hv₂Leaf : boundaryLeafDownVertex ha hleaf₂ q ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target :=
    (Finset.mem_filter.mp hv₂P).1
  calc
    exactBoundaryModeInteriorVector S X a eps
        (boundaryLeafDownVertex ha hleaf₁ q) =
      shiftedActualDownStarResolvent S X (squareRootCutoff X) target P
        (exactPrincipalMoleculeRoot S X a)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a)
        (boundaryLeafDownVertex ha hleaf₁ q) := by
          rw [exactBoundaryModeInteriorVector,
            firstExitStarResolventVector_apply_of_mem_selectedStar
              (exactBoundaryModeInteriorSource S X a eps)
              (PrimeStar.sqrtCutoff_condition X) hk
              (Finset.mem_insert_of_mem hv₁Leaf),
            restrict_exactBoundaryModeInteriorSource_eq_canonicalDownStar
              hS ha hd heps q]
          rfl
    _ = shiftedActualDownStarResolvent S X (squareRootCutoff X) target P
        (exactPrincipalMoleculeRoot S X a)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a)
        (boundaryLeafDownVertex ha hleaf₂ q) :=
      shiftedActualDownStarResolvent_apply_eq_of_mem
        hv₁Leaf hv₂Leaf hv₁P hv₂P
    _ = exactBoundaryModeInteriorVector S X a eps
        (boundaryLeafDownVertex ha hleaf₂ q) := by
          rw [exactBoundaryModeInteriorVector,
            firstExitStarResolventVector_apply_of_mem_selectedStar
              (exactBoundaryModeInteriorSource S X a eps)
              (PrimeStar.sqrtCutoff_condition X) hk
              (Finset.mem_insert_of_mem hv₂Leaf),
            restrict_exactBoundaryModeInteriorSource_eq_canonicalDownStar
              hS ha hd heps q]
          rfl

/-- The recombined signed interior has the same down-target value for every
original boundary leaf. -/

theorem exactPrincipalMoleculeSignedInteriorVector_apply_boundaryDown_eq
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf₁ leaf₂ : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hleaf₁ : leaf₁ ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (hleaf₂ : leaf₂ ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a) :
    exactPrincipalMoleculeSignedInteriorVector S X a
        (boundaryLeafDownVertex ha hleaf₁ q) =
      exactPrincipalMoleculeSignedInteriorVector S X a
        (boundaryLeafDownVertex ha hleaf₂ q) := by
  rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [exactBoundaryModeInteriorVector_apply_boundaryDown_eq
      hS ha hd (by norm_num) hleaf₁ hleaf₂ q,
    exactBoundaryModeInteriorVector_apply_boundaryDown_eq
      hS ha hd (by norm_num) hleaf₁ hleaf₂ q]

/-- Total down-target contribution to the signed boundary feedback at one
original boundary leaf. -/

def exactSignedBoundaryDownResponse
    {S : Finset ℕ} {X : ℕ} (a leaf : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hleaf : leaf ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a) : ℝ :=
  ∑ q : PrimeStar.CanonicalDownIndex a,
    exactPrincipalMoleculeSignedInteriorVector S X a
      (boundaryLeafDownVertex ha hleaf q)

/-- The complete down-target response is leaf-independent. -/

theorem exactSignedBoundaryDownResponse_eq
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf₁ leaf₂ : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hleaf₁ : leaf₁ ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (hleaf₂ : leaf₂ ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a) :
    exactSignedBoundaryDownResponse a leaf₁ ha hleaf₁ =
      exactSignedBoundaryDownResponse a leaf₂ ha hleaf₂ := by
  apply Finset.sum_congr rfl
  intro q _hq
  exact exactPrincipalMoleculeSignedInteriorVector_apply_boundaryDown_eq
    hS ha hd hleaf₁ hleaf₂ q

/-- The signed feedback row is the outgoing up-target sum plus the incoming
down-target sum. -/

theorem exactPrincipalMoleculeSignedBoundaryFeedback_apply_leaf_eq_up_add_down
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hleaf : leaf ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeSignedBoundaryFeedback S X a leaf =
      (∑ q : {q : ℕ // q ∈ boundaryLeafExitPrimeLabels S X
          (squareRootCutoff X) leaf},
        exactPrincipalMoleculeSignedInteriorVector S X a
          (boundaryLeafExitVertex hS leaf q)) +
      exactSignedBoundaryDownResponse a leaf ha hleaf := by
  have hsupport : leaf ∈ PrimeStar.largePrimeStarSupport S X
      (squareRootCutoff X) a := Finset.mem_insert_of_mem hleaf
  rw [exactPrincipalMoleculeSignedBoundaryFeedback,
    PrimeStar.primeStarBoundaryProjection_apply, if_pos hsupport,
    Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
  change Matrix.mulVec
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (fun v ↦ exactPrincipalMoleculeSignedInteriorVector S X a v) leaf = _
  rw [SimpleGraph.adjMatrix_mulVec_apply,
    PrimeStar.sum_neighborFinset_eq_outgoing_add_incoming,
    sum_outgoingSmallPrimeNeighbors_eq_boundaryLeafExitVertices hS,
    sum_incomingSmallPrimeNeighbors_eq_boundaryLeafDownVertices ha hleaf]
  rfl

/-- Pointwise signed feedback equals the explicit two-mode up response plus a
leaf-independent down response. -/

theorem exactPrincipalMoleculeSignedBoundaryFeedback_apply_leaf
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a leaf : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hleaf : leaf ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (hden : ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) : ℝ)) :
    exactPrincipalMoleculeSignedBoundaryFeedback S X a leaf =
      boundaryLeafTwoModeUpResponse hS a leaf ha (Nat.sqrt_le X)
          (exactPrincipalMoleculeRoot S X a) (moleculeStarEnergy S X a)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) +
        exactSignedBoundaryDownResponse a leaf ha hleaf := by
  rw [exactPrincipalMoleculeSignedBoundaryFeedback_apply_leaf_eq_up_add_down
    hS ha hleaf]
  unfold boundaryLeafTwoModeUpResponse
  congr 1
  apply Finset.sum_congr rfl
  intro q _hq
  exact exactPrincipalMoleculeSignedInteriorVector_apply_boundaryExit
    hS ha hd hleaf q hroot (hden _)

/-- After mean-zero projection, the exact signed feedback is precisely the
explicit two-mode up-target response.  The operator-large down contribution
is removed identically, not estimated. -/

theorem meanZero_exactPrincipalMoleculeSignedBoundaryFeedback_eq_upResponse
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (hden : ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) : ℝ)) :
    actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeSignedBoundaryFeedback S X a) =
      actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (fun v ↦ boundaryLeafTwoModeUpResponse hS a v ha (Nat.sqrt_le X)
          (exactPrincipalMoleculeRoot S X a) (moleculeStarEnergy S X a)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))) := by
  have hnonempty :
      (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a).Nonempty :=
    Finset.card_pos.mp (by
      simpa [PrimeStar.largePrimeStarDegree] using hd)
  let leaf₀ := hnonempty.choose
  have hleaf₀ : leaf₀ ∈
      PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a :=
    hnonempty.choose_spec
  let C := exactSignedBoundaryDownResponse a leaf₀ ha hleaf₀
  calc
    actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeSignedBoundaryFeedback S X a) =
      actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (fun v ↦ boundaryLeafTwoModeUpResponse hS a v ha (Nat.sqrt_le X)
          (exactPrincipalMoleculeRoot S X a) (moleculeStarEnergy S X a)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) + C) := by
            apply actualStarMeanZeroLeafVector_congr_on_leaves
            intro v hv
            rw [exactPrincipalMoleculeSignedBoundaryFeedback_apply_leaf
              hS ha hd hv hroot hden]
            congr 1
            exact exactSignedBoundaryDownResponse_eq
              hS ha hd hv hleaf₀
    _ = actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (fun v ↦ boundaryLeafTwoModeUpResponse hS a v ha (Nat.sqrt_le X)
          (exactPrincipalMoleculeRoot S X a) (moleculeStarEnergy S X a)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))) := by
            exact actualStarMeanZeroLeafVector_add_const a _ C

/-- Exact graph-specific adapter consumed by the half-error kernel estimate:
the full feedback is the explicit signed up response plus the mean-zero
self-return generated by the boundary kernel. -/

theorem exactPrincipalMoleculeFeedbackKernel_eq_upResponse_add_kernelReturn
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeBoundaryFeedback S X a) =
      actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (fun v ↦ boundaryLeafTwoModeUpResponse hS a v ha (Nat.sqrt_le X)
            (exactPrincipalMoleculeRoot S X a) (moleculeStarEnergy S X a)
            (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
            (exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))) +
        actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (exactPrincipalMoleculeKernelBoundaryReturn S X a) := by
  rw [exactPrincipalMoleculeFeedbackKernel_eq_signed_add_kernelReturn
      hS ha hroot gamma hgamma hgap hden,
    meanZero_exactPrincipalMoleculeSignedBoundaryFeedback_eq_upResponse
      hS ha hd hroot]
  intro q
  let i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a :=
    Sum.inl q
  rcases PrimeStar.canonicalExitTarget_mem_lower_or_isolated
      hS (PrimeStar.sqrtCutoff_condition X) ha i with hi | hi
  · simpa [i, PrimeStar.canonicalExitTarget] using
      hden (PrimeStar.canonicalUpTarget hS a q) (by
        simpa [i, PrimeStar.canonicalExitTarget] using hi)
  · have hdeg : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) = 0 := by
      apply PrimeStar.largePrimeStarDegree_eq_zero_iff.mpr
      simpa [i, PrimeStar.canonicalExitTarget] using
        (PrimeStar.mem_firstExitIsolatedVertices.mp hi).2
    rw [hdeg, Nat.cast_zero]
    exact pow_ne_zero 2 hroot


/- Source slice: ExactBoundaryKernelReturn.lean -/

local instance exactBoundaryKernelReturnSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance exactBoundaryKernelReturnLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Mean-zero projection on the leaves of a nonempty star is contractive in
Euclidean norm. -/

theorem norm_actualStarMeanZeroLeafVector_le
    {S : Finset ℕ} {X Y : ℕ} {a : PrimeStar.Vertex S X}
    (f : MoleculeAmbient S X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a) :
    ‖actualStarMeanZeroLeafVector S X Y a f‖ ≤
      ‖f‖ := by
  have hleaves : (PrimeStar.largePrimeLeaves S X Y a).Nonempty :=
    Finset.card_pos.mp (by
      simpa [PrimeStar.largePrimeStarDegree] using hd)
  have hvariance :
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y a,
          (f v - finsetMean (PrimeStar.largePrimeLeaves S X Y a) f) ^ 2) ≤
        ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a, f v ^ 2 :=
    sum_sq_sub_finsetMean_le_sum_sq hleaves f
  have hsubset :
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y a, f v ^ 2) ≤
        ∑ v, f v ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _v _hv _hnot ↦ sq_nonneg _)
  have hsquare :
      ‖actualStarMeanZeroLeafVector S X Y a f‖ ^ 2 ≤
        ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [actualStarMeanZeroLeafVector,
      PrimeStar.largePrimeStarDataVector_inner, zero_mul, zero_add]
    calc
      (∑ v ∈ PrimeStar.largePrimeLeaves S X Y a,
          (f v - finsetMean (PrimeStar.largePrimeLeaves S X Y a) f) *
            (f v - finsetMean (PrimeStar.largePrimeLeaves S X Y a) f)) ≤
        ∑ v ∈ PrimeStar.largePrimeLeaves S X Y a, f v ^ 2 := by
          simpa only [pow_two] using hvariance
      _ ≤ ∑ v, f v ^ 2 := hsubset
      _ = ‖f‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

/-- The kernel-generated first-exit source pays one small-prime application. -/

theorem norm_exactPrincipalMoleculeKernelInteriorSource_le
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (eta : ℝ) (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖) :
    ‖exactPrincipalMoleculeKernelInteriorSource S X a‖ ≤
      eta * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
  unfold exactPrincipalMoleculeKernelInteriorSource
  calc
    ‖PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeBoundaryKernel S X a))‖ ≤
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeBoundaryKernel S X a)‖ := by
        exact PrimeStar.norm_euclideanCoordinateProjection_le _ _
    _ ≤ eta * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ :=
      hH _

/-- The explicit first-exit inverse pays the reciprocal compression gap. -/

theorem gamma_mul_norm_exactPrincipalMoleculeKernelInteriorVector_le
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) :
    gamma * ‖exactPrincipalMoleculeKernelInteriorVector S X a‖ ≤
      ‖exactPrincipalMoleculeKernelInteriorSource S X a‖ := by
  let b := exactPrincipalMoleculeKernelInteriorSource S X a
  have hb : ∀ v, v ∉ PrimeStar.smallPrimeFirstExitSupport S X
      (squareRootCutoff X) a → b v = 0 := by
    intro v hv
    unfold b exactPrincipalMoleculeKernelInteriorSource
    rw [PrimeStar.firstExitCompressionProjection_apply]
    split
    next _hvCompression =>
      rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
      apply PrimeStar.smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
        (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
        (fun w ↦ exactPrincipalMoleculeBoundaryKernel S X a w)
      · intro w hw
        unfold exactPrincipalMoleculeBoundaryKernel
          actualStarMeanZeroLeafVector
        have hwc : w ≠ a := by
          intro hwa
          subst w
          exact hw (by simp [PrimeStar.largePrimeStarSupport])
        have hwleaf : w ∉ PrimeStar.largePrimeLeaves S X
            (squareRootCutoff X) a := by
          intro hwleaf
          exact hw (by simp [PrimeStar.largePrimeStarSupport, hwleaf])
        exact PrimeStar.largePrimeStarDataVector_outside _ _ hwc hwleaf
      · exact hv
    next _ => rfl
  have hsolve := PrimeStar.firstExitStar_shift_resolventVector
    b (PrimeStar.sqrtCutoff_condition X) hroot hden hb
  have hgapY := hgap (exactPrincipalMoleculeKernelInteriorVector S X a)
  have hxSupport : ∀ v,
      v ∉ PrimeStar.firstExitCompressionSupport S X
          (squareRootCutoff X) a →
        exactPrincipalMoleculeKernelInteriorVector S X a v = 0 := by
    intro v hv
    exact PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem b hv
  have hcompression :
      PrimeStar.firstExitLargePrimeCompressionOperator S X
          (squareRootCutoff X) a
          (exactPrincipalMoleculeKernelInteriorVector S X a) =
        Matrix.toEuclideanLin
          ((PrimeStar.largePrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeKernelInteriorVector S X a) :=
    PrimeStar.firstExitLargePrimeCompressionOperator_eq_of_supported
      (PrimeStar.sqrtCutoff_condition X)
      (exactPrincipalMoleculeKernelInteriorVector S X a) hxSupport
  change gamma * ‖exactPrincipalMoleculeKernelInteriorVector S X a‖ ≤ ‖b‖
  calc
    gamma * ‖exactPrincipalMoleculeKernelInteriorVector S X a‖ ≤
        ‖exactPrincipalMoleculeRoot S X a •
            exactPrincipalMoleculeKernelInteriorVector S X a -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a
            (exactPrincipalMoleculeKernelInteriorVector S X a)‖ := hgapY
    _ = ‖b‖ := by
      rw [hcompression]
      rw [exactPrincipalMoleculeKernelInteriorVector]
      exact congrArg norm hsolve

/-- The complete kernel self-return pays two small-prime crossings and one
first-exit gap.  This is the error term that enters each signed scalar
boundary equation. -/

theorem gamma_mul_norm_exactPrincipalMoleculeKernelBoundaryReturn_le
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖) :
    gamma * ‖exactPrincipalMoleculeKernelBoundaryReturn S X a‖ ≤
      eta ^ 2 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
  have hreturn :
      ‖exactPrincipalMoleculeKernelBoundaryReturn S X a‖ ≤
        eta * ‖exactPrincipalMoleculeKernelInteriorVector S X a‖ := by
    unfold exactPrincipalMoleculeKernelBoundaryReturn
    calc
      ‖PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) a
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X
              (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeKernelInteriorVector S X a))‖ ≤
        ‖Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X
              (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeKernelInteriorVector S X a)‖ := by
          exact PrimeStar.norm_euclideanCoordinateProjection_le _ _
      _ ≤ eta * ‖exactPrincipalMoleculeKernelInteriorVector S X a‖ := hH _
  have hinterior :=
    gamma_mul_norm_exactPrincipalMoleculeKernelInteriorVector_le
      hS ha hroot gamma hgamma hgap hden
  calc
    gamma * ‖exactPrincipalMoleculeKernelBoundaryReturn S X a‖ ≤
      gamma * (eta *
        ‖exactPrincipalMoleculeKernelInteriorVector S X a‖) := by
      gcongr
    _ = eta * (gamma *
        ‖exactPrincipalMoleculeKernelInteriorVector S X a‖) := by ring
    _ ≤ eta * ‖exactPrincipalMoleculeKernelInteriorSource S X a‖ := by
      gcongr
    _ ≤ eta * (eta *
        ‖exactPrincipalMoleculeBoundaryKernel S X a‖) := by
      gcongr
      exact norm_exactPrincipalMoleculeKernelInteriorSource_le eta hH
    _ = eta ^ 2 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by ring

/-- The mean-zero part of the kernel self-return obeys the same two-crossing
bound by contractivity of the leaf-centering projection. -/

theorem gamma_mul_norm_meanZero_kernelBoundaryReturn_le
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖) :
    gamma * ‖actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeKernelBoundaryReturn S X a)‖ ≤
      eta ^ 2 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
  have hmean := norm_actualStarMeanZeroLeafVector_le
    (exactPrincipalMoleculeKernelBoundaryReturn S X a) hd
  have hreturn :=
    gamma_mul_norm_exactPrincipalMoleculeKernelBoundaryReturn_le
      hS ha hroot gamma eta hgamma heta hgap hden hH
  calc
    gamma * ‖actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeKernelBoundaryReturn S X a)‖ ≤
      gamma * ‖exactPrincipalMoleculeKernelBoundaryReturn S X a‖ := by
        gcongr
    _ ≤ eta ^ 2 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := hreturn

/-- A scalar smallness condition turns the preceding finite estimate into the
one-half contraction required by the absorption theorem. -/

theorem norm_meanZero_kernelBoundaryReturn_le_half
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖)
    (hsmall : 2 * eta ^ 2 ≤
      |exactPrincipalMoleculeRoot S X a| * gamma) :
    ‖actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
        (exactPrincipalMoleculeKernelBoundaryReturn S X a)‖ ≤
      |exactPrincipalMoleculeRoot S X a| / 2 *
        ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
  have hmain := gamma_mul_norm_meanZero_kernelBoundaryReturn_le
    hS ha hd hroot gamma eta hgamma heta hgap hden hH
  have hscaled :
      gamma * ‖actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (exactPrincipalMoleculeKernelBoundaryReturn S X a)‖ ≤
        gamma * (|exactPrincipalMoleculeRoot S X a| / 2 *
          ‖exactPrincipalMoleculeBoundaryKernel S X a‖) := by
    calc
      gamma * ‖actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
          (exactPrincipalMoleculeKernelBoundaryReturn S X a)‖ ≤
        eta ^ 2 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := hmain
      _ ≤ (|exactPrincipalMoleculeRoot S X a| * gamma / 2) *
          ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
        gcongr
        linarith
      _ = gamma * (|exactPrincipalMoleculeRoot S X a| / 2 *
          ‖exactPrincipalMoleculeBoundaryKernel S X a‖) := by ring
  exact le_of_mul_le_mul_left hscaled hgamma

/-- Complete finite boundary-kernel estimate.  The graph-specific signed
response identity and the self-return contraction are discharged internally;
the remaining hypotheses are the quantitative molecule-window gap, the
small-prime operator bound, and their scalar smallness comparison. -/

theorem exactPrincipalMoleculeRoot_sq_mul_norm_sq_boundaryKernel_le_of_window
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a,
      exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ))
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖)
    (hsmall : 2 * eta ^ 2 ≤
      |exactPrincipalMoleculeRoot S X a| * gamma)
    (hlambda : |exactPrincipalMoleculeRoot S X a| ≤
      2 * moleculeStarEnergy S X a)
    (hupGap : ∀ q : PrimeStar.CanonicalUpIndex S X
        (squareRootCutoff X) a,
      moleculeStarEnergy S X a ^ 2 / 100 ≤
        |exactPrincipalMoleculeRoot S X a ^ 2 -
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) : ℝ)|) :
    exactPrincipalMoleculeRoot S X a ^ 2 *
        ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 ≤
      4 * (600 / moleculeStarEnergy S X a ^ 2) ^ 2 *
        (boundaryLeafCountSquareSumOnStar S X
          (squareRootCutoff X) a : ℝ) := by
  have hmu : 0 < moleculeStarEnergy S X a := by
    rw [moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  let cPlus := exactPrincipalMoleculeBoundarySourceAmplitude S X a 1
  let cMinus := exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  let err : MoleculeAmbient S X :=
    actualStarMeanZeroLeafVector S X (squareRootCutoff X) a
      (exactPrincipalMoleculeKernelBoundaryReturn S X a)
  have hcPlus : |cPlus| ≤ 1 := by
    exact abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one
      hd (by norm_num)
  have hcMinus : |cMinus| ≤ 1 := by
    exact abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one
      hd (by norm_num)
  have hcoeff : ∀ q : PrimeStar.CanonicalUpIndex S X
      (squareRootCutoff X) a,
      |shiftedCanonicalTwoModeUpLeafCoefficient hS a
          (exactPrincipalMoleculeRoot S X a)
          (moleculeStarEnergy S X a) cPlus cMinus q| ≤
        600 / moleculeStarEnergy S X a ^ 2 := by
    intro q
    exact abs_shiftedCanonicalTwoModeUpLeafCoefficient_le
      hS a (exactPrincipalMoleculeRoot S X a)
        (moleculeStarEnergy S X a) cPlus cMinus q
        hmu hcPlus hcMinus hlambda (hupGap q)
  have hfeedback :=
    exactPrincipalMoleculeFeedbackKernel_eq_upResponse_add_kernelReturn
      hS ha hd hroot gamma hgamma hgap hden
  have herr : ‖err‖ ≤ |exactPrincipalMoleculeRoot S X a| / 2 *
      ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
    exact norm_meanZero_kernelBoundaryReturn_le_half
      hS ha hd hroot gamma eta hgamma heta hgap hden hH hsmall
  have hbound :=
    exactPrincipalMoleculeRoot_sq_mul_norm_sq_boundaryKernel_twoMode_le_of_half_error
      hS ha hd (moleculeStarEnergy S X a) cPlus cMinus
        (600 / moleculeStarEnergy S X a ^ 2) 0
        (by positivity) err hcoeff (by simpa [cPlus, cMinus, err] using hfeedback)
        herr
  simpa [mul_assoc] using hbound


/- Source slice: MoleculeResidual.lean -/

local instance moleculeResidualPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Matrix defect between the ambient adjacency and the embedded principal
molecule.  Its columns are the literal continuation/collision residuals. -/


/- Source slice: MoleculeFamily.lean -/

local instance moleculeFamilyPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Allowed arithmetic centres retained in the prefix `a ≤ K`. -/


/- Source slice: ExactMoleculeInteriorMass.lean -/

local instance exactInteriorMassSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance exactInteriorMassLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The exact first-exit source pays one small-prime application to the
boundary part of the normalized molecule. -/

theorem norm_exactPrincipalMoleculeInteriorSource_le_smallPrime
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    {eta : ℝ} (heta : 0 ≤ eta)
    (hH : ∀ y : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          y‖ ≤ eta * ‖y‖) :
    ‖exactPrincipalMoleculeInteriorSource S X a‖ ≤ eta := by
  unfold exactPrincipalMoleculeInteriorSource
  calc
    ‖PrimeStar.firstExitCompressionProjection S X (squareRootCutoff X) a
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeBoundaryVector S X a))‖ ≤
        ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeBoundaryVector S X a)‖ :=
      PrimeStar.norm_euclideanCoordinateProjection_le _ _
    _ ≤ eta * ‖exactPrincipalMoleculeBoundaryVector S X a‖ := hH _
    _ ≤ eta * ‖exactPrincipalMoleculeAmbientVector S X a‖ := by
      gcongr
      exact PrimeStar.norm_euclideanCoordinateProjection_le _ _
    _ = eta := by rw [norm_exactPrincipalMoleculeAmbientVector, mul_one]

/-- A lower bound for the shifted first-exit compression charges the exact
interior by its literal boundary source. -/

theorem gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_source
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (gamma : ℝ)
    (hgap : ∀ y : MoleculeAmbient S X,
      gamma * ‖y‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • y -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a y‖) :
    gamma * ‖exactPrincipalMoleculeInteriorVector S X a‖ ≤
      ‖exactPrincipalMoleculeInteriorSource S X a‖ := by
  let xU := exactPrincipalMoleculeInteriorVector S X a
  have hxSupport : ∀ v,
      v ∉ PrimeStar.firstExitCompressionSupport S X
          (squareRootCutoff X) a → xU v = 0 := by
    intro v hv
    simp [xU, exactPrincipalMoleculeInteriorVector,
      PrimeStar.firstExitCompressionProjection_apply, hv]
  have hcompression :
      PrimeStar.firstExitLargePrimeCompressionOperator S X
          (squareRootCutoff X) a xU =
        Matrix.toEuclideanLin
          ((PrimeStar.largePrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ) xU :=
    PrimeStar.firstExitLargePrimeCompressionOperator_eq_of_supported
      (PrimeStar.sqrtCutoff_condition X) xU hxSupport
  calc
    gamma * ‖exactPrincipalMoleculeInteriorVector S X a‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • xU -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a xU‖ := hgap xU
    _ = ‖exactPrincipalMoleculeInteriorSource S X a‖ := by
      rw [hcompression]
      exact congrArg norm
        (exactPrincipalMoleculeInterior_shift_largePrime hS ha)

/-- Combining the exact source equation with a small-prime norm bound gives
the finite first-exit interior estimate in unsquared form. -/

theorem gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_smallPrime
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (gamma eta : ℝ) (heta : 0 ≤ eta)
    (hgap : ∀ y : MoleculeAmbient S X,
      gamma * ‖y‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • y -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a y‖)
    (hH : ∀ y : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          y‖ ≤ eta * ‖y‖) :
    gamma * ‖exactPrincipalMoleculeInteriorVector S X a‖ ≤ eta :=
  (gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_source
      hS ha gamma hgap).trans
    (norm_exactPrincipalMoleculeInteriorSource_le_smallPrime heta hH)

/-- Squared form of the source-weighted first-exit estimate. -/


/- Source slice: BakerHarmanPintzFiniteDeletion.lean -/

theorem allowedPrimeCount_mono {S : Finset ℕ} {M N : ℕ} (hMN : M ≤ N) :
    allowedPrimeCount S M ≤ allowedPrimeCount S N := by
  apply Finset.card_le_card
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp'.1).1.trans hMN,
        (Nat.mem_primesLE.mp hp'.1).2⟩,
      hp'.2⟩

@[simp]

theorem real_div_sub_one_lt_natCast_div
    (X d : ℕ) (hd : 0 < d) :
    (X : ℝ) / (d : ℝ) - 1 < ((X / d : ℕ) : ℝ) := by
  have hnat := Nat.lt_mul_div_succ X hd
  have hreal :
      (X : ℝ) < (d : ℝ) * (((X / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast hnat
  rw [sub_lt_iff_lt_add]
  apply (div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).2
  simpa [mul_comm] using hreal

/-- The real reciprocal displacement has the exact hyperbola form used in
the target-cluster calculation. -/


/- Source slice: CollisionBudget.lean -/

local instance collisionBudgetSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Two distinct positive centres with the same prime-labelled descendant
have the unique-factorization shape used by the coherent collision blocks:
`a = g * r`, `b = g * q`, and the common descendant is `g * r * q`.

This is the arithmetic classification behind the manuscript path
`g r -> g r q -> g q`; it does not estimate the resulting operator block. -/


/- Source slice: MoleculeFrameComplex.lean -/

local instance moleculeFrameComplexPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

/-- Entrywise scalar extension of a real matrix to a complex matrix. -/


/- Source slice: OneExitCyclicSubspace.lean -/

local instance oneExitLargePrimeDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

local instance oneExitSmallPrimeDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

/-- Complex large-prime forest adjacency at the square-root cutoff. -/


/- Source slice: PowerBandDegreeRatios.lean -/

theorem eventually_two_mul_center_le_natSqrt_on_powerRange
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ,
      InPowerRange θ X a → 2 * a ≤ Nat.sqrt X := by
  have hgap : 0 < 1 / 2 - θ := sub_pos.mpr hθ
  have hgapTop : Tendsto
      (fun X : ℕ ↦ (X : ℝ) ^ (1 / 2 - θ)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgapTop.eventually_ge_atTop 3, eventually_gt_atTop 0]
      with X hgapX hX
  intro a ha
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have haUpper : (a : ℝ) ≤ powerScale θ X := ha.2
  have hscaleOne : 1 ≤ powerScale θ X := by
    exact (by exact_mod_cast ha.1 : (1 : ℝ) ≤ a).trans ha.2
  have hroot : 3 * powerScale θ X ≤ Real.sqrt (X : ℝ) := by
    calc
      3 * powerScale θ X ≤
          (X : ℝ) ^ (1 / 2 - θ) * powerScale θ X := by
        exact mul_le_mul_of_nonneg_right hgapX
          (Real.rpow_nonneg hx.le θ)
      _ = Real.sqrt (X : ℝ) := by
        rw [powerScale, Real.sqrt_eq_rpow, ← Real.rpow_add hx]
        congr 1
        ring
  have htwoAOne : ((2 * a + 1 : ℕ) : ℝ) ≤
      3 * powerScale θ X := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [haUpper, hscaleOne]
  have hbelow : ((2 * a + 1 : ℕ) : ℝ) <
      (Nat.sqrt X : ℝ) + 1 :=
    lt_of_le_of_lt (htwoAOne.trans hroot)
      (Real.real_sqrt_lt_nat_sqrt_succ (a := X))
  have hbelowNat : 2 * a + 1 < Nat.sqrt X + 1 := by
    exact_mod_cast hbelow
  omega

/-- Uniform PNT bounds for every integer argument between the square-root
cutoff and `X`.  This is the common arithmetic input for all moving centres
and prime labels in the power-band ratio estimates. -/

theorem eventually_squareRootRange_allowedPrime_bounds
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ᶠ X : ℕ in atTop, ∀ N : ℕ,
      Nat.sqrt X ≤ N → N ≤ X →
        (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤
            (allowedPrimeCount S N : ℝ) -
              (allowedPrimeCount S (N / 2) : ℝ) ∧
          (allowedPrimeCount S N : ℝ) ≤
            4 * ((N : ℝ) / Real.log (N : ℝ)) ∧
          0 < Real.log (N : ℝ) ∧
          Real.log (N : ℝ) ≤ Real.log (X : ℝ) ∧
          Real.log (X : ℝ) ≤ 3 * Real.log (N : ℝ) := by
  obtain ⟨N₀, hgap⟩ := eventually_atTop.1
    (PrimeStar.eventually_allowedPrimeCount_fixedDenominator_gap_ge
      S hS (a := 1) (b := 2) (by norm_num) (by norm_num))
  obtain ⟨N₁, hupper⟩ := eventually_atTop.1
    (PrimeStar.eventually_allowedPrimeCount_nat_le_four_main S)
  have hlogRatio : ∀ᶠ X : ℕ in atTop,
      (1 / 3 : ℝ) <
        Real.log (Nat.sqrt X : ℝ) / Real.log (X : ℝ) :=
    PrimeStar.log_natSqrt_div_log_tendsto_half.eventually
      (isOpen_Ioi.mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2))
  filter_upwards [PrimeStar.tendsto_natSqrt_atTop.eventually_ge_atTop
      (max (max N₀ N₁) 2), hlogRatio, eventually_ge_atTop 4]
      with X hYlarge hratio hX
  intro N hYN hNX
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans
    ((le_max_left _ _).trans (hYlarge.trans hYN))
  have hN₁ : N₁ ≤ N := (le_max_right N₀ N₁).trans
    ((le_max_left _ _).trans (hYlarge.trans hYN))
  have hNtwo : 2 ≤ N := (le_max_right (max N₀ N₁) 2).trans
    (hYlarge.trans hYN)
  have hXlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hNlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hYpos : (0 : ℝ) < Nat.sqrt X := by
    exact_mod_cast (show 0 < Nat.sqrt X by omega)
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogYN : Real.log (Nat.sqrt X : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hYpos (by exact_mod_cast hYN)
  have hlogNX : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast hNX)
  have hlogXY : Real.log (X : ℝ) <
      3 * Real.log (Nat.sqrt X : ℝ) := by
    have := (lt_div_iff₀ hXlog).mp hratio
    nlinarith
  constructor
  · have hgapN := hgap N hN₀
    norm_num at hgapN
    simpa [allowedPrimeCount, PrimeStar.allowedPrimeCount] using hgapN
  constructor
  · simpa [allowedPrimeCount, PrimeStar.allowedPrimeCount] using hupper N hN₁
  constructor
  · exact hNlog
  constructor
  · exact hlogNX
  · linarith

/-- Uniform main-scale bounds for the arithmetic star degree of every centre
in a fixed sub-square-root power range. -/

theorem eventually_powerRange_arithmeticStarDegree_bounds
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InPowerRange θ X (a : ℕ) →
        let N := X / (a : ℕ)
        Nat.sqrt X ≤ N / 2 ∧
          0 < arithmeticStarDegree S (a : ℕ) X ∧
          (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤
            arithmeticStarDegree S (a : ℕ) X ∧
          arithmeticStarDegree S (a : ℕ) X ≤
            4 * ((N : ℝ) / Real.log (N : ℝ)) := by
  filter_upwards [eventually_two_mul_center_le_natSqrt_on_powerRange hθ,
      eventually_squareRootRange_allowedPrime_bounds S hS]
      with X hcenter hprime
  intro a ha
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let N : ℕ := X / A
  have hApos : 0 < A := PrimeStar.Vertex.coe_pos a
  have htwoAY : 2 * A ≤ Y := hcenter A ha
  have htwoYN : 2 * Y ≤ N := by
    apply (Nat.le_div_iff_mul_le hApos).2
    calc
      2 * Y * A = Y * (2 * A) := by ring
      _ ≤ Y * Y := Nat.mul_le_mul_left Y htwoAY
      _ ≤ X := Nat.sqrt_le X
  have hYNhalf : Y ≤ N / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by simpa [mul_comm] using htwoYN)
  have hYN : Y ≤ N := hYNhalf.trans (Nat.div_le_self N 2)
  have hNX : N ≤ X := Nat.div_le_self X A
  have hprimeN := hprime N hYN hNX
  have hmono := allowedPrimeCount_mono (S := S) hYNhalf
  have hdegreeLower :
      (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤
        arithmeticStarDegree S A X := by
    rw [arithmeticStarDegree]
    exact hprimeN.1.trans
      (sub_le_sub_left (by exact_mod_cast hmono) _)
  have hmainPos :
      0 < (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    exact mul_pos (by norm_num) (div_pos hNpos hprimeN.2.2.1)
  have hdegreeUpper : arithmeticStarDegree S A X ≤
      4 * ((N : ℝ) / Real.log (N : ℝ)) := by
    rw [arithmeticStarDegree]
    exact (sub_le_self _ (by positivity)).trans hprimeN.2.1
  simpa [A, Y, N] using
    (show Y ≤ N / 2 ∧ 0 < arithmeticStarDegree S A X ∧
        (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤
          arithmeticStarDegree S A X ∧
        arithmeticStarDegree S A X ≤
          4 * ((N : ℝ) / Real.log (N : ℝ)) from
      ⟨hYNhalf, hmainPos.trans_le hdegreeLower, hdegreeLower, hdegreeUpper⟩)

/-- Shared residual-scale package for the actual square-cutoff star degree.
This is the arithmetic estimate consumed by both the exact-molecule analysis
and the full-to-one-exit spectral transfer; it therefore lives below those
two spectral constructions. -/

theorem eventually_powerRange_largePrimeStarDegree_residualScaleBundle
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (a : ℕ) ≤ squareRootCutoff X ∧
        0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a ∧
        1000000 * PrimeStar.sqrtCutoffResidualScale X ^ 2 ≤
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) ∧
        (X : ℝ) / (8 * (a : ℝ) * Real.log (X : ℝ)) ≤
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) ∧
        PrimeStar.sqrtCutoffResidualScale X ^ 4 /
            (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) ≤
          128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
            ((a : ℝ) / Real.log (X : ℝ)) := by
  let C : ℝ := 32000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num)
      (sq_pos_of_pos PrimeStar.sqrtCutoffResidualConstant_pos)
  have hlim := (tendsto_powerScale_div_sqrt_zero htheta).const_mul C
  have hsmall : ∀ᶠ X : ℕ in atTop,
      C * (powerScale theta X / Real.sqrt (X : ℝ)) < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  filter_upwards [eventually_powerRange_arithmeticStarDegree_bounds S hS htheta,
      eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
      PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
      hsmall, eventually_ge_atTop 4]
      with X hdegree hcenter hresSq hsmallX hX
  intro a ha
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let N : ℕ := X / A
  let eta : ℝ := PrimeStar.sqrtCutoffResidualScale X
  let K : ℝ := PrimeStar.sqrtCutoffResidualConstant
  have hApos : 0 < A := PrimeStar.Vertex.coe_pos a
  have htwoAY : 2 * A ≤ Y := hcenter A ha
  have hYXa : Y ≤ X / A := by
    apply (Nat.le_div_iff_mul_le hApos).2
    calc
      Y * A ≤ Y * Y := Nat.mul_le_mul_left Y (by omega : A ≤ Y)
      _ ≤ X := Nat.sqrt_le X
  have hcountMono := PrimeStar.allowedPrimeCount_mono (S := S) hYXa
  have hdegreeEq :
      (PrimeStar.largePrimeStarDegree S X Y a : ℝ) =
        arithmeticStarDegree S A X := by
    rw [PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS a
      (by omega : A ≤ Y) hYXa, Nat.cast_sub hcountMono]
    rfl
  have hdegreeEq' :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) =
        arithmeticStarDegree S A X := by
    simpa [Y, squareRootCutoff] using hdegreeEq
  have hdegreeData := hdegree a ha
  have hdArith : 0 < arithmeticStarDegree S A X := by
    simpa [A] using hdegreeData.2.1
  have hd : 0 < PrimeStar.largePrimeStarDegree S X Y a := by
    exact_mod_cast (show (0 : ℝ) <
      (PrimeStar.largePrimeStarDegree S X Y a : ℝ) by
        rw [hdegreeEq]
        exact hdArith)
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.div_pos (by omega) hApos
  have hNleX : N ≤ X := Nat.div_le_self X A
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    have htwoAX : 2 * A ≤ X := htwoAY.trans (Nat.sqrt_le_self X)
    have hNtwo : 2 ≤ N := by
      apply (Nat.le_div_iff_mul_le hApos).2
      simpa [mul_comm] using htwoAX
    exact_mod_cast (show 1 < N by omega)
  have hlogNX : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hNleX)
  have hfloor := real_div_sub_one_lt_natCast_div X A hApos
  have htwoReal : (2 : ℝ) ≤ (X : ℝ) / (A : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hApos : (0 : ℝ) < A)).2
    exact_mod_cast (htwoAY.trans (Nat.sqrt_le_self X))
  have hNlower : (X : ℝ) / (2 * (A : ℝ)) ≤ (N : ℝ) := by
    have hhalf : (X : ℝ) / (2 * (A : ℝ)) ≤
        (X : ℝ) / (A : ℝ) - 1 := by
      have hAreal : (0 : ℝ) < A := by exact_mod_cast hApos
      have hrewrite :
          (X : ℝ) / (2 * (A : ℝ)) = ((X : ℝ) / (A : ℝ)) / 2 := by
        field_simp [ne_of_gt hAreal]
      rw [hrewrite]
      nlinarith
    exact hhalf.trans hfloor.le
  have hdLower :
      (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤
        arithmeticStarDegree S A X := by
    simpa [A, N] using hdegreeData.2.2.1
  have hdCoarse :
      (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) ≤
        arithmeticStarDegree S A X := by
    calc
      (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) =
          (1 / 4 : ℝ) * (((X : ℝ) / (2 * (A : ℝ))) /
            Real.log (X : ℝ)) := by ring
      _ ≤ (1 / 4 : ℝ) * ((N : ℝ) / Real.log (X : ℝ)) := by gcongr
      _ ≤ (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by positivity) hlogN hlogNX)
          (by norm_num)
      _ ≤ arithmeticStarDegree S A X := hdLower
  have hscale :
      32000000 * K ^ 2 * (A : ℝ) ≤ Real.sqrt (X : ℝ) := by
    have hpow : (A : ℝ) ≤ powerScale theta X := ha.2
    have hsqrtPos : 0 < Real.sqrt (X : ℝ) := by positivity
    have hratio : C * ((A : ℝ) / Real.sqrt (X : ℝ)) < 1 := by
      calc
        C * ((A : ℝ) / Real.sqrt (X : ℝ)) ≤
            C * (powerScale theta X / Real.sqrt (X : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hpow hsqrtPos.le) hC.le
        _ < 1 := hsmallX
    have hmul : C * (A : ℝ) < Real.sqrt (X : ℝ) := by
      calc
        C * (A : ℝ) =
            (C * ((A : ℝ) / Real.sqrt (X : ℝ))) *
              Real.sqrt (X : ℝ) := by field_simp [ne_of_gt hsqrtPos]
        _ < 1 * Real.sqrt (X : ℝ) :=
          mul_lt_mul_of_pos_right hratio hsqrtPos
        _ = Real.sqrt (X : ℝ) := one_mul _
    simpa [C, K] using hmul.le
  have hetaSq : eta ^ 2 ≤
      4 * K ^ 2 * (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by
    simpa [eta, K] using hresSq
  have hsqrtSq : Real.sqrt (X : ℝ) ^ 2 = (X : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hscaled : 1000000 * eta ^ 2 ≤ arithmeticStarDegree S A X := by
    calc
      1000000 * eta ^ 2 ≤
          4000000 * K ^ 2 *
            (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by
        nlinarith [hetaSq]
      _ ≤ (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) := by
        have hbase :
            4000000 * K ^ 2 * Real.sqrt (X : ℝ) ≤
              (X : ℝ) / (8 * (A : ℝ)) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * A)]
          calc
            4000000 * K ^ 2 * Real.sqrt (X : ℝ) * (8 * (A : ℝ)) =
                (32000000 * K ^ 2 * (A : ℝ)) * Real.sqrt (X : ℝ) := by ring
            _ ≤ Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) := by gcongr
            _ = (X : ℝ) := by nlinarith [hsqrtSq]
        have hdiv := div_le_div_of_nonneg_right hbase hlogX.le
        calc
          4000000 * K ^ 2 *
                (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) =
              (4000000 * K ^ 2 * Real.sqrt (X : ℝ)) /
                Real.log (X : ℝ) := by ring
          _ ≤ ((X : ℝ) / (8 * (A : ℝ))) / Real.log (X : ℝ) := hdiv
          _ = (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) := by ring
      _ ≤ arithmeticStarDegree S A X := hdCoarse
  have hetaFourth : eta ^ 4 ≤
      16 * K ^ 4 * ((X : ℝ) / Real.log (X : ℝ) ^ 2) := by
    calc
      eta ^ 4 = (eta ^ 2) ^ 2 := by ring
      _ ≤ (4 * K ^ 2 *
          (Real.sqrt (X : ℝ) / Real.log (X : ℝ))) ^ 2 := by gcongr
      _ = 16 * K ^ 4 * ((X : ℝ) / Real.log (X : ℝ) ^ 2) := by
        field_simp [ne_of_gt hlogX]
        rw [hsqrtSq]
        ring
  have hrate : eta ^ 4 / arithmeticStarDegree S A X ≤
      128 * K ^ 4 * ((A : ℝ) / Real.log (X : ℝ)) := by
    apply (div_le_iff₀ hdArith).2
    calc
      eta ^ 4 ≤ 16 * K ^ 4 *
          ((X : ℝ) / Real.log (X : ℝ) ^ 2) := hetaFourth
      _ ≤ (128 * K ^ 4 * ((A : ℝ) / Real.log (X : ℝ))) *
          arithmeticStarDegree S A X := by
        have hmul := mul_le_mul_of_nonneg_left hdCoarse
          (show 0 ≤ 128 * K ^ 4 * ((A : ℝ) / Real.log (X : ℝ)) by
            positivity)
        calc
          16 * K ^ 4 * ((X : ℝ) / Real.log (X : ℝ) ^ 2) =
              (128 * K ^ 4 * ((A : ℝ) / Real.log (X : ℝ))) *
                ((X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ))) := by
            field_simp [ne_of_gt (show (0 : ℝ) < A by exact_mod_cast hApos),
              ne_of_gt hlogX]
            ring
          _ ≤ (128 * K ^ 4 * ((A : ℝ) / Real.log (X : ℝ))) *
                arithmeticStarDegree S A X := hmul
  refine ⟨by simpa [Y] using (show A ≤ Y by omega), by simpa [Y] using hd, ?_, ?_, ?_⟩
  · rw [hdegreeEq']
    simpa [eta] using hscaled
  · rw [hdegreeEq']
    simpa [A] using hdCoarse
  · rw [hdegreeEq']
    simpa [eta, K, A] using hrate

/-- Uniform up-star ratios in every fixed sub-square-root power range.  The
first bound protects the pole at one; the reciprocal-prime bound makes the
sum over labels logarithmic. -/

theorem eventually_powerRange_actualUpStarRatio_bounds
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InPowerRange θ X (a : ℕ) →
        ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
          0 ≤ actualUpStarRatio S (a : ℕ) X q ∧
            actualUpStarRatio S (a : ℕ) X q ≤ 15 / 16 ∧
            actualUpStarRatio S (a : ℕ) X q ≤ 48 / (q : ℝ) := by
  filter_upwards [eventually_powerRange_arithmeticStarDegree_bounds S hS hθ,
      eventually_squareRootRange_allowedPrime_bounds S hS]
      with X hdegree hprime
  intro a ha q hq
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let N : ℕ := X / A
  let Nq : ℕ := X / (A * q)
  let d : ℝ := arithmeticStarDegree S A X
  let dq : ℝ := arithmeticStarDegree S (A * q) X
  have hqData := Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1
  have hqPrime : q.Prime := hqData.2
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hqPos : (0 : ℝ) < q := by positivity
  have hdegreeA := hdegree a ha
  have hdPos : 0 < d := by simpa [d, A] using hdegreeA.2.1
  have hdLower :
      (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤ d := by
    simpa [d, N, A] using hdegreeA.2.2.1
  have hdUpper : d ≤ 4 * ((N : ℝ) / Real.log (N : ℝ)) := by
    simpa [d, N, A] using hdegreeA.2.2.2
  by_cases hactive : A * q ≤ Y
  · have hYNq : Y ≤ Nq := by
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos (PrimeStar.Vertex.coe_pos a)
        hqPrime.pos)).2
      calc
        Y * (A * q) ≤ Y * Y := Nat.mul_le_mul_left Y hactive
        _ ≤ X := Nat.sqrt_le X
    have hNqX : Nq ≤ X := Nat.div_le_self X (A * q)
    have hprimeNq := hprime Nq hYNq hNqX
    have hYcountNq := allowedPrimeCount_mono (S := S) hYNq
    have hdqNonneg : 0 ≤ dq := by
      change 0 ≤ arithmeticStarDegree S (A * q) X
      rw [arithmeticStarDegree, sub_nonneg]
      exact_mod_cast hYcountNq
    have hNqEq : Nq = N / q := by
      dsimp [Nq, N]
      rw [Nat.div_div_eq_div_mul]
    have hNqHalf : Nq ≤ N / 2 := by
      rw [hNqEq]
      exact Nat.div_le_div_left hqTwo (by omega)
    have hcountNqHalf := allowedPrimeCount_mono (S := S) hNqHalf
    have hgapIdentity : d - dq =
        (allowedPrimeCount S N : ℝ) - (allowedPrimeCount S Nq : ℝ) := by
      simp [d, dq, arithmeticStarDegree, N, Nq, A]
    have hgap :
        (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤ d - dq := by
      rw [hgapIdentity]
      exact hprime N (hYNq.trans (by rw [hNqEq]; exact Nat.div_le_self N q))
        (Nat.div_le_self X A) |>.1 |>.trans
          (sub_le_sub_left (by exact_mod_cast hcountNqHalf) _)
    have hawayMul : dq ≤ (15 / 16 : ℝ) * d := by
      have hsmall : d / 16 ≤ d - dq := by
        calc
          d / 16 ≤ (4 * ((N : ℝ) / Real.log (N : ℝ))) / 16 := by gcongr
          _ = (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
          _ ≤ d - dq := hgap
      linarith
    have hlogNPos : 0 < Real.log (N : ℝ) :=
      (hprime N (hYNq.trans (by rw [hNqEq]; exact Nat.div_le_self N q))
        (Nat.div_le_self X A)).2.2.1
    have hlogNqPos : 0 < Real.log (Nq : ℝ) := hprimeNq.2.2.1
    have hlogCompare : Real.log (N : ℝ) ≤ 3 * Real.log (Nq : ℝ) :=
      (hprime N (hYNq.trans (by rw [hNqEq]; exact Nat.div_le_self N q))
        (Nat.div_le_self X A)).2.2.2.1.trans hprimeNq.2.2.2.2
    have hNqMul : (Nq : ℝ) * q ≤ (N : ℝ) := by
      exact_mod_cast (by rw [hNqEq]; exact Nat.div_mul_le_self N q)
    have hratioMain :
        (Nq : ℝ) / Real.log (Nq : ℝ) ≤
          (3 / (q : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by
      have hcross :
          (Nq : ℝ) * (q : ℝ) * Real.log (N : ℝ) ≤
            3 * (N : ℝ) * Real.log (Nq : ℝ) := by
        calc
          (Nq : ℝ) * (q : ℝ) * Real.log (N : ℝ) ≤
              (N : ℝ) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_right hNqMul hlogNPos.le
          _ ≤ (N : ℝ) * (3 * Real.log (Nq : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogCompare (by positivity)
          _ = 3 * (N : ℝ) * Real.log (Nq : ℝ) := by ring
      rw [show (3 / (q : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) =
          ((3 * (N : ℝ) / (q : ℝ)) / Real.log (N : ℝ)) by ring]
      rw [div_le_div_iff₀ hlogNqPos hlogNPos]
      rw [show (3 * (N : ℝ) / (q : ℝ)) * Real.log (Nq : ℝ) =
          (3 * (N : ℝ) * Real.log (Nq : ℝ)) / (q : ℝ) by ring]
      exact (le_div_iff₀ hqPos).2
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcross)
    have hdqUpper : dq ≤
        4 * ((Nq : ℝ) / Real.log (Nq : ℝ)) := by
      change arithmeticStarDegree S (A * q) X ≤
        4 * ((Nq : ℝ) / Real.log (Nq : ℝ))
      rw [arithmeticStarDegree]
      exact (sub_le_self _ (by positivity)).trans hprimeNq.2.1
    have hdqRecip : dq ≤ (48 / (q : ℝ)) * d := by
      calc
        dq ≤ 4 * ((Nq : ℝ) / Real.log (Nq : ℝ)) := hdqUpper
        _ ≤ 4 * ((3 / (q : ℝ)) *
            ((N : ℝ) / Real.log (N : ℝ))) := by gcongr
        _ = (48 / (q : ℝ)) *
            ((1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ))) := by ring
        _ ≤ (48 / (q : ℝ)) * d := by
          gcongr
    rw [actualUpStarRatio, if_pos hactive]
    constructor
    · exact div_nonneg hdqNonneg hdPos.le
    constructor
    · exact (div_le_iff₀ hdPos).2 (by simpa [d, dq] using hawayMul)
    · exact (div_le_iff₀ hdPos).2 (by simpa [d, dq] using hdqRecip)
  · rw [actualUpStarRatio, if_neg hactive]
    refine ⟨by norm_num, by norm_num, ?_⟩
    exact div_nonneg (by norm_num) hqPos.le

/-- Uniform down-star ratios in every fixed sub-square-root power range. -/

theorem eventually_powerRange_downStarRatio_ge
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InPowerRange θ X (a : ℕ) →
        ∀ q ∈ (a : ℕ).primeFactors,
          17 / 16 ≤ arithmeticStarDegree S ((a : ℕ) / q) X /
            arithmeticStarDegree S (a : ℕ) X := by
  filter_upwards [eventually_powerRange_arithmeticStarDegree_bounds S hS hθ,
      eventually_squareRootRange_allowedPrime_bounds S hS]
      with X hdegree hprime
  intro a ha q hq
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let N : ℕ := X / A
  let b : ℕ := A / q
  let Nb : ℕ := X / b
  let d : ℝ := arithmeticStarDegree S A X
  let db : ℝ := arithmeticStarDegree S b X
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hqDvd : q ∣ A := Nat.dvd_of_mem_primeFactors hq
  have hAPos : 0 < A := PrimeStar.Vertex.coe_pos a
  have hbPos : 0 < b := by
    dsimp [b]
    exact Nat.div_pos (Nat.le_of_mem_primeFactors hq) hqPrime.pos
  have hbLeA : b ≤ A := by
    dsimp [b]
    exact Nat.div_le_self A q
  have hbMul : b * q = A := by
    dsimp [b]
    exact Nat.div_mul_cancel hqDvd
  have hdegreeA := hdegree a ha
  have hdPos : 0 < d := by simpa [d, A] using hdegreeA.2.1
  have hYN : Y ≤ N := hdegreeA.1.trans (Nat.div_le_self N 2)
  have hNleNb : N ≤ Nb := by
    dsimp [N, Nb]
    exact Nat.div_le_div_left hbLeA (by omega)
  have hYNb : Y ≤ Nb := hYN.trans hNleNb
  have hNbX : Nb ≤ X := Nat.div_le_self X b
  have hprimeNb := hprime Nb hYNb hNbX
  have hNEq : N = Nb / q := by
    dsimp [N, Nb]
    rw [Nat.div_div_eq_div_mul, hbMul]
  have hNhalf : N ≤ Nb / 2 := by
    rw [hNEq]
    exact Nat.div_le_div_left hqTwo (by omega)
  have hcountNhalf := allowedPrimeCount_mono (S := S) hNhalf
  have hgapIdentity : db - d =
      (allowedPrimeCount S Nb : ℝ) - (allowedPrimeCount S N : ℝ) := by
    simp [db, d, arithmeticStarDegree, Nb, N, b, A]
  have hgap :
      (1 / 4 : ℝ) * ((Nb : ℝ) / Real.log (Nb : ℝ)) ≤ db - d := by
    rw [hgapIdentity]
    exact hprimeNb.1.trans
      (sub_le_sub_left (by exact_mod_cast hcountNhalf) _)
  have hcountNNb := allowedPrimeCount_mono (S := S) hNleNb
  have hdUpper : d ≤ 4 * ((Nb : ℝ) / Real.log (Nb : ℝ)) := by
    calc
      d ≤ (allowedPrimeCount S N : ℝ) := by
        change arithmeticStarDegree S A X ≤
          (allowedPrimeCount S N : ℝ)
        rw [arithmeticStarDegree]
        exact sub_le_self _ (by positivity)
      _ ≤ (allowedPrimeCount S Nb : ℝ) := by exact_mod_cast hcountNNb
      _ ≤ 4 * ((Nb : ℝ) / Real.log (Nb : ℝ)) := hprimeNb.2.1
  have hratioMul : (17 / 16 : ℝ) * d ≤ db := by
    have hsmall : d / 16 ≤ db - d := by
      calc
        d / 16 ≤ (4 * ((Nb : ℝ) / Real.log (Nb : ℝ))) / 16 := by gcongr
        _ = (1 / 4 : ℝ) * ((Nb : ℝ) / Real.log (Nb : ℝ)) := by ring
        _ ≤ db - d := hgap
    linarith
  exact (le_div_iff₀ hdPos).2 (by simpa [d, db] using hratioMul)

/-- An explicit source-independent constant for the logarithmic first-exit
bound on a fixed power range. -/


/- Source slice: BoundaryLeafSquareSum.lean -/

theorem boundaryLeafCountSquareSumOnStar_eq_labelSum
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : PrimeStar.Vertex S X) (ha : (a : ℕ) ≤ Y) :
    boundaryLeafCountSquareSumOnStar S X Y a =
      ∑ p ∈ PrimeStar.largePrimeLabels S X Y a,
        PrimeStar.allowedPrimeCount S
          (min Y (X / ((a : ℕ) * p))) ^ 2 := by
  classical
  unfold boundaryLeafCountSquareSumOnStar
  symm
  apply Finset.sum_bij
      (fun p hp ↦ arithmeticBoundaryLeaf (Y := Y) hS a p hp)
  · intro p hp
    rw [PrimeStar.mem_largePrimeLeaves_iff_child ha]
    have hpdata := Finset.mem_filter.mp hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hpdata.1).2
    exact ⟨p, hpprime, hpdata.2.1, hpdata.2.2, rfl⟩
  · intro p hp q hq hpq
    have hpEq : (a : ℕ) * p = (a : ℕ) * q :=
      congrArg (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) hpq
    exact Nat.eq_of_mul_eq_mul_left (PrimeStar.Vertex.coe_pos a) hpEq
  · intro v hv
    have hchild : PrimeStar.IsLargePrimeChild S Y a v :=
      (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hv
    obtain ⟨p, hpprime, hpS, hpY, hapv⟩ := hchild
    have hpLE : p ≤ X / (a : ℕ) := by
      apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos a)).2
      calc
        p * (a : ℕ) = (a : ℕ) * p := Nat.mul_comm _ _
        _ = (v : ℕ) := hapv
        _ ≤ X := PrimeStar.Vertex.coe_le v
    have hpLabels : p ∈ PrimeStar.largePrimeLabels S X Y a := by
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hpLE, hpprime⟩, hpS, hpY⟩
    refine ⟨p, hpLabels, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    exact hapv
  · intro p hp
    rw [boundaryLeafExitCount_arithmeticBoundaryLeaf hS a p hp]

/-- A completely elementary pointwise bound for one boundary-leaf count,
written in its arithmetic form. -/

theorem allowedPrimeCount_min_le_twice_div
    {S : Finset ℕ} {X Y : ℕ}
    (a : PrimeStar.Vertex S X) (p : ℕ)
    (hp : p ∈ PrimeStar.largePrimeLabels S X Y a) :
    PrimeStar.allowedPrimeCount S (min Y (X / ((a : ℕ) * p))) ≤
      2 * (X / ((a : ℕ) * p)) := by
  let N := min Y (X / ((a : ℕ) * p))
  have hcount : PrimeStar.allowedPrimeCount S N ≤ N + 1 := by
    exact (PrimeStar.allowedPrimeCount_le_primeCounting S N).trans (by
      simpa [Nat.primeCounting, Nat.primeCounting'] using
        (Nat.count_le (p := Nat.Prime) (n := N + 1)))
  have hpdata := Finset.mem_filter.mp hp
  have hpLE : p ≤ X / (a : ℕ) := (Nat.mem_primesLE.mp hpdata.1).1
  have hapX : (a : ℕ) * p ≤ X := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos a)).1 hpLE
  have hpPos : 0 < p := (Nat.mem_primesLE.mp hpdata.1).2.pos
  have hapPos : 0 < (a : ℕ) * p :=
    Nat.mul_pos (PrimeStar.Vertex.coe_pos a) hpPos
  have hdivOne : 1 ≤ X / ((a : ℕ) * p) := by
    exact (Nat.le_div_iff_mul_le hapPos).2 (by simpa using hapX)
  have hN : N ≤ X / ((a : ℕ) * p) := min_le_right _ _
  dsimp [N] at hcount hN ⊢
  omega

/-- The graph square sum is controlled by the inverse-square mass of its
large-prime labels. -/

theorem boundaryLeafCountSquareSumOnStar_le_inverseSquareInterval
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : PrimeStar.Vertex S X) (ha : (a : ℕ) ≤ Y) :
    (boundaryLeafCountSquareSumOnStar S X Y a : ℝ) ≤
      4 * ((X : ℝ) / (a : ℝ)) ^ 2 *
        allowedPrimeInverseSquareInterval S Y (X / (a : ℕ)) := by
  rw [boundaryLeafCountSquareSumOnStar_eq_labelSum hS a ha,
    Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [allowedPrimeInverseSquareInterval]
  change
    (∑ p ∈ PrimeStar.allowedPrimeInterval S Y (X / (a : ℕ)),
        (PrimeStar.allowedPrimeCount S
          (min Y (X / ((a : ℕ) * p))) : ℝ) ^ 2) ≤ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  have hpPrime : p.Prime := (Nat.mem_primesLE.mp hpdata.1).2
  have hpPos : 0 < p := hpPrime.pos
  have haPos : 0 < (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hapPosNat : 0 < (a : ℕ) * p :=
    Nat.mul_pos (PrimeStar.Vertex.coe_pos a) hpPos
  have hcountNat :=
    allowedPrimeCount_min_le_twice_div a p hp
  have hcountCast :
      (PrimeStar.allowedPrimeCount S
          (min Y (X / ((a : ℕ) * p))) : ℝ) ≤
        2 * ((X : ℝ) / (((a : ℕ) * p : ℕ) : ℝ)) := by
    calc
      (PrimeStar.allowedPrimeCount S
          (min Y (X / ((a : ℕ) * p))) : ℝ) ≤
          (2 * (X / ((a : ℕ) * p)) : ℕ) := by exact_mod_cast hcountNat
      _ = 2 * ((X / ((a : ℕ) * p) : ℕ) : ℝ) := by norm_num
      _ ≤ 2 * ((X : ℝ) / (((a : ℕ) * p : ℕ) : ℝ)) := by
        gcongr
        exact Nat.cast_div_le
  have hcountNonneg :
      0 ≤ (PrimeStar.allowedPrimeCount S
        (min Y (X / ((a : ℕ) * p))) : ℝ) := Nat.cast_nonneg _
  have hdivNonneg :
      0 ≤ 2 * ((X : ℝ) / (((a : ℕ) * p : ℕ) : ℝ)) := by positivity
  have hsquare :
      (PrimeStar.allowedPrimeCount S
          (min Y (X / ((a : ℕ) * p))) : ℝ) ^ 2 ≤
        (2 * ((X : ℝ) / (((a : ℕ) * p : ℕ) : ℝ))) ^ 2 := by
    nlinarith
  calc
    (PrimeStar.allowedPrimeCount S
        (min Y (X / ((a : ℕ) * p))) : ℝ) ^ 2 ≤
        (2 * ((X : ℝ) / (((a : ℕ) * p : ℕ) : ℝ))) ^ 2 := hsquare
    _ = 4 * ((X : ℝ) / (a : ℝ)) ^ 2 * (p : ℝ) ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (Nat.cast_nonneg p)]
      norm_num at *
      field_simp
      ring

/-- Finite Chebyshev-scale boundary-leaf estimate.  The constants are
deliberately explicit and unoptimized. -/

theorem boundaryLeafCountSquareSumOnStar_le_chebyshev
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : PrimeStar.Vertex S X) (ha : (a : ℕ) ≤ Y)
    (hY : 2 ≤ Y) (hYXa : Y ≤ X / (a : ℕ)) :
    (boundaryLeafCountSquareSumOnStar S X Y a : ℝ) ≤
      4 * ((X : ℝ) / (a : ℝ)) ^ 2 *
        ((6 * Real.log 4 / Real.log (Y : ℝ)) * (Y : ℝ) ^ (-1 : ℝ) +
          5 * (Y : ℝ) ^ (-(3 / 2 : ℝ))) := by
  calc
    (boundaryLeafCountSquareSumOnStar S X Y a : ℝ) ≤
        4 * ((X : ℝ) / (a : ℝ)) ^ 2 *
          allowedPrimeInverseSquareInterval S Y (X / (a : ℕ)) :=
      boundaryLeafCountSquareSumOnStar_le_inverseSquareInterval hS a ha
    _ ≤ 4 * ((X : ℝ) / (a : ℝ)) ^ 2 *
        ((6 * Real.log 4 / Real.log (Y : ℝ)) * (Y : ℝ) ^ (-1 : ℝ) +
          5 * (Y : ℝ) ^ (-(3 / 2 : ℝ))) := by
      gcongr
      exact allowedPrimeInverseSquareInterval_le_chebyshev hY hYXa

/-- Direct quantitative control of the discarded large-prime zero mode.
This is the finite graph-theoretic consumer of the inverse-square tail. -/


/- Source slice: ExactMoleculeFiniteCorrection.lean -/

local instance exactMoleculeFiniteCorrectionSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj := Classical.decRel _

local instance exactMoleculeFiniteCorrectionLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj := Classical.decRel _

/-- Uniform exact-molecule root window throughout every fixed power range
strictly below the square-root boundary.  The exact-molecule Weyl estimate is
fed the global tuned small-prime norm; the PNT degree lower bound then makes
that residual at most one percent of the star energy.  This is the finite
window used by the signed response and kernel estimates. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (a : ℕ) ≤ squareRootCutoff X ∧
        0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a ∧
        |exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a| ≤
          moleculeStarEnergy S X a / 100 ∧
        1000000 * PrimeStar.sqrtCutoffResidualScale X ^ 2 ≤
          moleculeStarEnergy S X a ^ 2 := by
  let C : ℝ := 32000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num)
      (sq_pos_of_pos PrimeStar.sqrtCutoffResidualConstant_pos)
  have hlim := (tendsto_powerScale_div_sqrt_zero htheta).const_mul C
  have hsmall : ∀ᶠ X : ℕ in atTop,
      C * (powerScale theta X / Real.sqrt (X : ℝ)) < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  filter_upwards [eventually_powerRange_arithmeticStarDegree_bounds S hS htheta,
      eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
      PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned,
      PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
      hsmall, eventually_ge_atTop 4]
      with X hdegree hcenter hresidual hresSq hsmallX hX
  intro a ha
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let N : ℕ := X / A
  let eta : ℝ := PrimeStar.sqrtCutoffResidualScale X
  let mu : ℝ := moleculeStarEnergy S X a
  have hApos : 0 < A := PrimeStar.Vertex.coe_pos a
  have htwoAY : 2 * A ≤ Y := hcenter A ha
  have hYleX : Y ≤ X := Nat.sqrt_le_self X
  have htwoAX : 2 * A ≤ X := htwoAY.trans hYleX
  have hYXa : Y ≤ X / A := by
    apply (Nat.le_div_iff_mul_le hApos).2
    calc
      Y * A ≤ Y * Y := Nat.mul_le_mul_left Y (by omega : A ≤ Y)
      _ ≤ X := Nat.sqrt_le X
  have hcountMono := PrimeStar.allowedPrimeCount_mono (S := S) hYXa
  have hdegreeEq :
      (PrimeStar.largePrimeStarDegree S X Y a : ℝ) =
        arithmeticStarDegree S A X := by
    rw [PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS a
      (by omega : A ≤ Y) hYXa, Nat.cast_sub hcountMono]
    rfl
  have hdegreeData := hdegree a ha
  have hdArith : 0 < arithmeticStarDegree S A X := by
    simpa [A] using hdegreeData.2.1
  have hd : 0 < PrimeStar.largePrimeStarDegree S X Y a := by
    exact_mod_cast (show (0 : ℝ) <
      (PrimeStar.largePrimeStarDegree S X Y a : ℝ) by
        rw [hdegreeEq]
        exact hdArith)
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.div_pos (by omega) hApos
  have hNleX : N ≤ X := Nat.div_le_self X A
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by
      have : 2 ≤ N := by
        apply (Nat.le_div_iff_mul_le hApos).2
        simpa [mul_comm] using htwoAX
      omega)
  have hlogNX : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hNleX)
  have hfloor := real_div_sub_one_lt_natCast_div X A hApos
  have htwoReal : (2 : ℝ) ≤ (X : ℝ) / (A : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hApos : (0 : ℝ) < A)).2
    exact_mod_cast htwoAX
  have hNlower : (X : ℝ) / (2 * (A : ℝ)) ≤ (N : ℝ) := by
    have : (X : ℝ) / (2 * (A : ℝ)) ≤ (X : ℝ) / (A : ℝ) - 1 := by
      have hAreal : (0 : ℝ) < A := by exact_mod_cast hApos
      have hrewrite :
          (X : ℝ) / (2 * (A : ℝ)) = ((X : ℝ) / (A : ℝ)) / 2 := by
        field_simp [ne_of_gt hAreal]
      rw [hrewrite]
      nlinarith
    exact this.trans hfloor.le
  have hdLower :
      (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤
        arithmeticStarDegree S A X := by
    simpa [A, N] using hdegreeData.2.2.1
  have hdCoarse :
      (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) ≤
        arithmeticStarDegree S A X := by
    calc
      (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) =
          (1 / 4 : ℝ) * (((X : ℝ) / (2 * (A : ℝ))) /
            Real.log (X : ℝ)) := by ring
      _ ≤ (1 / 4 : ℝ) * ((N : ℝ) / Real.log (X : ℝ)) := by gcongr
      _ ≤ (1 / 4 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) := by
        have hNnonneg : (0 : ℝ) ≤ N := by positivity
        have hdiv : (N : ℝ) / Real.log (X : ℝ) ≤
            (N : ℝ) / Real.log (N : ℝ) := by
          exact div_le_div_of_nonneg_left hNnonneg hlogN hlogNX
        exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ ≤ arithmeticStarDegree S A X := hdLower
  have hscale :
      32000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 * (A : ℝ) ≤
        Real.sqrt (X : ℝ) := by
    have hpow : (A : ℝ) ≤ powerScale theta X := ha.2
    have hsqrtPos : 0 < Real.sqrt (X : ℝ) := by positivity
    have hratio : C * ((A : ℝ) / Real.sqrt (X : ℝ)) < 1 := by
      calc
        C * ((A : ℝ) / Real.sqrt (X : ℝ)) ≤
            C * (powerScale theta X / Real.sqrt (X : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hpow hsqrtPos.le) hC.le
        _ < 1 := hsmallX
    have hmul : C * (A : ℝ) < Real.sqrt (X : ℝ) := by
      calc
        C * (A : ℝ) =
            (C * ((A : ℝ) / Real.sqrt (X : ℝ))) *
              Real.sqrt (X : ℝ) := by
                field_simp [ne_of_gt hsqrtPos]
        _ < 1 * Real.sqrt (X : ℝ) :=
          mul_lt_mul_of_pos_right hratio hsqrtPos
        _ = Real.sqrt (X : ℝ) := one_mul _
    dsimp [C] at hmul ⊢
    exact hmul.le
  have hetaSq :
      eta ^ 2 ≤ 4 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
        (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by
    simpa [eta] using hresSq
  have hsqrtSq : Real.sqrt (X : ℝ) ^ 2 = (X : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hscaled : 1000000 * eta ^ 2 ≤ arithmeticStarDegree S A X := by
    calc
      1000000 * eta ^ 2 ≤
          4000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
            (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by
        nlinarith [hetaSq]
      _ ≤ (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) := by
        have hAreal : (0 : ℝ) < A := by exact_mod_cast hApos
        have hsqrtPos : 0 < Real.sqrt (X : ℝ) := by positivity
        have hbase :
            4000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
                Real.sqrt (X : ℝ) ≤ (X : ℝ) / (8 * (A : ℝ)) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * A)]
          calc
            4000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
                  Real.sqrt (X : ℝ) * (8 * (A : ℝ)) =
                (32000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
                  (A : ℝ)) * Real.sqrt (X : ℝ) := by ring
            _ ≤ Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) := by gcongr
            _ = (X : ℝ) := by nlinarith [hsqrtSq]
        have hdiv := div_le_div_of_nonneg_right hbase hlogX.le
        calc
          4000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
                (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) =
              (4000000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
                Real.sqrt (X : ℝ)) / Real.log (X : ℝ) := by ring
          _ ≤ ((X : ℝ) / (8 * (A : ℝ))) / Real.log (X : ℝ) := hdiv
          _ = (X : ℝ) / (8 * (A : ℝ) * Real.log (X : ℝ)) := by ring
      _ ≤ arithmeticStarDegree S A X := hdCoarse
  have hetaNonneg : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hmuSq : mu ^ 2 = arithmeticStarDegree S A X := by
    dsimp [mu]
    rw [moleculeStarEnergy_sq, hdegreeEq]
  have hmuNonneg : 0 ≤ mu := moleculeStarEnergy_nonneg _ _ _
  have hsq : (1000 * eta) ^ 2 ≤ mu ^ 2 := by
    rw [mul_pow, hmuSq]
    norm_num
    exact hscaled
  have hsmallEta : 1000 * eta ≤ mu := by
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) hetaNonneg) hmuNonneg).mp hsq
  have hH : ∀ y : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) y‖ ≤
        eta * ‖y‖ := by
    intro y
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S y
  have hrootShift :
      |exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a| ≤ eta :=
    exactPrincipalMoleculeRoot_sub_starEnergy_abs_le_smallPrime
      hS (by simpa [Y] using (show A ≤ Y by omega)) hd eta hH
  have hsmallEtaDiv : eta ≤ mu / 100 := by linarith
  exact ⟨by simpa [Y] using (show A ≤ Y by omega),
    by simpa [Y] using hd,
    hrootShift.trans (by simpa [mu] using hsmallEtaDiv),
    by simpa [eta, mu, hmuSq] using hscaled⟩

/-- Root-window projection of the stronger estimate above. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_window
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (a : ℕ) ≤ squareRootCutoff X ∧
        0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a ∧
        |exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a| ≤
          moleculeStarEnergy S X a / 100 := by
  filter_upwards [
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
      S hS htheta] with X hX
  intro a ha
  exact ⟨(hX a ha).1, (hX a ha).2.1, (hX a ha).2.2.1⟩

/-- A scalar separated from every eigenvalue of a finite real symmetric
operator gives a lower bound for the corresponding shifted operator.  This
is the all-eigenvalue counterpart of the isolated-mode estimate used in the
Paper I matching argument. -/

private theorem shiftedOperator_lowerBound_of_all_eigenvalue_gaps
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (C : E →ₗ[ℝ] E) (hC : C.IsSymmetric) (lambda gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (hsep : ∀ i : Fin (Module.finrank ℝ E),
      gamma ≤ |lambda - hC.eigenvalues rfl i|)
    (x : E) :
    gamma * ‖x‖ ≤ ‖lambda • x - C x‖ := by
  let b := hC.eigenvectorBasis rfl
  let ev := hC.eigenvalues rfl
  let y := lambda • x - C x
  have hycoeff : ∀ i, b.repr y i =
      (lambda - ev i) * b.repr x i := by
    intro i
    have hdiag := hC.eigenvectorBasis_apply_self_apply rfl x i
    change b.repr (C x) i = ev i * b.repr x i at hdiag
    dsimp [y]
    rw [map_sub, map_smul]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hdiag]
    ring
  have hsum :
      gamma ^ 2 * ∑ i, (b.repr x i) ^ 2 ≤
        ∑ i, ((lambda - ev i) * b.repr x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    have hgapSq : gamma ^ 2 ≤ (lambda - ev i) ^ 2 := by
      calc
        gamma ^ 2 ≤ |lambda - ev i| ^ 2 :=
          (sq_le_sq₀ hgamma (abs_nonneg _)).2 (hsep i)
        _ = (lambda - ev i) ^ 2 := sq_abs _
    calc
      gamma ^ 2 * (b.repr x i) ^ 2 ≤
          (lambda - ev i) ^ 2 * (b.repr x i) ^ 2 :=
        mul_le_mul_of_nonneg_right hgapSq (sq_nonneg _)
      _ = ((lambda - ev i) * b.repr x i) ^ 2 := by ring
  have hsq : (gamma * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by
    calc
      (gamma * ‖x‖) ^ 2 =
          gamma ^ 2 * ∑ i, (b.repr x i) ^ 2 := by
        rw [mul_pow, ← b.repr.norm_map x,
          EuclideanSpace.real_norm_sq_eq]
      _ ≤ ∑ i, ((lambda - ev i) * b.repr x i) ^ 2 := hsum
      _ = ∑ i, (b.repr y i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hycoeff]
      _ = ‖b.repr y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      _ = ‖y‖ ^ 2 := by rw [b.repr.norm_map]
  have hleft : 0 ≤ gamma * ‖x‖ :=
    mul_nonneg hgamma (norm_nonneg x)
  have hright : 0 ≤ ‖y‖ := norm_nonneg y
  dsimp [y] at hsq ⊢
  nlinarith

/-- Every nonzero eigenvalue of the first-exit large-prime compression comes
from one of the selected non-isolated first-exit stars.  Isolated first exits
contribute only the zero eigenvalue. -/

private theorem firstExitCompression_eigenvalue_eq_zero_or_selectedStarDegree
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    {x : MoleculeAmbient S X} {xi : ℝ}
    (hx : PrimeStar.firstExitLargePrimeCompressionOperator S X
        (squareRootCutoff X) a x = xi • x)
    (hx0 : x ≠ 0) :
    xi = 0 ∨
      ∃ k ∈ PrimeStar.firstExitLowerCenters S X
          (squareRootCutoff X) a,
        xi = Real.sqrt (PrimeStar.largePrimeStarDegree S X
            (squareRootCutoff X) k : ℝ) ∨
          xi = -Real.sqrt (PrimeStar.largePrimeStarDegree S X
            (squareRootCutoff X) k : ℝ) := by
  by_cases hxi : xi = 0
  · exact Or.inl hxi
  right
  let Y := squareRootCutoff X
  let F := PrimeStar.firstExitCompressionSupport S X Y a
  have hsupport : ∀ v, v ∉ F → x v = 0 := by
    intro v hv
    have hcoord := congrArg (fun z : MoleculeAmbient S X ↦ z v) hx
    have hzero :
        PrimeStar.firstExitLargePrimeCompressionOperator S X Y a x v = 0 := by
      simp [PrimeStar.firstExitLargePrimeCompressionOperator,
        PrimeStar.firstExitCompressionProjection_apply, F, hv]
    rw [hzero] at hcoord
    simp only [PiLp.smul_apply, smul_eq_mul] at hcoord
    exact (mul_eq_zero.mp hcoord.symm).resolve_left hxi
  have hxL : Matrix.toEuclideanLin
      ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ) x = xi • x := by
    rw [← PrimeStar.firstExitLargePrimeCompressionOperator_eq_of_supported
      (PrimeStar.sqrtCutoff_condition X) x (by simpa [F, Y] using hsupport)]
    simpa [Y] using hx
  obtain ⟨v, hv⟩ : ∃ v : PrimeStar.Vertex S X, x v ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    ext v
    exact h v
  have hvF : v ∈ F := by
    by_contra hvnot
    exact hv (hsupport v hvnot)
  obtain ⟨b, hbY, hvb, hbd, hbxi⟩ :=
    PrimeStar.exists_signedStarDegree_of_eigenvector_coordinate_ne_zero
      (PrimeStar.sqrtCutoff_condition X) hxL hxi hv
  have hvUnion : v ∈ PrimeStar.largePrimeStarUnionSupport S X Y
      (PrimeStar.firstExitLowerCenters S X Y a) := by
    rcases Finset.mem_union.mp hvF with hvStars | hvIso
    · exact hvStars
    · have hviso :=
        (PrimeStar.mem_firstExitIsolatedVertices.mp hvIso).2
      rw [PrimeStar.mem_largePrimeStarSupport] at hvb
      rcases hvb with rfl | hbv
      · have hbNonisolated :
            ¬(PrimeStar.largePrimeGraph S X Y).IsIsolated v := by
          rw [← SimpleGraph.degree_pos]
          simpa [PrimeStar.largePrimeStarDegree_eq_degree] using hbd
        exact False.elim (hbNonisolated hviso)
      · exact False.elim (hviso b (PrimeStar.largePrimeAdj_symm hbv))
  obtain ⟨k, hk, hvk⟩ :=
    PrimeStar.mem_largePrimeStarUnionSupport.mp hvUnion
  have hkY := (PrimeStar.mem_firstExitLowerCenters.mp hk).1
  have hbk : b = k := by
    by_contra hne
    exact (Finset.disjoint_left.mp
      (PrimeStar.disjoint_largePrimeStarSupport
        (PrimeStar.sqrtCutoff_condition X) hbY hkY hne)) hvb hvk
  subst b
  exact ⟨k, hk, hbxi⟩

/-- The preceding root window also protects every canonical up-star
denominator by a fixed fraction of the boundary-star energy.  This packages
the nonzero root, the coarse root magnitude, and the exact gap consumed by
the signed-response boundary-kernel estimate. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_responseWindow
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        let lambda := exactPrincipalMoleculeRoot S X a
        let mu := moleculeStarEnergy S X a
        lambda ≠ 0 ∧ |lambda| ≤ 2 * mu ∧
          ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
            mu ^ 2 / 100 ≤
              |lambda ^ 2 -
                (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
                  (PrimeStar.canonicalUpTarget hS a q) : ℝ)| := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window
      S hS htheta,
    eventually_powerRange_actualUpStarRatio_bounds S hS htheta]
      with X hwindow hratio
  intro a ha
  dsimp only
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  let lambda := exactPrincipalMoleculeRoot S X a
  let mu := moleculeStarEnergy S X a
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hshift' : |lambda - mu| ≤ mu / 100 := by
    simpa [lambda, mu] using hshift
  have hbounds := abs_le.mp hshift'
  have hlambdaLower : (99 / 100 : ℝ) * mu ≤ lambda := by
    nlinarith
  have hlambdaUpper : lambda ≤ (101 / 100 : ℝ) * mu := by
    nlinarith
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le
    (mul_pos (by norm_num) hmu) hlambdaLower
  have hlambdaNonneg : 0 ≤ lambda := hlambdaPos.le
  have hroot : lambda ≠ 0 := ne_of_gt hlambdaPos
  have habs : |lambda| ≤ 2 * mu := by
    rw [abs_of_pos hlambdaPos]
    nlinarith
  refine ⟨hroot, habs, ?_⟩
  intro q
  let d : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a
  let dq : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
    (PrimeStar.canonicalUpTarget hS a q)
  have hdReal : 0 < d := by
    dsimp [d]
    exact_mod_cast hd
  have hmuSq : mu ^ 2 = d := by
    simpa [mu, d] using moleculeStarEnergy_sq S X a
  have hqdata := Finset.mem_filter.mp q.property
  have hqmem : (q : ℕ) ∈
      (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S) :=
    Finset.mem_filter.mpr ⟨hqdata.1, hqdata.2.1⟩
  have hratioArithmetic := (hratio a ha (q : ℕ) hqmem).2.1
  change PrimeStar.fixedCenterActualUpRatio S (a : ℕ) X (q : ℕ) ≤
      15 / 16 at hratioArithmetic
  have hratioGraph :=
    PrimeStar.canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a haY q
  rw [← hratioGraph] at hratioArithmetic
  have hdq : dq ≤ (15 / 16 : ℝ) * mu ^ 2 := by
    rw [hmuSq]
    exact (div_le_iff₀ hdReal).mp (by simpa [d, dq] using hratioArithmetic)
  have hlambdaSq : ((99 / 100 : ℝ) * mu) ^ 2 ≤ lambda ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) hmu.le) hlambdaNonneg).2
      hlambdaLower
  have hgap : mu ^ 2 / 100 ≤ lambda ^ 2 - dq := by
    nlinarith
  simpa [lambda, mu, dq] using
    hgap.trans (le_abs_self (lambda ^ 2 - dq))

/-- The same root window protects every canonical down-star denominator.
Unlike an up-star, a down-star has larger degree than the boundary star; the
uniform ratio `17 / 16` leaves a fixed gap even after the one-percent root
displacement. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_downResponseWindow
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        let lambda := exactPrincipalMoleculeRoot S X a
        let mu := moleculeStarEnergy S X a
        ∀ q : PrimeStar.CanonicalDownIndex a,
          mu ^ 2 / 100 ≤
            |lambda ^ 2 -
              (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
                (PrimeStar.canonicalDownTarget a q) : ℝ)| := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window
      S hS htheta,
    eventually_powerRange_downStarRatio_ge S hS htheta]
      with X hwindow hratio
  intro a ha
  dsimp only
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  let lambda := exactPrincipalMoleculeRoot S X a
  let mu := moleculeStarEnergy S X a
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hshift' : |lambda - mu| ≤ mu / 100 := by
    simpa [lambda, mu] using hshift
  have hbounds := abs_le.mp hshift'
  have hlambdaUpper : lambda ≤ (101 / 100 : ℝ) * mu := by
    nlinarith
  have hlambdaLower : (99 / 100 : ℝ) * mu ≤ lambda := by
    nlinarith
  have hlambdaNonneg : 0 ≤ lambda :=
    (lt_of_lt_of_le (mul_pos (by norm_num) hmu) hlambdaLower).le
  intro q
  let d : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a
  let dq : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
    (PrimeStar.canonicalDownTarget a q)
  have hdReal : 0 < d := by
    dsimp [d]
    exact_mod_cast hd
  have hmuSq : mu ^ 2 = d := by
    simpa [mu, d] using moleculeStarEnergy_sq S X a
  have hratioArithmetic := hratio a ha (q : ℕ) q.property
  change 17 / 16 ≤
      PrimeStar.fixedCenterArithmeticDegree S ((a : ℕ) / (q : ℕ)) X /
        PrimeStar.fixedCenterArithmeticDegree S (a : ℕ) X at hratioArithmetic
  have hratioGraph :=
    PrimeStar.canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio
      hS a haY q
  rw [← hratioGraph] at hratioArithmetic
  have hdq : (17 / 16 : ℝ) * mu ^ 2 ≤ dq := by
    rw [hmuSq]
    exact (le_div_iff₀ hdReal).mp (by simpa [d, dq] using hratioArithmetic)
  have hlambdaSq : lambda ^ 2 ≤ ((101 / 100 : ℝ) * mu) ^ 2 :=
    (sq_le_sq₀ hlambdaNonneg
      (mul_nonneg (by norm_num) hmu.le)).2 hlambdaUpper
  have hgap : mu ^ 2 / 100 ≤ dq - lambda ^ 2 := by
    nlinarith
  simpa [lambda, mu, dq, abs_sub_comm] using
    hgap.trans (le_abs_self (dq - lambda ^ 2))

/-- Every non-isolated star selected by the literal first-exit compression
is one of the canonical arithmetic targets `a*q` or `a/q`.  Consequently the
two response windows above discharge all denominator hypotheses used by the
exact signed response and boundary-kernel formulas. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ k ∈ PrimeStar.firstExitLowerCenters S X
            (squareRootCutoff X) a,
          exactPrincipalMoleculeRoot S X a ^ 2 ≠
            (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_responseWindow
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_downResponseWindow
      S hS htheta]
      with X hwindow hup hdown
  intro a ha k hk
  obtain ⟨haY, hd, _hshift⟩ := hwindow a ha
  let mu := moleculeStarEnergy S X a
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  obtain ⟨q, hqPrime, hqS, hqY, hqUp | hqDown⟩ :=
    PrimeStar.mem_firstExitLowerCenters_arithmetic
      (PrimeStar.sqrtCutoff_condition X) haY hk
  · have hqMem : q ∈ PrimeStar.canonicalUpPrimeLabels S X
        (squareRootCutoff X) a := by
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_primesLE.mpr ⟨hqY, hqPrime⟩, hqS,
        hqUp.trans_le (PrimeStar.Vertex.coe_le k)⟩
    let qi : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a :=
      ⟨q, hqMem⟩
    have htarget : PrimeStar.canonicalUpTarget hS a qi = k := by
      apply Subtype.ext
      apply Fin.ext
      exact hqUp
    have hgap := (hup a ha).2.2 qi
    rw [htarget] at hgap
    intro heq
    rw [heq, sub_self, abs_zero] at hgap
    have hmuSqPos : 0 < mu ^ 2 := sq_pos_of_pos hmu
    nlinarith
  · have hqDvd : q ∣ (a : ℕ) :=
      ⟨(k : ℕ), by simpa [Nat.mul_comm] using hqDown.symm⟩
    have hqMem : q ∈ (a : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hqPrime, hqDvd, (PrimeStar.Vertex.coe_pos a).ne'⟩
    let qi : PrimeStar.CanonicalDownIndex a := ⟨q, hqMem⟩
    have htarget : PrimeStar.canonicalDownTarget a qi = k := by
      apply Subtype.ext
      apply Fin.ext
      apply Nat.eq_of_mul_eq_mul_right hqPrime.pos
      calc
        (PrimeStar.canonicalDownTarget a qi : ℕ) * q = (a : ℕ) :=
          PrimeStar.canonicalDownTarget_mul_coe a qi
        _ = (k : ℕ) * q := hqDown.symm
    have hgap := hdown a ha qi
    rw [htarget] at hgap
    intro heq
    rw [heq, sub_self, abs_zero] at hgap
    have hmuSqPos : 0 < mu ^ 2 := sq_pos_of_pos hmu
    nlinarith

/-- Uniform gap for the literal first-exit compression at the exact
two-mode molecule root.  The proof uses only the stars actually selected by
the first exits: their centres are `a*q` or `a/q`, so the multiplicative
degree ratios keep their signed star eigenvalues a fixed fraction of the
boundary-star energy away from the exact root.  In particular, no global
adjacent-centre degree gap is used. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        let lambda := exactPrincipalMoleculeRoot S X a
        let mu := moleculeStarEnergy S X a
        ∀ x : MoleculeAmbient S X,
          (mu / 100) * ‖x‖ ≤
            ‖lambda • x -
              PrimeStar.firstExitLargePrimeCompressionOperator S X
                (squareRootCutoff X) a x‖ := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window
      S hS htheta,
    eventually_powerRange_actualUpStarRatio_bounds S hS htheta,
    eventually_powerRange_downStarRatio_ge S hS htheta]
      with X hwindow hup hdown
  intro a ha
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  let lambda := exactPrincipalMoleculeRoot S X a
  let mu := moleculeStarEnergy S X a
  let C := PrimeStar.firstExitLargePrimeCompressionOperator S X
    (squareRootCutoff X) a
  let hC := PrimeStar.firstExitLargePrimeCompressionOperator_isSymmetric
    S X (squareRootCutoff X) a
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hshift' : |lambda - mu| ≤ mu / 100 := by
    simpa [lambda, mu] using hshift
  have hbounds := abs_le.mp hshift'
  have hlambdaLower : (99 / 100 : ℝ) * mu ≤ lambda := by
    nlinarith
  have hlambdaUpper : lambda ≤ (101 / 100 : ℝ) * mu := by
    nlinarith
  have hlambdaPos : 0 < lambda :=
    lt_of_lt_of_le (mul_pos (by norm_num) hmu) hlambdaLower
  have hselected : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a,
      mu / 100 ≤
        |lambda - Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) k : ℝ)| := by
    intro k hk
    obtain ⟨q, hqPrime, hqS, hqY, hqUp | hqDown⟩ :=
      PrimeStar.mem_firstExitLowerCenters_arithmetic
        (PrimeStar.sqrtCutoff_condition X) haY hk
    · have hqMem : q ∈ PrimeStar.canonicalUpPrimeLabels S X
          (squareRootCutoff X) a := by
        apply Finset.mem_filter.mpr
        exact ⟨Nat.mem_primesLE.mpr ⟨hqY, hqPrime⟩, hqS,
          hqUp.trans_le (PrimeStar.Vertex.coe_le k)⟩
      let qi : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a :=
        ⟨q, hqMem⟩
      have htarget : PrimeStar.canonicalUpTarget hS a qi = k := by
        apply Subtype.ext
        apply Fin.ext
        exact hqUp
      let d : ℝ := PrimeStar.largePrimeStarDegree S X
        (squareRootCutoff X) a
      let dk : ℝ := PrimeStar.largePrimeStarDegree S X
        (squareRootCutoff X) k
      have hdReal : 0 < d := by
        dsimp [d]
        exact_mod_cast hd
      have hmuSq : mu ^ 2 = d := by
        simpa [mu, d] using moleculeStarEnergy_sq S X a
      have hqAllowed : q ∈
          (Nat.primesLE (Nat.sqrt X)).filter (fun p ↦ p ∉ S) :=
        Finset.mem_filter.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hqY, hqPrime⟩, hqS⟩
      have hratioArithmetic := (hup a ha q hqAllowed).2.1
      change PrimeStar.fixedCenterActualUpRatio S (a : ℕ) X q ≤
        15 / 16 at hratioArithmetic
      have hratioGraph :=
        PrimeStar.canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio
          hS a haY qi
      rw [htarget] at hratioGraph
      rw [← hratioGraph] at hratioArithmetic
      have hdk : dk ≤ (15 / 16 : ℝ) * mu ^ 2 := by
        rw [hmuSq]
        exact (div_le_iff₀ hdReal).mp
          (by simpa [d, dk] using hratioArithmetic)
      have hsqrtNonneg : 0 ≤ Real.sqrt dk := Real.sqrt_nonneg _
      have hdkNonneg : 0 ≤ dk := by
        dsimp [dk]
        positivity
      have hsqrtSq : (Real.sqrt dk) ^ 2 = dk := Real.sq_sqrt hdkNonneg
      by_contra hgap
      have hlt : |lambda - Real.sqrt dk| < mu / 100 :=
        lt_of_not_ge hgap
      have habs := abs_lt.mp hlt
      nlinarith
    · have hqDvd : q ∣ (a : ℕ) :=
        ⟨(k : ℕ), by simpa [Nat.mul_comm] using hqDown.symm⟩
      have hqMem : q ∈ (a : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr
          ⟨hqPrime, hqDvd, (PrimeStar.Vertex.coe_pos a).ne'⟩
      let qi : PrimeStar.CanonicalDownIndex a := ⟨q, hqMem⟩
      have htarget : PrimeStar.canonicalDownTarget a qi = k := by
        apply Subtype.ext
        apply Fin.ext
        apply Nat.eq_of_mul_eq_mul_right hqPrime.pos
        calc
          (PrimeStar.canonicalDownTarget a qi : ℕ) * q = (a : ℕ) :=
            PrimeStar.canonicalDownTarget_mul_coe a qi
          _ = (k : ℕ) * q := hqDown.symm
      let d : ℝ := PrimeStar.largePrimeStarDegree S X
        (squareRootCutoff X) a
      let dk : ℝ := PrimeStar.largePrimeStarDegree S X
        (squareRootCutoff X) k
      have hdReal : 0 < d := by
        dsimp [d]
        exact_mod_cast hd
      have hmuSq : mu ^ 2 = d := by
        simpa [mu, d] using moleculeStarEnergy_sq S X a
      have hratioArithmetic := hdown a ha q hqMem
      change 17 / 16 ≤
        PrimeStar.fixedCenterArithmeticDegree S ((a : ℕ) / q) X /
          PrimeStar.fixedCenterArithmeticDegree S (a : ℕ) X
        at hratioArithmetic
      have hratioGraph :=
        PrimeStar.canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio
          hS a haY qi
      rw [htarget] at hratioGraph
      rw [← hratioGraph] at hratioArithmetic
      have hdk : (17 / 16 : ℝ) * mu ^ 2 ≤ dk := by
        rw [hmuSq]
        exact (le_div_iff₀ hdReal).mp
          (by simpa [d, dk] using hratioArithmetic)
      have hsqrtNonneg : 0 ≤ Real.sqrt dk := Real.sqrt_nonneg _
      have hdkNonneg : 0 ≤ dk := by
        dsimp [dk]
        positivity
      have hsqrtSq : (Real.sqrt dk) ^ 2 = dk := Real.sq_sqrt hdkNonneg
      by_contra hgap
      have hlt : |lambda - Real.sqrt dk| < mu / 100 :=
        lt_of_not_ge hgap
      have habs := abs_lt.mp hlt
      nlinarith
  intro x
  apply shiftedOperator_lowerBound_of_all_eigenvalue_gaps C hC
      lambda (mu / 100) (by positivity)
  intro i
  let e := hC.eigenvectorBasis rfl i
  have heigen : C e = hC.eigenvalues rfl i • e := by
    exact hC.apply_eigenvectorBasis rfl i
  have he0 : e ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [(hC.eigenvectorBasis rfl).orthonormal.norm_eq_one i]
    norm_num
  rcases firstExitCompression_eigenvalue_eq_zero_or_selectedStarDegree
      haY heigen he0 with hzero | ⟨k, hk, hpositive | hnegative⟩
  · rw [hzero, sub_zero, abs_of_pos hlambdaPos]
    nlinarith
  · rw [hpositive]
    exact hselected k hk
  · rw [hnegative, sub_neg_eq_add,
      abs_of_nonneg (add_nonneg hlambdaPos.le (Real.sqrt_nonneg _))]
    exact (calc
      mu / 100 ≤ (99 / 100 : ℝ) * mu := by nlinarith
      _ ≤ lambda := hlambdaLower
      _ ≤ lambda + Real.sqrt
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ) :=
        le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- The exact boundary equation upgrades a first-order Weyl window to the
source-weighted, second-order displacement scale.  No local response is
estimated here: the positive star mode sees the boundary projection of the
small-prime return, symmetry moves the small-prime operator back to the
source, and the shifted compression gap controls the full first-exit
interior. -/

theorem exactPrincipalMoleculeRoot_sub_starEnergy_abs_le_sourceWeighted
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖)
    (halpha : 1 / 2 ≤
      |exactPrincipalMoleculeBoundaryModeCoefficient S X a 1|) :
    |exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a| ≤
      2 * eta ^ 2 / gamma := by
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let u := moleculePositiveStarMode S X a
  let xU := exactPrincipalMoleculeInteriorVector S X a
  let alpha := exactPrincipalMoleculeBoundaryModeCoefficient S X a 1
  let delta := exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a
  have hu : ‖u‖ = 1 := by
    dsimp [u, moleculePositiveStarMode]
    exact PrimeStar.norm_largePrimeNormalizedStarMode hd
  have hHsymm : H.IsSymmetric := by
    dsimp [H]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).isHermitian_adjMatrix (R := ℝ))
  have hscalar : delta * alpha =
      ⟪u, exactPrincipalMoleculeBoundaryFeedback S X a⟫_ℝ := by
    simpa [delta, alpha, u, moleculePositiveStarMode] using
      exactPrincipalMolecule_signedMode_scalarEquation
        hS ha (1 : ℝ) (by norm_num)
  have hfeedback :
      ⟪u, exactPrincipalMoleculeBoundaryFeedback S X a⟫_ℝ =
        ⟪H u, xU⟫_ℝ := by
    calc
      ⟪u, exactPrincipalMoleculeBoundaryFeedback S X a⟫_ℝ =
          ⟪u, H xU⟫_ℝ := by
        rw [exactPrincipalMoleculeBoundaryFeedback]
        simpa [u, moleculePositiveStarMode, H, xU] using
          (real_inner_largePrimeNormalizedStarMode_boundaryProjection
            (S := S) (X := X) (Y := squareRootCutoff X) (a := a)
            (1 : ℝ) (H xU))
      _ = ⟪H u, xU⟫_ℝ := (hHsymm u xU).symm
  have hsource : ‖H u‖ ≤ eta := by
    calc
      ‖H u‖ ≤ eta * ‖u‖ := by simpa [H] using hH u
      _ = eta := by rw [hu, mul_one]
  have hinterior : gamma * ‖xU‖ ≤ eta := by
    simpa [xU] using
      gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_smallPrime
        hS ha gamma eta heta hgap hH
  have hscaled : gamma * |delta| * |alpha| ≤ eta ^ 2 := by
    calc
      gamma * |delta| * |alpha| =
          gamma * |delta * alpha| := by rw [abs_mul]; ring
      _ = gamma * |⟪H u, xU⟫_ℝ| := by rw [hscalar, hfeedback]
      _ ≤ gamma * (‖H u‖ * ‖xU‖) := by
        gcongr
        exact abs_real_inner_le_norm _ _
      _ ≤ gamma * (eta * ‖xU‖) := by gcongr
      _ = eta * (gamma * ‖xU‖) := by ring
      _ ≤ eta * eta := by gcongr
      _ = eta ^ 2 := by ring
  have hhalf : gamma * |delta| / 2 ≤ eta ^ 2 := by
    calc
      gamma * |delta| / 2 = (gamma * |delta|) * (1 / 2 : ℝ) := by ring
      _ ≤ (gamma * |delta|) * |alpha| := by
        exact mul_le_mul_of_nonneg_left halpha
          (mul_nonneg hgamma.le (abs_nonneg delta))
      _ ≤ eta ^ 2 := hscaled
  apply (le_div_iff₀ hgamma).2
  nlinarith [abs_nonneg delta]

/-- Compression-gap control alone forces the exact molecule to retain a
positive signed-boundary coefficient of size at least one half.  This avoids
introducing a second spectral classification for the full large-prime
molecule: normalization, the negative signed equation, and the mean-zero
boundary equation are sufficient. -/

theorem one_half_le_abs_exactPrincipalMoleculeBoundaryModeCoefficient_of_firstExitGap
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖)
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖)
    (hlambda : moleculeStarEnergy S X a / 2 ≤
      exactPrincipalMoleculeRoot S X a)
    (hsmallInterior : 8 * eta ≤ gamma)
    (hsmallBoundary : 32 * eta ^ 2 ≤
      gamma * moleculeStarEnergy S X a) :
    1 / 2 ≤
      |exactPrincipalMoleculeBoundaryModeCoefficient S X a 1| := by
  let v := exactPrincipalMoleculeAmbientVector S X a
  let xB := exactPrincipalMoleculeBoundaryVector S X a
  let xU := exactPrincipalMoleculeInteriorVector S X a
  let k := exactPrincipalMoleculeBoundaryKernel S X a
  let F := exactPrincipalMoleculeBoundaryFeedback S X a
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let up := moleculePositiveStarMode S X a
  let um := PrimeStar.largePrimeNormalizedStarMode S X
    (squareRootCutoff X) a (-1)
  let alpha := exactPrincipalMoleculeBoundaryModeCoefficient S X a 1
  let beta := exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)
  let lambda := exactPrincipalMoleculeRoot S X a
  let mu := moleculeStarEnergy S X a
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hupNorm : ‖up‖ = 1 := by
    dsimp [up, moleculePositiveStarMode]
    exact PrimeStar.norm_largePrimeNormalizedStarMode hd
  have humNorm : ‖um‖ = 1 := by
    dsimp [um]
    exact PrimeStar.norm_largePrimeNormalizedStarMode hd
  have hvNorm : ‖v‖ = 1 := by
    exact norm_exactPrincipalMoleculeAmbientVector S X a
  have hxSplit : xB + xU = v := by
    simpa [xB, xU, v] using exactPrincipalMolecule_boundary_add_interior ha
  have hinteriorScaled : gamma * ‖xU‖ ≤ eta := by
    simpa [xU] using
      gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_smallPrime
        hS ha gamma eta heta hgap hH
  have hinterior : ‖xU‖ ≤ 1 / 8 := by
    have : 8 * (gamma * ‖xU‖) ≤ gamma := by
      calc
        8 * (gamma * ‖xU‖) ≤ 8 * eta := by gcongr
        _ ≤ gamma := hsmallInterior
    nlinarith [norm_nonneg xU]
  have hfeedbackProjection : ‖F‖ ≤ ‖H xU‖ := by
    dsimp [F, exactPrincipalMoleculeBoundaryFeedback]
    exact PrimeStar.norm_euclideanCoordinateProjection_le _ _
  have hfeedbackScaled : gamma * ‖F‖ ≤ eta ^ 2 := by
    calc
      gamma * ‖F‖ ≤ gamma * ‖H xU‖ := by gcongr
      _ ≤ gamma * (eta * ‖xU‖) := by
        gcongr
        simpa [H] using hH xU
      _ = eta * (gamma * ‖xU‖) := by ring
      _ ≤ eta * eta := by gcongr
      _ = eta ^ 2 := by ring
  have hnegative := exactPrincipalMolecule_negativeMode_scalarEquation hS ha
  have hnegativeAbs : |lambda + mu| * |beta| ≤ ‖F‖ := by
    have hinner := abs_real_inner_le_norm um F
    rw [humNorm, one_mul] at hinner
    calc
      |lambda + mu| * |beta| = |(lambda + mu) * beta| := by rw [abs_mul]
      _ = |⟪um, F⟫_ℝ| := by
        simpa [lambda, mu, beta, um, F] using congrArg abs hnegative
      _ ≤ ‖F‖ := hinner
  have hlambdaMu : mu ≤ |lambda + mu| := by
    have hlower : mu ≤ lambda + mu := by
      dsimp [lambda, mu] at hlambda ⊢
      nlinarith
    exact hlower.trans (le_abs_self _)
  have hbetaScaled : gamma * mu * |beta| ≤ eta ^ 2 := by
    calc
      gamma * mu * |beta| = gamma * (mu * |beta|) := by ring
      _ ≤ gamma * (|lambda + mu| * |beta|) := by gcongr
      _ ≤ gamma * ‖F‖ := by gcongr
      _ ≤ eta ^ 2 := hfeedbackScaled
  have hbeta : |beta| ≤ 1 / 32 := by
    have : 32 * (gamma * mu * |beta|) ≤ gamma * mu := by
      calc
        32 * (gamma * mu * |beta|) ≤ 32 * eta ^ 2 := by gcongr
        _ ≤ gamma * mu := by simpa [mu] using hsmallBoundary
    have hgammaMu : 0 < gamma * mu := mul_pos hgamma hmu
    nlinarith [abs_nonneg beta]
  have hkernelEq := exactPrincipalMoleculeRoot_smul_boundaryKernel_eq_feedbackKernel
    hS ha hd
  have hkernelRhs :
      ‖actualStarMeanZeroLeafVector S X (squareRootCutoff X) a F‖ ≤ ‖F‖ :=
    norm_actualStarMeanZeroLeafVector_le F hd
  have hkernelLambda : |lambda| * ‖k‖ ≤ ‖F‖ := by
    calc
      |lambda| * ‖k‖ = ‖lambda • k‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = ‖actualStarMeanZeroLeafVector S X (squareRootCutoff X) a F‖ := by
        simpa [lambda, k, F] using congrArg norm hkernelEq
      _ ≤ ‖F‖ := hkernelRhs
  have hlambdaAbs : mu / 2 ≤ |lambda| := by
    have hlambda' : mu / 2 ≤ lambda := by
      simpa [lambda, mu] using hlambda
    exact hlambda'.trans (le_abs_self _)
  have hkernelScaled : gamma * mu * ‖k‖ ≤ 2 * eta ^ 2 := by
    calc
      gamma * mu * ‖k‖ = 2 * gamma * (mu / 2 * ‖k‖) := by ring
      _ ≤ 2 * gamma * (|lambda| * ‖k‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hlambdaAbs (norm_nonneg k))
          (mul_nonneg (by norm_num) hgamma.le)
      _ ≤ 2 * gamma * ‖F‖ := by
        exact mul_le_mul_of_nonneg_left hkernelLambda
          (mul_nonneg (by norm_num) hgamma.le)
      _ ≤ 2 * eta ^ 2 := by
        nlinarith [hfeedbackScaled]
  have hkernel : ‖k‖ ≤ 1 / 16 := by
    have : 16 * (gamma * mu * ‖k‖) ≤ gamma * mu := by
      calc
        16 * (gamma * mu * ‖k‖) ≤ 32 * eta ^ 2 := by
          nlinarith [hkernelScaled]
        _ ≤ gamma * mu := by simpa [mu] using hsmallBoundary
    have hgammaMu : 0 < gamma * mu := mul_pos hgamma hmu
    nlinarith [norm_nonneg k]
  have hxBDecomp : xB = alpha • up + beta • um + k := by
    have hsigned := exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis
      (S := S) (X := X) (a := a) hd
    have hboundary : xB =
        exactPrincipalMoleculeSignedBoundaryVector S X a + k := by
      simp [xB, k, exactPrincipalMoleculeSignedBoundaryVector]
    rw [hboundary, hsigned]
    rfl
  have hxBNorm : ‖xB‖ ≤ |alpha| + |beta| + ‖k‖ := by
    rw [hxBDecomp]
    calc
      ‖alpha • up + beta • um + k‖ ≤
          ‖alpha • up + beta • um‖ + ‖k‖ := norm_add_le _ _
      _ ≤ (‖alpha • up‖ + ‖beta • um‖) + ‖k‖ := by
        gcongr
        exact norm_add_le _ _
      _ = |alpha| + |beta| + ‖k‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          hupNorm, humNorm, mul_one, mul_one]
  have hunit : 1 ≤ |alpha| + |beta| + ‖k‖ + ‖xU‖ := by
    calc
      1 = ‖v‖ := hvNorm.symm
      _ = ‖xB + xU‖ := by rw [hxSplit]
      _ ≤ ‖xB‖ + ‖xU‖ := norm_add_le _ _
      _ ≤ (|alpha| + |beta| + ‖k‖) + ‖xU‖ := by gcongr
  have : 1 ≤
      |exactPrincipalMoleculeBoundaryModeCoefficient S X a 1| +
        1 / 32 + 1 / 16 + 1 / 8 := by
    calc
      1 ≤ |alpha| + |beta| + ‖k‖ + ‖xU‖ := hunit
      _ ≤ |alpha| + 1 / 32 + 1 / 16 + 1 / 8 := by gcongr
  norm_num at this ⊢
  linarith

/-- On every fixed sub-square-root power range, the exact molecule selected
root has a uniformly nontrivial positive signed-boundary coefficient.  The
proof instantiates the finite overlap lemma from the already established
root window, first-exit compression gap, and tuned small-prime norm. -/

theorem eventually_powerRange_one_half_le_abs_exactPrincipalMoleculeBoundaryModeCoefficient
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        1 / 2 ≤
          |exactPrincipalMoleculeBoundaryModeCoefficient S X a 1| := by
  filter_upwards [
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
      S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned]
      with X hwindow hcompression hresidual
  intro a ha
  obtain ⟨haY, hd, hshift, hresSmall⟩ := hwindow a ha
  let lambda := exactPrincipalMoleculeRoot S X a
  let mu := moleculeStarEnergy S X a
  let eta := PrimeStar.sqrtCutoffResidualScale X
  let gamma := mu / 100
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have heta : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hshift' : |lambda - mu| ≤ mu / 100 := by
    simpa [lambda, mu] using hshift
  have hlambda : mu / 2 ≤ lambda := by
    have := (abs_le.mp hshift').1
    nlinarith
  have hresSmall' : 1000000 * eta ^ 2 ≤ mu ^ 2 := by
    simpa [eta, mu] using hresSmall
  have hsq : (1000 * eta) ^ 2 ≤ mu ^ 2 := by
    convert hresSmall' using 1 <;> ring
  have hsmallEta : 1000 * eta ≤ mu := by
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) heta) hmu.le).mp hsq
  have hsmallInterior : 8 * eta ≤ gamma := by
    dsimp [gamma]
    nlinarith
  have hsmallBoundary : 32 * eta ^ 2 ≤ gamma * mu := by
    dsimp [gamma]
    nlinarith
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  have hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖lambda • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖ := by
    simpa [gamma, lambda, mu] using hcompression a ha
  have hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖ := by
    intro x
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S x
  exact
    one_half_le_abs_exactPrincipalMoleculeBoundaryModeCoefficient_of_firstExitGap
      hS haY hd gamma eta hgamma heta hgap hH
        (by simpa [lambda, mu] using hlambda) hsmallInterior
        (by simpa [mu] using hsmallBoundary)

/-- The exact molecule root is second-order close to its boundary-star
energy throughout every fixed sub-square-root power range.  This is the
source-weighted displacement used when estimating the shifted signed
response; it improves the global Weyl window by one full power of the tuned
small-prime norm. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_sourceWeightedShift
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        |exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a| ≤
          200 * PrimeStar.sqrtCutoffResidualScale X ^ 2 /
            moleculeStarEnergy S X a := by
  filter_upwards [
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
      S hS htheta,
    eventually_powerRange_one_half_le_abs_exactPrincipalMoleculeBoundaryModeCoefficient
      S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned]
      with X hwindow hcompression hoverlap hresidual
  intro a ha
  obtain ⟨haY, hd, _hshift, _hresSmall⟩ := hwindow a ha
  let mu := moleculeStarEnergy S X a
  let eta := PrimeStar.sqrtCutoffResidualScale X
  let gamma := mu / 100
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have heta : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  have hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖ := by
    simpa [gamma, mu] using hcompression a ha
  have hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖ := by
    intro x
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S x
  have hbound :=
    exactPrincipalMoleculeRoot_sub_starEnergy_abs_le_sourceWeighted
      hS haY hd gamma eta hgamma heta hgap hH (hoverlap a ha)
  have hidentity : 2 * eta ^ 2 / gamma = 200 * eta ^ 2 / mu := by
    dsimp [gamma]
    field_simp [ne_of_gt hmu]
    ring
  simpa [eta, mu, hidentity] using hbound

/-- The fourth power of the tuned small-prime residual, divided by the
boundary-star energy squared, has exactly the Paper-II pointwise scale.  This
is the common scalar budget for the shifted response terms in the balanced
two-mode determinant. -/

theorem eventually_powerRange_moleculeStarEnergy_residualScaleBundle
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (X : ℝ) /
              (8 * (a : ℝ) * Real.log (X : ℝ)) ≤
            moleculeStarEnergy S X a ^ 2 ∧
          PrimeStar.sqrtCutoffResidualScale X ^ 4 /
              moleculeStarEnergy S X a ^ 2 ≤
            128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
              ((a : ℝ) / Real.log (X : ℝ)) := by
  filter_upwards
      [eventually_powerRange_largePrimeStarDegree_residualScaleBundle
        S hS htheta]
      with X hbundle
  intro a ha
  have hmuSq := moleculeStarEnergy_sq S X a
  constructor
  · simpa [hmuSq] using (hbundle a ha).2.2.2.1
  · simpa [hmuSq] using (hbundle a ha).2.2.2.2

/-! ## One common exact-molecule gap on the canonical power prefix -/

/-- Explicit common first-exit gap scale on the canonical power prefix.

The pointwise exact-molecule estimate supplies a gap equal to one hundredth
of the source-star energy.  The smallest energy in `a ≤ X^theta` occurs at
the power-range scale, so this quantity is a uniform lower bound suitable for
collective quadratic estimates. -/

theorem eventually_powerRange_boundaryLeafSquareSum_div_starEnergy_fourth_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (boundaryLeafCountSquareSumOnStar S X (squareRootCutoff X) a : ℝ) /
            moleculeStarEnergy S X a ^ 4 ≤
          5632 * Real.log (X : ℝ) ^ 2 / Real.sqrt (X : ℝ) := by
  filter_upwards [eventually_powerRange_moleculeStarEnergy_residualScaleBundle
      S hS htheta,
      eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
      eventually_ge_atTop 16]
      with X hscale hcenter hX
  intro a ha
  let A : ℕ := (a : ℕ)
  let Y : ℕ := Nat.sqrt X
  let x : ℝ := X
  let y : ℝ := Y
  let L : ℝ := Real.log x
  let mu : ℝ := moleculeStarEnergy S X a
  have hApos : 0 < A := PrimeStar.Vertex.coe_pos a
  have htwoAY : 2 * A ≤ Y := hcenter A ha
  have haY : (a : ℕ) ≤ squareRootCutoff X := by
    simpa [A, Y] using (show A ≤ Y by omega)
  have hYXa : Y ≤ X / A := by
    apply (Nat.le_div_iff_mul_le hApos).2
    calc
      Y * A ≤ Y * Y := Nat.mul_le_mul_left Y (by omega : A ≤ Y)
      _ ≤ X := Nat.sqrt_le X
  have hYfour : 4 ≤ Y := by
    have hsquare : 4 * 4 ≤ X := by omega
    simpa [Y] using (Nat.le_sqrt.mpr hsquare)
  have hy : 0 < y := by
    dsimp [y]
    exact_mod_cast (show 0 < Y by omega)
  have honeY : (1 : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hlogY : Real.log 4 ≤ Real.log y := by
    apply Real.log_le_log (by norm_num)
    dsimp [y]
    exact_mod_cast hYfour
  have hlogYpos : 0 < Real.log y := by
    apply Real.log_pos
    dsimp [y]
    exact_mod_cast (show 1 < Y by omega)
  have hratio : Real.log 4 / Real.log y ≤ 1 :=
    (div_le_one hlogYpos).2 hlogY
  have hpow : y ^ (-(3 / 2 : ℝ)) ≤ y ^ (-1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le honeY (by norm_num)
  have hbracket :
      (6 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) +
          5 * y ^ (-(3 / 2 : ℝ)) ≤
        11 * y ^ (-1 : ℝ) := by
    have hyInv : 0 ≤ y ^ (-1 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hfirst :
        (6 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) ≤
          6 * y ^ (-1 : ℝ) := by
      have hcoeff : 6 * Real.log 4 / Real.log y ≤ 6 := by
        calc
          6 * Real.log 4 / Real.log y =
              6 * (Real.log 4 / Real.log y) := by ring
          _ ≤ 6 * 1 := mul_le_mul_of_nonneg_left hratio (by norm_num)
          _ = 6 := by ring
      exact mul_le_mul_of_nonneg_right hcoeff hyInv
    have hsecond : 5 * y ^ (-(3 / 2 : ℝ)) ≤
        5 * y ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    linarith
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by
    dsimp [x]
    positivity)
  have hsqrtLe : Real.sqrt x ≤ 2 * y := by
    have hlt : Real.sqrt (X : ℝ) < (Nat.sqrt X : ℝ) + 1 :=
      Real.real_sqrt_lt_nat_sqrt_succ (a := X)
    have hsucc : (Nat.sqrt X : ℝ) + 1 ≤ 2 * (Nat.sqrt X : ℝ) := by
      exact_mod_cast (show Nat.sqrt X + 1 ≤ 2 * Nat.sqrt X by omega)
    dsimp [x, y, Y]
    exact hlt.le.trans hsucc
  have hyInv : y ^ (-1 : ℝ) ≤ 2 / Real.sqrt x := by
    rw [Real.rpow_neg_one, inv_eq_one_div]
    rw [div_le_div_iff₀ hy hsqrtPos]
    nlinarith
  have hcheb := boundaryLeafCountSquareSumOnStar_le_chebyshev
    hS a haY (by simpa [Y] using (show 2 ≤ Y by omega))
      (by simpa [A, Y] using hYXa)
  have hsum :
      (boundaryLeafCountSquareSumOnStar S X (squareRootCutoff X) a : ℝ) ≤
        88 * (x / (A : ℝ)) ^ 2 / Real.sqrt x := by
    calc
      (boundaryLeafCountSquareSumOnStar S X (squareRootCutoff X) a : ℝ) ≤
          4 * (x / (A : ℝ)) ^ 2 *
            ((6 * Real.log 4 / Real.log y) * y ^ (-1 : ℝ) +
              5 * y ^ (-(3 / 2 : ℝ))) := by
        simpa [x, y, Y, A] using hcheb
      _ ≤ 4 * (x / (A : ℝ)) ^ 2 * (11 * y ^ (-1 : ℝ)) := by
        gcongr
      _ ≤ 4 * (x / (A : ℝ)) ^ 2 *
          (11 * (2 / Real.sqrt x)) := by gcongr
      _ = 88 * (x / (A : ℝ)) ^ 2 / Real.sqrt x := by ring
  have hlogX : 0 < L := by
    dsimp [L, x]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hmu : 0 < mu := by
    have hlow := (hscale a ha).1
    have hleft : 0 < (X : ℝ) /
        (8 * (a : ℝ) * Real.log (X : ℝ)) := by positivity
    have hne : mu ≠ 0 := by
      simpa [mu] using (sq_pos_iff.mp (hleft.trans_le hlow))
    exact lt_of_le_of_ne (moleculeStarEnergy_nonneg S X a) (Ne.symm hne)
  have hstarLower : x / (8 * (A : ℝ) * L) ≤ mu ^ 2 := by
    simpa [x, A, L, mu] using (hscale a ha).1
  have hbaseNonneg : 0 ≤ x / (8 * (A : ℝ) * L) := by positivity
  have hmuFourth : (x / (8 * (A : ℝ) * L)) ^ 2 ≤ mu ^ 4 := by
    nlinarith [sq_nonneg (mu ^ 2 - x / (8 * (A : ℝ) * L))]
  have hmuFourthPos : 0 < mu ^ 4 := pow_pos hmu 4
  rw [show moleculeStarEnergy S X a = mu by rfl]
  apply (div_le_iff₀ hmuFourthPos).2
  calc
    (boundaryLeafCountSquareSumOnStar S X (squareRootCutoff X) a : ℝ) ≤
        88 * (x / (A : ℝ)) ^ 2 / Real.sqrt x := hsum
    _ = (5632 * L ^ 2 / Real.sqrt x) *
        (x / (8 * (A : ℝ) * L)) ^ 2 := by
      field_simp [ne_of_gt (show (0 : ℝ) < A by exact_mod_cast hApos),
        ne_of_gt hlogX, ne_of_gt hsqrtPos]
      ring
    _ ≤ (5632 * L ^ 2 / Real.sqrt x) * mu ^ 4 := by
      exact mul_le_mul_of_nonneg_left hmuFourth (by positivity)
    _ = (5632 * Real.log (X : ℝ) ^ 2 /
        Real.sqrt (X : ℝ)) * mu ^ 4 := by rfl

/-- The exact-root gap and the source-weighted displacement leave a uniform
gap at the unshifted boundary-star energy.  This is the reference resolvent
needed to identify the arithmetic first-exit correction. -/

theorem eventually_powerRange_moleculeStarEnergy_firstExitCompressionGap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ x : MoleculeAmbient S X,
          (moleculeStarEnergy S X a / 200) * ‖x‖ ≤
            ‖moleculeStarEnergy S X a • x -
              PrimeStar.firstExitLargePrimeCompressionOperator S X
                (squareRootCutoff X) a x‖ := by
  filter_upwards [
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_sourceWeightedShift
      S hS htheta]
      with X hwindow hgapRoot hshift
  intro a ha x
  obtain ⟨_haY, hd, _hcoarse, hresSmall⟩ := hwindow a ha
  let lambda := exactPrincipalMoleculeRoot S X a
  let mu := moleculeStarEnergy S X a
  let C := PrimeStar.firstExitLargePrimeCompressionOperator S X
    (squareRootCutoff X) a
  let eta := PrimeStar.sqrtCutoffResidualScale X
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hshiftRaw : |lambda - mu| ≤ 200 * eta ^ 2 / mu := by
    simpa [lambda, mu, eta] using hshift a ha
  have hshiftSmall : |lambda - mu| ≤ mu / 5000 := by
    apply hshiftRaw.trans
    apply (div_le_iff₀ hmu).2
    have hresSmall' : 1000000 * eta ^ 2 ≤ mu ^ 2 := by
      simpa [eta, mu] using hresSmall
    nlinarith
  have hrootGap : (mu / 100) * ‖x‖ ≤ ‖lambda • x - C x‖ := by
    simpa [lambda, mu, C] using hgapRoot a ha x
  have htriangle :
      ‖lambda • x - C x‖ ≤
        |lambda - mu| * ‖x‖ + ‖mu • x - C x‖ := by
    calc
      ‖lambda • x - C x‖ =
          ‖(lambda - mu) • x + (mu • x - C x)‖ := by
        congr 1
        rw [sub_smul]
        abel
      _ ≤ ‖(lambda - mu) • x‖ + ‖mu • x - C x‖ :=
        norm_add_le _ _
      _ = |lambda - mu| * ‖x‖ + ‖mu • x - C x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
  have hnorm : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

/-- On every fixed sub-square-root power range, the unshifted boundary-star
energy is nonresonant with every canonical up/down target and hence with the
whole selected first-exit star union. -/

theorem eventually_powerRange_moleculeStarEnergy_firstExitNonresonant
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
          moleculeStarEnergy S X a ^ 2 ≠
            (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
              (PrimeStar.canonicalUpTarget hS a q) : ℝ)) ∧
        (∀ q : PrimeStar.CanonicalDownIndex a,
          moleculeStarEnergy S X a ^ 2 ≠
            (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
              (PrimeStar.canonicalDownTarget a q) : ℝ)) ∧
        (∀ k ∈ PrimeStar.firstExitLowerCenters S X
            (squareRootCutoff X) a,
          moleculeStarEnergy S X a ^ 2 ≠
            (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ)) := by
  filter_upwards [
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_actualUpStarRatio_bounds S hS htheta,
    eventually_powerRange_downStarRatio_ge S hS htheta]
      with X hwindow hup hdown
  intro a ha
  obtain ⟨haY, hd, _hshift⟩ := hwindow a ha
  let mu := moleculeStarEnergy S X a
  let d : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hdPos : 0 < d := by
    dsimp [d]
    exact_mod_cast hd
  have hmuSq : mu ^ 2 = d := by
    simpa [mu, d] using moleculeStarEnergy_sq S X a
  have hupden : ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      mu ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) : ℝ) := by
    intro q heq
    let dq : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalUpTarget hS a q)
    have hqdata := Finset.mem_filter.mp q.property
    have hqmem : (q : ℕ) ∈
        (Nat.primesLE (Nat.sqrt X)).filter (fun p ↦ p ∉ S) :=
      Finset.mem_filter.mpr ⟨hqdata.1, hqdata.2.1⟩
    have hratioArithmetic := (hup a ha (q : ℕ) hqmem).2.1
    change PrimeStar.fixedCenterActualUpRatio S (a : ℕ) X (q : ℕ) ≤
      15 / 16 at hratioArithmetic
    have hratioGraph :=
      PrimeStar.canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a haY q
    rw [← hratioGraph] at hratioArithmetic
    have hdq : dq ≤ (15 / 16 : ℝ) * mu ^ 2 := by
      rw [hmuSq]
      exact (div_le_iff₀ hdPos).mp (by
        simpa [d, dq] using hratioArithmetic)
    have hmuSqPos : 0 < mu ^ 2 := sq_pos_of_pos hmu
    change mu ^ 2 = dq at heq
    nlinarith
  have hdownden : ∀ q : PrimeStar.CanonicalDownIndex a,
      mu ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) : ℝ) := by
    intro q heq
    let dq : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q)
    have hratioArithmetic := hdown a ha (q : ℕ) q.property
    change 17 / 16 ≤
      PrimeStar.fixedCenterArithmeticDegree S ((a : ℕ) / (q : ℕ)) X /
        PrimeStar.fixedCenterArithmeticDegree S (a : ℕ) X at hratioArithmetic
    have hratioGraph :=
      PrimeStar.canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio
        hS a haY q
    rw [← hratioGraph] at hratioArithmetic
    have hdq : (17 / 16 : ℝ) * mu ^ 2 ≤ dq := by
      rw [hmuSq]
      exact (le_div_iff₀ hdPos).mp (by
        simpa [d, dq] using hratioArithmetic)
    have hmuSqPos : 0 < mu ^ 2 := sq_pos_of_pos hmu
    change mu ^ 2 = dq at heq
    nlinarith
  refine ⟨hupden, hdownden, ?_⟩
  intro k hk heq
  obtain ⟨q, hqPrime, hqS, hqY, hqUp | hqDown⟩ :=
    PrimeStar.mem_firstExitLowerCenters_arithmetic
      (PrimeStar.sqrtCutoff_condition X) haY hk
  · have hqMem : q ∈ PrimeStar.canonicalUpPrimeLabels S X
        (squareRootCutoff X) a := by
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_primesLE.mpr ⟨hqY, hqPrime⟩, hqS,
        hqUp.trans_le (PrimeStar.Vertex.coe_le k)⟩
    let qi : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a :=
      ⟨q, hqMem⟩
    have htarget : PrimeStar.canonicalUpTarget hS a qi = k := by
      apply Subtype.ext
      apply Fin.ext
      exact hqUp
    apply hupden qi
    simpa [htarget] using heq
  · have hqDvd : q ∣ (a : ℕ) :=
      ⟨(k : ℕ), by simpa [Nat.mul_comm] using hqDown.symm⟩
    have hqMem : q ∈ (a : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hqPrime, hqDvd, (PrimeStar.Vertex.coe_pos a).ne'⟩
    let qi : PrimeStar.CanonicalDownIndex a := ⟨q, hqMem⟩
    have htarget : PrimeStar.canonicalDownTarget a qi = k := by
      apply Subtype.ext
      apply Fin.ext
      apply Nat.eq_of_mul_eq_mul_right hqPrime.pos
      calc
        (PrimeStar.canonicalDownTarget a qi : ℕ) * q = (a : ℕ) :=
          PrimeStar.canonicalDownTarget_mul_coe a qi
        _ = (k : ℕ) * q := hqDown.symm
    apply hdownden qi
    simpa [htarget] using heq

/-- Coarse but cancellation-safe scalar estimate for the exact two-mode
determinant.  The common response is not separated entry by entry here: the
exact balanced identity is used first, and only its remaining response and
kernel terms are bounded.  This is sufficient for the Paper-II
`a / log X` scale. -/

theorem abs_balancedSquaredDisplacement_le_of_response_bounds
    {lambda mu alpha rpp rpm rmp rmm kp km rho R E K D : ℝ}
    (hmu : 0 ≤ mu) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (halphaLower : 1 / 2 ≤ |alpha|) (halphaUpper : |alpha| ≤ 1)
    (hlambda : |lambda| ≤ 2 * mu)
    (hdelta : |lambda - mu| ≤ D)
    (hrpp : |rpp| ≤ R) (hrpm : |rpm| ≤ R)
    (hrmp : |rmp| ≤ R) (hrmm : |rmm| ≤ R)
    (hdiff : |rpp - rho| ≤ E)
    (hkp : |kp| ≤ K) (hkm : |km| ≤ K)
    (hidentity :
      alpha * (2 * mu * ((lambda - mu) - rho) + (lambda - mu) ^ 2) =
        kp * (lambda + mu - rmm) + rpm * km +
          alpha * (2 * mu * (rpp - rho) +
            (lambda - mu) * (rpp + rmm) + rpm * rmp - rpp * rmm)) :
    |2 * mu * ((lambda - mu) - rho) + (lambda - mu) ^ 2| ≤
      2 * (K * (3 * mu + R) + R * K +
        (2 * mu * E + D * (2 * R) + 2 * R ^ 2)) := by
  let Q := 2 * mu * ((lambda - mu) - rho) + (lambda - mu) ^ 2
  let C := 2 * mu * (rpp - rho) +
    (lambda - mu) * (rpp + rmm) + rpm * rmp - rpp * rmm
  let B := K * (3 * mu + R) + R * K +
    (2 * mu * E + D * (2 * R) + 2 * R ^ 2)
  have hmuAbs : |mu| = mu := abs_of_nonneg hmu
  have hlambdaSum : |lambda + mu - rmm| ≤ 3 * mu + R := by
    calc
      |lambda + mu - rmm| ≤ |lambda| + |mu| + |rmm| := by
        calc
          |lambda + mu - rmm| ≤ |lambda + mu| + |rmm| := abs_sub _ _
          _ ≤ (|lambda| + |mu|) + |rmm| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ 2 * mu + mu + R := by rw [hmuAbs]; gcongr
      _ = 3 * mu + R := by ring
  have hsumResponse : |rpp + rmm| ≤ 2 * R := by
    calc
      |rpp + rmm| ≤ |rpp| + |rmm| := abs_add_le _ _
      _ ≤ R + R := by gcongr
      _ = 2 * R := by ring
  have hC : |C| ≤ 2 * mu * E + D * (2 * R) + 2 * R ^ 2 := by
    dsimp [C]
    calc
      |2 * mu * (rpp - rho) +
          (lambda - mu) * (rpp + rmm) + rpm * rmp - rpp * rmm| ≤
          |2 * mu * (rpp - rho)| +
            |(lambda - mu) * (rpp + rmm)| +
            |rpm * rmp| + |rpp * rmm| := by
        calc
          |_ + _ + _ - _| ≤ |_ + _ + _| + |_| := abs_sub _ _
          _ ≤ (|_ + _| + |rpm * rmp|) + |rpp * rmm| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ ((|2 * mu * (rpp - rho)| +
              |(lambda - mu) * (rpp + rmm)|) + |rpm * rmp|) +
              |rpp * rmm| := by
            gcongr
            exact abs_add_le _ _
      _ = 2 * mu * |rpp - rho| +
          |lambda - mu| * |rpp + rmm| +
          |rpm| * |rmp| + |rpp| * |rmm| := by
        simp only [abs_mul, hmuAbs]
        ring
      _ ≤ 2 * mu * E + D * (2 * R) + R * R + R * R := by
        gcongr
      _ = 2 * mu * E + D * (2 * R) + 2 * R ^ 2 := by ring
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hscaled : |alpha| * |Q| ≤ B := by
    have hidAbs := congrArg abs hidentity
    have hleft : |alpha * Q| = |alpha| * |Q| := abs_mul _ _
    rw [show 2 * mu * ((lambda - mu) - rho) + (lambda - mu) ^ 2 = Q by rfl,
      hleft] at hidAbs
    calc
      |alpha| * |Q| =
          |kp * (lambda + mu - rmm) + rpm * km + alpha * C| := by
        rw [hidAbs]
      _ ≤ |kp| * |lambda + mu - rmm| + |rpm| * |km| +
          |alpha| * |C| := by
        calc
          |_ + _ + _| ≤ |_ + _| + |_| := abs_add_le _ _
          _ ≤ (|kp * (lambda + mu - rmm)| + |rpm * km|) +
              |alpha * C| := by gcongr; exact abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ K * (3 * mu + R) + R * K +
          1 * (2 * mu * E + D * (2 * R) + 2 * R ^ 2) := by
        gcongr
      _ = B := by simp [B]
  have hhalf : |Q| / 2 ≤ B := by
    calc
      |Q| / 2 = (1 / 2) * |Q| := by ring
      _ ≤ |alpha| * |Q| := by gcongr
      _ ≤ B := hscaled
  have hfinal : |Q| ≤ 2 * B := by
    nlinarith [abs_nonneg Q, hBnonneg]
  simpa [Q, B] using hfinal

/-- The quantitative first-exit gap makes the boundary-kernel self-return a
strict contraction uniformly on every fixed sub-square-root power range.
This is the concrete graph-level boundary-kernel estimate needed by the
two-mode determinant; all former gap, nonresonance, operator-norm, and
smallness premises are discharged here. -/

theorem eventually_powerRange_exactPrincipalMolecule_boundaryKernel_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        exactPrincipalMoleculeRoot S X a ^ 2 *
            ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 ≤
          4 * (600 / moleculeStarEnergy S X a ^ 2) ^ 2 *
            (boundaryLeafCountSquareSumOnStar S X
              (squareRootCutoff X) a : ℝ) := by
  filter_upwards [
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_responseWindow
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
      S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned]
      with X hwindow hresponse hdenominator hcompression hresidual
  intro a ha
  obtain ⟨haY, hd, hshift, hresSmall⟩ := hwindow a ha
  let lambda := exactPrincipalMoleculeRoot S X a
  let mu := moleculeStarEnergy S X a
  let eta := PrimeStar.sqrtCutoffResidualScale X
  let gamma := mu / 100
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hshift' : |lambda - mu| ≤ mu / 100 := by
    simpa [lambda, mu] using hshift
  have hlambdaLower : (99 / 100 : ℝ) * mu ≤ lambda := by
    have := abs_le.mp hshift'
    nlinarith
  have hlambdaPos : 0 < lambda :=
    lt_of_lt_of_le (mul_pos (by norm_num) hmu) hlambdaLower
  obtain ⟨hroot, hlambda, hupGap⟩ := hresponse a ha
  have hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖lambda • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a x‖ := by
    simpa [gamma, lambda, mu] using hcompression a ha
  have hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a,
      lambda ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) k : ℝ) := by
    simpa [lambda] using hdenominator a ha
  have heta : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          x‖ ≤ eta * ‖x‖ := by
    intro x
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S x
  have hresSmall' : 10000 * eta ^ 2 ≤ mu ^ 2 := by
    have hlarge : 1000000 * eta ^ 2 ≤ mu ^ 2 := by
      simpa [eta, mu] using hresSmall
    nlinarith [sq_nonneg eta]
  have hsmall : 2 * eta ^ 2 ≤ |lambda| * gamma := by
    rw [abs_of_pos hlambdaPos]
    dsimp [gamma]
    nlinarith
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  simpa [lambda, mu, eta, gamma] using
    (exactPrincipalMoleculeRoot_sq_mul_norm_sq_boundaryKernel_le_of_window
      hS haY hd hroot gamma eta hgamma heta hgap hden hH hsmall
        (by simpa [lambda, mu] using hlambda)
        (by simpa [lambda, mu] using hupGap))

/-- The complete mean-zero boundary return is negligible at the Paper-II
target scale.  The proof keeps the source weight: two small-prime crossings
are combined with the inverse-square boundary-leaf mass before the final
square-root estimate is taken. -/

theorem eventually_powerRange_starEnergy_mul_kernelBoundaryReturn_le_targetScale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        moleculeStarEnergy S X a *
            ‖exactPrincipalMoleculeKernelBoundaryReturn S X a‖ ≤
          (a : ℝ) / Real.log (X : ℝ) := by
  let C : ℝ :=
    160000 * 600 ^ 2 * 128 * 5632 *
      PrimeStar.sqrtCutoffResidualConstant ^ 4
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num)
      (pow_pos PrimeStar.sqrtCutoffResidualConstant_pos 4)
  filter_upwards [
      eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
        S hS htheta,
      eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
        S hS htheta,
      eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant
        S hS htheta,
      eventually_powerRange_exactPrincipalMolecule_boundaryKernel_le
        S hS htheta,
      eventually_powerRange_moleculeStarEnergy_residualScaleBundle
        S hS htheta,
      eventually_powerRange_boundaryLeafSquareSum_div_starEnergy_fourth_le
        S hS htheta,
      PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned,
      PrimeStar.eventually_const_mul_log_pow_le_sqrt C 3 hC.le,
      eventually_ge_atTop 16]
      with X hwindow hgapRoot hdenRoot hkernel hscale hleaf hresidual hlogGrowth hX
  intro a ha
  obtain ⟨haY, hd, hshift, _hresSmall⟩ := hwindow a ha
  let A : ℝ := (a : ℕ)
  let x : ℝ := X
  let L : ℝ := Real.log x
  let lambda : ℝ := exactPrincipalMoleculeRoot S X a
  let mu : ℝ := moleculeStarEnergy S X a
  let eta : ℝ := PrimeStar.sqrtCutoffResidualScale X
  let gamma : ℝ := mu / 100
  let k : ℝ := ‖exactPrincipalMoleculeBoundaryKernel S X a‖
  let r : ℝ := ‖exactPrincipalMoleculeKernelBoundaryReturn S X a‖
  let Q : ℝ := boundaryLeafCountSquareSumOnStar S X
    (squareRootCutoff X) a
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hlog : 0 < L := by
    dsimp [L, x]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (by
    dsimp [x]
    positivity)
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have heta : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hlambdaShift : |lambda - mu| ≤ mu / 100 := by
    simpa [lambda, mu] using hshift
  have hlambdaLower : mu / 2 ≤ lambda := by
    have := (abs_le.mp hlambdaShift).1
    nlinarith
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (half_pos hmu) hlambdaLower
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  have hgap : ∀ z : MoleculeAmbient S X,
      gamma * ‖z‖ ≤
        ‖lambda • z -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a z‖ := by
    simpa [gamma, lambda, mu] using hgapRoot a ha
  have hden : ∀ b ∈ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a,
      lambda ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b : ℝ) := by
    simpa [lambda] using hdenRoot a ha
  have hH : ∀ z : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          z‖ ≤ eta * ‖z‖ := by
    intro z
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S z
  have hreturnRaw :=
    gamma_mul_norm_exactPrincipalMoleculeKernelBoundaryReturn_le
      hS haY (by exact hlambdaPos.ne') gamma eta hgamma heta hgap hden hH
  have hreturn : mu * r ≤ 100 * eta ^ 2 * k := by
    have hraw : (mu / 100) * r ≤ eta ^ 2 * k := by
      simpa [gamma, mu, eta, k, r] using hreturnRaw
    nlinarith
  have hreturnSq : (mu * r) ^ 2 ≤ (100 * eta ^ 2 * k) ^ 2 := by
    exact sq_le_sq₀ (mul_nonneg hmu.le (norm_nonneg _))
      (mul_nonneg (by positivity) (norm_nonneg _)) |>.mpr hreturn
  have hkernelRaw := hkernel a ha
  have hmuLambda : mu ^ 2 ≤ 4 * lambda ^ 2 := by
    nlinarith [sq_nonneg (lambda - mu / 2)]
  have hweightedKernel : mu ^ 2 * k ^ 2 ≤
      16 * (600 / mu ^ 2) ^ 2 * Q := by
    calc
      mu ^ 2 * k ^ 2 ≤ 4 * lambda ^ 2 * k ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmuLambda (sq_nonneg k)
      _ ≤ 4 * (4 * (600 / mu ^ 2) ^ 2 * Q) := by
        have hkraw : lambda ^ 2 * k ^ 2 ≤
            4 * (600 / mu ^ 2) ^ 2 * Q := by
          simpa [lambda, mu, k, Q] using hkernelRaw
        nlinarith
      _ = 16 * (600 / mu ^ 2) ^ 2 * Q := by ring
  have hresRatio : eta ^ 4 / mu ^ 2 ≤
      128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 * (A / L) := by
    simpa [eta, mu, A, L, x] using (hscale a ha).2
  have hleafRatio : Q / mu ^ 4 ≤ 5632 * L ^ 2 / Real.sqrt x := by
    simpa [Q, mu, L, x] using hleaf a ha
  have hsqBudget : (mu * r) ^ 2 ≤
      C * A * L / Real.sqrt x := by
    calc
      (mu * r) ^ 2 ≤ (100 * eta ^ 2 * k) ^ 2 := hreturnSq
      _ = 10000 * eta ^ 4 * k ^ 2 := by ring
      _ = (10000 * eta ^ 4 / mu ^ 2) * (mu ^ 2 * k ^ 2) := by
        field_simp [ne_of_gt hmu]
      _ ≤ (10000 * eta ^ 4 / mu ^ 2) *
          (16 * (600 / mu ^ 2) ^ 2 * Q) := by
        exact mul_le_mul_of_nonneg_left hweightedKernel (by positivity)
      _ = 160000 * 600 ^ 2 * (eta ^ 4 / mu ^ 2) *
          (Q / mu ^ 4) := by
        field_simp [ne_of_gt hmu]
        ring
      _ ≤ 160000 * 600 ^ 2 *
          (128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 * (A / L)) *
          (5632 * L ^ 2 / Real.sqrt x) := by
        gcongr
      _ = C * A * L / Real.sqrt x := by
        dsimp [C]
        field_simp [ne_of_gt hlog, ne_of_gt hsqrt]
  have hgrowth : C * L ^ 3 ≤ Real.sqrt x := by
    simpa [C, L, x] using hlogGrowth
  have htargetSq : C * A * L / Real.sqrt x ≤ (A / L) ^ 2 := by
    rw [div_le_iff₀ hsqrt]
    have hscaled : (A / L ^ 2) * (C * L ^ 3) ≤
        (A / L ^ 2) * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hgrowth (by positivity)
    calc
      C * A * L = (A / L ^ 2) * (C * L ^ 3) := by
        field_simp [ne_of_gt hlog]
      _ ≤ (A / L ^ 2) * Real.sqrt x := hscaled
      _ ≤ (A / L) ^ 2 * Real.sqrt x := by
        gcongr
        have : A / L ^ 2 ≤ A ^ 2 / L ^ 2 := by
          exact div_le_div_of_nonneg_right
            (show A ≤ A ^ 2 by nlinarith) (sq_nonneg L)
        simpa [div_pow] using this
  have hsq : (mu * r) ^ 2 ≤ (A / L) ^ 2 := hsqBudget.trans htargetSq
  have hleft : 0 ≤ mu * r := mul_nonneg hmu.le (norm_nonneg _)
  have hright : 0 ≤ A / L := div_nonneg (by positivity) hlog.le
  have hfinal := (sq_le_sq₀ hleft hright).mp hsq
  simpa [mu, r, A, L, x] using hfinal

/-- The cancellation-preserving finite endpoint for the exact Paper II
molecule.  If the two-mode determinant controls the *combined* squared-energy
residual, then the exact molecule root has the same bound against the
arithmetic target.  In particular, the linear feedback error and the square
of the root displacement are not bounded separately.

All canonical up/down targets, leaf multiplicities, the square-root boundary
count, and the identification with `firstExitCorrection` are discharged
internally. -/

theorem exactPrincipalMoleculeRoot_targetDefect_le_of_balancedSquaredDisplacement
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (err eta : ℝ)
    (hupden : ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      moleculeStarEnergy S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) : ℝ))
    (hdownden : ∀ q : PrimeStar.CanonicalDownIndex a,
      moleculeStarEnergy S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) : ℝ))
    (hbalanced :
      2 * moleculeStarEnergy S X a *
          ((exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a) -
            ((∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
              ⟪PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X)
                  (PrimeStar.canonicalUpTarget hS a q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a),
                PrimeStar.actualUpStarResolvent S X (squareRootCutoff X)
                  (PrimeStar.canonicalUpTarget hS a q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a)⟫_ℝ) +
            (∑ q : PrimeStar.CanonicalDownIndex a,
              ⟪PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X)
                  (PrimeStar.canonicalDownTarget a q)
                  (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
                    (PrimeStar.canonicalDownTarget a q) q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a),
                PrimeStar.actualDownStarResolvent S X (squareRootCutoff X)
                  (PrimeStar.canonicalDownTarget a q)
                  (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
                    (PrimeStar.canonicalDownTarget a q) q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a)⟫_ℝ))) +
        (exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a) ^ 2 = err)
    (herr : |err| ≤ eta) :
    targetDefect S X a (exactPrincipalMoleculeRoot S X a) ≤ eta := by
  let Y := squareRootCutoff X
  let mu := moleculeStarEnergy S X a
  let lam := exactPrincipalMoleculeRoot S X a
  let c0 := PrimeStar.largePrimeNormalizedStarMode S X Y a 1 a
  let U : Finset (PrimeStar.CanonicalUpIndex S X Y a) := Finset.univ
  let D : Finset (PrimeStar.CanonicalDownIndex a) := Finset.univ
  let upTarget := fun q : PrimeStar.CanonicalUpIndex S X Y a ↦
    PrimeStar.canonicalUpTarget hS a q
  let downTarget := fun q : PrimeStar.CanonicalDownIndex a ↦
    PrimeStar.canonicalDownTarget a q
  let downLeaves := fun q : PrimeStar.CanonicalDownIndex a ↦
    PrimeStar.canonicalDownLeaves S X Y (downTarget q) q
  let rho :=
    (∑ q ∈ U,
      ⟪PrimeStar.actualUpStarFirstExit S X Y (upTarget q) mu c0,
        PrimeStar.actualUpStarResolvent S X Y (upTarget q) mu c0⟫_ℝ) +
    (∑ q ∈ D,
      ⟪PrimeStar.actualDownStarFirstExit S X Y (downTarget q)
          (downLeaves q) mu c0,
        PrimeStar.actualDownStarResolvent S X Y (downTarget q)
          (downLeaves q) mu c0⟫_ℝ)
  have hmu : mu ≠ 0 := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hc0 : c0 ^ 2 = 1 / 2 := by
    exact PrimeStar.sq_largePrimeNormalizedStarMode_center (by norm_num) hd
  have hdownLeaves : ∀ q ∈ D,
      downLeaves q ⊆ PrimeStar.largePrimeLeaves S X Y (downTarget q) := by
    intro q _hq
    exact PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves _
  have hdownCard : ∀ q ∈ D, ((downLeaves q).card : ℝ) = mu ^ 2 := by
    intro q _hq
    have hcard := PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
    rw [show (downLeaves q).card =
        PrimeStar.largePrimeStarDegree S X Y a by
      simpa [downLeaves, downTarget, Y] using hcard]
    simpa [mu, Y] using (moleculeStarEnergy_sq S X a).symm
  have hfinite := PrimeStar.actualFiniteStarCorrection_eq
    U D upTarget downTarget downLeaves mu c0 hmu hc0
    (by simpa [U, upTarget, mu, Y] using hupden)
    hdownLeaves hdownCard
    (by simpa [D, downTarget, mu, Y] using hdownden)
  have hcorrection :=
    PrimeStar.canonicalFiniteStarCorrection_eq_fixedCenterActualCorrection
      hS a ha
  have hcorrection' :
      PrimeStar.finiteStarCorrection U D
          (fun q ↦
            (PrimeStar.largePrimeStarDegree S X Y (upTarget q) : ℝ) / mu ^ 2)
          (fun q ↦
            (PrimeStar.largePrimeStarDegree S X Y (downTarget q) : ℝ) / mu ^ 2) =
        firstExitCorrection S X a := by
    simpa [U, D, upTarget, downTarget, mu, moleculeStarEnergy, Y,
      firstExitCorrection_eq_paperOne] using hcorrection
  have hboundary :
      (PrimeStar.allowedPrimeCount S Y : ℝ) = (U.card : ℕ) := by
    have hcY : (a : ℕ) * Y ≤ X :=
      (Nat.mul_le_mul_right Y ha).trans (Nat.sqrt_le X)
    exact_mod_cast
      (PrimeStar.card_univ_canonicalUpIndex_eq_allowedPrimeCount
        (S := S) (X := X) (Y := Y) (c := a) hcY).symm
  have hdegree : mu ^ 2 =
      (PrimeStar.allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
        (PrimeStar.allowedPrimeCount S Y : ℝ) := by
    have hcY : (a : ℕ) * Y ≤ X :=
      (Nat.mul_le_mul_right Y ha).trans (Nat.sqrt_le X)
    have hYXa : Y ≤ X / (a : ℕ) :=
      (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos a)).2
        (by simpa [Nat.mul_comm] using hcY)
    dsimp only [mu, moleculeStarEnergy, Y]
    exact PrimeStar.sq_sqrt_largePrimeStarDegree_eq_allowedPrimeDifference
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a) hS ha hYXa
  have hrho : 2 * mu * rho - (U.card : ℝ) =
      firstExitCorrection S X a := by
    rw [← hcorrection']
    dsimp [rho]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    simpa [mul_assoc] using hfinite
  have hbalanced' :
      2 * mu * ((lam - mu) - rho) + (lam - mu) ^ 2 = err := by
    simpa [lam, mu, rho, U, D, upTarget, downTarget, downLeaves, c0, Y,
      add_assoc] using hbalanced
  rw [targetDefect_eq]
  have hexact :
      lam ^ 2 - (PrimeStar.allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
          firstExitCorrection S X a = err := by
    rw [← hrho]
    rw [hboundary] at hdegree
    nlinarith
  rw [show exactPrincipalMoleculeRoot S X a = lam by rfl, hexact]
  exact herr

/-- A scalar displacement estimate for the exact Paper II molecule implies
the corresponding finite arithmetic target estimate.  All canonical
up/down targets, leaf multiplicities, the square-root boundary count, and
the identification with `firstExitCorrection` are discharged internally.

This is the exact finite bridge between the signed boundary calculation and
`ExactMoleculeTargetTransport`. -/

theorem inner_actualUpFirstExit_largePrimeStarResolvent_eq_actualUpResolvent
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {mu c0 : ℝ}
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    ⟪PrimeStar.actualUpStarFirstExit S X Y target mu c0,
        PrimeStar.largePrimeStarResolventOfVector S X Y target mu
          (PrimeStar.actualUpStarFirstExit S X Y target mu c0)⟫_ℝ =
      ⟪PrimeStar.actualUpStarFirstExit S X Y target mu c0,
        PrimeStar.actualUpStarResolvent S X Y target mu c0⟫_ℝ := by
  have hgeneric := actualUpStar_signedResponse
    (target := target) (lambda := mu) (mu := mu) (c0 := c0)
      (eps := (1 : ℝ)) (tau := (1 : ℝ))
      (by norm_num) (by norm_num) hmu hmu hden hc0
  have hactual := PrimeStar.actualUpStar_quadraticForm
    (target := target) (mu := mu) (c0 := c0) hmu hden hc0
  have hformula :
      (mu * mu + ((1 : ℝ) + 1) *
          (PrimeStar.largePrimeStarDegree S X Y target : ℝ) +
        1 * 1 * (PrimeStar.largePrimeStarDegree S X Y target : ℝ) *
          mu / mu) /
        (mu ^ 2 - (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) =
      (mu ^ 2 + 3 *
          (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) /
        (mu ^ 2 - (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) := by
    field_simp [hmu]
    ring
  rw [one_mul] at hgeneric
  rw [hformula] at hgeneric
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hmu)
    (hgeneric.trans hactual.symm)

/-- The analogous quadratic-form bridge for a nonresonant partial-leaf
down-star. -/

theorem inner_actualDownFirstExit_largePrimeStarResolvent_eq_actualDownResolvent
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {mu c0 : ℝ}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hmu : mu ≠ 0)
    (hden : mu ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ))
    (hc0 : c0 ^ 2 = 1 / 2) :
    ⟪PrimeStar.actualDownStarFirstExit S X Y target P mu c0,
        PrimeStar.largePrimeStarResolventOfVector S X Y target mu
          (PrimeStar.actualDownStarFirstExit S X Y target P mu c0)⟫_ℝ =
      ⟪PrimeStar.actualDownStarFirstExit S X Y target P mu c0,
        PrimeStar.actualDownStarResolvent S X Y target P mu c0⟫_ℝ := by
  have hgeneric := actualDownStar_signedResponse
    (target := target) (P := P) (lambda := mu) (mu := mu) (c0 := c0)
      (eps := (1 : ℝ)) (tau := (1 : ℝ)) hP hcard
      (by norm_num) (by norm_num) hmu hmu hden hc0
  have hactual := PrimeStar.actualDownStar_quadraticForm
    (target := target) (P := P) (mu := mu) (c0 := c0)
      hP hcard hmu hden hc0
  have hformula :
      mu *
          (mu ^ 2 * (1 + (1 : ℝ) * 1) +
            mu * mu * ((1 : ℝ) + 1) +
            1 * 1 *
              (mu ^ 2 -
                (PrimeStar.largePrimeStarDegree S X Y target : ℝ))) /
          (mu *
            (mu ^ 2 -
              (PrimeStar.largePrimeStarDegree S X Y target : ℝ))) =
        (5 * mu ^ 2 -
            (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) /
          (mu ^ 2 -
            (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) := by
    field_simp [hmu]
    ring
  rw [one_mul] at hgeneric
  rw [hformula] at hgeneric
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hmu)
    (hgeneric.trans hactual.symm)

/-- S1: the exact two-mode molecule root has the explicit first-exit target
to Paper-II accuracy, uniformly throughout every fixed sub-square-root power
range.  This theorem is the shared pointwise producer used by both the
prescribed-rank and almost-all assemblies. -/

theorem eventually_powerRange_exactPrincipalMoleculeRoot_targetDefect_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
        InPowerRange theta X (a : ℕ) →
          targetDefect S X a (exactPrincipalMoleculeRoot S X a) ≤
            C * (a : ℝ) / Real.log (X : ℝ) := by
  let C : ℝ :=
    10 + 12800000000 * PrimeStar.sqrtCutoffResidualConstant ^ 4
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [
      eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
        S hS htheta,
      eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
        S hS htheta,
      eventually_powerRange_moleculeStarEnergy_firstExitCompressionGap
        S hS htheta,
      eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant
        S hS htheta,
      eventually_powerRange_moleculeStarEnergy_firstExitNonresonant
        S hS htheta,
      eventually_powerRange_one_half_le_abs_exactPrincipalMoleculeBoundaryModeCoefficient
        S hS htheta,
      eventually_powerRange_exactPrincipalMoleculeRoot_sourceWeightedShift
        S hS htheta,
      eventually_powerRange_starEnergy_mul_kernelBoundaryReturn_le_targetScale
        S hS htheta,
      eventually_powerRange_moleculeStarEnergy_residualScaleBundle
        S hS htheta,
      PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned,
      eventually_ge_atTop 16]
      with X hwindow hgapRoot hgapMu hdenRoot hdenMu hoverlap hshiftSharp
        hkernelReturn hscale hresidual hX
  intro a ha
  obtain ⟨haY, hd, hshiftWindow, hresSmall⟩ := hwindow a ha
  obtain ⟨hupdenMu, hdowndenMu, hdenMuAll⟩ := hdenMu a ha
  let A : ℝ := (a : ℕ)
  let x : ℝ := X
  let L : ℝ := Real.log x
  let lambda : ℝ := exactPrincipalMoleculeRoot S X a
  let mu : ℝ := moleculeStarEnergy S X a
  let eta : ℝ := PrimeStar.sqrtCutoffResidualScale X
  let gammaLambda : ℝ := mu / 100
  let gammaMu : ℝ := mu / 200
  let alpha : ℝ := exactPrincipalMoleculeBoundaryModeCoefficient S X a 1
  let rpp : ℝ := ⟪exactBoundaryModeInteriorSource S X a 1,
    exactBoundaryModeInteriorVector S X a 1⟫_ℝ
  let rpm : ℝ := ⟪exactBoundaryModeInteriorSource S X a 1,
    exactBoundaryModeInteriorVector S X a (-1)⟫_ℝ
  let rmp : ℝ := ⟪exactBoundaryModeInteriorSource S X a (-1),
    exactBoundaryModeInteriorVector S X a 1⟫_ℝ
  let rmm : ℝ := ⟪exactBoundaryModeInteriorSource S X a (-1),
    exactBoundaryModeInteriorVector S X a (-1)⟫_ℝ
  let bplus : MoleculeAmbient S X := exactBoundaryModeInteriorSource S X a 1
  let rho : ℝ := ⟪bplus,
    PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
      mu bplus⟫_ℝ
  let kp : ℝ := ⟪moleculePositiveStarMode S X a,
    exactPrincipalMoleculeKernelBoundaryReturn S X a⟫_ℝ
  let km : ℝ := ⟪PrimeStar.largePrimeNormalizedStarMode S X
      (squareRootCutoff X) a (-1),
    exactPrincipalMoleculeKernelBoundaryReturn S X a⟫_ℝ
  let Kret : ℝ := ‖exactPrincipalMoleculeKernelBoundaryReturn S X a‖
  let R : ℝ := eta ^ 2 / gammaLambda
  let D : ℝ := 200 * eta ^ 2 / mu
  let E : ℝ := D * (eta / gammaLambda) * (eta / gammaMu)
  let err : ℝ :=
    2 * mu * ((lambda - mu) - rho) + (lambda - mu) ^ 2
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hlog : 0 < L := by
    dsimp [L, x]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have heta : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hgammaLambda : 0 < gammaLambda := by
    dsimp [gammaLambda]
    positivity
  have hgammaMu : 0 < gammaMu := by
    dsimp [gammaMu]
    positivity
  have hlambdaShift : |lambda - mu| ≤ mu / 100 := by
    simpa [lambda, mu] using hshiftWindow
  have hlambdaLower : mu / 2 ≤ lambda := by
    have := (abs_le.mp hlambdaShift).1
    nlinarith
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (half_pos hmu) hlambdaLower
  have hlambdaAbs : |lambda| ≤ 2 * mu := by
    rw [abs_of_pos hlambdaPos]
    have := (abs_le.mp hlambdaShift).2
    nlinarith
  have hgapLambda : ∀ z : MoleculeAmbient S X,
      gammaLambda * ‖z‖ ≤
        ‖lambda • z -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a z‖ := by
    simpa [gammaLambda, lambda, mu] using hgapRoot a ha
  have hgapMu' : ∀ z : MoleculeAmbient S X,
      gammaMu * ‖z‖ ≤
        ‖mu • z -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a z‖ := by
    simpa [gammaMu, mu] using hgapMu a ha
  have hdenLambda : ∀ b ∈ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a,
      lambda ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b : ℝ) := by
    simpa [lambda] using hdenRoot a ha
  have hdenMu' : ∀ b ∈ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a,
      mu ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b : ℝ) := by
    simpa [mu] using hdenMuAll
  have hH : ∀ z : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          z‖ ≤ eta * ‖z‖ := by
    intro z
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S z
  have halphaLower : 1 / 2 ≤ |alpha| := by
    simpa [alpha] using hoverlap a ha
  have halphaUpper : |alpha| ≤ 1 := by
    simpa [alpha] using
      (abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one
        (S := S) (X := X) (a := a) (eps := (1 : ℝ)) hd (by norm_num))
  have hD : |lambda - mu| ≤ D := by
    simpa [lambda, mu, eta, D] using hshiftSharp a ha
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hresponse (eps tau : ℝ) (heps : eps ^ 2 = 1)
      (htau : tau ^ 2 = 1) :
      |⟪exactBoundaryModeInteriorSource S X a eps,
          exactBoundaryModeInteriorVector S X a tau⟫_ℝ| ≤ R := by
    simpa [R, gammaLambda] using
      abs_exactBoundaryMode_sourceResponse_le_smallPrime
        hS haY hd heps htau hlambdaPos.ne' hgammaLambda heta
          hgapLambda hdenLambda hH
  have hrpp : |rpp| ≤ R := by
    simpa [rpp] using hresponse 1 1 (by norm_num) (by norm_num)
  have hrpm : |rpm| ≤ R := by
    simpa [rpm] using hresponse 1 (-1) (by norm_num) (by norm_num)
  have hrmp : |rmp| ≤ R := by
    simpa [rmp] using hresponse (-1) 1 (by norm_num) (by norm_num)
  have hrmm : |rmm| ≤ R := by
    simpa [rmm] using hresponse (-1) (-1) (by norm_num) (by norm_num)
  have hdiff : |rpp - rho| ≤ E := by
    have hraw := abs_boundaryMode_positiveResponse_sub_le_smallPrime
      hS haY hd hlambdaPos.ne' hmu.ne' hgammaLambda hgammaMu heta
        hgapLambda hgapMu' hdenLambda hdenMu' hH
    have hfacLambda : 0 ≤ eta / gammaLambda :=
      div_nonneg heta hgammaLambda.le
    have hfacMu : 0 ≤ eta / gammaMu :=
      div_nonneg heta hgammaMu.le
    calc
      |rpp - rho| ≤ |lambda - mu| * (eta / gammaLambda) *
          (eta / gammaMu) := by
        simpa [rpp, rho, bplus, lambda, mu,
          exactBoundaryModeInteriorVector] using hraw
      _ ≤ D * (eta / gammaLambda) * (eta / gammaMu) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hD hfacLambda) hfacMu
      _ = E := by rfl
  have hkp : |kp| ≤ Kret := by
    calc
      |kp| ≤ ‖moleculePositiveStarMode S X a‖ * Kret := by
        simpa [kp, Kret] using abs_real_inner_le_norm
          (moleculePositiveStarMode S X a)
          (exactPrincipalMoleculeKernelBoundaryReturn S X a)
      _ = Kret := by rw [norm_moleculePositiveStarMode hd, one_mul]
  have hkm : |km| ≤ Kret := by
    calc
      |km| ≤ ‖PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a (-1)‖ * Kret := by
        simpa [km, Kret] using abs_real_inner_le_norm
          (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a (-1))
          (exactPrincipalMoleculeKernelBoundaryReturn S X a)
      _ = Kret := by
        rw [PrimeStar.norm_largePrimeNormalizedStarMode hd, one_mul]
  have hidentity := exactPrincipalMolecule_balancedSquaredDisplacement_mul
    hS haY hd hlambdaPos.ne' gammaLambda hgammaLambda hgapLambda
      hdenLambda rho
  have herrRaw : |err| ≤
      2 * (Kret * (3 * mu + R) + R * Kret +
        (2 * mu * E + D * (2 * R) + 2 * R ^ 2)) := by
    simpa [err, lambda, mu, alpha, rpp, rpm, rmp, rmm, kp, km] using
      abs_balancedSquaredDisplacement_le_of_response_bounds
        hmu.le hR hE (norm_nonneg _) hDnonneg halphaLower halphaUpper
          hlambdaAbs hD hrpp hrpm hrmp hrmm hdiff hkp hkm hidentity
  have hRle : R ≤ mu := by
    have hsmall : 1000000 * eta ^ 2 ≤ mu ^ 2 := by
      simpa [eta, mu] using hresSmall
    have hrewrite : eta ^ 2 / (mu / 100) = 100 * eta ^ 2 / mu := by
      field_simp [ne_of_gt hmu]
    dsimp [R, gammaLambda]
    rw [hrewrite]
    apply (div_le_iff₀ hmu).2
    nlinarith
  have hkernelScale : mu * Kret ≤ A / L := by
    simpa [mu, Kret, A, L, x] using hkernelReturn a ha
  have hresRatio : eta ^ 4 / mu ^ 2 ≤
      128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 * (A / L) := by
    simpa [eta, mu, A, L, x] using (hscale a ha).2
  have hkernelPart :
      2 * (Kret * (3 * mu + R) + R * Kret) ≤
        10 * (mu * Kret) := by
    have hK : 0 ≤ Kret := norm_nonneg _
    have hRK : R * Kret ≤ mu * Kret :=
      mul_le_mul_of_nonneg_right hRle hK
    calc
      2 * (Kret * (3 * mu + R) + R * Kret) =
          6 * (mu * Kret) + 4 * (R * Kret) := by ring
      _ ≤ 6 * (mu * Kret) + 4 * (mu * Kret) := by
        simpa [add_comm] using
          (add_le_add_left
            (mul_le_mul_of_nonneg_left hRK (show (0 : ℝ) ≤ 4 by norm_num))
            (6 * (mu * Kret)))
      _ = 10 * (mu * Kret) := by ring
  have hresponsePart :
      2 * (2 * mu * E + D * (2 * R) + 2 * R ^ 2) =
        16120000 * (eta ^ 4 / mu ^ 2) := by
    dsimp [E, D, R, gammaLambda, gammaMu]
    field_simp [ne_of_gt hmu]
    ring
  have herrCompact : |err| ≤
      10 * (mu * Kret) + 16120000 * (eta ^ 4 / mu ^ 2) := by
    calc
      |err| ≤ 2 * (Kret * (3 * mu + R) + R * Kret +
          (2 * mu * E + D * (2 * R) + 2 * R ^ 2)) := herrRaw
      _ = 2 * (Kret * (3 * mu + R) + R * Kret) +
          2 * (2 * mu * E + D * (2 * R) + 2 * R ^ 2) := by ring
      _ ≤ 10 * (mu * Kret) +
          2 * (2 * mu * E + D * (2 * R) + 2 * R ^ 2) := by gcongr
      _ = 10 * (mu * Kret) + 16120000 * (eta ^ 4 / mu ^ 2) := by
        rw [hresponsePart]
  have herrTarget : |err| ≤ C * A / L := by
    calc
      |err| ≤ 10 * (mu * Kret) +
          16120000 * (eta ^ 4 / mu ^ 2) := herrCompact
      _ ≤ 10 * (A / L) +
          16120000 *
            (128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 * (A / L)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hkernelScale (by norm_num))
          (mul_le_mul_of_nonneg_left hresRatio (by norm_num))
      _ ≤ C * A / L := by
        have hAL : 0 ≤ A / L := div_nonneg hA.le hlog.le
        calc
          10 * (A / L) +
              16120000 *
                (128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 * (A / L)) =
              (10 + 2063360000 *
                PrimeStar.sqrtCutoffResidualConstant ^ 4) * (A / L) := by ring
          _ ≤ (10 + 12800000000 *
                PrimeStar.sqrtCutoffResidualConstant ^ 4) * (A / L) := by
            have hk4 : 0 ≤ PrimeStar.sqrtCutoffResidualConstant ^ 4 :=
              by positivity
            have hcoeff :
                10 + 2063360000 * PrimeStar.sqrtCutoffResidualConstant ^ 4 ≤
                  10 + 12800000000 *
                    PrimeStar.sqrtCutoffResidualConstant ^ 4 := by
              simpa [add_comm] using
                (add_le_add_left
                  (mul_le_mul_of_nonneg_right
                    (show (2063360000 : ℝ) ≤ 12800000000 by norm_num) hk4) 10)
            exact mul_le_mul_of_nonneg_right hcoeff hAL
          _ = C * A / L := by
            dsimp [C]
            ring
  have hrho := boundaryMode_sourceResponse_eq_sum_local_at
    hS haY hd (eps := (1 : ℝ)) (tau := (1 : ℝ))
      (lambda := mu) (by norm_num) (by norm_num) hmu.ne'
      gammaMu hgammaMu hgapMu' hdenMu'
  have hrhoCanonical : rho =
      (∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
        ⟪PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) mu
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a 1 a),
          PrimeStar.actualUpStarResolvent S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) mu
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a 1 a)⟫_ℝ) +
      (∑ q : PrimeStar.CanonicalDownIndex a,
        ⟪PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q)
            (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
              (PrimeStar.canonicalDownTarget a q) q) mu
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a 1 a),
          PrimeStar.actualDownStarResolvent S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q)
            (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
              (PrimeStar.canonicalDownTarget a q) q) mu
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a 1 a)⟫_ℝ) := by
    dsimp [rho, bplus]
    rw [hrho]
    simp only [Fintype.sum_sum_type, PrimeStar.canonicalExitFirstExit]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro q _hq
      rw [real_inner_comm]
      simpa [mu] using
        (inner_actualUpFirstExit_largePrimeStarResolvent_eq_actualUpResolvent
          (target := PrimeStar.canonicalUpTarget hS a q)
          (mu := mu)
          (c0 := PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a 1 a)
          hmu.ne' (hupdenMu q)
          (PrimeStar.sq_largePrimeNormalizedStarMode_center (by norm_num) hd))
    · apply Finset.sum_congr rfl
      intro q _hq
      rw [real_inner_comm]
      have hP : PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) q ⊆
          PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q) :=
        PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves _
      have hcard :
          ((PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q) q).card : ℝ) = mu ^ 2 := by
        have hcardNat :=
          PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS haY q
        rw [hcardNat]
        simpa [mu] using (moleculeStarEnergy_sq S X a).symm
      simpa [mu] using
        (inner_actualDownFirstExit_largePrimeStarResolvent_eq_actualDownResolvent
          (target := PrimeStar.canonicalDownTarget a q)
          (P := PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q) q)
          (mu := mu)
          (c0 := PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a 1 a)
          hP hcard hmu.ne' (hdowndenMu q)
          (PrimeStar.sq_largePrimeNormalizedStarMode_center (by norm_num) hd))
  have hbalanced :
      2 * moleculeStarEnergy S X a *
          ((exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a) -
            ((∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
              ⟪PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X)
                  (PrimeStar.canonicalUpTarget hS a q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a),
                PrimeStar.actualUpStarResolvent S X (squareRootCutoff X)
                  (PrimeStar.canonicalUpTarget hS a q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a)⟫_ℝ) +
            (∑ q : PrimeStar.CanonicalDownIndex a,
              ⟪PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X)
                  (PrimeStar.canonicalDownTarget a q)
                  (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
                    (PrimeStar.canonicalDownTarget a q) q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a),
                PrimeStar.actualDownStarResolvent S X (squareRootCutoff X)
                  (PrimeStar.canonicalDownTarget a q)
                  (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
                    (PrimeStar.canonicalDownTarget a q) q)
                  (moleculeStarEnergy S X a)
                  (PrimeStar.largePrimeNormalizedStarMode S X
                    (squareRootCutoff X) a 1 a)⟫_ℝ))) +
        (exactPrincipalMoleculeRoot S X a - moleculeStarEnergy S X a) ^ 2 =
          err := by
    rw [← hrhoCanonical]
  have htarget :=
    exactPrincipalMoleculeRoot_targetDefect_le_of_balancedSquaredDisplacement
      hS haY hd err (C * A / L) hupdenMu hdowndenMu hbalanced herrTarget
  simpa [C, A, L, x] using htarget

/-- The weaker pole margin `r ≤ 15/16` is sufficient for the power-band
application and follows uniformly from multiplicative PNT comparisons. -/
theorem abs_upStarCorrection_le_sixtyfour_mul
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 15 / 16) :
    |upStarCorrection r| ≤ 64 * r := by
  have hden : 0 < 1 - r := by linarith
  rw [upStarCorrection, abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hr0)
    hden.le)]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- A down-star ratio at least `17/16` remains a fixed distance from the
pole at one.  The deliberately coarse constant is uniform in the centre. -/
theorem abs_downStarCorrection_le_sixtyfive
    {s : ℝ} (hs : 17 / 16 ≤ s) :
    |downStarCorrection s| ≤ 65 := by
  have hden : 0 < s - 1 := by linarith
  have hdenAbs : |1 - s| = s - 1 := by
    rw [abs_of_neg (by linarith : 1 - s < 0)]
    ring
  rw [downStarCorrection, abs_div, hdenAbs]
  apply (div_le_iff₀ hden).2
  calc
    |5 - s| = |4 - (s - 1)| := by ring_nf
    _ ≤ |(4 : ℝ)| + |s - 1| := abs_sub _ _
    _ = 4 + (s - 1) := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_pos hden]
    _ ≤ 65 * (s - 1) := by
      nlinarith

/-- Allowed reciprocal primes through `Y` are dominated by the ordinary
harmonic sum. -/
theorem sum_allowedPrime_reciprocal_le_one_add_log
    (S : Finset ℕ) (Y : ℕ) :
    (∑ q ∈ (Nat.primesLE Y).filter (fun q ↦ q ∉ S), (q : ℝ)⁻¹) ≤
      1 + Real.log (Y : ℝ) := by
  let Q := (Nat.primesLE Y).filter (fun q ↦ q ∉ S)
  have hsubset : Q ⊆ Finset.Icc 1 Y := by
    intro q hq
    have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1)
    exact Finset.mem_Icc.mpr ⟨hprime.2.one_le, hprime.1⟩
  calc
    (∑ q ∈ Q, (q : ℝ)⁻¹) ≤
        ∑ q ∈ Finset.Icc 1 Y, (q : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (harmonic Y : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ ≤ 1 + Real.log (Y : ℝ) := harmonic_le_one_add_log Y

/-- The number of distinct prime factors is controlled by the real logarithm.
This is the form used for the finite down-star sum. -/
theorem primeFactors_card_le_log_div_log_two
    {a : ℕ} (ha : 0 < a) :
    (a.primeFactors.card : ℝ) ≤ Real.log (a : ℝ) / Real.log 2 := by
  have hpowNat : 2 ^ a.primeFactors.card ≤ a := by
    calc
      2 ^ a.primeFactors.card = ∏ _p ∈ a.primeFactors, 2 := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ a.primeFactors, p := by
        exact Finset.prod_le_prod' fun p hp ↦
          (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ a := Nat.le_of_dvd ha (Nat.prod_primeFactors_dvd a)
  have hpowReal : (2 : ℝ) ^ a.primeFactors.card ≤ (a : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.le_log_of_pow_le (by norm_num : (0 : ℝ) < 2) hpowReal
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 (by simpa using hlog)

/-- Finite first-exit bound at the coarser denominator margins supplied by
uniform power-band PNT. -/
theorem abs_firstExitCorrection_le_of_power_ratio_bounds
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X) {K : ℝ}
    (hup0 : ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
      0 ≤ actualUpStarRatio S (a : ℕ) X q)
    (hupAway :
      ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
        actualUpStarRatio S (a : ℕ) X q ≤ 15 / 16)
    (hupRecip : ∀ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
      actualUpStarRatio S (a : ℕ) X q ≤ K / (q : ℝ))
    (hdown : ∀ q ∈ (a : ℕ).primeFactors,
      17 / 16 ≤ arithmeticStarDegree S ((a : ℕ) / q) X /
        arithmeticStarDegree S (a : ℕ) X) :
    |firstExitCorrection S X a| ≤
      64 * K *
          (∑ q ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S),
            (q : ℝ)⁻¹) +
        65 * ((a : ℕ).primeFactors.card : ℝ) := by
  let Q := (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S)
  have hup :
      |∑ q ∈ Q, upStarCorrection (actualUpStarRatio S (a : ℕ) X q)| ≤
        64 * K * (∑ q ∈ Q, (q : ℝ)⁻¹) := by
    calc
      |∑ q ∈ Q, upStarCorrection (actualUpStarRatio S (a : ℕ) X q)| ≤
          ∑ q ∈ Q, |upStarCorrection (actualUpStarRatio S (a : ℕ) X q)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Q, 64 * (K / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        calc
          |upStarCorrection (actualUpStarRatio S (a : ℕ) X q)| ≤
              64 * actualUpStarRatio S (a : ℕ) X q :=
            abs_upStarCorrection_le_sixtyfour_mul (hup0 q hq) (hupAway q hq)
          _ ≤ 64 * (K / (q : ℝ)) := by
            gcongr
            exact hupRecip q hq
      _ = 64 * K * (∑ q ∈ Q, (q : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [div_eq_mul_inv]
        ring
  have hdownSum :
      |∑ q ∈ (a : ℕ).primeFactors,
          downStarCorrection
            (arithmeticStarDegree S ((a : ℕ) / q) X /
              arithmeticStarDegree S (a : ℕ) X)| ≤
        65 * ((a : ℕ).primeFactors.card : ℝ) := by
    calc
      |∑ q ∈ (a : ℕ).primeFactors,
          downStarCorrection
            (arithmeticStarDegree S ((a : ℕ) / q) X /
              arithmeticStarDegree S (a : ℕ) X)| ≤
          ∑ q ∈ (a : ℕ).primeFactors,
            |downStarCorrection
              (arithmeticStarDegree S ((a : ℕ) / q) X /
                arithmeticStarDegree S (a : ℕ) X)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ (a : ℕ).primeFactors, (65 : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact abs_downStarCorrection_le_sixtyfive (hdown q hq)
      _ = 65 * ((a : ℕ).primeFactors.card : ℝ) := by
        simp
        ring
  rw [firstExitCorrection]
  exact (abs_add_le _ _).trans (add_le_add hup hdownSum)
/-- An explicit source-independent constant for the logarithmic first-exit
bound on a fixed power range. -/
noncomputable def powerBandFirstExitCorrectionLogConstant : ℝ :=
  6144 + 65 / Real.log 2

theorem powerBandFirstExitCorrectionLogConstant_pos :
    0 < powerBandFirstExitCorrectionLogConstant := by
  rw [powerBandFirstExitCorrectionLogConstant]
  positivity

/-- The exact first-exit correction is uniformly logarithmic throughout every
fixed power range strictly below the square-root boundary.  The theorem also
proves that all totalized divisions in the correction have nonzero
denominators. -/
theorem eventually_powerRange_firstExitCorrection_le_log
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InPowerRange θ X (a : ℕ) →
        FirstExitCorrectionRegular S X a ∧
          |firstExitCorrection S X a| ≤
            powerBandFirstExitCorrectionLogConstant * Real.log (X : ℝ) := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_powerRange_arithmeticStarDegree_bounds S hS hθ,
      eventually_powerRange_actualUpStarRatio_bounds S hS hθ,
      eventually_powerRange_downStarRatio_ge S hS hθ,
      hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 4]
      with X hdegree hup hdown hlogX hX
  intro a ha
  let Q := (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S)
  have hratio := hup a ha
  have hdownRatio := hdown a ha
  have hfinite := abs_firstExitCorrection_le_of_power_ratio_bounds
    (a := a) (K := 48)
    (fun q hq ↦ (hratio q hq).1)
    (fun q hq ↦ (hratio q hq).2.1)
    (fun q hq ↦ by simpa using (hratio q hq).2.2)
    hdownRatio
  have hYpos : (0 : ℝ) < Nat.sqrt X := by
    exact_mod_cast (Nat.sqrt_pos.2 (by omega : 0 < X))
  have hYX : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
  have hlogYX : Real.log (Nat.sqrt X : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hYpos (by exact_mod_cast hYX)
  have hrecip : (∑ q ∈ Q, (q : ℝ)⁻¹) ≤
      2 * Real.log (X : ℝ) := by
    calc
      (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ 1 + Real.log (Nat.sqrt X : ℝ) :=
        sum_allowedPrime_reciprocal_le_one_add_log S (Nat.sqrt X)
      _ ≤ 2 * Real.log (X : ℝ) := by linarith
  have haPos : (0 : ℝ) < (a : ℕ) := by
    exact_mod_cast PrimeStar.Vertex.coe_pos a
  have haX : (a : ℕ) ≤ X := PrimeStar.Vertex.coe_le a
  have hlogAX : Real.log ((a : ℕ) : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log haPos (by exact_mod_cast haX)
  have hcard : (((a : ℕ).primeFactors.card : ℕ) : ℝ) ≤
      Real.log (X : ℝ) / Real.log 2 :=
    (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos a)).trans
      (div_le_div_of_nonneg_right hlogAX
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  constructor
  · refine ⟨(hdegree a ha).2.1, ?_, ?_⟩
    · intro q hq hone
      have := (hratio q hq).2.1
      rw [hone] at this
      norm_num at this
    · intro q hq hone
      have := hdownRatio q hq
      rw [hone] at this
      norm_num at this
  · calc
      |firstExitCorrection S X a| ≤
          64 * 48 * (∑ q ∈ Q, (q : ℝ)⁻¹) +
            65 * ((a : ℕ).primeFactors.card : ℝ) := hfinite
      _ ≤ 64 * 48 * (2 * Real.log (X : ℝ)) +
          65 * (Real.log (X : ℝ) / Real.log 2) := by gcongr
      _ = powerBandFirstExitCorrectionLogConstant * Real.log (X : ℝ) := by
        rw [powerBandFirstExitCorrectionLogConstant]
        field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
        ring

/-- The continuation root is positive throughout each fixed power range.
This is the positivity input used when sorting the squared molecule roots
in D31; it follows from the existing root window, not a new isolation bound. -/
theorem eventually_powerRange_exactPrincipalMoleculeRoot_pos
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {θ : ℝ} (hθ : θ < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InPowerRange θ X (a : ℕ) → 0 < exactPrincipalMoleculeRoot S X a := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS hθ]
    with X hX
  intro a ha
  obtain ⟨_, hd, hwindow⟩ := hX a ha
  have hmu : 0 < moleculeStarEnergy S X a := by
    unfold moleculeStarEnergy
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hlower := (abs_le.mp hwindow).1
  linarith

end

end PrimeCoverPowerBand
