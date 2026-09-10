import PrimeCoverPowerBand.FullSpectrumTransfer
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Fin

/-!
# Finite coherent-compression owner

This module is the consumer-only extraction of the checked Paper II
coherent-compression calculation. It proves the graph-specific decomposition
and reduces its Hilbert--Schmidt norm to the common-core, boundary-kernel, and
residual-energy budgets used by the prescribed-rank assembly.
-/

namespace PrimeCoverPowerBand

open Filter Topology
open scoped Classical InnerProductSpace Matrix Matrix.Norms.L2Operator

noncomputable section

/-- Allowed arithmetic centres retained in the prefix `a ≤ K`. -/
abbrev MoleculeCenter (S : Finset ℕ) (X K : ℕ) :=
  {a : PrimeStar.Vertex S X // (a : ℕ) ≤ K}

theorem card_moleculeCenter_le_succ (S : Finset ℕ) (X K : ℕ) :
    Fintype.card (MoleculeCenter S X K) ≤ K + 1 := by
  let f : MoleculeCenter S X K → Fin (K + 1) := fun a =>
    ⟨(a.1 : ℕ), Nat.lt_succ_of_le a.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hnat : (a.1 : ℕ) = (b.1 : ℕ) := Fin.mk.inj hab
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    exact Fin.ext hnat
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hinj

/-- Exact-molecule synthesis over retained arithmetic centres. -/
def exactMoleculeFamilyFrameMatrix (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
  fun v a ↦ exactPrincipalMoleculeAmbientVector S X a.1 v

/-- Diagonal matrix of exact continuation roots. -/
def exactMoleculeFamilyRootMatrix (S : Finset ℕ) (X K : ℕ) :
    Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℝ :=
  Matrix.diagonal fun a ↦ exactPrincipalMoleculeRoot S X a.1

/-- Literal full-graph intertwining residual of the exact frame. -/
def exactMoleculeFamilyResidualMatrix (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
  ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ) *
      exactMoleculeFamilyFrameMatrix S X K -
    exactMoleculeFamilyFrameMatrix S X K *
      exactMoleculeFamilyRootMatrix S X K

theorem exactMoleculeFamilyResidualMatrix_col
    (S : Finset ℕ) (X K : ℕ) (a : MoleculeCenter S X K) :
    (exactMoleculeFamilyResidualMatrix S X K).col a =
      (exactPrincipalMoleculeResidual S X a.1).ofLp := by
  ext v
  change exactMoleculeFamilyResidualMatrix S X K v a =
    exactPrincipalMoleculeResidual S X a.1 v
  rw [exactMoleculeFamilyResidualMatrix, Matrix.sub_apply,
    exactMoleculeFamilyRootMatrix, Matrix.mul_diagonal]
  have h := congrArg (fun x : MoleculeAmbient S X ↦ x v)
    (show exactPrincipalMoleculeResidual S X a.1 =
        primeCoverAdjacencyOperator S X
            (exactPrincipalMoleculeAmbientVector S X a.1) -
          exactPrincipalMoleculeRoot S X a.1 •
            exactPrincipalMoleculeAmbientVector S X a.1 from rfl)
  simpa [exactMoleculeFamilyFrameMatrix, Matrix.mul_apply,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, mul_comm,
    primeCoverAdjacencyOperator, Matrix.toLpLin_apply, Matrix.toLin'_apply]
    using h.symm

def exactMoleculeFamilyComplexFrame (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  complexifyRealMatrix (exactMoleculeFamilyFrameMatrix S X K)

def exactMoleculeFamilyComplexResidual (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  complexifyRealMatrix (exactMoleculeFamilyResidualMatrix S X K)

/-- Frobenius/Hilbert--Schmidt norm with its instance fixed explicitly. -/
noncomputable def matrixFrobeniusNorm
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ℝ :=
  @norm _ Matrix.frobeniusNormedAddCommGroup.toNorm A

theorem matrixFrobeniusNorm_nonneg
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    0 ≤ matrixFrobeniusNorm A := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  exact norm_nonneg A

theorem matrixFrobeniusNorm_add_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) :
    matrixFrobeniusNorm (A + B) ≤
      matrixFrobeniusNorm A + matrixFrobeniusNorm B := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  exact norm_add_le A B

theorem matrixFrobeniusNorm_sq
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    matrixFrobeniusNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [matrixFrobeniusNorm]
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]
  have hsum : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by positivity
  exact Real.sq_sqrt hsum

set_option maxHeartbeats 800000

local instance exactMoleculeProjectionTailSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- Part of an exact molecule assembled from its two signed boundary modes
and the corresponding first-exit response. -/
def exactPrincipalMoleculeChargedBranch
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  exactPrincipalMoleculeSignedBoundaryVector S X a +
    exactPrincipalMoleculeSignedInteriorVector S X a

/-- Part of an exact molecule generated by its mean-zero boundary kernel. -/
def exactPrincipalMoleculeKernelBranch
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    MoleculeAmbient S X :=
  exactPrincipalMoleculeBoundaryKernel S X a +
    exactPrincipalMoleculeKernelInteriorVector S X a

/-- Under the literal first-exit resolvent hypotheses, the exact molecule is
the sum of its charged and kernel-generated branches. -/
theorem exactPrincipalMoleculeAmbientVector_eq_charged_add_kernelBranch
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
    exactPrincipalMoleculeAmbientVector S X a =
      exactPrincipalMoleculeChargedBranch S X a +
        exactPrincipalMoleculeKernelBranch S X a := by
  have hboundary : exactPrincipalMoleculeBoundaryVector S X a =
      exactPrincipalMoleculeSignedBoundaryVector S X a +
        exactPrincipalMoleculeBoundaryKernel S X a := by
    simp [exactPrincipalMoleculeSignedBoundaryVector]
  have hinterior : exactPrincipalMoleculeInteriorVector S X a =
      exactPrincipalMoleculeSignedInteriorVector S X a +
        exactPrincipalMoleculeKernelInteriorVector S X a :=
    exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel
      hS ha hroot gamma hgamma hgap hden
  rw [← exactPrincipalMolecule_boundary_add_interior ha,
    hboundary, hinterior]
  simp only [exactPrincipalMoleculeChargedBranch,
    exactPrincipalMoleculeKernelBranch]
  module

local instance exactExteriorPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance exactExteriorLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

local instance exactExteriorSmallPrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X Y).Adj :=
  Classical.decRel _

/-- The literal exact-molecule support is closed under the large-prime
forest. -/
theorem exactPrincipalMoleculeSupport_closed_under_largePrimeAdj
    {S : Finset ℕ} {X : ℕ} {a v w : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hv : v ∈ exactPrincipalMoleculeSupport S X a)
    (hvw : PrimeStar.LargePrimeAdj S (squareRootCutoff X) v w) :
    w ∈ exactPrincipalMoleculeSupport S X a := by
  rw [exactPrincipalMoleculeSupport] at hv ⊢
  rcases Finset.mem_union.mp hv with hvB | hvU
  · exact Finset.mem_union_left _
      (PrimeStar.largePrimeStarSupport_closed
        (PrimeStar.sqrtCutoff_condition X) ha hvB hvw)
  · exact Finset.mem_union_right _
      (PrimeStar.firstExitCompressionSupport_closed_under_largePrimeAdj
        (PrimeStar.sqrtCutoff_condition X) hvU hvw)

/-- The large-prime forest applied to an exact molecule has no coordinate
outside the molecule support. -/
theorem largePrime_apply_exactPrincipalMoleculeAmbientVector_eq_zero_of_not_mem
    {S : Finset ℕ} {X : ℕ} {a v : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hv : v ∉ exactPrincipalMoleculeSupport S X a) :
    Matrix.toEuclideanLin
        ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeAmbientVector S X a) v = 0 := by
  rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
  change ((PrimeStar.largePrimeGraph S X
    (squareRootCutoff X)).adjMatrix ℝ).mulVec
      (fun w ↦ exactPrincipalMoleculeAmbientVector S X a w) v = 0
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_eq_zero
  intro w hw
  have hvw : PrimeStar.LargePrimeAdj S (squareRootCutoff X) v w := by
    simpa using hw
  have hwout : w ∉ exactPrincipalMoleculeSupport S X a := by
    intro hwsupp
    exact hv (exactPrincipalMoleculeSupport_closed_under_largePrimeAdj
      ha hwsupp (PrimeStar.largePrimeAdj_symm hvw))
  rw [exactPrincipalMoleculeAmbientVector_eq_zero_of_not_mem_support hwout]

/-- The small-prime image of the original boundary star is already contained
in the exact first-exit support. -/
theorem smallPrime_apply_exactPrincipalMoleculeBoundaryVector_eq_zero_of_not_mem
    {S : Finset ℕ} {X : ℕ} {a v : PrimeStar.Vertex S X}
    (hv : v ∉ exactPrincipalMoleculeSupport S X a) :
    Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeBoundaryVector S X a) v = 0 := by
  have hvExit : v ∉ PrimeStar.smallPrimeFirstExitSupport S X
      (squareRootCutoff X) a := by
    intro hvExit
    have hvU := PrimeStar.smallPrimeFirstExitSupport_subset_firstExitCompressionSupport
      (PrimeStar.sqrtCutoff_condition X) hvExit
    exact hv (Finset.mem_union_right _ hvU)
  rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
  apply PrimeStar.smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
      (fun w ↦ exactPrincipalMoleculeBoundaryVector S X a w) _ hvExit
  intro w hw
  simp [exactPrincipalMoleculeBoundaryVector,
    PrimeStar.primeStarBoundaryProjection_apply, hw]

/-- The exact full-graph residual is precisely the exterior part of one
additional small-prime step from the first-exit interior. -/
theorem exactPrincipalMoleculeResidual_eq_exterior_smallPrime_interior
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    exactPrincipalMoleculeResidual S X a =
      PrimeStar.euclideanCoordinateComplementProjection
        (exactPrincipalMoleculeSupport S X a)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeInteriorVector S X a)) := by
  classical
  let L := Matrix.toEuclideanLin
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let x := exactPrincipalMoleculeAmbientVector S X a
  let xB := exactPrincipalMoleculeBoundaryVector S X a
  let xU := exactPrincipalMoleculeInteriorVector S X a
  ext v
  by_cases hv : v ∈ exactPrincipalMoleculeSupport S X a
  · let w : ExactPrincipalMoleculeCoordinate S X a := ⟨v, hv⟩
    rw [exactPrincipalMoleculeResidual_apply_coordinate_eq_zero hS ha w]
    simp [PrimeStar.euclideanCoordinateComplementProjection_apply, hv]
  · have hx0 : x v = 0 :=
      exactPrincipalMoleculeAmbientVector_eq_zero_of_not_mem_support hv
    have hLx0 : L x v = 0 := by
      exact largePrime_apply_exactPrincipalMoleculeAmbientVector_eq_zero_of_not_mem
        ha hv
    have hHxB0 : H xB v = 0 := by
      exact smallPrime_apply_exactPrincipalMoleculeBoundaryVector_eq_zero_of_not_mem
        hv
    have hxsplit : xB + xU = x := by
      exact exactPrincipalMolecule_boundary_add_interior ha
    rw [exactPrincipalMoleculeResidual,
      PrimeStar.euclideanCoordinateComplementProjection_apply,
      if_neg hv]
    change primeCoverAdjacencyOperator S X x v -
        exactPrincipalMoleculeRoot S X a * x v = H xU v
    rw [hx0, mul_zero, sub_zero]
    have hA : primeCoverAdjacencyOperator S X = L + H := by
      exact PrimeStar.primeCover_toEuclideanLin_eq_large_add_small
        S X (squareRootCutoff X)
    rw [hA, LinearMap.add_apply]
    change (L x).ofLp v + (H x).ofLp v = (H xU).ofLp v
    rw [hLx0, zero_add]
    rw [← hxsplit, map_add]
    change (H xB).ofLp v + (H xU).ofLp v = (H xU).ofLp v
    rw [hHxB0, zero_add]

/-- Orthogonal exterior projection cannot increase the two-exit response. -/
theorem norm_exactPrincipalMoleculeResidual_le_smallPrime_interior
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    ‖exactPrincipalMoleculeResidual S X a‖ ≤
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeInteriorVector S X a)‖ := by
  rw [exactPrincipalMoleculeResidual_eq_exterior_smallPrime_interior hS ha]
  exact PrimeStar.norm_euclideanCoordinateComplementProjection_le _ _

/-- A finite small-prime operator bound charges the exact residual only by
the norm of the first-exit interior. -/
theorem norm_exactPrincipalMoleculeResidual_le_smallPrime_mul_interior
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    {eta : ℝ} (hH : ∀ y : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          y‖ ≤ eta * ‖y‖) :
    ‖exactPrincipalMoleculeResidual S X a‖ ≤
      eta * ‖exactPrincipalMoleculeInteriorVector S X a‖ :=
  (norm_exactPrincipalMoleculeResidual_le_smallPrime_interior hS ha).trans
    (hH (exactPrincipalMoleculeInteriorVector S X a))

/-- A nonzero coordinate of the exact-molecule residual is reached from the
first-exit interior by one literal small-prime edge.

This is the support half of the T4b bounded-word enumeration.  Combined with
the six-form support theorem for the source molecule, every nonzero summand in
the raw overlap majorant is now an explicit molecule coordinate followed by
one additional small-prime step. -/
theorem exists_firstExitInteriorNeighbor_of_exactPrincipalMoleculeResidual_ne_zero
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a v : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hv : exactPrincipalMoleculeResidual S X a v ≠ 0) :
    ∃ w : PrimeStar.Vertex S X,
      w ∈ PrimeStar.firstExitCompressionSupport S X
        (squareRootCutoff X) a ∧
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj v w := by
  classical
  rw [exactPrincipalMoleculeResidual_eq_exterior_smallPrime_interior hS ha] at hv
  have hvOut : v ∉ exactPrincipalMoleculeSupport S X a := by
    intro hvIn
    apply hv
    simp [PrimeStar.euclideanCoordinateComplementProjection_apply, hvIn]
  have hsmallNe :
      Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeInteriorVector S X a) v ≠ 0 := by
    simpa [PrimeStar.euclideanCoordinateComplementProjection_apply, hvOut]
      using hv
  rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply] at hsmallNe
  change Matrix.mulVec
      ((PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).adjMatrix ℝ)
      (fun w ↦ exactPrincipalMoleculeInteriorVector S X a w) v ≠ 0 at hsmallNe
  rw [SimpleGraph.adjMatrix_mulVec_apply] at hsmallNe
  by_contra hnone
  push Not at hnone
  apply hsmallNe
  apply Finset.sum_eq_zero
  intro w hw
  have hvw :
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj v w := by
    simpa using hw
  have hwOut : w ∉ PrimeStar.firstExitCompressionSupport S X
      (squareRootCutoff X) a := fun hwIn ↦ hnone w hwIn hvw
  simp [exactPrincipalMoleculeInteriorVector,
    PrimeStar.firstExitCompressionProjection_apply, hwOut]

/-- Two distinct positive centres with the same prime-labelled descendant
have the unique-factorization shape used by the coherent collision blocks:
`a = g * r`, `b = g * q`, and the common descendant is `g * r * q`.

This is the arithmetic classification behind the manuscript path
`g r -> g r q -> g q`; it does not estimate the resulting operator block. -/
theorem exists_commonCore_of_mul_prime_eq_mul_prime
    {a b q r : ℕ}
    (ha : 0 < a)
    (hq : q.Prime)
    (hr : r.Prime)
    (hab : a ≠ b)
    (h : a * q = b * r) :
    ∃ g : ℕ, 0 < g ∧ a = g * r ∧ b = g * q := by
  have hqr : q ≠ r := by
    intro hqr
    subst r
    exact hab (Nat.eq_of_mul_eq_mul_right hq.pos h)
  have hrDvd : r ∣ a * q := by
    refine ⟨b, ?_⟩
    calc
      a * q = b * r := h
      _ = r * b := Nat.mul_comm _ _
  have hrDvdA : r ∣ a := by
    rcases hr.dvd_mul.mp hrDvd with hra | hrq
    · exact hra
    · have : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
      exact False.elim (hqr this.symm)
  let g := a / r
  have hgr : g * r = a := Nat.div_mul_cancel hrDvdA
  have hg : 0 < g :=
    Nat.div_pos (Nat.le_of_dvd ha hrDvdA) hr.pos
  have hgb : g * q = b := by
    apply Nat.eq_of_mul_eq_mul_right hr.pos
    calc
      (g * q) * r = (g * r) * q := by ac_rfl
      _ = a * q := by rw [hgr]
      _ = b * r := h
  exact ⟨g, hg, hgr.symm, hgb.symm⟩

/-- The common core of a coherent source--output incidence is unique.

If two pairs of distinct prime labels represent the same ordered centres as
`a = g * r` and `b = g * q`, then both cores and both prime labels agree.
Thus a fixed matrix entry of the literal coherent block has at most one
common-core contribution; no divisor-multiplicity loss is needed when the
entries are aggregated by their actual source and output centres. -/
theorem commonCore_primeFactorization_unique
    {a b g₁ g₂ q₁ q₂ r₁ r₂ : ℕ}
    (hab : a ≠ b)
    (hg₁ : 0 < g₁)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hr₁ : r₁.Prime) (hr₂ : r₂.Prime)
    (ha₁ : a = g₁ * r₁) (hb₁ : b = g₁ * q₁)
    (ha₂ : a = g₂ * r₂) (hb₂ : b = g₂ * q₂) :
    g₁ = g₂ ∧ q₁ = q₂ ∧ r₁ = r₂ := by
  have hrq₁ : r₁ ≠ q₁ := by
    intro hrq
    apply hab
    rw [ha₁, hb₁, hrq]
  have hrq₂ : r₂ ≠ q₂ := by
    intro hrq
    apply hab
    rw [ha₂, hb₂, hrq]
  have hcoprime₁ : Nat.Coprime r₁ q₁ :=
    (Nat.coprime_primes hr₁ hq₁).2 hrq₁
  have hcoprime₂ : Nat.Coprime r₂ q₂ :=
    (Nat.coprime_primes hr₂ hq₂).2 hrq₂
  have hgcd₁ : Nat.gcd a b = g₁ := by
    rw [ha₁, hb₁, Nat.gcd_mul_left, hcoprime₁.gcd_eq_one, mul_one]
  have hgcd₂ : Nat.gcd a b = g₂ := by
    rw [ha₂, hb₂, Nat.gcd_mul_left, hcoprime₂.gcd_eq_one, mul_one]
  have hg : g₁ = g₂ := hgcd₁.symm.trans hgcd₂
  have hq : q₁ = q₂ := by
    apply Nat.eq_of_mul_eq_mul_left hg₁
    calc
      g₁ * q₁ = b := hb₁.symm
      _ = g₂ * q₂ := hb₂
      _ = g₁ * q₂ := by rw [hg]
  have hr : r₁ = r₂ := by
    apply Nat.eq_of_mul_eq_mul_left hg₁
    calc
      g₁ * r₁ = a := ha₁.symm
      _ = g₂ * r₂ := ha₂
      _ = g₁ * r₂ := by rw [hg]
  exact ⟨hg, hq, hr⟩

/-- Graph-level coherent-incidence classification.  If the small-prime
up-target `a*q` is also a large-prime leaf of a distinct retained centre
`b`, then the two centres and the leaf have the manuscript form

`g*r -> g*r*q = g*q*r <- g*q`.

The theorem retains the actual canonical up-target and large-prime leaf
predicates, so later collision sums can use it without replacing the graph by
an arithmetic surrogate. -/
theorem exists_commonCore_of_canonicalUpTarget_mem_largePrimeLeaves
    {S : Finset ℕ} {X Y : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (hb : (b : ℕ) ≤ Y)
    (q : PrimeStar.CanonicalUpIndex S X Y a)
    (hab : a ≠ b)
    (hmem : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.largePrimeLeaves S X Y b) :
    ∃ g r : ℕ, 0 < g ∧ r.Prime ∧ r ∉ S ∧ Y < r ∧
      (a : ℕ) = g * r ∧ (b : ℕ) = g * (q : ℕ) := by
  obtain ⟨r, hrPrime, hrS, hYr, hbr⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child hb).mp hmem
  have hqData := Finset.mem_filter.mp q.property
  have hqPrime : (q : ℕ).Prime :=
    (Nat.mem_primesLE.mp hqData.1).2
  have habCoe : (a : ℕ) ≠ (b : ℕ) := by
    intro hcoe
    apply hab
    apply Subtype.ext
    apply Fin.ext
    exact hcoe
  have heq : (a : ℕ) * (q : ℕ) = (b : ℕ) * r := by
    calc
      (a : ℕ) * (q : ℕ) =
          (PrimeStar.canonicalUpTarget hS a q : ℕ) :=
        (PrimeStar.canonicalUpTarget_coe hS a q).symm
      _ = (b : ℕ) * r := hbr.symm
  obtain ⟨g, hg, hag, hbg⟩ :=
    exists_commonCore_of_mul_prime_eq_mul_prime
      (PrimeStar.Vertex.coe_pos a) hqPrime hrPrime habCoe heq
  exact ⟨g, r, hg, hrPrime, hrS, hYr, hag, hbg⟩

/-- Two distinct retained centres whose canonical up-target stars coincide
have the common-core form used by the coherent internal collision block:

`a = g*r`, `b = g*q`, and `a*q = b*r = g*r*q`.

Unlike `exists_commonCore_of_canonicalUpTarget_mem_largePrimeLeaves`, this
is the literal incidence in manuscript Lemma 9.2: both small-prime labels
lead to the same first-exit target *centre*.  The prime, deletion, and cutoff
certificates are retained for the later core sum. -/
theorem exists_commonCore_of_canonicalUpTarget_eq
    {S : Finset ℕ} {X Y : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (q : PrimeStar.CanonicalUpIndex S X Y a)
    (r : PrimeStar.CanonicalUpIndex S X Y b)
    (hab : a ≠ b)
    (heq : PrimeStar.canonicalUpTarget hS a q =
      PrimeStar.canonicalUpTarget hS b r) :
    ∃ g : ℕ, 0 < g ∧
      (q : ℕ).Prime ∧ (r : ℕ).Prime ∧
      (q : ℕ) ∉ S ∧ (r : ℕ) ∉ S ∧
      (q : ℕ) ≤ Y ∧ (r : ℕ) ≤ Y ∧
      (a : ℕ) = g * (r : ℕ) ∧
      (b : ℕ) = g * (q : ℕ) := by
  have hqData := Finset.mem_filter.mp q.property
  have hrData := Finset.mem_filter.mp r.property
  have hqPrime : (q : ℕ).Prime :=
    (Nat.mem_primesLE.mp hqData.1).2
  have hrPrime : (r : ℕ).Prime :=
    (Nat.mem_primesLE.mp hrData.1).2
  have habCoe : (a : ℕ) ≠ (b : ℕ) := by
    intro hcoe
    apply hab
    apply Subtype.ext
    apply Fin.ext
    exact hcoe
  have hprod : (a : ℕ) * (q : ℕ) = (b : ℕ) * (r : ℕ) := by
    have hcoe := congrArg
      (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) heq
    simpa using hcoe
  obtain ⟨g, hg, hag, hbg⟩ :=
    exists_commonCore_of_mul_prime_eq_mul_prime
      (PrimeStar.Vertex.coe_pos a) hqPrime hrPrime habCoe hprod
  exact ⟨g, hg, hqPrime, hrPrime, hqData.2.1, hrData.2.1,
    (Nat.mem_primesLE.mp hqData.1).1,
    (Nat.mem_primesLE.mp hrData.1).1, hag, hbg⟩

/-- In a coherent common-core square, the output centre has only the two
advertised small-prime neighbours inside the union of the common target and
the core star.  A core leaf would introduce a large prime into a one-prime
step and is therefore impossible.  This is the centre-row exhaustiveness
needed by the actual T4b coefficient. -/
theorem smallPrimeNeighbor_eq_commonTarget_or_core_of_mem_commonCoreSupport
    {S : Finset ℕ} {X Y q r : ℕ}
    {g b target v : PrimeStar.Vertex S X}
    (hg : (g : ℕ) ≤ Y)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hr : r.Prime) (hrS : r ∉ S) (hrY : r ≤ Y)
    (hgb : (g : ℕ) * q = (b : ℕ))
    (hbt : (b : ℕ) * r = (target : ℕ))
    (hvSupport : v ∈ insert target
      (PrimeStar.largePrimeStarSupport S X Y g))
    (hAdj : (PrimeStar.smallPrimeGraph S X Y).Adj b v) :
    v = target ∨ v = g := by
  classical
  rcases Finset.mem_insert.mp hvSupport with rfl | hvCore
  · exact Or.inl rfl
  rw [PrimeStar.mem_largePrimeStarSupport] at hvCore
  rcases hvCore with rfl | hvLeafAdj
  · exact Or.inr rfl
  have hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y g :=
    PrimeStar.mem_largePrimeLeaves.mpr hvLeafAdj
  obtain ⟨p, hp, _hpS, hYp, hgp⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child hg).mp hvLeaf
  obtain ⟨ell, hell, _hellS, hellY, hEdge⟩ :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hAdj
  rcases hEdge with hbEll | hvEll
  · have hqell : q * ell = p := by
      apply Nat.eq_of_mul_eq_mul_left (PrimeStar.Vertex.coe_pos g)
      calc
        (g : ℕ) * (q * ell) = ((g : ℕ) * q) * ell := by ac_rfl
        _ = (b : ℕ) * ell := by rw [hgb]
        _ = (v : ℕ) := hbEll
        _ = (g : ℕ) * p := hgp.symm
    have hpDvd : p ∣ q * ell := ⟨1, by simpa [hqell]⟩
    rcases hp.dvd_mul.mp hpDvd with hpq | hpell
    · have hpEqQ : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      exact False.elim ((not_le_of_gt hYp) (hpEqQ ▸ hqY))
    · have hpEqEll : p = ell :=
        (Nat.prime_dvd_prime_iff_eq hp hell).mp hpell
      exact False.elim ((not_le_of_gt hYp) (hpEqEll ▸ hellY))
  · have hpell : p * ell = q := by
      apply Nat.eq_of_mul_eq_mul_left (PrimeStar.Vertex.coe_pos g)
      calc
        (g : ℕ) * (p * ell) = ((g : ℕ) * p) * ell := by ac_rfl
        _ = (v : ℕ) * ell := by rw [hgp]
        _ = (b : ℕ) := hvEll
        _ = (g : ℕ) * q := hgb.symm
    have hpLeQ : p ≤ q := by
      calc
        p ≤ p * ell := Nat.le_mul_of_pos_right p hell.pos
        _ = q := hpell
    exact False.elim ((not_le_of_gt hYp) (hpLeQ.trans hqY))

/-- For the ordered orientation `r ≤ q` of a coherent common-core square,
every leaf of the output star has a unique small-prime neighbour in the
chosen common-target/core-star support.  That neighbour is a selected leaf
of the source down-star at the common core.  The common target itself cannot
contribute to the leaf row, because it and the output leaf are two distinct
prime-step neighbours of the output centre. -/
theorem exists_unique_commonCoreLeafNeighbor_of_outputLeaf
    {S : Finset ℕ} {X Y q r : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    {g b target w : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hg : (g : ℕ) ≤ Y) (hb : (b : ℕ) ≤ Y)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hr : r.Prime) (hrS : r ∉ S) (hrY : r ≤ Y)
    (hrq : r ≤ q)
    (hgb : (g : ℕ) * q = (b : ℕ))
    (hbt : (b : ℕ) * r = (target : ℕ))
    (hw : w ∈ PrimeStar.largePrimeLeaves S X Y b) :
    ∃! v : PrimeStar.Vertex S X,
      v ∈ PrimeStar.canonicalDownLeaves S X Y g r ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj v w ∧
      ∀ u : PrimeStar.Vertex S X,
        u ∈ insert target (PrimeStar.largePrimeStarSupport S X Y g) →
        (PrimeStar.smallPrimeGraph S X Y).Adj u w → u = v := by
  classical
  obtain ⟨p, hp, hpS, hYp, hbp⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child hb).mp hw
  have hgpX : (g : ℕ) * p ≤ X := by
    calc
      (g : ℕ) * p ≤ ((g : ℕ) * p) * q :=
        Nat.le_mul_of_pos_right _ hq.pos
      _ = ((g : ℕ) * q) * p := by ac_rfl
      _ = (b : ℕ) * p := by rw [hgb]
      _ = (w : ℕ) := hbp
      _ ≤ X := PrimeStar.Vertex.coe_le w
  let v : PrimeStar.Vertex S X :=
    PrimeStar.vertexMulAllowedPrimeOfBound hS g p hp hpS hgpX
  have hvCoe : (v : ℕ) = (g : ℕ) * p :=
    PrimeStar.vertexMulAllowedPrimeOfBound_coe hS g p hp hpS hgpX
  have hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y g := by
    rw [PrimeStar.mem_largePrimeLeaves_iff_child hg]
    exact ⟨p, hp, hpS, hYp, hvCoe.symm⟩
  have hvrX : (v : ℕ) * r ≤ X := by
    calc
      (v : ℕ) * r ≤ (v : ℕ) * q := Nat.mul_le_mul_left _ hrq
      _ = ((g : ℕ) * p) * q := by rw [hvCoe]
      _ = ((g : ℕ) * q) * p := by ac_rfl
      _ = (b : ℕ) * p := by rw [hgb]
      _ = (w : ℕ) := hbp
      _ ≤ X := PrimeStar.Vertex.coe_le w
  have hvP : v ∈ PrimeStar.canonicalDownLeaves S X Y g r :=
    Finset.mem_filter.mpr ⟨hvLeaf, hvrX⟩
  have hvq : (v : ℕ) * q = (w : ℕ) := by
    calc
      (v : ℕ) * q = ((g : ℕ) * p) * q := by rw [hvCoe]
      _ = ((g : ℕ) * q) * p := by ac_rfl
      _ = (b : ℕ) * p := by rw [hgb]
      _ = (w : ℕ) := hbp
  have hvAdj : (PrimeStar.smallPrimeGraph S X Y).Adj v w :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨q, hq, hqS, hqY, Or.inl hvq⟩
  refine ⟨v, ⟨hvP, hvAdj, ?_⟩, ?_⟩
  · intro u huSupport huAdj
    rcases Finset.mem_insert.mp huSupport with rfl | huCore
    · obtain ⟨ell, hell, _hellS, _hellY, hEdge⟩ :=
        PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp huAdj
      exact False.elim (PrimeStar.no_prime_step_between_primeStepNeighbors
        (PrimeStar.Vertex.coe_pos b) (PrimeStar.Vertex.coe_pos u)
        (PrimeStar.Vertex.coe_pos w) hr hp hell
        (Or.inl hbt) (Or.inl hbp) hEdge)
    · exact PrimeStar.unique_smallPrime_neighbor_in_largePrimeStar
        hcut hg huCore
        (Finset.mem_insert_of_mem hvLeaf) huAdj hvAdj
  · intro u hu
    exact (hu.2.2 v (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem hvLeaf)) hvAdj).symm

/-- The same unique neighbour in the common-core support, without the
`r ≤ q` cutoff used only to keep `v * r` on the graph. -/
theorem exists_unique_commonCoreStarNeighbor_of_outputLeaf
    {S : Finset ℕ} {X Y q r : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    {g b target w : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hg : (g : ℕ) ≤ Y) (hb : (b : ℕ) ≤ Y)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hr : r.Prime) (hrS : r ∉ S) (hrY : r ≤ Y)
    (hgb : (g : ℕ) * q = (b : ℕ))
    (hbt : (b : ℕ) * r = (target : ℕ))
    (hw : w ∈ PrimeStar.largePrimeLeaves S X Y b) :
    ∃! v : PrimeStar.Vertex S X,
      v ∈ PrimeStar.largePrimeLeaves S X Y g ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj v w ∧
      ∀ u : PrimeStar.Vertex S X,
        u ∈ insert target (PrimeStar.largePrimeStarSupport S X Y g) →
        (PrimeStar.smallPrimeGraph S X Y).Adj u w → u = v := by
  classical
  obtain ⟨p, hp, hpS, hYp, hbp⟩ :=
    (PrimeStar.mem_largePrimeLeaves_iff_child hb).mp hw
  have hgpX : (g : ℕ) * p ≤ X := by
    calc
      (g : ℕ) * p ≤ ((g : ℕ) * p) * q :=
        Nat.le_mul_of_pos_right _ hq.pos
      _ = ((g : ℕ) * q) * p := by ac_rfl
      _ = (b : ℕ) * p := by rw [hgb]
      _ = (w : ℕ) := hbp
      _ ≤ X := PrimeStar.Vertex.coe_le w
  let v : PrimeStar.Vertex S X :=
    PrimeStar.vertexMulAllowedPrimeOfBound hS g p hp hpS hgpX
  have hvCoe : (v : ℕ) = (g : ℕ) * p :=
    PrimeStar.vertexMulAllowedPrimeOfBound_coe hS g p hp hpS hgpX
  have hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y g := by
    rw [PrimeStar.mem_largePrimeLeaves_iff_child hg]
    exact ⟨p, hp, hpS, hYp, hvCoe.symm⟩
  have hvq : (v : ℕ) * q = (w : ℕ) := by
    calc
      (v : ℕ) * q = ((g : ℕ) * p) * q := by rw [hvCoe]
      _ = ((g : ℕ) * q) * p := by ac_rfl
      _ = (b : ℕ) * p := by rw [hgb]
      _ = (w : ℕ) := hbp
  have hvAdj : (PrimeStar.smallPrimeGraph S X Y).Adj v w :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨q, hq, hqS, hqY, Or.inl hvq⟩
  refine ⟨v, ⟨hvLeaf, hvAdj, ?_⟩, ?_⟩
  · intro u huSupport huAdj
    rcases Finset.mem_insert.mp huSupport with rfl | huCore
    · obtain ⟨ell, hell, _hellS, _hellY, hEdge⟩ :=
        PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp huAdj
      exact False.elim (PrimeStar.no_prime_step_between_primeStepNeighbors
        (PrimeStar.Vertex.coe_pos b) (PrimeStar.Vertex.coe_pos u)
        (PrimeStar.Vertex.coe_pos w) hr hp hell
        (Or.inl hbt) (Or.inl hbp) hEdge)
    · exact PrimeStar.unique_smallPrime_neighbor_in_largePrimeStar
        hcut hg huCore
        (Finset.mem_insert_of_mem hvLeaf) huAdj hvAdj
  · intro u hu
    exact (hu.2.2 v (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem hvLeaf)) hvAdj).symm

/-- Applying the small-prime adjacency to a vector restricted to the common
target and core star gives exactly two terms at the output centre: the
inactive common target and the core centre. -/
theorem smallPrime_mulVec_restrict_commonCoreSupport_apply_outputCenter
    {S : Finset ℕ} {X Y q r : ℕ}
    {g b target : PrimeStar.Vertex S X}
    (hg : (g : ℕ) ≤ Y)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hr : r.Prime) (hrS : r ∉ S) (hrY : r ≤ Y)
    (hgb : (g : ℕ) * q = (b : ℕ))
    (hbt : (b : ℕ) * r = (target : ℕ))
    (x : EuclideanSpace ℝ (PrimeStar.Vertex S X)) :
    Matrix.mulVec ((PrimeStar.smallPrimeGraph S X Y).adjMatrix ℝ)
        (PrimeStar.restrictEuclideanToFinset
          (insert target (PrimeStar.largePrimeStarSupport S X Y g)) x) b =
      x target + x g := by
  classical
  let F := insert target (PrimeStar.largePrimeStarSupport S X Y g)
  have htargetAdj : (PrimeStar.smallPrimeGraph S X Y).Adj b target :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨r, hr, hrS, hrY, Or.inl hbt⟩
  have hgAdj : (PrimeStar.smallPrimeGraph S X Y).Adj b g :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨q, hq, hqS, hqY, Or.inr hgb⟩
  have htargetNeG : target ≠ g := by
    intro hEq
    have htargetCoe : (target : ℕ) = (g : ℕ) :=
      congrArg (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) hEq
    have hgqLt : (g : ℕ) < (g : ℕ) * q := by
      have := (Nat.mul_lt_mul_left (PrimeStar.Vertex.coe_pos g)).mpr hq.one_lt
      simpa using this
    have hbLt : (b : ℕ) < (b : ℕ) * r := by
      have := (Nat.mul_lt_mul_left (PrimeStar.Vertex.coe_pos b)).mpr hr.one_lt
      simpa using this
    have : (g : ℕ) < (target : ℕ) := by
      calc
        (g : ℕ) < (g : ℕ) * q := hgqLt
        _ = (b : ℕ) := hgb
        _ < (b : ℕ) * r := hbLt
        _ = (target : ℕ) := hbt
    exact (ne_of_lt this) htargetCoe.symm
  have hfilter :
      ((PrimeStar.smallPrimeGraph S X Y).neighborFinset b).filter
          (fun v ↦ v ∈ F) = {target, g} := by
    ext v
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      exact smallPrimeNeighbor_eq_commonTarget_or_core_of_mem_commonCoreSupport
        hg hq hqS hqY hr hrS hrY hgb hbt hv.2 hv.1
    · intro hv
      rcases hv with rfl | rfl
      · exact ⟨htargetAdj, Finset.mem_insert_self _ _⟩
      · exact ⟨hgAdj, Finset.mem_insert_of_mem
          (by simp [PrimeStar.largePrimeStarSupport])⟩
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  simp only [PrimeStar.restrictEuclideanToFinset_apply]
  rw [← Finset.sum_filter, hfilter]
  simp [htargetNeG]

/-- At an output leaf, the same restricted vector contributes exactly its
value at the unique selected core leaf.  The common target does not enter
this row. -/
theorem smallPrime_mulVec_restrict_commonCoreSupport_apply_outputLeaf
    {S : Finset ℕ} {X Y q r : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    {g b target w : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hg : (g : ℕ) ≤ Y) (hb : (b : ℕ) ≤ Y)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hr : r.Prime) (hrS : r ∉ S) (hrY : r ≤ Y)
    (hrq : r ≤ q)
    (hgb : (g : ℕ) * q = (b : ℕ))
    (hbt : (b : ℕ) * r = (target : ℕ))
    (hw : w ∈ PrimeStar.largePrimeLeaves S X Y b)
    (x : EuclideanSpace ℝ (PrimeStar.Vertex S X)) :
    ∃ v : PrimeStar.Vertex S X,
      v ∈ PrimeStar.canonicalDownLeaves S X Y g r ∧
      Matrix.mulVec ((PrimeStar.smallPrimeGraph S X Y).adjMatrix ℝ)
          (PrimeStar.restrictEuclideanToFinset
            (insert target (PrimeStar.largePrimeStarSupport S X Y g)) x) w =
        x v := by
  classical
  obtain ⟨v, hv, hvUnique⟩ :=
    exists_unique_commonCoreLeafNeighbor_of_outputLeaf
      hS hcut hg hb hq hqS hqY hr hrS hrY hrq hgb hbt hw
  refine ⟨v, hv.1, ?_⟩
  let F := insert target (PrimeStar.largePrimeStarSupport S X Y g)
  have hvSupport : v ∈ F := Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem
      (PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves g hv.1))
  have hvNeighbor : (PrimeStar.smallPrimeGraph S X Y).Adj w v :=
    (PrimeStar.smallPrimeGraph S X Y).adj_comm w v |>.mpr hv.2.1
  have hfilter :
      ((PrimeStar.smallPrimeGraph S X Y).neighborFinset w).filter
          (fun u ↦ u ∈ F) = {v} := by
    ext u
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_singleton]
    constructor
    · intro hu
      exact hv.2.2 u hu.2
        ((PrimeStar.smallPrimeGraph S X Y).adj_comm u w |>.mpr hu.1)
    · intro hu
      subst u
      exact ⟨hvNeighbor, hvSupport⟩
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  simp only [PrimeStar.restrictEuclideanToFinset_apply]
  rw [← Finset.sum_filter, hfilter]
  simp

theorem smallPrime_mulVec_restrict_commonCoreSupport_apply_outputLeaf_unoriented
    {S : Finset ℕ} {X Y q r : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    {g b target w : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hg : (g : ℕ) ≤ Y) (hb : (b : ℕ) ≤ Y)
    (hq : q.Prime) (hqS : q ∉ S) (hqY : q ≤ Y)
    (hr : r.Prime) (hrS : r ∉ S) (hrY : r ≤ Y)
    (hgb : (g : ℕ) * q = (b : ℕ))
    (hbt : (b : ℕ) * r = (target : ℕ))
    (hw : w ∈ PrimeStar.largePrimeLeaves S X Y b)
    (x : EuclideanSpace ℝ (PrimeStar.Vertex S X)) :
    ∃ v : PrimeStar.Vertex S X,
      v ∈ PrimeStar.largePrimeLeaves S X Y g ∧
      Matrix.mulVec ((PrimeStar.smallPrimeGraph S X Y).adjMatrix ℝ)
          (PrimeStar.restrictEuclideanToFinset
            (insert target (PrimeStar.largePrimeStarSupport S X Y g)) x) w =
        x v := by
  classical
  obtain ⟨v, hv, _hvUnique⟩ :=
    exists_unique_commonCoreStarNeighbor_of_outputLeaf
      hS hcut hg hb hq hqS hqY hr hrS hrY hgb hbt hw
  refine ⟨v, hv.1, ?_⟩
  let F := insert target (PrimeStar.largePrimeStarSupport S X Y g)
  have hvSupport : v ∈ F :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv.1)
  have hvNeighbor : (PrimeStar.smallPrimeGraph S X Y).Adj w v :=
    (PrimeStar.smallPrimeGraph S X Y).adj_comm w v |>.mpr hv.2.1
  have hfilter :
      ((PrimeStar.smallPrimeGraph S X Y).neighborFinset w).filter
          (fun u ↦ u ∈ F) = {v} := by
    ext u
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_singleton]
    constructor
    · intro hu
      exact hv.2.2 u hu.2
        ((PrimeStar.smallPrimeGraph S X Y).adj_comm u w |>.mpr hu.1)
    · intro hu
      subst u
      exact ⟨hvNeighbor, hvSupport⟩
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  simp only [PrimeStar.restrictEuclideanToFinset_apply]
  rw [← Finset.sum_filter, hfilter]
  simp

local instance signedStarCouplingSmallPrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

/-- A normalized signed star mode written as a literal centre/leaf data
vector. -/
theorem largePrimeNormalizedStarMode_eq_starDataVector
    {S : Finset ℕ} {X Y : ℕ} {a : PrimeStar.Vertex S X} {eps : ℝ}
    (heps : eps ^ 2 = 1)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a) :
    PrimeStar.largePrimeNormalizedStarMode S X Y a eps =
      PrimeStar.largePrimeStarDataVector S X Y a
        (PrimeStar.largePrimeNormalizedStarMode S X Y a eps a)
        (fun _ ↦
          PrimeStar.largePrimeNormalizedStarMode S X Y a eps a /
            (eps * Real.sqrt
              (PrimeStar.largePrimeStarDegree S X Y a : ℝ))) := by
  ext v
  by_cases hva : v = a
  · subst v
    simp
  · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X Y a
    · rw [PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
      exact largePrimeNormalizedStarMode_leaf_eq_center_div_signedEnergy
        heps hd hvleaf
    · have hvout : v ∉ PrimeStar.largePrimeStarSupport S X Y a := by
        simp [PrimeStar.largePrimeStarSupport, hva, hvleaf]
      rw [PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hvout,
        PrimeStar.largePrimeStarDataVector_outside _ _ hva hvleaf]

/-- Restricting an ambient vector to a star support does not change its inner
product against a mode supported on that star. -/
theorem real_inner_normalizedStarMode_restrict_starSupport
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    (eps : ℝ) (x : EuclideanSpace ℝ (PrimeStar.Vertex S X)) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X Y target eps, x⟫_ℝ =
      ⟪PrimeStar.largePrimeNormalizedStarMode S X Y target eps,
        PrimeStar.restrictEuclideanToFinset
          (PrimeStar.largePrimeStarSupport S X Y target) x⟫_ℝ := by
  classical
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hvs : v ∈ PrimeStar.largePrimeStarSupport S X Y target
  · rw [PrimeStar.restrictEuclideanToFinset_apply, if_pos hvs]
  · rw [PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hvs]
    simp

/-- Exact scalar recombination used by the coherent common-core projection.
The first parenthesis is the value sent to the output centre by the inactive
up-target and the down-target centre.  The second is the common value sent to
each output leaf, multiplied by the square root of the output degree.  After
recombination this is precisely manuscript formula (9.7a), with `tau` playing
the role of `sqrt t`.

In particular, the output ratio `tau` is never inverted.  The only
target-star inverse denominator is `z^2 - s`. -/
theorem coherentCommonCoreProjectionCoefficient_eq
    {z s mu alpha beta tau : ℝ}
    (hmu : mu ≠ 0) (hz : z ≠ 0) (hs : s ≠ 0)
    (hsep : z ^ 2 - s ≠ 0) :
    (Real.sqrt 2)⁻¹ *
          (alpha / (z * mu) +
            (z * alpha + beta) / (mu * (z ^ 2 - s))) +
        (mu * tau * (Real.sqrt 2)⁻¹) *
          (1 / mu ^ 2 *
            (beta / z +
              (z * alpha + beta) / (z * (z ^ 2 - s)))) =
      1 / (Real.sqrt 2 * mu) *
        (alpha / z +
          (z * alpha + beta) / (z ^ 2 - s) +
          tau *
            ((alpha + z * beta / s) / (z ^ 2 - s) +
              beta * (1 - 1 / s) / z)) := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hmu, hz, hs, hsep, hsqrt2]
  ring

/-- Uniform scalar majorant for the coherent common-core coefficient.

The hypotheses isolate exactly the four bounds later supplied on a fixed
sub-square-root power band: the molecule root ratio stays in `[1/2, 2]`, the
down-star ratio is at least one, its only resolvent denominator is separated
by `delta`, and the two signed source combinations have absolute value at
most two.  The conclusion is manuscript estimate (9.7) before substituting
`tau = mu_output / mu_source`. -/
theorem abs_coherentCommonCoreProjectionCoefficient_le
    {z s mu alpha beta tau delta : ℝ}
    (hmu : 0 < mu) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsLower : 1 ≤ s) (hsep : delta ≤ |z ^ 2 - s|)
    (halpha : |alpha| ≤ 2) (hbeta : |beta| ≤ 2) :
    |1 / (Real.sqrt 2 * mu) *
        (alpha / z +
          (z * alpha + beta) / (z ^ 2 - s) +
          tau *
            ((alpha + z * beta / s) / (z ^ 2 - s) +
              beta * (1 - 1 / s) / z))| ≤
      10 / delta * (1 / mu + |tau| / mu) := by
  have hsPos : 0 < s := lt_of_lt_of_le zero_lt_one hsLower
  have honeSub : |1 - 1 / s| ≤ 1 := by
    have hsInvNonneg : 0 ≤ 1 / s := le_of_lt (one_div_pos.mpr hsPos)
    have hsInvLe : 1 / s ≤ 1 := (div_le_one hsPos).2 hsLower
    rw [abs_of_nonneg (sub_nonneg.mpr hsInvLe)]
    linarith
  have hfirst : |alpha / z| ≤ 4 := by
    rw [abs_div]
    have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
      halpha (by norm_num : (0 : ℝ) < 1 / 2) hzLower
    norm_num at h
    exact h
  have hza : |z * alpha + beta| ≤ 6 := by
    calc
      |z * alpha + beta| ≤ |z * alpha| + |beta| := abs_add_le _ _
      _ = |z| * |alpha| + |beta| := by rw [abs_mul]
      _ ≤ 6 := by nlinarith [abs_nonneg z, abs_nonneg alpha, abs_nonneg beta]
  have hsecond : |(z * alpha + beta) / (z ^ 2 - s)| ≤ 6 / delta := by
    rw [abs_div]
    exact div_le_div₀ (by norm_num) hza hdelta hsep
  have hzb : |z * beta / s| ≤ 4 := by
    rw [abs_div, abs_mul, abs_of_pos hsPos]
    have hnum : |z| * |beta| ≤ 4 := by
      have hprod := mul_le_mul hzUpper hbeta (abs_nonneg beta)
        (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at hprod
      exact hprod
    have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 4)
      hnum (by norm_num : (0 : ℝ) < 1) hsLower
    simpa using h
  have hab : |alpha + z * beta / s| ≤ 6 := by
    calc
      |alpha + z * beta / s| ≤ |alpha| + |z * beta / s| := abs_add_le _ _
      _ ≤ 6 := by linarith
  have hthird : |(alpha + z * beta / s) / (z ^ 2 - s)| ≤ 6 / delta := by
    rw [abs_div]
    exact div_le_div₀ (by norm_num) hab hdelta hsep
  have hfourth : |beta * (1 - 1 / s) / z| ≤ 4 := by
    rw [abs_div, abs_mul]
    have hnum : |beta| * |1 - 1 / s| ≤ 2 := by
      nlinarith [mul_le_mul hbeta honeSub (abs_nonneg (1 - 1 / s))
        (by norm_num : (0 : ℝ) ≤ 2)]
    have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
      hnum (by norm_num : (0 : ℝ) < 1 / 2) hzLower
    norm_num at h
    simpa [one_div] using h
  have hbase :
      |alpha / z + (z * alpha + beta) / (z ^ 2 - s) +
        tau * ((alpha + z * beta / s) / (z ^ 2 - s) +
          beta * (1 - 1 / s) / z)| ≤
        10 / delta * (1 + |tau|) := by
    calc
      |alpha / z + (z * alpha + beta) / (z ^ 2 - s) +
          tau * ((alpha + z * beta / s) / (z ^ 2 - s) +
            beta * (1 - 1 / s) / z)| ≤
          |alpha / z| + |(z * alpha + beta) / (z ^ 2 - s)| +
            |tau| * (|(alpha + z * beta / s) / (z ^ 2 - s)| +
              |beta * (1 - 1 / s) / z|) := by
        calc
          |alpha / z + (z * alpha + beta) / (z ^ 2 - s) + tau *
              ((alpha + z * beta / s) / (z ^ 2 - s) +
                beta * (1 - 1 / s) / z)| ≤
              |alpha / z + (z * alpha + beta) / (z ^ 2 - s)| +
                |tau * ((alpha + z * beta / s) / (z ^ 2 - s) +
                  beta * (1 - 1 / s) / z)| := abs_add_le _ _
          _ ≤ (|alpha / z| + |(z * alpha + beta) / (z ^ 2 - s)|) +
                |tau| * (|(alpha + z * beta / s) / (z ^ 2 - s)| +
                  |beta * (1 - 1 / s) / z|) := by
            rw [abs_mul]
            exact add_le_add (abs_add_le _ _)
              (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg tau))
      _ ≤ 4 + 6 / delta + |tau| * (6 / delta + 4) := by
        exact add_le_add (add_le_add hfirst hsecond)
          (mul_le_mul_of_nonneg_left (add_le_add hthird hfourth)
            (abs_nonneg tau))
      _ ≤ 10 / delta * (1 + |tau|) := by
        have hdeltaInv : 1 ≤ 1 / delta := by
          rw [le_div_iff₀ hdelta]
          simpa using hdeltaOne
        have hfour : (4 : ℝ) ≤ 4 * (1 / delta) := by nlinarith
        have hleft : 4 + 6 / delta ≤ 10 / delta := by
          calc
            4 + 6 / delta ≤ 4 * (1 / delta) + 6 / delta := by linarith
            _ = 10 / delta := by ring
        have hright : 6 / delta + 4 ≤ 10 / delta := by
          calc
            6 / delta + 4 ≤ 6 / delta + 4 * (1 / delta) := by linarith
            _ = 10 / delta := by ring
        calc
          4 + 6 / delta + |tau| * (6 / delta + 4) ≤
              10 / delta + |tau| * (10 / delta) := by
            exact add_le_add hleft
              (mul_le_mul_of_nonneg_left hright (abs_nonneg tau))
          _ = 10 / delta * (1 + |tau|) := by ring
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsqrtMu : 0 < Real.sqrt 2 * mu :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) hmu
  rw [abs_mul]
  have hprefactor : |1 / (Real.sqrt 2 * mu)| ≤ 1 / mu := by
    rw [abs_of_pos (one_div_pos.mpr hsqrtMu)]
    apply div_le_div_of_nonneg_left (by norm_num) hmu
    nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hmu.le]
  calc
    |1 / (Real.sqrt 2 * mu)| *
        |alpha / z + (z * alpha + beta) / (z ^ 2 - s) +
          tau * ((alpha + z * beta / s) / (z ^ 2 - s) +
            beta * (1 - 1 / s) / z)| ≤
        (1 / mu) * (10 / delta * (1 + |tau|)) := by gcongr
    _ = 10 / delta * (1 / mu + |tau| / mu) := by ring

/-! ## Raw coherent/noncoherent compression split

Canonical frame normalization mixes molecule coordinates, so the common-core
mask is applied to the raw compression residual `Vᴴ J` before normalization.
-/

/-- Two distinct exact molecules form a raw coherent pair when one canonical
small-prime up-target of each source is the same isolated first-exit centre.
This is the global, pre-normalization form of the manuscript Ferrers path

`g*r -> g*r*q = g*q*r <- g*q`.

The strict cutoff condition is load-bearing: a shared target below the cutoff
carries a nontrivial target-star resolvent and belongs to the complementary
weighted row estimate.  There is still no terminal-buffer condition here,
because normalization is performed on the whole retained prefix. -/
def IsCoherentRawMoleculePair
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a b : MoleculeCenter S X K) : Prop :=
  a ≠ b ∧
    ∃ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a.1,
      ∃ r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) b.1,
        PrimeStar.canonicalUpTarget hS a.1 q =
          PrimeStar.canonicalUpTarget hS b.1 r ∧
        squareRootCutoff X <
          (PrimeStar.canonicalUpTarget hS a.1 q : ℕ)

/-- Raw coherent incidence is symmetric in the two molecule centres. -/
theorem isCoherentRawMoleculePair_comm
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a b : MoleculeCenter S X K) :
    IsCoherentRawMoleculePair hS a b ↔
      IsCoherentRawMoleculePair hS b a := by
  constructor
  · rintro ⟨hab, q, r, hqr, hcut⟩
    exact ⟨hab.symm, r, q, hqr.symm, by simpa [hqr] using hcut⟩
  · rintro ⟨hba, r, q, hrq, hcut⟩
    exact ⟨hba.symm, q, r, hrq.symm, by simpa [hrq] using hcut⟩

/-- Every raw coherent pair has the unique-factorization common-core form.
This is the arithmetic classification consumed by the later core summation;
it does not assert a norm estimate. -/
theorem exists_commonCore_of_isCoherentRawMoleculePair
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : MoleculeCenter S X K}
    (hab : IsCoherentRawMoleculePair hS a b) :
    ∃ g : ℕ, 0 < g ∧
      ∃ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a.1,
        ∃ r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) b.1,
          (q : ℕ).Prime ∧ (r : ℕ).Prime ∧
          (q : ℕ) ∉ S ∧ (r : ℕ) ∉ S ∧
          (q : ℕ) ≤ squareRootCutoff X ∧
          (r : ℕ) ≤ squareRootCutoff X ∧
          (a.1 : ℕ) = g * (r : ℕ) ∧
          (b.1 : ℕ) = g * (q : ℕ) ∧
          squareRootCutoff X <
            (PrimeStar.canonicalUpTarget hS a.1 q : ℕ) := by
  rcases hab with ⟨hne, q, r, htarget, hcut⟩
  have hne' : a.1 ≠ b.1 := by
    intro h
    exact hne (Subtype.ext h)
  obtain ⟨g, hg, hq, hr, hqS, hrS, hqY, hrY, ha, hb⟩ :=
    exists_commonCore_of_canonicalUpTarget_eq hS q r hne' htarget
  exact ⟨g, hg, q, r, hq, hr, hqS, hrS, hqY, hrY, ha, hb, hcut⟩

/-- The common target in the corrected coherent mask is a literal isolated
first-exit coordinate for the first source. -/
theorem coherentRawMoleculePair_commonTarget_mem_isolated
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : MoleculeCenter S X K}
    (ha : (a.1 : ℕ) ≤ squareRootCutoff X)
    (hab : IsCoherentRawMoleculePair hS a b) :
    ∃ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a.1,
      ∃ r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) b.1,
        PrimeStar.canonicalUpTarget hS a.1 q =
            PrimeStar.canonicalUpTarget hS b.1 r ∧
          PrimeStar.canonicalUpTarget hS a.1 q ∈
            PrimeStar.firstExitIsolatedVertices S X
              (squareRootCutoff X) a.1 := by
  rcases hab with ⟨_hne, q, r, htarget, hcut⟩
  refine ⟨q, r, htarget, ?_⟩
  apply PrimeStar.mem_firstExitIsolatedVertices.mpr
  constructor
  · simpa [PrimeStar.canonicalExitTarget] using
      (PrimeStar.canonicalExitTarget_mem_smallPrimeFirstExitSupport
        (Y := squareRootCutoff X) hS ha
        (Sum.inl q : PrimeStar.CanonicalExitIndex S X
          (squareRootCutoff X) a.1))
  · have hqData := Finset.mem_filter.mp q.property
    exact PrimeStar.canonicalUpTarget_isIsolated_of_cutoff_lt
      ha (PrimeStar.sqrtCutoff_condition X)
      (Nat.mem_primesLE.mp hqData.1).2
      (Nat.mem_primesLE.mp hqData.1).1
      (PrimeStar.canonicalUpTarget_coe hS a.1 q) hcut

/-- Distinct prime siblings of one positive common core cannot themselves
be a selected one-step lower centre of each other. -/
theorem not_mem_firstExitLowerCenters_of_primeSibling
    {S : Finset ℕ} {X Y g q r : ℕ}
    {a b : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (haY : (a : ℕ) ≤ Y)
    (hg : 0 < g) (hq : q.Prime) (hr : r.Prime)
    (ha : (a : ℕ) = g * r) (hb : (b : ℕ) = g * q) :
    b ∉ PrimeStar.firstExitLowerCenters S X Y a := by
  intro hbLower
  obtain ⟨ell, hell, _hellS, _hellY, hab⟩ :=
    PrimeStar.mem_firstExitLowerCenters_arithmetic hcut haY hbLower
  exact PrimeStar.no_prime_step_between_primeStepNeighbors
    hg (PrimeStar.Vertex.coe_pos a) (PrimeStar.Vertex.coe_pos b)
    hr hq hell (Or.inl ha.symm) (Or.inl hb.symm) hab

/-- For a coherent common-core pair, the output boundary star is disjoint
from the complete exact molecule support of the source.

The common descendant is an isolated small-prime target, not a large-prime
leaf of the output star.  Every non-isolated first-exit block of the source
has a prime-step centre; the prime-sibling lemma excludes the output centre,
and disjointness of the large-prime star forest excludes all remaining
blocks. -/
theorem disjoint_outputStar_exactPrincipalMoleculeSupport_of_coherentRawPair
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : MoleculeCenter S X K}
    (haY : (a.1 : ℕ) ≤ squareRootCutoff X)
    (hbY : (b.1 : ℕ) ≤ squareRootCutoff X)
    (hdb : 0 < PrimeStar.largePrimeStarDegree S X
      (squareRootCutoff X) b.1)
    (hab : IsCoherentRawMoleculePair hS a b) :
    Disjoint
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) b.1)
      (exactPrincipalMoleculeSupport S X a.1) := by
  classical
  obtain ⟨g, hg, q, r, hq, hr, _hqS, _hrS, _hqY, _hrY,
      ha, hb, _hcommonCut⟩ :=
    exists_commonCore_of_isCoherentRawMoleculePair hS hab
  have habCenter : a.1 ≠ b.1 := by
    intro h
    exact hab.1 (Subtype.ext h)
  have hbNotLower : b.1 ∉ PrimeStar.firstExitLowerCenters S X
      (squareRootCutoff X) a.1 :=
    not_mem_firstExitLowerCenters_of_primeSibling
      (PrimeStar.sqrtCutoff_condition X) haY hg hq hr ha hb
  rw [Finset.disjoint_left]
  intro v hvb hva
  rw [exactPrincipalMoleculeSupport] at hva
  rcases Finset.mem_union.mp hva with hvaBoundary | hvaExit
  · exact (Finset.disjoint_left.mp
      (PrimeStar.disjoint_largePrimeStarSupport
        (PrimeStar.sqrtCutoff_condition X) hbY haY habCenter.symm))
      hvb hvaBoundary
  · rcases Finset.mem_union.mp hvaExit with hvaStars | hvaIsolated
    · obtain ⟨k, hk, hvk⟩ :=
        PrimeStar.mem_largePrimeStarUnionSupport.mp hvaStars
      by_cases hkb : k = b.1
      · subst k
        exact hbNotLower hk
      · exact (Finset.disjoint_left.mp
          (PrimeStar.disjoint_largePrimeStarSupport
            (PrimeStar.sqrtCutoff_condition X) hbY
            (PrimeStar.mem_firstExitLowerCenters.mp hk).1 (Ne.symm hkb))) hvb hvk
    · have hvIsolated :=
        (PrimeStar.mem_firstExitIsolatedVertices.mp hvaIsolated).2
      rw [PrimeStar.mem_largePrimeStarSupport] at hvb
      rcases hvb with rfl | hvbLeaf
      · have hnonempty :
            (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) b.1).Nonempty :=
          Finset.card_pos.mp (by
            simpa [PrimeStar.largePrimeStarDegree] using hdb)
        exact hvIsolated hnonempty.choose
          (PrimeStar.mem_largePrimeLeaves.mp hnonempty.choose_spec)
      · exact hvIsolated b.1 (PrimeStar.largePrimeAdj_symm hvbLeaf)

/-- Locally supported compression residual `Vᴴ J` before the one-exit
projection is applied.

Both factors have the graph-local support dictionaries used by the
bounded-word collision enumeration.  In particular, the coherent mask must
be applied here, not to the projected residual. -/
def exactOneExitLocalCompressionResidual
    (S : Finset ℕ) (X K : ℕ) :
    Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
  (exactMoleculeFamilyComplexFrame S X K)ᴴ *
    exactMoleculeFamilyComplexResidual S X K

/-- Entrywise form of the locally supported compression residual `Vᴴ J`. -/
theorem exactOneExitLocalCompressionResidual_apply
    (S : Finset ℕ) (X K : ℕ)
    (a b : MoleculeCenter S X K) :
    exactOneExitLocalCompressionResidual S X K a b =
      ∑ v : PrimeStar.Vertex S X,
        starRingEnd ℂ (exactMoleculeFamilyComplexFrame S X K v a) *
          exactMoleculeFamilyComplexResidual S X K v b := by
  simp [exactOneExitLocalCompressionResidual, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- The graph-local compression entry is the scalar extension of the
literal real pairing between one exact molecule and the residual of the
other.  This is the bridge from the matrix endpoint to the signed-boundary
and kernel-branch decompositions, which are stated over the real molecule
ambient space. -/
theorem exactOneExitLocalCompressionResidual_eq_real_inner
    (S : Finset ℕ) (X K : ℕ)
    (a b : MoleculeCenter S X K) :
    exactOneExitLocalCompressionResidual S X K a b =
      ((inner ℝ (exactPrincipalMoleculeAmbientVector S X a.1)
        (exactPrincipalMoleculeResidual S X b.1) : ℝ) : ℂ) := by
  rw [exactOneExitLocalCompressionResidual_apply]
  simp only [exactMoleculeFamilyComplexFrame,
    exactMoleculeFamilyComplexResidual, complexifyRealMatrix_apply,
    exactMoleculeFamilyFrameMatrix]
  have hres : ∀ v : PrimeStar.Vertex S X,
      exactMoleculeFamilyResidualMatrix S X K v b =
        exactPrincipalMoleculeResidual S X b.1 v := by
    intro v
    have h := congrFun (exactMoleculeFamilyResidualMatrix_col S X K b) v
    exact h
  simp_rw [hres]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Exact three-branch decomposition of one graph-local compression entry.

The coherent coefficient theorem prices the signed-boundary part after one
small-prime return.  The remaining two displayed pairings are precisely the
signed-interior and kernel bounded-word remainders; they cannot be absorbed
silently into the positive-star coefficient. -/
theorem exactOneExitLocalCompressionResidual_eq_branch_inner
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a b : MoleculeCenter S X K)
    (ha : (a.1 : ℕ) ≤ squareRootCutoff X)
    (hroot : exactPrincipalMoleculeRoot S X a.1 ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a.1 • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a.1 x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) a.1,
      exactPrincipalMoleculeRoot S X a.1 ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) k : ℝ)) :
    exactOneExitLocalCompressionResidual S X K a b =
      ((inner ℝ (exactPrincipalMoleculeSignedBoundaryVector S X a.1)
          (exactPrincipalMoleculeResidual S X b.1) +
        inner ℝ (exactPrincipalMoleculeSignedInteriorVector S X a.1)
          (exactPrincipalMoleculeResidual S X b.1) +
        inner ℝ (exactPrincipalMoleculeKernelBranch S X a.1)
          (exactPrincipalMoleculeResidual S X b.1) : ℝ) : ℂ) := by
  rw [exactOneExitLocalCompressionResidual_eq_real_inner]
  rw [exactPrincipalMoleculeAmbientVector_eq_charged_add_kernelBranch
    hS ha hroot gamma hgamma hgap hden]
  simp only [exactPrincipalMoleculeChargedBranch, inner_add_left]

theorem inner_signedBoundary_residual_eq_modes
    {S : Finset ℕ} {X : ℕ}
    {a b : PrimeStar.Vertex S X}
    (hda : 0 < PrimeStar.largePrimeStarDegree S X
      (squareRootCutoff X) a) :
    inner ℝ (exactPrincipalMoleculeSignedBoundaryVector S X a)
        (exactPrincipalMoleculeResidual S X b) =
      exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 *
          inner ℝ
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a 1)
            (exactPrincipalMoleculeResidual S X b) +
        exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1) *
          inner ℝ
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) a (-1))
            (exactPrincipalMoleculeResidual S X b) := by
  rw [exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hda]
  simp only [inner_add_left, real_inner_smul_left]

/-- Restriction of the locally supported compression residual to
source/output pairs admitting a common-core incidence.

The pair mask does not claim a pathwise decomposition inside one scalar
entry; it merely separates entries that can carry the coherent common-core
family. -/
noncomputable def exactOneExitLocalCoherentCompressionResidual
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
  fun a b ↦
    if IsCoherentRawMoleculePair hS a b then
      exactOneExitLocalCompressionResidual S X K a b
    else 0

/-! ## Actual coherent common-core coefficient -/

/-- A signed output-star mode sees the exact source residual as one literal
small-prime step from the source interior whenever the output star is
disjoint from the source molecule support.

This removes the exterior coordinate projection from the pairing without a
norm loss.  The remaining coherent proof therefore has a purely arithmetic
support obligation: establish this disjointness for the oriented common-core
pair, then split the source interior into its common-core response and the
bounded-word remainder. -/
theorem real_inner_signedStarMode_exactPrincipalMoleculeResidual_eq_smallPrime_interior_of_disjoint
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : PrimeStar.Vertex S X}
    (hsource : (source : ℕ) ≤ squareRootCutoff X)
    {eps : ℝ}
    (hdisjoint : Disjoint
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) output)
      (exactPrincipalMoleculeSupport S X source)) :
    inner ℝ
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) output eps)
        (exactPrincipalMoleculeResidual S X source) =
      inner ℝ
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) output eps)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeInteriorVector S X source)) := by
  let F := exactPrincipalMoleculeSupport S X source
  let u := PrimeStar.largePrimeNormalizedStarMode S X
    (squareRootCutoff X) output eps
  let y := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
    (exactPrincipalMoleculeInteriorVector S X source)
  have hprojection :
      PrimeStar.euclideanCoordinateComplementProjection F u = u := by
    ext v
    rw [PrimeStar.euclideanCoordinateComplementProjection_apply]
    by_cases hvF : v ∈ F
    · rw [if_pos hvF]
      have hvStar : v ∉ PrimeStar.largePrimeStarSupport S X
          (squareRootCutoff X) output := by
        intro hv
        exact (Finset.disjoint_left.mp hdisjoint) hv hvF
      exact (PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem
        hvStar).symm
    · rw [if_neg hvF]
  have hsymm :=
    PrimeStar.euclideanCoordinateComplementProjection_isSymmetric F
  rw [exactPrincipalMoleculeResidual_eq_exterior_smallPrime_interior
    hS hsource]
  change inner ℝ u
      (PrimeStar.euclideanCoordinateComplementProjection F y) = inner ℝ u y
  calc
    inner ℝ u (PrimeStar.euclideanCoordinateComplementProjection F y) =
        inner ℝ (PrimeStar.euclideanCoordinateComplementProjection F u) y :=
      (hsymm u y).symm
    _ = inner ℝ u y := by rw [hprojection]

/-- On an actual coherent raw pair, a signed output-star mode sees the full
source residual through exactly one small-prime step from the source interior.

The arithmetic coherent mask supplies the disjointness needed by the preceding
projection lemma, so this statement has no auxiliary support hypothesis.  It
is the graph-local bridge from the matrix entry to the signed common-core
response used in the manuscript coefficient calculation. -/
theorem real_inner_signedStarMode_exactPrincipalMoleculeResidual_eq_smallPrime_interior_of_coherentRawPair
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hdoutput : 0 < PrimeStar.largePrimeStarDegree S X
      (squareRootCutoff X) output.1)
    (hcoherent : IsCoherentRawMoleculePair hS source output)
    {eps : ℝ} :
    inner ℝ
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) output.1 eps)
        (exactPrincipalMoleculeResidual S X source.1) =
      inner ℝ
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) output.1 eps)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeInteriorVector S X source.1)) := by
  exact
    real_inner_signedStarMode_exactPrincipalMoleculeResidual_eq_smallPrime_interior_of_disjoint
      hS hsource
        (disjoint_outputStar_exactPrincipalMoleculeSupport_of_coherentRawPair
          hS hsource houtput hdoutput hcoherent)

/-! The next declarations are the minimal local resolvent API needed by the
coherent common-core entry. They are extracted from the historical
`BoundaryTargetResolvent` and `ExactBoundarySignedResponse` modules so this
owner does not import their unrelated eigenvector and feedback cone. -/

theorem shiftedActualDownStarResolvent_apply_center
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {lambda mu c0 : ℝ}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target) :
    shiftedActualDownStarResolvent S X Y target P lambda mu c0 target =
      (lambda * c0 + (P.card : ℝ) * (c0 / mu)) /
        (lambda ^ 2 -
          (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) := by
  classical
  let source := PrimeStar.actualDownStarFirstExit S X Y target P mu c0
  have hsourceCenter : source target = c0 := by
    simp [source, PrimeStar.actualDownStarFirstExit]
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
    PrimeStar.largePrimeStarDataVector_center,
    hsourceCenter, hsumSource]

theorem shiftedActualDownStarResolvent_apply_center_normalized
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {z s mu c0 eps : ℝ}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hdegree : (PrimeStar.largePrimeStarDegree S X Y target : ℝ) =
      s * mu ^ 2)
    (heps : eps ^ 2 = 1) (hmu : mu ≠ 0)
    (hsep : z ^ 2 - s ≠ 0) :
    shiftedActualDownStarResolvent S X Y target P
        (z * mu) (eps * mu) c0 target =
      c0 / mu * ((z + eps) / (z ^ 2 - s)) := by
  rw [shiftedActualDownStarResolvent_apply_center hP, hcard, hdegree]
  have heps0 : eps ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at heps
    norm_num at heps
  field_simp [hmu, heps0, hsep]
  ring_nf at heps ⊢
  rw [heps]
  ring

theorem shiftedActualDownStarResolvent_apply_mem_normalized
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {z s mu c0 eps : ℝ}
    {v : PrimeStar.Vertex S X}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target)
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y target)
    (hvP : v ∈ P)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hdegree : (PrimeStar.largePrimeStarDegree S X Y target : ℝ) =
      s * mu ^ 2)
    (heps : eps ^ 2 = 1) (hmu : mu ≠ 0) (hz : z ≠ 0)
    (hsep : z ^ 2 - s ≠ 0) :
    shiftedActualDownStarResolvent S X Y target P
        (z * mu) (eps * mu) c0 v =
      c0 / mu ^ 2 *
        (eps / z + (z + eps) / (z * (z ^ 2 - s))) := by
  rw [shiftedActualDownStarResolvent_apply_mem hP hvLeaf hvP,
    hcard, hdegree]
  have heps0 : eps ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at heps
    norm_num at heps
  field_simp [hmu, hz, heps0, hsep]
  ring_nf at heps ⊢
  rw [heps]
  ring

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

theorem restrict_exactBoundaryModeInteriorVector_eq_canonicalDownResolvent
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} {eps : ℝ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (heps : eps ^ 2 = 1)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (q : PrimeStar.CanonicalDownIndex a) :
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q))
        (exactBoundaryModeInteriorVector S X a eps) =
      shiftedActualDownStarResolvent S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q)
        (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) q)
        (exactPrincipalMoleculeRoot S X a)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a) := by
  rw [exactBoundaryModeInteriorVector]
  calc
    PrimeStar.restrictEuclideanToFinset
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q))
        (PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X) a
          (exactPrincipalMoleculeRoot S X a)
          (exactBoundaryModeInteriorSource S X a eps)) =
      PrimeStar.largePrimeStarResolventOfVector S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q)
        (exactPrincipalMoleculeRoot S X a)
        (PrimeStar.restrictEuclideanToFinset
          (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q))
          (exactBoundaryModeInteriorSource S X a eps)) := by
            simpa only [PrimeStar.canonicalExitTarget_inr] using
              (restrict_firstExitStarResolventVector_eq_canonicalLocal
                (S := S) (X := X) (Y := squareRootCutoff X)
                hS (PrimeStar.sqrtCutoff_condition X) ha hroot
                (exactBoundaryModeInteriorSource S X a eps)
                (Sum.inr q : PrimeStar.CanonicalExitIndex S X
                  (squareRootCutoff X) a))
    _ = shiftedActualDownStarResolvent S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q)
        (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) q)
        (exactPrincipalMoleculeRoot S X a)
        (eps * moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a) := by
            rw [restrict_exactBoundaryModeInteriorSource_eq_canonicalDownStar
              hS ha hd heps q]
            rfl

theorem exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownTarget
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a)
    {z s : ℝ}
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegree :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hz : z ≠ 0) (hsep : z ^ 2 - s ≠ 0) :
    exactPrincipalMoleculeSignedInteriorVector S X a
        (PrimeStar.canonicalDownTarget a q) =
      (z * (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
              exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) +
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
              exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))) /
        (moleculeStarEnergy S X a * (z ^ 2 - s)) := by
  let target := PrimeStar.canonicalDownTarget a q
  let P := PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) target q
  let mu := moleculeStarEnergy S X a
  have hmu : mu ≠ 0 := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hroot : exactPrincipalMoleculeRoot S X a ≠ 0 := by
    rw [hrootEq]
    exact mul_ne_zero hz hmu
  have hP : P ⊆ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target :=
    PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves target
  have hcard : (P.card : ℝ) = mu ^ 2 := by
    calc
      (P.card : ℝ) =
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) := by
            exact_mod_cast
              PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
      _ = mu ^ 2 := by
        simpa [mu] using (moleculeStarEnergy_sq S X a).symm
  have hmode (eps : ℝ) (heps : eps ^ 2 = 1) :
      exactBoundaryModeInteriorVector S X a eps target =
        shiftedActualDownStarResolvent S X (squareRootCutoff X) target P
          (z * mu) (eps * mu) (Real.sqrt 2)⁻¹ target := by
    have hrestrict := congrArg (fun x : MoleculeAmbient S X ↦ x target)
      (restrict_exactBoundaryModeInteriorVector_eq_canonicalDownResolvent
        hS ha hd heps hroot q)
    rw [PrimeStar.restrictEuclideanToFinset_apply,
      if_pos (by simp [target, PrimeStar.largePrimeStarSupport])]
      at hrestrict
    rw [hrootEq,
      largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd]
      at hrestrict
    exact hrestrict
  have hp := shiftedActualDownStarResolvent_apply_center_normalized
    (target := target) (P := P) (z := z) (s := s) (mu := mu)
    (c0 := (Real.sqrt 2)⁻¹) (eps := (1 : ℝ))
    hP hcard (by simpa [target, mu] using hdegree)
      (by norm_num) hmu hsep
  have hm := shiftedActualDownStarResolvent_apply_center_normalized
    (target := target) (P := P) (z := z) (s := s) (mu := mu)
    (c0 := (Real.sqrt 2)⁻¹) (eps := (-1 : ℝ))
    hP hcard (by simpa [target, mu] using hdegree)
      (by norm_num) hmu hsep
  rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hmode 1 (by norm_num), hmode (-1) (by norm_num), hp, hm]
  unfold exactPrincipalMoleculeBoundarySourceAmplitude
  dsimp [mu]
  have hsqrt2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hmu, hsep, hsqrt2]
  ring

theorem exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a)
    {v : PrimeStar.Vertex S X}
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q))
    (hvP : v ∈ PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q) q)
    {z s : ℝ}
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegree :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hz : z ≠ 0) (hsep : z ^ 2 - s ≠ 0) :
    exactPrincipalMoleculeSignedInteriorVector S X a v =
      1 / moleculeStarEnergy S X a ^ 2 *
        ((exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
              exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) / z +
          (z * (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
                  exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) +
              (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
                  exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))) /
            (z * (z ^ 2 - s))) := by
  let target := PrimeStar.canonicalDownTarget a q
  let P := PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) target q
  let mu := moleculeStarEnergy S X a
  have hmu : mu ≠ 0 := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hroot : exactPrincipalMoleculeRoot S X a ≠ 0 := by
    rw [hrootEq]
    exact mul_ne_zero hz hmu
  have hP : P ⊆ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target :=
    PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves target
  have hcard : (P.card : ℝ) = mu ^ 2 := by
    calc
      (P.card : ℝ) =
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) := by
            exact_mod_cast
              PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
      _ = mu ^ 2 := by
        simpa [mu] using (moleculeStarEnergy_sq S X a).symm
  have hmode (eps : ℝ) (heps : eps ^ 2 = 1) :
      exactBoundaryModeInteriorVector S X a eps v =
        shiftedActualDownStarResolvent S X (squareRootCutoff X) target P
          (z * mu) (eps * mu) (Real.sqrt 2)⁻¹ v := by
    have hrestrict := congrArg (fun x : MoleculeAmbient S X ↦ x v)
      (restrict_exactBoundaryModeInteriorVector_eq_canonicalDownResolvent
        hS ha hd heps hroot q)
    rw [PrimeStar.restrictEuclideanToFinset_apply,
      if_pos (PrimeStar.mem_largePrimeStarSupport.mpr
        (Or.inr (PrimeStar.mem_largePrimeLeaves.mp
          (by simpa [target] using hvLeaf))))]
      at hrestrict
    rw [hrootEq,
      largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd]
      at hrestrict
    exact hrestrict
  have hp := shiftedActualDownStarResolvent_apply_mem_normalized
    (target := target) (P := P) (z := z) (s := s) (mu := mu)
    (c0 := (Real.sqrt 2)⁻¹) (eps := (1 : ℝ)) (v := v)
    hP (by simpa [target] using hvLeaf) (by simpa [P, target] using hvP)
      hcard (by simpa [target, mu] using hdegree)
      (by norm_num) hmu hz hsep
  have hm := shiftedActualDownStarResolvent_apply_mem_normalized
    (target := target) (P := P) (z := z) (s := s) (mu := mu)
    (c0 := (Real.sqrt 2)⁻¹) (eps := (-1 : ℝ)) (v := v)
    hP (by simpa [target] using hvLeaf) (by simpa [P, target] using hvP)
      hcard (by simpa [target, mu] using hdegree)
      (by norm_num) hmu hz hsep
  rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hmode 1 (by norm_num), hmode (-1) (by norm_num), hp, hm]
  unfold exactPrincipalMoleculeBoundarySourceAmplitude
  dsimp [mu]
  have hsqrt2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hmu, hz, hsep, hsqrt2]
  ring

theorem exactPrincipalMoleculeSignedInteriorVector_apply_isolatedCanonicalUpTarget
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (hiso : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.firstExitIsolatedVertices S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0) :
    exactPrincipalMoleculeSignedInteriorVector S X a
        (PrimeStar.canonicalUpTarget hS a q) =
      (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
          exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) /
        exactPrincipalMoleculeRoot S X a := by
  let target := PrimeStar.canonicalUpTarget hS a q
  have hqData := Finset.mem_filter.mp q.property
  have hqPrime : (q : ℕ).Prime :=
    (Nat.mem_primesLE.mp hqData.1).2
  have hqY : (q : ℕ) ≤ squareRootCutoff X :=
    (Nat.mem_primesLE.mp hqData.1).1
  have hAdj : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a target :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨q, hqPrime, hqData.2.1, hqY,
        Or.inl (PrimeStar.canonicalUpTarget_coe hS a q)⟩
  have hsource (eps : ℝ) :
      exactBoundaryModeInteriorSource S X a eps target =
        PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a eps a :=
    exactBoundaryModeInteriorSource_apply_eq_starMode_neighbor
      ha (by simp [PrimeStar.largePrimeStarSupport]) hAdj
  rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [exactBoundaryModeInteriorVector,
    firstExitStarResolventVector_apply_of_mem_isolated
      (exactBoundaryModeInteriorSource S X a 1) hiso,
    exactBoundaryModeInteriorVector,
    firstExitStarResolventVector_apply_of_mem_isolated
      (exactBoundaryModeInteriorSource S X a (-1)) hiso,
    hsource 1, hsource (-1),
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two (by norm_num) hd,
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two (by norm_num) hd]
  unfold exactPrincipalMoleculeBoundarySourceAmplitude
  field_simp [hroot, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]

/-- Projection of a vector that is constant on one nonempty star's leaves
onto either normalized signed star mode.  Unlike the earlier positive-only
formula, this exposes the negative output mode required by the complete T4b
coherent entry. -/
theorem real_inner_signedNormalizedStarMode_of_constant_on_leaves
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {x : EuclideanSpace ℝ (PrimeStar.Vertex S X)} {center leaf eps : ℝ}
    (heps : eps ^ 2 = 1)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y target)
    (hcenter : x target = center)
    (hleaf : ∀ v ∈ PrimeStar.largePrimeLeaves S X Y target,
      x v = leaf) :
    inner ℝ
      (PrimeStar.largePrimeNormalizedStarMode S X Y target eps) x =
      (Real.sqrt 2)⁻¹ *
        (center + eps *
          Real.sqrt
            (PrimeStar.largePrimeStarDegree S X Y target : ℝ) * leaf) := by
  classical
  let F := PrimeStar.largePrimeStarSupport S X Y target
  have hxData :
      PrimeStar.restrictEuclideanToFinset F x =
        PrimeStar.largePrimeStarDataVector S X Y target center
          (fun _ ↦ leaf) := by
    ext v
    by_cases hvt : v = target
    · subst v
      simp [F, hcenter]
    · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X Y target
      · rw [PrimeStar.restrictEuclideanToFinset_apply, if_pos (by
            simp [F, PrimeStar.largePrimeStarSupport, hvleaf])]
        rw [hleaf v hvleaf,
          PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
      · rw [PrimeStar.restrictEuclideanToFinset_apply, if_neg (by
            simp [F, PrimeStar.largePrimeStarSupport, hvt, hvleaf])]
        rw [PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf]
  rw [real_inner_normalizedStarMode_restrict_starSupport, hxData,
    largePrimeNormalizedStarMode_eq_starDataVector heps hd,
    PrimeStar.largePrimeStarDataVector_inner,
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have heps0 : eps ≠ 0 := by
    intro hzero
    rw [hzero] at heps
    norm_num at heps
  have hsqrt0 : Real.sqrt
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hsqrtSq :
      Real.sqrt
          (PrimeStar.largePrimeStarDegree S X Y target : ℝ) ^ 2 =
        (PrimeStar.largePrimeStarDegree S X Y target : ℝ) :=
    Real.sq_sqrt (by positivity)
  change (Real.sqrt 2)⁻¹ * center +
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ) *
        ((Real.sqrt 2)⁻¹ /
          (eps * Real.sqrt
            (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) * leaf) = _
  field_simp [heps0, hsqrt0]
  have hterm :
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ) * leaf =
        eps ^ 2 *
          Real.sqrt
            (PrimeStar.largePrimeStarDegree S X Y target : ℝ) ^ 2 * leaf := by
    rw [heps, hsqrtSq]
    ring
  rw [hterm]
  ring

/-- Signed-output version of the coherent common-core coefficient.

The positive and negative output modes have the same safe denominator
`z ^ 2 - s`; changing the output sign only changes the sign of the
`tau = mu_output / mu_source` term.  This is the second boundary-mode
coefficient required by the complete graph-local entry. -/
theorem real_inner_signedOutputStar_smallPrime_commonCoreSignedResponse
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdb : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (r : PrimeStar.CanonicalDownIndex a)
    (hrq : (r : ℕ) ≤ (q : ℕ))
    (houtput :
      (PrimeStar.canonicalDownTarget a r : ℕ) * (q : ℕ) = (b : ℕ))
    (hiso : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.firstExitIsolatedVertices S X (squareRootCutoff X) a)
    {eps z s tau : ℝ} (heps : eps ^ 2 = 1)
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegreeCore :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a r) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hsqrtOutput :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) b : ℝ) =
        moleculeStarEnergy S X a * tau)
    (hz : z ≠ 0) (hs : s ≠ 0) (hsep : z ^ 2 - s ≠ 0) :
    let alpha :=
      exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
        exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
    let beta :=
      exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
        exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
    let core := PrimeStar.canonicalDownTarget a r
    let common := PrimeStar.canonicalUpTarget hS a q
    let response := PrimeStar.restrictEuclideanToFinset
      (insert common
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) core))
      (exactPrincipalMoleculeSignedInteriorVector S X a)
    inner ℝ
      (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) b eps)
      ((Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).adjMatrix ℝ)) response) =
      1 / (Real.sqrt 2 * moleculeStarEnergy S X a) *
        (alpha / z +
          (z * alpha + beta) / (z ^ 2 - s) +
          eps * tau *
            ((alpha + z * beta / s) / (z ^ 2 - s) +
              beta * (1 - 1 / s) / z)) := by
  dsimp only
  let mu := moleculeStarEnergy S X a
  let alpha :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  let beta :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  let core := PrimeStar.canonicalDownTarget a r
  let common := PrimeStar.canonicalUpTarget hS a q
  let x := exactPrincipalMoleculeSignedInteriorVector S X a
  let response := PrimeStar.restrictEuclideanToFinset
    (insert common
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) core)) x
  let y := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) response
  have hmu : mu ≠ 0 := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hda)
  have hroot : exactPrincipalMoleculeRoot S X a ≠ 0 := by
    rw [hrootEq]
    exact mul_ne_zero hz hmu
  have hqData := Finset.mem_filter.mp q.property
  have hqPrime : (q : ℕ).Prime := (Nat.mem_primesLE.mp hqData.1).2
  have hqY : (q : ℕ) ≤ squareRootCutoff X :=
    (Nat.mem_primesLE.mp hqData.1).1
  have hrPrime : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.property
  have hrDvd : (r : ℕ) ∣ (a : ℕ) := Nat.dvd_of_mem_primeFactors r.property
  have hrS : (r : ℕ) ∉ S := by
    intro hrMem
    exact PrimeStar.Vertex.not_dvd_of_mem a hrMem hrDvd
  have hrY : (r : ℕ) ≤ squareRootCutoff X :=
    (Nat.le_of_mem_primeFactors r.property).trans ha
  have hcoreY : (core : ℕ) ≤ squareRootCutoff X := by
    dsimp [core]
    exact (Nat.div_le_self _ _).trans ha
  have hcommon : (b : ℕ) * (r : ℕ) = (common : ℕ) := by
    calc
      (b : ℕ) * (r : ℕ) = ((core : ℕ) * (q : ℕ)) * (r : ℕ) := by
        rw [houtput]
      _ = ((core : ℕ) * (r : ℕ)) * (q : ℕ) := by ac_rfl
      _ = (a : ℕ) * (q : ℕ) := by
        dsimp [core]
        rw [PrimeStar.canonicalDownTarget_mul_coe]
      _ = (common : ℕ) := by
        dsimp [common]
  have hcenter : y b =
      alpha / (z * mu) + (z * alpha + beta) / (mu * (z ^ 2 - s)) := by
    have hrow := smallPrime_mulVec_restrict_commonCoreSupport_apply_outputCenter
      hcoreY hqPrime hqData.2.1 hqY hrPrime hrS hrY houtput hcommon x
    have hisolated :=
      exactPrincipalMoleculeSignedInteriorVector_apply_isolatedCanonicalUpTarget
        hS ha hda q hiso hroot
    have hdown :=
      exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownTarget
        hS ha hda r hrootEq hdegreeCore hz hsep
    dsimp [y, response]
    rw [hrow]
    change x common + x core = _
    rw [show x common = alpha / exactPrincipalMoleculeRoot S X a by
      simpa [x, common, alpha] using hisolated]
    rw [show x core = (z * alpha + beta) / (mu * (z ^ 2 - s)) by
      simpa [x, core, mu, alpha, beta] using hdown]
    rw [hrootEq]
  have hleaf : ∀ w ∈ PrimeStar.largePrimeLeaves S X
      (squareRootCutoff X) b,
      y w = 1 / mu ^ 2 *
        (beta / z + (z * alpha + beta) / (z * (z ^ 2 - s))) := by
    intro w hw
    obtain ⟨v, hvP, hrow⟩ :=
      smallPrime_mulVec_restrict_commonCoreSupport_apply_outputLeaf
        hS (PrimeStar.sqrtCutoff_condition X) hcoreY hb
        hqPrime hqData.2.1 hqY hrPrime hrS hrY hrq
        houtput hcommon hw x
    have hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X
        (squareRootCutoff X) core :=
      PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves core hvP
    have hdown :=
      exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf
        hS ha hda r (by simpa [core] using hvLeaf)
        (by simpa [core] using hvP) hrootEq hdegreeCore hz hsep
    dsimp [y, response]
    rw [hrow]
    simpa [x, mu, alpha, beta] using hdown
  have hprojection :=
    real_inner_signedNormalizedStarMode_of_constant_on_leaves
      heps hdb hcenter hleaf
  change ⟪PrimeStar.largePrimeNormalizedStarMode S X
      (squareRootCutoff X) b eps, y⟫_ℝ = _
  rw [hprojection, hsqrtOutput]
  change (Real.sqrt 2)⁻¹ *
      ((alpha / (z * mu) + (z * alpha + beta) / (mu * (z ^ 2 - s))) +
        eps * (mu * tau) *
          (1 / mu ^ 2 *
            (beta / z + (z * alpha + beta) / (z * (z ^ 2 - s))))) = _
  simpa [mu, alpha, beta, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
    (coherentCommonCoreProjectionCoefficient_eq
      (z := z) (s := s) (mu := mu) (alpha := alpha) (beta := beta)
      (tau := eps * tau) hmu hz hs hsep)

/-- Uniform manuscript majorant for either signed output-star mode. -/
theorem abs_real_inner_signedOutputStar_smallPrime_commonCoreSignedResponse_le
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdb : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (r : PrimeStar.CanonicalDownIndex a)
    (hrq : (r : ℕ) ≤ (q : ℕ))
    (houtput :
      (PrimeStar.canonicalDownTarget a r : ℕ) * (q : ℕ) = (b : ℕ))
    (hiso : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.firstExitIsolatedVertices S X (squareRootCutoff X) a)
    {eps z s tau delta : ℝ} (heps : eps ^ 2 = 1)
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegreeCore :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a r) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hsqrtOutput :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) b : ℝ) =
        moleculeStarEnergy S X a * tau)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsLower : 1 ≤ s) (hsepLower : delta ≤ |z ^ 2 - s|) :
    let core := PrimeStar.canonicalDownTarget a r
    let common := PrimeStar.canonicalUpTarget hS a q
    let response := PrimeStar.restrictEuclideanToFinset
      (insert common
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) core))
      (exactPrincipalMoleculeSignedInteriorVector S X a)
    |inner ℝ
      (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) b eps)
      ((Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).adjMatrix ℝ)) response)| ≤
      10 / delta *
        (1 / moleculeStarEnergy S X a +
          |tau| / moleculeStarEnergy S X a) := by
  dsimp only
  let mu := moleculeStarEnergy S X a
  let alpha :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  let beta :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    positivity
  have hplus :
      |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hda (by norm_num)
  have hminus :
      |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hda (by norm_num)
  have halpha : |alpha| ≤ 2 := by
    dsimp [alpha]
    calc
      |_ + _| ≤
          |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| +
            |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| :=
        abs_add_le _ _
      _ ≤ 2 := by linarith
  have hbeta : |beta| ≤ 2 := by
    dsimp [beta]
    calc
      |_ - _| =
          |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
            (-exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))| := by
        rw [sub_eq_add_neg]
      _ ≤
          |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| +
            |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| := by
        simpa using
          (abs_add_le
            (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
            (-exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)))
      _ ≤ 2 := by linarith
  have hz : z ≠ 0 :=
    abs_pos.mp (lt_of_lt_of_le (by norm_num) hzLower)
  have hs : s ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hsLower)
  have hsep : z ^ 2 - s ≠ 0 :=
    abs_pos.mp (lt_of_lt_of_le hdelta hsepLower)
  have hepsAbs : |eps| = 1 := by
    have hsquare : |eps| ^ 2 = 1 := by simpa [sq_abs] using heps
    nlinarith [abs_nonneg eps]
  rw [real_inner_signedOutputStar_smallPrime_commonCoreSignedResponse
    hS ha hb hda hdb q r hrq houtput hiso heps hrootEq hdegreeCore
    hsqrtOutput hz hs hsep]
  have hbound :=
    abs_coherentCommonCoreProjectionCoefficient_le
      (z := z) (s := s) (mu := mu) (alpha := alpha) (beta := beta)
      (tau := eps * tau) (delta := delta) hmu hdelta hdeltaOne hzLower hzUpper
      hsLower hsepLower halpha hbeta
  simpa [mu, alpha, beta, abs_mul, hepsAbs] using hbound

private theorem exists_targetCenter_of_mem_firstExitCompressionSupport
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {c v : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ PrimeStar.firstExitCompressionSupport S X Y c) :
    ∃ k : PrimeStar.Vertex S X,
      v ∈ PrimeStar.largePrimeStarSupport S X Y k ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj c k ∧
      ((k : ℕ) ≤ Y ∨
        (k = v ∧ (PrimeStar.largePrimeGraph S X Y).IsIsolated k)) := by
  rcases Finset.mem_union.mp hv with hvStars | hvIso
  · obtain ⟨k, hkLower, hvk⟩ :=
      PrimeStar.mem_largePrimeStarUnionSupport.mp hvStars
    obtain ⟨q, hq, hqS, hqY, hrel⟩ :=
      PrimeStar.mem_firstExitLowerCenters_arithmetic hcut hc hkLower
    refine ⟨k, hvk, ?_, Or.inl (PrimeStar.mem_firstExitLowerCenters.mp hkLower).1⟩
    exact PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨q, hq, hqS, hqY, hrel⟩
  · obtain ⟨q, hq, hqS, hqY, hrel⟩ :=
      PrimeStar.mem_firstExitIsolatedVertices_arithmetic hS hc hvIso
    refine ⟨v, ?_, ?_, Or.inr ⟨rfl,
      (PrimeStar.mem_firstExitIsolatedVertices.mp hvIso).2⟩⟩
    · simp [PrimeStar.largePrimeStarSupport]
    · exact PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
        ⟨q, hq, hqS, hqY, hrel⟩

private theorem smallPrimeAdj_targetCenters_of_firstExit
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {v w ka kb : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (hvka : v ∈ PrimeStar.largePrimeStarSupport S X Y ka)
    (hwkb : w ∈ PrimeStar.largePrimeStarSupport S X Y kb)
    (hka : (ka : ℕ) ≤ Y ∨
      (ka = v ∧ (PrimeStar.largePrimeGraph S X Y).IsIsolated ka))
    (hkb : (kb : ℕ) ≤ Y ∨
      (kb = w ∧ (PrimeStar.largePrimeGraph S X Y).IsIsolated kb))
    (hvw : (PrimeStar.smallPrimeGraph S X Y).Adj v w) :
    (PrimeStar.smallPrimeGraph S X Y).Adj ka kb := by
  rcases hka with hkaY | ⟨rfl, hvaIso⟩ <;>
    rcases hkb with hkbY | ⟨rfl, hwbIso⟩
  · obtain ⟨q, hq, hqS, hqY, hrel⟩ :=
      PrimeStar.smallPrimeAdj_between_largePrimeStarSupports_centers
        hcut hkaY hkbY hvka hwkb hvw
    exact PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨q, hq, hqS, hqY, hrel⟩
  · rw [PrimeStar.mem_largePrimeStarSupport] at hvka
    rcases hvka with rfl | hvLeaf
    · exact hvw
    · exact False.elim
        (PrimeStar.not_isolated_of_smallPrimeAdj_largePrimeLeaf
          hS hkaY (PrimeStar.mem_largePrimeLeaves.mpr hvLeaf) hvw hwbIso)
  · rw [PrimeStar.mem_largePrimeStarSupport] at hwkb
    rcases hwkb with rfl | hwLeaf
    · exact hvw
    · exact False.elim
        (PrimeStar.not_isolated_of_smallPrimeAdj_largePrimeLeaf
          hS hkbY (PrimeStar.mem_largePrimeLeaves.mpr hwLeaf)
          (by simpa using hvw.symm) hvaIso)
  · exact hvw

private theorem common_smallPrimeNeighbor_of_primeSiblings
    {S : Finset ℕ} {X Y g q r : ℕ}
    {a b k : PrimeStar.Vertex S X}
    (hg : 0 < g) (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r)
    (ha : (a : ℕ) = g * r) (hb : (b : ℕ) = g * q)
    (hak : (PrimeStar.smallPrimeGraph S X Y).Adj a k)
    (hbk : (PrimeStar.smallPrimeGraph S X Y).Adj b k) :
    (k : ℕ) = g * r * q ∨ (k : ℕ) = g := by
  obtain ⟨ell, hell, _hellS, _hellY, hellRel⟩ :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hak
  obtain ⟨m, hm, _hmS, _hmY, hmRel⟩ :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hbk
  rcases hellRel with haell | hkell <;> rcases hmRel with hbm | hkm
  · have hab : (a : ℕ) ≠ (b : ℕ) := by
      rw [ha, hb]
      exact fun h ↦ hqr (Nat.eq_of_mul_eq_mul_left hg h).symm
    have heq : (a : ℕ) * ell = (b : ℕ) * m := haell.trans hbm.symm
    obtain ⟨g', hg', ha', hb'⟩ :=
      exists_commonCore_of_mul_prime_eq_mul_prime
        (PrimeStar.Vertex.coe_pos a) hell hm hab heq
    obtain ⟨rfl, hqell, _hrm⟩ :=
      commonCore_primeFactorization_unique hab hg hq hell hr hm
        ha hb ha' hb'
    left
    calc
      (k : ℕ) = (a : ℕ) * ell := haell.symm
      _ = (g * r) * q := by rw [ha, hqell]
      _ = g * r * q := rfl
  · have hrProduct : r * (ell * m) = q := by
      apply Nat.eq_of_mul_eq_mul_left hg
      calc
        g * (r * (ell * m)) = ((g * r) * ell) * m := by ac_rfl
        _ = ((a : ℕ) * ell) * m := by rw [ha]
        _ = (k : ℕ) * m := by rw [haell]
        _ = (b : ℕ) := hkm
        _ = g * q := hb
    exact False.elim
      ((Nat.not_prime_of_mul_eq hrProduct hr.ne_one (by
        nlinarith [hell.two_le, hm.two_le])) hq)
  · have hqProduct : q * (m * ell) = r := by
      apply Nat.eq_of_mul_eq_mul_left hg
      calc
        g * (q * (m * ell)) = ((g * q) * m) * ell := by ac_rfl
        _ = ((b : ℕ) * m) * ell := by rw [hb]
        _ = (k : ℕ) * ell := by rw [hbm]
        _ = (a : ℕ) := hkell
        _ = g * r := ha
    exact False.elim
      ((Nat.not_prime_of_mul_eq hqProduct hq.ne_one (by
        nlinarith [hm.two_le, hell.two_le])) hr)
  · have hellm : ell ≠ m := by
      intro helm
      apply hqr
      have habCoe : (a : ℕ) = (b : ℕ) := by
        calc
          (a : ℕ) = (k : ℕ) * ell := hkell.symm
          _ = (k : ℕ) * m := by rw [helm]
          _ = (b : ℕ) := hkm
      rw [ha, hb] at habCoe
      exact (Nat.eq_of_mul_eq_mul_left hg habCoe).symm
    have hgcdPrime : Nat.gcd ell m = 1 :=
      (Nat.coprime_primes hell hm).2 hellm |>.gcd_eq_one
    have hgcdAB : Nat.gcd (a : ℕ) (b : ℕ) = g := by
      rw [ha, hb, Nat.gcd_mul_left,
        (Nat.coprime_primes hr hq).2 hqr.symm |>.gcd_eq_one, mul_one]
    right
    calc
      (k : ℕ) = Nat.gcd (a : ℕ) (b : ℕ) := by
        rw [← hkell, ← hkm, Nat.gcd_mul_left, hgcdPrime, mul_one]
      _ = g := hgcdAB

private theorem mem_commonCoreSupport_of_data_outputBoundary_neighbor
    {S : Finset ℕ} {X K g : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (gV : PrimeStar.Vertex S X)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) source.1)
    (r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) output.1)
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hg : 0 < g) (hgV : (gV : ℕ) = g)
    (hq : (q : ℕ).Prime) (hr : (r : ℕ).Prime)
    (hqS : (q : ℕ) ∉ S) (hrS : (r : ℕ) ∉ S)
    (hqY : (q : ℕ) ≤ squareRootCutoff X)
    (hrY : (r : ℕ) ≤ squareRootCutoff X)
    (ha : (source.1 : ℕ) = g * (r : ℕ))
    (hb : (output.1 : ℕ) = g * (q : ℕ))
    (hcommonCut : squareRootCutoff X <
      (PrimeStar.canonicalUpTarget hS source.1 q : ℕ))
    (hne : source ≠ output)
    {v w : PrimeStar.Vertex S X}
    (hv : v ∈ PrimeStar.largePrimeStarSupport S X
      (squareRootCutoff X) output.1)
    (hw : w ∈ PrimeStar.firstExitCompressionSupport S X
      (squareRootCutoff X) source.1)
    (hvw : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj v w) :
    w ∈ insert (PrimeStar.canonicalUpTarget hS source.1 q)
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) gV) := by
  obtain ⟨k, hwk, hsourceK, hk⟩ :=
    exists_targetCenter_of_mem_firstExitCompressionSupport
      hS (PrimeStar.sqrtCutoff_condition X) hsource hw
  have houtputK : (PrimeStar.smallPrimeGraph S X
      (squareRootCutoff X)).Adj output.1 k :=
    smallPrimeAdj_targetCenters_of_firstExit hS
      (PrimeStar.sqrtCutoff_condition X) hv hwk (Or.inl houtput) hk hvw
  have hqr : (q : ℕ) ≠ (r : ℕ) := by
    intro hqr
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rw [ha, hb, hqr]
  rcases common_smallPrimeNeighbor_of_primeSiblings hg hq hr hqr ha hb
      hsourceK houtputK with hkCommon | hkCore
  · have hkTarget : k = PrimeStar.canonicalUpTarget hS source.1 q := by
      apply Subtype.ext
      apply Fin.ext
      calc
        (k : ℕ) = g * (r : ℕ) * (q : ℕ) := hkCommon
        _ = (source.1 : ℕ) * (q : ℕ) := by rw [ha]
        _ = (PrimeStar.canonicalUpTarget hS source.1 q : ℕ) :=
          (PrimeStar.canonicalUpTarget_coe hS source.1 q).symm
    have hkIso : (PrimeStar.largePrimeGraph S X
        (squareRootCutoff X)).IsIsolated k := by
      subst k
      exact PrimeStar.canonicalUpTarget_isIsolated_of_cutoff_lt
        hsource (PrimeStar.sqrtCutoff_condition X) hq hqY
        (PrimeStar.canonicalUpTarget_coe hS source.1 q) hcommonCut
    have hwEq : w = k := by
      rw [PrimeStar.mem_largePrimeStarSupport] at hwk
      rcases hwk with hwEq | hwAdj
      · exact hwEq
      · exact False.elim (hkIso w hwAdj)
    exact Finset.mem_insert.mpr (Or.inl (hwEq.trans hkTarget))
  · have hkG : k = gV := by
      apply Subtype.ext
      apply Fin.ext
      simpa [hgV] using hkCore
    exact Finset.mem_insert.mpr (Or.inr (by simpa [hkG] using hwk))

private theorem smallPrime_mulVec_signedInterior_eq_commonCore_on_outputStar_of_data
    {S : Finset ℕ} {X K g : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (gV : PrimeStar.Vertex S X)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) source.1)
    (r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) output.1)
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hg : 0 < g) (hgV : (gV : ℕ) = g)
    (hq : (q : ℕ).Prime) (hr : (r : ℕ).Prime)
    (hqS : (q : ℕ) ∉ S) (hrS : (r : ℕ) ∉ S)
    (hqY : (q : ℕ) ≤ squareRootCutoff X)
    (hrY : (r : ℕ) ≤ squareRootCutoff X)
    (ha : (source.1 : ℕ) = g * (r : ℕ))
    (hb : (output.1 : ℕ) = g * (q : ℕ))
    (hcommonCut : squareRootCutoff X <
      (PrimeStar.canonicalUpTarget hS source.1 q : ℕ))
    (hne : source ≠ output)
    {v : PrimeStar.Vertex S X}
    (hv : v ∈ PrimeStar.largePrimeStarSupport S X
      (squareRootCutoff X) output.1) :
    Matrix.mulVec
        ((PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeSignedInteriorVector S X source.1) v =
      Matrix.mulVec
        ((PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).adjMatrix ℝ)
        (PrimeStar.restrictEuclideanToFinset
          (insert (PrimeStar.canonicalUpTarget hS source.1 q)
            (PrimeStar.largePrimeStarSupport S X
              (squareRootCutoff X) gV))
          (exactPrincipalMoleculeSignedInteriorVector S X source.1)) v := by
  rw [SimpleGraph.adjMatrix_mulVec_apply,
    SimpleGraph.adjMatrix_mulVec_apply]
  apply Finset.sum_congr rfl
  intro w hwNeighbor
  rw [PrimeStar.restrictEuclideanToFinset_apply]
  by_cases hwCore : w ∈ insert (PrimeStar.canonicalUpTarget hS source.1 q)
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) gV)
  · rw [if_pos hwCore]
  · have hwZero : exactPrincipalMoleculeSignedInteriorVector S X source.1 w = 0 := by
      by_contra hwNe
      have hwExit : w ∈ PrimeStar.firstExitCompressionSupport S X
          (squareRootCutoff X) source.1 := by
        by_contra hwOut
        exact hwNe
          (PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem
            (exactPrincipalMoleculeSignedInteriorSource S X source.1) hwOut)
      exact hwCore
        (mem_commonCoreSupport_of_data_outputBoundary_neighbor
          hS gV q r hsource houtput hg hgV
          hq hr hqS hrS hqY hrY ha hb hcommonCut hne
          hv hwExit
          (((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).mem_neighborFinset
            v w).mp hwNeighbor))
    rw [if_neg hwCore, hwZero]

private theorem real_inner_signedOutput_smallPrime_signedInterior_eq_commonCore_of_data
    {S : Finset ℕ} {X K g : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (gV : PrimeStar.Vertex S X)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) source.1)
    (r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) output.1)
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hg : 0 < g) (hgV : (gV : ℕ) = g)
    (hq : (q : ℕ).Prime) (hr : (r : ℕ).Prime)
    (hqS : (q : ℕ) ∉ S) (hrS : (r : ℕ) ∉ S)
    (hqY : (q : ℕ) ≤ squareRootCutoff X)
    (hrY : (r : ℕ) ≤ squareRootCutoff X)
    (ha : (source.1 : ℕ) = g * (r : ℕ))
    (hb : (output.1 : ℕ) = g * (q : ℕ))
    (hcommonCut : squareRootCutoff X <
      (PrimeStar.canonicalUpTarget hS source.1 q : ℕ))
    (hne : source ≠ output) (eps : ℝ) :
    inner ℝ
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) output.1 eps)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeSignedInteriorVector S X source.1)) =
      inner ℝ
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) output.1 eps)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ)
          (PrimeStar.restrictEuclideanToFinset
            (insert (PrimeStar.canonicalUpTarget hS source.1 q)
              (PrimeStar.largePrimeStarSupport S X
                (squareRootCutoff X) gV))
            (exactPrincipalMoleculeSignedInteriorVector S X source.1))) := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hvStar : v ∈ PrimeStar.largePrimeStarSupport S X
      (squareRootCutoff X) output.1
  · congr 1
    change Matrix.mulVec
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeSignedInteriorVector S X source.1) v = _
    exact
      smallPrime_mulVec_signedInterior_eq_commonCore_on_outputStar_of_data
        hS gV q r hsource houtput hg hgV hq hr hqS hrS hqY hrY
        ha hb hcommonCut hne hvStar
  · rw [PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hvStar]
    simp

private theorem not_smallPrimeAdj_between_coherent_firstExitCompressionSupports
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : MoleculeCenter S X K}
    (haY : (a.1 : ℕ) ≤ squareRootCutoff X)
    (hbY : (b.1 : ℕ) ≤ squareRootCutoff X)
    (hab : IsCoherentRawMoleculePair hS a b)
    {v w : PrimeStar.Vertex S X}
    (hv : v ∈ PrimeStar.firstExitCompressionSupport S X
      (squareRootCutoff X) a.1)
    (hw : w ∈ PrimeStar.firstExitCompressionSupport S X
      (squareRootCutoff X) b.1) :
    ¬(PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj v w := by
  intro hvw
  obtain ⟨ka, hvka, haka, hka⟩ :=
    exists_targetCenter_of_mem_firstExitCompressionSupport
      hS (PrimeStar.sqrtCutoff_condition X) haY hv
  obtain ⟨kb, hwkb, hbkb, hkb⟩ :=
    exists_targetCenter_of_mem_firstExitCompressionSupport
      hS (PrimeStar.sqrtCutoff_condition X) hbY hw
  have hkakb : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj ka kb :=
    smallPrimeAdj_targetCenters_of_firstExit hS
      (PrimeStar.sqrtCutoff_condition X) hvka hwkb hka hkb hvw
  obtain ⟨g, hg, q, r, hq, hr, hqS, hrS, hqY, hrY,
      ha, hb, _hcommonCut⟩ :=
    exists_commonCore_of_isCoherentRawMoleculePair hS hab
  have hgDvdA : g ∣ (a.1 : ℕ) := ⟨r, ha⟩
  let gv : PrimeStar.Vertex S X :=
    PrimeStar.vertexDivisorOfDvd a.1 hg hgDvdA
  have hga : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj gv a.1 := by
    apply PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
    refine ⟨r, hr, hrS, hrY, Or.inl ?_⟩
    simpa [gv] using ha.symm
  have hgb : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj gv b.1 := by
    apply PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
    refine ⟨q, hq, hqS, hqY, Or.inl ?_⟩
    simpa [gv] using hb.symm
  have sign_a := PrimeStar.primeCoverParitySign_eq_neg_of_adj
    ((PrimeStar.smallPrimeGraph_adj.mp hga).1)
  have sign_b := PrimeStar.primeCoverParitySign_eq_neg_of_adj
    ((PrimeStar.smallPrimeGraph_adj.mp hgb).1)
  have sign_ka := PrimeStar.primeCoverParitySign_eq_neg_of_adj
    ((PrimeStar.smallPrimeGraph_adj.mp haka).1)
  have sign_kb := PrimeStar.primeCoverParitySign_eq_neg_of_adj
    ((PrimeStar.smallPrimeGraph_adj.mp hbkb).1)
  have sign_ab := PrimeStar.primeCoverParitySign_eq_neg_of_adj
    ((PrimeStar.smallPrimeGraph_adj.mp hkakb).1)
  have sign_sq := PrimeStar.primeCoverParitySign_sq kb
  nlinarith

private theorem real_inner_firstExitResolvent_residual_eq_zero_of_coherentRawPair
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hcoherent : IsCoherentRawMoleculePair hS source output)
    (mu : ℝ) (u : EuclideanSpace ℝ (PrimeStar.Vertex S X)) :
    inner ℝ
        (PrimeStar.firstExitStarResolventVector S X (squareRootCutoff X)
          output.1 mu u)
        (exactPrincipalMoleculeResidual S X source.1) = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro v _hv
  by_cases hresolvent : PrimeStar.firstExitStarResolventVector S X
      (squareRootCutoff X) output.1 mu u v = 0
  · simp [hresolvent]
  by_cases hresidual : exactPrincipalMoleculeResidual S X source.1 v = 0
  · simp [hresidual]
  have hvOutput : v ∈ PrimeStar.firstExitCompressionSupport S X
      (squareRootCutoff X) output.1 := by
    by_contra hvOut
    exact hresolvent
      (PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem u hvOut)
  obtain ⟨w, hwSource, hvw⟩ :=
    exists_firstExitInteriorNeighbor_of_exactPrincipalMoleculeResidual_ne_zero
      hS hsource hresidual
  exact False.elim
    (not_smallPrimeAdj_between_coherent_firstExitCompressionSupports
      hS hsource houtput hcoherent hwSource hvOutput
      (by simpa using hvw.symm))

private theorem real_inner_signedInterior_residual_eq_zero_of_coherentRawPair
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hcoherent : IsCoherentRawMoleculePair hS source output) :
    inner ℝ
        (exactPrincipalMoleculeSignedInteriorVector S X output.1)
        (exactPrincipalMoleculeResidual S X source.1) = 0 := by
  exact real_inner_firstExitResolvent_residual_eq_zero_of_coherentRawPair
    hS hsource houtput hcoherent (exactPrincipalMoleculeRoot S X output.1)
    (exactPrincipalMoleculeSignedInteriorSource S X output.1)

private theorem real_inner_kernelInterior_residual_eq_zero_of_coherentRawPair
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hcoherent : IsCoherentRawMoleculePair hS source output) :
    inner ℝ
        (exactPrincipalMoleculeKernelInteriorVector S X output.1)
        (exactPrincipalMoleculeResidual S X source.1) = 0 := by
  exact real_inner_firstExitResolvent_residual_eq_zero_of_coherentRawPair
    hS hsource houtput hcoherent (exactPrincipalMoleculeRoot S X output.1)
    (exactPrincipalMoleculeKernelInteriorSource S X output.1)

private theorem moleculeCenter_signedStarMode_orthonormal
    {S : Finset ℕ} {X K : ℕ}
    (ha : ∀ a : MoleculeCenter S X K,
      (a.1 : ℕ) ≤ squareRootCutoff X)
    (hd : ∀ a : MoleculeCenter S X K,
      0 < PrimeStar.largePrimeStarDegree S X
        (squareRootCutoff X) a.1)
    (eps : ℝ) (heps : eps ^ 2 = 1) :
    Orthonormal ℝ (fun a : MoleculeCenter S X K ↦
      PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a.1 eps) := by
  constructor
  · intro a
    exact PrimeStar.norm_largePrimeNormalizedStarMode (hd a)
  · intro a b hab
    have habCenter : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    have hdisjoint := PrimeStar.sqrtCutoff_disjoint_largePrimeStarSupport
      (ha a) (ha b) habCenter
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro v _hv
    by_cases hva : v ∈ PrimeStar.largePrimeStarSupport S X
        (squareRootCutoff X) a.1
    · have hvb : v ∉ PrimeStar.largePrimeStarSupport S X
          (squareRootCutoff X) b.1 := by
        intro hvb
        exact (Finset.disjoint_left.mp hdisjoint) hva hvb
      rw [PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hvb]
      simp
    · rw [PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hva]
      simp

private theorem sum_sq_abs_inner_signedBoundary_le_four_norm_sq
    {S : Finset ℕ} {X K : ℕ}
    (ha : ∀ a : MoleculeCenter S X K,
      (a.1 : ℕ) ≤ squareRootCutoff X)
    (hd : ∀ a : MoleculeCenter S X K,
      0 < PrimeStar.largePrimeStarDegree S X
        (squareRootCutoff X) a.1)
    (y : MoleculeAmbient S X) :
    (∑ a : MoleculeCenter S X K,
        |inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X a.1) y| ^ 2) ≤
      4 * ‖y‖ ^ 2 := by
  let up : MoleculeCenter S X K → MoleculeAmbient S X := fun a ↦
    PrimeStar.largePrimeNormalizedStarMode S X
      (squareRootCutoff X) a.1 1
  let um : MoleculeCenter S X K → MoleculeAmbient S X := fun a ↦
    PrimeStar.largePrimeNormalizedStarMode S X
      (squareRootCutoff X) a.1 (-1)
  have hup : Orthonormal ℝ up := by
    simpa [up] using moleculeCenter_signedStarMode_orthonormal
      ha hd (1 : ℝ) (by norm_num)
  have hum : Orthonormal ℝ um := by
    simpa [um] using moleculeCenter_signedStarMode_orthonormal
      ha hd (-1 : ℝ) (by norm_num)
  have hupBessel : (∑ a : MoleculeCenter S X K,
      |inner ℝ (up a) y| ^ 2) ≤ ‖y‖ ^ 2 := by
    simpa [Real.norm_eq_abs] using
      (hup.sum_inner_products_le y (s := Finset.univ))
  have humBessel : (∑ a : MoleculeCenter S X K,
      |inner ℝ (um a) y| ^ 2) ≤ ‖y‖ ^ 2 := by
    simpa [Real.norm_eq_abs] using
      (hum.sum_inner_products_le y (s := Finset.univ))
  calc
    (∑ a : MoleculeCenter S X K,
        |inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X a.1) y| ^ 2) ≤
        ∑ a : MoleculeCenter S X K,
          2 * (|inner ℝ (up a) y| ^ 2 + |inner ℝ (um a) y| ^ 2) := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis (hd a)]
      simp only [inner_add_left, real_inner_smul_left]
      have hcp := abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one
        (S := S) (X := X) (a := a.1) (hd a) (by norm_num : (1 : ℝ) ^ 2 = 1)
      have hcm := abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one
        (S := S) (X := X) (a := a.1) (hd a) (by norm_num : (-1 : ℝ) ^ 2 = 1)
      have hp :
          |exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 1 *
              inner ℝ (up a) y| ≤ |inner ℝ (up a) y| := by
        rw [abs_mul]
        simpa using mul_le_of_le_one_left (abs_nonneg _) hcp
      have hm :
          |exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 (-1) *
              inner ℝ (um a) y| ≤ |inner ℝ (um a) y| := by
        rw [abs_mul]
        simpa using mul_le_of_le_one_left (abs_nonneg _) hcm
      have hadd := abs_add_le
        (exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 1 *
          inner ℝ (up a) y)
        (exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 (-1) *
          inner ℝ (um a) y)
      have htotal :
          |exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 1 *
                inner ℝ (up a) y +
              exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 (-1) *
                inner ℝ (um a) y| ≤
            |inner ℝ (up a) y| + |inner ℝ (um a) y| :=
        hadd.trans (add_le_add hp hm)
      have htotalSq :
          |exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 1 *
                inner ℝ (up a) y +
              exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 (-1) *
                inner ℝ (um a) y| ^ 2 ≤
            (|inner ℝ (up a) y| + |inner ℝ (um a) y|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _)
          (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 htotal
      calc
        |exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 1 *
              inner ℝ (up a) y +
            exactPrincipalMoleculeBoundaryModeCoefficient S X a.1 (-1) *
              inner ℝ (um a) y| ^ 2 ≤
            (|inner ℝ (up a) y| + |inner ℝ (um a) y|) ^ 2 := htotalSq
        _ ≤ 2 * (|inner ℝ (up a) y| ^ 2 + |inner ℝ (um a) y| ^ 2) := by
          nlinarith [sq_nonneg
            (|inner ℝ (up a) y| - |inner ℝ (um a) y|)]
    _ = 2 * ((∑ a : MoleculeCenter S X K, |inner ℝ (up a) y| ^ 2) +
        ∑ a : MoleculeCenter S X K, |inner ℝ (um a) y| ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (‖y‖ ^ 2 + ‖y‖ ^ 2) := by
      gcongr
    _ = 4 * ‖y‖ ^ 2 := by ring_nf


private theorem
    exactOneExitLocalCompressionResidual_eq_signedBoundary_add_boundaryKernel_of_coherent
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hcoherent : IsCoherentRawMoleculePair hS source output)
    (hroot : exactPrincipalMoleculeRoot S X output.1 ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X output.1 • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) output.1 x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) output.1,
      exactPrincipalMoleculeRoot S X output.1 ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) k : ℝ)) :
    exactOneExitLocalCompressionResidual S X K output source =
      ((inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
          (exactPrincipalMoleculeResidual S X source.1) +
        inner ℝ
          (exactPrincipalMoleculeBoundaryKernel S X output.1)
          (exactPrincipalMoleculeResidual S X source.1) : ℝ) : ℂ) := by
  rw [exactOneExitLocalCompressionResidual_eq_branch_inner
    hS output source houtput hroot gamma hgamma hgap hden]
  rw [real_inner_signedInterior_residual_eq_zero_of_coherentRawPair
    hS hsource houtput hcoherent]
  rw [exactPrincipalMoleculeKernelBranch, inner_add_left,
    real_inner_kernelInterior_residual_eq_zero_of_coherentRawPair
      hS hsource houtput hcoherent]
  ring

private theorem
    inner_signedBoundary_residual_eq_signedInterior_add_kernelInterior_of_coherent
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsource : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtput : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hdoutput : 0 < PrimeStar.largePrimeStarDegree S X
      (squareRootCutoff X) output.1)
    (hcoherent : IsCoherentRawMoleculePair hS source output)
    (hroot : exactPrincipalMoleculeRoot S X source.1 ≠ 0)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : MoleculeAmbient S X,
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X source.1 • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) source.1 x‖)
    (hden : ∀ k ∈ PrimeStar.firstExitLowerCenters S X
        (squareRootCutoff X) source.1,
      exactPrincipalMoleculeRoot S X source.1 ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) k : ℝ)) :
    let H := Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).adjMatrix ℝ)
    inner ℝ
        (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
        (exactPrincipalMoleculeResidual S X source.1) =
      inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
          (H (exactPrincipalMoleculeSignedInteriorVector S X source.1)) +
        inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
          (H (exactPrincipalMoleculeKernelInteriorVector S X source.1)) := by
  dsimp only
  rw [inner_signedBoundary_residual_eq_modes hdoutput]
  rw [real_inner_signedStarMode_exactPrincipalMoleculeResidual_eq_smallPrime_interior_of_coherentRawPair
      hS hsource houtput hdoutput hcoherent,
    real_inner_signedStarMode_exactPrincipalMoleculeResidual_eq_smallPrime_interior_of_coherentRawPair
      hS hsource houtput hdoutput hcoherent]
  rw [exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel
    hS hsource hroot gamma hgamma hgap hden]
  simp only [map_add, inner_add_right, mul_add]
  rw [exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hdoutput]
  simp only [inner_add_left, real_inner_smul_left]
  ring_nf

set_option maxHeartbeats 3000000 in
/-- Exact coherent Hilbert--Schmidt assembly with the two kernel-mediated
families charged at source-weighted scale.

The only arithmetic input left abstract is the common-core matrix budget.
The other two terms are not pointwise full-entry hypotheses: they are
produced from the literal boundary-kernel square sum, the exact residual
energy, the small-prime operator bound, and the common first-exit gap.  Thus
the theorem is the finite Corollary R.4 interface and does not reintroduce
the superseded pointwise coherent-entry target. -/
theorem exactOneExitLocalCoherentCompressionResidual_frobenius_sq_le_core_kernel
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (ha : ∀ a : MoleculeCenter S X K,
      (a.1 : ℕ) ≤ squareRootCutoff X)
    (hd : ∀ a : MoleculeCenter S X K,
      0 < PrimeStar.largePrimeStarDegree S X
        (squareRootCutoff X) a.1)
    (hroot : ∀ a : MoleculeCenter S X K,
      exactPrincipalMoleculeRoot S X a.1 ≠ 0)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 ≤ eta)
    (hgap : ∀ (a : MoleculeCenter S X K) (x : MoleculeAmbient S X),
      gamma * ‖x‖ ≤
        ‖exactPrincipalMoleculeRoot S X a.1 • x -
          PrimeStar.firstExitLargePrimeCompressionOperator S X
            (squareRootCutoff X) a.1 x‖)
    (hden : ∀ (a : MoleculeCenter S X K)
        (k : PrimeStar.Vertex S X),
      k ∈ PrimeStar.firstExitLowerCenters S X
          (squareRootCutoff X) a.1 →
        exactPrincipalMoleculeRoot S X a.1 ^ 2 ≠
          (PrimeStar.largePrimeStarDegree S X
            (squareRootCutoff X) k : ℝ))
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X
            (squareRootCutoff X)).adjMatrix ℝ) x‖ ≤ eta * ‖x‖)
    {coreBudget boundaryKernelBudget residualBudget : ℝ}
    (hcore :
      (∑ output : MoleculeCenter S X K,
        ∑ source : MoleculeCenter S X K,
          if IsCoherentRawMoleculePair hS output source then
            |inner ℝ
              (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
              (Matrix.toEuclideanLin
                ((PrimeStar.smallPrimeGraph S X
                  (squareRootCutoff X)).adjMatrix ℝ)
                (exactPrincipalMoleculeSignedInteriorVector S X source.1))| ^ 2
          else 0) ≤ coreBudget)
    (hboundary :
      (∑ a : MoleculeCenter S X K,
        ‖exactPrincipalMoleculeBoundaryKernel S X a.1‖ ^ 2) ≤
          boundaryKernelBudget)
    (hresidual :
      (∑ a : MoleculeCenter S X K,
        ‖exactPrincipalMoleculeResidual S X a.1‖ ^ 2) ≤
          residualBudget) :
    matrixFrobeniusNorm
        (exactOneExitLocalCoherentCompressionResidual
          (S := S) (X := X) (K := K) hS) ^ 2 ≤
      3 * (coreBudget +
        4 * eta ^ 4 / gamma ^ 2 * boundaryKernelBudget +
        boundaryKernelBudget * residualBudget) := by
  let H : MoleculeAmbient S X →ₗ[ℝ] MoleculeAmbient S X :=
    Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X
        (squareRootCutoff X)).adjMatrix ℝ)
  let C : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
    fun output source ↦
      if IsCoherentRawMoleculePair hS output source then
        ((inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
          (H (exactPrincipalMoleculeSignedInteriorVector S X source.1)) : ℝ) : ℂ)
      else 0
  let KI : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
    fun output source ↦
      if IsCoherentRawMoleculePair hS output source then
        ((inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
          (H (exactPrincipalMoleculeKernelInteriorVector S X source.1)) : ℝ) : ℂ)
      else 0
  let KB : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
    fun output source ↦
      if IsCoherentRawMoleculePair hS output source then
        ((inner ℝ
          (exactPrincipalMoleculeBoundaryKernel S X output.1)
          (exactPrincipalMoleculeResidual S X source.1) : ℝ) : ℂ)
      else 0
  have hdecomp :
      exactOneExitLocalCoherentCompressionResidual
          (S := S) (X := X) (K := K) hS = C + KI + KB := by
    ext output source
    by_cases hcoh : IsCoherentRawMoleculePair hS output source
    · rw [exactOneExitLocalCoherentCompressionResidual]
      simp only [hcoh, ↓reduceIte]
      have hcoh' : IsCoherentRawMoleculePair hS source output :=
        (isCoherentRawMoleculePair_comm hS source output).2 hcoh
      rw [exactOneExitLocalCompressionResidual_eq_signedBoundary_add_boundaryKernel_of_coherent
        hS (ha source) (ha output) hcoh' (hroot output) gamma hgamma
        (hgap output) (hden output)]
      rw [inner_signedBoundary_residual_eq_signedInterior_add_kernelInterior_of_coherent
        hS (ha source) (ha output) (hd output) hcoh' (hroot source)
        gamma hgamma (hgap source) (hden source)]
      simp only [C, KI, KB, H, hcoh, ↓reduceIte, Matrix.add_apply]
      push_cast
      ring_nf
    · rw [exactOneExitLocalCoherentCompressionResidual]
      simp [hcoh, C, KI, KB]
  have hC : matrixFrobeniusNorm C ^ 2 ≤ coreBudget := by
    rw [matrixFrobeniusNorm_sq]
    calc
      (∑ output : MoleculeCenter S X K,
          ∑ source : MoleculeCenter S X K, ‖C output source‖ ^ 2) =
          ∑ output : MoleculeCenter S X K,
            ∑ source : MoleculeCenter S X K,
              if IsCoherentRawMoleculePair hS output source then
                |inner ℝ
                  (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
                  (Matrix.toEuclideanLin
                    ((PrimeStar.smallPrimeGraph S X
                      (squareRootCutoff X)).adjMatrix ℝ)
                    (exactPrincipalMoleculeSignedInteriorVector
                      S X source.1))| ^ 2
              else 0 := by
        apply Finset.sum_congr rfl
        intro output _houtput
        apply Finset.sum_congr rfl
        intro source _hsource
        by_cases hcoh : IsCoherentRawMoleculePair hS output source <;>
          simp [C, H, hcoh, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ coreBudget := hcore
  have hKI : matrixFrobeniusNorm KI ^ 2 ≤
      4 * eta ^ 4 / gamma ^ 2 * boundaryKernelBudget := by
    rw [matrixFrobeniusNorm_sq, Finset.sum_comm]
    calc
      (∑ source : MoleculeCenter S X K,
          ∑ output : MoleculeCenter S X K, ‖KI output source‖ ^ 2) ≤
          ∑ source : MoleculeCenter S X K,
            4 * ‖H (exactPrincipalMoleculeKernelInteriorVector
              S X source.1)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro source _hsource
        calc
          (∑ output : MoleculeCenter S X K, ‖KI output source‖ ^ 2) ≤
              ∑ output : MoleculeCenter S X K,
                |inner ℝ
                  (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
                  (H (exactPrincipalMoleculeKernelInteriorVector
                    S X source.1))| ^ 2 := by
            apply Finset.sum_le_sum
            intro output _houtput
            by_cases hcoh : IsCoherentRawMoleculePair hS output source
            · simp [KI, hcoh, Complex.norm_real, Real.norm_eq_abs]
            · simp only [KI, hcoh, ↓reduceIte, norm_zero]
              simpa only [pow_two, zero_mul] using
                sq_nonneg
                  |inner ℝ
                    (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
                    (H (exactPrincipalMoleculeKernelInteriorVector
                      S X source.1))|
          _ ≤ 4 * ‖H (exactPrincipalMoleculeKernelInteriorVector
                S X source.1)‖ ^ 2 :=
            sum_sq_abs_inner_signedBoundary_le_four_norm_sq
              ha hd (H (exactPrincipalMoleculeKernelInteriorVector
                S X source.1))
      _ ≤ ∑ source : MoleculeCenter S X K,
          (4 * eta ^ 4 / gamma ^ 2) *
            ‖exactPrincipalMoleculeBoundaryKernel S X source.1‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro source _hsource
        have hHsource :
            ‖H (exactPrincipalMoleculeKernelInteriorVector S X source.1)‖ ≤
              eta * ‖exactPrincipalMoleculeKernelInteriorVector
                S X source.1‖ := by
          simpa [H] using hH
            (exactPrincipalMoleculeKernelInteriorVector S X source.1)
        have hsource := norm_exactPrincipalMoleculeKernelInteriorSource_le
          (a := source.1) eta hH
        have hinverse :=
          gamma_mul_norm_exactPrincipalMoleculeKernelInteriorVector_le
            hS (ha source) (hroot source) gamma hgamma
            (hgap source) (hden source)
        have hscaled :
            gamma * ‖exactPrincipalMoleculeKernelInteriorVector
                S X source.1‖ ≤
              eta * ‖exactPrincipalMoleculeBoundaryKernel S X source.1‖ :=
          hinverse.trans hsource
        have hHsq :
            ‖H (exactPrincipalMoleculeKernelInteriorVector S X source.1)‖ ^ 2 ≤
              eta ^ 2 *
                ‖exactPrincipalMoleculeKernelInteriorVector S X source.1‖ ^ 2 := by
          simpa [mul_pow] using
            ((sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg heta (norm_nonneg _))).2 hHsource)
        have hkSq :
            ‖exactPrincipalMoleculeKernelInteriorVector S X source.1‖ ^ 2 ≤
              eta ^ 2 / gamma ^ 2 *
                ‖exactPrincipalMoleculeBoundaryKernel S X source.1‖ ^ 2 := by
          have hscaledSq :
              (gamma * ‖exactPrincipalMoleculeKernelInteriorVector
                  S X source.1‖) ^ 2 ≤
                (eta * ‖exactPrincipalMoleculeBoundaryKernel
                  S X source.1‖) ^ 2 :=
            (sq_le_sq₀
              (mul_nonneg hgamma.le (norm_nonneg _))
              (mul_nonneg heta (norm_nonneg _))).2 hscaled
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ (sq_pos_of_pos hgamma)).2
          simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hscaledSq
        calc
          4 * ‖H (exactPrincipalMoleculeKernelInteriorVector
              S X source.1)‖ ^ 2 ≤
              4 * (eta ^ 2 *
                ‖exactPrincipalMoleculeKernelInteriorVector S X source.1‖ ^ 2) := by
            gcongr
          _ ≤ 4 * (eta ^ 2 *
              (eta ^ 2 / gamma ^ 2 *
                ‖exactPrincipalMoleculeBoundaryKernel S X source.1‖ ^ 2)) := by
            gcongr
          _ = (4 * eta ^ 4 / gamma ^ 2) *
              ‖exactPrincipalMoleculeBoundaryKernel S X source.1‖ ^ 2 := by ring
      _ = (4 * eta ^ 4 / gamma ^ 2) *
          ∑ source : MoleculeCenter S X K,
            ‖exactPrincipalMoleculeBoundaryKernel S X source.1‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ (4 * eta ^ 4 / gamma ^ 2) * boundaryKernelBudget := by
        gcongr
  have hKB : matrixFrobeniusNorm KB ^ 2 ≤
      boundaryKernelBudget * residualBudget := by
    rw [matrixFrobeniusNorm_sq]
    calc
      (∑ output : MoleculeCenter S X K,
          ∑ source : MoleculeCenter S X K, ‖KB output source‖ ^ 2) ≤
          ∑ output : MoleculeCenter S X K,
            ∑ source : MoleculeCenter S X K,
              ‖exactPrincipalMoleculeBoundaryKernel S X output.1‖ ^ 2 *
                ‖exactPrincipalMoleculeResidual S X source.1‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro output _houtput
        apply Finset.sum_le_sum
        intro source _hsource
        by_cases hcoh : IsCoherentRawMoleculePair hS output source
        · simp only [KB, hcoh, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
          have hinner := abs_real_inner_le_norm
            (exactPrincipalMoleculeBoundaryKernel S X output.1)
            (exactPrincipalMoleculeResidual S X source.1)
          have hinnerSq :=
            (sq_le_sq₀ (abs_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
          simpa [mul_pow] using hinnerSq
        · simp only [KB, hcoh, ↓reduceIte, norm_zero]
          simpa only [pow_two, zero_mul] using
            mul_nonneg
              (sq_nonneg ‖exactPrincipalMoleculeBoundaryKernel S X output.1‖)
              (sq_nonneg ‖exactPrincipalMoleculeResidual S X source.1‖)
      _ = (∑ output : MoleculeCenter S X K,
            ‖exactPrincipalMoleculeBoundaryKernel S X output.1‖ ^ 2) *
          (∑ source : MoleculeCenter S X K,
            ‖exactPrincipalMoleculeResidual S X source.1‖ ^ 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro output _houtput
        rw [Finset.mul_sum]
      _ ≤ boundaryKernelBudget * residualBudget := by
        have hboundaryNonneg : 0 ≤ boundaryKernelBudget :=
          (show 0 ≤ ∑ output : MoleculeCenter S X K,
              ‖exactPrincipalMoleculeBoundaryKernel S X output.1‖ ^ 2 by
            positivity).trans hboundary
        calc
          (∑ output : MoleculeCenter S X K,
              ‖exactPrincipalMoleculeBoundaryKernel S X output.1‖ ^ 2) *
                (∑ source : MoleculeCenter S X K,
                  ‖exactPrincipalMoleculeResidual S X source.1‖ ^ 2) ≤
              boundaryKernelBudget *
                (∑ source : MoleculeCenter S X K,
                  ‖exactPrincipalMoleculeResidual S X source.1‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hboundary (by positivity)
          _ ≤ boundaryKernelBudget * residualBudget :=
            mul_le_mul_of_nonneg_left hresidual hboundaryNonneg
  have hnorm : matrixFrobeniusNorm
      (exactOneExitLocalCoherentCompressionResidual
        (S := S) (X := X) (K := K) hS) ≤
      matrixFrobeniusNorm C + matrixFrobeniusNorm KI +
        matrixFrobeniusNorm KB := by
    rw [hdecomp]
    linarith [matrixFrobeniusNorm_add_le (C + KI) KB,
      matrixFrobeniusNorm_add_le C KI]
  have hsq : matrixFrobeniusNorm
      (exactOneExitLocalCoherentCompressionResidual
        (S := S) (X := X) (K := K) hS) ^ 2 ≤
      3 * (matrixFrobeniusNorm C ^ 2 + matrixFrobeniusNorm KI ^ 2 +
        matrixFrobeniusNorm KB ^ 2) := by
    have hnormSq := (sq_le_sq₀ (matrixFrobeniusNorm_nonneg _)
      (add_nonneg
        (add_nonneg (matrixFrobeniusNorm_nonneg C)
          (matrixFrobeniusNorm_nonneg KI))
        (matrixFrobeniusNorm_nonneg KB))).2 hnorm
    nlinarith [sq_nonneg (matrixFrobeniusNorm C - matrixFrobeniusNorm KI),
      sq_nonneg (matrixFrobeniusNorm C - matrixFrobeniusNorm KB),
      sq_nonneg (matrixFrobeniusNorm KI - matrixFrobeniusNorm KB)]
  calc
    matrixFrobeniusNorm
        (exactOneExitLocalCoherentCompressionResidual
          (S := S) (X := X) (K := K) hS) ^ 2 ≤
        3 * (matrixFrobeniusNorm C ^ 2 + matrixFrobeniusNorm KI ^ 2 +
          matrixFrobeniusNorm KB ^ 2) := hsq
    _ ≤ 3 * (coreBudget +
        4 * eta ^ 4 / gamma ^ 2 * boundaryKernelBudget +
        boundaryKernelBudget * residualBudget) := by
      gcongr

/-- The boundary-kernel part of the exact molecule has the source-weighted
scale used by the terminal coherent-compression estimate. -/
theorem eventually_powerRange_exactPrincipalMoleculeBoundaryKernel_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
        InPowerRange theta X (a : ℕ) →
          ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 ≤
            C * (a : ℝ) * Real.log (X : ℝ) ^ 3 /
              ((X : ℝ) * Real.sqrt (X : ℝ)) := by
  let C : ℝ := 16 * 600 ^ 2 * 5632 * 8
  have hC : 0 < C := by norm_num [C]
  refine ⟨C, hC, ?_⟩
  filter_upwards [
      eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
        S hS htheta,
      eventually_powerRange_exactPrincipalMolecule_boundaryKernel_le
        S hS htheta,
      eventually_powerRange_moleculeStarEnergy_residualScaleBundle
        S hS htheta,
      eventually_powerRange_boundaryLeafSquareSum_div_starEnergy_fourth_le
        S hS htheta,
      eventually_ge_atTop 16]
      with X hwindow hkernel hscale hleaf hX
  intro a ha
  let A : ℝ := (a : ℕ)
  let x : ℝ := X
  let L : ℝ := Real.log x
  let mu : ℝ := moleculeStarEnergy S X a
  let lambda : ℝ := exactPrincipalMoleculeRoot S X a
  let k : ℝ := ‖exactPrincipalMoleculeBoundaryKernel S X a‖
  let Q : ℝ := boundaryLeafCountSquareSumOnStar S X
    (squareRootCutoff X) a
  obtain ⟨_haY, hd, hshift, _hsmall⟩ := hwindow a ha
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hL : 0 < L := by
    dsimp [L, x]
    exact Real.log_pos (by
      exact_mod_cast ((by norm_num : (1 : ℕ) < 16).trans_le hX))
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hlambdaLower : mu / 2 ≤ lambda := by
    have h := (abs_le.mp (show |lambda - mu| ≤ mu / 100 by
      simpa [lambda, mu] using hshift)).1
    nlinarith
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (half_pos hmu) hlambdaLower
  have hlambdaSq : mu ^ 2 / 4 ≤ lambda ^ 2 := by
    nlinarith [sq_nonneg (lambda - mu / 2)]
  have hkernel' :
      lambda ^ 2 * k ^ 2 ≤ 4 * (600 / mu ^ 2) ^ 2 * Q := by
    simpa [lambda, mu, k, Q] using hkernel a ha
  have hfirst : k ^ 2 ≤ 16 * 600 ^ 2 * (Q / mu ^ 6) := by
    calc
      k ^ 2 = (4 / mu ^ 2) * (mu ^ 2 / 4 * k ^ 2) := by
        field_simp [ne_of_gt hmu]
        <;> ring
      _ ≤ (4 / mu ^ 2) * (lambda ^ 2 * k ^ 2) := by
        gcongr
      _ ≤ (4 / mu ^ 2) * (4 * (600 / mu ^ 2) ^ 2 * Q) := by
        gcongr
      _ = 16 * 600 ^ 2 * (Q / mu ^ 6) := by
        field_simp [ne_of_gt hmu]
        <;> ring
  have hq : Q / mu ^ 4 ≤ 5632 * L ^ 2 / Real.sqrt x := by
    simpa [Q, mu, L, x] using hleaf a ha
  have hmuScale : x / (8 * A * L) ≤ mu ^ 2 := by
    simpa [x, A, L, mu] using (hscale a ha).1
  have hmuInv : 1 / mu ^ 2 ≤ 8 * A * L / x := by
    calc
      1 / mu ^ 2 ≤ 1 / (x / (8 * A * L)) :=
        one_div_le_one_div_of_le (by positivity) hmuScale
      _ = 8 * A * L / x := by
        field_simp [ne_of_gt hx, ne_of_gt hA, ne_of_gt hL]
        <;> ring
  have hquot :
      Q / mu ^ 6 ≤
        (5632 * L ^ 2 / Real.sqrt x) * (8 * A * L / x) := by
    calc
      Q / mu ^ 6 = (Q / mu ^ 4) * (1 / mu ^ 2) := by
        field_simp [ne_of_gt hmu]
        <;> ring
      _ ≤ (5632 * L ^ 2 / Real.sqrt x) * (1 / mu ^ 2) := by
        gcongr
      _ ≤ (5632 * L ^ 2 / Real.sqrt x) * (8 * A * L / x) := by
        gcongr
  calc
    k ^ 2 ≤ 16 * 600 ^ 2 * (Q / mu ^ 6) := hfirst
    _ ≤ 16 * 600 ^ 2 *
        ((5632 * L ^ 2 / Real.sqrt x) * (8 * A * L / x)) := by
      gcongr
    _ = C * A * L ^ 3 / (x * Real.sqrt x) := by
      dsimp [C]
      field_simp [ne_of_gt hx, ne_of_gt hsqrt]
      <;> ring
    _ = C * (a : ℝ) * Real.log (X : ℝ) ^ 3 /
        ((X : ℝ) * Real.sqrt (X : ℝ)) := by rfl

/-- Summed terminal-prefix boundary-kernel budget.  This discharges the
`boundaryKernelBudget` premise of the finite coherent Schur theorem on every
fixed power range below the square-root boundary. -/
theorem eventually_powerRange_sum_exactPrincipalMoleculeBoundaryKernel_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ K : ℕ,
        (K : ℝ) ≤ powerScale theta X →
          (∑ a : MoleculeCenter S X K,
              ‖exactPrincipalMoleculeBoundaryKernel S X a.1‖ ^ 2) ≤
            C * (K + 1 : ℝ) ^ 2 * Real.log (X : ℝ) ^ 3 /
              ((X : ℝ) * Real.sqrt (X : ℝ)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    eventually_powerRange_exactPrincipalMoleculeBoundaryKernel_sq_le_scale
      S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpoint, eventually_ge_atTop 16] with X hpointX hX
  intro K hK
  have hXone : (1 : ℕ) ≤ X := (by norm_num : (1 : ℕ) ≤ 16).trans hX
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hXone)
  have hx : 0 ≤ (X : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  have hcardNat := card_moleculeCenter_le_succ S X K
  have hcard :
      (Fintype.card (MoleculeCenter S X K) : ℝ) ≤ (K + 1 : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (∑ a : MoleculeCenter S X K,
        ‖exactPrincipalMoleculeBoundaryKernel S X a.1‖ ^ 2) ≤
        ∑ _a : MoleculeCenter S X K,
          C * (K + 1 : ℝ) * Real.log (X : ℝ) ^ 3 /
            ((X : ℝ) * Real.sqrt (X : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _ha
      have haPower : InPowerRange theta X (a.1 : ℕ) := by
        refine ⟨PrimeStar.Vertex.coe_pos a.1, ?_⟩
        have hle : ((a.1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast a.2
        exact hle.trans hK
      calc
        ‖exactPrincipalMoleculeBoundaryKernel S X a.1‖ ^ 2 ≤
            C * (a.1 : ℝ) * Real.log (X : ℝ) ^ 3 /
              ((X : ℝ) * Real.sqrt (X : ℝ)) := hpointX a.1 haPower
        _ ≤ C * (K + 1 : ℝ) * Real.log (X : ℝ) ^ 3 /
              ((X : ℝ) * Real.sqrt (X : ℝ)) := by
          gcongr
          exact_mod_cast (a.2.trans (Nat.le_succ K))
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) *
          (C * (K + 1 : ℝ) * Real.log (X : ℝ) ^ 3 /
            ((X : ℝ) * Real.sqrt (X : ℝ))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K + 1 : ℝ) *
          (C * (K + 1 : ℝ) * Real.log (X : ℝ) ^ 3 /
            ((X : ℝ) * Real.sqrt (X : ℝ))) := by
      gcongr
    _ = C * (K + 1 : ℝ) ^ 2 * Real.log (X : ℝ) ^ 3 /
          ((X : ℝ) * Real.sqrt (X : ℝ)) := by ring

/-- Pointwise residual energy of the exact molecule, charged by the first-exit
gap and the tuned small-prime scale. -/
theorem eventually_powerRange_exactPrincipalMoleculeResidual_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
        InPowerRange theta X (a : ℕ) →
          ‖exactPrincipalMoleculeResidual S X a‖ ^ 2 ≤
            C * (a : ℝ) / Real.log (X : ℝ) := by
  let C : ℝ :=
    10000 * 128 * PrimeStar.sqrtCutoffResidualConstant ^ 4
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num)
      (pow_pos PrimeStar.sqrtCutoffResidualConstant_pos 4)
  refine ⟨C, hC, ?_⟩
  filter_upwards [
      eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
        S hS htheta,
      eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap
        S hS htheta,
      eventually_powerRange_moleculeStarEnergy_residualScaleBundle
        S hS htheta,
      PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned,
      eventually_ge_atTop 16]
      with X hwindow hgapRoot hscale hresidual hX
  intro a ha
  obtain ⟨haY, hd, _hshift, _hsmall⟩ := hwindow a ha
  let mu : ℝ := moleculeStarEnergy S X a
  let eta : ℝ := PrimeStar.sqrtCutoffResidualScale X
  let gamma : ℝ := mu / 100
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  have heta : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hH : ∀ y : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          y‖ ≤ eta * ‖y‖ := by
    intro y
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S y
  have hinterior :
      gamma * ‖exactPrincipalMoleculeInteriorVector S X a‖ ≤ eta :=
    gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_smallPrime
      hS haY gamma eta heta (by simpa [gamma, mu] using hgapRoot a ha) hH
  have hinterior' :
      ‖exactPrincipalMoleculeInteriorVector S X a‖ ≤ eta / gamma :=
    (le_div_iff₀ hgamma).2 (by rw [mul_comm]; exact hinterior)
  have hres :
      ‖exactPrincipalMoleculeResidual S X a‖ ≤
        eta * ‖exactPrincipalMoleculeInteriorVector S X a‖ :=
    norm_exactPrincipalMoleculeResidual_le_smallPrime_mul_interior hS haY hH
  have hres' :
      ‖exactPrincipalMoleculeResidual S X a‖ ≤ eta ^ 2 / gamma := by
    calc
      ‖exactPrincipalMoleculeResidual S X a‖ ≤
          eta * ‖exactPrincipalMoleculeInteriorVector S X a‖ := hres
      _ ≤ eta * (eta / gamma) := by
        gcongr
      _ = eta ^ 2 / gamma := by
        field_simp [ne_of_gt hgamma]
  have hsq :
      ‖exactPrincipalMoleculeResidual S X a‖ ^ 2 ≤
        eta ^ 4 / gamma ^ 2 := by
    have hrhs : 0 ≤ eta ^ 2 / gamma :=
      div_nonneg (sq_nonneg eta) hgamma.le
    have := (sq_le_sq₀ (norm_nonneg _) hrhs).2 hres'
    calc
      ‖exactPrincipalMoleculeResidual S X a‖ ^ 2 ≤
          (eta ^ 2 / gamma) ^ 2 := this
      _ = eta ^ 4 / gamma ^ 2 := by
        field_simp [ne_of_gt hgamma]
  have hscale' :
      eta ^ 4 / mu ^ 2 ≤
        128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
          ((a : ℝ) / Real.log (X : ℝ)) := by
    simpa [eta, mu] using (hscale a ha).2
  have hgammaMu : gamma ^ 2 = mu ^ 2 / 10000 := by
    dsimp [gamma]
    ring
  calc
    ‖exactPrincipalMoleculeResidual S X a‖ ^ 2 ≤
        eta ^ 4 / gamma ^ 2 := hsq
    _ = 10000 * (eta ^ 4 / mu ^ 2) := by
      rw [hgammaMu]
      field_simp [ne_of_gt hmu]
    _ ≤ 10000 *
        (128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
          ((a : ℝ) / Real.log (X : ℝ))) := by
      gcongr
    _ = C * (a : ℝ) / Real.log (X : ℝ) := by
      dsimp [C]
      ring

/-- Summed terminal-prefix residual-energy budget.  This discharges the
`residualBudget` premise of the finite coherent Schur theorem on every fixed
power range below the square-root boundary. -/
theorem eventually_powerRange_sum_exactPrincipalMoleculeResidual_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ K : ℕ,
        (K : ℝ) ≤ powerScale theta X →
          (∑ a : MoleculeCenter S X K,
              ‖exactPrincipalMoleculeResidual S X a.1‖ ^ 2) ≤
            C * (K + 1 : ℝ) ^ 2 / Real.log (X : ℝ) := by
  obtain ⟨C, hC, hpoint⟩ :=
    eventually_powerRange_exactPrincipalMoleculeResidual_sq_le_scale
      S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpoint, eventually_ge_atTop 16] with X hpointX hX
  intro K hK
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast ((by norm_num : (1 : ℕ) < 16).trans_le hX))
  have hcardNat := card_moleculeCenter_le_succ S X K
  have hcard :
      (Fintype.card (MoleculeCenter S X K) : ℝ) ≤ (K + 1 : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (∑ a : MoleculeCenter S X K,
        ‖exactPrincipalMoleculeResidual S X a.1‖ ^ 2) ≤
        ∑ _a : MoleculeCenter S X K,
          C * (K + 1 : ℝ) / Real.log (X : ℝ) := by
      apply Finset.sum_le_sum
      intro a _ha
      have haPower : InPowerRange theta X (a.1 : ℕ) := by
        refine ⟨PrimeStar.Vertex.coe_pos a.1, ?_⟩
        have hle : ((a.1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast a.2
        exact hle.trans hK
      calc
        ‖exactPrincipalMoleculeResidual S X a.1‖ ^ 2 ≤
            C * (a.1 : ℝ) / Real.log (X : ℝ) := hpointX a.1 haPower
        _ ≤ C * (K + 1 : ℝ) / Real.log (X : ℝ) := by
          gcongr
          exact_mod_cast (a.2.trans (Nat.le_succ K))
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) *
          (C * (K + 1 : ℝ) / Real.log (X : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K + 1 : ℝ) *
          (C * (K + 1 : ℝ) / Real.log (X : ℝ)) := by
      gcongr
    _ = C * (K + 1 : ℝ) ^ 2 / Real.log (X : ℝ) := by
      ring

set_option maxHeartbeats 800000 in
/-- Signed-boundary form of the checked common-core coefficient majorant. -/
theorem inner_signedBoundary_smallPrime_signedInterior_eq_commonCoreResponse
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdb : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (r : PrimeStar.CanonicalDownIndex a)
    (houtput :
      (PrimeStar.canonicalDownTarget a r : ℕ) * (q : ℕ) = (b : ℕ))
    (hcut : squareRootCutoff X <
      (PrimeStar.canonicalUpTarget hS a q : ℕ))
    (hne : a ≠ b) :
    let core := PrimeStar.canonicalDownTarget a r
    let common := PrimeStar.canonicalUpTarget hS a q
    let response := PrimeStar.restrictEuclideanToFinset
      (insert common
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) core))
      (exactPrincipalMoleculeSignedInteriorVector S X a)
    inner ℝ
        (exactPrincipalMoleculeSignedBoundaryVector S X b)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeSignedInteriorVector S X a)) =
      inner ℝ
        (exactPrincipalMoleculeSignedBoundaryVector S X b)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          response) := by
  dsimp only
  let K : ℕ := max (a : ℕ) (b : ℕ)
  let source : MoleculeCenter S X K := ⟨a, Nat.le_max_left _ _⟩
  let output : MoleculeCenter S X K := ⟨b, Nat.le_max_right _ _⟩
  let gV := PrimeStar.canonicalDownTarget a r
  have hg : 0 < (gV : ℕ) := PrimeStar.Vertex.coe_pos gV
  have hgV : (gV : ℕ) = (gV : ℕ) := rfl
  have hqPrime : (q : ℕ).Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp q.property).1).2
  have hqS : (q : ℕ) ∉ S := (Finset.mem_filter.mp q.property).2.1
  have hqY : (q : ℕ) ≤ squareRootCutoff X :=
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp q.property).1).1
  have hrPrime : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.property
  have hrDvd : (r : ℕ) ∣ (a : ℕ) := Nat.dvd_of_mem_primeFactors r.property
  have hrS : (r : ℕ) ∉ S := fun hrMem =>
    PrimeStar.Vertex.not_dvd_of_mem a hrMem hrDvd
  have hrY : (r : ℕ) ≤ squareRootCutoff X :=
    (Nat.le_of_mem_primeFactors r.property).trans ha
  have hbr : (b : ℕ) * (r : ℕ) =
      (PrimeStar.canonicalUpTarget hS a q : ℕ) := by
    calc
      (b : ℕ) * (r : ℕ) =
          ((PrimeStar.canonicalDownTarget a r : ℕ) * (q : ℕ)) * (r : ℕ) := by
        rw [houtput]
      _ = ((PrimeStar.canonicalDownTarget a r : ℕ) * (r : ℕ)) * (q : ℕ) := by
        ac_rfl
      _ = (a : ℕ) * (q : ℕ) := by
        rw [PrimeStar.canonicalDownTarget_mul_coe]
      _ = (PrimeStar.canonicalUpTarget hS a q : ℕ) :=
        PrimeStar.canonicalUpTarget_coe hS a q
  have hrUpMem : (r : ℕ) ∈
      PrimeStar.canonicalUpPrimeLabels S X (squareRootCutoff X) b := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Nat.mem_primesLE.mpr ⟨hrY, hrPrime⟩, hrS, ?_⟩
    simpa [hbr] using
      (PrimeStar.Vertex.coe_le (PrimeStar.canonicalUpTarget hS a q) :
        _ ≤ X)
  let rUp : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) b :=
    ⟨r, hrUpMem⟩
  have haMul : (a : ℕ) = (gV : ℕ) * (rUp : ℕ) := by
    have := PrimeStar.canonicalDownTarget_mul_coe a r
    simpa [gV, rUp, mul_comm] using this.symm
  have hbMul : (b : ℕ) = (gV : ℕ) * (q : ℕ) := by
    simpa [gV] using houtput.symm
  have hneMC : source ≠ output := by
    intro h
    apply hne
    simpa [source, output] using congrArg Subtype.val h
  have hrestrict (eps : ℝ) :
      inner ℝ
          (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) b eps)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X
              (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X a)) =
        inner ℝ
          (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) b eps)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X
              (squareRootCutoff X)).adjMatrix ℝ)
            (PrimeStar.restrictEuclideanToFinset
              (insert (PrimeStar.canonicalUpTarget hS a q)
                (PrimeStar.largePrimeStarSupport S X
                  (squareRootCutoff X) gV))
              (exactPrincipalMoleculeSignedInteriorVector S X a))) := by
    simpa [source, output, gV] using
      (real_inner_signedOutput_smallPrime_signedInterior_eq_commonCore_of_data
        (S := S) (X := X) (K := K) (g := (gV : ℕ)) hS
        (source := source) (output := output) gV q rUp
        (by simpa [source] using ha)
        (by simpa [output] using hb)
        hg (by rfl) hqPrime hrPrime hqS hrS hqY hrY
        (by simpa [source, rUp] using haMul)
        (by simpa [output] using hbMul)
        (by simpa [source] using hcut) hneMC eps)
  have hdecomp :=
    exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hdb
  rw [hdecomp, inner_add_left, inner_add_left]
  simp only [real_inner_smul_left]
  rw [hrestrict 1, hrestrict (-1)]

set_option maxHeartbeats 800000 in
/-- Full signed-interior form of the common-core coefficient majorant. -/
theorem exists_orientedCoherent_downUp
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsourceY : (source.1 : ℕ) ≤ squareRootCutoff X)
    (hcoherent : IsCoherentRawMoleculePair hS source output) :
    ∃ g : ℕ, 0 < g ∧
      ∃ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) source.1,
        ∃ r : PrimeStar.CanonicalDownIndex source.1,
          (PrimeStar.canonicalDownTarget source.1 r : ℕ) = g ∧
          (PrimeStar.canonicalDownTarget source.1 r : ℕ) * (q : ℕ) =
            (output.1 : ℕ) ∧
          PrimeStar.canonicalUpTarget hS source.1 q ∈
            PrimeStar.firstExitIsolatedVertices S X
              (squareRootCutoff X) source.1 ∧
          squareRootCutoff X <
            (PrimeStar.canonicalUpTarget hS source.1 q : ℕ) ∧
          source.1 ≠ output.1 ∧
          (source.1 : ℕ).gcd (output.1 : ℕ) = g := by
  obtain ⟨g, hg, q, r, hq, hr, _hqS, _hrS, _hqY, _hrY, ha, hb, hcut⟩ :=
    exists_commonCore_of_isCoherentRawMoleculePair hS hcoherent
  have hrDvd : (r : ℕ) ∣ (source.1 : ℕ) :=
    ⟨g, by rw [ha, mul_comm]⟩
  have hrMem : (r : ℕ) ∈ (source.1 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hr, hrDvd, (PrimeStar.Vertex.coe_pos source.1).ne'⟩
  let rDown : PrimeStar.CanonicalDownIndex source.1 := ⟨r, hrMem⟩
  have hdown :
      (PrimeStar.canonicalDownTarget source.1 rDown : ℕ) = g := by
    have hmul := PrimeStar.canonicalDownTarget_mul_coe source.1 rDown
    apply Nat.eq_of_mul_eq_mul_right hr.pos
    calc
      (PrimeStar.canonicalDownTarget source.1 rDown : ℕ) * (r : ℕ) =
          (source.1 : ℕ) := hmul
      _ = g * (r : ℕ) := ha
  have houtputEq :
      (PrimeStar.canonicalDownTarget source.1 rDown : ℕ) * (q : ℕ) =
        (output.1 : ℕ) := by
    rw [hdown, hb]
  have hiso : PrimeStar.canonicalUpTarget hS source.1 q ∈
      PrimeStar.firstExitIsolatedVertices S X
        (squareRootCutoff X) source.1 := by
    apply PrimeStar.mem_firstExitIsolatedVertices.mpr
    constructor
    · simpa [PrimeStar.canonicalExitTarget] using
        (PrimeStar.canonicalExitTarget_mem_smallPrimeFirstExitSupport
          (Y := squareRootCutoff X) hS hsourceY
          (Sum.inl q : PrimeStar.CanonicalExitIndex S X
            (squareRootCutoff X) source.1))
    · have hqData := Finset.mem_filter.mp q.property
      exact PrimeStar.canonicalUpTarget_isIsolated_of_cutoff_lt
        hsourceY (PrimeStar.sqrtCutoff_condition X)
        (Nat.mem_primesLE.mp hqData.1).2
        (Nat.mem_primesLE.mp hqData.1).1
        (PrimeStar.canonicalUpTarget_coe hS source.1 q) hcut
  have hne : source.1 ≠ output.1 := by
    intro h
    exact hcoherent.1 (Subtype.ext h)
  have hrqNe : (r : ℕ) ≠ (q : ℕ) := by
    intro h
    apply hne
    apply Subtype.ext
    apply Fin.ext
    rw [ha, hb, h]
  have hcoprime : Nat.Coprime (r : ℕ) (q : ℕ) :=
    (Nat.coprime_primes hr hq).2 hrqNe
  have hgcd : (source.1 : ℕ).gcd (output.1 : ℕ) = g := by
    rw [ha, hb, Nat.gcd_mul_left, hcoprime.gcd_eq_one, mul_one]
  exact ⟨g, hg, q, rDown, hdown, houtputEq, hiso, hcut, hne, hgcd⟩

set_option maxHeartbeats 800000 in
theorem shiftedActualDownStarResolvent_apply_not_mem
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {lambda mu c0 : ℝ}
    {v : PrimeStar.Vertex S X}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target)
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y target)
    (hvP : v ∉ P) :
    shiftedActualDownStarResolvent S X Y target P lambda mu c0 v =
      ((lambda * c0 + (P.card : ℝ) * (c0 / mu)) /
          (lambda ^ 2 -
            (PrimeStar.largePrimeStarDegree S X Y target : ℝ))) /
        lambda := by
  classical
  let source := PrimeStar.actualDownStarFirstExit S X Y target P mu c0
  have hsourceCenter : source target = c0 := by
    simp [source, PrimeStar.actualDownStarFirstExit]
  have hsourceLeaf : source v = 0 := by
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
  ring

/-- Dimensionless form of the unselected-leaf response. -/
theorem shiftedActualDownStarResolvent_apply_not_mem_normalized
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {P : Finset (PrimeStar.Vertex S X)} {z s mu c0 eps : ℝ}
    {v : PrimeStar.Vertex S X}
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y target)
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X Y target)
    (hvP : v ∉ P)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hdegree : (PrimeStar.largePrimeStarDegree S X Y target : ℝ) =
      s * mu ^ 2)
    (heps : eps ^ 2 = 1) (hmu : mu ≠ 0) (hz : z ≠ 0)
    (hsep : z ^ 2 - s ≠ 0) :
    shiftedActualDownStarResolvent S X Y target P
        (z * mu) (eps * mu) c0 v =
      c0 / mu ^ 2 * ((z + eps) / (z * (z ^ 2 - s))) := by
  rw [shiftedActualDownStarResolvent_apply_not_mem hP hvLeaf hvP,
    hcard, hdegree]
  have heps0 : eps ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at heps
    norm_num at heps
  field_simp [hmu, hz, heps0, hsep]
  ring_nf at heps ⊢
  rw [heps]
  ring

/-- On an unselected leaf of a canonical down-star, the signed interior has
only the centre-mediated leaf value. -/
theorem exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf_not_mem
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a)
    {v : PrimeStar.Vertex S X}
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q))
    (hvP : v ∉ PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q) q)
    {z s : ℝ}
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegree :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hz : z ≠ 0) (hsep : z ^ 2 - s ≠ 0) :
    exactPrincipalMoleculeSignedInteriorVector S X a v =
      1 / moleculeStarEnergy S X a ^ 2 *
        ((z * (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
                  exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) +
              (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
                  exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))) /
            (z * (z ^ 2 - s))) := by
  let target := PrimeStar.canonicalDownTarget a q
  let P := PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) target q
  let mu := moleculeStarEnergy S X a
  have hmu : mu ≠ 0 := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hroot : exactPrincipalMoleculeRoot S X a ≠ 0 := by
    rw [hrootEq]
    exact mul_ne_zero hz hmu
  have hP : P ⊆ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) target :=
    PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves target
  have hcard : (P.card : ℝ) = mu ^ 2 := by
    calc
      (P.card : ℝ) =
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) := by
            exact_mod_cast
              PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
      _ = mu ^ 2 := by
        simpa [mu] using (moleculeStarEnergy_sq S X a).symm
  have hmode (eps : ℝ) (heps : eps ^ 2 = 1) :
      exactBoundaryModeInteriorVector S X a eps v =
        shiftedActualDownStarResolvent S X (squareRootCutoff X) target P
          (z * mu) (eps * mu) (Real.sqrt 2)⁻¹ v := by
    have hrestrict := congrArg (fun x : MoleculeAmbient S X ↦ x v)
      (restrict_exactBoundaryModeInteriorVector_eq_canonicalDownResolvent
        hS ha hd heps hroot q)
    rw [PrimeStar.restrictEuclideanToFinset_apply,
      if_pos (PrimeStar.mem_largePrimeStarSupport.mpr
        (Or.inr (PrimeStar.mem_largePrimeLeaves.mp
          (by simpa [target] using hvLeaf))))]
      at hrestrict
    rw [hrootEq,
      largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd]
      at hrestrict
    exact hrestrict
  have hp := shiftedActualDownStarResolvent_apply_not_mem_normalized
    (target := target) (P := P) (z := z) (s := s) (mu := mu)
    (c0 := (Real.sqrt 2)⁻¹) (eps := (1 : ℝ)) (v := v)
    hP (by simpa [target] using hvLeaf) (by simpa [P, target] using hvP)
      hcard (by simpa [target, mu] using hdegree)
      (by norm_num) hmu hz hsep
  have hm := shiftedActualDownStarResolvent_apply_not_mem_normalized
    (target := target) (P := P) (z := z) (s := s) (mu := mu)
    (c0 := (Real.sqrt 2)⁻¹) (eps := (-1 : ℝ)) (v := v)
    hP (by simpa [target] using hvLeaf) (by simpa [P, target] using hvP)
      hcard (by simpa [target, mu] using hdegree)
      (by norm_num) hmu hz hsep
  rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hmode 1 (by norm_num), hmode (-1) (by norm_num), hp, hm]
  unfold exactPrincipalMoleculeBoundarySourceAmplitude
  dsimp [mu]
  have hsqrt2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hmu, hz, hsep, hsqrt2]
  ring

private theorem abs_selected_downLeafCoefficient_le
    {z s mu alpha beta delta : ℝ}
    (hmu : 0 < mu) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsep : delta ≤ |z ^ 2 - s|)
    (halpha : |alpha| ≤ 2) (hbeta : |beta| ≤ 2) :
    |1 / mu ^ 2 *
        (beta / z + (z * alpha + beta) / (z * (z ^ 2 - s)))| ≤
      20 / delta * (1 / mu ^ 2) := by
  have hbetaDiv : |beta / z| ≤ 4 := by
    rw [abs_div]
    have h := div_le_div₀ (by positivity : (0 : ℝ) ≤ 2)
      hbeta (by norm_num : (0 : ℝ) < 1 / 2) hzLower
    norm_num at h
    exact h
  have hza : |z * alpha + beta| ≤ 6 := by
    calc
      |z * alpha + beta| ≤ |z * alpha| + |beta| := abs_add_le _ _
      _ = |z| * |alpha| + |beta| := by rw [abs_mul]
      _ ≤ 6 := by nlinarith [abs_nonneg z, abs_nonneg alpha, abs_nonneg beta]
  have hfirstFrac : |(z * alpha + beta) / (z ^ 2 - s)| ≤ 6 / delta := by
    rw [abs_div]
    exact div_le_div₀ (by norm_num) hza hdelta hsep
  have hfrac : |(z * alpha + beta) / (z * (z ^ 2 - s))| ≤ 12 / delta := by
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      norm_num at hzLower
    have hden0 : z ^ 2 - s ≠ 0 := by
      intro hs0
      rw [hs0, abs_zero] at hsep
      linarith
    rw [show (z * alpha + beta) / (z * (z ^ 2 - s)) =
      ((z * alpha + beta) / (z ^ 2 - s)) / z by
        field_simp [hz0, hden0]
        <;> ring, abs_div]
    have h := div_le_div₀ (by positivity : 0 ≤ 6 / delta)
      hfirstFrac (by norm_num : (0 : ℝ) < 1 / 2) hzLower
    have hcalc : (6 / delta) / (1 / 2 : ℝ) = 12 / delta := by
      ring
    rw [hcalc] at h
    exact h
  have hsum :
      |beta / z + (z * alpha + beta) / (z * (z ^ 2 - s))| ≤
        20 / delta := by
    calc
      _ ≤ |beta / z| + |(z * alpha + beta) / (z * (z ^ 2 - s))| :=
        abs_add_le _ _
      _ ≤ 4 + 12 / delta := add_le_add hbetaDiv hfrac
      _ ≤ 20 / delta := by
        have hInv : 1 ≤ 1 / delta := by
          rw [le_div_iff₀ hdelta]
          simpa using hdeltaOne
        have h4 : (4 : ℝ) ≤ 8 / delta := by
          rw [le_div_iff₀ hdelta]
          nlinarith
        calc
          4 + 12 / delta ≤ 8 / delta + 12 / delta :=
            by simpa [add_comm] using add_le_add_right h4 (12 / delta)
          _ = 20 / delta := by ring
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / mu ^ 2)]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 / mu ^ 2))

private theorem abs_unselected_downLeafCoefficient_le
    {z s mu alpha beta delta : ℝ}
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsep : delta ≤ |z ^ 2 - s|)
    (halpha : |alpha| ≤ 2) (hbeta : |beta| ≤ 2) :
    |1 / mu ^ 2 * ((z * alpha + beta) / (z * (z ^ 2 - s)))| ≤
      20 / delta * (1 / mu ^ 2) := by
  have hza : |z * alpha + beta| ≤ 6 := by
    calc
      |z * alpha + beta| ≤ |z * alpha| + |beta| := abs_add_le _ _
      _ = |z| * |alpha| + |beta| := by rw [abs_mul]
      _ ≤ 6 := by nlinarith [abs_nonneg z, abs_nonneg alpha, abs_nonneg beta]
  have hfirstFrac : |(z * alpha + beta) / (z ^ 2 - s)| ≤ 6 / delta := by
    rw [abs_div]
    exact div_le_div₀ (by norm_num) hza hdelta hsep
  have hfrac : |(z * alpha + beta) / (z * (z ^ 2 - s))| ≤ 12 / delta := by
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      norm_num at hzLower
    have hden0 : z ^ 2 - s ≠ 0 := by
      intro hs0
      rw [hs0, abs_zero] at hsep
      linarith
    rw [show (z * alpha + beta) / (z * (z ^ 2 - s)) =
      ((z * alpha + beta) / (z ^ 2 - s)) / z by
        field_simp [hz0, hden0]
        <;> ring, abs_div]
    have h := div_le_div₀ (by positivity : 0 ≤ 6 / delta)
      hfirstFrac (by norm_num : (0 : ℝ) < 1 / 2) hzLower
    have hcalc : (6 / delta) / (1 / 2 : ℝ) = 12 / delta := by
      ring
    rw [hcalc] at h
    exact h
  have hfrac' : |(z * alpha + beta) / (z * (z ^ 2 - s))| ≤ 20 / delta := by
    have h12 : (12 : ℝ) / delta ≤ 20 / delta := by
      exact div_le_div_of_nonneg_right (by norm_num) hdelta.le
    exact hfrac.trans h12
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / mu ^ 2)]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hfrac' (by positivity : 0 ≤ 1 / mu ^ 2))

private theorem abs_downStarCenterCoefficient_le
    {z s mu alpha beta delta : ℝ}
    (hmu : 0 < mu) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsep : delta ≤ |z ^ 2 - s|)
    (halpha : |alpha| ≤ 2) (hbeta : |beta| ≤ 2) :
    |alpha / (z * mu) + (z * alpha + beta) / (mu * (z ^ 2 - s))| ≤
      20 / delta * (1 / mu) := by
  have hfirst : |alpha / z| ≤ 4 := by
    rw [abs_div]
    have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
      halpha (by norm_num : (0 : ℝ) < 1 / 2) hzLower
    norm_num at h
    exact h
  have hza : |z * alpha + beta| ≤ 6 := by
    calc
      |z * alpha + beta| ≤ |z * alpha| + |beta| := abs_add_le _ _
      _ = |z| * |alpha| + |beta| := by rw [abs_mul]
      _ ≤ 6 := by nlinarith [abs_nonneg z, abs_nonneg alpha, abs_nonneg beta]
  have hsecond : |(z * alpha + beta) / (z ^ 2 - s)| ≤ 6 / delta := by
    rw [abs_div]
    exact div_le_div₀ (by norm_num) hza hdelta hsep
  have hrearrange :
      alpha / (z * mu) + (z * alpha + beta) / (mu * (z ^ 2 - s)) =
        (1 / mu) * (alpha / z + (z * alpha + beta) / (z ^ 2 - s)) := by
    field_simp [hmu.ne']
  rw [hrearrange, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / mu)]
  have hscaled : (1 / mu) *
      |alpha / z + (z * alpha + beta) / (z ^ 2 - s)| ≤
      (1 / mu) * (20 / delta) :=
    mul_le_mul_of_nonneg_left (by
      calc
        |alpha / z + (z * alpha + beta) / (z ^ 2 - s)| ≤
            |alpha / z| + |(z * alpha + beta) / (z ^ 2 - s)| := abs_add_le _ _
        _ ≤ 4 + 6 / delta := add_le_add hfirst hsecond
        _ ≤ 20 / delta := by
          have h4 : (4 : ℝ) ≤ 14 / delta := by
            rw [le_div_iff₀ hdelta]
            nlinarith
          calc
            4 + 6 / delta ≤ 14 / delta + 6 / delta := by
              simpa [add_comm] using add_le_add_right h4 (6 / delta)
            _ = 20 / delta := by ring) (by positivity)
  simpa [mul_comm] using hscaled

/-- Every leaf of a canonical down-star obeys the same safe majorant,
whether or not it belongs to the selected first-exit leaf set. -/
theorem abs_exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf_le
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a)
    {v : PrimeStar.Vertex S X}
    (hvLeaf : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q))
    {z s delta : ℝ}
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegree :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsepLower : delta ≤ |z ^ 2 - s|) :
    |exactPrincipalMoleculeSignedInteriorVector S X a v| ≤
      20 / delta * (1 / moleculeStarEnergy S X a ^ 2) := by
  let mu := moleculeStarEnergy S X a
  let alpha :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  let beta :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    positivity
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0, abs_zero] at hzLower
    norm_num at hzLower
  have hsep : z ^ 2 - s ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hsepLower
    linarith
  have hplus :
      |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd (by norm_num)
  have hminus :
      |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd (by norm_num)
  have halpha : |alpha| ≤ 2 := by
    dsimp [alpha]
    calc
      |_ + _| ≤
          |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| +
            |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| :=
        abs_add_le _ _
      _ ≤ 2 := by linarith
  have hbeta : |beta| ≤ 2 := by
    dsimp [beta]
    calc
      |_ - _| ≤
          |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| +
            |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| :=
        abs_sub _ _
      _ ≤ 2 := by linarith
  by_cases hvP : v ∈ PrimeStar.canonicalDownLeaves S X
      (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q) q
  · rw [exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf
      hS ha hd q hvLeaf hvP hrootEq hdegree hz hsep]
    exact abs_selected_downLeafCoefficient_le hmu hdelta hdeltaOne
      hzLower hzUpper hsepLower halpha hbeta
  · rw [exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf_not_mem
      hS ha hd q hvLeaf hvP hrootEq hdegree hz hsep]
    exact abs_unselected_downLeafCoefficient_le hmu hdelta
      hzLower hzUpper hsepLower halpha hbeta

/-- Coordinatewise centre/leaf bounds imply a matching bound on either
normalized signed output-star coefficient. -/
theorem abs_real_inner_signedNormalizedStarMode_le_of_leaf_bound
    {S : Finset ℕ} {X Y : ℕ} {target : PrimeStar.Vertex S X}
    {x : EuclideanSpace ℝ (PrimeStar.Vertex S X)}
    {centerBound leafBound eps : ℝ}
    (heps : eps ^ 2 = 1)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y target)
    (hcenterBound : 0 ≤ centerBound) (hleafBound : 0 ≤ leafBound)
    (hcenter : |x target| ≤ centerBound)
    (hleaf : ∀ v ∈ PrimeStar.largePrimeLeaves S X Y target,
      |x v| ≤ leafBound) :
    |inner ℝ
      (PrimeStar.largePrimeNormalizedStarMode S X Y target eps) x| ≤
      (Real.sqrt 2)⁻¹ *
        (centerBound +
          Real.sqrt (PrimeStar.largePrimeStarDegree S X Y target : ℝ) *
            leafBound) := by
  classical
  let F := PrimeStar.largePrimeStarSupport S X Y target
  have hxData :
      PrimeStar.restrictEuclideanToFinset F x =
        PrimeStar.largePrimeStarDataVector S X Y target (x target)
          (fun v ↦ x v) := by
    ext v
    by_cases hvt : v = target
    · subst v
      simp [F]
    · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X Y target
      · rw [PrimeStar.restrictEuclideanToFinset_apply, if_pos (by
            simp [F, PrimeStar.largePrimeStarSupport, hvleaf])]
        rw [PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
      · rw [PrimeStar.restrictEuclideanToFinset_apply, if_neg (by
            simp [F, PrimeStar.largePrimeStarSupport, hvt, hvleaf])]
        rw [PrimeStar.largePrimeStarDataVector_outside _ _ hvt hvleaf]
  rw [real_inner_normalizedStarMode_restrict_starSupport, hxData,
    largePrimeNormalizedStarMode_eq_starDataVector heps hd,
    PrimeStar.largePrimeStarDataVector_inner,
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd]
  let d : ℝ := PrimeStar.largePrimeStarDegree S X Y target
  have hdPos : 0 < d := by
    dsimp [d]
    exact_mod_cast hd
  have hsqrtPos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdPos
  have hsqrtSq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdPos.le
  have hepsAbs : |eps| = 1 := by
    have : |eps| ^ 2 = 1 := by rw [sq_abs, heps]
    nlinarith [abs_nonneg eps]
  have hinvSqrtTwo : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  have hcenterTerm :
      |(Real.sqrt 2)⁻¹ * x target| ≤
        (Real.sqrt 2)⁻¹ * centerBound := by
    rw [abs_mul, abs_of_nonneg hinvSqrtTwo]
    exact mul_le_mul_of_nonneg_left hcenter hinvSqrtTwo
  have hleafCoeff :
      |(Real.sqrt 2)⁻¹ / (eps * Real.sqrt d)| =
        (Real.sqrt 2)⁻¹ / Real.sqrt d := by
    rw [abs_div, abs_mul, hepsAbs, one_mul,
      abs_of_nonneg hinvSqrtTwo, abs_of_pos hsqrtPos]
  have hsum :
      |∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          ((Real.sqrt 2)⁻¹ / (eps * Real.sqrt d)) * x v| ≤
        d * ((Real.sqrt 2)⁻¹ / Real.sqrt d * leafBound) := by
    calc
      _ ≤ ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          |((Real.sqrt 2)⁻¹ / (eps * Real.sqrt d)) * x v| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ PrimeStar.largePrimeLeaves S X Y target,
          ((Real.sqrt 2)⁻¹ / Real.sqrt d * leafBound) := by
        gcongr with v hv
        rw [abs_mul, hleafCoeff]
        exact mul_le_mul_of_nonneg_left (hleaf v hv) (by positivity)
      _ = d * ((Real.sqrt 2)⁻¹ / Real.sqrt d * leafBound) := by
        simp [d, PrimeStar.largePrimeStarDegree, nsmul_eq_mul]
  have hsum' :
      |∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          ((Real.sqrt 2)⁻¹ / (eps * Real.sqrt d)) * x v| ≤
        (Real.sqrt 2)⁻¹ * (Real.sqrt d * leafBound) := by
    calc
      _ ≤ d * ((Real.sqrt 2)⁻¹ / Real.sqrt d * leafBound) := hsum
      _ = (Real.sqrt 2)⁻¹ * (Real.sqrt d * leafBound) := by
        field_simp [hsqrtPos.ne']
        nlinarith
  calc
    |(Real.sqrt 2)⁻¹ * x target +
        ∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          ((Real.sqrt 2)⁻¹ / (eps * Real.sqrt d)) * x v| ≤
      |(Real.sqrt 2)⁻¹ * x target| +
        |∑ v ∈ PrimeStar.largePrimeLeaves S X Y target,
          ((Real.sqrt 2)⁻¹ / (eps * Real.sqrt d)) * x v| := abs_add_le _ _
    _ ≤ (Real.sqrt 2)⁻¹ * centerBound +
        (Real.sqrt 2)⁻¹ * (Real.sqrt d * leafBound) :=
      add_le_add hcenterTerm hsum'
    _ = (Real.sqrt 2)⁻¹ *
        (centerBound + Real.sqrt d * leafBound) := by ring

/-- Unoriented coherent common-core bound.  The selected and unselected
core leaves are treated separately, so no comparison between the two prime
labels is required. -/
theorem abs_real_inner_signedOutputStar_smallPrime_commonCoreSignedResponse_le_unoriented
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdb : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (r : PrimeStar.CanonicalDownIndex a)
    (houtput :
      (PrimeStar.canonicalDownTarget a r : ℕ) * (q : ℕ) = (b : ℕ))
    (hiso : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.firstExitIsolatedVertices S X (squareRootCutoff X) a)
    {eps z s tau delta : ℝ} (heps : eps ^ 2 = 1)
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegreeCore :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a r) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hsqrtOutput :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) b : ℝ) =
        moleculeStarEnergy S X a * tau)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsepLower : delta ≤ |z ^ 2 - s|) :
    let core := PrimeStar.canonicalDownTarget a r
    let common := PrimeStar.canonicalUpTarget hS a q
    let response := PrimeStar.restrictEuclideanToFinset
      (insert common
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) core))
      (exactPrincipalMoleculeSignedInteriorVector S X a)
    |inner ℝ
      (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) b eps)
      ((Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).adjMatrix ℝ)) response)| ≤
      40 / delta *
        (1 / moleculeStarEnergy S X a +
          |tau| / moleculeStarEnergy S X a) := by
  dsimp only
  let mu := moleculeStarEnergy S X a
  let alpha :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  let beta :=
    exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
      exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)
  let core := PrimeStar.canonicalDownTarget a r
  let common := PrimeStar.canonicalUpTarget hS a q
  let x := exactPrincipalMoleculeSignedInteriorVector S X a
  let response := PrimeStar.restrictEuclideanToFinset
    (insert common
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) core)) x
  let y := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) response
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    positivity
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0, abs_zero] at hzLower
    norm_num at hzLower
  have hsep : z ^ 2 - s ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hsepLower
    linarith
  have hroot : exactPrincipalMoleculeRoot S X a ≠ 0 := by
    rw [hrootEq]
    exact mul_ne_zero hz hmu.ne'
  have hqData := Finset.mem_filter.mp q.property
  have hqPrime : (q : ℕ).Prime := (Nat.mem_primesLE.mp hqData.1).2
  have hqY : (q : ℕ) ≤ squareRootCutoff X :=
    (Nat.mem_primesLE.mp hqData.1).1
  have hrPrime : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.property
  have hrDvd : (r : ℕ) ∣ (a : ℕ) := Nat.dvd_of_mem_primeFactors r.property
  have hrS : (r : ℕ) ∉ S := by
    intro hrMem
    exact PrimeStar.Vertex.not_dvd_of_mem a hrMem hrDvd
  have hrY : (r : ℕ) ≤ squareRootCutoff X :=
    (Nat.le_of_mem_primeFactors r.property).trans ha
  have hcoreY : (core : ℕ) ≤ squareRootCutoff X := by
    dsimp [core]
    exact (Nat.div_le_self _ _).trans ha
  have hcommon : (b : ℕ) * (r : ℕ) = (common : ℕ) := by
    calc
      (b : ℕ) * (r : ℕ) = ((core : ℕ) * (q : ℕ)) * (r : ℕ) := by
        rw [houtput]
      _ = ((core : ℕ) * (r : ℕ)) * (q : ℕ) := by ac_rfl
      _ = (a : ℕ) * (q : ℕ) := by
        dsimp [core]
        rw [PrimeStar.canonicalDownTarget_mul_coe]
      _ = (common : ℕ) := by
        dsimp [common]
  have hplus :
      |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hda (by norm_num)
  have hminus :
      |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hda (by norm_num)
  have halpha : |alpha| ≤ 2 := by
    dsimp [alpha]
    calc
      |_ + _| ≤
          |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| +
            |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| :=
        abs_add_le _ _
      _ ≤ 2 := by linarith
  have hbeta : |beta| ≤ 2 := by
    dsimp [beta]
    calc
      |_ - _| ≤
          |exactPrincipalMoleculeBoundarySourceAmplitude S X a 1| +
            |exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)| :=
        abs_sub _ _
      _ ≤ 2 := by linarith
  have hcenterEq : y b =
      alpha / (z * mu) + (z * alpha + beta) / (mu * (z ^ 2 - s)) := by
    have hrow := smallPrime_mulVec_restrict_commonCoreSupport_apply_outputCenter
      hcoreY hqPrime hqData.2.1 hqY hrPrime hrS hrY houtput hcommon x
    have hisolated :=
      exactPrincipalMoleculeSignedInteriorVector_apply_isolatedCanonicalUpTarget
        hS ha hda q hiso hroot
    have hdown :=
      exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownTarget
        hS ha hda r hrootEq hdegreeCore hz hsep
    dsimp [y, response]
    rw [hrow]
    change x common + x core = _
    rw [show x common = alpha / exactPrincipalMoleculeRoot S X a by
      simpa [x, common, alpha] using hisolated]
    rw [show x core = (z * alpha + beta) / (mu * (z ^ 2 - s)) by
      simpa [x, core, mu, alpha, beta] using hdown]
    rw [hrootEq]
  have hcenter : |y b| ≤ 20 / delta * (1 / mu) := by
    rw [hcenterEq]
    exact abs_downStarCenterCoefficient_le hmu hdelta hdeltaOne
      hzLower hzUpper hsepLower halpha hbeta
  have hleaf : ∀ w ∈ PrimeStar.largePrimeLeaves S X
      (squareRootCutoff X) b,
      |y w| ≤ 20 / delta * (1 / mu ^ 2) := by
    intro w hw
    obtain ⟨v, hvLeaf, hrow⟩ :=
      smallPrime_mulVec_restrict_commonCoreSupport_apply_outputLeaf_unoriented
        hS (PrimeStar.sqrtCutoff_condition X) hcoreY hb
        hqPrime hqData.2.1 hqY hrPrime hrS hrY
        houtput hcommon hw x
    dsimp [y, response]
    rw [hrow]
    exact abs_exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf_le
      hS ha hda r (by simpa [core] using hvLeaf)
      hrootEq hdegreeCore hdelta hdeltaOne hzLower hzUpper hsepLower
  have hproj := abs_real_inner_signedNormalizedStarMode_le_of_leaf_bound
    heps hdb (by positivity : 0 ≤ 20 / delta * (1 / mu))
    (by positivity : 0 ≤ 20 / delta * (1 / mu ^ 2)) hcenter hleaf
  have htau : 0 ≤ tau := by
    have hsqrtNonneg : 0 ≤ Real.sqrt
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b : ℝ) :=
      Real.sqrt_nonneg _
    rw [hsqrtOutput] at hsqrtNonneg
    exact nonneg_of_mul_nonneg_left
      (by simpa [mu, mul_comm] using hsqrtNonneg) hmu
  have hsqrtTwoInvLe : (Real.sqrt 2)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (Real.sqrt_pos.2 (by norm_num))).2
      (Real.one_le_sqrt.mpr (by norm_num))
  calc
    |inner ℝ
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) b eps) y| ≤
      (Real.sqrt 2)⁻¹ *
        (20 / delta * (1 / mu) +
          Real.sqrt
            (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b : ℝ) *
              (20 / delta * (1 / mu ^ 2))) := hproj
    _ ≤ 20 / delta * (1 / mu + |tau| / mu) := by
      rw [hsqrtOutput, abs_of_nonneg htau]
      have hparen : 0 ≤
          20 / delta * (1 / mu) +
            (mu * tau) * (20 / delta * (1 / mu ^ 2)) := by positivity
      calc
        _ ≤ 1 * (20 / delta * (1 / mu) +
            (mu * tau) * (20 / delta * (1 / mu ^ 2))) := by gcongr
        _ = 20 / delta * (1 / mu + tau / mu) := by
          field_simp [hmu.ne', hdelta.ne']
    _ ≤ 40 / delta * (1 / mu + |tau| / mu) := by
      have hsumNonneg : 0 ≤ 1 / mu + |tau| / mu := by positivity
      apply mul_le_mul_of_nonneg_right _ hsumNonneg
      exact div_le_div_of_nonneg_right (by norm_num) hdelta.le

/-- Signed-boundary version of the unoriented common-core estimate. -/
theorem abs_inner_signedBoundary_smallPrime_commonCoreSignedResponse_le_unoriented
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdb : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (r : PrimeStar.CanonicalDownIndex a)
    (houtput :
      (PrimeStar.canonicalDownTarget a r : ℕ) * (q : ℕ) = (b : ℕ))
    (hiso : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.firstExitIsolatedVertices S X (squareRootCutoff X) a)
    {z s tau delta : ℝ}
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegreeCore :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a r) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hsqrtOutput :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) b : ℝ) =
        moleculeStarEnergy S X a * tau)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsepLower : delta ≤ |z ^ 2 - s|) :
    let core := PrimeStar.canonicalDownTarget a r
    let common := PrimeStar.canonicalUpTarget hS a q
    let response := PrimeStar.restrictEuclideanToFinset
      (insert common
        (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) core))
      (exactPrincipalMoleculeSignedInteriorVector S X a)
    |inner ℝ
      (exactPrincipalMoleculeSignedBoundaryVector S X b)
      ((Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X
          (squareRootCutoff X)).adjMatrix ℝ)) response)| ≤
      80 / delta *
        (1 / moleculeStarEnergy S X a +
          |tau| / moleculeStarEnergy S X a) := by
  dsimp only
  have hplus :=
    abs_real_inner_signedOutputStar_smallPrime_commonCoreSignedResponse_le_unoriented
      hS ha hb hda hdb q r houtput hiso
      (by norm_num : (1 : ℝ) ^ 2 = 1) hrootEq hdegreeCore hsqrtOutput
      hdelta hdeltaOne hzLower hzUpper hsepLower
  have hminus :=
    abs_real_inner_signedOutputStar_smallPrime_commonCoreSignedResponse_le_unoriented
      hS ha hb hda hdb q r houtput hiso
      (by norm_num : (-1 : ℝ) ^ 2 = 1) hrootEq hdegreeCore hsqrtOutput
      hdelta hdeltaOne hzLower hzUpper hsepLower
  have hdecomp :=
    exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hdb
  have hcp :
      |exactPrincipalMoleculeBoundaryModeCoefficient S X b 1| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one hdb (by norm_num)
  have hcm :
      |exactPrincipalMoleculeBoundaryModeCoefficient S X b (-1)| ≤ 1 :=
    abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one hdb (by norm_num)
  rw [hdecomp, inner_add_left]
  simp only [real_inner_smul_left]
  calc
    |_ * _ + _ * _| ≤ |_ * _| + |_ * _| := abs_add_le _ _
    _ = |exactPrincipalMoleculeBoundaryModeCoefficient S X b 1| *
          |inner ℝ
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) b 1)
            ((Matrix.toEuclideanLin
              ((PrimeStar.smallPrimeGraph S X
                (squareRootCutoff X)).adjMatrix ℝ))
              (PrimeStar.restrictEuclideanToFinset
                (insert (PrimeStar.canonicalUpTarget hS a q)
                  (PrimeStar.largePrimeStarSupport S X
                    (squareRootCutoff X)
                    (PrimeStar.canonicalDownTarget a r)))
                (exactPrincipalMoleculeSignedInteriorVector S X a)))| +
        |exactPrincipalMoleculeBoundaryModeCoefficient S X b (-1)| *
          |inner ℝ
            (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) b (-1))
            ((Matrix.toEuclideanLin
              ((PrimeStar.smallPrimeGraph S X
                (squareRootCutoff X)).adjMatrix ℝ))
              (PrimeStar.restrictEuclideanToFinset
                (insert (PrimeStar.canonicalUpTarget hS a q)
                  (PrimeStar.largePrimeStarSupport S X
                    (squareRootCutoff X)
                    (PrimeStar.canonicalDownTarget a r)))
                (exactPrincipalMoleculeSignedInteriorVector S X a)))| := by
      rw [abs_mul, abs_mul]
    _ ≤ 1 * _ + 1 * _ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcp (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hcm (abs_nonneg _))
    _ ≤ 40 / delta *
          (1 / moleculeStarEnergy S X a +
            |tau| / moleculeStarEnergy S X a) +
        40 / delta *
          (1 / moleculeStarEnergy S X a +
            |tau| / moleculeStarEnergy S X a) := by
      simpa only [one_mul] using add_le_add hplus hminus
    _ = 80 / delta *
          (1 / moleculeStarEnergy S X a +
            |tau| / moleculeStarEnergy S X a) := by ring

/-- Full signed-interior version, still without an orientation hypothesis. -/
theorem abs_inner_signedBoundary_smallPrime_signedInterior_le_unoriented
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdb : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (r : PrimeStar.CanonicalDownIndex a)
    (houtput :
      (PrimeStar.canonicalDownTarget a r : ℕ) * (q : ℕ) = (b : ℕ))
    (hiso : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.firstExitIsolatedVertices S X (squareRootCutoff X) a)
    (hcut : squareRootCutoff X <
      (PrimeStar.canonicalUpTarget hS a q : ℕ))
    (hne : a ≠ b)
    {z s tau delta : ℝ}
    (hrootEq : exactPrincipalMoleculeRoot S X a =
      z * moleculeStarEnergy S X a)
    (hdegreeCore :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a r) : ℝ) =
        s * moleculeStarEnergy S X a ^ 2)
    (hsqrtOutput :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) b : ℝ) =
        moleculeStarEnergy S X a * tau)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsepLower : delta ≤ |z ^ 2 - s|) :
    |inner ℝ
        (exactPrincipalMoleculeSignedBoundaryVector S X b)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeSignedInteriorVector S X a))| ≤
      80 / delta *
        (1 / moleculeStarEnergy S X a +
          |tau| / moleculeStarEnergy S X a) := by
  rw [inner_signedBoundary_smallPrime_signedInterior_eq_commonCoreResponse
    hS ha hb hda hdb q r houtput hcut hne]
  exact abs_inner_signedBoundary_smallPrime_commonCoreSignedResponse_le_unoriented
    hS ha hb hda hdb q r houtput hiso hrootEq hdegreeCore hsqrtOutput
    hdelta hdeltaOne hzLower hzUpper hsepLower

/-- The direct two-orientation estimate, expressed from the coherent-pair
predicate used by the finite compression. -/
theorem abs_inner_signedBoundary_smallPrime_signedInterior_le_of_coherent_unoriented
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {source output : MoleculeCenter S X K}
    (hsourceY : (source.1 : ℕ) ≤ squareRootCutoff X)
    (houtputY : (output.1 : ℕ) ≤ squareRootCutoff X)
    (hdSource : 0 < PrimeStar.largePrimeStarDegree S X
      (squareRootCutoff X) source.1)
    (hdOutput : 0 < PrimeStar.largePrimeStarDegree S X
      (squareRootCutoff X) output.1)
    (hcoherent : IsCoherentRawMoleculePair hS source output)
    {z s tau delta : ℝ}
    (hrootEq : exactPrincipalMoleculeRoot S X source.1 =
      z * moleculeStarEnergy S X source.1)
    (hsqrtOutput :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) output.1 : ℝ) =
        moleculeStarEnergy S X source.1 * tau)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hzLower : (1 : ℝ) / 2 ≤ |z|) (hzUpper : |z| ≤ 2)
    (hsepLower : delta ≤ |z ^ 2 - s|)
    (hdegreeEq :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.vertexDivisorOfDvd source.1
          (Nat.gcd_pos_of_pos_left (output.1 : ℕ)
            (PrimeStar.Vertex.coe_pos source.1))
          (Nat.gcd_dvd_left (source.1 : ℕ) (output.1 : ℕ))) : ℝ) =
        s * moleculeStarEnergy S X source.1 ^ 2) :
    |inner ℝ
        (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeSignedInteriorVector S X source.1))| ≤
      80 / delta *
        (1 / moleculeStarEnergy S X source.1 +
          |tau| / moleculeStarEnergy S X source.1) := by
  obtain ⟨g, _hg, q, r, hdown, houtput, hiso, hcut, hne, hgcd⟩ :=
    exists_orientedCoherent_downUp hS hsourceY hcoherent
  have hcore :
      PrimeStar.canonicalDownTarget source.1 r =
        PrimeStar.vertexDivisorOfDvd source.1
          (Nat.gcd_pos_of_pos_left (output.1 : ℕ)
            (PrimeStar.Vertex.coe_pos source.1))
          (Nat.gcd_dvd_left (source.1 : ℕ) (output.1 : ℕ)) := by
    apply Subtype.ext
    apply Fin.ext
    calc
      (PrimeStar.canonicalDownTarget source.1 r : ℕ) = g := hdown
      _ = (source.1 : ℕ).gcd (output.1 : ℕ) := hgcd.symm
      _ = (PrimeStar.vertexDivisorOfDvd source.1
            (Nat.gcd_pos_of_pos_left (output.1 : ℕ)
              (PrimeStar.Vertex.coe_pos source.1))
            (Nat.gcd_dvd_left (source.1 : ℕ) (output.1 : ℕ)) : ℕ) :=
        (PrimeStar.vertexDivisorOfDvd_coe _ _ _).symm
  have hdegreeCore :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget source.1 r) : ℝ) =
        s * moleculeStarEnergy S X source.1 ^ 2 := by
    simpa [hcore] using hdegreeEq
  exact abs_inner_signedBoundary_smallPrime_signedInterior_le_unoriented
    hS hsourceY houtputY hdSource hdOutput q r houtput hiso hcut hne
    hrootEq hdegreeCore hsqrtOutput
    hdelta hdeltaOne hzLower hzUpper hsepLower

set_option maxHeartbeats 2000000 in
theorem eventually_powerRange_coherent_core_entry_le_unoriented
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ K : ℕ,
        (K : ℝ) ≤ powerScale theta X →
          ∀ source output : MoleculeCenter S X K,
            InPowerRange theta X (source.1 : ℕ) →
            InPowerRange theta X (output.1 : ℕ) →
            IsCoherentRawMoleculePair hS source output →
              |inner ℝ
                  (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
                  (Matrix.toEuclideanLin
                    ((PrimeStar.smallPrimeGraph S X
                      (squareRootCutoff X)).adjMatrix ℝ)
                    (exactPrincipalMoleculeSignedInteriorVector S X
                      source.1))| ≤
                C *
                  (1 / moleculeStarEnergy S X source.1 +
                    moleculeStarEnergy S X output.1 /
                      moleculeStarEnergy S X source.1 ^ 2) := by
  let C : ℝ := 2560
  refine ⟨C, by norm_num [C], ?_⟩
  filter_upwards [
      eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
        S hS htheta,
      eventually_powerRange_downStarRatio_ge S hS htheta,
      eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
      eventually_ge_atTop 16]
      with X hwindow hdownRatio hcenter hX
  intro K hK source output hsrc hout hcoh
  obtain ⟨hsourceY, hdSource, hshift, _⟩ := hwindow source.1 hsrc
  obtain ⟨houtputY, hdOutput, _, _⟩ := hwindow output.1 hout
  let mu : ℝ := moleculeStarEnergy S X source.1
  let tau : ℝ := moleculeStarEnergy S X output.1 / mu
  let z : ℝ := exactPrincipalMoleculeRoot S X source.1 / mu
  let delta : ℝ := 1 / 32
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hdSource)
  have hrootEq : exactPrincipalMoleculeRoot S X source.1 = z * mu := by
    dsimp [z]
    field_simp [ne_of_gt hmu]
  have hsqrtOutput :
      Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) output.1 : ℝ) =
        mu * tau := by
    have htau : mu * tau = moleculeStarEnergy S X output.1 :=
      mul_div_cancel₀ _ (ne_of_gt hmu)
    exact (rfl : moleculeStarEnergy S X output.1 =
        Real.sqrt (PrimeStar.largePrimeStarDegree S X
          (squareRootCutoff X) output.1 : ℝ)).symm.trans htau.symm
  have hzIneq := abs_le.mp hshift
  have hzlo : (99 / 100) * mu ≤ exactPrincipalMoleculeRoot S X source.1 := by
    linarith [hzIneq.1]
  have hzhi : exactPrincipalMoleculeRoot S X source.1 ≤ (101 / 100) * mu := by
    linarith [hzIneq.2]
  have hzpos : 0 < z := by
    dsimp [z]
    exact div_pos (lt_of_lt_of_le (mul_pos (by norm_num) hmu) hzlo) hmu
  have hzLower : (1 : ℝ) / 2 ≤ |z| := by
    rw [abs_of_pos hzpos]
    dsimp [z]
    have : (99 / 100 : ℝ) ≤
        exactPrincipalMoleculeRoot S X source.1 / mu :=
      (le_div_iff₀ hmu).2 (by linarith)
    linarith
  have hzUpper : |z| ≤ 2 := by
    rw [abs_of_pos hzpos]
    dsimp [z]
    have : exactPrincipalMoleculeRoot S X source.1 / mu ≤ (101 / 100 : ℝ) :=
      (div_le_iff₀ hmu).2 (by linarith)
    linarith
  have hdelta : 0 < delta := by norm_num [delta]
  have hdeltaOne : delta ≤ 1 := by norm_num [delta]
  obtain ⟨g, _hg, _q, r, hdown, _houtput, _hiso, _hcut, _hne, hgcd⟩ :=
    exists_orientedCoherent_downUp hS hsourceY hcoh
  have hrMem : (r : ℕ) ∈ (source.1 : ℕ).primeFactors := r.property
  have hYsrc' : squareRootCutoff X ≤ X / (source.1 : ℕ) := by
    have htwo : 2 * (source.1 : ℕ) ≤ Nat.sqrt X := hcenter (source.1 : ℕ) hsrc
    have hApos : 0 < (source.1 : ℕ) := PrimeStar.Vertex.coe_pos source.1
    have hA : (source.1 : ℕ) ≤ Nat.sqrt X :=
      (Nat.le_mul_of_pos_left (source.1 : ℕ) (by norm_num : 0 < 2)).trans htwo
    apply (Nat.le_div_iff_mul_le hApos).2
    simpa [squareRootCutoff, mul_comm] using
      (Nat.mul_le_mul_left (Nat.sqrt X) hA).trans (Nat.sqrt_le X)
  have hscore :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget source.1 r) : ℝ) /
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) source.1 : ℝ) ≥
          17 / 16 := by
    have hcoreY : (PrimeStar.canonicalDownTarget source.1 r : ℕ) ≤
        squareRootCutoff X := (Nat.div_le_self _ _).trans hsourceY
    have hYcore : squareRootCutoff X ≤
        X / (PrimeStar.canonicalDownTarget source.1 r : ℕ) := by
      have hApos : 0 < (PrimeStar.canonicalDownTarget source.1 r : ℕ) :=
        PrimeStar.Vertex.coe_pos _
      have hle' : (PrimeStar.canonicalDownTarget source.1 r : ℕ) ≤
          (source.1 : ℕ) := Nat.div_le_self _ _
      exact hYsrc'.trans (Nat.div_le_div_left hle' hApos)
    have hsrcEq :=
      PrimeStar.sq_sqrt_largePrimeStarDegree_eq_allowedPrimeDifference
        (Y := squareRootCutoff X) hS hsourceY hYsrc'
    have hcoreEq :=
      PrimeStar.sq_sqrt_largePrimeStarDegree_eq_allowedPrimeDifference
        (Y := squareRootCutoff X) hS hcoreY hYcore
    have harith := hdownRatio source.1 hsrc (r : ℕ) hrMem
    have hmuSrc : moleculeStarEnergy S X source.1 ^ 2 =
        arithmeticStarDegree S (source.1 : ℕ) X := by
      rw [moleculeStarEnergy_sq, arithmeticStarDegree]
      rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hsrcEq
      exact hsrcEq
    have hmuCore :
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget source.1 r) : ℝ) =
          arithmeticStarDegree S
            (PrimeStar.canonicalDownTarget source.1 r : ℕ) X := by
      rw [arithmeticStarDegree]
      rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hcoreEq
      exact hcoreEq
    have hdivq : (source.1 : ℕ) / (r : ℕ) =
        (PrimeStar.canonicalDownTarget source.1 r : ℕ) := by
      have hmul := PrimeStar.canonicalDownTarget_mul_coe source.1 r
      exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_mem_primeFactors hrMem) hmul.symm
    have hdsrc :
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) source.1 : ℝ) =
          arithmeticStarDegree S (source.1 : ℕ) X := by
      rw [← moleculeStarEnergy_sq]
      exact hmuSrc
    rw [hmuCore, hdsrc, ← hdivq]
    exact harith
  let s : ℝ :=
    (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget source.1 r) : ℝ) /
      moleculeStarEnergy S X source.1 ^ 2
  have hs17 : 17 / 16 ≤ s := by
    dsimp [s]
    rw [moleculeStarEnergy_sq]
    exact hscore
  have hsepLower : delta ≤ |z ^ 2 - s| := by
    have hzabs : |z| ≤ 101 / 100 := by
      rw [abs_of_pos hzpos]
      dsimp [z]
      exact (div_le_iff₀ hmu).2 (by linarith [hzhi])
    have hz2 : z ^ 2 ≤ (101 / 100) ^ 2 := by
      rw [← sq_abs]
      simpa [pow_two] using mul_self_le_mul_self (abs_nonneg z) hzabs
    have hnum : ((101 / 100) ^ 2 : ℝ) ≤ 17 / 16 := by norm_num
    have hspos : z ^ 2 ≤ s := le_trans hz2 (le_trans hnum hs17)
    have hgap : 17 / 16 - (101 / 100) ^ 2 ≤ s - z ^ 2 := by linarith
    have hval : (1 / 32 : ℝ) ≤ 17 / 16 - (101 / 100) ^ 2 := by norm_num
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hspos)]
    exact le_trans hval hgap
  have hdegreeEq :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.vertexDivisorOfDvd source.1
          (Nat.gcd_pos_of_pos_left (output.1 : ℕ)
            (PrimeStar.Vertex.coe_pos source.1))
          (Nat.gcd_dvd_left (source.1 : ℕ) (output.1 : ℕ))) : ℝ) =
        s * moleculeStarEnergy S X source.1 ^ 2 := by
    have hcore : PrimeStar.canonicalDownTarget source.1 r =
        PrimeStar.vertexDivisorOfDvd source.1
          (Nat.gcd_pos_of_pos_left (output.1 : ℕ)
            (PrimeStar.Vertex.coe_pos source.1))
          (Nat.gcd_dvd_left (source.1 : ℕ) (output.1 : ℕ)) := by
      apply Subtype.ext
      apply Fin.ext
      calc
        (PrimeStar.canonicalDownTarget source.1 r : ℕ) = g := hdown
        _ = (source.1 : ℕ).gcd (output.1 : ℕ) := hgcd.symm
        _ = _ := (PrimeStar.vertexDivisorOfDvd_coe _ _ _).symm
    have hsdef : s * moleculeStarEnergy S X source.1 ^ 2 =
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget source.1 r) : ℝ) :=
      div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hmu))
    simpa [hcore] using hsdef.symm
  have hbound :=
    abs_inner_signedBoundary_smallPrime_signedInterior_le_of_coherent_unoriented
      hS hsourceY houtputY hdSource hdOutput hcoh hrootEq hsqrtOutput
      hdelta hdeltaOne hzLower hzUpper hsepLower hdegreeEq
  have htau : moleculeStarEnergy S X output.1 /
      moleculeStarEnergy S X source.1 ^ 2 = |tau| / mu := by
    have htau0 : 0 ≤ tau := div_nonneg (moleculeStarEnergy_nonneg _ _ _) hmu.le
    rw [abs_of_nonneg htau0]
    dsimp [tau, mu]
    rw [pow_two]
    exact (div_div _ _ _).symm
  have hC : 80 / delta = C := by norm_num [C, delta]
  simpa [hC, htau, mu] using hbound

theorem sum_inv_moleculeCenter_le_one_add_log
    (S : Finset ℕ) (X K : ℕ) :
    (∑ a : MoleculeCenter S X K, ((a.1 : ℕ) : ℝ)⁻¹) ≤
      1 + Real.log (K : ℝ) := by
  classical
  let f : MoleculeCenter S X K → ℕ := fun a ↦ (a.1 : ℕ)
  let T : Finset ℕ := Finset.univ.image f
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact Fin.ext hab
  have hT : T ⊆ Finset.Icc 1 K := by
    intro n hn
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨PrimeStar.Vertex.coe_pos a.1, a.2⟩
  have heq : (∑ a : MoleculeCenter S X K, ((a.1 : ℕ) : ℝ)⁻¹) =
      ∑ n ∈ T, (n : ℝ)⁻¹ := by
    rw [show (∑ a : MoleculeCenter S X K, ((a.1 : ℕ) : ℝ)⁻¹) =
        ∑ a ∈ (Finset.univ : Finset (MoleculeCenter S X K)),
          ((f a : ℕ) : ℝ)⁻¹ by simp [f]]
    exact (Finset.sum_image
      (f := fun n : ℕ ↦ (n : ℝ)⁻¹) hf.injOn).symm
  rw [heq]
  calc
    (∑ n ∈ T, (n : ℝ)⁻¹) ≤
        ∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hT (by
        intro n _hn _hnT
        positivity)
    _ = (harmonic K : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ ≤ 1 + Real.log (K : ℝ) := harmonic_le_one_add_log K

/-- Elementary upper scale for a nonempty square-cutoff star. -/
theorem moleculeStarEnergy_sq_le_twice_div
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (b : PrimeStar.Vertex S X)
    (hbY : (b : ℕ) ≤ squareRootCutoff X)
    (hYX : squareRootCutoff X ≤ X / (b : ℕ)) :
    moleculeStarEnergy S X b ^ 2 ≤ 2 * (X / (b : ℕ) : ℕ) := by
  rw [moleculeStarEnergy_sq,
    PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS b hbY hYX]
  have hcount : PrimeStar.allowedPrimeCount S (X / (b : ℕ)) ≤
      X / (b : ℕ) + 1 := by
    exact (PrimeStar.allowedPrimeCount_le_primeCounting S _).trans (by
      simpa [Nat.primeCounting, Nat.primeCounting'] using
        (Nat.count_le (p := Nat.Prime) (n := X / (b : ℕ) + 1)))
  have hdiv : 1 ≤ X / (b : ℕ) := by
    apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos b)).2
    simpa using PrimeStar.Vertex.coe_le b
  exact_mod_cast (show
    PrimeStar.allowedPrimeCount S (X / (b : ℕ)) -
        PrimeStar.allowedPrimeCount S (squareRootCutoff X) ≤
      2 * (X / (b : ℕ)) by omega)

private theorem coherent_entry_sq_le_arithmetic_scale
    {A B X L mu nu C y : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hX : 0 < X) (hL : 0 < L)
    (hmu : 0 < mu) (hnu : 0 ≤ nu) (hC : 0 ≤ C)
    (hy : |y| ≤ C * (1 / mu + nu / mu ^ 2))
    (hmuLower : X / (8 * A * L) ≤ mu ^ 2)
    (hnuUpper : nu ^ 2 ≤ 4 * X / B) :
    |y| ^ 2 ≤
      2 * C ^ 2 *
        (8 * A * L / X + 256 * A ^ 2 * L ^ 2 / (B * X)) := by
  have hmuSq : 0 < mu ^ 2 := sq_pos_of_pos hmu
  have hmuFourth : 0 < mu ^ 4 := by positivity
  have hmuInv : 1 / mu ^ 2 ≤ 8 * A * L / X := by
    rw [div_le_iff₀ hmuSq, div_mul_eq_mul_div, le_div_iff₀ hX]
    have hden : 0 < 8 * A * L := by positivity
    have := (div_le_iff₀ hden).mp hmuLower
    nlinarith
  have hratio : nu ^ 2 / mu ^ 4 ≤
      256 * A ^ 2 * L ^ 2 / (B * X) := by
    rw [div_le_iff₀ hmuFourth, div_mul_eq_mul_div,
      le_div_iff₀ (mul_pos hB hX)]
    have hnuBX : nu ^ 2 * (B * X) ≤ 4 * X ^ 2 := by
      have hnuB : nu ^ 2 * B ≤ 4 * X := by
        have := (le_div_iff₀ hB).mp hnuUpper
        nlinarith
      nlinarith
    have hXsq : X ^ 2 ≤ 64 * A ^ 2 * L ^ 2 * mu ^ 4 := by
      have hden : 0 < 8 * A * L := by positivity
      have hxmu := (div_le_iff₀ hden).mp hmuLower
      nlinarith [sq_nonneg (X - 8 * A * L * mu ^ 2)]
    nlinarith
  have hsumNonneg : 0 ≤ 1 / mu + nu / mu ^ 2 := by positivity
  have hySq : |y| ^ 2 ≤ C ^ 2 * (1 / mu + nu / mu ^ 2) ^ 2 := by
    simpa [mul_pow] using
      ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hsumNonneg)).2 hy)
  calc
    |y| ^ 2 ≤ C ^ 2 * (1 / mu + nu / mu ^ 2) ^ 2 := hySq
    _ ≤ 2 * C ^ 2 * ((1 / mu) ^ 2 + (nu / mu ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (1 / mu - nu / mu ^ 2)]
    _ = 2 * C ^ 2 * (1 / mu ^ 2 + nu ^ 2 / mu ^ 4) := by
      field_simp [hmu.ne']
      <;> ring
    _ ≤ 2 * C ^ 2 *
        (8 * A * L / X + 256 * A ^ 2 * L ^ 2 / (B * X)) := by
      gcongr

private theorem sum_moleculePair_of_arithmetic_scale
    (S : Finset ℕ) (X K : ℕ) {D L : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hX : 0 < (X : ℝ))
    (F : MoleculeCenter S X K → MoleculeCenter S X K → ℝ)
    (hF : ∀ source output,
      F source output ≤
        2 * D ^ 2 *
          (8 * (source.1 : ℝ) * L / X +
            256 * (source.1 : ℝ) ^ 2 * L ^ 2 /
              ((output.1 : ℝ) * X))) :
    (∑ output, ∑ source, F source output) ≤
      2 * D ^ 2 *
        ((K + 1 : ℝ) ^ 2 * (8 * K * L / X) +
          (K + 1 : ℝ) * (256 * K ^ 2 * L ^ 2 / X) *
            (1 + Real.log (K : ℝ))) := by
  have hcard : (Fintype.card (MoleculeCenter S X K) : ℝ) ≤ K + 1 := by
    exact_mod_cast card_moleculeCenter_le_succ S X K
  have hK : 0 ≤ (K : ℝ) := by positivity
  have hK1 : 0 ≤ (K + 1 : ℝ) := by positivity
  have hinv := sum_inv_moleculeCenter_le_one_add_log S X K
  have hsource (output : MoleculeCenter S X K) :
      (∑ source : MoleculeCenter S X K, F source output) ≤
        (Fintype.card (MoleculeCenter S X K) : ℝ) *
          (2 * D ^ 2 * (8 * K * L / X) +
            (2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X)) *
              ((output.1 : ℕ) : ℝ)⁻¹) := by
    calc
      (∑ source : MoleculeCenter S X K, F source output) ≤
          ∑ source : MoleculeCenter S X K, 2 * D ^ 2 *
            (8 * (source.1 : ℝ) * L / X +
              256 * (source.1 : ℝ) ^ 2 * L ^ 2 /
                ((output.1 : ℝ) * X)) := by
            exact Finset.sum_le_sum fun source _ ↦ hF source output
      _ ≤ ∑ _source : MoleculeCenter S X K,
          2 * D ^ 2 *
            (8 * K * L / X +
              256 * K ^ 2 * L ^ 2 / ((output.1 : ℝ) * X)) := by
            apply Finset.sum_le_sum
            intro source _
            have hs : (source.1 : ℝ) ≤ K := by exact_mod_cast source.2
            have hs2 : (source.1 : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by
              nlinarith [show 0 ≤ (source.1 : ℝ) by positivity]
            gcongr
      _ = ∑ _source : MoleculeCenter S X K,
          (2 * D ^ 2 * (8 * K * L / X) +
            (2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X)) *
              ((output.1 : ℕ) : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro source _
            have hout : ((output.1 : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (PrimeStar.Vertex.coe_pos output.1).ne'
            field_simp [hX.ne', hout]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    (∑ output : MoleculeCenter S X K,
        ∑ source : MoleculeCenter S X K, F source output) ≤
        ∑ output : MoleculeCenter S X K,
          (Fintype.card (MoleculeCenter S X K) : ℝ) *
          (2 * D ^ 2 * (8 * K * L / X) +
            (2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X)) *
              ((output.1 : ℕ) : ℝ)⁻¹) := by
          exact Finset.sum_le_sum fun output _ ↦ hsource output
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) ^ 2 *
          (2 * D ^ 2 * (8 * K * L / X)) +
        (Fintype.card (MoleculeCenter S X K) : ℝ) *
          (2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X)) *
          (∑ output : MoleculeCenter S X K, ((output.1 : ℕ) : ℝ)⁻¹) := by
      have hsum :
          (∑ output : MoleculeCenter S X K,
              (Fintype.card (MoleculeCenter S X K) : ℝ) *
                ((2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X)) *
                  ((output.1 : ℕ) : ℝ)⁻¹)) =
            (Fintype.card (MoleculeCenter S X K) : ℝ) *
              (2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X)) *
              (∑ output : MoleculeCenter S X K,
                ((output.1 : ℕ) : ℝ)⁻¹) := by
        calc
          _ = ∑ output : MoleculeCenter S X K,
              ((Fintype.card (MoleculeCenter S X K) : ℝ) *
                (2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X))) *
                  ((output.1 : ℕ) : ℝ)⁻¹ := by
                apply Finset.sum_congr rfl
                intro output _
                ring
          _ = _ := by rw [Finset.mul_sum]
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_const]
      rw [hsum]
      simp only [Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ (K + 1 : ℝ) ^ 2 *
          (2 * D ^ 2 * (8 * K * L / X)) +
        (K + 1 : ℝ) *
          (2 * D ^ 2 * (256 * K ^ 2 * L ^ 2 / X)) *
          (1 + Real.log (K : ℝ)) := by
      gcongr
    _ = 2 * D ^ 2 *
        ((K + 1 : ℝ) ^ 2 * (8 * K * L / X) +
          (K + 1 : ℝ) * (256 * K ^ 2 * L ^ 2 / X) *
            (1 + Real.log (K : ℝ))) := by ring

set_option maxHeartbeats 3000000 in
/-- Full two-orientation common-core budget on a fixed power range.  The
reverse orientation is charged by the harmonic mass of the output centres,
not by a second coherent-pair enumeration. -/
theorem eventually_powerRange_sum_coherent_core_entry_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ X : ℕ in atTop, ∀ K : ℕ,
        (K : ℝ) ≤ powerScale theta X →
          (∑ output : MoleculeCenter S X K,
            ∑ source : MoleculeCenter S X K,
              if IsCoherentRawMoleculePair hS output source then
                |inner ℝ
                  (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
                  (Matrix.toEuclideanLin
                    ((PrimeStar.smallPrimeGraph S X
                      (squareRootCutoff X)).adjMatrix ℝ)
                    (exactPrincipalMoleculeSignedInteriorVector S X
                      source.1))| ^ 2
              else 0) ≤
            2 * D ^ 2 *
              ((K + 1 : ℝ) ^ 2 *
                  (8 * K * Real.log (X : ℝ) / X) +
                (K + 1 : ℝ) *
                  (256 * K ^ 2 * Real.log (X : ℝ) ^ 2 / X) *
                    (1 + Real.log (K : ℝ))) := by
  obtain ⟨D, hD, hentry⟩ :=
    eventually_powerRange_coherent_core_entry_le_unoriented S hS htheta
  refine ⟨D, hD, ?_⟩
  filter_upwards [hentry,
      eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
      eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
        S hS htheta,
      eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
      eventually_ge_atTop 3]
      with X hentryX hscale hwindow hcenter hX
  intro K hK
  have hXr : 0 < (X : ℝ) := by positivity
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  let F : MoleculeCenter S X K → MoleculeCenter S X K → ℝ :=
    fun source output ↦
      if IsCoherentRawMoleculePair hS output source then
        |inner ℝ
          (exactPrincipalMoleculeSignedBoundaryVector S X output.1)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X
              (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X source.1))| ^ 2
      else 0
  have hF : ∀ source output : MoleculeCenter S X K,
      F source output ≤
        2 * D ^ 2 *
          (8 * (source.1 : ℝ) * Real.log (X : ℝ) / X +
            256 * (source.1 : ℝ) ^ 2 * Real.log (X : ℝ) ^ 2 /
              ((output.1 : ℝ) * X)) := by
    intro source output
    dsimp [F]
    split_ifs with hcoh
    · have hsrcK : (source.1 : ℝ) ≤ K := by exact_mod_cast source.2
      have houtK : (output.1 : ℝ) ≤ K := by exact_mod_cast output.2
      have hsrc : InPowerRange theta X (source.1 : ℕ) :=
        ⟨PrimeStar.Vertex.coe_pos source.1, hsrcK.trans hK⟩
      have hout : InPowerRange theta X (output.1 : ℕ) :=
        ⟨PrimeStar.Vertex.coe_pos output.1, houtK.trans hK⟩
      obtain ⟨hsrcY, hdsrc, _⟩ := hwindow source.1 hsrc
      obtain ⟨houtY, hdout, _⟩ := hwindow output.1 hout
      let mu := moleculeStarEnergy S X source.1
      let nu := moleculeStarEnergy S X output.1
      have hmu : 0 < mu := by
        dsimp [mu, moleculeStarEnergy]
        exact Real.sqrt_pos.2 (by exact_mod_cast hdsrc)
      have hnu : 0 ≤ nu := moleculeStarEnergy_nonneg _ _ _
      have hcoh' : IsCoherentRawMoleculePair hS source output :=
        (isCoherentRawMoleculePair_comm hS source output).mpr hcoh
      have hraw := hentryX K hK source output hsrc hout hcoh'
      have hmuLower : (X : ℝ) /
          (8 * (source.1 : ℝ) * Real.log (X : ℝ)) ≤ mu ^ 2 := by
        simpa [mu] using (hscale source.1 hsrc).1
      have hYout : squareRootCutoff X ≤ X / (output.1 : ℕ) := by
        have htwo : 2 * (output.1 : ℕ) ≤ Nat.sqrt X :=
          hcenter (output.1 : ℕ) hout
        have hbpos : 0 < (output.1 : ℕ) := PrimeStar.Vertex.coe_pos output.1
        have hb : (output.1 : ℕ) ≤ Nat.sqrt X :=
          (Nat.le_mul_of_pos_left (output.1 : ℕ) (by norm_num : 0 < 2)).trans htwo
        apply (Nat.le_div_iff_mul_le hbpos).2
        simpa [squareRootCutoff, mul_comm] using
          (Nat.mul_le_mul_left (Nat.sqrt X) hb).trans (Nat.sqrt_le X)
      have hnuNat := moleculeStarEnergy_sq_le_twice_div
        hS output.1 houtY hYout
      have hnuUpper : nu ^ 2 ≤
          4 * (X : ℝ) / (output.1 : ℝ) := by
        calc
          nu ^ 2 ≤ (2 * (X / (output.1 : ℕ)) : ℕ) := by
            exact_mod_cast hnuNat
          _ = 2 * ((X / (output.1 : ℕ) : ℕ) : ℝ) := by norm_num
          _ ≤ 2 * ((X : ℝ) / (output.1 : ℝ)) := by
            gcongr
            exact Nat.cast_div_le
          _ ≤ 4 * ((X : ℝ) / (output.1 : ℝ)) := by
            gcongr <;> norm_num
          _ = 4 * (X : ℝ) / (output.1 : ℝ) := by ring
      exact coherent_entry_sq_le_arithmetic_scale
        (A := (source.1 : ℝ)) (B := (output.1 : ℝ))
        (X := (X : ℝ)) (L := Real.log (X : ℝ))
        (mu := mu) (nu := nu) (C := D) (by exact_mod_cast hsrc.1) (by
          exact_mod_cast PrimeStar.Vertex.coe_pos output.1)
        hXr hlog hmu hnu hD.le hraw hmuLower hnuUpper
    · positivity
  simpa [F] using
    sum_moleculePair_of_arithmetic_scale S X K hD.le hlog.le hXr F hF

/-- The finite coherent compression theorem with all three Hilbert--Schmidt
budgets instantiated on a fixed sub-square-root power range.  Only the
spectral gap and operator hypotheses of the finite Schur theorem remain. -/
theorem eventually_powerRange_exactOneExitLocalCoherentCompressionResidual_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ D Cb Cr : ℝ, 0 < D ∧ 0 < Cb ∧ 0 < Cr ∧
      ∀ᶠ X : ℕ in atTop, ∀ K : ℕ,
        (K : ℝ) ≤ powerScale theta X →
        ∀ (gamma eta : ℝ), 0 < gamma → 0 ≤ eta →
        (∀ a : MoleculeCenter S X K,
          (a.1 : ℕ) ≤ squareRootCutoff X) →
        (∀ a : MoleculeCenter S X K,
          0 < PrimeStar.largePrimeStarDegree S X
            (squareRootCutoff X) a.1) →
        (∀ a : MoleculeCenter S X K,
          exactPrincipalMoleculeRoot S X a.1 ≠ 0) →
        (∀ (a : MoleculeCenter S X K) (x : MoleculeAmbient S X),
          gamma * ‖x‖ ≤
            ‖exactPrincipalMoleculeRoot S X a.1 • x -
              PrimeStar.firstExitLargePrimeCompressionOperator S X
                (squareRootCutoff X) a.1 x‖) →
        (∀ (a : MoleculeCenter S X K) (k : PrimeStar.Vertex S X),
          k ∈ PrimeStar.firstExitLowerCenters S X
              (squareRootCutoff X) a.1 →
            exactPrincipalMoleculeRoot S X a.1 ^ 2 ≠
              (PrimeStar.largePrimeStarDegree S X
                (squareRootCutoff X) k : ℝ)) →
        (∀ x : MoleculeAmbient S X,
          ‖Matrix.toEuclideanLin
              ((PrimeStar.smallPrimeGraph S X
                (squareRootCutoff X)).adjMatrix ℝ) x‖ ≤ eta * ‖x‖) →
          matrixFrobeniusNorm
              (exactOneExitLocalCoherentCompressionResidual
                (S := S) (X := X) (K := K) hS) ^ 2 ≤
            3 * (
              2 * D ^ 2 *
                ((K + 1 : ℝ) ^ 2 *
                    (8 * K * Real.log (X : ℝ) / X) +
                  (K + 1 : ℝ) *
                    (256 * K ^ 2 * Real.log (X : ℝ) ^ 2 / X) *
                      (1 + Real.log (K : ℝ))) +
              4 * eta ^ 4 / gamma ^ 2 *
                (Cb * (K + 1 : ℝ) ^ 2 * Real.log (X : ℝ) ^ 3 /
                  ((X : ℝ) * Real.sqrt (X : ℝ))) +
              (Cb * (K + 1 : ℝ) ^ 2 * Real.log (X : ℝ) ^ 3 /
                  ((X : ℝ) * Real.sqrt (X : ℝ))) *
                (Cr * (K + 1 : ℝ) ^ 2 / Real.log (X : ℝ))) := by
  obtain ⟨D, hD, hcore⟩ :=
    eventually_powerRange_sum_coherent_core_entry_sq_le S hS htheta
  obtain ⟨Cb, hCb, hboundary⟩ :=
    eventually_powerRange_sum_exactPrincipalMoleculeBoundaryKernel_sq_le
      S hS htheta
  obtain ⟨Cr, hCr, hresidual⟩ :=
    eventually_powerRange_sum_exactPrincipalMoleculeResidual_sq_le
      S hS htheta
  refine ⟨D, Cb, Cr, hD, hCb, hCr, ?_⟩
  filter_upwards [hcore, hboundary, hresidual]
      with X hcoreX hboundaryX hresidualX
  intro K hK gamma eta hgamma heta ha hd hroot hgap hden hH
  exact exactOneExitLocalCoherentCompressionResidual_frobenius_sq_le_core_kernel
    hS ha hd hroot gamma eta hgamma heta hgap hden hH
      (hcoreX K hK) (hboundaryX K hK) (hresidualX K hK)

end
end PrimeCoverPowerBand
