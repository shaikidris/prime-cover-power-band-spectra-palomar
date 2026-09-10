import PrimeCoverPowerBand.FirstExitTarget
import PrimeStar.StarInertia
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.Matrix.PosDef

/- Generated declaration-level S2 migration candidate. -/
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


/- Source slice: FirstExitMolecules.lean -/

open scoped BigOperators


/- Source slice: PrincipalMolecule.lean -/

open Matrix


/- Source slice: MoleculeEmbedding.lean -/


/- Source slice: MoleculeResidual.lean -/


/- Source slice: MoleculeFamily.lean -/


/- Source slice: CollisionBudget.lean -/

variable {m n : Type*} [Fintype m] [Fintype n]


/- Source slice: MixedMatrixNorms.lean -/

open scoped Matrix

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

noncomputable def matrixL2OperatorNorm [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A


/- Source slice: MoleculeFrameComplex.lean -/

variable {m n o : Type*}

def complexifyRealMatrix (A : Matrix m n ℝ) : Matrix m n ℂ :=
  fun i j ↦ A i j

theorem complexifyRealMatrix_apply (A : Matrix m n ℝ) (i : m) (j : n) :
    complexifyRealMatrix A i j = A i j :=
  rfl

theorem complexifyRealMatrix_eq_map (A : Matrix m n ℝ) :
    complexifyRealMatrix A = A.map Complex.ofRealHom := by
  ext i j
  rfl

theorem eigenvalues₀_complexifyRealMatrix_eq
    [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (hA : A.IsHermitian) :
    (show (complexifyRealMatrix A).IsHermitian by
        rw [complexifyRealMatrix_eq_map]
        exact hA.map Complex.ofRealHom (fun x ↦ by simp)).eigenvalues₀ =
      hA.eigenvalues₀ := by
  let hAC : (complexifyRealMatrix A).IsHermitian := by
    rw [complexifyRealMatrix_eq_map]
    exact hA.map Complex.ofRealHom (fun x ↦ by simp)
  have hroots :
      (complexifyRealMatrix A).charpoly.roots.map Complex.re =
        A.charpoly.roots := by
    rw [complexifyRealMatrix_eq_map, Matrix.charpoly_map,
      hA.splits_charpoly.roots_map]
    simp
  have hlists : List.ofFn hAC.eigenvalues₀ = List.ofFn hA.eigenvalues₀ := by
    rw [← hAC.sort_roots_charpoly_eq_eigenvalues₀,
      ← hA.sort_roots_charpoly_eq_eigenvalues₀]
    simpa using congrArg (fun s ↦ s.sort (· ≥ ·)) hroots
  exact List.ofFn_inj.mp hlists

theorem complexifyRealMatrix_mul
    [Fintype n] (A : Matrix m n ℝ) (B : Matrix n o ℝ) :
    complexifyRealMatrix (A * B) =
      complexifyRealMatrix A * complexifyRealMatrix B := by
  ext i j
  simp [complexifyRealMatrix, Matrix.mul_apply]

theorem complexifyRealMatrix_transpose (A : Matrix m n ℝ) :
    complexifyRealMatrix A.transpose =
      (complexifyRealMatrix A).conjTranspose := by
  ext i j
  simp [complexifyRealMatrix]

def moleculeFamilyComplexAdjacency (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  complexifyRealMatrix ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ)

theorem moleculeFamilyComplexAdjacency_eq_adjMatrix
    (S : Finset ℕ) (X : ℕ) :
    moleculeFamilyComplexAdjacency S X =
      (PrimeStar.primeCoverGraph S X).adjMatrix ℂ := by
  ext v w
  change ((((PrimeStar.primeCoverGraph S X).adjMatrix ℝ) v w : ℝ) : ℂ) =
    ((PrimeStar.primeCoverGraph S X).adjMatrix ℂ) v w
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : (PrimeStar.primeCoverGraph S X).Adj v w
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

theorem moleculeFamilyComplexAdjacency_isHermitian
    (S : Finset ℕ) (X : ℕ) :
    (moleculeFamilyComplexAdjacency S X).IsHermitian := by
  rw [moleculeFamilyComplexAdjacency_eq_adjMatrix]
  exact (PrimeStar.primeCoverGraph S X).isHermitian_adjMatrix ℂ

theorem moleculeFamilyComplexAdjacency_eigenvalues₀_eq_real
    (S : Finset ℕ) (X : ℕ) :
    (moleculeFamilyComplexAdjacency_isHermitian S X).eigenvalues₀ =
      ((PrimeStar.primeCoverGraph S X).isHermitian_adjMatrix
        (R := ℝ)).eigenvalues₀ := by
  simpa [moleculeFamilyComplexAdjacency] using
    (eigenvalues₀_complexifyRealMatrix_eq
      ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ)
      ((PrimeStar.primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ)))


/- Source slice: FrameCompressionBounds.lean -/

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n]

theorem isometricFrame_mul_conjTranspose_isStarProjection
    [DecidableEq m] [DecidableEq n]
    (Q : Matrix n m ℂ) (hQ : Qᴴ * Q = 1) :
    IsStarProjection (Q * Qᴴ) := by
  constructor
  · show (Q * Qᴴ) * (Q * Qᴴ) = Q * Qᴴ
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᴴ Q Qᴴ, hQ, Matrix.one_mul]
  · show star (Q * Qᴴ) = Q * Qᴴ
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]


/- Source slice: PositiveStarProjection.lean -/

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

abbrev PositiveStarCenter (S : Finset ℕ) (X : ℕ) :=
  {a : PrimeStar.Vertex S X //
    (a : ℕ) ≤ squareRootCutoff X ∧
      0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a}

def positiveStarFrameReal (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PositiveStarCenter S X) ℝ :=
  fun v a ↦ moleculePositiveStarMode S X a.1 v

def positiveStarFrame (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PositiveStarCenter S X) ℂ :=
  complexifyRealMatrix (positiveStarFrameReal S X)

theorem positiveStarFrameReal_mul_eq_zero_of_ne
    {S : Finset ℕ} {X : ℕ} {a b : PositiveStarCenter S X}
    (hab : a ≠ b) (v : PrimeStar.Vertex S X) :
    positiveStarFrameReal S X v a * positiveStarFrameReal S X v b = 0 := by
  have habv : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  have hdisjoint := PrimeStar.sqrtCutoff_disjoint_largePrimeStarSupport
    a.2.1 b.2.1 habv
  by_cases hva : v ∈
      PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a.1
  · have hvb : v ∉
        PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) b.1 := by
      intro hvb
      exact (Finset.disjoint_left.mp hdisjoint) hva hvb
    have hbzero : positiveStarFrameReal S X v b = 0 := by
      change moleculePositiveStarMode S X b.1 v = 0
      exact PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hvb
    rw [hbzero, mul_zero]
  · have hazero : positiveStarFrameReal S X v a = 0 := by
      change moleculePositiveStarMode S X a.1 v = 0
      exact PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem hva
    rw [hazero, zero_mul]

theorem positiveStarFrameReal_transpose_mul_self
    (S : Finset ℕ) (X : ℕ) :
    (positiveStarFrameReal S X).transpose * positiveStarFrameReal S X = 1 := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, positiveStarFrameReal]
    have hnorm := norm_moleculePositiveStarMode (S := S) (X := X)
      (a := a.1) a.2.2
    simp only [Matrix.one_apply]
    calc
      (∑ v, moleculePositiveStarMode S X a.1 v *
          moleculePositiveStarMode S X a.1 v) =
          ∑ v, (moleculePositiveStarMode S X a.1 v) ^ 2 := by
            apply Finset.sum_congr rfl
            intro v _hv
            ring
      _ = ‖moleculePositiveStarMode S X a.1‖ ^ 2 :=
        (EuclideanSpace.real_norm_sq_eq
          (moleculePositiveStarMode S X a.1)).symm
      _ = 1 := by rw [hnorm]; norm_num
  · rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [Finset.sum_eq_zero]
    · simp [hab]
    · intro v _hv
      exact positiveStarFrameReal_mul_eq_zero_of_ne hab v

theorem positiveStarFrame_conjTranspose_mul_self
    (S : Finset ℕ) (X : ℕ) :
    (positiveStarFrame S X)ᴴ * positiveStarFrame S X = 1 := by
  rw [positiveStarFrame, ← complexifyRealMatrix_transpose,
    ← complexifyRealMatrix_mul, positiveStarFrameReal_transpose_mul_self]
  ext a b
  simp only [complexifyRealMatrix, Matrix.one_apply]
  split_ifs <;> norm_num

def positiveStarProjection (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  positiveStarFrame S X * (positiveStarFrame S X)ᴴ

theorem positiveStarProjection_isStarProjection
    (S : Finset ℕ) (X : ℕ) :
    IsStarProjection (positiveStarProjection S X) := by
  exact isometricFrame_mul_conjTranspose_isStarProjection
    (positiveStarFrame S X) (positiveStarFrame_conjTranspose_mul_self S X)

theorem positiveStarProjection_mul_frame
    (S : Finset ℕ) (X : ℕ) :
    positiveStarProjection S X * positiveStarFrame S X =
      positiveStarFrame S X := by
  rw [positiveStarProjection, Matrix.mul_assoc,
    positiveStarFrame_conjTranspose_mul_self, Matrix.mul_one]

def positiveStarComplementProjection (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  1 - positiveStarProjection S X

theorem positiveStarComplementProjection_isStarProjection
    (S : Finset ℕ) (X : ℕ) :
    IsStarProjection (positiveStarComplementProjection S X) := by
  exact (positiveStarProjection_isStarProjection S X).one_sub


/- Source slice: OneExitCyclicSubspace.lean -/

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

def oneExitLargePrimeMatrix (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℂ

def oneExitSmallPrimeMatrix (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℂ

def oneExitCoreMatrix (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  positiveStarComplementProjection S X * oneExitLargePrimeMatrix S X *
    positiveStarComplementProjection S X

def oneExitSourceMatrix (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  positiveStarComplementProjection S X * oneExitSmallPrimeMatrix S X *
    positiveStarProjection S X

theorem oneExitCoreMatrix_isHermitian (S : Finset ℕ) (X : ℕ) :
    (oneExitCoreMatrix S X).IsHermitian := by
  have hQ : (positiveStarComplementProjection S X).IsHermitian :=
    (positiveStarComplementProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hL : (oneExitLargePrimeMatrix S X).IsHermitian :=
    (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix ℂ
  simpa [oneExitCoreMatrix, hQ.eq] using
    Matrix.isHermitian_conjTranspose_mul_mul
      (positiveStarComplementProjection S X) hL

def oneExitCyclicLayer (S : Finset ℕ) (X k : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (PrimeStar.Vertex S X)) :=
  LinearMap.range
    (Matrix.toEuclideanLin
      ((oneExitCoreMatrix S X) ^ k * oneExitSourceMatrix S X))

def oneExitCyclicSubspace (S : Finset ℕ) (X : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (PrimeStar.Vertex S X)) :=
  ⨆ k : ℕ, oneExitCyclicLayer S X k

theorem oneExitSource_range_le_cyclicSubspace
    (S : Finset ℕ) (X : ℕ) :
    LinearMap.range (Matrix.toEuclideanLin (oneExitSourceMatrix S X)) ≤
      oneExitCyclicSubspace S X := by
  have hzero : oneExitCyclicLayer S X 0 =
      LinearMap.range (Matrix.toEuclideanLin (oneExitSourceMatrix S X)) := by
    simp [oneExitCyclicLayer]
  rw [← hzero]
  exact le_iSup (fun k : ℕ ↦ oneExitCyclicLayer S X k) 0

theorem oneExitCore_map_cyclicLayer_le_succ
    (S : Finset ℕ) (X k : ℕ) :
    Submodule.map (Matrix.toEuclideanLin (oneExitCoreMatrix S X))
        (oneExitCyclicLayer S X k) ≤
      oneExitCyclicLayer S X (k + 1) := by
  rw [oneExitCyclicLayer, oneExitCyclicLayer, ← LinearMap.range_comp]
  have hmatrix :
      oneExitCoreMatrix S X *
          ((oneExitCoreMatrix S X) ^ k * oneExitSourceMatrix S X) =
        (oneExitCoreMatrix S X) ^ (k + 1) * oneExitSourceMatrix S X := by
    rw [pow_succ']
    simp only [Matrix.mul_assoc]
  have hlin :
      Matrix.toEuclideanLin (oneExitCoreMatrix S X) ∘ₗ
          Matrix.toEuclideanLin
            ((oneExitCoreMatrix S X) ^ k * oneExitSourceMatrix S X) =
        Matrix.toEuclideanLin
          ((oneExitCoreMatrix S X) ^ (k + 1) * oneExitSourceMatrix S X) := by
    rw [← Matrix.toLpLin_mul_same]
    exact congrArg Matrix.toEuclideanLin hmatrix
  rw [hlin]

theorem oneExitCyclicSubspace_mem_invtSubmodule
    (S : Finset ℕ) (X : ℕ) :
    oneExitCyclicSubspace S X ∈
      Module.End.invtSubmodule
        (Matrix.toEuclideanLin (oneExitCoreMatrix S X)) := by
  rw [Module.End.mem_invtSubmodule_iff_map_le]
  rw [oneExitCyclicSubspace, Submodule.map_iSup]
  exact iSup_le fun k ↦
    (oneExitCore_map_cyclicLayer_le_succ S X k).trans
      (le_iSup (fun j : ℕ ↦ oneExitCyclicLayer S X j) (k + 1))

theorem oneExitCyclicSubspace_orthogonal_mem_invtSubmodule
    (S : Finset ℕ) (X : ℕ) :
    (oneExitCyclicSubspace S X)ᗮ ∈
      Module.End.invtSubmodule
        (Matrix.toEuclideanLin (oneExitCoreMatrix S X)) := by
  have hsym :
      (Matrix.toEuclideanLin (oneExitCoreMatrix S X)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (oneExitCoreMatrix_isHermitian S X)
  exact hsym.orthogonalComplement_mem_invtSubmodule
    (oneExitCyclicSubspace_mem_invtSubmodule S X)

def oneExitCyclicProjection (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  Matrix.toEuclideanLin.symm
    (oneExitCyclicSubspace S X).starProjection.toLinearMap

theorem oneExitCyclicProjection_toEuclideanLin
    (S : Finset ℕ) (X : ℕ) :
    Matrix.toEuclideanLin (oneExitCyclicProjection S X) =
      (oneExitCyclicSubspace S X).starProjection.toLinearMap := by
  exact Matrix.toEuclideanLin.apply_symm_apply _

theorem oneExitCyclicProjection_isStarProjection
    (S : Finset ℕ) (X : ℕ) :
    IsStarProjection (oneExitCyclicProjection S X) := by
  constructor
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same,
      oneExitCyclicProjection_toEuclideanLin]
    rw [← Module.End.mul_eq_comp]
    simpa using congrArg ContinuousLinearMap.toLinearMap
      (oneExitCyclicSubspace S X).isIdempotentElem_starProjection
  · apply Matrix.IsHermitian.isSelfAdjoint
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [oneExitCyclicProjection_toEuclideanLin]
    exact (oneExitCyclicSubspace S X).starProjection_isSymmetric


/- Source slice: OneExitCompression.lean -/

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

theorem positiveStarProjection_mul_complement
    (S : Finset ℕ) (X : ℕ) :
    positiveStarProjection S X * positiveStarComplementProjection S X = 0 := by
  rw [positiveStarComplementProjection, Matrix.mul_sub, Matrix.mul_one]
  exact sub_eq_zero.mpr
    (positiveStarProjection_isStarProjection S X).isIdempotentElem.eq.symm

theorem positiveStarComplement_mul_oneExitCore
    (S : Finset ℕ) (X : ℕ) :
    positiveStarComplementProjection S X * oneExitCoreMatrix S X =
      oneExitCoreMatrix S X := by
  rw [oneExitCoreMatrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [(positiveStarComplementProjection_isStarProjection S X).isIdempotentElem]

theorem positiveStarComplement_mul_oneExitSource
    (S : Finset ℕ) (X : ℕ) :
    positiveStarComplementProjection S X * oneExitSourceMatrix S X =
      oneExitSourceMatrix S X := by
  rw [oneExitSourceMatrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [(positiveStarComplementProjection_isStarProjection S X).isIdempotentElem]

theorem positiveStarComplement_mul_cyclicSource
    (S : Finset ℕ) (X k : ℕ) :
    positiveStarComplementProjection S X *
        ((oneExitCoreMatrix S X) ^ k * oneExitSourceMatrix S X) =
      (oneExitCoreMatrix S X) ^ k * oneExitSourceMatrix S X := by
  cases k with
  | zero =>
      simpa using positiveStarComplement_mul_oneExitSource S X
  | succ k =>
      rw [pow_succ', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, positiveStarComplement_mul_oneExitCore,
        Matrix.mul_assoc]

theorem positiveStarProjection_mul_cyclicSource
    (S : Finset ℕ) (X k : ℕ) :
    positiveStarProjection S X *
        ((oneExitCoreMatrix S X) ^ k * oneExitSourceMatrix S X) = 0 := by
  let Q := positiveStarComplementProjection S X
  let F := (oneExitCoreMatrix S X) ^ k * oneExitSourceMatrix S X
  have hQF : Q * F = F :=
    positiveStarComplement_mul_cyclicSource S X k
  calc
    positiveStarProjection S X * F =
        positiveStarProjection S X * (Q * F) := by rw [hQF]
    _ = (positiveStarProjection S X * Q) * F := by
      rw [Matrix.mul_assoc]
    _ = 0 := by rw [positiveStarProjection_mul_complement, Matrix.zero_mul]

theorem oneExitCyclicSubspace_le_ker_positiveStarProjection
    (S : Finset ℕ) (X : ℕ) :
    oneExitCyclicSubspace S X ≤
      LinearMap.ker (Matrix.toEuclideanLin (positiveStarProjection S X)) := by
  rw [oneExitCyclicSubspace]
  refine iSup_le fun k ↦ ?_
  intro x hx
  rcases hx with ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  have h := congrArg Matrix.toEuclideanLin
    (positiveStarProjection_mul_cyclicSource S X k)
  have hy := congrArg (fun T ↦ T y) h
  simpa [Matrix.toLpLin_mul_same] using hy

theorem positiveStarProjection_mul_cyclicProjection
    (S : Finset ℕ) (X : ℕ) :
    positiveStarProjection S X * oneExitCyclicProjection S X = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same,
    oneExitCyclicProjection_toEuclideanLin]
  apply LinearMap.ext
  intro x
  have hx : (oneExitCyclicSubspace S X).starProjection x ∈
      oneExitCyclicSubspace S X :=
    Submodule.starProjection_apply_mem _ _
  have hker := LinearMap.mem_ker.mp
    (oneExitCyclicSubspace_le_ker_positiveStarProjection S X hx)
  simpa using hker

theorem oneExitCyclicProjection_mul_positiveStarProjection
    (S : Finset ℕ) (X : ℕ) :
    oneExitCyclicProjection S X * positiveStarProjection S X = 0 := by
  have hP : (positiveStarProjection S X).IsHermitian :=
    (positiveStarProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hE : (oneExitCyclicProjection S X).IsHermitian :=
    (oneExitCyclicProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have h := congrArg Matrix.conjTranspose
    (positiveStarProjection_mul_cyclicProjection S X)
  simpa [Matrix.conjTranspose_mul, hP.eq, hE.eq] using h

def oneExitProjection (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  positiveStarProjection S X + oneExitCyclicProjection S X

theorem oneExitCyclicProjection_mul_oneExitProjection
    (S : Finset ℕ) (X : ℕ) :
    oneExitCyclicProjection S X * oneExitProjection S X =
      oneExitCyclicProjection S X := by
  rw [oneExitProjection, Matrix.mul_add,
    oneExitCyclicProjection_mul_positiveStarProjection,
    (oneExitCyclicProjection_isStarProjection S X).isIdempotentElem,
    zero_add]

theorem oneExitProjection_isStarProjection
    (S : Finset ℕ) (X : ℕ) :
    IsStarProjection (oneExitProjection S X) := by
  constructor
  · change (positiveStarProjection S X + oneExitCyclicProjection S X) *
        (positiveStarProjection S X + oneExitCyclicProjection S X) =
      positiveStarProjection S X + oneExitCyclicProjection S X
    rw [add_mul, Matrix.mul_add, Matrix.mul_add,
      (positiveStarProjection_isStarProjection S X).isIdempotentElem,
      positiveStarProjection_mul_cyclicProjection,
      oneExitCyclicProjection_mul_positiveStarProjection,
      (oneExitCyclicProjection_isStarProjection S X).isIdempotentElem]
    abel
  · apply Matrix.IsHermitian.isSelfAdjoint
    exact Matrix.IsHermitian.add
      (positiveStarProjection_isStarProjection S X).isSelfAdjoint.isHermitian
      (oneExitCyclicProjection_isStarProjection S X).isSelfAdjoint.isHermitian

def oneExitComplementProjection (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  1 - oneExitProjection S X

theorem oneExitComplementProjection_isStarProjection
    (S : Finset ℕ) (X : ℕ) :
    IsStarProjection (oneExitComplementProjection S X) := by
  exact (oneExitProjection_isStarProjection S X).one_sub

theorem oneExitComplementProjection_mul_oneExitProjection
    (S : Finset ℕ) (X : ℕ) :
    oneExitComplementProjection S X * oneExitProjection S X = 0 := by
  rw [oneExitComplementProjection, Matrix.sub_mul, Matrix.one_mul,
    (oneExitProjection_isStarProjection S X).isIdempotentElem, sub_self]

theorem oneExitCyclicProjection_mul_oneExitComplementProjection
    (S : Finset ℕ) (X : ℕ) :
    oneExitCyclicProjection S X * oneExitComplementProjection S X = 0 := by
  rw [oneExitComplementProjection, Matrix.mul_sub, Matrix.mul_one,
    oneExitCyclicProjection_mul_oneExitProjection, sub_self]

theorem oneExitComplementProjection_mul_oneExitCyclicProjection
    (S : Finset ℕ) (X : ℕ) :
    oneExitComplementProjection S X * oneExitCyclicProjection S X = 0 := by
  have hE : (oneExitCyclicProjection S X).IsHermitian :=
    (oneExitCyclicProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hF : (oneExitComplementProjection S X).IsHermitian :=
    (oneExitComplementProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have h := congrArg Matrix.conjTranspose
    (oneExitCyclicProjection_mul_oneExitComplementProjection S X)
  simpa [Matrix.conjTranspose_mul, hE.eq, hF.eq] using h

theorem oneExitComplementProjection_mul_positiveStarProjection
    (S : Finset ℕ) (X : ℕ) :
    oneExitComplementProjection S X * positiveStarProjection S X = 0 := by
  have hQP : oneExitProjection S X * positiveStarProjection S X =
      positiveStarProjection S X := by
    rw [oneExitProjection, Matrix.add_mul,
      (positiveStarProjection_isStarProjection S X).isIdempotentElem,
      oneExitCyclicProjection_mul_positiveStarProjection, add_zero]
  calc
    oneExitComplementProjection S X * positiveStarProjection S X =
        oneExitComplementProjection S X *
          (oneExitProjection S X * positiveStarProjection S X) := by rw [hQP]
    _ = 0 := by
      rw [← Matrix.mul_assoc,
        oneExitComplementProjection_mul_oneExitProjection, Matrix.zero_mul]

theorem positiveStarProjection_mul_oneExitComplementProjection
    (S : Finset ℕ) (X : ℕ) :
    positiveStarProjection S X * oneExitComplementProjection S X = 0 := by
  have hP : (positiveStarProjection S X).IsHermitian :=
    (positiveStarProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hF : (oneExitComplementProjection S X).IsHermitian :=
    (oneExitComplementProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have h := congrArg Matrix.conjTranspose
    (oneExitComplementProjection_mul_positiveStarProjection S X)
  simpa [Matrix.conjTranspose_mul, hP.eq, hF.eq] using h

theorem oneExitCyclicProjection_mul_oneExitSourceMatrix
    (S : Finset ℕ) (X : ℕ) :
    oneExitCyclicProjection S X * oneExitSourceMatrix S X =
      oneExitSourceMatrix S X := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, oneExitCyclicProjection_toEuclideanLin]
  apply LinearMap.ext
  intro x
  exact Submodule.starProjection_eq_self_iff.mpr
    (oneExitSource_range_le_cyclicSubspace S X ⟨x, rfl⟩)

theorem oneExitProjection_mul_oneExitSourceMatrix
    (S : Finset ℕ) (X : ℕ) :
    oneExitProjection S X * oneExitSourceMatrix S X =
      oneExitSourceMatrix S X := by
  have hPsource : positiveStarProjection S X * oneExitSourceMatrix S X = 0 := by
    simpa using positiveStarProjection_mul_cyclicSource S X 0
  rw [oneExitProjection, Matrix.add_mul,
    hPsource,
    oneExitCyclicProjection_mul_oneExitSourceMatrix, zero_add]

theorem oneExitComplementProjection_mul_oneExitSourceMatrix
    (S : Finset ℕ) (X : ℕ) :
    oneExitComplementProjection S X * oneExitSourceMatrix S X = 0 := by
  rw [oneExitComplementProjection, Matrix.sub_mul, Matrix.one_mul,
    oneExitProjection_mul_oneExitSourceMatrix, sub_self]

def oneExitCompression (S : Finset ℕ) (X : ℕ) :
    Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ :=
  oneExitProjection S X * moleculeFamilyComplexAdjacency S X *
    oneExitProjection S X

theorem oneExitCompression_isHermitian (S : Finset ℕ) (X : ℕ) :
    (oneExitCompression S X).IsHermitian := by
  have hR : (oneExitProjection S X).IsHermitian :=
    (oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  simpa [oneExitCompression, hR.eq] using
    Matrix.isHermitian_conjTranspose_mul_mul (oneExitProjection S X)
      (moleculeFamilyComplexAdjacency_isHermitian S X)

theorem oneExitCompression_isSymmetric (S : Finset ℕ) (X : ℕ) :
    (Matrix.toEuclideanLin (oneExitCompression S X)).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (oneExitCompression_isHermitian S X)


/- Source slice: CyclicSpectralCapture.lean -/

open scoped InnerProductSpace

theorem oneExitCyclicProjection_commutes_core
    (S : Finset ℕ) (X : ℕ) :
    Commute (oneExitCyclicProjection S X) (oneExitCoreMatrix S X) := by
  have hlinear : Commute
      (oneExitCyclicSubspace S X).starProjection.toLinearMap
      (Matrix.toEuclideanLin (oneExitCoreMatrix S X)) := by
    have hIdem : IsIdempotentElem
        (oneExitCyclicSubspace S X).starProjection.toLinearMap := by
      unfold IsIdempotentElem
      rw [← ContinuousLinearMap.toLinearMap_mul]
      exact congrArg ContinuousLinearMap.toLinearMap
        (oneExitCyclicSubspace S X).isIdempotentElem_starProjection
    apply LinearMap.IsIdempotentElem.commute_iff hIdem |>.2
    simpa [Submodule.range_starProjection, Submodule.ker_starProjection] using And.intro
      (oneExitCyclicSubspace_mem_invtSubmodule S X)
      (oneExitCyclicSubspace_orthogonal_mem_invtSubmodule S X)
  apply Matrix.toEuclideanLin.injective
  simpa only [Matrix.toLpLin_mul_same,
    oneExitCyclicProjection_toEuclideanLin,
    ← Module.End.mul_eq_comp] using hlinear.eq


/- Source slice: PositiveStarCapture.lean -/

def positiveStarCenterOf
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    PositiveStarCenter S X :=
  ⟨a, ha, hd⟩

theorem positiveStarFrame_mulVec_single_center
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    (positiveStarFrame S X).mulVec
        (Pi.single (positiveStarCenterOf a ha hd) 1) =
      PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a) := by
  rw [Matrix.mulVec_single_one]
  funext v
  rfl

theorem positiveStarProjection_fixes_complexified_positiveStarMode
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin (positiveStarProjection S X)
        (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)) =
      PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a) := by
  let e : PositiveStarCenter S X → ℂ :=
    Pi.single (positiveStarCenterOf a ha hd) 1
  have hcolumn : (positiveStarFrame S X).mulVec e =
      PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a) := by
    simpa [e] using positiveStarFrame_mulVec_single_center ha hd
  have hmatrix := congrArg (fun M ↦ M.mulVec e)
    (positiveStarProjection_mul_frame S X)
  have hmulVec :
      (positiveStarProjection S X).mulVec
          (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)) =
        PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a) := by
    rw [← hcolumn]
    simpa only [Matrix.mulVec_mulVec] using hmatrix
  apply PiLp.ext
  intro v
  rw [Matrix.toLpLin_toLp, Matrix.toLin'_apply]
  exact congrFun hmulVec v


/- Source slice: NegativeStarSimplicity.lean -/

open scoped InnerProductSpace

local instance negativeStarLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _


/- Source slice: NegativeStarCapture.lean -/

open scoped InnerProductSpace

local instance negativeStarCaptureLargePrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel
      (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

theorem oneExitLargePrimeMatrix_complexify
    (S : Finset ℕ) (X : ℕ)
    (x : EuclideanSpace ℝ (PrimeStar.Vertex S X)) :
    Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
        (PrimeStar.complexifyEuclidean x) =
      PrimeStar.complexifyEuclidean
        (Matrix.toEuclideanLin
          ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) x) := by
  apply PiLp.ext
  intro i
  simp only [oneExitLargePrimeMatrix, Matrix.toLpLin_apply,
    PrimeStar.complexifyEuclidean_apply]
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show (PrimeStar.complexifyEuclidean x).ofLp j = (x.ofLp j : ℂ) from rfl]
  by_cases hij : (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
  · rw [if_pos hij, if_pos hij]
    norm_num
  · rw [if_neg hij, if_neg hij]
    norm_num


/- Source slice: LargePrimePositiveProjectionCommute.lean -/

local instance positiveProjectionCommuteLargePrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel
      (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

local instance positiveProjectionCommuteSmallPrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

private theorem complexifyRealMatrix_add_oneExit
    {m n : Type*} (A B : Matrix m n ℝ) :
    complexifyRealMatrix (A + B) =
      complexifyRealMatrix A + complexifyRealMatrix B := by
  ext i j
  simp [complexifyRealMatrix]

def positiveStarEnergyMatrix (S : Finset ℕ) (X : ℕ) :
    Matrix (PositiveStarCenter S X) (PositiveStarCenter S X) ℂ :=
  Matrix.diagonal fun a ↦
    (Real.sqrt
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a.1 : ℝ) : ℂ)

theorem oneExitLargePrimeMatrix_apply_complexified_positiveStarMode
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) :
    Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
        (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)) =
      (Real.sqrt
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) : ℂ) •
        PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a) := by
  have hLreal := PrimeStar.largePrime_toEuclideanLin_normalizedStarMode
    (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
    (PrimeStar.sqrtCutoff_condition X) ha (by norm_num : (1 : ℝ) ^ 2 = 1)
  rw [oneExitLargePrimeMatrix_complexify]
  change PrimeStar.complexifyEuclidean
      (Matrix.toEuclideanLin
        ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (PrimeStar.largePrimeNormalizedStarMode S X
          (squareRootCutoff X) a 1)) = _
  rw [hLreal,
    PrimeStar.complexifyEuclidean_smul]
  norm_num
  rfl

theorem oneExitLargePrimeMatrix_mul_positiveStarFrame
    (S : Finset ℕ) (X : ℕ) :
    oneExitLargePrimeMatrix S X * positiveStarFrame S X =
      positiveStarFrame S X * positiveStarEnergyMatrix S X := by
  ext v a
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single a]
  · have heig := oneExitLargePrimeMatrix_apply_complexified_positiveStarMode
      (S := S) (X := X) (a := a.1) a.2.1
    have hv := congrArg (fun z ↦ z v) heig
    simpa [positiveStarFrame, positiveStarFrameReal, complexifyRealMatrix,
      positiveStarEnergyMatrix, Matrix.mulVec, dotProduct, mul_comm] using hv
  · intro b _hb hba
    simp [positiveStarEnergyMatrix, hba]
  · intro haNot
    exact False.elim (haNot (Finset.mem_univ a))

theorem positiveStarEnergyMatrix_isHermitian
    (S : Finset ℕ) (X : ℕ) :
    (positiveStarEnergyMatrix S X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  by_cases h : a = b
  · subst b
    simp [positiveStarEnergyMatrix]
  · simp [positiveStarEnergyMatrix, h, Ne.symm h]

theorem positiveStarProjection_commutes_oneExitLargePrimeMatrix
    (S : Finset ℕ) (X : ℕ) :
    Commute (positiveStarProjection S X) (oneExitLargePrimeMatrix S X) := by
  let U := positiveStarFrame S X
  let D := positiveStarEnergyMatrix S X
  let L := oneExitLargePrimeMatrix S X
  have hLU : L * U = U * D := by
    simpa [L, U, D] using oneExitLargePrimeMatrix_mul_positiveStarFrame S X
  have hL : L.IsHermitian :=
    (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix ℂ
  have hD : D.IsHermitian := by
    simpa [D] using positiveStarEnergyMatrix_isHermitian S X
  have hUL : U.conjTranspose * L = D * U.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hLU
    simpa [Matrix.conjTranspose_mul, hL.eq, hD.eq] using h
  apply Commute.symm
  change L * (U * U.conjTranspose) = (U * U.conjTranspose) * L
  calc
    L * (U * U.conjTranspose) = (L * U) * U.conjTranspose := by
      rw [Matrix.mul_assoc]
    _ = (U * D) * U.conjTranspose := by rw [hLU]
    _ = U * (D * U.conjTranspose) := by rw [Matrix.mul_assoc]
    _ = U * (U.conjTranspose * L) := by rw [hUL]
    _ = (U * U.conjTranspose) * L := by rw [Matrix.mul_assoc]

theorem positiveStarComplement_commutes_oneExitLargePrimeMatrix
    (S : Finset ℕ) (X : ℕ) :
    Commute (positiveStarComplementProjection S X)
      (oneExitLargePrimeMatrix S X) := by
  change (1 - positiveStarProjection S X) * oneExitLargePrimeMatrix S X =
    oneExitLargePrimeMatrix S X * (1 - positiveStarProjection S X)
  rw [Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [(positiveStarProjection_commutes_oneExitLargePrimeMatrix S X).eq]

theorem oneExitCoreMatrix_apply_eq_largePrime_of_complement_fixed
    {S : Finset ℕ} {X : ℕ}
    {x : EuclideanSpace ℂ (PrimeStar.Vertex S X)}
    (hQ : Matrix.toEuclideanLin (positiveStarComplementProjection S X) x = x) :
    Matrix.toEuclideanLin (oneExitCoreMatrix S X) x =
      Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x := by
  have hcomm := positiveStarComplement_commutes_oneExitLargePrimeMatrix S X
  have happ := congrArg Matrix.toEuclideanLin hcomm.eq
  rw [oneExitCoreMatrix]
  simp only [Matrix.toLpLin_mul_same]
  change Matrix.toEuclideanLin (positiveStarComplementProjection S X)
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
        (Matrix.toEuclideanLin (positiveStarComplementProjection S X) x)) = _
  rw [hQ]
  have hswap : Matrix.toEuclideanLin (positiveStarComplementProjection S X)
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x) =
    Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
      (Matrix.toEuclideanLin (positiveStarComplementProjection S X) x) := by
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same] at happ
    exact LinearMap.congr_fun happ x
  rw [hswap, hQ]

theorem positiveStarComplement_mul_oneExitCyclicProjection
    (S : Finset ℕ) (X : ℕ) :
    positiveStarComplementProjection S X *
        oneExitCyclicProjection S X =
      oneExitCyclicProjection S X := by
  rw [positiveStarComplementProjection, Matrix.sub_mul, Matrix.one_mul,
    positiveStarProjection_mul_cyclicProjection, sub_zero]

theorem oneExitCyclicProjection_mul_positiveStarComplement
    (S : Finset ℕ) (X : ℕ) :
    oneExitCyclicProjection S X *
        positiveStarComplementProjection S X =
      oneExitCyclicProjection S X := by
  rw [positiveStarComplementProjection, Matrix.mul_sub, Matrix.mul_one,
    oneExitCyclicProjection_mul_positiveStarProjection, sub_zero]

theorem oneExitCyclicProjection_commutes_oneExitLargePrimeMatrix
    (S : Finset ℕ) (X : ℕ) :
    Commute (oneExitCyclicProjection S X)
      (oneExitLargePrimeMatrix S X) := by
  let E := oneExitCyclicProjection S X
  let Q := positiveStarComplementProjection S X
  let L := oneExitLargePrimeMatrix S X
  let C := oneExitCoreMatrix S X
  have hEQ : E * Q = E := by
    simpa [E, Q] using
      oneExitCyclicProjection_mul_positiveStarComplement S X
  have hQE : Q * E = E := by
    simpa [E, Q] using
      positiveStarComplement_mul_oneExitCyclicProjection S X
  have hQL : Q * L = L * Q := by
    simpa [Q, L] using
      (positiveStarComplement_commutes_oneExitLargePrimeMatrix S X).eq
  have hEC : E * C = C * E := by
    simpa [E, C] using (oneExitCyclicProjection_commutes_core S X).eq
  have hEL : E * L = E * C := by
    symm
    calc
      E * C = E * (Q * (L * Q)) := by
        change E * (Q * L * Q) = E * (Q * (L * Q))
        simp only [Matrix.mul_assoc]
      _ = (E * Q) * (L * Q) := by rw [Matrix.mul_assoc]
      _ = E * (L * Q) := by rw [hEQ]
      _ = E * (Q * L) := by rw [hQL]
      _ = (E * Q) * L := by rw [Matrix.mul_assoc]
      _ = E * L := by rw [hEQ]
  have hLE : L * E = C * E := by
    symm
    calc
      C * E = (Q * L) * (Q * E) := by
        change (Q * L * Q) * E = (Q * L) * (Q * E)
        simp only [Matrix.mul_assoc]
      _ = (Q * L) * E := by rw [hQE]
      _ = (L * Q) * E := by rw [hQL]
      _ = L * (Q * E) := by rw [Matrix.mul_assoc]
      _ = L * E := by rw [hQE]
  change E * L = L * E
  rw [hEL, hLE, hEC]

theorem moleculeFamilyComplexAdjacency_eq_large_add_small
    (S : Finset ℕ) (X : ℕ) :
    moleculeFamilyComplexAdjacency S X =
      oneExitLargePrimeMatrix S X + oneExitSmallPrimeMatrix S X := by
  rw [moleculeFamilyComplexAdjacency]
  rw [PrimeStar.primeCover_adjMatrix_eq_large_add_small
    S X (squareRootCutoff X)]
  have hL :
      complexifyRealMatrix
          ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) =
        (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℂ := by
    ext v w
    simp only [complexifyRealMatrix, SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have hH :
      complexifyRealMatrix
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) =
        (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℂ := by
    ext v w
    simp only [complexifyRealMatrix, SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  rw [complexifyRealMatrix_add_oneExit, hL, hH]
  rfl

theorem oneExitComplement_mul_adjacency_mul_positiveStar_eq_zero
    (S : Finset ℕ) (X : ℕ) :
    oneExitComplementProjection S X *
        moleculeFamilyComplexAdjacency S X *
        positiveStarProjection S X = 0 := by
  let F := oneExitComplementProjection S X
  let P := positiveStarProjection S X
  let Q := positiveStarComplementProjection S X
  let L := oneExitLargePrimeMatrix S X
  let H := oneExitSmallPrimeMatrix S X
  have hFP : F * P = 0 := by
    simpa [F, P] using
      oneExitComplementProjection_mul_positiveStarProjection S X
  have hFQ : F * Q = F := by
    change F * (1 - P) = F
    rw [Matrix.mul_sub, Matrix.mul_one, hFP, sub_zero]
  have hFLP : F * L * P = 0 := by
    calc
      F * L * P = F * (L * P) := by rw [Matrix.mul_assoc]
      _ = F * (P * L) := by
        rw [← (positiveStarProjection_commutes_oneExitLargePrimeMatrix S X).eq]
      _ = (F * P) * L := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hFP, Matrix.zero_mul]
  have hFHP : F * H * P = 0 := by
    calc
      F * H * P = (F * Q) * H * P := by rw [hFQ]
      _ = F * (Q * H * P) := by simp only [Matrix.mul_assoc]
      _ = F * oneExitSourceMatrix S X := by rw [oneExitSourceMatrix]
      _ = 0 := by
        simpa [F] using oneExitComplementProjection_mul_oneExitSourceMatrix S X
  rw [moleculeFamilyComplexAdjacency_eq_large_add_small]
  change F * (L + H) * P = 0
  rw [Matrix.mul_add, Matrix.add_mul, hFLP, hFHP, add_zero]

theorem oneExitComplement_mul_adjacency_mul_cyclic_eq_smallPrime
    (S : Finset ℕ) (X : ℕ) :
    oneExitComplementProjection S X *
        moleculeFamilyComplexAdjacency S X *
        oneExitCyclicProjection S X =
      oneExitComplementProjection S X * oneExitSmallPrimeMatrix S X *
        oneExitCyclicProjection S X := by
  let F := oneExitComplementProjection S X
  let E := oneExitCyclicProjection S X
  let L := oneExitLargePrimeMatrix S X
  let H := oneExitSmallPrimeMatrix S X
  have hFE : F * E = 0 := by
    simpa [F, E] using
      oneExitComplementProjection_mul_oneExitCyclicProjection S X
  have hFLE : F * L * E = 0 := by
    calc
      F * L * E = F * (L * E) := by rw [Matrix.mul_assoc]
      _ = F * (E * L) := by
        rw [← (oneExitCyclicProjection_commutes_oneExitLargePrimeMatrix S X).eq]
      _ = (F * E) * L := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hFE, Matrix.zero_mul]
  rw [moleculeFamilyComplexAdjacency_eq_large_add_small]
  change F * (L + H) * E = F * H * E
  rw [Matrix.mul_add, Matrix.add_mul, hFLE, zero_add]


/- Source slice: TwoStageSchurParameters.lean -/

theorem twoStageSchur_parameter_margins
    {beta rho : ℝ} (hbeta : 0 ≤ beta) (hrho : 0 < rho)
    (hscale : 4 * beta ≤ rho) :
    let delta := 3 * beta ^ 4 / rho ^ 3
    let z := rho + delta
    let s := beta ^ 2 / (z - beta)
    0 ≤ delta ∧ beta < z ∧ 0 ≤ s ∧ s ≤ beta / 3 ∧
      2 * rho / 3 ≤ z - s - beta ∧
      3 * rho / 4 ≤ rho - beta := by
  dsimp only
  let delta := 3 * beta ^ 4 / rho ^ 3
  let z := rho + delta
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hzbeta : 3 * rho / 4 ≤ z - beta := by
    dsimp [z]
    linarith
  have hzbetaPos : 0 < z - beta := lt_of_lt_of_le (by positivity) hzbeta
  let s := beta ^ 2 / (z - beta)
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hscaleMul : 4 * beta * beta ≤ rho * beta :=
    mul_le_mul_of_nonneg_right hscale hbeta
  have hsUpper : s ≤ beta / 3 := by
    dsimp [s]
    rw [div_le_iff₀ hzbetaPos]
    have hmul := mul_le_mul_of_nonneg_left hzbeta (div_nonneg hbeta (by norm_num : (0 : ℝ) ≤ 3))
    nlinarith
  have hgap : 2 * rho / 3 ≤ z - s - beta := by
    have hbetaUpper : beta ≤ rho / 4 := by linarith
    dsimp [z]
    linarith
  have hrhoBeta : 3 * rho / 4 ≤ rho - beta := by linarith
  exact ⟨hdelta, by linarith, hs, hsUpper, hgap, hrhoBeta⟩

theorem twoStageSchur_s_le_four_mul_sq_div_three_mul
    {beta rho : ℝ} (hrho : 0 < rho)
    (hscale : 4 * beta ≤ rho) :
    let delta := 3 * beta ^ 4 / rho ^ 3
    let z := rho + delta
    beta ^ 2 / (z - beta) ≤ 4 * beta ^ 2 / (3 * rho) := by
  dsimp only
  let delta := 3 * beta ^ 4 / rho ^ 3
  let z := rho + delta
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hzbeta : 3 * rho / 4 ≤ z - beta := by
    dsimp [z]
    linarith
  have hthreeRho : 0 < 3 * rho := by positivity
  calc
    beta ^ 2 / (z - beta) ≤ beta ^ 2 / (3 * rho / 4) :=
      div_le_div_of_nonneg_left (sq_nonneg beta) (by positivity) hzbeta
    _ = 4 * beta ^ 2 / (3 * rho) := by
      field_simp

theorem twoStageSchur_resolvent_error_le
    {beta rho : ℝ} (hbeta : 0 ≤ beta) (hrho : 0 < rho)
    (hscale : 4 * beta ≤ rho) :
    let delta := 3 * beta ^ 4 / rho ^ 3
    let z := rho + delta
    let s := beta ^ 2 / (z - beta)
    delta < s →
      beta ^ 2 * (s - delta) /
          ((z - s - beta) * (rho - beta)) ≤
        8 * beta ^ 4 / (3 * rho ^ 3) := by
  dsimp only
  let delta := 3 * beta ^ 4 / rho ^ 3
  let z := rho + delta
  let s := beta ^ 2 / (z - beta)
  intro hdeltaS
  have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
  dsimp only at hparams
  rcases hparams with
    ⟨hdelta, _hzbeta, hs, _hsCoarse, hgap, hrhoBeta⟩
  have hsSharp :=
    twoStageSchur_s_le_four_mul_sq_div_three_mul hrho hscale
  dsimp only at hsSharp
  have hdenLower : rho ^ 2 / 2 ≤
      (z - s - beta) * (rho - beta) := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hgap) (sub_nonneg.mpr hrhoBeta)
    nlinarith
  have hdenPos : 0 < (z - s - beta) * (rho - beta) := by
    have hleft : 0 < z - s - beta :=
      lt_of_lt_of_le (by positivity) hgap
    have hright : 0 < rho - beta :=
      lt_of_lt_of_le (by positivity) hrhoBeta
    positivity
  have hnum : beta ^ 2 * (s - delta) ≤ beta ^ 2 * s := by
    exact mul_le_mul_of_nonneg_left (sub_le_self s hdelta) (sq_nonneg beta)
  calc
    beta ^ 2 * (s - delta) /
          ((z - s - beta) * (rho - beta)) ≤
        (beta ^ 2 * s) /
          ((z - s - beta) * (rho - beta)) :=
      (div_le_div_iff_of_pos_right hdenPos).2 hnum
    _ ≤ (beta ^ 2 * (4 * beta ^ 2 / (3 * rho))) /
          ((z - s - beta) * (rho - beta)) := by
      apply (div_le_div_iff_of_pos_right hdenPos).2
      exact mul_le_mul_of_nonneg_left hsSharp (sq_nonneg beta)
    _ ≤ (beta ^ 2 * (4 * beta ^ 2 / (3 * rho))) /
          (rho ^ 2 / 2) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact hdenLower
    _ = 8 * beta ^ 4 / (3 * rho ^ 3) := by
      field_simp
      ring

theorem twoStageSchur_resolvent_error_lt_delta
    {beta rho : ℝ} (hbeta : 0 ≤ beta) (hrho : 0 < rho)
    (hscale : 4 * beta ≤ rho) :
    let delta := 3 * beta ^ 4 / rho ^ 3
    let z := rho + delta
    let s := beta ^ 2 / (z - beta)
    delta < s →
      beta ^ 2 * (s - delta) /
          ((z - s - beta) * (rho - beta)) < delta := by
  dsimp only
  let delta := 3 * beta ^ 4 / rho ^ 3
  let z := rho + delta
  let s := beta ^ 2 / (z - beta)
  intro hdeltaS
  have herror := twoStageSchur_resolvent_error_le hbeta hrho hscale hdeltaS
  have hbetaPos : 0 < beta := by
    by_contra hnot
    have hzero : beta = 0 := le_antisymm (le_of_not_gt hnot) hbeta
    subst beta
    simp at hdeltaS
  have hratio : 0 < beta ^ 4 / rho ^ 3 := by positivity
  have hconst : 8 * beta ^ 4 / (3 * rho ^ 3) <
      3 * beta ^ 4 / rho ^ 3 := by
    calc
      8 * beta ^ 4 / (3 * rho ^ 3) =
          (8 / 3 : ℝ) * (beta ^ 4 / rho ^ 3) := by
        field_simp
      _ < 3 * (beta ^ 4 / rho ^ 3) := by nlinarith
      _ = 3 * beta ^ 4 / rho ^ 3 := by ring
  exact herror.trans_lt hconst


/- Source slice: ComplexNegativeStarSimplicity.lean -/

local instance complexNegativeStarLargePrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel
      (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

def complexEuclideanRealPart
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ (x i).re

def complexEuclideanImagPart
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ (x i).im

theorem complexify_realPart_add_I_imagPart
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    PrimeStar.complexifyEuclidean (complexEuclideanRealPart x) +
        Complex.I • PrimeStar.complexifyEuclidean (complexEuclideanImagPart x) = x := by
  apply PiLp.ext
  intro i
  apply Complex.ext <;>
    simp [complexEuclideanRealPart, complexEuclideanImagPart]

theorem oneExitLargePrimeMatrix_realPart_eigenvector
    {S : Finset ℕ} {X : ℕ}
    {x : EuclideanSpace ℂ (PrimeStar.Vertex S X)} {lambda : ℝ}
    (hx : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x =
      (lambda : ℂ) • x) :
    Matrix.toEuclideanLin
        ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (complexEuclideanRealPart x) =
      lambda • complexEuclideanRealPart x := by
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z ↦ (z i).re) hx
  simp only [oneExitLargePrimeMatrix, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, SimpleGraph.adjMatrix_apply, complexEuclideanRealPart] at hi ⊢
  have hsum :
      (∑ j, if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0).re =
        ∑ j, (if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0).re := by
    simpa only [Complex.reCLM_apply] using
      (map_sum Complex.reCLM
        (fun j ↦ if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0) Finset.univ)
  have hterms :
      (∑ j, (if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then (1 : ℂ) else 0) * x j) =
        ∑ j, if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0 := by
    apply Finset.sum_congr rfl
    intro j _hj
    split <;> simp
  rw [hterms, hsum] at hi
  have hpoint :
      (∑ j, (if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0).re) =
        ∑ j, if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then (x j).re else 0 := by
    apply Finset.sum_congr rfl
    intro j _hj
    split <;> simp
  rw [hpoint] at hi
  simpa [PiLp.smul_apply, smul_eq_mul] using hi

theorem oneExitLargePrimeMatrix_imagPart_eigenvector
    {S : Finset ℕ} {X : ℕ}
    {x : EuclideanSpace ℂ (PrimeStar.Vertex S X)} {lambda : ℝ}
    (hx : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x =
      (lambda : ℂ) • x) :
    Matrix.toEuclideanLin
        ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (complexEuclideanImagPart x) =
      lambda • complexEuclideanImagPart x := by
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z ↦ (z i).im) hx
  simp only [oneExitLargePrimeMatrix, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, SimpleGraph.adjMatrix_apply, complexEuclideanImagPart] at hi ⊢
  have hsum :
      (∑ j, if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0).im =
        ∑ j, (if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0).im := by
    simpa only [Complex.imCLM_apply] using
      (map_sum Complex.imCLM
        (fun j ↦ if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0) Finset.univ)
  have hterms :
      (∑ j, (if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then (1 : ℂ) else 0) * x j) =
        ∑ j, if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0 := by
    apply Finset.sum_congr rfl
    intro j _hj
    split <;> simp
  rw [hterms, hsum] at hi
  have hpoint :
      (∑ j, (if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then x j else 0).im) =
        ∑ j, if (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).Adj i j
          then (x j).im else 0 := by
    apply Finset.sum_congr rfl
    intro j _hj
    split <;> simp
  rw [hpoint] at hi
  simpa [PiLp.smul_apply, smul_eq_mul] using hi

theorem complement_fixes_oneExitCore_eigenvector_of_ne_zero
    {S : Finset ℕ} {X : ℕ}
    {x : EuclideanSpace ℂ (PrimeStar.Vertex S X)} {lambda : ℂ}
    (hlambda : lambda ≠ 0)
    (hx : Matrix.toEuclideanLin (oneExitCoreMatrix S X) x = lambda • x) :
    Matrix.toEuclideanLin (positiveStarComplementProjection S X) x = x := by
  have hQC := congrArg Matrix.toEuclideanLin
    (positiveStarComplement_mul_oneExitCore S X)
  rw [Matrix.toLpLin_mul_same] at hQC
  have happ := LinearMap.congr_fun hQC x
  have hsmul : lambda •
      Matrix.toEuclideanLin (positiveStarComplementProjection S X) x =
      lambda • x := by
    calc
      lambda • Matrix.toEuclideanLin (positiveStarComplementProjection S X) x =
          Matrix.toEuclideanLin (positiveStarComplementProjection S X)
            (lambda • x) := by simp
      _ = Matrix.toEuclideanLin (positiveStarComplementProjection S X)
            (Matrix.toEuclideanLin (oneExitCoreMatrix S X) x) := by rw [hx]
      _ = Matrix.toEuclideanLin (oneExitCoreMatrix S X) x := happ
      _ = lambda • x := hx
  exact smul_right_injective (EuclideanSpace ℂ (PrimeStar.Vertex S X)) hlambda hsmul


/- Source slice: PositiveStarClusterCapture.lean -/

local instance positiveClusterLargePrimeDecidableAdj
    (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj :=
  Classical.decRel _

theorem complexifyEuclidean_sum
    {I ι : Type*} [Fintype I] [Fintype ι]
    (f : I → EuclideanSpace ℝ ι) :
    PrimeStar.complexifyEuclidean (∑ i, f i) =
      ∑ i, PrimeStar.complexifyEuclidean (f i) := by
  apply PiLp.ext
  intro j
  simp [PrimeStar.complexifyEuclidean]

theorem largePrime_positive_eigenvector_eq_degreeFiber_sum
    {S : Finset ℕ} {X Y : ℕ} {mu : ℝ}
    (hcut : X < (Y + 1) * (Y + 1)) (hmu : 0 < mu)
    {x : EuclideanSpace ℝ (PrimeStar.Vertex S X)}
    (hx : Matrix.toEuclideanLin
        ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ) x = mu • x) :
    x = ∑ b : ↑(PrimeStar.largePrimePositiveDegreeFiber S X Y mu),
      (x b.1 / mu) •
        PrimeStar.largePrimeEuclideanStarVector S X Y b.1 1 := by
  let L := Matrix.toEuclideanLin
    ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ)
  let F := PrimeStar.largePrimePositiveDegreeFiber S X Y mu
  let y : EuclideanSpace ℝ (PrimeStar.Vertex S X) :=
    ∑ b : ↑F, (x b.1 / mu) •
      PrimeStar.largePrimeEuclideanStarVector S X Y b.1 1
  have hy : L y = mu • y := by
    dsimp [y]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [map_smul, smul_smul]
    have hbmem := PrimeStar.mem_largePrimePositiveDegreeFiber.mp b.property
    have hbeig := PrimeStar.largePrime_toEuclideanLin_signedStarVector
      (S := S) (X := X) (Y := Y) (c := b.1) hcut hbmem.1
      (by norm_num : (1 : ℝ) ^ 2 = 1)
    change L (PrimeStar.largePrimeEuclideanStarVector S X Y b.1 1) = _ at hbeig
    rw [hbeig, hbmem.2.2]
    module
  have hcentres : ∀ b : ↑F, y b.1 = x b.1 := by
    intro b
    dsimp only [y]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply]
    change (∑ i : ↑F, (x i.1 / mu) *
      PrimeStar.largePrimeEuclideanStarVector S X Y i.1 1 b.1) = x b.1
    rw [Finset.sum_eq_single b]
    · have hbmem := PrimeStar.mem_largePrimePositiveDegreeFiber.mp b.property
      rw [PrimeStar.largePrimeEuclideanStarVector_eq_starDataVector,
        PrimeStar.largePrimeStarDataVector_center]
      rw [hbmem.2.2]
      field_simp
    · intro i _hi hib
      have hi := PrimeStar.mem_largePrimePositiveDegreeFiber.mp i.property
      have hb := PrimeStar.mem_largePrimePositiveDegreeFiber.mp b.property
      have hibv : i.1 ≠ b.1 := fun h ↦ hib (Subtype.ext h)
      have hdisj := PrimeStar.disjoint_largePrimeStarSupport
        hcut hi.1 hb.1 hibv
      have hbmem : b.1 ∈ PrimeStar.largePrimeStarSupport S X Y b.1 := by
        simp [PrimeStar.largePrimeStarSupport]
      have hbnot : b.1 ∉ PrimeStar.largePrimeStarSupport S X Y i.1 := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem hbmem
      have hbleaf : b.1 ∉ PrimeStar.largePrimeLeaves S X Y i.1 := by
        intro hmem
        exact hbnot (by simp [PrimeStar.largePrimeStarSupport, hmem])
      rw [PrimeStar.largePrimeEuclideanStarVector_eq_starDataVector,
        PrimeStar.largePrimeStarDataVector_outside _ _ (Ne.symm hibv) hbleaf,
        mul_zero]
    · simp
  let xe : Module.End.eigenspace L mu :=
    ⟨x, Module.End.mem_eigenspace_iff.mpr (by simpa [L] using hx)⟩
  let ye : Module.End.eigenspace L mu :=
    ⟨y, Module.End.mem_eigenspace_iff.mpr (by simpa [L] using hy)⟩
  have hrestrict : PrimeStar.largePrimeEigenspaceCenterRestriction
      (S := S) (X := X) (Y := Y) mu xe =
      PrimeStar.largePrimeEigenspaceCenterRestriction
        (S := S) (X := X) (Y := Y) mu ye := by
    funext b
    exact (hcentres b).symm
  have hxy := PrimeStar.injective_largePrimeEigenspaceCenterRestriction
    (S := S) (X := X) (Y := Y) hcut hmu hrestrict
  exact congrArg Subtype.val hxy

theorem positiveStarProjection_fixes_complexified_positiveStarVector
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin (positiveStarProjection S X)
        (PrimeStar.complexifyEuclidean
          (PrimeStar.largePrimeEuclideanStarVector S X
            (squareRootCutoff X) a 1)) =
      PrimeStar.complexifyEuclidean
        (PrimeStar.largePrimeEuclideanStarVector S X
          (squareRootCutoff X) a 1) := by
  let v := PrimeStar.largePrimeEuclideanStarVector S X
    (squareRootCutoff X) a 1
  have hv : ‖v‖ • moleculePositiveStarMode S X a = v := by
    simp [v, moleculePositiveStarMode,
      PrimeStar.largePrimeNormalizedStarMode]
  have hfix := positiveStarProjection_fixes_complexified_positiveStarMode ha hd
  change Matrix.toEuclideanLin (positiveStarProjection S X)
      (PrimeStar.complexifyEuclidean v) = PrimeStar.complexifyEuclidean v
  rw [← hv, PrimeStar.complexifyEuclidean_smul, map_smul, hfix]

theorem positiveStarProjection_fixes_positive_forest_eigenvector
    {S : Finset ℕ} {X : ℕ} {mu : ℝ} (hmu : 0 < mu)
    {x : EuclideanSpace ℂ (PrimeStar.Vertex S X)}
    (hx : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x =
      (mu : ℂ) • x) :
    Matrix.toEuclideanLin (positiveStarProjection S X) x = x := by
  let xr := complexEuclideanRealPart x
  let xi := complexEuclideanImagPart x
  have hxr := oneExitLargePrimeMatrix_realPart_eigenvector
    (S := S) (X := X) (lambda := mu) hx
  have hxi := oneExitLargePrimeMatrix_imagPart_eigenvector
    (S := S) (X := X) (lambda := mu) hx
  have hxrSum := largePrime_positive_eigenvector_eq_degreeFiber_sum
    (PrimeStar.sqrtCutoff_condition X) hmu hxr
  have hxiSum := largePrime_positive_eigenvector_eq_degreeFiber_sum
    (PrimeStar.sqrtCutoff_condition X) hmu hxi
  have hfixReal : Matrix.toEuclideanLin (positiveStarProjection S X)
      (PrimeStar.complexifyEuclidean xr) =
      PrimeStar.complexifyEuclidean xr := by
    dsimp [xr]
    rw [hxrSum, complexifyEuclidean_sum, map_sum]
    simp only [PrimeStar.complexifyEuclidean_smul, map_smul]
    apply Finset.sum_congr rfl
    intro b _hb
    have hb := PrimeStar.mem_largePrimePositiveDegreeFiber.mp b.property
    rw [positiveStarProjection_fixes_complexified_positiveStarVector hb.1 hb.2.1]
  have hfixImag : Matrix.toEuclideanLin (positiveStarProjection S X)
      (PrimeStar.complexifyEuclidean xi) =
      PrimeStar.complexifyEuclidean xi := by
    dsimp [xi]
    rw [hxiSum, complexifyEuclidean_sum, map_sum]
    simp only [PrimeStar.complexifyEuclidean_smul, map_smul]
    apply Finset.sum_congr rfl
    intro b _hb
    have hb := PrimeStar.mem_largePrimePositiveDegreeFiber.mp b.property
    rw [positiveStarProjection_fixes_complexified_positiveStarVector hb.1 hb.2.1]
  rw [← complexify_realPart_add_I_imagPart x, map_add, map_smul,
    hfixReal, hfixImag]


/- Source slice: RCLikeOrderedCompressionInterlacing.lean -/

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private def rclikeOrderedEigenPrefix [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) : Submodule 𝕜 E :=
  Submodule.span 𝕜
    (Set.range fun j : ↥(Finset.Iic i) ↦ hT.eigenvectorBasis rfl j.1)

private def rclikeOrderedEigenSuffix [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) : Submodule 𝕜 E :=
  Submodule.span 𝕜
    (Set.range fun j : ↥(Finset.Ici i) ↦ hT.eigenvectorBasis rfl j.1)

private theorem finrank_rclikeOrderedEigenPrefix [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) :
    Module.finrank 𝕜 (rclikeOrderedEigenPrefix T hT i) = i.1 + 1 := by
  rw [rclikeOrderedEigenPrefix, finrank_span_eq_card]
  · calc
      Fintype.card ↥(Finset.Iic i) = (Finset.Iic i).card := Fintype.card_coe _
      _ = i.1 + 1 := Fin.card_Iic i
  · exact (hT.eigenvectorBasis rfl).orthonormal.linearIndependent.comp
      (fun j : ↥(Finset.Iic i) ↦ j.1) Subtype.val_injective

private theorem finrank_rclikeOrderedEigenSuffix [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) :
    Module.finrank 𝕜 (rclikeOrderedEigenSuffix T hT i) =
      Module.finrank 𝕜 E - i.1 := by
  rw [rclikeOrderedEigenSuffix, finrank_span_eq_card]
  · calc
      Fintype.card ↥(Finset.Ici i) = (Finset.Ici i).card := Fintype.card_coe _
      _ = Module.finrank 𝕜 E - i.1 := Fin.card_Ici i
  · exact (hT.eigenvectorBasis rfl).orthonormal.linearIndependent.comp
      (fun j : ↥(Finset.Ici i) ↦ j.1) Subtype.val_injective

private theorem rclikeOrderedEigenPrefix_repr_eq_zero_of_lt
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i k : Fin (Module.finrank 𝕜 E)) (x : E)
    (hx : x ∈ rclikeOrderedEigenPrefix T hT i) (hik : i < k) :
    (hT.eigenvectorBasis rfl).repr x k = 0 := by
  rw [rclikeOrderedEigenPrefix,
    Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp only [map_sum, map_smul]
  rw [WithLp.ofLp_sum]
  simp only [PiLp.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _hj
  rw [(hT.eigenvectorBasis rfl).repr_self]
  have hjk : (j.1 : Fin (Module.finrank 𝕜 E)) ≠ k := by
    intro h
    have : k ≤ i := by simpa [h] using j.2
    exact (not_le_of_gt hik) this
  simp [hjk]

private theorem rclikeOrderedEigenSuffix_repr_eq_zero_of_lt
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i k : Fin (Module.finrank 𝕜 E)) (x : E)
    (hx : x ∈ rclikeOrderedEigenSuffix T hT i) (hki : k < i) :
    (hT.eigenvectorBasis rfl).repr x k = 0 := by
  rw [rclikeOrderedEigenSuffix,
    Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp only [map_sum, map_smul]
  rw [WithLp.ofLp_sum]
  simp only [PiLp.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _hj
  rw [(hT.eigenvectorBasis rfl).repr_self]
  have hjk : (j.1 : Fin (Module.finrank 𝕜 E)) ≠ k := by
    intro h
    have : i ≤ k := by simpa [h] using j.2
    exact (not_le_of_gt hki) this
  simp [hjk]

private theorem rclike_re_inner_apply_eq_sum_eigenvalues
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) (x : E) :
    RCLike.re ⟪x, T x⟫_𝕜 =
      ∑ j, hT.eigenvalues rfl j *
        ‖(hT.eigenvectorBasis rfl).repr x j‖ ^ 2 := by
  let b := hT.eigenvectorBasis rfl
  calc
    RCLike.re ⟪x, T x⟫_𝕜 =
        RCLike.re (∑ j, ⟪x, b j⟫_𝕜 * ⟪b j, T x⟫_𝕜) := by
      rw [b.sum_inner_mul_inner]
    _ = ∑ j, hT.eigenvalues rfl j * ‖b.repr x j‖ ^ 2 := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      have hcoord := hT.eigenvectorBasis_apply_self_apply rfl x j
      change b.repr (T x) j =
        hT.eigenvalues rfl j * b.repr x j at hcoord
      have hxinner : ⟪b j, x⟫_𝕜 = b.repr x j :=
        (b.repr_apply_apply x j).symm
      have hxinner' : ⟪x, b j⟫_𝕜 = star (b.repr x j) := by
        calc
          ⟪x, b j⟫_𝕜 = star ⟪b j, x⟫_𝕜 :=
            (inner_conj_symm x (b j)).symm
          _ = star (b.repr x j) := congrArg star hxinner
      have hTxinner : ⟪b j, T x⟫_𝕜 = b.repr (T x) j :=
        (b.repr_apply_apply (T x) j).symm
      rw [hxinner', hTxinner, hcoord]
      rw [RCLike.mul_re]
      simp [RCLike.star_def, RCLike.mul_re, RCLike.norm_sq_eq_def]
      ring

private theorem rclike_eigenvalue_mul_norm_sq_le_re_inner_apply_of_mem_prefix
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) (x : E)
    (hx : x ∈ rclikeOrderedEigenPrefix T hT i) :
    hT.eigenvalues rfl i * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_𝕜 := by
  let b := hT.eigenvectorBasis rfl
  let ev := hT.eigenvalues rfl
  have hmono := hT.eigenvalues_antitone rfl
  have hsum :
      ∑ j, ev i * ‖b.repr x j‖ ^ 2 ≤
        ∑ j, ev j * ‖b.repr x j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hji : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hmono hji) (sq_nonneg _)
    · have hij : i < j := lt_of_not_ge hji
      have hz := rclikeOrderedEigenPrefix_repr_eq_zero_of_lt
        T hT i j x hx hij
      simp [b, hz]
  rw [rclike_re_inner_apply_eq_sum_eigenvalues T hT x]
  calc
    ev i * ‖x‖ ^ 2 = ∑ j, ev i * ‖b.repr x j‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [b.repr_apply_apply] using
        (b.sum_sq_norm_inner_right x).symm
    _ ≤ ∑ j, ev j * ‖b.repr x j‖ ^ 2 := hsum

private theorem rclike_re_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_suffix
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) (x : E)
    (hx : x ∈ rclikeOrderedEigenSuffix T hT i) :
    RCLike.re ⟪x, T x⟫_𝕜 ≤ hT.eigenvalues rfl i * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis rfl
  let ev := hT.eigenvalues rfl
  have hmono := hT.eigenvalues_antitone rfl
  have hsum :
      ∑ j, ev j * ‖b.repr x j‖ ^ 2 ≤
        ∑ j, ev i * ‖b.repr x j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hij : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hmono hij) (sq_nonneg _)
    · have hji : j < i := lt_of_not_ge hij
      have hz := rclikeOrderedEigenSuffix_repr_eq_zero_of_lt
        T hT i j x hx hji
      simp [b, hz]
  rw [rclike_re_inner_apply_eq_sum_eigenvalues T hT x]
  calc
    ∑ j, ev j * ‖b.repr x j‖ ^ 2 ≤
        ∑ j, ev i * ‖b.repr x j‖ ^ 2 := hsum
    _ = ev i * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [b.repr_apply_apply] using b.sum_sq_norm_inner_right x

theorem rclike_le_eigenvalue_of_large_subspace
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) (z : ℝ)
    (W : Submodule 𝕜 E)
    (hWrank : i.1 + 1 ≤ Module.finrank 𝕜 W)
    (hWquad : ∀ x ∈ W,
      z * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (T x))) :
    z ≤ hT.eigenvalues rfl i := by
  let V := rclikeOrderedEigenSuffix T hT i
  have hVrank : Module.finrank 𝕜 V = Module.finrank 𝕜 E - i.1 :=
    finrank_rclikeOrderedEigenSuffix T hT i
  have hsum : Module.finrank 𝕜 E <
      Module.finrank 𝕜 W + Module.finrank 𝕜 V := by
    rw [hVrank]
    omega
  have hnot : ¬ Disjoint W V := by
    intro hdis
    exact (not_le_of_gt hsum)
      (Submodule.finrank_add_finrank_le_of_disjoint hdis)
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxW, hxV, hx0⟩ := hnot
  have hxNorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hlower := hWquad x hxW
  have hupper :=
    rclike_re_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_suffix
      T hT i x hxV
  nlinarith

theorem rclike_positive_paddedCompression_eigenvalue_le
    [FiniteDimensional 𝕜 E]
    (A G : E →ₗ[𝕜] E) (hA : A.IsSymmetric) (hG : G.IsSymmetric)
    (P : E →ₗ[𝕜] E)
    (hcompression : ∀ x : E,
      RCLike.re (inner 𝕜 x (G x)) =
        RCLike.re (inner 𝕜 (P x) (A (P x))))
    (hcontract : ∀ x : E, ‖P x‖ ≤ ‖x‖)
    (j : Fin (Module.finrank 𝕜 E))
    (hpos : 0 < hG.eigenvalues rfl j) :
    hG.eigenvalues rfl j ≤ hA.eigenvalues rfl j := by
  let U := rclikeOrderedEigenPrefix G hG j
  let pU : U →ₗ[𝕜] E := P.domRestrict U
  have hpU : Function.Injective pU := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hsubmem : (x : E) - (y : E) ∈ U := U.sub_mem x.property y.property
    have hsubne : (x : E) - (y : E) ≠ 0 := sub_ne_zero.mpr hne
    have hlower :=
      rclike_eigenvalue_mul_norm_sq_le_re_inner_apply_of_mem_prefix
        G hG j ((x : E) - (y : E)) hsubmem
    have hzero : P ((x : E) - (y : E)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    rw [hcompression, hzero] at hlower
    simp at hlower
    have hnorm : 0 < ‖(x : E) - (y : E)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hsubne)
    nlinarith
  let V : Submodule 𝕜 E := LinearMap.range pU
  have hVrank : j.1 + 1 ≤ Module.finrank 𝕜 V := by
    rw [LinearMap.finrank_range_of_inj hpU,
      finrank_rclikeOrderedEigenPrefix G hG j]
  have hVquad : ∀ y ∈ V,
      hG.eigenvalues rfl j * ‖y‖ ^ 2 ≤
        RCLike.re (inner 𝕜 y (A y)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    have hlower :=
      rclike_eigenvalue_mul_norm_sq_le_re_inner_apply_of_mem_prefix
        G hG j (x : E) x.property
    have hnormSq : ‖P (x : E)‖ ^ 2 ≤ ‖(x : E)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(x : E)‖ - ‖P (x : E)‖),
        hcontract (x : E), norm_nonneg (x : E), norm_nonneg (P (x : E))]
    dsimp [pU]
    rw [← hcompression]
    nlinarith
  exact rclike_le_eigenvalue_of_large_subspace A hA j
    (hG.eigenvalues rfl j) V hVrank hVquad

theorem rclike_eigenvalue_le_of_positive_subspace_finrank_le
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) (z : ℝ)
    (hpos : ∀ W : Submodule 𝕜 E,
      (∀ x ∈ W, x ≠ 0 →
        z * ‖x‖ ^ 2 < RCLike.re (inner 𝕜 x (T x))) →
      Module.finrank 𝕜 W ≤ i.1) :
    hT.eigenvalues rfl i ≤ z := by
  by_contra hnot
  have hzi : z < hT.eigenvalues rfl i := lt_of_not_ge hnot
  let U := rclikeOrderedEigenPrefix T hT i
  have hUrank : Module.finrank 𝕜 U = i.1 + 1 :=
    finrank_rclikeOrderedEigenPrefix T hT i
  have hpositive : ∀ x ∈ U, x ≠ 0 →
      z * ‖x‖ ^ 2 < RCLike.re (inner 𝕜 x (T x)) := by
    intro x hxU hx0
    have hxNorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    have hlower :=
      rclike_eigenvalue_mul_norm_sq_le_re_inner_apply_of_mem_prefix
        T hT i x hxU
    nlinarith
  have hdim := hpos U hpositive
  omega

theorem rclike_finrank_positive_subspace_le_eigenvalue_index
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E))
    (W : Submodule 𝕜 E)
    (hpositive : ∀ x ∈ W, x ≠ 0 →
      hT.eigenvalues rfl i * ‖x‖ ^ 2 <
        RCLike.re (inner 𝕜 x (T x))) :
    Module.finrank 𝕜 W ≤ i.1 := by
  by_contra hnot
  have hiW : i.1 < Module.finrank 𝕜 W := lt_of_not_ge hnot
  let V := rclikeOrderedEigenSuffix T hT i
  have hVrank : Module.finrank 𝕜 V = Module.finrank 𝕜 E - i.1 :=
    finrank_rclikeOrderedEigenSuffix T hT i
  have hsum : Module.finrank 𝕜 E <
      Module.finrank 𝕜 W + Module.finrank 𝕜 V := by
    rw [hVrank]
    omega
  have hnotDisjoint : ¬ Disjoint W V := by
    intro hdis
    exact (not_le_of_gt hsum)
      (Submodule.finrank_add_finrank_le_of_disjoint hdis)
  rw [Submodule.disjoint_def] at hnotDisjoint
  push Not at hnotDisjoint
  obtain ⟨x, hxW, hxV, hx0⟩ := hnotDisjoint
  have hlower := hpositive x hxW hx0
  have hupper :=
    rclike_re_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_suffix
      T hT i x hxV
  exact (not_lt_of_ge hupper) hlower


/- Source slice: ExactPrincipalMolecule.lean -/

open Matrix

open scoped Matrix.Norms.L2Operator


/- Source slice: ExactMoleculeEmbedding.lean -/


/- Source slice: ExactMoleculeFamily.lean -/

open scoped Matrix Matrix.Norms.L2Operator

local instance exactMoleculeFamilyPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _


/- Source slice: OneExitCoreNonpositive.lean -/

open scoped ComplexOrder InnerProductSpace MatrixOrder

theorem neg_oneExitCoreMatrix_posSemidef
    (S : Finset ℕ) (X : ℕ) :
    (-oneExitCoreMatrix S X).PosSemidef := by
  let C := oneExitCoreMatrix S X
  have hC : C.IsHermitian := by
    simpa [C] using oneExitCoreMatrix_isHermitian S X
  have hneg : (-C).IsHermitian := hC.neg
  rw [hneg.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hi
  have hei : hneg.eigenvalues i < 0 := lt_of_not_ge hi
  let v : EuclideanSpace ℂ (PrimeStar.Vertex S X) :=
    hneg.eigenvectorBasis i
  let mu : ℝ := -hneg.eigenvalues i
  have hmu : 0 < mu := by dsimp [mu]; linarith
  have hvneg : Matrix.toEuclideanLin (-C) v =
      (hneg.eigenvalues i : ℂ) • v := by
    apply PiLp.ext
    intro j
    change (-C).mulVec v.ofLp j =
      (hneg.eigenvalues i : ℂ) * v.ofLp j
    exact congrFun (hneg.mulVec_eigenvectorBasis i) j
  have hvC : Matrix.toEuclideanLin C v = (mu : ℂ) • v := by
    have h := congrArg Neg.neg hvneg
    simpa [mu] using h
  have hQ : Matrix.toEuclideanLin
      (positiveStarComplementProjection S X) v = v :=
    complement_fixes_oneExitCore_eigenvector_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hmu.ne') (by simpa [C] using hvC)
  have hLcore := oneExitCoreMatrix_apply_eq_largePrime_of_complement_fixed hQ
  have hL : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) v =
      (mu : ℂ) • v := by
    rw [← hLcore]
    simpa [C] using hvC
  have hP : Matrix.toEuclideanLin (positiveStarProjection S X) v = v :=
    positiveStarProjection_fixes_positive_forest_eigenvector hmu hL
  have hvzero : v = 0 := by
    apply PiLp.ext
    intro j
    have hqj := congrArg (fun z ↦ z j) hQ
    have hpj := congrArg (fun z ↦ z j) hP
    simp only [Matrix.toLpLin_apply] at hpj
    simp only [positiveStarComplementProjection, Matrix.toLpLin_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec] at hqj
    change v.ofLp j - (positiveStarProjection S X).mulVec v.ofLp j =
      v.ofLp j at hqj
    rw [hpj] at hqj
    simpa using hqj.symm
  exact (hneg.eigenvectorBasis.toBasis.ne_zero i) hvzero

theorem re_inner_oneExitCoreMatrix_apply_nonpos
    (S : Finset ℕ) (X : ℕ)
    (z : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    (⟪z, Matrix.toEuclideanLin (oneExitCoreMatrix S X) z⟫_ℂ).re ≤ 0 := by
  have hpos : (Matrix.toEuclideanLin (-oneExitCoreMatrix S X)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr
      (neg_oneExitCoreMatrix_posSemidef S X)
  have hz := hpos.re_inner_nonneg_right z
  simpa using hz


/- Source slice: RealSchurResolventForm.lean -/

open scoped InnerProductSpace

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

variable {𝕜 V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

private theorem rclike_injective_of_lowerBound
    (T : V →ₗ[𝕜] V) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : V, gamma * ‖x‖ ≤ ‖T x‖) : Function.Injective T := by
  intro x y hxy
  have hzero : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hbound := hlower (x - y)
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

def rclikeInverseOfLowerBound
    (T : V →ₗ[𝕜] V) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : V, gamma * ‖x‖ ≤ ‖T x‖) : V →ₗ[𝕜] V :=
  (LinearEquiv.ofInjectiveEndo T
    (rclike_injective_of_lowerBound T gamma hgamma hlower)).symm.toLinearMap

theorem rclikeInverseOfLowerBound_apply_shift
    (T : V →ₗ[𝕜] V) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : V, gamma * ‖x‖ ≤ ‖T x‖) (x : V) :
    rclikeInverseOfLowerBound T gamma hgamma hlower (T x) = x := by
  unfold rclikeInverseOfLowerBound
  exact (LinearEquiv.ofInjectiveEndo T
    (rclike_injective_of_lowerBound T gamma hgamma hlower)).symm_apply_apply x

theorem rclike_shift_apply_inverseOfLowerBound
    (T : V →ₗ[𝕜] V) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : V, gamma * ‖x‖ ≤ ‖T x‖) (x : V) :
    T (rclikeInverseOfLowerBound T gamma hgamma hlower x) = x := by
  unfold rclikeInverseOfLowerBound
  exact (LinearEquiv.ofInjectiveEndo T
    (rclike_injective_of_lowerBound T gamma hgamma hlower)).apply_symm_apply x

theorem norm_rclikeInverseOfLowerBound_apply_le
    (T : V →ₗ[𝕜] V) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : V, gamma * ‖x‖ ≤ ‖T x‖) (x : V) :
    ‖rclikeInverseOfLowerBound T gamma hgamma hlower x‖ ≤ gamma⁻¹ * ‖x‖ := by
  have h := hlower (rclikeInverseOfLowerBound T gamma hgamma hlower x)
  rw [rclike_shift_apply_inverseOfLowerBound] at h
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hgamma).2
  simpa [mul_comm] using h

def rclikeShiftedEndomorphism (C : V →ₗ[𝕜] V) (mu : ℝ) : V →ₗ[𝕜] V :=
  (RCLike.ofReal (K := 𝕜) mu) • (LinearMap.id : V →ₗ[𝕜] V) - C

@[simp]
theorem rclikeShiftedEndomorphism_apply
    (C : V →ₗ[𝕜] V) (mu : ℝ) (x : V) :
    rclikeShiftedEndomorphism C mu x =
      (RCLike.ofReal (K := 𝕜) mu) • x - C x := by
  simp [rclikeShiftedEndomorphism]

def rclikeFiniteResolventOfGap
    (C : V →ₗ[𝕜] V) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : V,
      gamma * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) mu) • x - C x‖) : V →ₗ[𝕜] V :=
  rclikeInverseOfLowerBound (rclikeShiftedEndomorphism C mu) gamma hgamma (by
    intro x
    simpa using hgap x)

@[simp]
theorem rclikeFiniteResolventOfGap_shift_apply
    (C : V →ₗ[𝕜] V) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : V,
      gamma * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) mu) • x - C x‖) (x : V) :
    rclikeFiniteResolventOfGap C mu gamma hgamma hgap
        ((RCLike.ofReal (K := 𝕜) mu) • x - C x) = x := by
  exact rclikeInverseOfLowerBound_apply_shift
    (rclikeShiftedEndomorphism C mu) gamma hgamma (by
      intro y
      simpa using hgap y) x

@[simp]
theorem rclikeFiniteResolventOfGap_apply_inverse
    (C : V →ₗ[𝕜] V) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : V,
      gamma * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) mu) • x - C x‖) (x : V) :
    (RCLike.ofReal (K := 𝕜) mu) •
          rclikeFiniteResolventOfGap C mu gamma hgamma hgap x -
        C (rclikeFiniteResolventOfGap C mu gamma hgamma hgap x) = x := by
  exact rclike_shift_apply_inverseOfLowerBound
    (rclikeShiftedEndomorphism C mu) gamma hgamma (by
      intro y
      simpa using hgap y) x

theorem norm_rclikeFiniteResolventOfGap_apply_le
    (C : V →ₗ[𝕜] V) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : V,
      gamma * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) mu) • x - C x‖) (x : V) :
    ‖rclikeFiniteResolventOfGap C mu gamma hgamma hgap x‖ ≤
      gamma⁻¹ * ‖x‖ := by
  exact norm_rclikeInverseOfLowerBound_apply_le
    (rclikeShiftedEndomorphism C mu) gamma hgamma (by
      intro y
      simpa using hgap y) x

theorem rclikeInverseOfLowerBound_isSymmetric
    (T : V →ₗ[𝕜] V) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlower : ∀ x : V, gamma * ‖x‖ ≤ ‖T x‖)
    (hT : T.IsSymmetric) :
    (rclikeInverseOfLowerBound T gamma hgamma hlower).IsSymmetric := by
  intro x y
  let R := rclikeInverseOfLowerBound T gamma hgamma hlower
  calc
    inner 𝕜 (R x) y = inner 𝕜 (R x) (T (R y)) := by
      rw [rclike_shift_apply_inverseOfLowerBound]
    _ = inner 𝕜 (T (R x)) (R y) := (hT (R x) (R y)).symm
    _ = inner 𝕜 x (R y) := by
      rw [rclike_shift_apply_inverseOfLowerBound]

theorem rclikeFiniteResolventOfGap_isSymmetric
    (C : V →ₗ[𝕜] V) (mu gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ x : V,
      gamma * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) mu) • x - C x‖)
    (hC : C.IsSymmetric) :
    (rclikeFiniteResolventOfGap C mu gamma hgamma hgap).IsSymmetric := by
  apply rclikeInverseOfLowerBound_isSymmetric
  intro x y
  simp only [rclikeShiftedEndomorphism_apply, inner_sub_right,
    inner_sub_left, inner_smul_right, inner_smul_left]
  rw [hC x y]
  simp

theorem rclikeFiniteResolventOfGap_sub_apply
    (C : V →ₗ[𝕜] V) (lam mu gammaLam gammaMu : ℝ)
    (hgammaLam : 0 < gammaLam) (hgammaMu : 0 < gammaMu)
    (hgapLam : ∀ x : V,
      gammaLam * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) lam) • x - C x‖)
    (hgapMu : ∀ x : V,
      gammaMu * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) mu) • x - C x‖)
    (b : V) :
    rclikeFiniteResolventOfGap C lam gammaLam hgammaLam hgapLam b -
        rclikeFiniteResolventOfGap C mu gammaMu hgammaMu hgapMu b =
      (RCLike.ofReal (K := 𝕜) (mu - lam)) •
        rclikeFiniteResolventOfGap C lam gammaLam hgammaLam hgapLam
          (rclikeFiniteResolventOfGap C mu gammaMu hgammaMu hgapMu b) := by
  let Rlam := rclikeFiniteResolventOfGap C lam gammaLam hgammaLam hgapLam
  let Rmu := rclikeFiniteResolventOfGap C mu gammaMu hgammaMu hgapMu
  have hRlamShift (x : V) :
      Rlam ((RCLike.ofReal (K := 𝕜) lam) • x - C x) = x := by
    exact rclikeFiniteResolventOfGap_shift_apply
      C lam gammaLam hgammaLam hgapLam x
  have hRmuInv :
      (RCLike.ofReal (K := 𝕜) mu) • Rmu b - C (Rmu b) = b := by
    exact rclikeFiniteResolventOfGap_apply_inverse
      C mu gammaMu hgammaMu hgapMu b
  have hsource :
      b - ((RCLike.ofReal (K := 𝕜) lam) • Rmu b - C (Rmu b)) =
        (RCLike.ofReal (K := 𝕜) (mu - lam)) • Rmu b := by
    calc
      b - ((RCLike.ofReal (K := 𝕜) lam) • Rmu b - C (Rmu b)) =
          ((RCLike.ofReal (K := 𝕜) mu) • Rmu b - C (Rmu b)) -
            ((RCLike.ofReal (K := 𝕜) lam) • Rmu b - C (Rmu b)) := by
              rw [hRmuInv]
      _ = (RCLike.ofReal (K := 𝕜) (mu - lam)) • Rmu b := by
        simp only [RCLike.ofReal_sub, sub_smul]
        module
  calc
    Rlam b - Rmu b =
        Rlam b - Rlam
          ((RCLike.ofReal (K := 𝕜) lam) • Rmu b - C (Rmu b)) := by
            rw [hRlamShift]
    _ = Rlam
        (b - ((RCLike.ofReal (K := 𝕜) lam) • Rmu b - C (Rmu b))) :=
      (map_sub Rlam _ _).symm
    _ = Rlam ((RCLike.ofReal (K := 𝕜) (mu - lam)) • Rmu b) := by
      rw [hsource]
    _ = (RCLike.ofReal (K := 𝕜) (mu - lam)) • Rlam (Rmu b) := by
      rw [map_smul]

theorem abs_re_inner_rclikeFiniteResolventOfGap_sub_le
    (C : V →ₗ[𝕜] V) (lam mu gammaLam gammaMu : ℝ)
    (hgammaLam : 0 < gammaLam) (hgammaMu : 0 < gammaMu)
    (hgapLam : ∀ x : V,
      gammaLam * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) lam) • x - C x‖)
    (hgapMu : ∀ x : V,
      gammaMu * ‖x‖ ≤
        ‖(RCLike.ofReal (K := 𝕜) mu) • x - C x‖)
    (hC : C.IsSymmetric) (b : V) :
    |RCLike.re (inner 𝕜 b
          (rclikeFiniteResolventOfGap C lam gammaLam hgammaLam hgapLam b)) -
        RCLike.re (inner 𝕜 b
          (rclikeFiniteResolventOfGap C mu gammaMu hgammaMu hgapMu b))| ≤
      |lam - mu| *
        ‖rclikeFiniteResolventOfGap C lam gammaLam hgammaLam hgapLam b‖ *
        ‖rclikeFiniteResolventOfGap C mu gammaMu hgammaMu hgapMu b‖ := by
  let Rlam := rclikeFiniteResolventOfGap C lam gammaLam hgammaLam hgapLam
  let Rmu := rclikeFiniteResolventOfGap C mu gammaMu hgammaMu hgapMu
  have hRlam : Rlam.IsSymmetric :=
    rclikeFiniteResolventOfGap_isSymmetric
      C lam gammaLam hgammaLam hgapLam hC
  have hdiff := rclikeFiniteResolventOfGap_sub_apply
    C lam mu gammaLam gammaMu hgammaLam hgammaMu hgapLam hgapMu b
  have hre :
      RCLike.re (inner 𝕜 b (Rlam b)) -
          RCLike.re (inner 𝕜 b (Rmu b)) =
        (mu - lam) * RCLike.re (inner 𝕜 (Rlam b) (Rmu b)) := by
    rw [← map_sub, ← inner_sub_right, hdiff, inner_smul_right,
      ← hRlam b (Rmu b)]
    simp
  rw [hre, abs_mul, abs_sub_comm]
  have hinner : |RCLike.re (inner 𝕜 (Rlam b) (Rmu b))| ≤
      ‖Rlam b‖ * ‖Rmu b‖ :=
    (RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  calc
    |lam - mu| * |RCLike.re (inner 𝕜 (Rlam b) (Rmu b))| ≤
        |lam - mu| * (‖Rlam b‖ * ‖Rmu b‖) :=
      mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = |lam - mu| * ‖Rlam b‖ * ‖Rmu b‖ := by ring

theorem rclike_shifted_lowerBound_of_quadratic_upper
    (D : V →ₗ[𝕜] V) {beta w : ℝ}
    (hD : ∀ x : V,
      RCLike.re (inner 𝕜 x (D x)) ≤ beta * ‖x‖ ^ 2) :
    ∀ x : V, (w - beta) * ‖x‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) w) • x - D x‖ := by
  intro x
  have hinner :
      RCLike.re (inner 𝕜 x
          ((RCLike.ofReal (K := 𝕜) w) • x - D x)) =
        w * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 x (D x)) := by
    rw [inner_sub_right, inner_smul_right, map_sub,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  have hlower :
      (w - beta) * ‖x‖ ^ 2 ≤
        RCLike.re (inner 𝕜 x
          ((RCLike.ofReal (K := 𝕜) w) • x - D x)) := by
    rw [hinner]
    nlinarith [hD x]
  have hcauchy :
      RCLike.re (inner 𝕜 x
          ((RCLike.ofReal (K := 𝕜) w) • x - D x)) ≤
        ‖x‖ * ‖(RCLike.ofReal (K := 𝕜) w) • x - D x‖ :=
    re_inner_le_norm _ _
  by_cases hx : ‖x‖ = 0
  · simp [hx]
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    nlinarith

theorem rclike_schur_cross_quadratic_le_resolvent
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    (D : V →ₗ[𝕜] V) (K : U →ₗ[𝕜] V)
    {beta w : ℝ} (hwbeta : beta < w)
    (hDsymm : D.IsSymmetric)
    (hD : ∀ x : V,
      RCLike.re (inner 𝕜 x (D x)) ≤ beta * ‖x‖ ^ 2) :
    let gap := w - beta
    let R := rclikeFiniteResolventOfGap D w gap (sub_pos.mpr hwbeta)
      (rclike_shifted_lowerBound_of_quadratic_upper D hD)
    ∀ u : U, ∀ e : V,
      2 * RCLike.re (inner 𝕜 (K u) e) +
          RCLike.re (inner 𝕜 e (D e)) - w * ‖e‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (K u) (R (K u))) := by
  dsimp only
  let gap := w - beta
  let hgap : ∀ x : V, gap * ‖x‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) w) • x - D x‖ :=
    rclike_shifted_lowerBound_of_quadratic_upper D hD
  let R := rclikeFiniteResolventOfGap D w gap (sub_pos.mpr hwbeta) hgap
  intro u e
  let r := R (K u)
  have hr : (RCLike.ofReal (K := 𝕜) w) • r - D r = K u := by
    exact rclikeFiniteResolventOfGap_apply_inverse
      D w gap (sub_pos.mpr hwbeta) hgap (K u)
  have hpositive :
      0 ≤ RCLike.re (inner 𝕜 (e - r)
        ((RCLike.ofReal (K := 𝕜) w) • (e - r) - D (e - r))) := by
    have hquad := hD (e - r)
    rw [inner_sub_right, inner_smul_right, map_sub,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    nlinarith
  have hcross :
      RCLike.re (inner 𝕜 r (D e)) =
        RCLike.re (inner 𝕜 e (D r)) := by
    calc
      RCLike.re (inner 𝕜 r (D e)) =
          RCLike.re (inner 𝕜 (D r) e) :=
        congrArg RCLike.re (hDsymm r e).symm
      _ = RCLike.re (inner 𝕜 e (D r)) := inner_re_symm _ _
  have hidentity :
      RCLike.re (inner 𝕜 (K u) r) -
          (2 * RCLike.re (inner 𝕜 (K u) e) +
            RCLike.re (inner 𝕜 e (D e)) - w * ‖e‖ ^ 2) =
        RCLike.re (inner 𝕜 (e - r)
          ((RCLike.ofReal (K := 𝕜) w) • (e - r) - D (e - r))) := by
    rw [← hr]
    simp only [map_sub, smul_sub, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [inner_re_symm e r, inner_re_symm (D r) r,
      inner_re_symm e (D r), hcross]
    rw [inner_re_symm (D r) e]
    ring
  linarith

theorem rclike_abs_schurSelfEnergy_sub_le
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    (D : V →ₗ[𝕜] V) (K : U →ₗ[𝕜] V)
    {beta lam mu : ℝ} (hlam : beta < lam) (hmu : beta < mu)
    (hDsymm : D.IsSymmetric)
    (hD : ∀ x : V,
      RCLike.re (inner 𝕜 x (D x)) ≤ beta * ‖x‖ ^ 2)
    (hKsq : ∀ u : U, ‖K u‖ ^ 2 ≤ beta ^ 2 * ‖u‖ ^ 2) :
    let gapLam := lam - beta
    let gapMu := mu - beta
    let Rlam := rclikeFiniteResolventOfGap D lam gapLam
      (sub_pos.mpr hlam) (rclike_shifted_lowerBound_of_quadratic_upper D hD)
    let Rmu := rclikeFiniteResolventOfGap D mu gapMu
      (sub_pos.mpr hmu) (rclike_shifted_lowerBound_of_quadratic_upper D hD)
    ∀ u : U,
      |RCLike.re (inner 𝕜 (K u) (Rlam (K u))) -
          RCLike.re (inner 𝕜 (K u) (Rmu (K u)))| ≤
        beta ^ 2 * |lam - mu| / (gapLam * gapMu) * ‖u‖ ^ 2 := by
  dsimp only
  let gapLam := lam - beta
  let gapMu := mu - beta
  let hgapLam : ∀ x : V, gapLam * ‖x‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) lam) • x - D x‖ :=
    rclike_shifted_lowerBound_of_quadratic_upper D hD
  let hgapMu : ∀ x : V, gapMu * ‖x‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) mu) • x - D x‖ :=
    rclike_shifted_lowerBound_of_quadratic_upper D hD
  let Rlam := rclikeFiniteResolventOfGap D lam gapLam
    (sub_pos.mpr hlam) hgapLam
  let Rmu := rclikeFiniteResolventOfGap D mu gapMu
    (sub_pos.mpr hmu) hgapMu
  intro u
  have hres := abs_re_inner_rclikeFiniteResolventOfGap_sub_le
    D lam mu gapLam gapMu (sub_pos.mpr hlam) (sub_pos.mpr hmu)
      hgapLam hgapMu hDsymm (K u)
  have hRlam : ‖Rlam (K u)‖ ≤ gapLam⁻¹ * ‖K u‖ :=
    norm_rclikeFiniteResolventOfGap_apply_le
      D lam gapLam (sub_pos.mpr hlam) hgapLam (K u)
  have hRmu : ‖Rmu (K u)‖ ≤ gapMu⁻¹ * ‖K u‖ :=
    norm_rclikeFiniteResolventOfGap_apply_le
      D mu gapMu (sub_pos.mpr hmu) hgapMu (K u)
  have hgapLamPos : 0 < gapLam := sub_pos.mpr hlam
  have hgapMuPos : 0 < gapMu := sub_pos.mpr hmu
  have hsource : ‖K u‖ * ‖K u‖ ≤ beta ^ 2 * ‖u‖ ^ 2 := by
    simpa [pow_two] using hKsq u
  calc
    |RCLike.re (inner 𝕜 (K u) (Rlam (K u))) -
        RCLike.re (inner 𝕜 (K u) (Rmu (K u)))| ≤
        |lam - mu| * ‖Rlam (K u)‖ * ‖Rmu (K u)‖ := hres
    _ ≤ |lam - mu| * (gapLam⁻¹ * ‖K u‖) *
        (gapMu⁻¹ * ‖K u‖) := by gcongr
    _ = |lam - mu| / (gapLam * gapMu) * (‖K u‖ * ‖K u‖) := by
      field_simp
    _ ≤ |lam - mu| / (gapLam * gapMu) *
        (beta ^ 2 * ‖u‖ ^ 2) := by gcongr
    _ = beta ^ 2 * |lam - mu| / (gapLam * gapMu) * ‖u‖ ^ 2 := by
      ring

theorem rclike_twoStageSchur_selfEnergy_sub_le_delta
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    (D : V →ₗ[𝕜] V) (K : U →ₗ[𝕜] V)
    {beta rho : ℝ} (hbeta : 0 ≤ beta) (hrho : 0 < rho)
    (hscale : 4 * beta ≤ rho) (hDsymm : D.IsSymmetric)
    (hD : ∀ x : V,
      RCLike.re (inner 𝕜 x (D x)) ≤ beta * ‖x‖ ^ 2)
    (hKsq : ∀ u : U, ‖K u‖ ^ 2 ≤ beta ^ 2 * ‖u‖ ^ 2) :
    let delta := 3 * beta ^ 4 / rho ^ 3
    let z := rho + delta
    let s := beta ^ 2 / (z - beta)
    delta < s →
      let newEnergy := z - s
      let newGap := newEnergy - beta
      let oldGap := rho - beta
      let Rnew := rclikeFiniteResolventOfGap D newEnergy newGap
        (by
          have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
          dsimp only at hparams
          exact lt_of_lt_of_le (by positivity) hparams.2.2.2.2.1)
        (rclike_shifted_lowerBound_of_quadratic_upper D hD)
      let Rold := rclikeFiniteResolventOfGap D rho oldGap
        (by
          have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
          dsimp only at hparams
          exact lt_of_lt_of_le (by positivity) hparams.2.2.2.2.2)
        (rclike_shifted_lowerBound_of_quadratic_upper D hD)
      ∀ u : U,
        RCLike.re (inner 𝕜 (K u) (Rnew (K u))) -
            RCLike.re (inner 𝕜 (K u) (Rold (K u))) ≤
          delta * ‖u‖ ^ 2 := by
  dsimp only
  let delta := 3 * beta ^ 4 / rho ^ 3
  let z := rho + delta
  let s := beta ^ 2 / (z - beta)
  intro hdeltaS
  have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
  dsimp only at hparams
  rcases hparams with
    ⟨hdelta, _hzbeta, _hs, _hsUpper, hnewGap, holdGap⟩
  let newEnergy := z - s
  let newGap := newEnergy - beta
  let oldGap := rho - beta
  have hnewGapPos : 0 < newGap :=
    lt_of_lt_of_le (by positivity) hnewGap
  have holdGapPos : 0 < oldGap :=
    lt_of_lt_of_le (by positivity) holdGap
  have hnewEnergy : beta < newEnergy := sub_pos.mp hnewGapPos
  have holdEnergy : beta < rho := sub_pos.mp holdGapPos
  let Rnew := rclikeFiniteResolventOfGap D newEnergy newGap
    hnewGapPos (rclike_shifted_lowerBound_of_quadratic_upper D hD)
  let Rold := rclikeFiniteResolventOfGap D rho oldGap
    holdGapPos (rclike_shifted_lowerBound_of_quadratic_upper D hD)
  intro u
  have habs := rclike_abs_schurSelfEnergy_sub_le D K
    (beta := beta) (lam := newEnergy) (mu := rho)
      hnewEnergy holdEnergy hDsymm hD hKsq u
  have henergy : |newEnergy - rho| = s - delta := by
    dsimp [newEnergy, z]
    rw [abs_of_nonpos]
    · ring
    · linarith
  have hcoefficient :
      beta ^ 2 * |newEnergy - rho| / (newGap * oldGap) < delta := by
    rw [henergy]
    exact twoStageSchur_resolvent_error_lt_delta
      hbeta hrho hscale hdeltaS
  have hnorm : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have hraw :
      RCLike.re (inner 𝕜 (K u) (Rnew (K u))) -
          RCLike.re (inner 𝕜 (K u) (Rold (K u))) ≤
        beta ^ 2 * |newEnergy - rho| /
          (newGap * oldGap) * ‖u‖ ^ 2 :=
    (le_abs_self _).trans habs
  exact hraw.trans <| mul_le_mul_of_nonneg_right hcoefficient.le hnorm


/- Source slice: RCLikeSchurCrossTerm.lean -/

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem two_mul_mul_sub_mul_sq_le_sq_div
    {u v a : ℝ} (ha : 0 < a) :
    2 * u * v - a * v ^ 2 ≤ u ^ 2 / a := by
  rw [le_div_iff₀ ha]
  nlinarith [sq_nonneg (u - a * v)]

theorem two_re_inner_sub_mul_norm_sq_le_norm_sq_div
    (x y : E) {a : ℝ} (ha : 0 < a) :
    2 * RCLike.re (inner 𝕜 x y) - a * ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 / a := by
  have hinner : RCLike.re (inner 𝕜 x y) ≤ ‖x‖ * ‖y‖ :=
    re_inner_le_norm x y
  have htwo : 2 * RCLike.re (inner 𝕜 x y) ≤
      2 * (‖x‖ * ‖y‖) :=
    mul_le_mul_of_nonneg_left hinner (by norm_num)
  calc
    2 * RCLike.re (inner 𝕜 x y) - a * ‖y‖ ^ 2 ≤
        2 * ‖x‖ * ‖y‖ - a * ‖y‖ ^ 2 := by
      nlinarith
    _ ≤ ‖x‖ ^ 2 / a := two_mul_mul_sub_mul_sq_le_sq_div ha

theorem schur_cross_block_quadratic_upper
    (x y : E) {q beta z : ℝ}
    (hq : q ≤ beta * ‖y‖ ^ 2) (hz : beta < z) :
    2 * RCLike.re (inner 𝕜 x y) + q - z * ‖y‖ ^ 2 ≤
      ‖x‖ ^ 2 / (z - beta) := by
  calc
    2 * RCLike.re (inner 𝕜 x y) + q - z * ‖y‖ ^ 2 ≤
        2 * RCLike.re (inner 𝕜 x y) + beta * ‖y‖ ^ 2 -
          z * ‖y‖ ^ 2 := by linarith
    _ = 2 * RCLike.re (inner 𝕜 x y) -
          (z - beta) * ‖y‖ ^ 2 := by ring
    _ ≤ ‖x‖ ^ 2 / (z - beta) :=
      two_re_inner_sub_mul_norm_sq_le_norm_sq_div x y (sub_pos.mpr hz)


/- Source slice: RealTwoStageSchurForms.lean -/

open scoped InnerProductSpace

variable {F G₀ P E W : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G₀] [InnerProductSpace ℝ G₀]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {𝕜 F P E W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

def rclikeSchurReducedForm
    (T : P →ₗ[𝕜] P) (K : P →ₗ[𝕜] E) (R : E →ₗ[𝕜] E)
    (energy : ℝ) (u : P) : ℝ :=
  RCLike.re (inner 𝕜 u (T u)) - energy * ‖u‖ ^ 2 +
    RCLike.re (inner 𝕜 (K u) (R (K u)))

theorem rclike_twoBlock_reducedForm_eq_reconstruction
    {G₀ : Type*} [NormedAddCommGroup G₀] [InnerProductSpace 𝕜 G₀]
    (G : G₀ →ₗ[𝕜] G₀) (T : P →ₗ[𝕜] P) (D : E →ₗ[𝕜] E)
    (K : P →ₗ[𝕜] E) (p : G₀ →ₗ[𝕜] P) (e : G₀ →ₗ[𝕜] E)
    {beta rho : ℝ} (hrho : beta < rho)
    (hD : ∀ y : E,
      RCLike.re (inner 𝕜 y (D y)) ≤ beta * ‖y‖ ^ 2)
    (reconstruct : G₀ →ₗ[𝕜] G₀)
    (hnorm : ∀ x : G₀,
      ‖reconstruct x‖ ^ 2 =
        ‖p (reconstruct x)‖ ^ 2 + ‖e (reconstruct x)‖ ^ 2)
    (hform : ∀ x : G₀,
      RCLike.re (inner 𝕜 (reconstruct x) (G (reconstruct x))) =
        RCLike.re (inner 𝕜 (p (reconstruct x))
          (T (p (reconstruct x)))) +
          2 * RCLike.re (inner 𝕜 (K (p (reconstruct x)))
            (e (reconstruct x))) +
          RCLike.re (inner 𝕜 (e (reconstruct x))
            (D (e (reconstruct x)))))
    (hp : ∀ x : G₀, p (reconstruct x) = p x)
    (he :
      let gap := rho - beta
      let Rold := rclikeFiniteResolventOfGap D rho gap
        (sub_pos.mpr hrho)
        (rclike_shifted_lowerBound_of_quadratic_upper D hD)
      ∀ x : G₀,
        e (reconstruct x) = Rold (K (p x))) :
    let gap := rho - beta
    let Rold := rclikeFiniteResolventOfGap D rho gap
      (sub_pos.mpr hrho)
      (rclike_shifted_lowerBound_of_quadratic_upper D hD)
    ∀ x : G₀,
      rclikeSchurReducedForm T K Rold rho (p x) =
        RCLike.re (inner 𝕜 (reconstruct x)
          (G (reconstruct x))) -
          rho * ‖reconstruct x‖ ^ 2 := by
  dsimp only at he ⊢
  let gap := rho - beta
  let hgap : ∀ y : E, gap * ‖y‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) rho) • y - D y‖ :=
    rclike_shifted_lowerBound_of_quadratic_upper D hD
  let Rold := rclikeFiniteResolventOfGap D rho gap
    (sub_pos.mpr hrho) hgap
  intro x
  let u := p x
  let r := Rold (K u)
  have hr : (RCLike.ofReal (K := 𝕜) rho) • r - D r = K u := by
    exact rclikeFiniteResolventOfGap_apply_inverse
      D rho gap (sub_pos.mpr hrho) hgap (K u)
  have hself :
      RCLike.re (inner 𝕜 (K u) r) =
        rho * ‖r‖ ^ 2 - RCLike.re (inner 𝕜 r (D r)) := by
    rw [← hr]
    rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
      RCLike.re_ofReal_mul, inner_re_symm (D r) r]
    simp
  rw [hform x, hnorm x, hp x, he x]
  dsimp [rclikeSchurReducedForm, r]
  nlinarith

theorem rclike_threeBlock_quadratic_le_reducedForm
    (A : F →ₗ[𝕜] F) (T : P →ₗ[𝕜] P)
    (D : E →ₗ[𝕜] E) (C : W →ₗ[𝕜] W)
    (K : P →ₗ[𝕜] E) (R : E →ₗ[𝕜] W)
    (p : F →ₗ[𝕜] P) (e : F →ₗ[𝕜] E) (f : F →ₗ[𝕜] W)
    {beta z : ℝ} (hz : beta < z) (hDsymm : D.IsSymmetric)
    (hnorm : ∀ x : F,
      ‖x‖ ^ 2 = ‖p x‖ ^ 2 + ‖e x‖ ^ 2 + ‖f x‖ ^ 2)
    (hform : ∀ x : F,
      RCLike.re (inner 𝕜 x (A x)) =
        RCLike.re (inner 𝕜 (p x) (T (p x))) +
          2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
          RCLike.re (inner 𝕜 (e x) (D (e x))) +
          2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
          RCLike.re (inner 𝕜 (f x) (C (f x))))
    (hD : ∀ y : E,
      RCLike.re (inner 𝕜 y (D y)) ≤ beta * ‖y‖ ^ 2)
    (hC : ∀ y : W,
      RCLike.re (inner 𝕜 y (C y)) ≤ beta * ‖y‖ ^ 2)
    (hRsq : ∀ y : E, ‖R y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2)
    (hnewGap : beta < z - beta ^ 2 / (z - beta)) :
    let s := beta ^ 2 / (z - beta)
    let newEnergy := z - s
    let newGap := newEnergy - beta
    let Rnew := rclikeFiniteResolventOfGap D newEnergy newGap
      (sub_pos.mpr hnewGap)
      (rclike_shifted_lowerBound_of_quadratic_upper D hD)
    ∀ x : F,
      RCLike.re (inner 𝕜 x (A x)) - z * ‖x‖ ^ 2 ≤
        rclikeSchurReducedForm T K Rnew z (p x) := by
  dsimp only
  let s := beta ^ 2 / (z - beta)
  let newEnergy := z - s
  let newGap := newEnergy - beta
  let hgap : ∀ y : E, newGap * ‖y‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) newEnergy) • y - D y‖ :=
    rclike_shifted_lowerBound_of_quadratic_upper D hD
  let Rnew := rclikeFiniteResolventOfGap D newEnergy newGap
    (sub_pos.mpr hnewGap) hgap
  intro x
  have hlast := schur_cross_block_quadratic_upper
    (𝕜 := 𝕜) (E := W) (x := R (e x)) (y := f x)
    (q := RCLike.re (inner 𝕜 (f x) (C (f x))))
    (hC (f x)) hz
  have hzPos : 0 < z - beta := sub_pos.mpr hz
  have hlast' :
      2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
          RCLike.re (inner 𝕜 (f x) (C (f x))) - z * ‖f x‖ ^ 2 ≤
        s * ‖e x‖ ^ 2 := by
    calc
      2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
            RCLike.re (inner 𝕜 (f x) (C (f x))) - z * ‖f x‖ ^ 2 ≤
          ‖R (e x)‖ ^ 2 / (z - beta) := hlast
      _ ≤ (beta ^ 2 * ‖e x‖ ^ 2) / (z - beta) :=
        (div_le_div_iff_of_pos_right hzPos).2 (hRsq (e x))
      _ = s * ‖e x‖ ^ 2 := by dsimp [s]; ring
  have hmiddle := rclike_schur_cross_quadratic_le_resolvent
    D K hnewGap hDsymm hD (p x) (e x)
  rw [hform x, hnorm x]
  dsimp [rclikeSchurReducedForm]
  calc
    RCLike.re (inner 𝕜 (p x) (T (p x))) +
          2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
          RCLike.re (inner 𝕜 (e x) (D (e x))) +
          2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
          RCLike.re (inner 𝕜 (f x) (C (f x))) -
        z * (‖p x‖ ^ 2 + ‖e x‖ ^ 2 + ‖f x‖ ^ 2) =
      (RCLike.re (inner 𝕜 (p x) (T (p x))) - z * ‖p x‖ ^ 2) +
        (2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
          RCLike.re (inner 𝕜 (e x) (D (e x))) -
          newEnergy * ‖e x‖ ^ 2) +
        (2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
          RCLike.re (inner 𝕜 (f x) (C (f x))) - z * ‖f x‖ ^ 2 -
          s * ‖e x‖ ^ 2) := by dsimp [newEnergy]; ring
    _ ≤ (RCLike.re (inner 𝕜 (p x) (T (p x))) - z * ‖p x‖ ^ 2) +
        (2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
          RCLike.re (inner 𝕜 (e x) (D (e x))) -
          newEnergy * ‖e x‖ ^ 2) := by linarith
    _ ≤ RCLike.re (inner 𝕜 (p x) (T (p x))) - z * ‖p x‖ ^ 2 +
        RCLike.re (inner 𝕜 (K (p x)) (Rnew (K (p x)))) := by linarith

theorem rclike_threeBlock_quadratic_le_oldReducedForm_of_s_le_delta
    (A : F →ₗ[𝕜] F) (T : P →ₗ[𝕜] P)
    (D : E →ₗ[𝕜] E) (C : W →ₗ[𝕜] W)
    (K : P →ₗ[𝕜] E) (R : E →ₗ[𝕜] W)
    (p : F →ₗ[𝕜] P) (e : F →ₗ[𝕜] E) (f : F →ₗ[𝕜] W)
    {beta rho : ℝ} (hbeta : 0 ≤ beta) (hrho : 0 < rho)
    (hscale : 4 * beta ≤ rho) (hDsymm : D.IsSymmetric)
    (hnorm : ∀ x : F,
      ‖x‖ ^ 2 = ‖p x‖ ^ 2 + ‖e x‖ ^ 2 + ‖f x‖ ^ 2)
    (hform : ∀ x : F,
      RCLike.re (inner 𝕜 x (A x)) =
        RCLike.re (inner 𝕜 (p x) (T (p x))) +
          2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
          RCLike.re (inner 𝕜 (e x) (D (e x))) +
          2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
          RCLike.re (inner 𝕜 (f x) (C (f x))))
    (hD : ∀ y : E,
      RCLike.re (inner 𝕜 y (D y)) ≤ beta * ‖y‖ ^ 2)
    (hC : ∀ y : W,
      RCLike.re (inner 𝕜 y (C y)) ≤ beta * ‖y‖ ^ 2)
    (hRsq : ∀ y : E, ‖R y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2) :
    let delta := 3 * beta ^ 4 / rho ^ 3
    let z := rho + delta
    let s := beta ^ 2 / (z - beta)
    s ≤ delta →
      let oldGap := rho - beta
      let Rold := rclikeFiniteResolventOfGap D rho oldGap
        (by
          have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
          dsimp only at hparams
          exact lt_of_lt_of_le (by positivity) hparams.2.2.2.2.2)
        (rclike_shifted_lowerBound_of_quadratic_upper D hD)
      ∀ x : F,
        RCLike.re (inner 𝕜 x (A x)) - z * ‖x‖ ^ 2 ≤
          rclikeSchurReducedForm T K Rold rho (p x) := by
  dsimp only
  let delta := 3 * beta ^ 4 / rho ^ 3
  let z := rho + delta
  let s := beta ^ 2 / (z - beta)
  intro hs
  have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
  dsimp only at hparams
  rcases hparams with
    ⟨hdelta, hzbeta, _hsNonneg, _hsUpper, _hnewGap, holdGap⟩
  let oldGap := rho - beta
  have holdGapPos : 0 < oldGap :=
    lt_of_lt_of_le (by positivity) holdGap
  let hgap : ∀ y : E, oldGap * ‖y‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) rho) • y - D y‖ :=
    rclike_shifted_lowerBound_of_quadratic_upper D hD
  let Rold := rclikeFiniteResolventOfGap D rho oldGap holdGapPos hgap
  intro x
  have hlast := schur_cross_block_quadratic_upper
    (𝕜 := 𝕜) (E := W) (x := R (e x)) (y := f x)
    (q := RCLike.re (inner 𝕜 (f x) (C (f x))))
    (hC (f x)) hzbeta
  have hzPos : 0 < z - beta := sub_pos.mpr hzbeta
  have hlast' :
      2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
          RCLike.re (inner 𝕜 (f x) (C (f x))) - z * ‖f x‖ ^ 2 ≤
        s * ‖e x‖ ^ 2 := by
    calc
      2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
            RCLike.re (inner 𝕜 (f x) (C (f x))) - z * ‖f x‖ ^ 2 ≤
          ‖R (e x)‖ ^ 2 / (z - beta) := hlast
      _ ≤ (beta ^ 2 * ‖e x‖ ^ 2) / (z - beta) :=
        (div_le_div_iff_of_pos_right hzPos).2 (hRsq (e x))
      _ = s * ‖e x‖ ^ 2 := by dsimp [s]; ring
  have hmiddle := rclike_schur_cross_quadratic_le_resolvent
    D K (sub_pos.mp holdGapPos) hDsymm hD (p x) (e x)
  rw [hform x, hnorm x]
  dsimp [rclikeSchurReducedForm]
  have hpre :
      RCLike.re (inner 𝕜 (p x) (T (p x))) +
            2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
            RCLike.re (inner 𝕜 (e x) (D (e x))) +
            2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
            RCLike.re (inner 𝕜 (f x) (C (f x))) -
          z * (‖p x‖ ^ 2 + ‖e x‖ ^ 2 + ‖f x‖ ^ 2) ≤
        (RCLike.re (inner 𝕜 (p x) (T (p x))) - rho * ‖p x‖ ^ 2) +
          (2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
            RCLike.re (inner 𝕜 (e x) (D (e x))) -
            rho * ‖e x‖ ^ 2) := by
    dsimp [z] at hlast' ⊢
    nlinarith [mul_nonneg hdelta (sq_nonneg ‖p x‖),
      mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg ‖e x‖)]
  exact hpre.trans <| by linarith


/- Source slice: QuadraticPositiveSubspaceTransfer.lean -/

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem rclike_positiveSubspace_transfer_of_quadratic_domination
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] E) (G : F →ₗ[𝕜] F)
    (z rho : ℝ) (f : E →ₗ[𝕜] F)
    (hdom : ∀ x : E,
      RCLike.re (inner 𝕜 x (A x)) - z * ‖x‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (f x) (G (f x))) - rho * ‖f x‖ ^ 2)
    (W : Submodule 𝕜 E)
    (hWpositive : ∀ x ∈ W, x ≠ 0 →
      z * ‖x‖ ^ 2 < RCLike.re (inner 𝕜 x (A x))) :
    ∃ V : Submodule 𝕜 F,
      (∀ y ∈ V, y ≠ 0 →
        rho * ‖y‖ ^ 2 < RCLike.re (inner 𝕜 y (G y))) ∧
      Module.finrank 𝕜 W ≤ Module.finrank 𝕜 V := by
  let fW : W →ₗ[𝕜] F := f.domRestrict W
  have hfW : Function.Injective fW := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hsubmem : (x : E) - (y : E) ∈ W := W.sub_mem x.property y.property
    have hsubne : (x : E) - (y : E) ≠ 0 := sub_ne_zero.mpr hne
    have hpositive := hWpositive ((x : E) - (y : E)) hsubmem hsubne
    have hzero : f ((x : E) - (y : E)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hupper := hdom ((x : E) - (y : E))
    rw [hzero] at hupper
    simp at hupper
    rw [map_sub] at hpositive
    linarith
  let V : Submodule 𝕜 F := LinearMap.range fW
  refine ⟨V, ?_, ?_⟩
  · intro y hyV hy0
    obtain ⟨x, rfl⟩ := hyV
    have hx0 : x ≠ 0 := by
      intro hx
      apply hy0
      simp [hx]
    have hpositive := hWpositive (x : E) x.property (by
      intro hx
      apply hx0
      exact Subtype.ext hx)
    have hupper := hdom (x : E)
    change rho * ‖fW x‖ ^ 2 < RCLike.re (inner 𝕜 (fW x) (G (fW x)))
    dsimp [fW] at hupper ⊢
    linarith
  · rw [LinearMap.finrank_range_of_inj hfW]


/- Source slice: TwoStageSchurScalar.lean -/

theorem twoStageSchur_sq_sub_sq_le
    {lambda rho B : ℝ}
    (hB : 0 ≤ B) (hrho : 0 < rho) (hscale : 4 * B ≤ rho)
    (hlower : rho ≤ lambda)
    (hupper : lambda ≤ rho + 3 * B ^ 4 / rho ^ 3) :
    0 ≤ lambda ^ 2 - rho ^ 2 ∧
      lambda ^ 2 - rho ^ 2 ≤ 7 * B ^ 4 / rho ^ 2 := by
  have hlambda : 0 ≤ lambda := hrho.le.trans hlower
  have hpow : (4 * B) ^ 4 ≤ rho ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hB) hscale 4
  have h9 : 9 * B ^ 4 ≤ rho ^ 4 := by
    norm_num [mul_pow] at hpow
    have hB4 : 0 ≤ B ^ 4 := by positivity
    exact (mul_le_mul_of_nonneg_right (by norm_num : (9 : ℝ) ≤ 256) hB4).trans hpow
  have htail : 9 * B ^ 8 / rho ^ 6 ≤ B ^ 4 / rho ^ 2 := by
    rw [div_le_iff₀ (pow_pos hrho 6)]
    have hmul := mul_le_mul_of_nonneg_left h9 (show 0 ≤ B ^ 4 by positivity)
    calc
      9 * B ^ 8 = B ^ 4 * (9 * B ^ 4) := by ring
      _ ≤ B ^ 4 * rho ^ 4 := hmul
      _ = B ^ 4 / rho ^ 2 * rho ^ 6 := by
        field_simp
  have hdelta : 0 ≤ 3 * B ^ 4 / rho ^ 3 := by positivity
  have hdiff : 0 ≤ lambda - rho := sub_nonneg.mpr hlower
  have hdiffUpper : lambda - rho ≤ 3 * B ^ 4 / rho ^ 3 := by
    linarith
  have hsumUpper : lambda + rho ≤ 2 * rho + 3 * B ^ 4 / rho ^ 3 := by
    linarith
  constructor
  · calc
      0 ≤ (lambda - rho) * (lambda + rho) :=
        mul_nonneg hdiff (add_nonneg hlambda hrho.le)
      _ = lambda ^ 2 - rho ^ 2 := by ring
  · calc
      lambda ^ 2 - rho ^ 2 = (lambda - rho) * (lambda + rho) := by ring
      _ ≤ (3 * B ^ 4 / rho ^ 3) *
          (2 * rho + 3 * B ^ 4 / rho ^ 3) := by
        exact mul_le_mul hdiffUpper hsumUpper
          (add_nonneg hlambda hrho.le) hdelta
      _ = 6 * B ^ 4 / rho ^ 2 + 9 * B ^ 8 / rho ^ 6 := by
        field_simp
        ring
      _ ≤ 6 * B ^ 4 / rho ^ 2 + B ^ 4 / rho ^ 2 :=
        add_le_add_right htail _
      _ = 7 * B ^ 4 / rho ^ 2 := by ring


/- Source slice: TwoStageSchurComparison.lean -/

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem rclike_padded_twoStageSchur_sq_comparison_of_root_upper
    (A G : E →ₗ[𝕜] E) (hA : A.IsSymmetric) (hG : G.IsSymmetric)
    (P : E →ₗ[𝕜] E)
    (hcompression : ∀ x : E,
      RCLike.re (inner 𝕜 x (G x)) =
        RCLike.re (inner 𝕜 (P x) (A (P x))))
    (hcontract : ∀ x : E, ‖P x‖ ≤ ‖x‖)
    (i : Fin (Module.finrank 𝕜 E)) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hrho : 0 < hG.eigenvalues rfl i)
    (hscale : 4 * beta ≤ hG.eigenvalues rfl i)
    (hrootUpper :
      hA.eigenvalues rfl i ≤
        hG.eigenvalues rfl i +
          3 * beta ^ 4 / (hG.eigenvalues rfl i) ^ 3) :
    0 ≤ (hA.eigenvalues rfl i) ^ 2 - (hG.eigenvalues rfl i) ^ 2 ∧
      (hA.eigenvalues rfl i) ^ 2 - (hG.eigenvalues rfl i) ^ 2 ≤
        7 * beta ^ 4 / (hG.eigenvalues rfl i) ^ 2 := by
  have hlower : hG.eigenvalues rfl i ≤ hA.eigenvalues rfl i :=
    rclike_positive_paddedCompression_eigenvalue_le
      A G hA hG P hcompression hcontract i hrho
  exact twoStageSchur_sq_sub_sq_le hbeta hrho hscale hlower hrootUpper

theorem rclike_padded_twoStageSchur_sq_comparison_of_quadratic_domination
    (A G : E →ₗ[𝕜] E) (hA : A.IsSymmetric) (hG : G.IsSymmetric)
    (P : E →ₗ[𝕜] E)
    (hcompression : ∀ x : E,
      RCLike.re (inner 𝕜 x (G x)) =
        RCLike.re (inner 𝕜 (P x) (A (P x))))
    (hcontract : ∀ x : E, ‖P x‖ ≤ ‖x‖)
    (i : Fin (Module.finrank 𝕜 E)) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hrho : 0 < hG.eigenvalues rfl i)
    (hscale : 4 * beta ≤ hG.eigenvalues rfl i)
    (f : E →ₗ[𝕜] E)
    (hdom : ∀ x : E,
      RCLike.re (inner 𝕜 x (A x)) -
          (hG.eigenvalues rfl i +
            3 * beta ^ 4 / (hG.eigenvalues rfl i) ^ 3) * ‖x‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (f x) (G (f x))) -
          hG.eigenvalues rfl i * ‖f x‖ ^ 2) :
    0 ≤ (hA.eigenvalues rfl i) ^ 2 - (hG.eigenvalues rfl i) ^ 2 ∧
      (hA.eigenvalues rfl i) ^ 2 - (hG.eigenvalues rfl i) ^ 2 ≤
        7 * beta ^ 4 / (hG.eigenvalues rfl i) ^ 2 := by
  have hrootUpper :
      hA.eigenvalues rfl i ≤
        hG.eigenvalues rfl i +
          3 * beta ^ 4 / (hG.eigenvalues rfl i) ^ 3 := by
    apply rclike_eigenvalue_le_of_positive_subspace_finrank_le A hA i _
    intro W hWpositive
    obtain ⟨V, hVpositive, hWV⟩ :=
      rclike_positiveSubspace_transfer_of_quadratic_domination
        A G _ _ f hdom W hWpositive
    exact hWV.trans
      (rclike_finrank_positive_subspace_le_eigenvalue_index
        G hG i V hVpositive)
  exact rclike_padded_twoStageSchur_sq_comparison_of_root_upper
    A G hA hG P hcompression hcontract i hbeta hrho hscale hrootUpper


/- Source slice: RealTwoStageSchurComparison.lean -/

open scoped InnerProductSpace

variable {F G₀ P E W : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G₀] [InnerProductSpace ℝ G₀]
  [FiniteDimensional ℝ G₀]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {𝕜 F P E W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

theorem rclike_padded_twoStageSchur_sq_comparison_of_block_reduction
    (A G : F →ₗ[𝕜] F) (hA : A.IsSymmetric) (hG : G.IsSymmetric)
    (Q : F →ₗ[𝕜] F)
    (hcompression : ∀ x : F,
      RCLike.re (inner 𝕜 x (G x)) =
        RCLike.re (inner 𝕜 (Q x) (A (Q x))))
    (hcontract : ∀ x : F, ‖Q x‖ ≤ ‖x‖)
    (i : Fin (Module.finrank 𝕜 F)) {beta : ℝ}
    (hbeta : 0 ≤ beta) (hrho : 0 < hG.eigenvalues rfl i)
    (hscale : 4 * beta ≤ hG.eigenvalues rfl i)
    (T : P →ₗ[𝕜] P) (D : E →ₗ[𝕜] E) (C : W →ₗ[𝕜] W)
    (K : P →ₗ[𝕜] E) (R : E →ₗ[𝕜] W)
    (p : F →ₗ[𝕜] P) (e : F →ₗ[𝕜] E) (f : F →ₗ[𝕜] W)
    (hDsymm : D.IsSymmetric)
    (hnorm : ∀ x : F,
      ‖x‖ ^ 2 = ‖p x‖ ^ 2 + ‖e x‖ ^ 2 + ‖f x‖ ^ 2)
    (hform : ∀ x : F,
      RCLike.re (inner 𝕜 x (A x)) =
        RCLike.re (inner 𝕜 (p x) (T (p x))) +
          2 * RCLike.re (inner 𝕜 (K (p x)) (e x)) +
          RCLike.re (inner 𝕜 (e x) (D (e x))) +
          2 * RCLike.re (inner 𝕜 (R (e x)) (f x)) +
          RCLike.re (inner 𝕜 (f x) (C (f x))))
    (hD : ∀ y : E,
      RCLike.re (inner 𝕜 y (D y)) ≤ beta * ‖y‖ ^ 2)
    (hC : ∀ y : W,
      RCLike.re (inner 𝕜 y (C y)) ≤ beta * ‖y‖ ^ 2)
    (hKsq : ∀ y : P, ‖K y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2)
    (hRsq : ∀ y : E, ‖R y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2)
    (reconstruct : P →ₗ[𝕜] F)
    (hold :
      let rho := hG.eigenvalues rfl i
      let oldGap := rho - beta
      let Rold := rclikeFiniteResolventOfGap D rho oldGap
        (by
          have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
          dsimp only at hparams
          exact lt_of_lt_of_le (by positivity) hparams.2.2.2.2.2)
        (rclike_shifted_lowerBound_of_quadratic_upper D hD)
      ∀ x : F,
        rclikeSchurReducedForm T K Rold rho (p x) =
          RCLike.re (inner 𝕜 (reconstruct (p x))
            (G (reconstruct (p x)))) -
            rho * ‖reconstruct (p x)‖ ^ 2) :
    0 ≤ (hA.eigenvalues rfl i) ^ 2 - (hG.eigenvalues rfl i) ^ 2 ∧
      (hA.eigenvalues rfl i) ^ 2 - (hG.eigenvalues rfl i) ^ 2 ≤
        7 * beta ^ 4 / (hG.eigenvalues rfl i) ^ 2 := by
  let rho := hG.eigenvalues rfl i
  let delta := 3 * beta ^ 4 / rho ^ 3
  let z := rho + delta
  let s := beta ^ 2 / (z - beta)
  have hparams := twoStageSchur_parameter_margins hbeta hrho hscale
  change 0 ≤ delta ∧ beta < z ∧ 0 ≤ s ∧ s ≤ beta / 3 ∧
      2 * rho / 3 ≤ z - s - beta ∧ 3 * rho / 4 ≤ rho - beta at hparams
  rcases hparams with
    ⟨hdelta, hzbeta, _hsNonneg, _hsUpper, hnewGap, holdGap⟩
  let oldGap := rho - beta
  have holdGapPos : 0 < oldGap :=
    lt_of_lt_of_le (by positivity) holdGap
  let hgapOld : ∀ y : E, oldGap * ‖y‖ ≤
      ‖(RCLike.ofReal (K := 𝕜) rho) • y - D y‖ :=
    rclike_shifted_lowerBound_of_quadratic_upper D hD
  let Rold := rclikeFiniteResolventOfGap D rho oldGap
    holdGapPos hgapOld
  have hold' : ∀ x : F,
      rclikeSchurReducedForm T K Rold rho (p x) =
        RCLike.re (inner 𝕜 (reconstruct (p x))
          (G (reconstruct (p x)))) -
          rho * ‖reconstruct (p x)‖ ^ 2 := by
    simpa [rho, oldGap, Rold, hgapOld] using hold
  have hdom : ∀ x : F,
      RCLike.re (inner 𝕜 x (A x)) - z * ‖x‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (reconstruct (p x))
            (G (reconstruct (p x)))) -
          rho * ‖reconstruct (p x)‖ ^ 2 := by
    intro x
    by_cases hs : s ≤ delta
    · have heasy := rclike_threeBlock_quadratic_le_oldReducedForm_of_s_le_delta
        A T D C K R p e f hbeta hrho hscale hDsymm hnorm hform hD hC hRsq
          hs x
      exact heasy.trans_eq (hold' x)
    · have hdeltaS : delta < s := lt_of_not_ge hs
      let newEnergy := z - s
      let newGap := newEnergy - beta
      have hnewGapPos : 0 < newGap :=
        lt_of_lt_of_le (by positivity) hnewGap
      let hgapNew : ∀ y : E, newGap * ‖y‖ ≤
          ‖(RCLike.ofReal (K := 𝕜) newEnergy) • y - D y‖ :=
        rclike_shifted_lowerBound_of_quadratic_upper D hD
      let Rnew := rclikeFiniteResolventOfGap D newEnergy newGap
        hnewGapPos hgapNew
      have hnew := rclike_threeBlock_quadratic_le_reducedForm
        A T D C K R p e f hzbeta hDsymm hnorm hform hD hC hRsq
          (sub_pos.mp hnewGapPos) x
      have hself := rclike_twoStageSchur_selfEnergy_sub_le_delta
        D K hbeta hrho hscale hDsymm hD hKsq hdeltaS (p x)
      have hcompare :
          rclikeSchurReducedForm T K Rnew z (p x) ≤
            rclikeSchurReducedForm T K Rold rho (p x) := by
        dsimp [rclikeSchurReducedForm, Rnew, Rold, newEnergy, newGap,
          oldGap, hgapNew, hgapOld] at hself ⊢
        dsimp [z] at hself ⊢
        nlinarith
      exact (hnew.trans hcompare).trans_eq (hold' x)
  apply rclike_padded_twoStageSchur_sq_comparison_of_quadratic_domination
    A G hA hG Q hcompression hcontract i hbeta hrho hscale
      (reconstruct.comp p)
  simpa [rho, delta, z] using hdom


/- Source slice: FullSpectrumTargetTransport.lean -/

open Filter Topology

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

local instance fullSpectrumPrimeCoverDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.primeCoverGraph S X).Adj :=
  Classical.decRel _

local instance fullSpectrumSmallPrimeDecidableAdj
    (S : Finset ℕ) (X : ℕ) :
    DecidableRel
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

def fullAdjacencyArithmeticRankIndex
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) :
    Fin (Module.finrank ℝ (EuclideanSpace ℝ (PrimeStar.Vertex S X))) := by
  let T := Finset.univ.filter fun b : PrimeStar.Vertex S X ↦
    (b : ℕ) < (a : ℕ)
  refine ⟨T.card, ?_⟩
  have hproper : T ⊂ (Finset.univ : Finset (PrimeStar.Vertex S X)) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, ?_⟩
    intro hEq
    have ha : a ∈ T := by simp [hEq]
    simp [T] at ha
  simpa using Finset.card_lt_card hproper

theorem fullPrimeCoverAdjacencyIsSymmetric (S : Finset ℕ) (X : ℕ) :
    (Matrix.toEuclideanLin
      ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ)).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((PrimeStar.primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))

def fullAdjacencyEigenvalueAtArithmeticRank
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) : ℝ :=
  (fullPrimeCoverAdjacencyIsSymmetric S X).eigenvalues rfl
    (fullAdjacencyArithmeticRankIndex a)

/-- S2's full-adjacency value is the exact ordered eigenvalue selected by the
public Challenge, with no permutation or rank-offset hypothesis. -/
theorem fullAdjacencyEigenvalueAtArithmeticRank_eq_lambdaAtArithmeticRank
    {S : Finset ℕ} {X : ℕ} (a : Vertex S X) :
    fullAdjacencyEigenvalueAtArithmeticRank a = lambdaAtArithmeticRank a := by
  rfl

def oneExitArithmeticRankIndex
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) :
    Fin (Fintype.card (PrimeStar.Vertex S X)) := by
  let T := Finset.univ.filter fun b : PrimeStar.Vertex S X ↦
    (b : ℕ) < (a : ℕ)
  refine ⟨T.card, ?_⟩
  have hproper : T ⊂ (Finset.univ : Finset (PrimeStar.Vertex S X)) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, ?_⟩
    intro hEq
    have ha : a ∈ T := by simp [hEq]
    simp [T] at ha
  simpa using Finset.card_lt_card hproper

def oneExitEigenvalueAtArithmeticRank
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) : ℝ :=
  (oneExitCompression_isHermitian S X).eigenvalues₀
    (oneExitArithmeticRankIndex a)

theorem moleculeFamilyComplexAdjacencyEigenvalueAtArithmeticRank_eq
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) :
    (moleculeFamilyComplexAdjacency_isHermitian S X).eigenvalues₀
        (oneExitArithmeticRankIndex a) =
      fullAdjacencyEigenvalueAtArithmeticRank a := by
  rw [moleculeFamilyComplexAdjacency_eigenvalues₀_eq_real]
  let A := Matrix.toEuclideanLin
    ((PrimeStar.primeCoverGraph S X).adjMatrix ℝ)
  let hA : A.IsSymmetric := fullPrimeCoverAdjacencyIsSymmetric S X
  let i : Fin (Module.finrank ℝ
      (EuclideanSpace ℝ (PrimeStar.Vertex S X))) :=
    Fin.cast finrank_euclideanSpace.symm (oneExitArithmeticRankIndex a)
  have hi : i = fullAdjacencyArithmeticRankIndex a := by
    apply Fin.ext
    rfl
  calc
    ((PrimeStar.primeCoverGraph S X).isHermitian_adjMatrix
        (R := ℝ)).eigenvalues₀ (oneExitArithmeticRankIndex a) =
        hA.eigenvalues finrank_euclideanSpace
          (oneExitArithmeticRankIndex a) := by rfl
    _ = hA.eigenvalues rfl i := by
      exact (symmetricEigenvalues_cast A hA finrank_euclideanSpace
        (oneExitArithmeticRankIndex a)).symm
    _ = fullAdjacencyEigenvalueAtArithmeticRank a := by
      rw [hi]
      rfl

theorem oneExitCompression_quadraticForm_eq
    (S : Finset ℕ) (X : ℕ)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    RCLike.re (inner ℂ x
        (Matrix.toEuclideanLin (oneExitCompression S X) x)) =
      RCLike.re (inner ℂ
        (Matrix.toEuclideanLin (oneExitProjection S X) x)
        (Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
          (Matrix.toEuclideanLin (oneExitProjection S X) x))) := by
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  let A := Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
  have hP : P.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have happly :
      Matrix.toEuclideanLin (oneExitCompression S X) x = P (A (P x)) := by
    apply PiLp.ext
    intro i
    simp only [oneExitCompression, P, A, Matrix.toLpLin_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [happly]
  exact congrArg RCLike.re (hP x (A (P x))).symm

theorem norm_oneExitProjection_apply_le
    (S : Finset ℕ) (X : ℕ)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    ‖Matrix.toEuclideanLin (oneExitProjection S X) x‖ ≤ ‖x‖ := by
  have hnorm : ‖oneExitProjection S X‖ ≤ (1 : ℝ) :=
    IsStarProjection.norm_le _ (oneExitProjection_isStarProjection S X)
  have hmul := (oneExitProjection S X).l2_opNorm_mulVec x
  change
    ‖(EuclideanSpace.equiv (PrimeStar.Vertex S X) ℂ).symm
        ((oneExitProjection S X).mulVec x.ofLp)‖ ≤ ‖x‖
  simpa only [one_mul] using
    hmul.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))

private theorem norm_matrixToEuclideanLin_apply_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A x‖ ≤ matrixL2OperatorNorm A * ‖x‖ := by
  change
    ‖(EuclideanSpace.equiv n ℂ).symm (A.mulVec x.ofLp)‖ ≤
      matrixL2OperatorNorm A * ‖x‖
  simpa only [matrixL2OperatorNorm] using A.l2_opNorm_mulVec x

private theorem norm_complexEuclideanRealPart_le
    {n : Type*} [Fintype n]
    (x : EuclideanSpace ℂ n) :
    ‖complexEuclideanRealPart x‖ ≤ ‖x‖ := by
  have hsquares : ‖complexEuclideanRealPart x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _hi
    change (x i).re ^ 2 ≤ ‖x i‖ ^ 2
    nlinarith [Complex.sq_norm_sub_sq_re (x i), sq_nonneg (x i).im]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares

private theorem norm_complexEuclideanImagPart_le
    {n : Type*} [Fintype n]
    (x : EuclideanSpace ℂ n) :
    ‖complexEuclideanImagPart x‖ ≤ ‖x‖ := by
  have hsquares : ‖complexEuclideanImagPart x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _hi
    change (x i).im ^ 2 ≤ ‖x i‖ ^ 2
    nlinarith [Complex.sq_norm_sub_sq_im (x i), sq_nonneg (x i).re]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares

private def lowerArithmeticCenters
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) :
    Finset (PrimeStar.Vertex S X) :=
  Finset.univ.filter fun b ↦ (b : ℕ) ≤ (a : ℕ)

private theorem card_lowerArithmeticCenters
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) :
    (lowerArithmeticCenters a).card = (oneExitArithmeticRankIndex a).1 + 1 := by
  let T := Finset.univ.filter fun b : PrimeStar.Vertex S X ↦
    (b : ℕ) < (a : ℕ)
  have hdecomp : lowerArithmeticCenters a = insert a T := by
    ext b
    simp only [lowerArithmeticCenters, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, T]
    constructor
    · intro hba
      rcases hba.eq_or_lt with h | h
      · left
        exact Subtype.ext (Fin.ext h)
      · exact Or.inr h
    · rintro (h | h)
      · subst b
        exact le_rfl
      · exact h.le
  have haT : a ∉ T := by simp [T]
  rw [hdecomp, Finset.card_insert_of_notMem haT]
  rfl

private def lowerArithmeticPositiveStarCenter
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (b : ↑(lowerArithmeticCenters a)) : PositiveStarCenter S X := by
  have hba : (b.1 : ℕ) ≤ (a : ℕ) := by
    exact (Finset.mem_filter.mp b.2).2
  have hbY : (b.1 : ℕ) ≤ squareRootCutoff X := hba.trans ha
  have hdegree := PrimeStar.largePrimeStarDegree_antitone_of_center_le
    hS hbY ha hba
  exact ⟨b.1, hbY, hd.trans_le hdegree⟩

private def lowerPositiveStarFrame
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix (PrimeStar.Vertex S X) (↑(lowerArithmeticCenters a)) ℂ :=
  fun v b ↦ positiveStarFrame S X v
    (lowerArithmeticPositiveStarCenter hS a ha hd b)

private theorem lowerPositiveStarFrame_conjTranspose_mul_self
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    (lowerPositiveStarFrame hS a ha hd).conjTranspose *
        lowerPositiveStarFrame hS a ha hd = 1 := by
  let f := lowerArithmeticPositiveStarCenter hS a ha hd
  have hf : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    have hval := congrArg (fun z : PositiveStarCenter S X ↦ z.1) hbc
    simpa [f, lowerArithmeticPositiveStarCenter] using hval
  have hglobal := positiveStarFrame_conjTranspose_mul_self S X
  ext b c
  have hentry := congrArg (fun M ↦ M (f b) (f c)) hglobal
  simpa [lowerPositiveStarFrame, Matrix.mul_apply, Matrix.one_apply, f,
    hf.eq_iff] using hentry

private theorem lowerPositiveStarFrame_inner_map_map
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (x y : EuclideanSpace ℂ (↑(lowerArithmeticCenters a))) :
    inner ℂ
        (Matrix.toEuclideanLin (lowerPositiveStarFrame hS a ha hd) x)
        (Matrix.toEuclideanLin (lowerPositiveStarFrame hS a ha hd) y) =
      inner ℂ x y := by
  let Q := lowerPositiveStarFrame hS a ha hd
  have hQ := lowerPositiveStarFrame_conjTranspose_mul_self hS a ha hd
  have hleft : Matrix.toEuclideanLin Q.conjTranspose
      (Matrix.toEuclideanLin Q y) = y := by
    have hlin := congrArg Matrix.toEuclideanLin hQ
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one] at hlin
    exact LinearMap.congr_fun hlin y
  calc
    inner ℂ (Matrix.toEuclideanLin Q x) (Matrix.toEuclideanLin Q y) =
        inner ℂ x
          ((Matrix.toEuclideanLin Q).adjoint
            (Matrix.toEuclideanLin Q y)) :=
      (LinearMap.adjoint_inner_right (Matrix.toEuclideanLin Q) x
        (Matrix.toEuclideanLin Q y)).symm
    _ = inner ℂ x y := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      rw [hleft]

private theorem lowerPositiveStarFrame_toEuclideanLin_injective
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Function.Injective
      (Matrix.toEuclideanLin (lowerPositiveStarFrame hS a ha hd)) := by
  intro x y hxy
  let Q := lowerPositiveStarFrame hS a ha hd
  have hQ := lowerPositiveStarFrame_conjTranspose_mul_self hS a ha hd
  have hleft : ∀ z, Matrix.toEuclideanLin Q.conjTranspose
      (Matrix.toEuclideanLin Q z) = z := by
    intro z
    have hlin := congrArg Matrix.toEuclideanLin hQ
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one] at hlin
    exact LinearMap.congr_fun hlin z
  calc
    x = Matrix.toEuclideanLin Q.conjTranspose
        (Matrix.toEuclideanLin Q x) := (hleft x).symm
    _ = Matrix.toEuclideanLin Q.conjTranspose
        (Matrix.toEuclideanLin Q y) := congrArg _ hxy
    _ = y := hleft y

private def lowerPositiveStarEnergyMatrix
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) :
    Matrix (↑(lowerArithmeticCenters a)) (↑(lowerArithmeticCenters a)) ℂ :=
  Matrix.diagonal fun b ↦
    (Real.sqrt (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      b.1 : ℝ) : ℂ)

private theorem oneExitLargePrimeMatrix_mul_lowerPositiveStarFrame
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    oneExitLargePrimeMatrix S X * lowerPositiveStarFrame hS a ha hd =
      lowerPositiveStarFrame hS a ha hd * lowerPositiveStarEnergyMatrix a := by
  ext v b
  have hbY : (b.1 : ℕ) ≤ squareRootCutoff X :=
    (lowerArithmeticPositiveStarCenter hS a ha hd b).2.1
  have heig := oneExitLargePrimeMatrix_apply_complexified_positiveStarMode
    (S := S) (X := X) (a := b.1) hbY
  have hv := congrArg (fun z ↦ z v) heig
  change
    (∑ x, oneExitLargePrimeMatrix S X v x *
        lowerPositiveStarFrame hS a ha hd x b) =
      (lowerPositiveStarFrame hS a ha hd *
        lowerPositiveStarEnergyMatrix a) v b
  unfold lowerPositiveStarEnergyMatrix
  rw [Matrix.mul_diagonal]
  simpa [lowerPositiveStarFrame, positiveStarFrame, positiveStarFrameReal,
    lowerArithmeticPositiveStarCenter, complexifyRealMatrix,
    lowerPositiveStarEnergyMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    mul_comm] using hv

private theorem lowerPositiveStarEnergy_ge_terminal
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (b : ↑(lowerArithmeticCenters a)) :
    Real.sqrt (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) ≤
      Real.sqrt (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b.1 : ℝ) := by
  have hba : (b.1 : ℕ) ≤ (a : ℕ) := (Finset.mem_filter.mp b.2).2
  have hbY : (b.1 : ℕ) ≤ squareRootCutoff X := hba.trans ha
  have hdegree := PrimeStar.largePrimeStarDegree_antitone_of_center_le
    hS hbY ha hba
  exact Real.sqrt_le_sqrt (by exact_mod_cast hdegree)

private theorem lowerPositiveStarEnergy_quadratic_ge_terminal
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (x : EuclideanSpace ℂ (↑(lowerArithmeticCenters a))) :
    Real.sqrt (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) *
        ‖x‖ ^ 2 ≤
      RCLike.re (inner ℂ x
        (Matrix.toEuclideanLin (lowerPositiveStarEnergyMatrix a) x)) := by
  rw [EuclideanSpace.norm_sq_eq, PiLp.inner_apply, map_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _hb
  have henergy := lowerPositiveStarEnergy_ge_terminal hS a ha b
  unfold lowerPositiveStarEnergyMatrix
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  have hnorm : ‖x b‖ ^ 2 = (x b).re * (x b).re + (x b).im * (x b).im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hmul := mul_le_mul_of_nonneg_right henergy (sq_nonneg ‖x b‖)
  rw [hnorm] at hmul
  rw [hnorm]
  simpa [inner_smul_right, inner_self_eq_norm_sq_to_K, mul_add, mul_assoc] using hmul

private theorem oneExitProjection_mul_lowerPositiveStarFrame
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    oneExitProjection S X * lowerPositiveStarFrame hS a ha hd =
      lowerPositiveStarFrame hS a ha hd := by
  have hpositive :
      positiveStarProjection S X * lowerPositiveStarFrame hS a ha hd =
        lowerPositiveStarFrame hS a ha hd := by
    ext v b
    have hentry := congrArg
      (fun M ↦ M v (lowerArithmeticPositiveStarCenter hS a ha hd b))
      (positiveStarProjection_mul_frame S X)
    simpa [lowerPositiveStarFrame, Matrix.mul_apply] using hentry
  have hcyclic :
      oneExitCyclicProjection S X * lowerPositiveStarFrame hS a ha hd = 0 := by
    calc
      oneExitCyclicProjection S X * lowerPositiveStarFrame hS a ha hd =
          oneExitCyclicProjection S X *
            (positiveStarProjection S X * lowerPositiveStarFrame hS a ha hd) := by
              rw [hpositive]
      _ = (oneExitCyclicProjection S X * positiveStarProjection S X) *
            lowerPositiveStarFrame hS a ha hd := by rw [Matrix.mul_assoc]
      _ = 0 := by
        rw [oneExitCyclicProjection_mul_positiveStarProjection, Matrix.zero_mul]
  rw [oneExitProjection, Matrix.add_mul, hpositive, hcyclic, add_zero]

set_option maxHeartbeats 800000 in

private theorem oneExitEigenvalueAtArithmeticRank_ge_starEnergy_sub
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : PrimeStar.Vertex S X)
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    {beta : ℝ}
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta) :
    Real.sqrt (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) -
        beta ≤ oneExitEigenvalueAtArithmeticRank a := by
  let Qm := lowerPositiveStarFrame hS a ha hd
  let Q := Matrix.toEuclideanLin Qm
  let G := Matrix.toEuclideanLin (oneExitCompression S X)
  let i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ (PrimeStar.Vertex S X))) :=
    Fin.cast finrank_euclideanSpace.symm (oneExitArithmeticRankIndex a)
  let W : Submodule ℂ (EuclideanSpace ℂ (PrimeStar.Vertex S X)) :=
    LinearMap.range Q
  have hQinj : Function.Injective Q := by
    exact lowerPositiveStarFrame_toEuclideanLin_injective hS a ha hd
  have hWrank : i.1 + 1 ≤ Module.finrank ℂ W := by
    rw [LinearMap.finrank_range_of_inj hQinj]
    change (oneExitArithmeticRankIndex a).1 + 1 ≤
      Module.finrank ℂ (EuclideanSpace ℂ (↑(lowerArithmeticCenters a)))
    rw [finrank_euclideanSpace, Fintype.card_coe,
      card_lowerArithmeticCenters]
  have hWquad : ∀ y ∈ W,
      (Real.sqrt
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) - beta) *
          ‖y‖ ^ 2 ≤
        RCLike.re (inner ℂ y (G y)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    have hprojMatrix := congrArg Matrix.toEuclideanLin
      (oneExitProjection_mul_lowerPositiveStarFrame hS a ha hd)
    rw [Matrix.toLpLin_mul_same] at hprojMatrix
    have hproj : Matrix.toEuclideanLin (oneExitProjection S X) (Q x) = Q x := by
      simpa [Q, Qm] using LinearMap.congr_fun hprojMatrix x
    have hlargeMatrix := congrArg Matrix.toEuclideanLin
      (oneExitLargePrimeMatrix_mul_lowerPositiveStarFrame hS a ha hd)
    rw [Matrix.toLpLin_mul_same] at hlargeMatrix
    have hlarge :
        Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) (Q x) =
          Q (Matrix.toEuclideanLin (lowerPositiveStarEnergyMatrix a) x) := by
      simpa [Q, Qm, LinearMap.comp_apply] using
        LinearMap.congr_fun hlargeMatrix x
    have hnorm : ‖Q x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ),
        ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact congrArg RCLike.re
        (lowerPositiveStarFrame_inner_map_map hS a ha hd x x)
    have hlargeLower :
        Real.sqrt
            (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) *
            ‖Q x‖ ^ 2 ≤
          RCLike.re (inner ℂ (Q x)
            (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) (Q x))) := by
      rw [hlarge, hnorm]
      rw [lowerPositiveStarFrame_inner_map_map]
      exact lowerPositiveStarEnergy_quadratic_ge_terminal hS a ha x
    have hsmallNorm :
        ‖Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) (Q x)‖ ≤
          beta * ‖Q x‖ := by
      exact (norm_matrixToEuclideanLin_apply_le
        (oneExitSmallPrimeMatrix S X) (Q x)).trans
          (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))
    have hsmallAbs :
        |RCLike.re (inner ℂ (Q x)
          (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) (Q x)))| ≤
            beta * ‖Q x‖ ^ 2 := by
      calc
        |RCLike.re (inner ℂ (Q x)
            (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) (Q x)))| ≤
            ‖Q x‖ *
              ‖Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) (Q x)‖ :=
          (RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
        _ ≤ ‖Q x‖ * (beta * ‖Q x‖) :=
          mul_le_mul_of_nonneg_left hsmallNorm (norm_nonneg _)
        _ = beta * ‖Q x‖ ^ 2 := by ring
    have hsmallLower :
        -beta * ‖Q x‖ ^ 2 ≤
          RCLike.re (inner ℂ (Q x)
            (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) (Q x))) := by
      simpa [neg_mul] using neg_le_of_abs_le hsmallAbs
    rw [oneExitCompression_quadraticForm_eq, hproj]
    rw [moleculeFamilyComplexAdjacency_eq_large_add_small]
    simp only [LinearMap.add_apply, inner_add_right, map_add]
    nlinarith
  have hroot := rclike_le_eigenvalue_of_large_subspace G
    (oneExitCompression_isSymmetric S X) i
    (Real.sqrt
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) - beta)
    W hWrank hWquad
  have hcast : (oneExitCompression_isSymmetric S X).eigenvalues rfl i =
      oneExitEigenvalueAtArithmeticRank a := by
    calc
      (oneExitCompression_isSymmetric S X).eigenvalues rfl i =
          (oneExitCompression_isSymmetric S X).eigenvalues
            finrank_euclideanSpace (oneExitArithmeticRankIndex a) := by
              exact symmetricEigenvalues_cast
                (Matrix.toEuclideanLin (oneExitCompression S X))
                (oneExitCompression_isSymmetric S X)
                finrank_euclideanSpace (oneExitArithmeticRankIndex a)
      _ = oneExitEigenvalueAtArithmeticRank a := by rfl
  rw [hcast] at hroot
  exact hroot

private theorem complexifyRealMatrix_apply_complexifyEuclidean
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin (complexifyRealMatrix A)
        (PrimeStar.complexifyEuclidean x) =
      PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin A x) := by
  apply PiLp.ext
  intro i
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    complexifyRealMatrix_apply, PrimeStar.complexifyEuclidean_apply]
  push_cast
  rfl

theorem oneExitSmallPrimeMatrix_l2OperatorNorm_le_two_mul_real
    (S : Finset ℕ) (X : ℕ) {eta : ℝ} (heta : 0 ≤ eta)
    (hreal :
      ‖(PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ‖ ≤ eta) :
    matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ 2 * eta := by
  let HC := Matrix.toEuclideanCLM
    (n := PrimeStar.Vertex S X) (𝕜 := ℂ)
    (oneExitSmallPrimeMatrix S X)
  let HR :=
    (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ
  have hHC : oneExitSmallPrimeMatrix S X = complexifyRealMatrix HR := by
    ext i j
    simp only [oneExitSmallPrimeMatrix, HR, complexifyRealMatrix_apply,
      SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have happly : ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
      ‖HC x‖ ≤ (2 * eta) * ‖x‖ := by
    intro x
    let xr := complexEuclideanRealPart x
    let xi := complexEuclideanImagPart x
    have hre :
        ‖Matrix.toEuclideanLin HR xr‖ ≤ eta * ‖xr‖ := by
      calc
        ‖Matrix.toEuclideanLin HR xr‖ ≤ ‖HR‖ * ‖xr‖ := by
          change ‖WithLp.toLp 2 (HR.mulVec xr.ofLp)‖ ≤ ‖HR‖ * ‖xr‖
          exact HR.l2_opNorm_mulVec xr
        _ ≤ eta * ‖xr‖ :=
          mul_le_mul_of_nonneg_right hreal (norm_nonneg xr)
    have him :
        ‖Matrix.toEuclideanLin HR xi‖ ≤ eta * ‖xi‖ := by
      calc
        ‖Matrix.toEuclideanLin HR xi‖ ≤ ‖HR‖ * ‖xi‖ := by
          change ‖WithLp.toLp 2 (HR.mulVec xi.ofLp)‖ ≤ ‖HR‖ * ‖xi‖
          exact HR.l2_opNorm_mulVec xi
        _ ≤ eta * ‖xi‖ :=
          mul_le_mul_of_nonneg_right hreal (norm_nonneg xi)
    have hsplit :
        HC x =
          PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin HR xr) +
            Complex.I •
              PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin HR xi) := by
      rw [← complexify_realPart_add_I_imagPart x]
      change Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
          (PrimeStar.complexifyEuclidean xr +
            Complex.I • PrimeStar.complexifyEuclidean xi) = _
      rw [hHC, map_add, map_smul,
        complexifyRealMatrix_apply_complexifyEuclidean HR xr,
        complexifyRealMatrix_apply_complexifyEuclidean HR xi]
    calc
      ‖HC x‖ ≤
          ‖PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin HR xr)‖ +
            ‖Complex.I •
              PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin HR xi)‖ := by
        rw [hsplit]
        exact norm_add_le _ _
      _ = ‖Matrix.toEuclideanLin HR xr‖ +
          ‖Matrix.toEuclideanLin HR xi‖ := by
        rw [norm_smul, Complex.norm_I, one_mul,
          PrimeStar.norm_complexifyEuclidean,
          PrimeStar.norm_complexifyEuclidean]
      _ ≤ eta * ‖xr‖ + eta * ‖xi‖ := add_le_add hre him
      _ ≤ eta * ‖x‖ + eta * ‖x‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (norm_complexEuclideanRealPart_le x) heta)
          (mul_le_mul_of_nonneg_left (norm_complexEuclideanImagPart_le x) heta)
      _ = (2 * eta) * ‖x‖ := by ring
  change ‖oneExitSmallPrimeMatrix S X‖ ≤ 2 * eta
  rw [Matrix.l2_opNorm_def]
  exact HC.opNorm_le_bound (mul_nonneg (by norm_num) heta) happly

private theorem norm_starProjectionToEuclideanLin_apply_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : IsStarProjection P)
    (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin P x‖ ≤ ‖x‖ := by
  have hnorm : matrixL2OperatorNorm P ≤ 1 := by
    simpa only [matrixL2OperatorNorm] using IsStarProjection.norm_le P hP
  exact (norm_matrixToEuclideanLin_apply_le P x).trans <| by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)

theorem oneExit_threeBlock_norm_sq
    (S : Finset ℕ) (X : ℕ)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    ‖x‖ ^ 2 =
      ‖Matrix.toEuclideanLin (positiveStarProjection S X) x‖ ^ 2 +
      ‖Matrix.toEuclideanLin (oneExitCyclicProjection S X) x‖ ^ 2 +
      ‖Matrix.toEuclideanLin (oneExitComplementProjection S X) x‖ ^ 2 := by
  let P := Matrix.toEuclideanLin (positiveStarProjection S X)
  let E := Matrix.toEuclideanLin (oneExitCyclicProjection S X)
  let F := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  have hP : P.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((positiveStarProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have hE : E.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((oneExitCyclicProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have hPE : inner ℂ (P x) (E x) = 0 := by
    rw [hP x (E x)]
    have hzero : P (E x) = 0 := by
      have hlin := congrArg Matrix.toEuclideanLin
        (positiveStarProjection_mul_cyclicProjection S X)
      rw [Matrix.toLpLin_mul_same] at hlin
      simpa [P, E] using LinearMap.congr_fun hlin x
    rw [hzero, inner_zero_right]
  have hPF : inner ℂ (P x) (F x) = 0 := by
    rw [hP x (F x)]
    have hzero : P (F x) = 0 := by
      have hlin := congrArg Matrix.toEuclideanLin
        (positiveStarProjection_mul_oneExitComplementProjection S X)
      rw [Matrix.toLpLin_mul_same] at hlin
      simpa [P, F] using LinearMap.congr_fun hlin x
    rw [hzero, inner_zero_right]
  have hEF : inner ℂ (E x) (F x) = 0 := by
    rw [hE x (F x)]
    have hzero : E (F x) = 0 := by
      have hlin := congrArg Matrix.toEuclideanLin
        (oneExitCyclicProjection_mul_oneExitComplementProjection S X)
      rw [Matrix.toLpLin_mul_same] at hlin
      simpa [E, F] using LinearMap.congr_fun hlin x
    rw [hzero, inner_zero_right]
  have hsum : P x + E x + F x = x := by
    have hmatrix :
        positiveStarProjection S X + oneExitCyclicProjection S X +
            oneExitComplementProjection S X = 1 := by
      rw [oneExitComplementProjection, oneExitProjection]
      abel
    have hlin := congrArg Matrix.toEuclideanLin hmatrix
    simpa [P, E, F] using LinearMap.congr_fun hlin x
  have hsumF : inner ℂ (P x + E x) (F x) = 0 := by
    rw [inner_add_left, hPF, hEF, add_zero]
  have hPE_norm : ‖P x + E x‖ ^ 2 = ‖P x‖ ^ 2 + ‖E x‖ ^ 2 := by
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (E x) hPE
  have hsumF_norm :
      ‖P x + E x + F x‖ ^ 2 = ‖P x + E x‖ ^ 2 + ‖F x‖ ^ 2 := by
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (P x + E x) (F x) hsumF
  calc
    ‖x‖ ^ 2 = ‖P x + E x + F x‖ ^ 2 := by rw [hsum]
    _ = ‖P x + E x‖ ^ 2 + ‖F x‖ ^ 2 := hsumF_norm
    _ = ‖P x‖ ^ 2 + ‖E x‖ ^ 2 + ‖F x‖ ^ 2 := by rw [hPE_norm]

private theorem oneExit_threeBlock_quadraticForm
    (S : Finset ℕ) (X : ℕ)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    let A := Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
    let P := Matrix.toEuclideanLin (positiveStarProjection S X)
    let E := Matrix.toEuclideanLin (oneExitCyclicProjection S X)
    let F := Matrix.toEuclideanLin (oneExitComplementProjection S X)
    let T := Matrix.toEuclideanLin
      (positiveStarProjection S X * moleculeFamilyComplexAdjacency S X *
        positiveStarProjection S X)
    let D := Matrix.toEuclideanLin
      (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
        oneExitCyclicProjection S X)
    let C := Matrix.toEuclideanLin
      (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
        oneExitComplementProjection S X)
    let K := Matrix.toEuclideanLin
      (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
        positiveStarProjection S X)
    let R := Matrix.toEuclideanLin
      (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
        oneExitCyclicProjection S X)
    RCLike.re (inner ℂ x (A x)) =
      RCLike.re (inner ℂ (P x) (T (P x))) +
        2 * RCLike.re (inner ℂ (K (P x)) (E x)) +
        RCLike.re (inner ℂ (E x) (D (E x))) +
        2 * RCLike.re (inner ℂ (R (E x)) (F x)) +
        RCLike.re (inner ℂ (F x) (C (F x))) := by
  dsimp only
  let A := Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
  let P := Matrix.toEuclideanLin (positiveStarProjection S X)
  let E := Matrix.toEuclideanLin (oneExitCyclicProjection S X)
  let F := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  let T := Matrix.toEuclideanLin
    (positiveStarProjection S X * moleculeFamilyComplexAdjacency S X *
      positiveStarProjection S X)
  let D := Matrix.toEuclideanLin
    (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitCyclicProjection S X)
  let C := Matrix.toEuclideanLin
    (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitComplementProjection S X)
  let K := Matrix.toEuclideanLin
    (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
      positiveStarProjection S X)
  let R := Matrix.toEuclideanLin
    (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitCyclicProjection S X)
  have hA : A.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (moleculeFamilyComplexAdjacency_isHermitian S X)
  have hP : P.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((positiveStarProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have hE : E.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((oneExitCyclicProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have hF : F.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((oneExitComplementProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have hPid : P (P x) = P x := by
    have hlin := congrArg Matrix.toEuclideanLin
      (positiveStarProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    exact LinearMap.congr_fun hlin x
  have hEid : E (E x) = E x := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitCyclicProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    exact LinearMap.congr_fun hlin x
  have hFid : F (F x) = F x := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitComplementProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    exact LinearMap.congr_fun hlin x
  have hsum : P x + E x + F x = x := by
    have hmatrix :
        positiveStarProjection S X + oneExitCyclicProjection S X +
            oneExitComplementProjection S X = 1 := by
      rw [oneExitComplementProjection, oneExitProjection]
      abel
    have hlin := congrArg Matrix.toEuclideanLin hmatrix
    simpa [P, E, F] using LinearMap.congr_fun hlin x
  have hT : T (P x) = P (A (P x)) := by
    simp only [T, P, A, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    rw [hPid]
  have hD : D (E x) = E (A (E x)) := by
    simp only [D, E, A, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    rw [hEid]
  have hC : C (F x) = F (A (F x)) := by
    simp only [C, F, A, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    rw [hFid]
  have hK : K (P x) = E (A (P x)) := by
    simp only [K, E, P, A, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    rw [hPid]
  have hR : R (E x) = F (A (E x)) := by
    simp only [R, F, E, A, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    rw [hEid]
  have hPP : RCLike.re (inner ℂ (P x) (T (P x))) =
      RCLike.re (inner ℂ (P x) (A (P x))) := by
    rw [hT, ← hP (P x) (A (P x)), hPid]
  have hEE : RCLike.re (inner ℂ (E x) (D (E x))) =
      RCLike.re (inner ℂ (E x) (A (E x))) := by
    rw [hD, ← hE (E x) (A (E x)), hEid]
  have hFF : RCLike.re (inner ℂ (F x) (C (F x))) =
      RCLike.re (inner ℂ (F x) (A (F x))) := by
    rw [hC, ← hF (F x) (A (F x)), hFid]
  have hPE : RCLike.re (inner ℂ (K (P x)) (E x)) =
      RCLike.re (inner ℂ (P x) (A (E x))) := by
    rw [hK, hE (A (P x)) (E x), hEid, hA (P x) (E x)]
  have hEF : RCLike.re (inner ℂ (R (E x)) (F x)) =
      RCLike.re (inner ℂ (E x) (A (F x))) := by
    rw [hR, hF (A (E x)) (F x), hFid, hA (E x) (F x)]
  have hPF : RCLike.re (inner ℂ (P x) (A (F x))) = 0 := by
    have hzero : F (A (P x)) = 0 := by
      have hlin := congrArg Matrix.toEuclideanLin
        (oneExitComplement_mul_adjacency_mul_positiveStar_eq_zero S X)
      rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same] at hlin
      have happ := LinearMap.congr_fun hlin x
      simpa [F, A, P, hPid] using happ
    rw [← hA (P x) (F x), ← hF (A (P x)) x, hzero,
      inner_zero_left, map_zero]
  calc
    RCLike.re (inner ℂ x (A x)) =
        RCLike.re (inner ℂ (P x + E x + F x)
          (A (P x + E x + F x))) := by rw [hsum]
    _ = RCLike.re (inner ℂ (P x) (T (P x))) +
          2 * RCLike.re (inner ℂ (K (P x)) (E x)) +
          RCLike.re (inner ℂ (E x) (D (E x))) +
          2 * RCLike.re (inner ℂ (R (E x)) (F x)) +
          RCLike.re (inner ℂ (F x) (C (F x))) := by
      simp only [map_add, inner_add_left, inner_add_right, map_add]
      rw [hPP, hEE, hFF, hPE, hEF, hPF]
      rw [← hA (E x) (P x), inner_re_symm (A (E x)) (P x)]
      rw [← hA (F x) (E x), inner_re_symm (A (F x)) (E x)]
      rw [← hA (F x) (P x), inner_re_symm (A (F x)) (P x), hPF]
      ring

private theorem oneExitCyclicBlock_isSymmetric
    (S : Finset ℕ) (X : ℕ) :
    (Matrix.toEuclideanLin
      (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
        oneExitCyclicProjection S X)).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  have hAdj := moleculeFamilyComplexAdjacency_isHermitian S X
  have hProj :=
    (oneExitCyclicProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  simpa [hProj.eq] using
    Matrix.isHermitian_conjTranspose_mul_mul
      (oneExitCyclicProjection S X) hAdj

private theorem norm_oneExitSmallPrime_apply_le
    (S : Finset ℕ) (X : ℕ) {beta : ℝ}
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta)
    (y : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    ‖Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) y‖ ≤ beta * ‖y‖ := by
  exact (norm_matrixToEuclideanLin_apply_le
    (oneExitSmallPrimeMatrix S X) y).trans <| by
      exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg y)

private theorem oneExitCyclicBlock_quadraticForm_le
    (S : Finset ℕ) (X : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta)
    (y : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    RCLike.re (inner ℂ y
      (Matrix.toEuclideanLin
        (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
          oneExitCyclicProjection S X) y)) ≤ beta * ‖y‖ ^ 2 := by
  let A := Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let H := Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
  let E := Matrix.toEuclideanLin (oneExitCyclicProjection S X)
  let D := Matrix.toEuclideanLin
    (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitCyclicProjection S X)
  have hEsymm : E.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((oneExitCyclicProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have hEid : E (E y) = E y := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitCyclicProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    exact LinearMap.congr_fun hlin y
  have hQEy :
      Matrix.toEuclideanLin (positiveStarComplementProjection S X) (E y) = E y := by
    have hlin := congrArg Matrix.toEuclideanLin
      (positiveStarComplement_mul_oneExitCyclicProjection S X)
    rw [Matrix.toLpLin_mul_same] at hlin
    exact LinearMap.congr_fun hlin y
  have hDapply : D y = E (A (E y)) := by
    simp only [D, E, A, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  have hAsplit : A (E y) = L (E y) + H (E y) := by
    have hlin := congrArg Matrix.toEuclideanLin
      (moleculeFamilyComplexAdjacency_eq_large_add_small S X)
    simpa [A, L, H] using LinearMap.congr_fun hlin (E y)
  have hlarge : RCLike.re (inner ℂ (E y) (L (E y))) ≤ 0 := by
    have hcore := re_inner_oneExitCoreMatrix_apply_nonpos S X (E y)
    have hcoreEq := oneExitCoreMatrix_apply_eq_largePrime_of_complement_fixed hQEy
    simpa [L, hcoreEq] using hcore
  have hsmallQuad :
      RCLike.re (inner ℂ (E y) (H (E y))) ≤ beta * ‖E y‖ ^ 2 := by
    calc
      RCLike.re (inner ℂ (E y) (H (E y))) ≤ ‖E y‖ * ‖H (E y)‖ :=
        re_inner_le_norm _ _
      _ ≤ ‖E y‖ * (beta * ‖E y‖) := by
        gcongr
        exact norm_oneExitSmallPrime_apply_le S X hsmall (E y)
      _ = beta * ‖E y‖ ^ 2 := by ring
  have hEnorm : ‖E y‖ ≤ ‖y‖ :=
    norm_starProjectionToEuclideanLin_apply_le _
      (oneExitCyclicProjection_isStarProjection S X) y
  have hEsq : ‖E y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hEnorm
  calc
    RCLike.re (inner ℂ y (D y)) =
        RCLike.re (inner ℂ (E y) (A (E y))) := by
          rw [hDapply]
          exact congrArg RCLike.re (hEsymm y (A (E y))).symm
    _ = RCLike.re (inner ℂ (E y) (L (E y))) +
        RCLike.re (inner ℂ (E y) (H (E y))) := by
          rw [hAsplit, inner_add_right, map_add]
    _ ≤ beta * ‖E y‖ ^ 2 := by linarith
    _ ≤ beta * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_left hEsq hbeta

private theorem oneExitComplementBlock_quadraticForm_le
    (S : Finset ℕ) (X : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta)
    (y : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    RCLike.re (inner ℂ y
      (Matrix.toEuclideanLin
        (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
          oneExitComplementProjection S X) y)) ≤ beta * ‖y‖ ^ 2 := by
  let A := Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let H := Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
  let F := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  let C := Matrix.toEuclideanLin
    (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitComplementProjection S X)
  have hFsymm : F.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((oneExitComplementProjection_isStarProjection S X).isSelfAdjoint.isHermitian)
  have hFid : F (F y) = F y := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitComplementProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    exact LinearMap.congr_fun hlin y
  have hQFy :
      Matrix.toEuclideanLin (positiveStarComplementProjection S X) (F y) = F y := by
    have hPF : positiveStarProjection S X * oneExitComplementProjection S X = 0 :=
      positiveStarProjection_mul_oneExitComplementProjection S X
    have hmatrix :
        positiveStarComplementProjection S X * oneExitComplementProjection S X =
          oneExitComplementProjection S X := by
      rw [positiveStarComplementProjection, Matrix.sub_mul, Matrix.one_mul,
        hPF, sub_zero]
    have hlin := congrArg Matrix.toEuclideanLin hmatrix
    rw [Matrix.toLpLin_mul_same] at hlin
    exact LinearMap.congr_fun hlin y
  have hCapply : C y = F (A (F y)) := by
    simp only [C, F, A, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  have hAsplit : A (F y) = L (F y) + H (F y) := by
    have hlin := congrArg Matrix.toEuclideanLin
      (moleculeFamilyComplexAdjacency_eq_large_add_small S X)
    simpa [A, L, H] using LinearMap.congr_fun hlin (F y)
  have hlarge : RCLike.re (inner ℂ (F y) (L (F y))) ≤ 0 := by
    have hcore := re_inner_oneExitCoreMatrix_apply_nonpos S X (F y)
    have hcoreEq := oneExitCoreMatrix_apply_eq_largePrime_of_complement_fixed hQFy
    simpa [L, hcoreEq] using hcore
  have hsmallQuad :
      RCLike.re (inner ℂ (F y) (H (F y))) ≤ beta * ‖F y‖ ^ 2 := by
    calc
      RCLike.re (inner ℂ (F y) (H (F y))) ≤ ‖F y‖ * ‖H (F y)‖ :=
        re_inner_le_norm _ _
      _ ≤ ‖F y‖ * (beta * ‖F y‖) := by
        gcongr
        exact norm_oneExitSmallPrime_apply_le S X hsmall (F y)
      _ = beta * ‖F y‖ ^ 2 := by ring
  have hFnorm : ‖F y‖ ≤ ‖y‖ :=
    norm_starProjectionToEuclideanLin_apply_le _
      (oneExitComplementProjection_isStarProjection S X) y
  have hFsq : ‖F y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hFnorm
  calc
    RCLike.re (inner ℂ y (C y)) =
        RCLike.re (inner ℂ (F y) (A (F y))) := by
          rw [hCapply]
          exact congrArg RCLike.re (hFsymm y (A (F y))).symm
    _ = RCLike.re (inner ℂ (F y) (L (F y))) +
        RCLike.re (inner ℂ (F y) (H (F y))) := by
          rw [hAsplit, inner_add_right, map_add]
    _ ≤ beta * ‖F y‖ ^ 2 := by linarith
    _ ≤ beta * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_left hFsq hbeta

private theorem oneExitPositiveCyclicBlock_norm_sq_le
    (S : Finset ℕ) (X : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta)
    (y : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    ‖Matrix.toEuclideanLin
      (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
        positiveStarProjection S X) y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2 := by
  let H := Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
  let P := Matrix.toEuclideanLin (positiveStarProjection S X)
  let E := Matrix.toEuclideanLin (oneExitCyclicProjection S X)
  let K := Matrix.toEuclideanLin
    (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
      positiveStarProjection S X)
  have hKsmall : K y = E (H (P y)) := by
    have hELP : oneExitCyclicProjection S X * oneExitLargePrimeMatrix S X *
        positiveStarProjection S X = 0 := by
      calc
        oneExitCyclicProjection S X * oneExitLargePrimeMatrix S X *
              positiveStarProjection S X =
            oneExitCyclicProjection S X *
              (oneExitLargePrimeMatrix S X * positiveStarProjection S X) := by
                rw [Matrix.mul_assoc]
        _ = oneExitCyclicProjection S X *
              (positiveStarProjection S X * oneExitLargePrimeMatrix S X) := by
                rw [← (positiveStarProjection_commutes_oneExitLargePrimeMatrix
                  S X).eq]
        _ = (oneExitCyclicProjection S X * positiveStarProjection S X) *
              oneExitLargePrimeMatrix S X := by rw [Matrix.mul_assoc]
        _ = 0 := by
          rw [oneExitCyclicProjection_mul_positiveStarProjection,
            Matrix.zero_mul]
    have hmatrix :
        oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
            positiveStarProjection S X =
          oneExitCyclicProjection S X * oneExitSmallPrimeMatrix S X *
            positiveStarProjection S X := by
      rw [moleculeFamilyComplexAdjacency_eq_large_add_small,
        Matrix.mul_add, Matrix.add_mul, hELP, zero_add]
    have hlin := congrArg Matrix.toEuclideanLin hmatrix
    simpa [K, E, H, P, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply] using LinearMap.congr_fun hlin y
  have hKn : ‖K y‖ ≤ beta * ‖y‖ := by
    calc
      ‖K y‖ = ‖E (H (P y))‖ := by rw [hKsmall]
      _ ≤ ‖H (P y)‖ := norm_starProjectionToEuclideanLin_apply_le _
        (oneExitCyclicProjection_isStarProjection S X) _
      _ ≤ beta * ‖P y‖ := norm_oneExitSmallPrime_apply_le S X hsmall _
      _ ≤ beta * ‖y‖ := mul_le_mul_of_nonneg_left
        (norm_starProjectionToEuclideanLin_apply_le _
          (positiveStarProjection_isStarProjection S X) y) hbeta
  have hnonneg : 0 ≤ beta * ‖y‖ := mul_nonneg hbeta (norm_nonneg y)
  simpa [K, mul_pow] using
    (sq_le_sq₀ (norm_nonneg (K y)) hnonneg).2 hKn

private theorem oneExitCyclicComplementBlock_norm_sq_le
    (S : Finset ℕ) (X : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta)
    (y : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    ‖Matrix.toEuclideanLin
      (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
        oneExitCyclicProjection S X) y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2 := by
  let H := Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
  let E := Matrix.toEuclideanLin (oneExitCyclicProjection S X)
  let F := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  let R := Matrix.toEuclideanLin
    (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitCyclicProjection S X)
  have hRsmall : R y = F (H (E y)) := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitComplement_mul_adjacency_mul_cyclic_eq_smallPrime S X)
    simpa [R, F, H, E, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply] using LinearMap.congr_fun hlin y
  have hRn : ‖R y‖ ≤ beta * ‖y‖ := by
    calc
      ‖R y‖ = ‖F (H (E y))‖ := by rw [hRsmall]
      _ ≤ ‖H (E y)‖ := norm_starProjectionToEuclideanLin_apply_le _
        (oneExitComplementProjection_isStarProjection S X) _
      _ ≤ beta * ‖E y‖ := norm_oneExitSmallPrime_apply_le S X hsmall _
      _ ≤ beta * ‖y‖ := mul_le_mul_of_nonneg_left
        (norm_starProjectionToEuclideanLin_apply_le _
          (oneExitCyclicProjection_isStarProjection S X) y) hbeta
  have hnonneg : 0 ≤ beta * ‖y‖ := mul_nonneg hbeta (norm_nonneg y)
  simpa [R, mul_pow] using
    (sq_le_sq₀ (norm_nonneg (R y)) hnonneg).2 hRn

private abbrev OneExitAmbient (S : Finset ℕ) (X : ℕ) :=
  EuclideanSpace ℂ (PrimeStar.Vertex S X)

private noncomputable def fullComplexAdjacencyLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)

private noncomputable def oneExitCompressionLin (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin (oneExitCompression S X)

private noncomputable def oneExitPositiveProjectionLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin (positiveStarProjection S X)

private noncomputable def oneExitCyclicProjectionLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin (oneExitCyclicProjection S X)

private noncomputable def oneExitDiscardedProjectionLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin (oneExitComplementProjection S X)

private noncomputable def oneExitProjectionLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin (oneExitProjection S X)

private noncomputable def oneExitPositiveBlockLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin
    (positiveStarProjection S X * moleculeFamilyComplexAdjacency S X *
      positiveStarProjection S X)

private noncomputable def oneExitCyclicBlockLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin
    (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitCyclicProjection S X)

private noncomputable def oneExitPositiveCyclicBlockLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin
    (oneExitCyclicProjection S X * moleculeFamilyComplexAdjacency S X *
      positiveStarProjection S X)

private noncomputable def oneExitDiscardedBlockLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin
    (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitComplementProjection S X)

private noncomputable def oneExitCyclicDiscardedBlockLin
    (S : Finset ℕ) (X : ℕ) :
    OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X :=
  Matrix.toEuclideanLin
    (oneExitComplementProjection S X * moleculeFamilyComplexAdjacency S X *
      oneExitCyclicProjection S X)

private theorem fullComplexAdjacencyLin_isSymmetric
    (S : Finset ℕ) (X : ℕ) :
    (fullComplexAdjacencyLin S X).IsSymmetric := by
  simpa [fullComplexAdjacencyLin] using
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (moleculeFamilyComplexAdjacency_isHermitian S X))

private theorem oneExitCompressionLin_isSymmetric
    (S : Finset ℕ) (X : ℕ) :
    (oneExitCompressionLin S X).IsSymmetric := by
  simpa [oneExitCompressionLin] using oneExitCompression_isSymmetric S X

private structure OneExitThreeBlockData
    (S : Finset ℕ) (X : ℕ) (beta : ℝ) where
  cyclic_symmetric : (oneExitCyclicBlockLin S X).IsSymmetric
  norm_decomposition : ∀ y : OneExitAmbient S X,
    ‖y‖ ^ 2 =
      ‖oneExitPositiveProjectionLin S X y‖ ^ 2 +
      ‖oneExitCyclicProjectionLin S X y‖ ^ 2 +
      ‖oneExitDiscardedProjectionLin S X y‖ ^ 2
  form_decomposition : ∀ y : OneExitAmbient S X,
    RCLike.re (inner ℂ y (fullComplexAdjacencyLin S X y)) =
      RCLike.re (inner ℂ
        (oneExitPositiveProjectionLin S X y)
        (oneExitPositiveBlockLin S X
          (oneExitPositiveProjectionLin S X y))) +
      2 * RCLike.re (inner ℂ
        (oneExitPositiveCyclicBlockLin S X
          (oneExitPositiveProjectionLin S X y))
        (oneExitCyclicProjectionLin S X y)) +
      RCLike.re (inner ℂ
        (oneExitCyclicProjectionLin S X y)
        (oneExitCyclicBlockLin S X
          (oneExitCyclicProjectionLin S X y))) +
      2 * RCLike.re (inner ℂ
        (oneExitCyclicDiscardedBlockLin S X
          (oneExitCyclicProjectionLin S X y))
        (oneExitDiscardedProjectionLin S X y)) +
      RCLike.re (inner ℂ
        (oneExitDiscardedProjectionLin S X y)
        (oneExitDiscardedBlockLin S X
          (oneExitDiscardedProjectionLin S X y)))
  cyclic_upper : ∀ y : OneExitAmbient S X,
    RCLike.re (inner ℂ y (oneExitCyclicBlockLin S X y)) ≤ beta * ‖y‖ ^ 2
  discarded_upper : ∀ y : OneExitAmbient S X,
    RCLike.re (inner ℂ y (oneExitDiscardedBlockLin S X y)) ≤ beta * ‖y‖ ^ 2
  positive_cyclic_sq : ∀ y : OneExitAmbient S X,
    ‖oneExitPositiveCyclicBlockLin S X y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2
  cyclic_discarded_sq : ∀ y : OneExitAmbient S X,
    ‖oneExitCyclicDiscardedBlockLin S X y‖ ^ 2 ≤ beta ^ 2 * ‖y‖ ^ 2

private theorem oneExit_threeBlock_data
    (S : Finset ℕ) (X : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta) :
    OneExitThreeBlockData S X beta := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [oneExitCyclicBlockLin] using oneExitCyclicBlock_isSymmetric S X
  · simpa [oneExitPositiveProjectionLin, oneExitCyclicProjectionLin,
      oneExitDiscardedProjectionLin] using oneExit_threeBlock_norm_sq S X
  · simpa [fullComplexAdjacencyLin, oneExitPositiveProjectionLin,
      oneExitCyclicProjectionLin, oneExitDiscardedProjectionLin,
      oneExitPositiveBlockLin, oneExitCyclicBlockLin,
      oneExitDiscardedBlockLin, oneExitPositiveCyclicBlockLin,
      oneExitCyclicDiscardedBlockLin] using
        oneExit_threeBlock_quadraticForm S X
  · exact oneExitCyclicBlock_quadraticForm_le S X hbeta hsmall
  · exact oneExitComplementBlock_quadraticForm_le S X hbeta hsmall
  · exact oneExitPositiveCyclicBlock_norm_sq_le S X hbeta hsmall
  · exact oneExitCyclicComplementBlock_norm_sq_le S X hbeta hsmall

set_option maxHeartbeats 800000 in

private theorem oneExit_oldBlock_reconstruction_data
    (S : Finset ℕ) (X : ℕ) {beta rho : ℝ}
    (hrho : 0 < rho) (hrhoBeta : beta < rho)
    (hD : ∀ y : OneExitAmbient S X,
      RCLike.re (inner ℂ y (oneExitCyclicBlockLin S X y)) ≤ beta * ‖y‖ ^ 2) :
    ∃ reconstruct : OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X,
      (∀ u,
        ‖reconstruct u‖ ^ 2 =
          ‖oneExitPositiveProjectionLin S X (reconstruct u)‖ ^ 2 +
            ‖oneExitCyclicProjectionLin S X (reconstruct u)‖ ^ 2) ∧
      (∀ u,
        RCLike.re (inner ℂ (reconstruct u)
          (oneExitCompressionLin S X (reconstruct u))) =
          RCLike.re (inner ℂ
            (oneExitPositiveProjectionLin S X (reconstruct u))
            (oneExitPositiveBlockLin S X
              (oneExitPositiveProjectionLin S X (reconstruct u)))) +
          2 * RCLike.re (inner ℂ
            (oneExitPositiveCyclicBlockLin S X
              (oneExitPositiveProjectionLin S X (reconstruct u)))
            (oneExitCyclicProjectionLin S X (reconstruct u))) +
          RCLike.re (inner ℂ
            (oneExitCyclicProjectionLin S X (reconstruct u))
            (oneExitCyclicBlockLin S X
              (oneExitCyclicProjectionLin S X (reconstruct u))))) ∧
      (∀ u, oneExitPositiveProjectionLin S X (reconstruct u) =
        oneExitPositiveProjectionLin S X u) ∧
      (let Rold := rclikeFiniteResolventOfGap
        (oneExitCyclicBlockLin S X) rho (rho - beta)
        (sub_pos.mpr hrhoBeta)
        (rclike_shifted_lowerBound_of_quadratic_upper
          (oneExitCyclicBlockLin S X) hD)
       ∀ u, oneExitCyclicProjectionLin S X (reconstruct u) =
        Rold (oneExitPositiveCyclicBlockLin S X
          (oneExitPositiveProjectionLin S X u))) := by
  let V := OneExitAmbient S X
  let A : V →ₗ[ℂ] V :=
    Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
  let G : V →ₗ[ℂ] V := oneExitCompressionLin S X
  let P : V →ₗ[ℂ] V := oneExitPositiveProjectionLin S X
  let E : V →ₗ[ℂ] V := oneExitCyclicProjectionLin S X
  let F : V →ₗ[ℂ] V := oneExitDiscardedProjectionLin S X
  let Q : V →ₗ[ℂ] V := Matrix.toEuclideanLin (oneExitProjection S X)
  let T : V →ₗ[ℂ] V := oneExitPositiveBlockLin S X
  let D : V →ₗ[ℂ] V := oneExitCyclicBlockLin S X
  let K : V →ₗ[ℂ] V := oneExitPositiveCyclicBlockLin S X
  let hD' : ∀ y : V,
      RCLike.re (inner ℂ y (D y)) ≤ beta * ‖y‖ ^ 2 := hD
  let Rold := rclikeFiniteResolventOfGap D rho (rho - beta)
    (sub_pos.mpr hrhoBeta)
    (rclike_shifted_lowerBound_of_quadratic_upper D hD')
  have hPid (y : V) : P (P y) = P y := by
    have hlin := congrArg Matrix.toEuclideanLin
      (positiveStarProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [P, oneExitPositiveProjectionLin] using LinearMap.congr_fun hlin y
  have hEid (y : V) : E (E y) = E y := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitCyclicProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [E, oneExitCyclicProjectionLin] using LinearMap.congr_fun hlin y
  have hPEzero (y : V) : P (E y) = 0 := by
    have hlin := congrArg Matrix.toEuclideanLin
      (positiveStarProjection_mul_cyclicProjection S X)
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [P, E, oneExitPositiveProjectionLin,
      oneExitCyclicProjectionLin] using LinearMap.congr_fun hlin y
  have hEPzero (y : V) : E (P y) = 0 := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitCyclicProjection_mul_positiveStarProjection S X)
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [E, P, oneExitPositiveProjectionLin,
      oneExitCyclicProjectionLin] using LinearMap.congr_fun hlin y
  have hFEzero (y : V) : F (E y) = 0 := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitComplementProjection_mul_oneExitCyclicProjection S X)
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [F, E, oneExitDiscardedProjectionLin,
      oneExitCyclicProjectionLin] using LinearMap.congr_fun hlin y
  have hFPzero (y : V) : F (P y) = 0 := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitComplementProjection_mul_positiveStarProjection S X)
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [F, P, oneExitDiscardedProjectionLin,
      oneExitPositiveProjectionLin] using LinearMap.congr_fun hlin y
  have hDapply (y : V) : D y = E (A (E y)) := by
    simp only [D, E, A, oneExitCyclicBlockLin,
      oneExitCyclicProjectionLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply]
  have hED (y : V) : E (D y) = D y := by rw [hDapply, hEid]
  have hEK (y : V) : E (K y) = K y := by
    have hlin := congrArg Matrix.toEuclideanLin
      (oneExitCyclicProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [K, E, A, P, oneExitPositiveCyclicBlockLin,
      oneExitCyclicProjectionLin, oneExitPositiveProjectionLin,
      Matrix.toLpLin_mul_same, LinearMap.comp_apply] using
        LinearMap.congr_fun hlin (A (P y))
  have hEr (u : V) : E (Rold (K (P u))) = Rold (K (P u)) := by
    let r := Rold (K (P u))
    have hr : (rho : ℂ) • r - D r = K (P u) := by
      exact rclikeFiniteResolventOfGap_apply_inverse
        D rho (rho - beta) (sub_pos.mpr hrhoBeta)
          (rclike_shifted_lowerBound_of_quadratic_upper D hD') (K (P u))
    have hErEq := congrArg E hr
    rw [map_sub, map_smul, hED, hEK] at hErEq
    have hsmul : (rho : ℂ) • E r = (rho : ℂ) • r :=
      sub_left_inj.mp (hErEq.trans hr.symm)
    have hscalar : (rho : ℂ) • (E r - r) = 0 := by
      rw [smul_sub, hsmul, sub_self]
    have hscalarNe : (rho : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrho.ne'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hscalar).resolve_left hscalarNe)
  let reconstruct : V →ₗ[ℂ] V := P + Rold.comp (K.comp P)
  have hreconstruct (u : V) :
      reconstruct u = P u + Rold (K (P u)) := by rfl
  have hPreconstruct (u : V) : P (reconstruct u) = P u := by
    rw [hreconstruct, map_add, hPid]
    have hPr : P (Rold (K (P u))) = 0 := by
      rw [← hEr u]
      exact hPEzero _
    rw [hPr, add_zero]
  have hEreconstruct (u : V) :
      E (reconstruct u) = Rold (K (P u)) := by
    rw [hreconstruct, map_add, hEPzero, hEr, zero_add]
  have hFreconstruct (u : V) : F (reconstruct u) = 0 := by
    rw [hreconstruct, map_add, hFPzero]
    have hFr : F (Rold (K (P u))) = 0 := by
      rw [← hEr u]
      exact hFEzero _
    rw [hFr, add_zero]
  have hQreconstruct (u : V) : Q (reconstruct u) = reconstruct u := by
    have hQPmatrix :
        oneExitProjection S X * positiveStarProjection S X =
          positiveStarProjection S X := by
      rw [oneExitProjection, Matrix.add_mul,
        (positiveStarProjection_isStarProjection S X).isIdempotentElem.eq,
        oneExitCyclicProjection_mul_positiveStarProjection, add_zero]
    have hQEmatrix :
        oneExitProjection S X * oneExitCyclicProjection S X =
          oneExitCyclicProjection S X := by
      rw [oneExitProjection, Matrix.add_mul,
        positiveStarProjection_mul_cyclicProjection,
        (oneExitCyclicProjection_isStarProjection S X).isIdempotentElem.eq,
        zero_add]
    have hQP (y : V) : Q (P y) = P y := by
      have hlin := congrArg Matrix.toEuclideanLin hQPmatrix
      rw [Matrix.toLpLin_mul_same] at hlin
      simpa [Q, P, oneExitPositiveProjectionLin] using LinearMap.congr_fun hlin y
    have hQE (y : V) : Q (E y) = E y := by
      have hlin := congrArg Matrix.toEuclideanLin hQEmatrix
      rw [Matrix.toLpLin_mul_same] at hlin
      simpa [Q, E, oneExitCyclicProjectionLin] using LinearMap.congr_fun hlin y
    have hQr : Q (Rold (K (P u))) = Rold (K (P u)) := by
      calc
        Q (Rold (K (P u))) = Q (E (Rold (K (P u)))) := by rw [hEr u]
        _ = E (Rold (K (P u))) := hQE _
        _ = Rold (K (P u)) := hEr u
    rw [hreconstruct, map_add, hQP, hQr]
  have hreconstructNorm (u : V) :
      ‖reconstruct u‖ ^ 2 =
        ‖P (reconstruct u)‖ ^ 2 + ‖E (reconstruct u)‖ ^ 2 := by
    have hthree := oneExit_threeBlock_norm_sq S X (reconstruct u)
    change ‖reconstruct u‖ ^ 2 =
      ‖P (reconstruct u)‖ ^ 2 + ‖E (reconstruct u)‖ ^ 2 +
        ‖F (reconstruct u)‖ ^ 2 at hthree
    rw [hFreconstruct u, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hthree
    exact hthree
  have hreconstructForm (u : V) :
      RCLike.re (inner ℂ (reconstruct u) (G (reconstruct u))) =
        RCLike.re (inner ℂ (P (reconstruct u))
          (T (P (reconstruct u)))) +
          2 * RCLike.re (inner ℂ (K (P (reconstruct u)))
            (E (reconstruct u))) +
          RCLike.re (inner ℂ (E (reconstruct u))
            (D (E (reconstruct u)))) := by
    let w := reconstruct u
    have hGquad : RCLike.re (inner ℂ w (G w)) =
        RCLike.re (inner ℂ w (A w)) := by
      have hcompression := oneExitCompression_quadraticForm_eq S X w
      change RCLike.re (inner ℂ w (G w)) =
        RCLike.re (inner ℂ (Q w) (A (Q w))) at hcompression
      have hQw : Q w = w := by
        dsimp only [w]
        exact hQreconstruct u
      rw [hQw] at hcompression
      exact hcompression
    have hthree := oneExit_threeBlock_quadraticForm S X w
    change RCLike.re (inner ℂ w (A w)) =
      RCLike.re (inner ℂ (P w) (T (P w))) +
        2 * RCLike.re (inner ℂ (K (P w)) (E w)) +
        RCLike.re (inner ℂ (E w) (D (E w))) +
        2 * RCLike.re (inner ℂ
          (Matrix.toEuclideanLin
            (oneExitComplementProjection S X *
              moleculeFamilyComplexAdjacency S X *
              oneExitCyclicProjection S X) (E w)) (F w)) +
        RCLike.re (inner ℂ (F w)
          (Matrix.toEuclideanLin
            (oneExitComplementProjection S X *
              moleculeFamilyComplexAdjacency S X *
              oneExitComplementProjection S X) (F w))) at hthree
    have hFw : F w = 0 := by
      dsimp only [w]
      exact hFreconstruct u
    rw [hFw, map_zero, inner_zero_right, inner_zero_left] at hthree
    exact hGquad.trans (by simpa using hthree)
  refine ⟨reconstruct, ?_, ?_, ?_, ?_⟩
  · simpa [V, P, E, oneExitPositiveProjectionLin,
      oneExitCyclicProjectionLin] using hreconstructNorm
  · simpa [V, G, P, E, T, D, K, oneExitCompressionLin,
      oneExitPositiveProjectionLin, oneExitCyclicProjectionLin,
      oneExitPositiveBlockLin, oneExitCyclicBlockLin,
      oneExitPositiveCyclicBlockLin] using hreconstructForm
  · simpa [V, P, oneExitPositiveProjectionLin] using hPreconstruct
  · dsimp only
    intro u
    change E (reconstruct u) = Rold (K (P u))
    exact hEreconstruct u

set_option maxHeartbeats 400000 in

private theorem oneExit_oldBlock_reconstruction
    (S : Finset ℕ) (X : ℕ) {beta rho : ℝ}
    (hrho : 0 < rho) (hrhoBeta : beta < rho)
    (hD : ∀ y : OneExitAmbient S X,
      RCLike.re (inner ℂ y (oneExitCyclicBlockLin S X y)) ≤ beta * ‖y‖ ^ 2) :
    ∃ reconstruct : OneExitAmbient S X →ₗ[ℂ] OneExitAmbient S X,
      let Rold := rclikeFiniteResolventOfGap
        (oneExitCyclicBlockLin S X) rho (rho - beta)
        (sub_pos.mpr hrhoBeta)
        (rclike_shifted_lowerBound_of_quadratic_upper
          (oneExitCyclicBlockLin S X) hD)
      ∀ x : OneExitAmbient S X,
        rclikeSchurReducedForm
            (oneExitPositiveBlockLin S X)
            (oneExitPositiveCyclicBlockLin S X) Rold rho
            (oneExitPositiveProjectionLin S X x) =
          RCLike.re (inner ℂ (reconstruct (oneExitPositiveProjectionLin S X x))
            (oneExitCompressionLin S X
              (reconstruct (oneExitPositiveProjectionLin S X x)))) -
            rho * ‖reconstruct (oneExitPositiveProjectionLin S X x)‖ ^ 2 := by
  rcases oneExit_oldBlock_reconstruction_data S X hrho hrhoBeta hD with
    ⟨reconstruct, hnorm, hform, hp, he⟩
  refine ⟨reconstruct, ?_⟩
  have hbase := rclike_twoBlock_reducedForm_eq_reconstruction
    (oneExitCompressionLin S X) (oneExitPositiveBlockLin S X)
    (oneExitCyclicBlockLin S X) (oneExitPositiveCyclicBlockLin S X)
    (oneExitPositiveProjectionLin S X) (oneExitCyclicProjectionLin S X)
    hrhoBeta hD reconstruct hnorm hform hp he
  dsimp only at hbase ⊢
  intro x
  have hx := hbase (oneExitPositiveProjectionLin S X x)
  have hPid :
      oneExitPositiveProjectionLin S X
          (oneExitPositiveProjectionLin S X x) =
        oneExitPositiveProjectionLin S X x := by
    have hlin := congrArg Matrix.toEuclideanLin
      (positiveStarProjection_isStarProjection S X).isIdempotentElem.eq
    rw [Matrix.toLpLin_mul_same] at hlin
    simpa [oneExitPositiveProjectionLin] using LinearMap.congr_fun hlin x
  rw [hPid] at hx
  exact hx

set_option maxHeartbeats 400000 in

private theorem fullAdjacency_oneExit_sq_comparison_linear
    (S : Finset ℕ) (X : ℕ)
    (i : Fin (Module.finrank ℂ (OneExitAmbient S X))) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta)
    (hrho : 0 <
      (oneExitCompressionLin_isSymmetric S X).eigenvalues rfl i)
    (hscale : 4 * beta ≤
      (oneExitCompressionLin_isSymmetric S X).eigenvalues rfl i) :
    0 ≤
        (fullComplexAdjacencyLin_isSymmetric S X).eigenvalues rfl i ^ 2 -
          (oneExitCompressionLin_isSymmetric S X).eigenvalues rfl i ^ 2 ∧
      (fullComplexAdjacencyLin_isSymmetric S X).eigenvalues rfl i ^ 2 -
          (oneExitCompressionLin_isSymmetric S X).eigenvalues rfl i ^ 2 ≤
        7 * beta ^ 4 /
          (oneExitCompressionLin_isSymmetric S X).eigenvalues rfl i ^ 2 := by
  let hA := fullComplexAdjacencyLin_isSymmetric S X
  let hG := oneExitCompressionLin_isSymmetric S X
  have data := oneExit_threeBlock_data S X hbeta hsmall
  let rho := hG.eigenvalues rfl i
  have hrhoBeta : beta < rho := by
    have : beta ≤ rho / 4 := by
      change 4 * beta ≤ rho at hscale
      linarith
    change 0 < rho at hrho
    nlinarith
  rcases oneExit_oldBlock_reconstruction S X
      (by simpa [rho, hG] using hrho) hrhoBeta data.cyclic_upper with
    ⟨reconstruct, hold⟩
  have hcompression : ∀ y : OneExitAmbient S X,
      RCLike.re (inner ℂ y (oneExitCompressionLin S X y)) =
        RCLike.re (inner ℂ
          (oneExitProjectionLin S X y)
          (fullComplexAdjacencyLin S X (oneExitProjectionLin S X y))) := by
    simpa [oneExitCompressionLin, oneExitProjectionLin,
      fullComplexAdjacencyLin] using oneExitCompression_quadraticForm_eq S X
  have hcontract : ∀ y : OneExitAmbient S X,
      ‖oneExitProjectionLin S X y‖ ≤ ‖y‖ := by
    simpa [oneExitProjectionLin] using norm_oneExitProjection_apply_le S X
  have hresult := rclike_padded_twoStageSchur_sq_comparison_of_block_reduction
    (fullComplexAdjacencyLin S X) (oneExitCompressionLin S X) hA hG
    (oneExitProjectionLin S X) hcompression hcontract i hbeta
    (by simpa [hG] using hrho) (by simpa [hG] using hscale)
    (oneExitPositiveBlockLin S X) (oneExitCyclicBlockLin S X)
    (oneExitDiscardedBlockLin S X) (oneExitPositiveCyclicBlockLin S X)
    (oneExitCyclicDiscardedBlockLin S X)
    (oneExitPositiveProjectionLin S X) (oneExitCyclicProjectionLin S X)
    (oneExitDiscardedProjectionLin S X) data.cyclic_symmetric
    data.norm_decomposition data.form_decomposition data.cyclic_upper
    data.discarded_upper data.positive_cyclic_sq data.cyclic_discarded_sq
    reconstruct hold
  simpa [hA, hG] using hresult

set_option maxHeartbeats 800000 in

theorem fullAdjacency_oneExit_sq_comparison_of_smallPrimeNorm
    (S : Finset ℕ) (X : ℕ)
    (i : Fin (Fintype.card (PrimeStar.Vertex S X))) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta)
    (hrho : 0 < (oneExitCompression_isHermitian S X).eigenvalues₀ i)
    (hscale :
      4 * beta ≤ (oneExitCompression_isHermitian S X).eigenvalues₀ i) :
    0 ≤
        (moleculeFamilyComplexAdjacency_isHermitian S X).eigenvalues₀ i ^ 2 -
          (oneExitCompression_isHermitian S X).eigenvalues₀ i ^ 2 ∧
      (moleculeFamilyComplexAdjacency_isHermitian S X).eigenvalues₀ i ^ 2 -
          (oneExitCompression_isHermitian S X).eigenvalues₀ i ^ 2 ≤
        7 * beta ^ 4 /
          (oneExitCompression_isHermitian S X).eigenvalues₀ i ^ 2 := by
  let V := OneExitAmbient S X
  let i' : Fin (Module.finrank ℂ V) :=
    Fin.cast finrank_euclideanSpace.symm i
  have hGroot : (oneExitCompressionLin_isSymmetric S X).eigenvalues rfl i' =
      (oneExitCompression_isHermitian S X).eigenvalues₀ i := by
    calc
      (oneExitCompressionLin_isSymmetric S X).eigenvalues rfl i' =
          (oneExitCompressionLin_isSymmetric S X).eigenvalues
            finrank_euclideanSpace i := by
              exact symmetricEigenvalues_cast (oneExitCompressionLin S X)
                (oneExitCompressionLin_isSymmetric S X)
                finrank_euclideanSpace i
      _ = (oneExitCompression_isHermitian S X).eigenvalues₀ i := by rfl
  have hAroot : (fullComplexAdjacencyLin_isSymmetric S X).eigenvalues rfl i' =
      (moleculeFamilyComplexAdjacency_isHermitian S X).eigenvalues₀ i := by
    calc
      (fullComplexAdjacencyLin_isSymmetric S X).eigenvalues rfl i' =
          (fullComplexAdjacencyLin_isSymmetric S X).eigenvalues
            finrank_euclideanSpace i := by
              exact symmetricEigenvalues_cast (fullComplexAdjacencyLin S X)
                (fullComplexAdjacencyLin_isSymmetric S X)
                finrank_euclideanSpace i
      _ = (moleculeFamilyComplexAdjacency_isHermitian S X).eigenvalues₀ i := by rfl
  have hresult := fullAdjacency_oneExit_sq_comparison_linear
    S X i' hbeta hsmall (by simpa [hGroot] using hrho)
      (by simpa [hGroot] using hscale)
  rw [hAroot, hGroot] at hresult
  exact hresult

set_option maxHeartbeats 800000 in

theorem eventually_powerRange_fullAdjacency_oneExit_sq_comparison
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        0 ≤ (fullAdjacencyEigenvalueAtArithmeticRank a) ^ 2 -
            (oneExitEigenvalueAtArithmeticRank a) ^ 2 ∧
          (fullAdjacencyEigenvalueAtArithmeticRank a) ^ 2 -
              (oneExitEigenvalueAtArithmeticRank a) ^ 2 ≤
            57344 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
              ((a : ℝ) / Real.log (X : ℝ)) := by
  filter_upwards
      [eventually_powerRange_largePrimeStarDegree_residualScaleBundle
        S hS htheta,
       PrimeStar.eventually_sqrtCutoff_smallPrimeGraph_l2_opNorm_le_tuned]
      with X hscaleBundle hreal
  intro a ha
  obtain ⟨haY, hd, hresidualSmall, _hdegreeLower, hrate⟩ :=
    hscaleBundle a ha
  let eta : ℝ := PrimeStar.sqrtCutoffResidualScale X
  let beta : ℝ := 2 * eta
  let mu : ℝ := moleculeStarEnergy S X a
  let rho : ℝ := oneExitEigenvalueAtArithmeticRank a
  have heta : 0 ≤ eta := by
    dsimp [eta, PrimeStar.sqrtCutoffResidualScale]
    exact mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
  have hbeta : 0 ≤ beta := by dsimp [beta]; positivity
  have hmu : 0 < mu := by
    dsimp [mu, moleculeStarEnergy]
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsmall : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ beta := by
    exact oneExitSmallPrimeMatrix_l2OperatorNorm_le_two_mul_real
      S X heta (by
        simpa [eta, PrimeStar.sqrtCutoffResidualScale,
          PrimeStar.sqrtCutoffResidualConstant] using hreal S)
  have hrhoLower : mu - beta ≤ rho := by
    simpa [mu, beta, rho, moleculeStarEnergy] using
      oneExitEigenvalueAtArithmeticRank_ge_starEnergy_sub
        hS a haY hd hsmall
  have hresidualSmall' : 1000000 * eta ^ 2 ≤ mu ^ 2 := by
    rw [show mu ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) by
        simpa [mu] using moleculeStarEnergy_sq S X a]
    simpa [eta] using hresidualSmall
  have hthousand : 1000 * eta ≤ mu := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ 1000 * eta) hmu.le).mp
    nlinarith
  have hrho : 0 < rho := by
    dsimp [beta] at hrhoLower
    nlinarith
  have hfour : 4 * beta ≤ rho := by
    dsimp [beta] at hrhoLower ⊢
    nlinarith
  have hcomparison :=
    fullAdjacency_oneExit_sq_comparison_of_smallPrimeNorm S X
      (oneExitArithmeticRankIndex a) hbeta hsmall
      (by simpa [rho, oneExitEigenvalueAtArithmeticRank] using hrho)
      (by simpa [rho, oneExitEigenvalueAtArithmeticRank] using hfour)
  have hcomparison' :
      0 ≤ (fullAdjacencyEigenvalueAtArithmeticRank a) ^ 2 - rho ^ 2 ∧
        (fullAdjacencyEigenvalueAtArithmeticRank a) ^ 2 - rho ^ 2 ≤
          7 * beta ^ 4 / rho ^ 2 := by
    rw [moleculeFamilyComplexAdjacencyEigenvalueAtArithmeticRank_eq] at hcomparison
    simpa [rho, oneExitEigenvalueAtArithmeticRank] using hcomparison
  have hrhoHalf : mu / 2 ≤ rho := by
    dsimp [beta] at hrhoLower
    nlinarith
  have hmuSqLe : mu ^ 2 ≤ 4 * rho ^ 2 := by
    have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ mu / 2) hrho.le).2 hrhoHalf
    nlinarith
  have hrhoSqPos : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hmuSqPos : 0 < mu ^ 2 := sq_pos_of_pos hmu
  have hschurRate : 7 * beta ^ 4 / rho ^ 2 ≤
      448 * (eta ^ 4 / mu ^ 2) := by
    have hcross :
        (112 * eta ^ 4) * mu ^ 2 ≤ (448 * eta ^ 4) * rho ^ 2 := by
      calc
        (112 * eta ^ 4) * mu ^ 2 ≤
            (112 * eta ^ 4) * (4 * rho ^ 2) :=
          mul_le_mul_of_nonneg_left hmuSqLe (by positivity)
        _ = (448 * eta ^ 4) * rho ^ 2 := by ring
    calc
      7 * beta ^ 4 / rho ^ 2 = (112 * eta ^ 4) / rho ^ 2 := by
        dsimp [beta]
        ring
      _ ≤ (448 * eta ^ 4) / mu ^ 2 :=
        (div_le_div_iff₀ hrhoSqPos hmuSqPos).2 hcross
      _ = 448 * (eta ^ 4 / mu ^ 2) := by ring
  have hbundle : eta ^ 4 / mu ^ 2 ≤
      128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
        ((a : ℝ) / Real.log (X : ℝ)) := by
    rw [show mu ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) by
        simpa [mu] using moleculeStarEnergy_sq S X a]
    simpa [eta] using hrate
  refine ⟨hcomparison'.1, hcomparison'.2.trans ?_⟩
  calc
    7 * beta ^ 4 / rho ^ 2 ≤ 448 * (eta ^ 4 / mu ^ 2) := hschurRate
    _ ≤ 448 *
        (128 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
          ((a : ℝ) / Real.log (X : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hbundle (by norm_num)
    _ = 57344 * PrimeStar.sqrtCutoffResidualConstant ^ 4 *
          ((a : ℝ) / Real.log (X : ℝ)) := by ring

end

section OrderedComparison

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- An ordered eigenvalue is bounded above by any quadratic-form bound on a
subspace of the corresponding codimension.  This is the finite min--max
interface used by the two-stage Schur comparison. -/
theorem rclike_eigenvalue_le_of_large_subspace
    [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) (z : ℝ)
    (W : Submodule 𝕜 E)
    (hWrank : Module.finrank 𝕜 E - i.1 ≤ Module.finrank 𝕜 W)
    (hWquad : ∀ x ∈ W,
      RCLike.re (inner 𝕜 x (T x)) ≤ z * ‖x‖ ^ 2) :
    hT.eigenvalues rfl i ≤ z := by
  let U := rclikeOrderedEigenPrefix T hT i
  have hUrank : Module.finrank 𝕜 U = i.1 + 1 :=
    finrank_rclikeOrderedEigenPrefix T hT i
  have hsum : Module.finrank 𝕜 E <
      Module.finrank 𝕜 U + Module.finrank 𝕜 W := by
    rw [hUrank]
    omega
  have hnot : ¬ Disjoint U W := by
    intro hdis
    exact (not_le_of_gt hsum)
      (Submodule.finrank_add_finrank_le_of_disjoint hdis)
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxU, hxW, hx0⟩ := hnot
  have hxNorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hlower :=
    rclike_eigenvalue_mul_norm_sq_le_re_inner_apply_of_mem_prefix
      T hT i x hxU
  have hupper := hWquad x hxW
  nlinarith

/-- A pointwise operator-norm bound controls the real part of the quadratic
form over either `ℝ` or `ℂ`. -/
theorem abs_re_inner_apply_le_of_pointwise_norm_bound
    (H : E →ₗ[𝕜] E) (eta : ℝ)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖) (x : E) :
    |RCLike.re (inner 𝕜 x (H x))| ≤ eta * ‖x‖ ^ 2 := by
  calc
    |RCLike.re (inner 𝕜 x (H x))| ≤ ‖inner 𝕜 x (H x)‖ :=
      RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖H x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (eta * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hH x) (norm_nonneg x)
    _ = eta * ‖x‖ ^ 2 := by ring

/-- Ordered Weyl comparison for a symmetric perturbation over an RCLike
field.  This is the complex-Hermitian analogue of Paper I's real theorem,
proved from the min--max interfaces already owned by this module. -/
theorem abs_rclike_orderedEigenvalue_add_sub_le
    [FiniteDimensional 𝕜 E]
    (L H : E →ₗ[𝕜] E) (hL : L.IsSymmetric) (hHsymm : H.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) (eta : ℝ)
    (hH : ∀ x : E, ‖H x‖ ≤ eta * ‖x‖) :
    |(hL.add hHsymm).eigenvalues rfl i - hL.eigenvalues rfl i| ≤ eta := by
  let A := L + H
  let hA : A.IsSymmetric := hL.add hHsymm
  have hupper : hA.eigenvalues rfl i ≤ hL.eigenvalues rfl i + eta := by
    apply rclike_eigenvalue_le_of_large_subspace A hA i
      (hL.eigenvalues rfl i + eta)
      (rclikeOrderedEigenSuffix L hL i)
    · exact le_of_eq (finrank_rclikeOrderedEigenSuffix L hL i).symm
    · intro x hx
      have hLhi :=
        rclike_re_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_suffix
          L hL i x hx
      have hHabs := abs_re_inner_apply_le_of_pointwise_norm_bound H eta hH x
      have hHhi : RCLike.re (inner 𝕜 x (H x)) ≤ eta * ‖x‖ ^ 2 :=
        (le_abs_self _).trans hHabs
      have hsplit : RCLike.re (inner 𝕜 x (A x)) =
          RCLike.re (inner 𝕜 x (L x)) +
            RCLike.re (inner 𝕜 x (H x)) := by
        simp [A, inner_add_right]
      rw [hsplit]
      nlinarith
  have hlower : hL.eigenvalues rfl i - eta ≤ hA.eigenvalues rfl i := by
    apply rclike_le_eigenvalue_of_large_subspace A hA i
      (hL.eigenvalues rfl i - eta)
      (rclikeOrderedEigenPrefix L hL i)
    · exact le_of_eq (finrank_rclikeOrderedEigenPrefix L hL i).symm
    · intro x hx
      have hLlo :=
        rclike_eigenvalue_mul_norm_sq_le_re_inner_apply_of_mem_prefix
          L hL i x hx
      have hHabs := abs_re_inner_apply_le_of_pointwise_norm_bound H eta hH x
      have hHlo : -(eta * ‖x‖ ^ 2) ≤ RCLike.re (inner 𝕜 x (H x)) :=
        (neg_le_neg hHabs).trans (neg_abs_le _)
      have hsplit : RCLike.re (inner 𝕜 x (A x)) =
          RCLike.re (inner 𝕜 x (L x)) +
            RCLike.re (inner 𝕜 x (H x)) := by
        simp [A, inner_add_right]
      rw [hsplit]
      nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- An index in an RCLike compression, lifted to the ambient finrank. -/
def liftRCLikeCompressionEigenIndex [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (Q : F →ₗᵢ[𝕜] E)
    (i : Fin (Module.finrank 𝕜 F)) : Fin (Module.finrank 𝕜 E) :=
  ⟨i.1, lt_of_lt_of_le i.2
    (Q.toLinearMap.finrank_le_finrank_of_injective Q.injective)⟩

/-- Cauchy interlacing for an isometric compression over an RCLike field. -/
theorem rclike_compressed_eigenvalue_le_ambient_eigenvalue
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] E) (B : F →ₗ[𝕜] F)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (Q : F →ₗᵢ[𝕜] E)
    (hcompression : ∀ x : F,
      RCLike.re ⟪x, B x⟫_𝕜 = RCLike.re ⟪Q x, A (Q x)⟫_𝕜)
    (i : Fin (Module.finrank 𝕜 F)) :
    hB.eigenvalues rfl i ≤
      hA.eigenvalues rfl (liftRCLikeCompressionEigenIndex Q i) := by
  let j := liftRCLikeCompressionEigenIndex Q i
  let U := (rclikeOrderedEigenPrefix B hB i).map Q.toLinearMap
  let W := rclikeOrderedEigenSuffix A hA j
  have hUrank : Module.finrank 𝕜 U = i.1 + 1 := by
    let e := Submodule.equivMapOfInjective Q.toLinearMap Q.injective
      (rclikeOrderedEigenPrefix B hB i)
    calc
      Module.finrank 𝕜 U =
          Module.finrank 𝕜 (rclikeOrderedEigenPrefix B hB i) := by
        simpa [U, e] using e.finrank_eq.symm
      _ = i.1 + 1 := finrank_rclikeOrderedEigenPrefix B hB i
  have hWrank : Module.finrank 𝕜 W = Module.finrank 𝕜 E - i.1 := by
    simpa [W, j, liftRCLikeCompressionEigenIndex] using
      finrank_rclikeOrderedEigenSuffix A hA j
  have hsum : Module.finrank 𝕜 E <
      Module.finrank 𝕜 U + Module.finrank 𝕜 W := by
    rw [hUrank, hWrank]
    have hi : i.1 < Module.finrank 𝕜 E :=
      lt_of_lt_of_le i.2
        (Q.toLinearMap.finrank_le_finrank_of_injective Q.injective)
    omega
  have hnot : ¬ Disjoint U W := by
    intro hdis
    exact (not_le_of_gt hsum)
      (Submodule.finrank_add_finrank_le_of_disjoint hdis)
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxU, hxW, hx0⟩ := hnot
  rcases hxU with ⟨y, hy, rfl⟩
  have hy0 : y ≠ 0 := by
    intro hyzero
    apply hx0
    simp [hyzero]
  have hyNorm : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hy0)
  have hBlower :=
    rclike_eigenvalue_mul_norm_sq_le_re_inner_apply_of_mem_prefix
      B hB i y hy
  have hAupper :=
    rclike_re_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_suffix
      A hA j (Q y) hxW
  rw [← hcompression] at hAupper
  rw [Q.norm_map] at hAupper
  nlinarith

end OrderedComparison

end PrimeCoverPowerBand
