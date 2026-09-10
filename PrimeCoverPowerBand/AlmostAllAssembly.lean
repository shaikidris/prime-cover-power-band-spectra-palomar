import PrimeCoverPowerBand.AlmostAllSpectralBudget
import Mathlib.Data.Finset.Sort

/-!
# Ordered power-band assembly on the complete arithmetic prefix

The increasing prefix enumeration preserves the global arithmetic rank.
Weak sorting compares values, including plateaus. The actual frame and
complement producers are imported from `AlmostAllSpectralBudget`.
Declaration-level extraction provenance is recorded in `PORT_MANIFEST.md`.
-/

namespace PrimeCoverPowerBand

open Filter Topology
open scoped BigOperators Classical InnerProductSpace Matrix Matrix.Norms.L2Operator

noncomputable section

/-- Arithmetic order on retained centres, inherited through their natural values. -/
instance moleculeCenterLinearOrder (S : Finset ℕ) (X K : ℕ) :
    LinearOrder (MoleculeCenter S X K) :=
  LinearOrder.lift' (fun a : MoleculeCenter S X K ↦ (a.1 : ℕ)) (by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact Fin.ext hab)

/-- The canonical increasing enumeration of the complete allowed prefix. -/
def increasingMoleculeCenterOrderIso (S : Finset ℕ) (X K : ℕ) :
    Fin (Fintype.card (MoleculeCenter S X K)) ≃o MoleculeCenter S X K :=
  Fintype.orderIsoFinOfCardEq (MoleculeCenter S X K) rfl

/-- The zero-based position of a centre in the complete arithmetic prefix. -/
def moleculeCenterRankIndex {S : Finset ℕ} {X K : ℕ}
    (a : MoleculeCenter S X K) : Fin (Fintype.card (MoleculeCenter S X K)) :=
  (increasingMoleculeCenterOrderIso S X K).symm a

/-- Every allowed vertex preceding a retained centre is itself retained. -/
theorem card_prefix_predecessors_eq {S : Finset ℕ} {X K : ℕ}
    (a : MoleculeCenter S X K) :
    (Finset.univ.filter fun b : MoleculeCenter S X K ↦
      (b.1 : ℕ) < (a.1 : ℕ)).card =
    (Finset.univ.filter fun b : Vertex S X ↦ (b : ℕ) < (a.1 : ℕ)).card := by
  apply Finset.card_bij (fun b _ ↦ b.1)
  · intro b hb
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
  · intro b _ c _ hbc
    exact Subtype.ext hbc
  · intro b hb
    have hba := (Finset.mem_filter.mp hb).2
    refine ⟨⟨b, hba.le.trans a.2⟩, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hba

/-- The complete-prefix position is the literal global arithmetic index. -/
theorem moleculeCenterRankIndex_val {S : Finset ℕ} {X K : ℕ}
    (a : MoleculeCenter S X K) :
    (moleculeCenterRankIndex a).val = (arithmeticRankIndex a.1).val := by
  let e := increasingMoleculeCenterOrderIso S X K
  have hcard : (Finset.Iio (e.symm a)).card =
      (Finset.univ.filter fun b : MoleculeCenter S X K ↦
        (b.1 : ℕ) < (a.1 : ℕ)).card := by
    apply Finset.card_bij (fun i _ ↦ e i)
    · intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change e i < a
      exact (e.lt_symm_apply).mp (Finset.mem_Iio.mp hi)
    · intro i _ j _ hij
      exact e.injective hij
    · intro b hb
      refine ⟨e.symm b, Finset.mem_Iio.mpr ?_, e.apply_symm_apply b⟩
      exact e.symm.strictMono ((Finset.mem_filter.mp hb).2)
  rw [Fin.card_Iio, card_prefix_predecessors_eq] at hcard
  exact hcard

/-- The prime-counting targets decrease weakly in arithmetic order. -/
theorem antitone_prefixPrimeCount (S : Finset ℕ) (X K : ℕ) :
    Antitone (fun i : Fin (Fintype.card (MoleculeCenter S X K)) ↦
      (allowedPrimeCount S
        (X / ((increasingMoleculeCenterOrderIso S X K i).1 : ℕ)) : ℝ)) := by
  intro i j hij
  have hcent : ((increasingMoleculeCenterOrderIso S X K i).1 : ℕ) ≤
      ((increasingMoleculeCenterOrderIso S X K j).1 : ℕ) :=
    (increasingMoleculeCenterOrderIso S X K).monotone hij
  have hdiv : X / ((increasingMoleculeCenterOrderIso S X K j).1 : ℕ) ≤
      X / ((increasingMoleculeCenterOrderIso S X K i).1 : ℕ) :=
    Nat.div_le_div_left hcent (Vertex.coe_pos _)
  have hcount : allowedPrimeCount S
      (X / ((increasingMoleculeCenterOrderIso S X K j).1 : ℕ)) ≤
      allowedPrimeCount S (X / ((increasingMoleculeCenterOrderIso S X K i).1 : ℕ)) :=
    PrimeStar.allowedPrimeCount_mono hdiv
  exact Nat.cast_le.mpr hcount

/-- A real diagonal Hermitian matrix has its entries in descending value
order as its ordered spectrum. This assertion includes repeated entries. -/
theorem eigenvalues₀_diagonal_eq_descendingSort
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℂ} (hA : A.IsHermitian)
    (f : α → ℝ) (e : Fin (Fintype.card α) ≃ α)
    (hdiag : A = Matrix.diagonal (fun j ↦ (f j : ℂ)))
    (i : Fin (Fintype.card α)) :
    hA.eigenvalues₀ i = f (e (Tuple.sort (fun j ↦ -f (e j)) i)) := by
  let fEnum : Fin (Fintype.card α) → ℝ := f ∘ e
  let σ := Tuple.sort (fun j ↦ -fEnum j)
  have hanti : Antitone (fEnum ∘ σ) := by
    intro i j hij
    have h := Tuple.monotone_sort (fun k ↦ -fEnum k) hij
    dsimp [σ] at h ⊢
    linarith
  have huniv : Finset.univ.val.map f = Finset.univ.val.map fEnum := by
    calc
      Finset.univ.val.map f = (Finset.univ.val.map e).map f := by
        rw [Multiset.map_univ_val_equiv e]
      _ = Finset.univ.val.map fEnum := by rw [Multiset.map_map]
  have hrootsRaw : A.charpoly.roots.map Complex.re = Finset.univ.val.map f := by
    rw [hdiag, Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hroots : (A.charpoly.roots.map Complex.re).sort (· ≥ ·) =
      (Finset.univ.val.map fEnum).sort (· ≥ ·) :=
    (congrArg (fun m : Multiset ℝ ↦ m.sort (· ≥ ·)) hrootsRaw).trans
      (congrArg (fun m : Multiset ℝ ↦ m.sort (· ≥ ·)) huniv)
  have heigs : (Finset.univ.val.map fEnum).sort (· ≥ ·) =
      List.ofFn hA.eigenvalues₀ := by
    rw [← hroots]
    exact hA.sort_roots_charpoly_eq_eigenvalues₀
  have hperm : List.Perm ((Finset.univ.val.map fEnum).sort (· ≥ ·))
      (List.ofFn (fEnum ∘ σ)) := by
    rw [Fin.univ_val_map]
    exact (List.mergeSort_perm _ _).trans (σ.ofFn_comp_perm fEnum).symm
  have hleft : ((Finset.univ.val.map fEnum).sort (· ≥ ·)).SortedGE :=
    List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)
  have hlist : (Finset.univ.val.map fEnum).sort (· ≥ ·) =
      List.ofFn (fEnum ∘ σ) := hperm.eq_of_sortedGE hleft hanti.sortedGE_ofFn
  have heq : hA.eigenvalues₀ = fEnum ∘ σ := by
    rw [← List.ofFn_inj, ← heigs, hlist]
  exact congrFun heq i

/-- Complexification retains the literal exact-root diagonal. -/
theorem complexify_exactMoleculeFamilyRootMatrix_eq_diagonal
    (S : Finset ℕ) (X K : ℕ) :
    complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K) =
      Matrix.diagonal (fun a ↦ (exactPrincipalMoleculeRoot S X a.1 : ℂ)) := by
  ext a b
  by_cases h : a = b <;>
    simp [complexifyRealMatrix, exactMoleculeFamilyRootMatrix, h]

/-- The actual complexified molecule-root diagonal is Hermitian. -/
theorem complexify_exactMoleculeFamilyRootMatrix_isHermitian
    (S : Finset ℕ) (X K : ℕ) :
    (complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)).IsHermitian := by
  rw [complexify_exactMoleculeFamilyRootMatrix_eq_diagonal]
  apply Matrix.IsHermitian.ext
  intro a b
  by_cases h : a = b
  · subst b; simp
  · simp [h, Ne.symm h]

/-- The ordered value of the actual complete-prefix root model. -/
def orderedPrefixMoleculeRoot (S : Finset ℕ) (X K : ℕ)
    (i : Fin (Fintype.card (MoleculeCenter S X K))) : ℝ :=
  (complexify_exactMoleculeFamilyRootMatrix_isHermitian S X K).eigenvalues₀ i

/-- Sorting the positive exact roots preserves the uniform squared-energy
error at the SAME arithmetic rank, even on prime-counting plateaus. -/
theorem abs_orderedPrefixMoleculeRoot_sq_sub_primeCount_le
    {S : Finset ℕ} {X K : ℕ} {u : ℝ}
    (hpos : ∀ a : MoleculeCenter S X K, 0 ≤ exactPrincipalMoleculeRoot S X a.1)
    (hbound : ∀ a : MoleculeCenter S X K,
      |exactPrincipalMoleculeRoot S X a.1 ^ 2 -
        (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ)| ≤ u)
    (a : MoleculeCenter S X K) :
    |orderedPrefixMoleculeRoot S X K (moleculeCenterRankIndex a) ^ 2 -
      (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ)| ≤ u := by
  let e := increasingMoleculeCenterOrderIso S X K
  let f := fun i ↦ exactPrincipalMoleculeRoot S X (e i).1
  let σ := Tuple.sort (fun i ↦ -f i)
  have hsort : Antitone (f ∘ σ) := by
    intro i j hij
    have h := Tuple.monotone_sort (fun k ↦ -f k) hij
    dsimp [σ] at h ⊢
    linarith
  have hsquares : Antitone ((fun i ↦ f i ^ 2) ∘ σ) := by
    intro i j hij
    exact pow_le_pow_left₀ (hpos (e (σ j))) (hsort hij) 2
  have h := abs_comp_perm_sub_le_of_antitone (antitone_prefixPrimeCount S X K)
    σ hsquares (fun i ↦ hbound (e i)) (moleculeCenterRankIndex a)
  have heigen := eigenvalues₀_diagonal_eq_descendingSort
    (complexify_exactMoleculeFamilyRootMatrix_isHermitian S X K)
    (fun b : MoleculeCenter S X K ↦ exactPrincipalMoleculeRoot S X b.1)
    e.toEquiv (complexify_exactMoleculeFamilyRootMatrix_eq_diagonal S X K)
    (moleculeCenterRankIndex a)
  change orderedPrefixMoleculeRoot S X K (moleculeCenterRankIndex a) =
    f (σ (moleculeCenterRankIndex a)) at heigen
  rw [heigen]
  simpa only [moleculeCenterRankIndex, e, OrderIso.apply_symm_apply] using h


/-- A fixed prefix factor is absorbed by any strictly larger power exponent. -/
theorem eventually_powerScale_fixed_mul_le {theta theta' : ℝ}
    (hgap : theta < theta') (P : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ B : ℕ, (B : ℝ) ≤ powerScale theta X →
      P * B ≤ powerScale theta' X := by
  have hp : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (theta' - theta)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hgap)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually_ge_atTop P, eventually_gt_atTop 0] with X hP hX
  intro B hB
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  calc
    P * B ≤ (X : ℝ) ^ (theta' - theta) * powerScale theta X :=
      mul_le_mul hP hB (by positivity) (Real.rpow_nonneg hx.le _)
    _ = powerScale theta' X := by
      rw [powerScale, ← Real.rpow_add hx]
      congr 1
      ring

/-- PNT bounds the literal prime-count target on each fixed power range. -/
theorem eventually_powerRange_primeCount_scale_bounds
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (X : ℝ) / (8 * (a : ℝ) * Real.log (X : ℝ)) ≤
          (allowedPrimeCount S (X / (a : ℕ)) : ℝ) ∧
        (allowedPrimeCount S (X / (a : ℕ)) : ℝ) ≤
          12 * (X : ℝ) / ((a : ℝ) * Real.log (X : ℝ)) := by
  filter_upwards [eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
    eventually_squareRootRange_allowedPrime_bounds S hS, eventually_gt_atTop 1]
    with X hscale hcenter hp hX
  intro a ha
  have hap := Vertex.coe_pos a
  have har : (0 : ℝ) < a := by exact_mod_cast hap
  have haY : (a : ℕ) ≤ Nat.sqrt X := by have := hcenter (a : ℕ) ha; omega
  have hYN : Nat.sqrt X ≤ X / (a : ℕ) := by
    apply (Nat.le_div_iff_mul_le hap).mpr
    exact (Nat.mul_le_mul_left (Nat.sqrt X) haY).trans (Nat.sqrt_le X)
  have hdata := hp (X / (a : ℕ)) hYN (Nat.div_le_self _ _)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  constructor
  · apply (hscale a ha).1.trans
    rw [moleculeStarEnergy_sq,
      PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS a haY hYN]
    exact_mod_cast Nat.sub_le (PrimeStar.allowedPrimeCount S (X / (a : ℕ))) _
  · calc
      _ ≤ 4 * ((X / (a : ℕ) : ℕ) : ℝ) / Real.log ((X / (a : ℕ) : ℕ) : ℝ) := by
        simpa only [mul_div_assoc] using hdata.2.1
      _ ≤ 4 * ((X : ℝ) / (a : ℝ)) / (Real.log (X : ℝ) / 3) := by
        gcongr
        · exact Nat.cast_div_le
        · linarith [hdata.2.2.2.2]
      _ = _ := by ring

/-- The logarithmic correction fits the deterministic terminal-band scale. -/
theorem eventually_terminalScale_log_sq_le {theta : ℝ}
    (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X → Real.log (X : ℝ) ^ 2 ≤ B := by
  filter_upwards [eventually_terminalScale_polylog_schurFactor_lt 2 hthetaPos htheta
    (C := 1) (ε := 1) (by norm_num) (by norm_num), eventually_gt_atTop 1]
    with X hs hX
  intro B hlo hhi
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < (B : ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hx theta) hL).trans_le hlo
  have h := hs B hlo hhi
  have hterm : Real.log (X : ℝ) ^ 2 / B < 1 := by
    apply lt_of_le_of_lt _ h
    simp only [one_mul, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (sq_nonneg _)
  simpa only [one_mul] using ((div_lt_iff₀ hb).mp hterm).le

/-- S1 and the correction bound supply a uniform error on the actual
complete prefix; neither the model energy nor its error is a free premise. -/
theorem eventually_terminalScale_prefixMolecule_primeCount_error
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      ∀ a : MoleculeCenter S X (12288 * B),
        0 < exactPrincipalMoleculeRoot S X a.1 ∧
        |exactPrincipalMoleculeRoot S X a.1 ^ 2 -
          (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ)| ≤
            C * B / Real.log (X : ℝ) := by
  let theta' := (theta + 1 / 2) / 2
  have ht' : theta' < 1 / 2 := by dsimp [theta']; linarith
  have htt' : theta < theta' := by dsimp [theta']; linarith
  obtain ⟨C, hC, hs1⟩ := eventually_powerRange_exactPrincipalMoleculeRoot_targetDefect_le S hS ht'
  let M := powerBandFirstExitCorrectionLogConstant
  have hM : 0 < M := powerBandFirstExitCorrectionLogConstant_pos
  refine ⟨12288 * C + M, by positivity, ?_⟩
  filter_upwards [hs1, eventually_powerRange_firstExitCorrection_le_log S hS ht',
    eventually_powerRange_exactPrincipalMoleculeRoot_pos S hS ht',
    eventually_powerScale_fixed_mul_le htt' 12288,
    eventually_terminalScale_log_sq_le hthetaPos htheta, eventually_gt_atTop 1]
    with X hs1 hc hp hk hlog hX
  intro B hlo hhi a
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have ha : InPowerRange theta' X (a.1 : ℕ) :=
    ⟨Vertex.coe_pos _, (show (a.1 : ℝ) ≤ 12288 * B by exact_mod_cast a.2).trans (hk B hhi)⟩
  refine ⟨hp a.1 ha, ?_⟩
  have hs := hs1 a.1 ha
  rw [targetDefect_eq] at hs
  have hcorr := (hc a.1 ha).2
  have hML : M * Real.log (X : ℝ) ≤ M * B / Real.log (X : ℝ) := by
    apply (le_div_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hlog B hlo hhi) hM.le]
  calc
    _ ≤ |exactPrincipalMoleculeRoot S X a.1 ^ 2 -
        (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ) - firstExitCorrection S X a.1| +
        |firstExitCorrection S X a.1| := by
      have heq : (exactPrincipalMoleculeRoot S X a.1 ^ 2 -
          (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ) - firstExitCorrection S X a.1) +
          firstExitCorrection S X a.1 = exactPrincipalMoleculeRoot S X a.1 ^ 2 -
            (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ) := by ring
      exact (congrArg abs heq).symm.le.trans (abs_add_le _ _)
    _ ≤ C * (a.1 : ℝ) / Real.log (X : ℝ) + M * Real.log (X : ℝ) := add_le_add hs hcorr
    _ ≤ C * (12288 * B) / Real.log (X : ℝ) + M * B / Real.log (X : ℝ) := by
      apply add_le_add _ hML
      gcongr
      exact_mod_cast a.2
    _ = _ := by ring

/-- Every fixed deterministic multiple of B/log X is smaller than the
terminal energy squared by a fixed factor, uniformly in the retained band. -/
theorem eventually_terminalScale_linearError_le_energy
    {theta C : ℝ} (htheta : theta < 1 / 2) (hC : 0 ≤ C) :
    ∀ᶠ X : ℕ in atTop, ∀ B : ℕ, 0 < B →
      (B : ℝ) ≤ powerScale theta X →
      C * B / Real.log (X : ℝ) ≤
        ((X : ℝ) / (B * Real.log (X : ℝ))) / 16 := by
  have hlim := ((tendsto_powerScale_div_sqrt_zero htheta).pow 2).const_mul C
  have hsmall : ∀ᶠ X : ℕ in atTop,
      C * (powerScale theta X / Real.sqrt (X : ℝ)) ^ 2 < 1 / 16 := by
    simpa using (tendsto_order.mp hlim).2 (1 / 16) (by norm_num)
  filter_upwards [hsmall, eventually_gt_atTop 1] with X hs hX
  intro B hB hhi
  have hb : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hr : C * ((B : ℝ) / Real.sqrt (X : ℝ)) ^ 2 < 1 / 16 := by
    apply lt_of_le_of_lt _ hs
    gcongr
  have hBB : C * (B : ℝ) ^ 2 ≤ (X : ℝ) / 16 := by
    rw [div_pow, Real.sq_sqrt hx.le, ← mul_div_assoc] at hr
    have h := (div_lt_iff₀ hx).mp hr
    linarith
  have heq : ((X : ℝ) / (B * Real.log (X : ℝ))) / 16 =
      ((X : ℝ) / 16) / (B * Real.log (X : ℝ)) := by ring
  rw [heq]
  apply (div_le_div_iff₀ hL (mul_pos hb hL)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hBB hL.le]

/-- Actual sorted-prefix errors and the fixed root window at each dyadic
arithmetic rank. No sorting gap or strict ordering of prime targets is used. -/
theorem eventually_terminalScale_orderedPrefixMoleculeRoot_bounds
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      ∀ a : MoleculeCenter S X (12288 * B),
        |orderedPrefixMoleculeRoot S X (12288 * B) (moleculeCenterRankIndex a) ^ 2 -
          (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ)| ≤
            C * B / Real.log (X : ℝ) ∧
        ((B : ℝ) / 2 ≤ (a.1 : ℝ) → (a.1 : ℕ) ≤ B →
          Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ))) / 8 ≤
            orderedPrefixMoleculeRoot S X (12288 * B) (moleculeCenterRankIndex a) ∧
          orderedPrefixMoleculeRoot S X (12288 * B) (moleculeCenterRankIndex a) ≤
            8 * Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ)))) := by
  obtain ⟨C, hC, herr⟩ := eventually_terminalScale_prefixMolecule_primeCount_error S hS hthetaPos htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [herr, eventually_powerRange_primeCount_scale_bounds S hS htheta,
    eventually_terminalScale_linearError_le_energy htheta hC.le, eventually_gt_atTop 1]
    with X he hp hsmall hX
  intro B hlo hhi a
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < (B : ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hx theta) hL).trans_le hlo
  have hbn : 0 < B := by exact_mod_cast hb
  have haerr := abs_orderedPrefixMoleculeRoot_sq_sub_primeCount_le
    (fun b ↦ (he B hlo hhi b).1.le) (fun b ↦ (he B hlo hhi b).2) a
  refine ⟨haerr, ?_⟩
  intro haLow haHigh
  let mu := Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ)))
  let nu := orderedPrefixMoleculeRoot S X (12288 * B) (moleculeCenterRankIndex a)
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by positivity)
  have hmu2 : mu ^ 2 = (X : ℝ) / (B * Real.log (X : ℝ)) := Real.sq_sqrt (by positivity)
  have hnu : 0 ≤ nu := by
    dsimp only [nu, orderedPrefixMoleculeRoot]
    rw [eigenvalues₀_diagonal_eq_descendingSort
      (complexify_exactMoleculeFamilyRootMatrix_isHermitian S X (12288 * B))
      (fun b : MoleculeCenter S X (12288 * B) ↦ exactPrincipalMoleculeRoot S X b.1)
      (increasingMoleculeCenterOrderIso S X (12288 * B)).toEquiv
      (complexify_exactMoleculeFamilyRootMatrix_eq_diagonal S X (12288 * B))]
    exact (he B hlo hhi _).1.le
  have har : 0 < (a.1 : ℝ) := by exact_mod_cast Vertex.coe_pos a.1
  have ha : InPowerRange theta X (a.1 : ℕ) :=
    ⟨Vertex.coe_pos _, (show (a.1 : ℝ) ≤ B by exact_mod_cast haHigh).trans hhi⟩
  have hpdata := hp a.1 ha
  have hpLow : mu ^ 2 / 8 ≤ (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ) := by
    apply le_trans _ hpdata.1
    rw [hmu2]
    have hha : (a.1 : ℝ) ≤ B := by exact_mod_cast haHigh
    calc
      ((X : ℝ) / (B * Real.log (X : ℝ))) / 8 =
          (X : ℝ) / (8 * B * Real.log (X : ℝ)) := by ring
      _ ≤ _ := by gcongr
  have hpHigh : (allowedPrimeCount S (X / (a.1 : ℕ)) : ℝ) ≤ 24 * mu ^ 2 := by
    apply hpdata.2.trans
    rw [hmu2]
    calc
      12 * (X : ℝ) / ((a.1 : ℝ) * Real.log (X : ℝ)) ≤
          12 * (X : ℝ) / (((B : ℝ) / 2) * Real.log (X : ℝ)) := by gcongr
      _ = _ := by ring
  have hdet : C * B / Real.log (X : ℝ) ≤ mu ^ 2 / 16 := by
    simpa only [hmu2] using hsmall B hbn hhi
  have hd := abs_le.mp (haerr.trans hdet)
  change -(mu ^ 2 / 16) ≤ nu ^ 2 - _ ∧ nu ^ 2 - _ ≤ mu ^ 2 / 16 at hd
  constructor
  · apply (sq_le_sq₀ (by positivity : 0 ≤ mu / 8) hnu).mp
    nlinarith [sq_nonneg mu]
  · apply (sq_le_sq₀ hnu (by positivity : 0 ≤ 8 * mu)).mp
    nlinarith [sq_nonneg mu]


-- Exact private cast adapter reused from FullSpectrumTransfer:19--27.
private theorem assemblyEigenvalues_cast
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) (j : Fin n) :
    hT.eigenvalues rfl (Fin.cast hn.symm j) = hT.eigenvalues hn j := by
  subst n
  rfl

/-- Increasing arithmetic positions, with only the Euclidean dimension cast. -/
def moleculeCenterEigenEquiv (S : Finset ℕ) (X K : ℕ) :
    MoleculeCenter S X K ≃
      Fin (Module.finrank ℂ (EuclideanSpace ℂ (MoleculeCenter S X K))) :=
  (increasingMoleculeCenterOrderIso S X K).symm.toEquiv.trans
    (finCongr finrank_euclideanSpace.symm)

/-- Lifting the prefix spectral index keeps the exact global arithmetic rank. -/
theorem lift_moleculeCenterEigenEquiv_eq {S : Finset ℕ} {X K : ℕ}
    (Q : EuclideanSpace ℂ (MoleculeCenter S X K) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Vertex S X)) (a : MoleculeCenter S X K) :
    liftRCLikeCompressionEigenIndex Q (moleculeCenterEigenEquiv S X K a) =
      Fin.cast finrank_euclideanSpace.symm (oneExitArithmeticRankIndex a.1) := by
  apply Fin.ext
  exact moleculeCenterRankIndex_val a

/-- The actual diagonal operator and its ordered root values agree after
the dimension cast; no permutation of arithmetic labels occurs. -/
theorem eigenvalues_moleculeCenterEigenEquiv_eq {S : Finset ℕ} {X K : ℕ}
    (a : MoleculeCenter S X K) :
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (complexify_exactMoleculeFamilyRootMatrix_isHermitian S X K)).eigenvalues rfl
      (moleculeCenterEigenEquiv S X K a) =
        orderedPrefixMoleculeRoot S X K (moleculeCenterRankIndex a) :=
  assemblyEigenvalues_cast _ _ finrank_euclideanSpace (moleculeCenterRankIndex a)

/-- The ambient one-exit spectrum at a lifted prefix position is the
literal one-exit eigenvalue at that centre's global arithmetic rank. -/
theorem oneExit_eigenvalues_lift_moleculeCenterEigenEquiv_eq
    {S : Finset ℕ} {X K : ℕ}
    (Q : EuclideanSpace ℂ (MoleculeCenter S X K) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Vertex S X)) (a : MoleculeCenter S X K) :
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (oneExitCompression_isHermitian S X)).eigenvalues rfl
      (liftRCLikeCompressionEigenIndex Q (moleculeCenterEigenEquiv S X K a)) =
        oneExitEigenvalueAtArithmeticRank a.1 := by
  rw [lift_moleculeCenterEigenEquiv_eq]
  exact assemblyEigenvalues_cast _ _ finrank_euclideanSpace (oneExitArithmeticRankIndex a.1)

/-- Actual same-rank ordered comparison with quadratic noise mass. The
isometry, Hilbert--Schmidt budget, complement gap and residual absorptions
are produced by R4--R5; none is a hypothesis of this theorem. -/
theorem eventually_terminalScale_oneExit_ordered_comparison
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ H : ℝ, 0 < H ∧ ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      ∃ eps : MoleculeCenter S X (12288 * B) → ℝ,
        (∀ a, 0 ≤ eps a) ∧
        (∑ a, eps a ^ 2 ≤ H * B * Real.log (X : ℝ) ^ 5) ∧
        (∀ a, eps a ≤ matrixL2OperatorNorm
          (whitenedProjectedFullStarFrameResidual S X (12288 * B))) ∧
        ∀ a, (B : ℝ) / 2 ≤ (a.1 : ℝ) → (a.1 : ℕ) ≤ B →
          |oneExitEigenvalueAtArithmeticRank a.1 ^ 2 -
            orderedPrefixMoleculeRoot S X (12288 * B) (moleculeCenterRankIndex a) ^ 2| ≤
            32 * Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ))) * eps a +
              (B : ℝ) / Real.log (X : ℝ) := by
  let theta' := (theta + 1 / 2) / 2
  have ht' : theta' < 1 / 2 := by dsimp [theta']; linarith
  have htt' : theta < theta' := by dsimp [theta']; linarith
  obtain ⟨C, hC, hHSbudget⟩ :=
    eventually_powerRange_whitenedProjectedFullStarFrameResidual_hsSq_le S hS ht'
  obtain ⟨_Cr, _hCr, hroots⟩ :=
    eventually_terminalScale_orderedPrefixMoleculeRoot_bounds S hS hthetaPos htheta
  refine ⟨12288 * C, by positivity, ?_⟩
  filter_upwards [hHSbudget, hroots,
    eventually_powerRange_whitenedProjectedFullStarFrame_linearIsometry S hS ht',
    eventually_terminalScale_oneExit_whitenedComplement_gap S hS hthetaPos htheta,
    eventually_terminalScale_whitenedResidual_small S hS hthetaPos htheta
      (P := 12288) (ε := 1 / 1024) (by norm_num) (by norm_num),
    eventually_powerScale_fixed_mul_le htt' 12288, eventually_gt_atTop 1]
    with X hHS hroots hframe hgap hsmall hprefix hX
  intro B hlo hhi
  let K := 12288 * B
  have hK : (K : ℝ) ≤ powerScale theta' X := by
    simpa only [K, Nat.cast_mul, Nat.cast_ofNat] using hprefix B hhi
  obtain ⟨Q, hQ⟩ := hframe K hK
  let T := Matrix.toEuclideanLin (oneExitCompression S X)
  let D := Matrix.toEuclideanLin (complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K))
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (oneExitCompression_isHermitian S X)
  let hD : D.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (complexify_exactMoleculeFamilyRootMatrix_isHermitian S X K)
  let R := whitenedProjectedFullStarFrameResidual S X K
  let e := matrixL2OperatorNorm R
  let h := matrixFrobeniusNorm R
  let mu := Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ)))
  let r := moleculeCenterEigenEquiv S X K
  let I := Finset.univ.filter fun i ↦
    (B : ℝ) / 2 ≤ ((r.symm i).1 : ℝ) ∧ ((r.symm i).1 : ℕ) ≤ B
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < (B : ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hx theta) hL).trans_le hlo
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by positivity)
  have hmu2 : mu ^ 2 = (X : ℝ) / (B * Real.log (X : ℝ)) := Real.sq_sqrt (by positivity)
  have he : 0 ≤ e := matrixL2OperatorNorm_nonneg _
  have heSmallSq := hsmall B K hlo hhi
    (by simp only [K, Nat.cast_mul, Nat.cast_ofNat]; exact le_rfl)
  have heSmall : e ≤ (1 / 8 : ℝ) * mu / 4 := by
    apply (sq_le_sq₀ he (by positivity)).mp
    have he2 := heSmallSq.2
    change e ^ 2 < (1 / 1024) * _ at he2
    rw [← hmu2] at he2
    nlinarith [he2]
  have hresEq (v) : T (Q v) - Q (D v) = Matrix.toEuclideanLin R v := by
    change (T ∘ₗ Q.toLinearMap - Q.toLinearMap ∘ₗ D) v = _
    rw [hQ]
    simp only [T, D, R, whitenedProjectedFullStarFrameResidual,
      map_sub, Matrix.toLpLin_mul_same, LinearMap.sub_apply, LinearMap.comp_apply]
  have hres (v) : ‖T (Q v) - Q (D v)‖ ≤ e * ‖v‖ := by
    rw [hresEq]
    change ‖(EuclideanSpace.equiv (PrimeStar.Vertex S X) ℂ).symm (R.mulVec v.ofLp)‖ ≤ e * ‖v‖
    simpa only [e, matrixL2OperatorNorm] using R.l2_opNorm_mulVec v
  have hHS' : ∑ i, ‖T (Q (hD.eigenvectorBasis rfl i)) -
      Q (D (hD.eigenvectorBasis rfl i))‖ ^ 2 ≤ h ^ 2 := by
    simp_rw [hresEq]
    have hs := sum_norm_toEuclideanLin_sq_eq_matrixFrobeniusNorm_sq R
      (hD.eigenvectorBasis finrank_euclideanSpace)
    have hcast {n : ℕ} (hn : Module.finrank ℂ (EuclideanSpace ℂ (MoleculeCenter S X K)) = n)
        (j : Fin n) : hD.eigenvectorBasis rfl (Fin.cast hn.symm j) =
          hD.eigenvectorBasis hn j := by
      subst n
      rfl
    calc
      _ = ∑ j : Fin (Fintype.card (MoleculeCenter S X K)),
          ‖Matrix.toEuclideanLin R (hD.eigenvectorBasis rfl
            (Fin.cast finrank_euclideanSpace.symm j))‖ ^ 2 :=
        ((finCongr finrank_euclideanSpace.symm).sum_comp
          (fun i ↦ ‖Matrix.toEuclideanLin R (hD.eigenvectorBasis rfl i)‖ ^ 2)).symm
      _ = h ^ 2 := by
        calc
          _ = ∑ j : Fin (Fintype.card (MoleculeCenter S X K)),
              ‖Matrix.toEuclideanLin R (hD.eigenvectorBasis finrank_euclideanSpace j)‖ ^ 2 :=
            Finset.sum_congr rfl (fun j _ ↦ congrArg
              (fun v ↦ ‖Matrix.toEuclideanLin R v‖ ^ 2) (hcast finrank_euclideanSpace j))
          _ = h ^ 2 := hs
      _ ≤ _ := le_rfl
  have hcomp (y) (hy : Q.toLinearMap.adjoint y = 0) :
      RCLike.re ⟪y, T y⟫_ℂ ≤ ((1 / 8 : ℝ) * mu / 2) * ‖y‖ ^ 2 := by
    rw [hQ] at hy
    have hg := hgap B hlo hhi y hy
    rw [show (1 / 8 : ℝ) * mu / 2 = mu / 16 by ring]
    exact hg
  have hmodel (a) : hD.eigenvalues rfl (r a) =
      orderedPrefixMoleculeRoot S X K (moleculeCenterRankIndex a) :=
    eigenvalues_moleculeCenterEigenEquiv_eq a
  have hwindow (i) (hi : i ∈ I) :
      (1 / 8 : ℝ) * mu ≤ hD.eigenvalues rfl i ∧ hD.eigenvalues rfl i ≤ 8 * mu := by
    obtain ⟨haLow, haHigh⟩ := (Finset.mem_filter.mp hi).2
    have hw := (hroots B hlo hhi (r.symm i)).2 haLow haHigh
    have hm := hmodel (r.symm i)
    rw [r.apply_symm_apply] at hm
    rw [hm]
    simpa only [mu, K, div_eq_mul_inv, one_mul, mul_comm] using hw
  obtain ⟨hmass, hmax, hpoint, _hsq⟩ := ordered_residual_squaredEnergy_comparison
    T hT D hD Q I hmu (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ) ≤ 8) he heSmall hres hHS' hcomp hwindow
  let eps := fun a ↦ |(hT.adjoint_conj Q.toLinearMap).eigenvalues rfl (r a) -
    hD.eigenvalues rfl (r a)|
  refine ⟨eps, fun _ ↦ abs_nonneg _, ?_, fun a ↦ hmax (r a), ?_⟩
  · calc
      ∑ a, eps a ^ 2 = ∑ i,
          ((hT.adjoint_conj Q.toLinearMap).eigenvalues rfl i - hD.eigenvalues rfl i) ^ 2 := by
        simp only [eps, sq_abs]
        exact r.sum_comp (fun i ↦
          ((hT.adjoint_conj Q.toLinearMap).eigenvalues rfl i - hD.eigenvalues rfl i) ^ 2)
      _ ≤ h ^ 2 := hmass
      _ ≤ C * K * Real.log (X : ℝ) ^ 5 := hHS K hK
      _ = _ := by simp only [K, Nat.cast_mul, Nat.cast_ofNat]; ring
  · intro a haLow haHigh
    have hi : r a ∈ I := by
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, r.symm_apply_apply]
      exact ⟨haLow, haHigh⟩
    have hp := (hpoint (r a) hi).2.2
    have hz : hT.eigenvalues rfl (liftRCLikeCompressionEigenIndex Q (r a)) =
        oneExitEigenvalueAtArithmeticRank a.1 :=
      oneExit_eigenvalues_lift_moleculeCenterEigenEquiv_eq Q a
    change |hT.eigenvalues rfl (liftRCLikeCompressionEigenIndex Q (r a)) ^ 2 -
        hD.eigenvalues rfl (r a) ^ 2| ≤
      4 * 8 * mu * eps a + (16 * 8 / (1 / 8)) * e ^ 2 at hp
    conv_lhs at hp => rw [hz, hmodel]
    have he1 := heSmallSq.1
    change e ^ 2 < (1 / 1024) * ((B : ℝ) / Real.log (X : ℝ)) at he1
    change _ ≤ 32 * mu * eps a + (B : ℝ) / Real.log (X : ℝ)
    nlinarith [he1]


/-- The actual allowed centres in the closed dyadic band B/2 ≤ a ≤ B. -/
def dyadicBandCenters (S : Finset ℕ) (X B : ℕ) : Finset (Vertex S X) :=
  Finset.univ.filter fun a ↦ (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B

/-- Literal membership in the dyadic band, with both endpoints retained. -/
@[simp] theorem mem_dyadicBandCenters {S : Finset ℕ} {X B : ℕ} {a : Vertex S X} :
    a ∈ dyadicBandCenters S X B ↔ (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B := by
  simp [dyadicBandCenters]

/-- A dyadic band has at most B allowed centres. -/
theorem card_dyadicBandCenters_le (S : Finset ℕ) (X B : ℕ) :
    (dyadicBandCenters S X B).card ≤ B := by
  have hcard : (dyadicBandCenters S X B).card ≤ (Finset.Icc 1 B).card := by
    apply Finset.card_le_card_of_injOn (fun a : Vertex S X ↦ (a : ℕ))
    · intro a ha
      exact Finset.mem_Icc.mpr ⟨Vertex.coe_pos a, (mem_dyadicBandCenters.mp ha).2⟩
    · intro a _ b _ hab
      exact Subtype.ext (Fin.ext hab)
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hcard

/-- Extending prefix noise by zero preserves its quadratic upper bound on
the actual dyadic band. Every band centre belongs to the complete prefix. -/
theorem sum_dyadicBand_extend_prefix_le
    {S : Finset ℕ} {X B : ℕ} (eps : MoleculeCenter S X (12288 * B) → ℝ) :
    ∑ a ∈ dyadicBandCenters S X B,
      (if ha : (a : ℕ) ≤ 12288 * B then eps ⟨a, ha⟩ else 0) ^ 2 ≤ ∑ a, eps a ^ 2 := by
  let J := Finset.univ.filter fun a : MoleculeCenter S X (12288 * B) ↦
    (B : ℝ) / 2 ≤ (a.1 : ℝ) ∧ (a.1 : ℕ) ≤ B
  have hK (a) (ha : a ∈ dyadicBandCenters S X B) : (a : ℕ) ≤ 12288 * B := by
    have := (mem_dyadicBandCenters.mp ha).2
    omega
  have heq : (∑ a ∈ dyadicBandCenters S X B,
      (if ha : (a : ℕ) ≤ 12288 * B then eps ⟨a, ha⟩ else 0) ^ 2) =
      ∑ b ∈ J, eps b ^ 2 := by
    apply Finset.sum_bij (fun a ha ↦ (⟨a, hK a ha⟩ : MoleculeCenter S X (12288 * B)))
    · intro a ha
      simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and] using mem_dyadicBandCenters.mp ha
    · intro a _ b _ hab
      exact congrArg Subtype.val hab
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      exact ⟨b.1, mem_dyadicBandCenters.mpr hb', Subtype.ext rfl⟩
    · intro a ha
      simp only [dif_pos (hK a ha)]
  rw [heq]
  exact Finset.sum_le_univ_sum_of_nonneg (fun a ↦ sq_nonneg (eps a))

/-- Actual global-rank defect is a deterministic B/log X term plus noise
with mass O(B log^5 X). This includes S1, correction regularity, ordered
comparison and the A-to-G transfer at the same prescribed arithmetic rank. -/
theorem eventually_terminalScale_arithmeticRank_noise_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧ ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      ∃ eps : Vertex S X → ℝ,
        (∀ a, 0 ≤ eps a) ∧
        (∑ a ∈ dyadicBandCenters S X B, eps a ^ 2 ≤ H * B * Real.log (X : ℝ) ^ 5) ∧
        (∀ a, eps a ≤ matrixL2OperatorNorm
          (whitenedProjectedFullStarFrameResidual S X (12288 * B))) ∧
        ∀ a ∈ dyadicBandCenters S X B,
          FirstExitCorrectionRegular S X a ∧
          targetDefect S X a (lambdaAtArithmeticRank a) ≤
            C * B / Real.log (X : ℝ) +
              32 * Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ))) * eps a := by
  obtain ⟨H, hH, hcomp⟩ := eventually_terminalScale_oneExit_ordered_comparison S hS hthetaPos htheta
  obtain ⟨C, hC, hroot⟩ := eventually_terminalScale_orderedPrefixMoleculeRoot_bounds S hS hthetaPos htheta
  let M := powerBandFirstExitCorrectionLogConstant
  let T := 57344 * PrimeStar.sqrtCutoffResidualConstant ^ 4
  have hM : 0 < M := powerBandFirstExitCorrectionLogConstant_pos
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨T + C + M + 1, H, by positivity, hH, ?_⟩
  filter_upwards [hcomp, hroot,
    eventually_powerRange_fullAdjacency_oneExit_sq_comparison S hS htheta,
    eventually_powerRange_firstExitCorrection_le_log S hS htheta,
    eventually_terminalScale_log_sq_le hthetaPos htheta, eventually_gt_atTop 1]
    with X hcomp hroot htransfer hcorrection hlog hX
  intro B hlo hhi
  obtain ⟨eps, heps, hmass, hmax, hpoint⟩ := hcomp B hlo hhi
  let noise := fun a : Vertex S X ↦
    if ha : (a : ℕ) ≤ 12288 * B then eps ⟨a, ha⟩ else 0
  refine ⟨noise, ?_, (sum_dyadicBand_extend_prefix_le eps).trans hmass, ?_, ?_⟩
  · intro a
    dsimp [noise]
    split_ifs with ha
    · exact heps _
    · exact le_rfl
  · intro a
    dsimp [noise]
    split_ifs with ha
    · exact hmax _
    · exact matrixL2OperatorNorm_nonneg _
  · intro a ha
    obtain ⟨haLow, haHigh⟩ := mem_dyadicBandCenters.mp ha
    have haK : (a : ℕ) ≤ 12288 * B := by omega
    let b : MoleculeCenter S X (12288 * B) := ⟨a, haK⟩
    have hnoise : noise a = eps b := by simp only [noise, dif_pos haK, b]
    have haPow : InPowerRange theta X (a : ℕ) :=
      ⟨Vertex.coe_pos a, (show (a : ℝ) ≤ B by exact_mod_cast haHigh).trans hhi⟩
    have hc := hcorrection a haPow
    refine ⟨hc.1, ?_⟩
    have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
    have hs := (hroot B hlo hhi b).1
    have hp := hpoint b haLow haHigh
    have ht := htransfer a haPow
    rw [fullAdjacencyEigenvalueAtArithmeticRank_eq_lambdaAtArithmeticRank] at ht
    have hta : |lambdaAtArithmeticRank a ^ 2 - oneExitEigenvalueAtArithmeticRank a ^ 2| ≤
        T * B / Real.log (X : ℝ) := by
      rw [abs_of_nonneg ht.1]
      apply ht.2.trans
      dsimp [T]
      rw [mul_div_assoc]
      gcongr
    have hca : |firstExitCorrection S X a| ≤ M * B / Real.log (X : ℝ) := by
      apply hc.2.trans
      apply (le_div_iff₀ hL).mpr
      nlinarith [mul_le_mul_of_nonneg_left (hlog B hlo hhi) hM.le]
    let nu := orderedPrefixMoleculeRoot S X (12288 * B) (moleculeCenterRankIndex b)
    rw [targetDefect_eq, hnoise]
    change |lambdaAtArithmeticRank a ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
      firstExitCorrection S X a| ≤ _
    calc
      _ = |(lambdaAtArithmeticRank a ^ 2 - oneExitEigenvalueAtArithmeticRank a ^ 2) +
          (oneExitEigenvalueAtArithmeticRank a ^ 2 - nu ^ 2) +
          (nu ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ) - firstExitCorrection S X a)| := by
        congr 1
        ring
      _ ≤ (|lambdaAtArithmeticRank a ^ 2 - oneExitEigenvalueAtArithmeticRank a ^ 2| +
          |oneExitEigenvalueAtArithmeticRank a ^ 2 - nu ^ 2|) +
          (|nu ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ)| +
            |firstExitCorrection S X a|) :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_sub _ _))
      _ ≤ (T * B / Real.log (X : ℝ) +
          (32 * Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ))) * eps b +
            (B : ℝ) / Real.log (X : ℝ))) +
          (C * B / Real.log (X : ℝ) + M * B / Real.log (X : ℝ)) :=
        add_le_add (add_le_add hta hp) (add_le_add hs hca)
      _ = _ := by ring

/-- Ordered mean-square estimate for the actual adjacency eigenvalues at
their prescribed arithmetic ranks. The deterministic term is B³/log² X. -/
theorem eventually_terminalScale_ordered_meanSquare
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      ∑ a ∈ dyadicBandCenters S X B, targetDefect S X a (lambdaAtArithmeticRank a) ^ 2 ≤
        C * X * Real.log (X : ℝ) ^ 5 + C * (B : ℝ) ^ 3 / Real.log (X : ℝ) ^ 2 := by
  obtain ⟨C, H, hC, hH, hnoise⟩ :=
    eventually_terminalScale_arithmeticRank_noise_bound S hS hthetaPos htheta
  let C' := 2 * C ^ 2 + 2048 * H
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C', hC', ?_⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnoise, hlog.eventually_ge_atTop 1, eventually_gt_atTop 1]
    with X hn hlog hX
  intro B hlo hhi
  obtain ⟨eps, heps, hmass, _hmax, hpoint⟩ := hn B hlo hhi
  let L := Real.log (X : ℝ)
  let mu := Real.sqrt ((X : ℝ) / (B * L))
  have hL : 0 < L := by dsimp [L]; linarith
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hb : 0 < (B : ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hx theta) hL).trans_le hlo
  have hmu : 0 ≤ mu := Real.sqrt_nonneg _
  have hmu2 : mu ^ 2 = (X : ℝ) / (B * L) := Real.sq_sqrt (by positivity)
  have hfinite : ∑ a ∈ dyadicBandCenters S X B,
      targetDefect S X a (lambdaAtArithmeticRank a) ^ 2 ≤
      (dyadicBandCenters S X B).card * (2 * (C * B / L) ^ 2) +
        2048 * mu ^ 2 * ∑ a ∈ dyadicBandCenters S X B, eps a ^ 2 := by
    calc
      _ ≤ ∑ a ∈ dyadicBandCenters S X B,
          (2 * (C * B / L) ^ 2 + 2048 * mu ^ 2 * eps a ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        have hp := (hpoint a ha).2
        have hea := heps a
        have hd : 0 ≤ targetDefect S X a (lambdaAtArithmeticRank a) := abs_nonneg _
        have hs := (sq_le_sq₀ hd (by positivity : 0 ≤ C * B / L + 32 * mu * eps a)).mpr hp
        nlinarith only [hs, sq_nonneg (C * B / L - 32 * mu * eps a)]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
  have hcard : ((dyadicBandCenters S X B).card : ℝ) ≤ B :=
    Nat.cast_le.mpr (card_dyadicBandCenters_le S X B)
  have h45 : L ^ 4 ≤ L ^ 5 := by
    calc
      L ^ 4 ≤ L ^ 4 * L := le_mul_of_one_le_right (pow_nonneg hL.le _) hlog
      _ = L ^ 5 := by ring
  calc
    _ ≤ (B : ℝ) * (2 * (C * B / L) ^ 2) + 2048 * mu ^ 2 * (H * B * L ^ 5) := by
      apply hfinite.trans
      exact add_le_add (mul_le_mul_of_nonneg_right hcard (by positivity))
        (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = 2 * C ^ 2 * (B : ℝ) ^ 3 / L ^ 2 + 2048 * H * X * L ^ 4 := by
      rw [hmu2]
      field_simp
    _ ≤ C' * (B : ℝ) ^ 3 / L ^ 2 + C' * X * L ^ 5 := by
      apply add_le_add
      · gcongr
        dsimp [C']
        nlinarith [sq_nonneg C]
      · apply mul_le_mul
        · gcongr
          dsimp [C']
          nlinarith [sq_nonneg C]
        · exact h45
        · positivity
        · positivity
    _ = _ := by ring

/-- Quantitative tail at every positive threshold, with the deterministic
B/log X term separated from Markov noise. The defect uses the actual full
adjacency eigenvalue at the prescribed arithmetic rank. -/
theorem eventually_terminalScale_ordered_tail
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ C₀ C₁ C₂ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
        powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
        (B : ℝ) ≤ powerScale theta X → ∀ t : ℝ, 0 < t →
        (((dyadicBandCenters S X B).filter fun a ↦
          C₀ * B / Real.log (X : ℝ) +
            C₁ * t * Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ))) <
              targetDefect S X a (lambdaAtArithmeticRank a)).card : ℝ) ≤
          C₂ * B * Real.log (X : ℝ) ^ 5 / t ^ 2 := by
  obtain ⟨C, H, hC, hH, hnoise⟩ :=
    eventually_terminalScale_arithmeticRank_noise_bound S hS hthetaPos htheta
  refine ⟨C, 32, H, hC, by norm_num, hH, ?_⟩
  filter_upwards [hnoise, eventually_gt_atTop 1] with X hn hX
  intro B hlo hhi t ht
  obtain ⟨eps, heps, hmass, _hmax, hpoint⟩ := hn B hlo hhi
  let L := Real.log (X : ℝ)
  let mu := Real.sqrt ((X : ℝ) / (B * L))
  let bad := (dyadicBandCenters S X B).filter fun a ↦
    C * B / L + 32 * t * mu < targetDefect S X a (lambdaAtArithmeticRank a)
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < (B : ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hx theta) hL).trans_le hlo
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by positivity)
  have hlarge (a) (ha : a ∈ bad) : t < eps a := by
    obtain ⟨haBand, haBad⟩ := Finset.mem_filter.mp ha
    have hp := (hpoint a haBand).2
    change C * B / L + 32 * t * mu < _ at haBad
    change _ ≤ C * B / L + 32 * mu * eps a at hp
    nlinarith
  have hmarkov : (bad.card : ℝ) * t ^ 2 ≤ ∑ a ∈ bad, eps a ^ 2 := by
    simpa only [nsmul_eq_mul] using bad.card_nsmul_le_sum (fun a ↦ eps a ^ 2) (t ^ 2)
      (fun a ha ↦ (sq_le_sq₀ ht.le (heps a)).mpr (hlarge a ha).le)
  have hsub : ∑ a ∈ bad, eps a ^ 2 ≤ H * B * L ^ 5 := by
    apply le_trans _ hmass
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro a _ _
    exact sq_nonneg _
  exact (le_div_iff₀ (sq_pos_of_pos ht)).mpr (hmarkov.trans hsub)

/-- Dyadic budgets sum geometrically on every integer prefix. The lower
half and the closed upper band cover the cutoff, including midpoint ties. -/
theorem card_prefix_le_two_mul_of_dyadic {S : Finset ℕ} {X : ℕ}
    (s : Finset (Vertex S X)) {u : ℝ} (hu : 0 ≤ u) :
    ∀ N : ℕ,
      (∀ B : ℕ, B ≤ N →
        ((s.filter fun a : Vertex S X ↦ (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B).card : ℝ) ≤ u * B) →
      ((s.filter fun a : Vertex S X ↦ (a : ℕ) ≤ N).card : ℝ) ≤ 2 * u * N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hband
    by_cases hN : N = 0
    · subst N
      have he : (s.filter fun a : Vertex S X ↦ (a : ℕ) ≤ 0) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have := (Finset.mem_filter.mp ha).2
        have := Vertex.coe_pos a
        omega
      simp only [he, Finset.card_empty, Nat.cast_zero, mul_zero, le_refl]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      have hhalf := ih (N / 2) (Nat.div_lt_self hNpos (by norm_num))
        (fun B hB ↦ hband B (hB.trans (Nat.div_le_self _ _)))
      have hcover : (s.filter fun a : Vertex S X ↦ (a : ℕ) ≤ N) ⊆
          (s.filter fun a : Vertex S X ↦ (a : ℕ) ≤ N / 2) ∪
            (s.filter fun a : Vertex S X ↦ (N : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ N) := by
        intro a ha
        obtain ⟨has, haN⟩ := Finset.mem_filter.mp ha
        by_cases hah : (a : ℕ) ≤ N / 2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨has, hah⟩)
        · have hnat : N < (a : ℕ) * 2 := by omega
          have hreal : (N : ℝ) < (a : ℝ) * 2 := by exact_mod_cast hnat
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨has, by linarith, haN⟩)
      have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
      have hhalfReal : (N / 2 : ℕ) * (2 : ℝ) ≤ N := by
        exact_mod_cast Nat.div_mul_le_self N 2
      calc
        _ ≤ ((s.filter fun a : Vertex S X ↦ (a : ℕ) ≤ N / 2).card : ℝ) +
            ((s.filter fun a : Vertex S X ↦ (N : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ N).card : ℝ) := by
          exact_mod_cast hcount
        _ ≤ 2 * u * (N / 2 : ℕ) + u * N := add_le_add hhalf (hband N le_rfl)
        _ ≤ 2 * u * N := by nlinarith [mul_le_mul_of_nonneg_left hhalfReal hu]

/-- The actual allowed vertices below a real cutoff have at most its floor
plus one elements, independently of which primes have been deleted. -/
theorem card_lt_realCutoff_le {S : Finset ℕ} {X : ℕ}
    (s : Finset (Vertex S X)) {c : ℝ} (hc : 0 ≤ c) :
    ((s.filter fun a : Vertex S X ↦ (a : ℝ) < c).card : ℝ) ≤ c + 1 := by
  have hcard : (s.filter fun a : Vertex S X ↦ (a : ℝ) < c).card ≤ ⌊c⌋₊ + 1 := by
    rw [show ⌊c⌋₊ + 1 = (Finset.range (⌊c⌋₊ + 1)).card by simp]
    apply Finset.card_le_card_of_injOn (fun a : Vertex S X ↦ (a : ℕ))
    · intro a ha
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (Finset.mem_filter.mp ha).2.le))
    · intro a _ b _ hab
      exact Subtype.ext (Fin.ext hab)
  calc
    _ ≤ (⌊c⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
    _ ≤ c + 1 := add_le_add (Nat.floor_le hc) le_rfl

/-- Any actual exceptional set splits into its explicit initial segment
and its retained upper part, with the initial count kept in the bound. -/
theorem card_le_realCutoff_add_upper {S : Finset ℕ} {X : ℕ}
    (s : Finset (Vertex S X)) {c : ℝ} (hc : 0 ≤ c) :
    (s.card : ℝ) ≤ c + 1 + ((s.filter fun a : Vertex S X ↦ c ≤ (a : ℝ)).card : ℝ) := by
  have hcover : s ⊆ (s.filter fun a : Vertex S X ↦ (a : ℝ) < c) ∪
      (s.filter fun a : Vertex S X ↦ c ≤ (a : ℝ)) := by
    intro a ha
    rcases lt_or_ge (a : ℝ) c with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, h⟩)
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  exact (show (s.card : ℝ) ≤ ((s.filter fun a : Vertex S X ↦ (a : ℝ) < c).card : ℝ) +
    ((s.filter fun a : Vertex S X ↦ c ≤ (a : ℝ)).card : ℝ) by exact_mod_cast hcard).trans
      (add_le_add (card_lt_realCutoff_le s hc) le_rfl)

/-- A sufficiently large natural logarithmic exponent pays any prescribed
positive tail rate without changing its comparison constants. -/
theorem log_fifth_div_pow_sq_le_inv_rpow {L R : ℝ} (hL : 1 ≤ L)
    (D : ℕ) (hD : R + 5 ≤ 2 * (D : ℝ)) :
    L ^ 5 / (L ^ D) ^ 2 ≤ 1 / L ^ R := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow := Real.rpow_le_rpow_of_exponent_le hL hD
  have he : L ^ (R + 5) = L ^ R * L ^ 5 := by
    rw [Real.rpow_add hLp]
    norm_num
  have he' : L ^ (2 * (D : ℝ)) = (L ^ D) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hLp.le, Real.rpow_natCast, Real.rpow_two]
  rw [he, he'] at hpow
  apply (div_le_div_iff₀ (sq_pos_of_pos (pow_pos hLp D)) (Real.rpow_pos_of_pos hLp R)).mpr
  nlinarith

/-- A strict power margin absorbs each fixed natural power of the logarithm. -/
theorem eventually_log_pow_mul_rpow_le (D : ℕ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ D * (X : ℝ) ^ p ≤ (X : ℝ) ^ q := by
  have h := tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero (D : ℝ) hpq
  filter_upwards [h.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop 0] with X hsmall hX
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  rw [Real.rpow_natCast] at hsmall
  simpa only [one_mul] using ((div_lt_iff₀ (Real.rpow_pos_of_pos hx q)).mp hsmall).le

/-- The actual terminal failure count has any prescribed logarithmic rate.
The logarithmic error exponent is chosen after that rate. -/
theorem eventually_terminalPowerBand_badCenters_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) (R : ℝ) :
    ∃ D : ℕ, ∃ C Cexc : ℝ, 0 < C ∧ 0 < Cexc ∧
      ∀ᶠ X : ℕ in atTop,
        ((terminalPowerBandBadCenters S theta C D X).card : ℝ) ≤
          Cexc * powerScale theta X / Real.log (X : ℝ) ^ R := by
  obtain ⟨C₀, C₁, C₂, hC₀, hC₁, hC₂, htail⟩ :=
    eventually_terminalScale_ordered_tail S hS hthetaPos htheta
  obtain ⟨D, hD⟩ := exists_nat_ge (R + 5)
  have hD' : R + 5 ≤ 2 * (D : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) D]
  let C := 2 * C₀ + C₁
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨D, C, 2 * C₂, hC, by positivity, ?_⟩
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htail, eventually_powerRange_firstExitCorrection_le_log S hS htheta,
    hlogTop.eventually_ge_atTop 1, eventually_gt_atTop 1]
    with X ht hc hlog hX
  let L := Real.log (X : ℝ)
  let A := powerScale theta X
  let N := ⌊A⌋₊
  let s := terminalPowerBandBadCenters S theta C D X
  have hL : 0 < L := by dsimp [L]; linarith
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hA : 0 < A := Real.rpow_pos_of_pos hx theta
  have hN : (N : ℝ) ≤ A := Nat.floor_le hA.le
  have hsN : (s.filter fun a : Vertex S X ↦ (a : ℕ) ≤ N) = s := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    exact Nat.le_floor (Finset.mem_filter.mp ha).2.2.2
  have hband (B : ℕ) (hBN : B ≤ N) :
      ((s.filter fun a : Vertex S X ↦ (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B).card : ℝ) ≤
        (C₂ / L ^ R) * B := by
    have hBhi : (B : ℝ) ≤ powerScale theta X := (Nat.cast_le.mpr hBN).trans hN
    by_cases hlo : A / L ≤ (B : ℝ)
    · have hsub : (s.filter fun a : Vertex S X ↦ (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B) ⊆
          (dyadicBandCenters S X B).filter fun a : Vertex S X ↦
            C₀ * B / L + C₁ * L ^ D * Real.sqrt ((X : ℝ) / (B * L)) <
              targetDefect S X a (lambdaAtArithmeticRank a) := by
        intro a ha
        obtain ⟨has, haLow, haHigh⟩ := Finset.mem_filter.mp ha
        obtain ⟨haBad, _haTerminal⟩ := Finset.mem_filter.mp has
        obtain ⟨_haUniv, haPower, haFail⟩ := Finset.mem_filter.mp haBad
        have hreg := (hc a haPower).1
        have haLarge : C * powerBandErrorScale D X (a : ℕ) <
            targetDefect S X a (lambdaAtArithmeticRank a) := by
          rcases haFail with hbad | hlarge
          · exact (hbad hreg).elim
          · rw [targetDefect_eq]
            change C * powerBandErrorScale D X (a : ℕ) <
              |lambdaAtArithmeticRank a ^ 2 - (allowedPrimeCount S (X / (a : ℕ)) : ℝ) -
                firstExitCorrection S X a|
            exact hlarge
        have har : 0 < (a : ℝ) := by exact_mod_cast Vertex.coe_pos a
        have haB : (a : ℝ) ≤ B := Nat.cast_le.mpr haHigh
        have hmu : Real.sqrt ((X : ℝ) / (B * L)) ≤
            Real.sqrt ((X : ℝ) / ((a : ℝ) * L)) := by
          apply Real.sqrt_le_sqrt
          exact div_le_div_of_nonneg_left hx.le (mul_pos har hL)
            (mul_le_mul_of_nonneg_right haB hL.le)
        have hdet : C₀ * B / L ≤ (2 * C₀) * ((a : ℝ) / L) := by
          have hh : (B : ℝ) ≤ 2 * (a : ℝ) := by linarith
          have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC₀.le) hL.le
          calc
            _ ≤ C₀ * (2 * (a : ℝ)) / L := hm
            _ = _ := by ring
        have hCleft : 2 * C₀ ≤ C := by dsimp [C]; linarith
        have hCright : C₁ ≤ C := by dsimp [C]; linarith
        have hscale : C₀ * B / L + C₁ * L ^ D * Real.sqrt ((X : ℝ) / (B * L)) ≤
            C * powerBandErrorScale D X (a : ℕ) := by
          calc
            _ ≤ (2 * C₀) * ((a : ℝ) / L) +
                C₁ * (L ^ D * Real.sqrt ((X : ℝ) / ((a : ℝ) * L))) := by
              apply add_le_add hdet
              simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmu
                (mul_nonneg hC₁.le (pow_nonneg hL.le D))
            _ ≤ C * ((a : ℝ) / L) +
                C * (L ^ D * Real.sqrt ((X : ℝ) / ((a : ℝ) * L))) :=
              add_le_add (mul_le_mul_of_nonneg_right hCleft (by positivity))
                (mul_le_mul_of_nonneg_right hCright (by positivity))
            _ = _ := by dsimp [powerBandErrorScale, L]; ring
        exact Finset.mem_filter.mpr ⟨mem_dyadicBandCenters.mpr ⟨haLow, haHigh⟩,
          hscale.trans_lt haLarge⟩
      have hcount := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (ht B hlo hBhi (L ^ D) (pow_pos hL D))
      calc
        _ ≤ C₂ * B * L ^ 5 / (L ^ D) ^ 2 := hcount
        _ = (C₂ * B) * (L ^ 5 / (L ^ D) ^ 2) := by ring
        _ ≤ (C₂ * B) * (1 / L ^ R) :=
          mul_le_mul_of_nonneg_left (log_fifth_div_pow_sq_le_inv_rpow hlog D hD') (by positivity)
        _ = _ := by ring
    · have he : (s.filter fun a : Vertex S X ↦ (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro a ha hab
        have hat := (Finset.mem_filter.mp ha).2
        exact hlo (hat.2.1.trans (Nat.cast_le.mpr hab.2))
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
  have hcount := card_prefix_le_two_mul_of_dyadic s
    (show 0 ≤ C₂ / L ^ R by positivity) N hband
  rw [hsN] at hcount
  calc
    _ ≤ 2 * (C₂ / L ^ R) * N := hcount
    _ ≤ 2 * (C₂ / L ^ R) * A := mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by dsimp [A, L]; ring

/-- The full failure count keeps the omitted initial segment separate from
the terminal failures, with the same comparison constant and exponent. -/
theorem card_powerBandBadCenters_le_initial_add_terminal
    (S : Finset ℕ) (theta C : ℝ) (D X : ℕ)
    (hcut : 0 ≤ powerScale theta X / Real.log (X : ℝ)) :
    ((powerBandBadCenters S theta C D X).card : ℝ) ≤
      powerScale theta X / Real.log (X : ℝ) + 1 +
        ((terminalPowerBandBadCenters S theta C D X).card : ℝ) := by
  have he : ((powerBandBadCenters S theta C D X).filter fun a : Vertex S X ↦
      powerScale theta X / Real.log (X : ℝ) ≤ (a : ℝ)) =
        terminalPowerBandBadCenters S theta C D X := by
    ext a
    constructor
    · intro ha
      obtain ⟨hab, hal⟩ := Finset.mem_filter.mp ha
      have hap := (Finset.mem_filter.mp hab).2.1
      exact Finset.mem_filter.mpr ⟨hab, hap.1, hal, hap.2⟩
    · intro ha
      obtain ⟨hab, hat⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hab, hat.2.1⟩
  have h := card_le_realCutoff_add_upper (powerBandBadCenters S theta C D X) hcut
  rw [he] at h
  exact h

/-- A positive terminal logarithmic rate implies the full density-zero
conclusion after accounting for the explicit initial segment. -/
theorem tendsto_powerBandBadDensity_zero_of_terminal_bound
    (S : Finset ℕ) {theta C Cexc R : ℝ} (D : ℕ)
    (htheta : 0 < theta) (hR : 0 < R)
    (hbound : ∀ᶠ X : ℕ in atTop,
      ((terminalPowerBandBadCenters S theta C D X).card : ℝ) ≤
        Cexc * powerScale theta X / Real.log (X : ℝ) ^ R) :
    Tendsto (powerBandBadDensity S theta C D) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA : Tendsto (fun X : ℕ ↦ powerScale theta X) atTop atTop :=
    (tendsto_rpow_atTop htheta).comp tendsto_natCast_atTop_atTop
  have hlogInv : Tendsto (fun X : ℕ ↦ 1 / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  have hAInv : Tendsto (fun X : ℕ ↦ 1 / powerScale theta X) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hA
  have hRInv : Tendsto (fun X : ℕ ↦ 1 / Real.log (X : ℝ) ^ R) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop hR).comp hlog)
  apply squeeze_zero' (Eventually.of_forall fun X ↦
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg X) theta))
  · filter_upwards [hbound, eventually_gt_atTop 1] with X hb hX
    have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
    have hAp : 0 < powerScale theta X := Real.rpow_pos_of_pos hx theta
    have hc := (card_powerBandBadCenters_le_initial_add_terminal S theta C D X
      (div_pos hAp hL).le).trans (add_le_add le_rfl hb)
    calc
      _ ≤ (powerScale theta X / Real.log (X : ℝ) + 1 +
          Cexc * powerScale theta X / Real.log (X : ℝ) ^ R) / powerScale theta X :=
        div_le_div_of_nonneg_right hc hAp.le
      _ = 1 / Real.log (X : ℝ) + 1 / powerScale theta X +
          Cexc * (1 / Real.log (X : ℝ) ^ R) := by field_simp
  · simpa using (hlogInv.add hAInv).add (hRInv.const_mul Cexc)

/-- On the retained terminal interval the root-energy scale is bounded by
the power determined by its lower arithmetic endpoint. -/
theorem rootScale_le_of_terminalPowerBand {theta : ℝ} {X a : ℕ}
    (hX : 1 < X) (ha : InTerminalPowerBand theta X a) :
    Real.sqrt ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ))) ≤
      (X : ℝ) ^ ((1 - theta) / 2) := by
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hA : 0 < powerScale theta X := Real.rpow_pos_of_pos hx theta
  have hden : powerScale theta X ≤ (a : ℝ) * Real.log (X : ℝ) :=
    (div_le_iff₀ hL).mp ha.2.1
  calc
    _ ≤ Real.sqrt ((X : ℝ) / powerScale theta X) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hx.le hA hden)
    _ = Real.sqrt ((X : ℝ) ^ (1 - theta)) := by
      rw [Real.rpow_sub hx, Real.rpow_one, powerScale]
    _ = (X : ℝ) ^ ((1 - theta) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
      congr 1
      ring

/-- The two D31 error terms fit every strict sub-block margin on the
terminal range; no false uniform assertion is made near the initial centre. -/
theorem eventually_terminalPowerBand_errorScale_le_power
    (D : ℕ) {theta delta : ℝ} (hdelta : delta < subBlockMargin theta) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ℕ, InTerminalPowerBand theta X a →
      powerBandErrorScale D X a ≤ 2 * (X : ℝ) ^ (1 / 2 - delta) := by
  have hd := lt_min_iff.mp hdelta
  have hp : theta < 1 / 2 - delta := by linarith [hd.2]
  have hq : (1 - theta) / 2 < 1 / 2 - delta := by linarith [hd.1]
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_pow_mul_rpow_le 0 hp,
    eventually_log_pow_mul_rpow_le D hq, hlogTop.eventually_ge_atTop 1,
    eventually_gt_atTop 1] with X hpX hqX hL hX
  intro a ha
  have hfirst : (a : ℝ) / Real.log (X : ℝ) ≤ (X : ℝ) ^ (1 / 2 - delta) := by
    apply (div_le_self (Nat.cast_nonneg a) hL).trans
    apply ha.2.2.trans
    simpa only [pow_zero, one_mul, powerScale] using hpX
  have hsecond : Real.log (X : ℝ) ^ D *
      Real.sqrt ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ))) ≤
        (X : ℝ) ^ (1 / 2 - delta) :=
    (mul_le_mul_of_nonneg_left (rootScale_le_of_terminalPowerBand hX ha)
      (pow_nonneg (by linarith) D)).trans hqX
  dsimp [powerBandErrorScale]
  linarith

/-- The actual sub-block failure set has density zero for each strict
positive margin. Its small initial segment is retained in the counting proof. -/
theorem almostAll_subBlock_of_ordered_tail
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2)
    {delta : ℝ} (hdelta : delta < subBlockMargin theta) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (subBlockBadDensity S theta delta C) atTop (𝓝 0) := by
  obtain ⟨D, C, Cexc, hC, _hCexc, hterminal⟩ :=
    eventually_terminalPowerBand_badCenters_le S hS hthetaPos htheta 1
  have hmain := tendsto_powerBandBadDensity_zero_of_terminal_bound S D hthetaPos
    (by norm_num : (0 : ℝ) < 1) hterminal
  refine ⟨2 * C, by positivity, ?_⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA : Tendsto (fun X : ℕ ↦ powerScale theta X) atTop atTop :=
    (tendsto_rpow_atTop hthetaPos).comp tendsto_natCast_atTop_atTop
  have hlogInv : Tendsto (fun X : ℕ ↦ 1 / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  have hAInv : Tendsto (fun X : ℕ ↦ 1 / powerScale theta X) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hA
  apply squeeze_zero' (Eventually.of_forall fun X ↦
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg X) theta))
  · filter_upwards [eventually_terminalPowerBand_errorScale_le_power D hdelta,
      eventually_gt_atTop 1] with X hscale hX
    have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
    have hAp : 0 < powerScale theta X := Real.rpow_pos_of_pos hx theta
    have hsub : ((subBlockBadCenters S theta delta (2 * C) X).filter fun a : Vertex S X ↦
        powerScale theta X / Real.log (X : ℝ) ≤ (a : ℝ)) ⊆
          powerBandBadCenters S theta C D X := by
      intro a ha
      obtain ⟨hab, hal⟩ := Finset.mem_filter.mp ha
      obtain ⟨_haUniv, hap, hbad⟩ := Finset.mem_filter.mp hab
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ a, hap, ?_⟩
      rcases hbad with hirreg | hlarge
      · exact Or.inl hirreg
      · right
        have hs := mul_le_mul_of_nonneg_left (hscale (a : ℕ) ⟨hap.1, hal, hap.2⟩) hC.le
        have he : C * powerBandErrorScale D X (a : ℕ) ≤
            (2 * C) * (X : ℝ) ^ (1 / 2 - delta) := by
          nlinarith [hs]
        exact he.trans_lt hlarge
    have hc := (card_le_realCutoff_add_upper (subBlockBadCenters S theta delta (2 * C) X)
      (div_pos hAp hL).le).trans (add_le_add le_rfl (Nat.cast_le.mpr (Finset.card_le_card hsub)))
    calc
      _ ≤ (powerScale theta X / Real.log (X : ℝ) + 1 +
          ((powerBandBadCenters S theta C D X).card : ℝ)) / powerScale theta X :=
        div_le_div_of_nonneg_right hc hAp.le
      _ = 1 / Real.log (X : ℝ) + 1 / powerScale theta X +
          powerBandBadDensity S theta C D X := by
        dsimp [powerBandBadDensity]
        field_simp
  · simpa using (hlogInv.add hAInv).add hmain

/-- The sharp dyadic threshold has an explicit quadratic tail budget.
Its density payoff is obtained when the power exponent exceeds one third. -/
theorem eventually_terminalScale_sharp_tail
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      (((dyadicBandCenters S X B).filter fun a : Vertex S X ↦
        C * B / Real.log (X : ℝ) < targetDefect S X a (lambdaAtArithmeticRank a)).card : ℝ) ≤
          K * X * Real.log (X : ℝ) ^ 6 / (B : ℝ) ^ 2 := by
  obtain ⟨C₀, C₁, C₂, hC₀, hC₁, hC₂, htail⟩ :=
    eventually_terminalScale_ordered_tail S hS hthetaPos htheta
  refine ⟨C₀ + C₁, C₂, by positivity, hC₂, ?_⟩
  filter_upwards [htail, eventually_gt_atTop 1] with X ht hX
  intro B hlo hhi
  let L := Real.log (X : ℝ)
  let mu := Real.sqrt ((X : ℝ) / (B * L))
  let t := (B : ℝ) / (mu * L)
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < (B : ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hx theta) hL).trans_le hlo
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by positivity)
  have hmu2 : mu ^ 2 = (X : ℝ) / (B * L) := Real.sq_sqrt (by positivity)
  have htpos : 0 < t := div_pos hb (mul_pos hmu hL)
  have hthreshold : C₀ * B / L + C₁ * t * mu = (C₀ + C₁) * B / L := by
    dsimp [t]
    field_simp
  have hp := ht B hlo hhi t htpos
  change (((dyadicBandCenters S X B).filter fun a : Vertex S X ↦
    C₀ * B / L + C₁ * t * mu < targetDefect S X a (lambdaAtArithmeticRank a)).card : ℝ) ≤
      C₂ * B * L ^ 5 / t ^ 2 at hp
  rw [hthreshold] at hp
  apply hp.trans_eq
  dsimp [t]
  rw [div_pow, mul_pow, hmu2]
  dsimp [L]
  field_simp

/-- Actual failures of the sharp a/log X estimate in the full power range,
including irregular finite corrections. -/
def sharpPowerBandBadCenters (S : Finset ℕ) (theta C : ℝ) (X : ℕ) :
    Finset (Vertex S X) :=
  Finset.univ.filter fun a : Vertex S X ↦
    InPowerRange theta X (a : ℕ) ∧
      (¬FirstExitCorrectionRegular S X a ∨
        C * (a : ℝ) / Real.log (X : ℝ) < targetDefect S X a (lambdaAtArithmeticRank a))

/-- Above exponent one third, the literal sharp-error failures have density
zero. The full count retains the initial segment omitted by dyadic control. -/
theorem almostAll_sharpPowerBand
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaLow : 1 / 3 < theta) (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun X : ℕ ↦ ((sharpPowerBandBadCenters S theta C X).card : ℝ) /
        powerScale theta X) atTop (𝓝 0) := by
  have hthetaPos : 0 < theta := by linarith
  obtain ⟨C, K, hC, hK, htail⟩ := eventually_terminalScale_sharp_tail S hS hthetaPos htheta
  refine ⟨2 * C, by positivity, ?_⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA : Tendsto (fun X : ℕ ↦ powerScale theta X) atTop atTop :=
    (tendsto_rpow_atTop hthetaPos).comp tendsto_natCast_atTop_atTop
  have hlogInv : Tendsto (fun X : ℕ ↦ 1 / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  have hAInv : Tendsto (fun X : ℕ ↦ 1 / powerScale theta X) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hA
  have huLimit : Tendsto (fun X : ℕ ↦
      K * X * Real.log (X : ℝ) ^ 9 / powerScale theta X ^ 3) atTop (𝓝 0) := by
    have hr := tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero (9 : ℝ)
      (show (1 : ℝ) < 3 * theta by linarith)
    have hrK := hr.const_mul K
    rw [mul_zero] at hrK
    refine hrK.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hx : 0 < (X : ℝ) := by exact_mod_cast hX
    have he : powerScale theta X ^ 3 = (X : ℝ) ^ (3 * theta) := by
      rw [powerScale, show 3 * theta = theta * 3 by ring,
        Real.rpow_mul hx.le]
      norm_num only [Real.rpow_ofNat]
    rw [Real.rpow_ofNat, Real.rpow_one, ← he]
    ring
  have hmajorant : Tendsto (fun X : ℕ ↦ 1 / Real.log (X : ℝ) +
      1 / powerScale theta X +
      2 * (K * X * Real.log (X : ℝ) ^ 9 / powerScale theta X ^ 3)) atTop (𝓝 0) := by
    simpa using (hlogInv.add hAInv).add (huLimit.const_mul 2)
  refine squeeze_zero' (Eventually.of_forall fun X ↦
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg X) theta)) ?_ hmajorant
  · filter_upwards [htail, eventually_powerRange_firstExitCorrection_le_log S hS htheta,
      eventually_gt_atTop 1] with X ht hc hX
    let L := Real.log (X : ℝ)
    let A := powerScale theta X
    let N := ⌊A⌋₊
    let bad := sharpPowerBandBadCenters S theta (2 * C) X
    let s := bad.filter fun a : Vertex S X ↦ A / L ≤ (a : ℝ)
    let u := K * X * L ^ 9 / A ^ 3
    have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hL : 0 < L := Real.log_pos (by exact_mod_cast hX)
    have hAp : 0 < A := Real.rpow_pos_of_pos hx theta
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hN : (N : ℝ) ≤ A := Nat.floor_le hAp.le
    have hsN : (s.filter fun a : Vertex S X ↦ (a : ℕ) ≤ N) = s := by
      apply Finset.filter_eq_self.mpr
      intro a ha
      exact Nat.le_floor (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.1.2
    have hband (B : ℕ) (hBN : B ≤ N) :
        ((s.filter fun a : Vertex S X ↦ (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B).card : ℝ) ≤
          u * B := by
      have hBhi : (B : ℝ) ≤ powerScale theta X := (Nat.cast_le.mpr hBN).trans hN
      by_cases hlo : A / L ≤ (B : ℝ)
      · have hb : 0 < (B : ℝ) := (div_pos hAp hL).trans_le hlo
        have hsub : (s.filter fun a : Vertex S X ↦
            (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B) ⊆
              (dyadicBandCenters S X B).filter fun a : Vertex S X ↦
                C * B / L < targetDefect S X a (lambdaAtArithmeticRank a) := by
          intro a ha
          obtain ⟨has, haLow, haHigh⟩ := Finset.mem_filter.mp ha
          obtain ⟨hab, _hal⟩ := Finset.mem_filter.mp has
          obtain ⟨_haUniv, hap, hbad⟩ := Finset.mem_filter.mp hab
          have hlarge : (2 * C) * (a : ℝ) / L < targetDefect S X a (lambdaAtArithmeticRank a) :=
            hbad.resolve_left (not_not_intro (hc a hap).1)
          have hdet : C * B / L ≤ (2 * C) * (a : ℝ) / L := by
            apply div_le_div_of_nonneg_right _ hL.le
            nlinarith [mul_le_mul_of_nonneg_left
              (show (B : ℝ) ≤ 2 * (a : ℝ) by linarith) hC.le]
          exact Finset.mem_filter.mpr ⟨mem_dyadicBandCenters.mpr ⟨haLow, haHigh⟩,
            hdet.trans_lt hlarge⟩
        have hcount := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (ht B hlo hBhi)
        apply hcount.trans
        have hden : A ≤ (B : ℝ) * L := (div_le_iff₀ hL).mp hlo
        have hpow : A ^ 3 ≤ (B : ℝ) ^ 3 * L ^ 3 := by
          simpa only [mul_pow] using pow_le_pow_left₀ hAp.le hden 3
        have hmul := mul_le_mul_of_nonneg_left hpow
          (show 0 ≤ K * X * L ^ 6 by positivity)
        dsimp [u]
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff₀ (sq_pos_of_pos hb) (pow_pos hAp 3)).mpr
        nlinarith only [hmul]
      · have he : (s.filter fun a : Vertex S X ↦
            (B : ℝ) / 2 ≤ (a : ℝ) ∧ (a : ℕ) ≤ B) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro a ha hab
          exact hlo ((Finset.mem_filter.mp ha).2.trans (Nat.cast_le.mpr hab.2))
        rw [he, Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hu (Nat.cast_nonneg B)
    have hcount := card_prefix_le_two_mul_of_dyadic s hu N hband
    rw [hsN] at hcount
    have hterminal : (s.card : ℝ) ≤ 2 * u * A :=
      hcount.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have hfull := (card_le_realCutoff_add_upper bad (div_pos hAp hL).le).trans
      (add_le_add le_rfl hterminal)
    calc
      _ ≤ (A / L + 1 + 2 * u * A) / A := div_le_div_of_nonneg_right hfull hAp.le
      _ = 1 / L + 1 / A + 2 * u := by
        field_simp

/-- The R4 operator budget controls every retained centre. The coherent
term is retained as X^(1/4) sqrt(a/log X), exactly as in Corollary 10.3. -/
theorem eventually_terminalPowerBand_everyCenter_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∃ D : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : Vertex S X, InTerminalPowerBand theta X (a : ℕ) →
        FirstExitCorrectionRegular S X a ∧
        targetDefect S X a (lambdaAtArithmeticRank a) ≤
          C * ((a : ℝ) / Real.log (X : ℝ) + Real.log (X : ℝ) ^ D *
            (Real.sqrt ((X : ℝ) / ((a : ℝ) * Real.log (X : ℝ))) +
              (X : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt ((a : ℝ) / Real.log (X : ℝ)))) := by
  let theta' := (theta + 1 / 2) / 2
  have htt' : theta < theta' := by dsimp [theta']; linarith
  have ht' : theta' < 1 / 2 := by dsimp [theta']; linarith
  obtain ⟨C₀, H, hC₀, _hH, hnoise⟩ :=
    eventually_terminalScale_arithmeticRank_noise_bound S hS hthetaPos htheta
  obtain ⟨Ce, hCe, hop⟩ :=
    eventually_powerRange_whitenedProjectedFullStarFrameResidual_operatorNorm_sq_le S hS ht'
  let K := 12288 * (Ce + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : Ce ≤ K ^ 2 := by dsimp [K]; nlinarith only [sq_nonneg Ce, hCe]
  have hCPK : Ce * 12288 ^ 2 ≤ K ^ 2 := by dsimp [K]; nlinarith only [sq_nonneg Ce, hCe]
  refine ⟨5, C₀ + 32 * K, by positivity, ?_⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnoise, hop, eventually_powerScale_fixed_mul_le htt' 12288,
    hlog.eventually_ge_atTop 1, eventually_gt_atTop 1] with X hn ho hprefix hLone hX
  intro a ha
  obtain ⟨eps, heps, _hmass, hmax, hpoint⟩ := hn (a : ℕ) ha.2.1 ha.2.2
  have hband : a ∈ dyadicBandCenters S X (a : ℕ) :=
    mem_dyadicBandCenters.mpr ⟨by have := (Nat.cast_nonneg (a : ℕ) : (0 : ℝ) ≤ a); linarith,
      le_rfl⟩
  refine ⟨(hpoint a hband).1, ?_⟩
  let L := Real.log (X : ℝ)
  let mu := Real.sqrt ((X : ℝ) / ((a : ℝ) * L))
  let v := (X : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt ((a : ℝ) / L)
  let e := matrixL2OperatorNorm (whitenedProjectedFullStarFrameResidual S X (12288 * (a : ℕ)))
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := by dsimp [L]; linarith
  have hap : 0 < (a : ℝ) := by exact_mod_cast ha.1
  have hmu : 0 ≤ mu := Real.sqrt_nonneg _
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have he : 0 ≤ e := matrixL2OperatorNorm_nonneg _
  have hmu2 : mu ^ 2 = (X : ℝ) / ((a : ℝ) * L) := Real.sq_sqrt (by positivity)
  have hquarter : ((X : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (X : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.sqrt_eq_rpow]
    norm_num
  have hv2 : v ^ 2 = Real.sqrt (X : ℝ) * (a : ℝ) / L := by
    dsimp [v]
    rw [mul_pow, hquarter, Real.sq_sqrt (div_pos hap hL).le]
    ring
  have hsx : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hx
  have hcoherent : mu ^ 2 * ((a : ℝ) ^ 2 / Real.sqrt (X : ℝ)) = v ^ 2 := by
    rw [hmu2, hv2]
    apply (eq_div_iff hL.ne').mpr
    field_simp
    nlinarith only [Real.sq_sqrt hx.le]
  have hprefixa : ((12288 * (a : ℕ) : ℕ) : ℝ) ≤ powerScale theta' X := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hprefix (a : ℕ) ha.2.2
  have henergy := ho (12288 * (a : ℕ)) hprefixa
  change e ^ 2 ≤ Ce * L ^ 5 * (1 + ((12288 * (a : ℕ) : ℕ) : ℝ) ^ 2 /
    Real.sqrt (X : ℝ)) at henergy
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow] at henergy
  have hscaled : (mu * e) ^ 2 ≤ Ce * L ^ 5 * (mu ^ 2 + 12288 ^ 2 * v ^ 2) := by
    calc
      _ ≤ mu ^ 2 * (Ce * L ^ 5 * (1 + 12288 ^ 2 * (a : ℝ) ^ 2 /
          Real.sqrt (X : ℝ))) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left henergy (sq_nonneg mu)
      _ = _ := by rw [← hcoherent]; ring
  have hscalar : Ce * (mu ^ 2 + 12288 ^ 2 * v ^ 2) ≤ K ^ 2 * (mu + v) ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hCK (sq_nonneg mu)
    have h₂ := mul_le_mul_of_nonneg_right hCPK (sq_nonneg v)
    nlinarith only [h₁, h₂, mul_nonneg (sq_nonneg K) (mul_nonneg hmu hv)]
  have hLpow : L ^ 5 ≤ L ^ 10 := pow_le_pow_right₀ hLone (by omega)
  have hboundSq : (mu * e) ^ 2 ≤ (K * L ^ 5 * (mu + v)) ^ 2 := by
    calc
      _ ≤ L ^ 5 * (Ce * (mu ^ 2 + 12288 ^ 2 * v ^ 2)) := by nlinarith only [hscaled]
      _ ≤ L ^ 5 * (K ^ 2 * (mu + v) ^ 2) :=
        mul_le_mul_of_nonneg_left hscalar (pow_nonneg hL.le 5)
      _ ≤ L ^ 10 * (K ^ 2 * (mu + v) ^ 2) :=
        mul_le_mul_of_nonneg_right hLpow (by positivity)
      _ = _ := by ring
  have hbound : mu * e ≤ K * L ^ 5 * (mu + v) :=
    (sq_le_sq₀ (mul_nonneg hmu he) (by positivity)).mp hboundSq
  calc
    _ ≤ C₀ * (a : ℝ) / L + 32 * mu * eps a := (hpoint a hband).2
    _ ≤ C₀ * (a : ℝ) / L + 32 * mu * e :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmax a) (by positivity))
    _ ≤ C₀ * (a : ℝ) / L + 32 * (K * L ^ 5 * (mu + v)) := by nlinarith only [hbound]
    _ ≤ (C₀ + 32 * K) * ((a : ℝ) / L + L ^ 5 * (mu + v)) := by
      have h₁ : 0 ≤ K * ((a : ℝ) / L) := by positivity
      have h₂ : 0 ≤ C₀ * (L ^ 5 * (mu + v)) := by positivity
      rw [mul_div_assoc]
      nlinarith only [h₁, h₂]

/-- Every strict margin below the Corollary 10.3 endpoint is valid even
relative to the block scale sqrt(X)/log X, with the logarithm retained. -/
theorem eventually_terminalPowerBand_everyCenter_subBlock
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2)
    {delta : ℝ} (hdelta : delta < min (theta / 2) ((1 - 2 * theta) / 4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : Vertex S X, InTerminalPowerBand theta X (a : ℕ) →
        FirstExitCorrectionRegular S X a ∧
        targetDefect S X a (lambdaAtArithmeticRank a) ≤
          C * (X : ℝ) ^ (1 / 2 - delta) / Real.log (X : ℝ) := by
  obtain ⟨D, C, hC, hall⟩ := eventually_terminalPowerBand_everyCenter_bound S hS hthetaPos htheta
  refine ⟨3 * C, by positivity, ?_⟩
  have hd := lt_min_iff.mp hdelta
  have hp : theta < 1 / 2 - delta := by linarith [hd.2]
  have hq : (1 - theta) / 2 < 1 / 2 - delta := by linarith [hd.1]
  have hr : 1 / 4 + theta / 2 < 1 / 2 - delta := by linarith [hd.2]
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hall, eventually_log_pow_mul_rpow_le 0 hp,
    eventually_log_pow_mul_rpow_le (D + 1) hq,
    eventually_log_pow_mul_rpow_le (D + 1) hr,
    hlog.eventually_ge_atTop 1, eventually_gt_atTop 1] with X haX hpX hqX hrX hLone hX
  intro a ha
  refine ⟨(haX a ha).1, ?_⟩
  let L := Real.log (X : ℝ)
  let mu := Real.sqrt ((X : ℝ) / ((a : ℝ) * L))
  let v := (X : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt ((a : ℝ) / L)
  let q := (X : ℝ) ^ (1 / 2 - delta)
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := by dsimp [L]; linarith
  have hroot : Real.sqrt ((a : ℝ) / L) ≤ (X : ℝ) ^ (theta / 2) := by
    calc
      _ ≤ Real.sqrt (powerScale theta X) :=
        Real.sqrt_le_sqrt ((div_le_self (Nat.cast_nonneg (a : ℕ)) hLone).trans ha.2.2)
      _ = _ := by
        rw [powerScale, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
        congr 1
        ring
  have hv : v ≤ (X : ℝ) ^ (1 / 4 + theta / 2) := by
    dsimp [v]
    rw [Real.rpow_add hx]
    exact mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hx.le _)
  have hfirst : (a : ℝ) ≤ q := by
    apply ha.2.2.trans
    simpa only [pow_zero, one_mul, powerScale] using hpX
  have hsecond : L ^ (D + 1) * mu ≤ q :=
    (mul_le_mul_of_nonneg_left (rootScale_le_of_terminalPowerBand hX ha)
      (pow_nonneg hL.le (D + 1))).trans hqX
  have hthird : L ^ (D + 1) * v ≤ q :=
    (mul_le_mul_of_nonneg_left hv (pow_nonneg hL.le (D + 1))).trans hrX
  have hscale : (a : ℝ) / L + L ^ D * (mu + v) ≤ 3 * q / L := by
    apply (le_div_iff₀ hL).mpr
    rw [add_mul, div_mul_cancel₀ _ hL.ne']
    have hsum : L ^ (D + 1) * mu + L ^ (D + 1) * v ≤ 2 * q := by
      linarith only [hsecond, hthird]
    rw [pow_succ] at hsum
    nlinarith only [hfirst, hsum]
  calc
    _ ≤ C * ((a : ℝ) / L + L ^ D * (mu + v)) := (haX a ha).2
    _ ≤ C * (3 * q / L) := mul_le_mul_of_nonneg_left hscale hC.le
    _ = _ := by ring

end

end PrimeCoverPowerBand
