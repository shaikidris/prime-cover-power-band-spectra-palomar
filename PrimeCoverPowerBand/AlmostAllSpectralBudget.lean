import PrimeCoverPowerBand.TerminalSchur
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Ordered residual comparison for the complete molecule prefix

Finite same-index comparison (Paper II, Lemma 5.4), weak sorting
contraction, and the actual normalized projected full-star synthesis.
Global arithmetic residual estimates are separate obligations.
Only declaration-level finite spectral inputs are reused here.
-/

namespace PrimeCoverPowerBand

open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator

noncomputable section

variable {N : ℕ}

/-- A doubly stochastic coupling of two decreasing real sequences has cross
term at most their identity-paired cross term. -/
theorem sum_doublyStochastic_mul_mul_le_sum_mul
    {alpha beta : Fin N → ℝ} (halpha : Antitone alpha) (hbeta : Antitone beta)
    {W : Matrix (Fin N) (Fin N) ℝ} (hW : W ∈ doublyStochastic ℝ (Fin N)) :
    ∑ i, ∑ j, W i j * (alpha i * beta j) ≤ ∑ i, alpha i * beta i := by
  obtain ⟨w, hw_nonneg, hw_sum, hw_matrix⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic hW
  have hentry (i j : Fin N) :
      W i j = ∑ sigma, w sigma * sigma.permMatrix ℝ i j := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ ↦ M i j) hw_matrix.symm
    simpa [Matrix.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  calc
    ∑ i, ∑ j, W i j * (alpha i * beta j) =
        ∑ i, ∑ j, ∑ sigma,
          (w sigma * sigma.permMatrix ℝ i j) * (alpha i * beta j) := by
            simp_rw [hentry, Finset.sum_mul]
    _ = ∑ i, ∑ sigma, ∑ j,
        (w sigma * sigma.permMatrix ℝ i j) * (alpha i * beta j) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.sum_comm]
    _ = ∑ sigma, ∑ i, ∑ j,
        (w sigma * sigma.permMatrix ℝ i j) * (alpha i * beta j) := by
          rw [Finset.sum_comm]
    _ = ∑ sigma, w sigma * ∑ i, alpha i * beta (sigma i) := by
          apply Finset.sum_congr rfl
          intro sigma _hsigma
          calc
            ∑ i, ∑ j,
                (w sigma * sigma.permMatrix ℝ i j) * (alpha i * beta j) =
                w sigma * ∑ i, ∑ j,
                  sigma.permMatrix ℝ i j * (alpha i * beta j) := by
                    simp only [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i _hi
                    apply Finset.sum_congr rfl
                    intro j _hj
                    ring
            _ = w sigma * ∑ i, alpha i * beta (sigma i) := by
              apply congrArg (fun x : ℝ ↦ w sigma * x)
              apply Finset.sum_congr rfl
              intro i _hi
              simp [Equiv.toPEquiv_apply, mul_comm]
    _ ≤ ∑ sigma, w sigma * ∑ i, alpha i * beta i := by
      apply Finset.sum_le_sum
      intro sigma _hsigma
      exact mul_le_mul_of_nonneg_left
        ((halpha.monovary hbeta).sum_mul_comp_perm_le_sum_mul)
        (hw_nonneg sigma)
    _ = ∑ i, alpha i * beta i := by
      rw [← Finset.sum_mul, hw_sum, one_mul]

/-- Quadratic transport by a doubly stochastic coupling dominates the
identity matching for decreasing real sequences.  This is the combinatorial
heart of the Hoffman--Wielandt inequality. -/
theorem sum_sq_sub_le_doublyStochastic_transport
    {alpha beta : Fin N → ℝ} (halpha : Antitone alpha) (hbeta : Antitone beta)
    {W : Matrix (Fin N) (Fin N) ℝ} (hW : W ∈ doublyStochastic ℝ (Fin N)) :
    ∑ i, (alpha i - beta i) ^ 2 ≤
      ∑ i, ∑ j, W i j * (alpha i - beta j) ^ 2 := by
  have hcross := sum_doublyStochastic_mul_mul_le_sum_mul halpha hbeta hW
  have hrows : ∀ i, ∑ j, W i j = 1 :=
    sum_row_of_mem_doublyStochastic hW
  have hcols : ∀ j, ∑ i, W i j = 1 :=
    sum_col_of_mem_doublyStochastic hW
  calc
    ∑ i, (alpha i - beta i) ^ 2 =
        (∑ i, alpha i ^ 2) + (∑ i, beta i ^ 2) -
          2 * ∑ i, alpha i * beta i := by
            simp_rw [sub_sq]
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            have htwice : ∑ i, 2 * alpha i * beta i =
                2 * ∑ i, alpha i * beta i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _hi
              ring
            rw [htwice]
            ring
    _ ≤ (∑ i, alpha i ^ 2) + (∑ i, beta i ^ 2) -
          2 * (∑ i, ∑ j, W i j * (alpha i * beta j)) := by
            linarith
    _ = ∑ i, ∑ j, W i j * (alpha i - beta j) ^ 2 := by
      have hfirst : ∑ i, ∑ j, W i j * alpha i ^ 2 =
          ∑ i, alpha i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        calc
          ∑ j, W i j * alpha i ^ 2 =
              (∑ j, W i j) * alpha i ^ 2 := by rw [Finset.sum_mul]
          _ = alpha i ^ 2 := by rw [hrows i, one_mul]
      have hsecond : ∑ i, ∑ j, W i j * beta j ^ 2 =
          ∑ j, beta j ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _hj
        calc
          ∑ i, W i j * beta j ^ 2 =
              (∑ i, W i j) * beta j ^ 2 := by rw [Finset.sum_mul]
          _ = beta j ^ 2 := by rw [hcols j, one_mul]
      calc
        (∑ i, alpha i ^ 2) + (∑ i, beta i ^ 2) -
            2 * (∑ i, ∑ j, W i j * (alpha i * beta j)) =
            (∑ i, ∑ j, W i j * alpha i ^ 2) +
              (∑ i, ∑ j, W i j * beta j ^ 2) -
                2 * (∑ i, ∑ j, W i j * (alpha i * beta j)) := by
                  rw [hfirst, hsecond]
        _ = ∑ i, ∑ j, W i j * (alpha i - beta j) ^ 2 := by
          symm
          calc
            ∑ i, ∑ j, W i j * (alpha i - beta j) ^ 2 =
                ∑ i, ∑ j,
                  (W i j * alpha i ^ 2 -
                    2 * W i j * (alpha i * beta j) +
                      W i j * beta j ^ 2) := by
                        apply Finset.sum_congr rfl
                        intro i _hi
                        apply Finset.sum_congr rfl
                        intro j _hj
                        ring
            _ = (∑ i, ∑ j, W i j * alpha i ^ 2) +
                  (∑ i, ∑ j, W i j * beta j ^ 2) -
                    2 * (∑ i, ∑ j, W i j * (alpha i * beta j)) := by
                      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                      have htwice :
                          ∑ i, ∑ j, 2 * W i j * (alpha i * beta j) =
                            2 * ∑ i, ∑ j,
                              W i j * (alpha i * beta j) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro i _hi
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro j _hj
                        ring
                      rw [htwice]
                      ring

variable {N : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Squared overlap matrix of two complex orthonormal bases. -/
noncomputable def complexOrthonormalBasisOverlapSq
    (u v : OrthonormalBasis (Fin N) ℂ E) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ ‖inner ℂ (u i) (v j)‖ ^ 2

/-- The squared absolute overlaps of two complex orthonormal bases form a
doubly stochastic matrix. -/
theorem complexOrthonormalBasisOverlapSq_mem_doublyStochastic
    (u v : OrthonormalBasis (Fin N) ℂ E) :
    complexOrthonormalBasisOverlapSq u v ∈ doublyStochastic ℝ (Fin N) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j ↦ sq_nonneg _, ?_, ?_⟩
  · intro i
    change ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2 = 1
    rw [v.sum_sq_norm_inner_left, u.norm_eq_one, one_pow]
  · intro j
    change ∑ i, ‖inner ℂ (u i) (v j)‖ ^ 2 = 1
    rw [u.sum_sq_norm_inner_right, v.norm_eq_one, one_pow]

/-- Squared Hilbert--Schmidt mass of a complex finite linear operator,
evaluated on an orthonormal basis. -/
noncomputable def complexLinearMapHilbertSchmidtSq
    (b : OrthonormalBasis (Fin N) ℂ E) (T : E →ₗ[ℂ] E) : ℝ :=
  ∑ j, ‖T (b j)‖ ^ 2

/-- Matrix-entry expansion of the complex Hilbert--Schmidt mass in arbitrary
orthonormal domain and codomain bases. -/
theorem complexLinearMapHilbertSchmidtSq_eq_sum_sq_norm_inner
    (u v : OrthonormalBasis (Fin N) ℂ E) (T : E →ₗ[ℂ] E) :
    complexLinearMapHilbertSchmidtSq v T =
      ∑ j, ∑ i, ‖inner ℂ (u i) (T (v j))‖ ^ 2 := by
  unfold complexLinearMapHilbertSchmidtSq
  apply Finset.sum_congr rfl
  intro j _hj
  exact (u.sum_sq_norm_inner_right (T (v j))).symm

variable [FiniteDimensional ℂ E]

/-- Entry of the difference of two symmetric complex operators in their
respective ordered eigenbases. -/
theorem inner_complexEigenvectorBasis_sub_apply_complexEigenvectorBasis
    {T U : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hU : U.IsSymmetric)
    (hn : Module.finrank ℂ E = N) (i j : Fin N) :
    inner ℂ (hT.eigenvectorBasis hn i)
        ((T - U) (hU.eigenvectorBasis hn j)) =
      ((hT.eigenvalues hn i - hU.eigenvalues hn j : ℝ) : ℂ) *
        inner ℂ (hT.eigenvectorBasis hn i) (hU.eigenvectorBasis hn j) := by
  rw [LinearMap.sub_apply, inner_sub_right, ← hT]
  rw [hT.apply_eigenvectorBasis hn i, hU.apply_eigenvectorBasis hn j]
  change inner ℂ
      ((hT.eigenvalues hn i : ℂ) • hT.eigenvectorBasis hn i)
        (hU.eigenvectorBasis hn j) -
      inner ℂ (hT.eigenvectorBasis hn i)
        ((hU.eigenvalues hn j : ℂ) • hU.eigenvectorBasis hn j) =
    ((hT.eigenvalues hn i - hU.eigenvalues hn j : ℝ) : ℂ) *
      inner ℂ (hT.eigenvectorBasis hn i) (hU.eigenvectorBasis hn j)
  rw [inner_smul_left, inner_smul_right]
  simp
  ring

/-- Hoffman--Wielandt inequality for finite-dimensional complex symmetric
operators. -/
theorem sum_sq_eigenvalues_sub_le_complexLinearMapHilbertSchmidtSq
    {T U : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hU : U.IsSymmetric)
    (hn : Module.finrank ℂ E = N) :
    ∑ i : Fin N,
        (hT.eigenvalues hn i - hU.eigenvalues hn i) ^ 2 ≤
      complexLinearMapHilbertSchmidtSq (hU.eigenvectorBasis hn) (T - U) := by
  let u : OrthonormalBasis (Fin N) ℂ E := hT.eigenvectorBasis hn
  let v : OrthonormalBasis (Fin N) ℂ E := hU.eigenvectorBasis hn
  let alpha : Fin N → ℝ := hT.eigenvalues hn
  let beta : Fin N → ℝ := hU.eigenvalues hn
  have halpha : Antitone alpha := hT.eigenvalues_antitone hn
  have hbeta : Antitone beta := hU.eigenvalues_antitone hn
  have htransport := sum_sq_sub_le_doublyStochastic_transport halpha hbeta
    (complexOrthonormalBasisOverlapSq_mem_doublyStochastic u v)
  rw [complexLinearMapHilbertSchmidtSq_eq_sum_sq_norm_inner u v]
  calc
    ∑ i : Fin N, (alpha i - beta i) ^ 2 ≤
        ∑ i, ∑ j,
          complexOrthonormalBasisOverlapSq u v i j *
            (alpha i - beta j) ^ 2 := htransport
    _ = ∑ j, ∑ i, ‖inner ℂ (u i) ((T - U) (v j))‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      rw [inner_complexEigenvectorBasis_sub_apply_complexEigenvectorBasis
        hT hU hn]
      change complexOrthonormalBasisOverlapSq u v i j *
          (alpha i - beta j) ^ 2 =
        ‖((alpha i - beta j : ℝ) : ℂ) * inner ℂ (u i) (v j)‖ ^ 2
      rw [norm_mul, mul_pow]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp only [complexOrthonormalBasisOverlapSq]
      ring

end


/-- Weak sorting contraction: ties are allowed, and the conclusion compares
VALUES at the same rank rather than bounding a sorting permutation. -/
theorem abs_comp_perm_sub_le_of_antitone
    {N : ℕ} {x p : Fin N → ℝ} (hp : Antitone p)
    (σ : Equiv.Perm (Fin N)) (hx : Antitone (x ∘ σ))
    {u : ℝ} (hbound : ∀ i, |x i - p i| ≤ u) (j : Fin N) :
    |x (σ j) - p j| ≤ u := by
  classical
  have hcard (P : Fin N → Prop) [DecidablePred P] :
      (Finset.univ.filter fun i ↦ P (σ i)).card =
        (Finset.univ.filter P).card := by
    apply Finset.card_bij (fun i _ ↦ σ i)
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    · intro i _ k _ hik
      exact σ.injective hik
    · intro i hi
      exact ⟨σ.symm i, by simpa using hi, σ.apply_symm_apply i⟩
  have hlo : p j - u ≤ x (σ j) := by
    apply (Tuple.lt_card_ge_iff_apply_ge_of_antitone hx).1
    rw [show (Finset.univ.filter fun i ↦ p j - u ≤ (x ∘ σ) i).card =
      (Finset.univ.filter fun i ↦ p j - u ≤ x i).card from
        hcard (fun i ↦ p j - u ≤ x i)]
    have hj : j.val < (Finset.univ.filter fun i ↦ p j ≤ p i).card :=
      (Tuple.lt_card_ge_iff_apply_ge_of_antitone hp).2 le_rfl
    apply hj.trans_le (Finset.card_le_card ?_)
    intro i hi
    have hpi := (Finset.mem_filter.mp hi).2
    have hxi := (abs_le.mp (hbound i)).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
  have hhi : x (σ j) ≤ p j + u := by
    by_contra hn
    have hj := (Tuple.lt_card_gt_iff_apply_gt_of_antitone hx).2
      (lt_of_not_ge hn)
    rw [show (Finset.univ.filter fun i ↦ p j + u < (x ∘ σ) i).card =
      (Finset.univ.filter fun i ↦ p j + u < x i).card from
        hcard (fun i ↦ p j + u < x i)] at hj
    have hle : (Finset.univ.filter fun i ↦ p j + u < x i).card ≤
        (Finset.univ.filter fun i ↦ p j < p i).card := by
      apply Finset.card_le_card
      intro i hi
      have hxi := (Finset.mem_filter.mp hi).2
      have hpi := (abs_le.mp (hbound i)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
    exact (lt_irrefl (p j))
      ((Tuple.lt_card_gt_iff_apply_gt_of_antitone hp).1 (hj.trans_le hle))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Concrete descending-sort version of the weak contraction (5.12). -/
theorem abs_descendingSort_sub_le_of_antitone
    {N : ℕ} {x p : Fin N → ℝ} (hp : Antitone p)
    {u : ℝ} (hbound : ∀ i, |x i - p i| ≤ u) (j : Fin N) :
    |x (Tuple.sort (fun i ↦ -x i) j) - p j| ≤ u := by
  apply abs_comp_perm_sub_le_of_antitone hp _ _ hbound j
  intro i k hik
  have h := Tuple.monotone_sort (fun l ↦ -x l) hik
  dsimp at h ⊢
  linarith


section LowComplement

variable {𝕜 V U : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]

/-- The adjoint of an isometric frame is contractive. -/
theorem norm_isometry_adjoint_apply_le (Q : U →ₗᵢ[𝕜] V) (x : V) :
    ‖Q.toLinearMap.adjoint x‖ ≤ ‖x‖ := by
  have h : ‖Q.toLinearMap.adjoint x‖ ^ 2 ≤
      ‖Q.toLinearMap.adjoint x‖ * ‖x‖ := by
    calc
      ‖Q.toLinearMap.adjoint x‖ ^ 2 =
          RCLike.re ⟪Q (Q.toLinearMap.adjoint x), x⟫_𝕜 := by
        calc
          _ = RCLike.re ⟪Q.toLinearMap.adjoint x,
              Q.toLinearMap.adjoint x⟫_𝕜 := norm_sq_eq_re_inner _
          _ = _ := congrArg RCLike.re
            (LinearMap.adjoint_inner_right Q.toLinearMap _ _)
      _ ≤ ‖Q (Q.toLinearMap.adjoint x)‖ * ‖x‖ :=
        (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ = _ := by rw [Q.norm_map]
  nlinarith [norm_nonneg (Q.toLinearMap.adjoint x), norm_nonneg x]

/-- Low-complement Schur comparison at the SAME index (Lemma 5.2).
The residual is measured against any model D; its component orthogonal to
the frame is the actual off-diagonal block. No ordered-root premise occurs. -/
theorem ordered_isometricCompression_schur_le
    (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) (Q : U →ₗᵢ[𝕜] V)
    (D : U →ₗ[𝕜] U) {eta beta : ℝ} (heta : 0 ≤ eta)
    (hres : ∀ v : U, ‖T (Q v) - Q (D v)‖ ≤ eta * ‖v‖)
    (hcomp : ∀ y : V, Q.toLinearMap.adjoint y = 0 →
      RCLike.re ⟪y, T y⟫_𝕜 ≤ beta * ‖y‖ ^ 2)
    (i : Fin (Module.finrank 𝕜 U))
    (hgap : beta < (hT.adjoint_conj Q.toLinearMap).eigenvalues rfl i) :
    let xi := (hT.adjoint_conj Q.toLinearMap).eigenvalues rfl i
    let zeta := hT.eigenvalues rfl (liftRCLikeCompressionEigenIndex Q i)
    xi ≤ zeta ∧ zeta ≤ xi + eta ^ 2 / (xi - beta) := by
  let p := Q.toLinearMap.adjoint
  let M := p ∘ₗ T ∘ₗ Q.toLinearMap
  let hM : M.IsSymmetric := hT.adjoint_conj Q.toLinearMap
  let xi := hM.eigenvalues rfl i
  let delta := eta ^ 2 / (xi - beta)
  have hgb : 0 < xi - beta := sub_pos.mpr hgap
  have hd : 0 ≤ delta := div_nonneg (sq_nonneg _) hgb.le
  have hpQ (v : U) : p (Q v) = v :=
    congrArg (fun f : U →ₗ[𝕜] U ↦ f v) Q.adjoint_comp_self'
  have hmquad (v : U) :
      RCLike.re ⟪v, M v⟫_𝕜 = RCLike.re ⟪Q v, T (Q v)⟫_𝕜 := by
    exact congrArg RCLike.re (LinearMap.adjoint_inner_right Q.toLinearMap _ _)
  refine ⟨rclike_compressed_eigenvalue_le_ambient_eigenvalue
    T M hT hM Q hmquad i, ?_⟩
  apply rclike_eigenvalue_le_of_positive_subspace_finrank_le
    T hT (liftRCLikeCompressionEigenIndex Q i) (xi + delta)
  intro W hW
  have hdom (x : V) :
      RCLike.re ⟪x, T x⟫_𝕜 - (xi + delta) * ‖x‖ ^ 2 ≤
        RCLike.re ⟪p x, M (p x)⟫_𝕜 - xi * ‖p x‖ ^ 2 := by
    let v := p x
    let y := x - Q v
    have hy : p y = 0 := by simp [y, v, map_sub, hpQ]
    have horth (w : U) : ⟪Q w, y⟫_𝕜 = 0 := by
      calc
        _ = ⟪w, p y⟫_𝕜 := (LinearMap.adjoint_inner_right Q.toLinearMap w y).symm
        _ = 0 := by rw [hy, inner_zero_right]
    have hsplit : x = Q v + y := by dsimp [y]; abel
    have hnorm : ‖x‖ ^ 2 = ‖v‖ ^ 2 + ‖y‖ ^ 2 := by
      rw [hsplit, norm_add_sq (𝕜 := 𝕜), horth v, map_zero, Q.norm_map]
      ring
    have hcross : RCLike.re ⟪Q v, T y⟫_𝕜 =
        RCLike.re ⟪T (Q v) - Q (D v), y⟫_𝕜 := by
      rw [inner_sub_left, horth (D v), sub_zero, hT]
    have hform : RCLike.re ⟪x, T x⟫_𝕜 =
        RCLike.re ⟪v, M v⟫_𝕜 +
          2 * RCLike.re ⟪T (Q v) - Q (D v), y⟫_𝕜 +
          RCLike.re ⟪y, T y⟫_𝕜 := by
      conv_lhs => rw [hsplit, map_add, inner_add_left, inner_add_right,
        inner_add_right, map_add, map_add, map_add]
      rw [← hmquad, ← hT (Q v) y, inner_re_symm y (T (Q v)),
        hT (Q v) y, hcross]
      ring
    have hden : 0 < xi + delta - beta := by linarith
    have hschur := schur_cross_block_quadratic_upper (𝕜 := 𝕜)
      (T (Q v) - Q (D v)) y (z := xi + delta) (hcomp y hy) (by linarith)
    have hsq : ‖T (Q v) - Q (D v)‖ ^ 2 ≤ eta ^ 2 * ‖v‖ ^ 2 := by
      simpa [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hres v)
    have hfrac : eta ^ 2 / (xi + delta - beta) ≤ delta := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hgb (by linarith)
    have hpay : ‖T (Q v) - Q (D v)‖ ^ 2 / (xi + delta - beta) ≤
        delta * ‖v‖ ^ 2 := by
      calc
        _ ≤ (eta ^ 2 * ‖v‖ ^ 2) / (xi + delta - beta) :=
          div_le_div_of_nonneg_right hsq hden.le
        _ = (eta ^ 2 / (xi + delta - beta)) * ‖v‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
    rw [hform, hnorm]
    dsimp [v] at *
    nlinarith
  obtain ⟨Z, hZ, hrank⟩ :=
    rclike_positiveSubspace_transfer_of_quadratic_domination
      T M (xi + delta) xi p hdom W hW
  exact hrank.trans
    (rclike_finrank_positive_subspace_le_eigenvalue_index M hM i Z hZ)

end LowComplement


/-- Squaring the same-index root comparison with explicit uniform constants.
All roots stay positive; no claim about negative or unordered roots is used. -/
theorem sq_displacement_le_of_lowComplement
    {mu c0 C0 e eps nu xi zeta : ℝ}
    (hmu : 0 < mu) (hc0 : 0 < c0) (hC : c0 ≤ C0)
    (he : 0 ≤ e) (heSmall : e ≤ c0 * mu / 4)
    (heps : 0 ≤ eps) (heps_le : eps ≤ e)
    (hnuLo : c0 * mu ≤ nu) (hnuHi : nu ≤ C0 * mu)
    (hxi : |xi - nu| ≤ eps) (hzLo : xi ≤ zeta)
    (hzHi : zeta ≤ xi + 4 * e ^ 2 / (c0 * mu)) :
    |zeta ^ 2 - nu ^ 2| ≤
      4 * C0 * mu * eps + (16 * C0 / c0) * e ^ 2 := by
  have hden : 0 < c0 * mu := mul_pos hc0 hmu
  have hC0 : 0 < C0 := hc0.trans_le hC
  have hs : 4 * e ^ 2 / (c0 * mu) ≤ e := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hs0 : 0 ≤ 4 * e ^ 2 / (c0 * mu) := by positivity
  obtain ⟨hxiLo, hxiHi⟩ := abs_le.mp hxi
  have hnu0 : 0 < nu := hden.trans_le hnuLo
  have hz0 : 0 < zeta := by nlinarith
  have hzsum : |zeta + nu| ≤ 4 * C0 * mu := by
    rw [abs_of_pos (add_pos hz0 hnu0)]
    nlinarith [mul_le_mul_of_nonneg_right hC hmu.le]
  have hzdiff : |zeta - nu| ≤ eps + 4 * e ^ 2 / (c0 * mu) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |zeta ^ 2 - nu ^ 2| = |zeta - nu| * |zeta + nu| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (eps + 4 * e ^ 2 / (c0 * mu)) * (4 * C0 * mu) :=
      mul_le_mul hzdiff hzsum (abs_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

/-- The summed squared-energy consequence of the pointwise bound in 5.4. -/
theorem sum_sq_squaredDisplacement_le
    {n : ℕ} (I : Finset (Fin n)) (zeta nu eps : Fin n → ℝ)
    {mu c0 C0 e h : ℝ}
    (hmu : 0 < mu) (hc0 : 0 < c0) (hC0 : 0 ≤ C0)
    (heps : ∀ i, 0 ≤ eps i)
    (hHW : ∑ i, eps i ^ 2 ≤ h ^ 2)
    (hpoint : ∀ i ∈ I, |zeta i ^ 2 - nu i ^ 2| ≤
      4 * C0 * mu * eps i + (16 * C0 / c0) * e ^ 2) :
    ∑ i ∈ I, (zeta i ^ 2 - nu i ^ 2) ^ 2 ≤
      32 * C0 ^ 2 * mu ^ 2 * h ^ 2 +
        512 * (C0 / c0) ^ 2 * I.card * e ^ 4 := by
  have hsub : ∑ i ∈ I, eps i ^ 2 ≤ h ^ 2 :=
    (Finset.sum_le_univ_sum_of_nonneg (fun i ↦ sq_nonneg (eps i))).trans hHW
  have hsum : ∑ i ∈ I, (zeta i ^ 2 - nu i ^ 2) ^ 2 ≤
      ∑ i ∈ I, (32 * C0 ^ 2 * mu ^ 2 * eps i ^ 2 +
        512 * (C0 / c0) ^ 2 * e ^ 4) := by
    apply Finset.sum_le_sum
    intro i hi
    have hpi := heps i
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hpoint i hi)
    rw [sq_abs] at hh
    have hid : 32 * C0 ^ 2 * mu ^ 2 * eps i ^ 2 +
        512 * (C0 / c0) ^ 2 * e ^ 4 =
        2 * (4 * C0 * mu * eps i) ^ 2 + 2 * ((16 * C0 / c0) * e ^ 2) ^ 2 := by ring
    rw [hid]
    nlinarith [sq_nonneg (4 * C0 * mu * eps i - (16 * C0 / c0) * e ^ 2)]
  calc
    _ ≤ _ := hsum
    _ = 32 * C0 ^ 2 * mu ^ 2 * (∑ i ∈ I, eps i ^ 2) +
        512 * (C0 / c0) ^ 2 * I.card * e ^ 4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      gcongr


section OrderedResidual

variable {V U : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]

/-- Paper II Lemma 5.4, finite SAME-index version. Q is the actual isometry,
the residual is TQ-QD, and the complement is bounded on ker Q*. The HS mass
is evaluated in D's orthonormal eigenbasis; matrix Frobenius budgets can be
transported to this basis. No separation of neighbouring model roots is
assumed or concluded. -/
theorem ordered_residual_squaredEnergy_comparison
    (T : V →ₗ[ℂ] V) (hT : T.IsSymmetric)
    (D : U →ₗ[ℂ] U) (hD : D.IsSymmetric) (Q : U →ₗᵢ[ℂ] V)
    (I : Finset (Fin (Module.finrank ℂ U)))
    {mu c0 C0 e h : ℝ} (hmu : 0 < mu) (hc0 : 0 < c0) (hC : c0 ≤ C0)
    (he : 0 ≤ e) (heSmall : e ≤ c0 * mu / 4)
    (hres : ∀ v : U, ‖T (Q v) - Q (D v)‖ ≤ e * ‖v‖)
    (hHS : ∑ i, ‖T (Q (hD.eigenvectorBasis rfl i)) -
        Q (D (hD.eigenvectorBasis rfl i))‖ ^ 2 ≤ h ^ 2)
    (hcomp : ∀ y : V, Q.toLinearMap.adjoint y = 0 →
      RCLike.re ⟪y, T y⟫_ℂ ≤ (c0 * mu / 2) * ‖y‖ ^ 2)
    (hwindow : ∀ i ∈ I,
      c0 * mu ≤ hD.eigenvalues rfl i ∧ hD.eigenvalues rfl i ≤ C0 * mu) :
    let hM := hT.adjoint_conj Q.toLinearMap
    let nu := hD.eigenvalues rfl
    let xi := hM.eigenvalues rfl
    let zeta := fun i ↦ hT.eigenvalues rfl (liftRCLikeCompressionEigenIndex Q i)
    (∑ i, (xi i - nu i) ^ 2 ≤ h ^ 2) ∧
    (∀ i, |xi i - nu i| ≤ e) ∧
    (∀ i ∈ I, 0 ≤ zeta i - xi i ∧
      zeta i - xi i ≤ 4 * e ^ 2 / (c0 * mu) ∧
      |zeta i ^ 2 - nu i ^ 2| ≤
        4 * C0 * mu * |xi i - nu i| + (16 * C0 / c0) * e ^ 2) ∧
    (∑ i ∈ I, (zeta i ^ 2 - nu i ^ 2) ^ 2 ≤
      32 * C0 ^ 2 * mu ^ 2 * h ^ 2 +
        512 * (C0 / c0) ^ 2 * I.card * e ^ 4) := by
  let M := Q.toLinearMap.adjoint ∘ₗ T ∘ₗ Q.toLinearMap
  let hM : M.IsSymmetric := hT.adjoint_conj Q.toLinearMap
  let nu := hD.eigenvalues rfl
  let xi := hM.eigenvalues rfl
  let zeta := fun i ↦ hT.eigenvalues rfl (liftRCLikeCompressionEigenIndex Q i)
  have hpQ (v : U) : Q.toLinearMap.adjoint (Q v) = v :=
    congrArg (fun f : U →ₗ[ℂ] U ↦ f v) Q.adjoint_comp_self'
  have hcontract (v : U) : ‖(M - D) v‖ ≤ ‖T (Q v) - Q (D v)‖ := by
    have heq : (M - D) v = Q.toLinearMap.adjoint (T (Q v) - Q (D v)) := by
      simp [M, map_sub, hpQ]
    rw [heq]
    exact norm_isometry_adjoint_apply_le Q _
  have hpoint (v : U) : ‖(M - D) v‖ ≤ e * ‖v‖ :=
    (hcontract v).trans (hres v)
  have hweyl (i) : |xi i - nu i| ≤ e := by
    have hw := abs_rclike_orderedEigenvalue_add_sub_le D (M - D) hD
      (hM.sub hD) i e hpoint
    have hcancel : D + (M - D) = M := by abel
    simpa only [hcancel] using hw
  have hhw : ∑ i, (xi i - nu i) ^ 2 ≤ h ^ 2 := by
    apply (sum_sq_eigenvalues_sub_le_complexLinearMapHilbertSchmidtSq hM hD rfl).trans
    apply le_trans _ hHS
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hcontract _)
  have hjoint (i) (hi : i ∈ I) :
      0 ≤ zeta i - xi i ∧ zeta i - xi i ≤ 4 * e ^ 2 / (c0 * mu) ∧
      |zeta i ^ 2 - nu i ^ 2| ≤
        4 * C0 * mu * |xi i - nu i| + (16 * C0 / c0) * e ^ 2 := by
    obtain ⟨hlo, hhi⟩ := hwindow i hi
    have hxilo := (abs_le.mp (hweyl i)).1
    have hgap : c0 * mu / 2 < xi i := by
      have hh : 0 < c0 * mu := mul_pos hc0 hmu
      dsimp [nu] at hxilo
      linarith
    obtain ⟨hzlo, hzhi⟩ := ordered_isometricCompression_schur_le
      T hT Q D he hres hcomp i hgap
    have hfrac : e ^ 2 / (xi i - c0 * mu / 2) ≤ 4 * e ^ 2 / (c0 * mu) := by
      have hden : 0 < c0 * mu := mul_pos hc0 hmu
      have hden' : 0 < xi i - c0 * mu / 2 := sub_pos.mpr hgap
      apply (div_le_iff₀ hden').2
      have hbound : c0 * mu / 4 ≤ xi i - c0 * mu / 2 := by
        dsimp [nu] at hxilo
        linarith
      have hpay := mul_le_mul_of_nonneg_left hbound
        (show 0 ≤ 4 * e ^ 2 / (c0 * mu) by positivity)
      have heq : (4 * e ^ 2 / (c0 * mu)) * (c0 * mu / 4) = e ^ 2 := by
        field_simp
      rw [heq] at hpay
      exact hpay
    have hzupper : zeta i ≤ xi i + 4 * e ^ 2 / (c0 * mu) :=
      hzhi.trans (add_le_add_right hfrac _)
    refine ⟨sub_nonneg.mpr hzlo, by linarith, ?_⟩
    exact sq_displacement_le_of_lowComplement hmu hc0 hC he heSmall
      (abs_nonneg _) (hweyl i) hlo hhi le_rfl hzlo hzupper
  refine ⟨hhw, hweyl, hjoint, ?_⟩
  apply sum_sq_squaredDisplacement_le I zeta nu (fun i ↦ |xi i - nu i|)
    hmu hc0 (hc0.le.trans hC) (fun _ ↦ abs_nonneg _) _ (fun i hi ↦ (hjoint i hi).2.2)
  simpa only [sq_abs] using hhw

end OrderedResidual


/-- A rectangular residual has the same HS mass in every orthonormal domain
basis. This connects the finite comparison's basis sum to R4's matrix budget. -/
theorem sum_norm_toEuclideanLin_sq_eq_matrixFrobeniusNorm_sq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (R : Matrix m n ℂ)
    (v : OrthonormalBasis (Fin (Fintype.card n)) ℂ (EuclideanSpace ℂ n)) :
    ∑ j, ‖Matrix.toEuclideanLin R (v j)‖ ^ 2 = matrixFrobeniusNorm R ^ 2 := by
  let T := Matrix.toEuclideanLin R
  let b := EuclideanSpace.basisFun m ℂ
  calc
    _ = ∑ j, ∑ i, ‖inner ℂ (b i) (T (v j))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (b.sum_sq_norm_inner_right _).symm
    _ = ∑ i, ∑ j, ‖inner ℂ (T.adjoint (b i)) (v j)‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp only [LinearMap.adjoint_inner_left]
    _ = ∑ i, ‖T.adjoint (b i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact v.sum_sq_norm_inner_left _
    _ = ∑ i, ∑ k, ‖R i k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro k _
      have hentry : T.adjoint (b i) k = star (R i k) := by
        change (Matrix.toEuclideanLin R).adjoint (b i) k = star (R i k)
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
        simp [b, Matrix.toLpLin_apply]
      rw [hentry, norm_star]
    _ = _ := (matrixFrobeniusNorm_sq R).symm

section ProjectedFullStarFrame

noncomputable section

open Filter Topology
open scoped Classical

/-- The sign fixing positive overlap with the boundary star. At zero overlap
the sign is one; eventual nonzero overlap is proved separately. -/
def fullStarMoleculePhase (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) : ℝ :=
  if exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 < 0 then -1 else 1

/-- The actual full principal molecule, with its real phase fixed. -/
def phasedFullStarMolecule (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    EuclideanSpace ℂ (PrimeStar.Vertex S X) :=
  (fullStarMoleculePhase S X a : ℂ) •
    PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a)

/-- Projection of the full-star molecule into the actual one-exit space. -/
def projectedFullStarMolecule (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    EuclideanSpace ℂ (PrimeStar.Vertex S X) :=
  Matrix.toEuclideanLin (oneExitProjection S X) (phasedFullStarMolecule S X a)

/-- Unit projected column on the eventual power range. The definition is
total, but no unit-norm assertion is made when its denominator is zero. -/
def normalizedProjectedFullStarMolecule
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    EuclideanSpace ℂ (PrimeStar.Vertex S X) :=
  (‖projectedFullStarMolecule S X a‖⁻¹ : ℂ) • projectedFullStarMolecule S X a

/-- The chosen phase always has modulus one. -/
theorem abs_fullStarMoleculePhase (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    |fullStarMoleculePhase S X a| = 1 := by
  unfold fullStarMoleculePhase
  split_ifs <;> norm_num

/-- Phase fixing preserves the norm of the actual principal eigenvector. -/
theorem norm_phasedFullStarMolecule (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : ‖phasedFullStarMolecule S X a‖ = 1 := by
  simp [phasedFullStarMolecule, norm_smul,
    Real.norm_eq_abs, abs_fullStarMoleculePhase,
    PrimeStar.norm_complexifyEuclidean, norm_exactPrincipalMoleculeAmbientVector]

/-- The retained space fixes every nonempty positive star mode. -/
theorem oneExitProjection_fixes_positiveStarMode
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin (oneExitProjection S X)
        (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)) =
      PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a) := by
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  let Pp := Matrix.toEuclideanLin (positiveStarProjection S X)
  let u := PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)
  have hp : Pp u = u := positiveStarProjection_fixes_complexified_positiveStarMode ha hd
  have hmat : oneExitProjection S X * positiveStarProjection S X =
      positiveStarProjection S X := by
    rw [oneExitProjection, Matrix.add_mul,
      (positiveStarProjection_isStarProjection S X).isIdempotentElem,
      oneExitCyclicProjection_mul_positiveStarProjection, add_zero]
  have hPP : P (Pp u) = Pp u := by
    simpa only [P, Pp, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
      using congrArg (fun M ↦ Matrix.toEuclideanLin M u) hmat
  simpa only [hp] using hPP

/-- The chosen raw phase makes the boundary overlap the absolute value of
the original coefficient, as a real nonnegative complex number. -/
theorem inner_positiveStarMode_phasedFullStarMolecule
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    ⟪PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a),
      phasedFullStarMolecule S X a⟫_ℂ =
      ((|exactPrincipalMoleculeBoundaryModeCoefficient S X a 1| : ℝ) : ℂ) := by
  rw [phasedFullStarMolecule, inner_smul_right, PrimeStar.inner_complexifyEuclidean]
  change (fullStarMoleculePhase S X a : ℂ) *
      (exactPrincipalMoleculeBoundaryModeCoefficient S X a 1 : ℂ) = _
  unfold fullStarMoleculePhase
  split_ifs with h
  · rw [abs_of_neg h]
    push_cast
    ring
  · rw [abs_of_nonneg (le_of_not_gt h)]
    simp

/-- Projection preserves the positive-star overlap; this uses the actual
one-exit projection, not an assumed charged-branch inclusion. -/
theorem inner_positiveStarMode_projectedFullStarMolecule
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ⟪PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a),
      projectedFullStarMolecule S X a⟫_ℂ =
      ((|exactPrincipalMoleculeBoundaryModeCoefficient S X a 1| : ℝ) : ℂ) := by
  have hP := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  rw [projectedFullStarMolecule, ← hP,
    oneExitProjection_fixes_positiveStarMode ha hd,
    inner_positiveStarMode_phasedFullStarMolecule]

/-- The projected norm is at least the original boundary overlap and at
most one. This is a finite, graph-specific nondegeneracy bound. -/
theorem projectedFullStarMolecule_norm_bounds
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    |exactPrincipalMoleculeBoundaryModeCoefficient S X a 1| ≤
        ‖projectedFullStarMolecule S X a‖ ∧
      ‖projectedFullStarMolecule S X a‖ ≤ 1 := by
  constructor
  · have h := norm_inner_le_norm (𝕜 := ℂ)
      (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a))
      (projectedFullStarMolecule S X a)
    simpa only [inner_positiveStarMode_projectedFullStarMolecule ha hd,
      Complex.norm_real, Real.norm_eq_abs, abs_abs,
      PrimeStar.norm_complexifyEuclidean, norm_moleculePositiveStarMode hd,
      one_mul] using h
  · exact (norm_oneExitProjection_apply_le S X _).trans
      (norm_phasedFullStarMolecule S X a).le

/-- Normalization is justified uniformly for actual full-star columns on
every fixed sub-square-root power range. -/
theorem eventually_powerRange_projectedFullStarMolecule_norm_bounds
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        1 / 2 ≤ ‖projectedFullStarMolecule S X a‖ ∧
          ‖projectedFullStarMolecule S X a‖ ≤ 1 := by
  filter_upwards [
    eventually_powerRange_one_half_le_abs_exactPrincipalMoleculeBoundaryModeCoefficient
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta]
    with X hoverlap hwindow
  intro a ha
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  obtain ⟨hlower, hupper⟩ := projectedFullStarMolecule_norm_bounds haY hd
  exact ⟨(hoverlap a ha).trans hlower, hupper⟩

/-- The actual normalized projected columns have unit norm eventually,
with no abstract nonvanishing or gap premise left. -/
theorem eventually_powerRange_normalizedProjectedFullStarMolecule_unit
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ‖normalizedProjectedFullStarMolecule S X a‖ = 1 := by
  filter_upwards [eventually_powerRange_projectedFullStarMolecule_norm_bounds
    S hS htheta] with X hnorm
  intro a ha
  have hpos : 0 < ‖projectedFullStarMolecule S X a‖ :=
    lt_of_lt_of_le (by norm_num) (hnorm a ha).1
  simp [normalizedProjectedFullStarMolecule, norm_smul, Complex.norm_real,
    inv_mul_cancel₀ hpos.ne']

/-- Orthogonal projection splits the unit mass into retained and discarded parts. -/
theorem projectedFullStarMolecule_pythagoras (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    ‖projectedFullStarMolecule S X a‖ ^ 2 +
        ‖phasedFullStarMolecule S X a - projectedFullStarMolecule S X a‖ ^ 2 = 1 := by
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  let f := phasedFullStarMolecule S X a
  have hP : P.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hPP : P (P f) = P f := by
    have h := congrArg (fun M ↦ Matrix.toEuclideanLin M f)
      (oneExitProjection_isStarProjection S X).isIdempotentElem
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h
  have horth : ⟪P f, f - P f⟫_ℂ = 0 := by
    rw [hP, map_sub, hPP, sub_self, inner_zero_right]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P f) (f - P f) horth
  rw [show P f + (f - P f) = f by abel,
    show ‖f‖ = 1 from norm_phasedFullStarMolecule S X a,
    one_mul] at h
  simpa only [pow_two, P, f, projectedFullStarMolecule] using h.symm

/-- The normalizing denominator is exactly the paper's square root of
one minus the discarded mass. No tail bound is assumed in this identity. -/
theorem projectedFullStarMolecule_norm_eq_sqrt (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) :
    ‖projectedFullStarMolecule S X a‖ =
      Real.sqrt (1 -
        ‖phasedFullStarMolecule S X a - projectedFullStarMolecule S X a‖ ^ 2) := by
  have h := projectedFullStarMolecule_pythagoras S X a
  rw [← eq_sub_iff_add_eq] at h
  rw [← h, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Complete-prefix synthesis of the phase-fixed raw principal molecules. -/
def phasedFullStarFrame (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  fun v a ↦ phasedFullStarMolecule S X a.1 v

/-- Actual normalization factors of the projected prefix columns. -/
def projectedFullStarNormalization (S : Finset ℕ) (X K : ℕ) :
    Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
  Matrix.diagonal fun a ↦ (‖projectedFullStarMolecule S X a.1‖⁻¹ : ℂ)

/-- The manuscript's projected, column-normalized complete-prefix synthesis.
Symmetric reorthonormalization is a later operation, not part of this definition. -/
def projectedFullStarFrame (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  oneExitProjection S X * phasedFullStarFrame S X K *
    projectedFullStarNormalization S X K

/-- The actual discarded part of the phase-fixed complete prefix. -/
def fullStarFrameTail (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  (1 - oneExitProjection S X) * phasedFullStarFrame S X K

/-- Residual of the projected normalized frame against its actual root diagonal. -/
def projectedFullStarFrameResidual (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  oneExitCompression S X * projectedFullStarFrame S X K -
    projectedFullStarFrame S X K *
      complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)

/-- The matrix columns are exactly the previously normalized actual vectors. -/
theorem projectedFullStarFrame_apply (S : Finset ℕ) (X K : ℕ)
    (v : PrimeStar.Vertex S X) (a : MoleculeCenter S X K) :
    projectedFullStarFrame S X K v a =
      normalizedProjectedFullStarMolecule S X a.1 v := by
  simp only [projectedFullStarFrame, projectedFullStarNormalization, Matrix.mul_diagonal]
  change (∑ w, oneExitProjection S X v w * phasedFullStarMolecule S X a.1 w) *
      (‖projectedFullStarMolecule S X a.1‖⁻¹ : ℂ) = _
  simp only [normalizedProjectedFullStarMolecule, PiLp.smul_apply, smul_eq_mul]
  rw [mul_comm]
  rfl

/-- Exact phase and amplitude of a normalized projected column. -/
theorem inner_positiveStarMode_normalizedProjectedFullStarMolecule
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ⟪PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a),
      normalizedProjectedFullStarMolecule S X a⟫_ℂ =
      ((|exactPrincipalMoleculeBoundaryModeCoefficient S X a 1| /
        ‖projectedFullStarMolecule S X a‖ : ℝ) : ℂ) := by
  rw [normalizedProjectedFullStarMolecule, inner_smul_right,
    inner_positiveStarMode_projectedFullStarMolecule ha hd]
  push_cast
  ring

/-- On every complete power prefix, all actual projected columns are unit
and have strictly positive real overlap with their designated star mode. -/
theorem eventually_powerRange_projectedFullStarFrame_columns
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∀ a : MoleculeCenter S X K,
        ‖normalizedProjectedFullStarMolecule S X a.1‖ = 1 ∧
          0 < (⟪PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a.1),
            normalizedProjectedFullStarMolecule S X a.1⟫_ℂ).re := by
  filter_upwards [eventually_powerRange_normalizedProjectedFullStarMolecule_unit S hS htheta,
    eventually_powerRange_projectedFullStarMolecule_norm_bounds S hS htheta,
    eventually_powerRange_one_half_le_abs_exactPrincipalMoleculeBoundaryModeCoefficient
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta]
    with X hunit hnorm hoverlap hwindow
  intro K hK a
  have ha : InPowerRange theta X (a.1 : ℕ) :=
    ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
  obtain ⟨haY, hd, _⟩ := hwindow a.1 ha
  refine ⟨hunit a.1 ha, ?_⟩
  rw [inner_positiveStarMode_normalizedProjectedFullStarMolecule haY hd, Complex.ofReal_re]
  exact div_pos (lt_of_lt_of_le (by norm_num) (hoverlap a.1 ha))
    (lt_of_lt_of_le (by norm_num) (hnorm a.1 ha).1)

/-- The actual one-exit projection fixes the normalized synthesis exactly. -/
theorem oneExitProjection_mul_projectedFullStarFrame (S : Finset ℕ) (X K : ℕ) :
    oneExitProjection S X * projectedFullStarFrame S X K =
      projectedFullStarFrame S X K := by
  unfold projectedFullStarFrame
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    (oneExitProjection_isStarProjection S X).isIdempotentElem]

/-- Column normalization commutes with the actual diagonal molecule roots. -/
theorem projectedFullStarNormalization_commutes_roots (S : Finset ℕ) (X K : ℕ) :
    projectedFullStarNormalization S X K *
        complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K) =
      complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K) *
        projectedFullStarNormalization S X K := by
  have hroot : complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K) =
      Matrix.diagonal (fun a : MoleculeCenter S X K ↦
        (exactPrincipalMoleculeRoot S X a.1 : ℂ)) := by
    ext a b
    by_cases hab : a = b <;>
      simp [complexifyRealMatrix, exactMoleculeFamilyRootMatrix, Matrix.diagonal, hab]
  rw [hroot, projectedFullStarNormalization, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

/-- Exact Gram subtraction with the actual column normalization on both sides.
This retains the full discarded tail rather than assuming it vanishes. -/
theorem projectedFullStarFrame_gram_eq (S : Finset ℕ) (X K : ℕ) :
    (projectedFullStarFrame S X K)ᴴ * projectedFullStarFrame S X K =
      (projectedFullStarNormalization S X K)ᴴ *
        ((phasedFullStarFrame S X K)ᴴ * phasedFullStarFrame S X K -
          (fullStarFrameTail S X K)ᴴ * fullStarFrameTail S X K) *
        projectedFullStarNormalization S X K := by
  let P := oneExitProjection S X
  let V := phasedFullStarFrame S X K
  have hP := oneExitProjection_isStarProjection S X
  have hPstar : Pᴴ = P := hP.isSelfAdjoint.isHermitian.eq
  have hQstar : (1 - P)ᴴ = 1 - P := hP.one_sub.isSelfAdjoint.isHermitian.eq
  have hgram : (P * V)ᴴ * (P * V) =
      Vᴴ * V - ((1 - P) * V)ᴴ * ((1 - P) * V) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hPstar, hQstar]
    rw [← Matrix.mul_assoc P P V, hP.isIdempotentElem,
      ← Matrix.mul_assoc (1 - P) (1 - P) V, hP.one_sub.isIdempotentElem]
    simp [Matrix.mul_sub, Matrix.sub_mul]
  change ((P * V) * _)ᴴ * ((P * V) * _) = _
  calc
    _ = (projectedFullStarNormalization S X K)ᴴ *
        ((P * V)ᴴ * (P * V)) * projectedFullStarNormalization S X K := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hgram]; rfl

/-- Exact projected residual, with the adjacency acting on the discarded
tail still explicit. Replacing that action by H requires the R4b zero-mode proof. -/
theorem projectedFullStarFrameResidual_eq (S : Finset ℕ) (X K : ℕ) :
    projectedFullStarFrameResidual S X K =
      (oneExitProjection S X *
          (moleculeFamilyComplexAdjacency S X * phasedFullStarFrame S X K -
            phasedFullStarFrame S X K *
              complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)) -
        oneExitProjection S X *
          (moleculeFamilyComplexAdjacency S X * fullStarFrameTail S X K)) *
        projectedFullStarNormalization S X K := by
  let P := oneExitProjection S X
  let V := phasedFullStarFrame S X K
  let A := moleculeFamilyComplexAdjacency S X
  let D := complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)
  let N := projectedFullStarNormalization S X K
  have hPPV (W : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ) :
      P * (P * W) = P * W := by
    rw [← Matrix.mul_assoc, (oneExitProjection_isStarProjection S X).isIdempotentElem]
  have hcomm : N * D = D * N := projectedFullStarNormalization_commutes_roots S X K
  change (P * A * P) * ((P * V) * N) - ((P * V) * N) * D =
    (P * (A * V - V * D) - P * (A * ((1 - P) * V))) * N
  simp only [Matrix.mul_assoc, hPPV, hcomm, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.one_mul]
  abel

end

end ProjectedFullStarFrame

noncomputable section DiscardedFullStarTail

private theorem eigenprojection_commutes_of_commute
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T P : Module.End ℂ V)
    (hP : P.IsSymmetric) (hcomm : Commute P T) (lambda : ℂ) :
    Commute (Module.End.eigenspace T lambda).starProjection.toLinearMap P := by
  let U := Module.End.eigenspace T lambda
  have hinv : U ∈ Module.End.invtSubmodule P := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have h := congrArg (fun F : Module.End ℂ V ↦ F x) hcomm.eq
    simpa only [Module.End.mul_apply, hx, map_smul] using h.symm
  have hidem : IsIdempotentElem U.starProjection.toLinearMap := by
    unfold IsIdempotentElem
    rw [← ContinuousLinearMap.toLinearMap_mul]
    exact congrArg ContinuousLinearMap.toLinearMap U.isIdempotentElem_starProjection
  apply LinearMap.IsIdempotentElem.commute_iff hidem |>.2
  simpa [Submodule.range_starProjection, Submodule.ker_starProjection] using
    And.intro hinv (hP.orthogonalComplement_mem_invtSubmodule hinv)

/-- The complete one-exit projection reduces the actual large-prime forest. -/
theorem oneExitProjection_commutes_largePrime (S : Finset ℕ) (X : ℕ) :
    Commute (oneExitProjection S X) (oneExitLargePrimeMatrix S X) := by
  change (positiveStarProjection S X + oneExitCyclicProjection S X) *
      oneExitLargePrimeMatrix S X =
    oneExitLargePrimeMatrix S X *
      (positiveStarProjection S X + oneExitCyclicProjection S X)
  rw [Matrix.add_mul, Matrix.mul_add,
    (positiveStarProjection_commutes_oneExitLargePrimeMatrix S X).eq,
    (oneExitCyclicProjection_commutes_oneExitLargePrimeMatrix S X).eq]

/-- Spectral capture acts on the charged component, including repeated
eigenvalues; it does not assert that an entire eigenspace is captured. -/
theorem oneExitProjection_fixes_spectralComponent
    (S : Finset ℕ) (X : ℕ) (lambda : ℂ)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X))
    (hx : Matrix.toEuclideanLin (oneExitProjection S X) x = x) :
    Matrix.toEuclideanLin (oneExitProjection S X)
        ((Module.End.eigenspace
          (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection x) =
      (Module.End.eigenspace
        (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection x := by
  let T := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  have hP : P.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hcomm : Commute P T := by
    change P * T = T * P
    have h := congrArg Matrix.toEuclideanLin (oneExitProjection_commutes_largePrime S X).eq
    simpa only [P, T, Matrix.toLpLin_mul_same, ← Module.End.mul_eq_comp] using h
  have h := LinearMap.congr_fun
    (eigenprojection_commutes_of_commute T P hP hcomm lambda).eq x
  change (Module.End.eigenspace T lambda).starProjection (P x) =
    P ((Module.End.eigenspace T lambda).starProjection x) at h
  have hx' : P x = x := hx
  rw [hx'] at h
  exact h.symm

/-- Orthogonal projection onto the kernel of the actual large-prime forest. -/
def largePrimeZeroModeProjection (S : Finset ℕ) (X : ℕ) :
    EuclideanSpace ℂ (PrimeStar.Vertex S X) →L[ℂ]
      EuclideanSpace ℂ (PrimeStar.Vertex S X) :=
  (Module.End.eigenspace
    (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) 0).starProjection

/-- The full one-exit space captures the small-prime source of each nonempty
positive star. This uses the actual source inclusion, not a norm bound. -/
theorem oneExitProjection_fixes_positiveStarSource
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin (oneExitProjection S X)
        (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
          (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a))) =
      Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
        (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)) := by
  let u := PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  let A := Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let H := Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
  have hu : Matrix.toEuclideanLin (positiveStarProjection S X) u = u :=
    positiveStarProjection_fixes_complexified_positiveStarMode ha hd
  have hzero := congrArg (fun M ↦ Matrix.toEuclideanLin M u)
    (oneExitComplement_mul_adjacency_mul_positiveStar_eq_zero S X)
  have hAu : P (A u) = A u := by
    have hz : A u - P (A u) = 0 := by
      simpa only [oneExitComplementProjection, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply, hu, map_sub, Matrix.toLpLin_one, LinearMap.sub_apply,
      LinearMap.id_apply, map_zero, LinearMap.zero_apply, P, A] using hzero
    exact (sub_eq_zero.mp hz).symm
  have hLu : P (L u) = L u := by
    rw [oneExitLargePrimeMatrix_apply_complexified_positiveStarMode ha,
      map_smul, oneExitProjection_fixes_positiveStarMode ha hd]
  have hsplit : A u = L u + H u := by
    simp only [A, L, H, moleculeFamilyComplexAdjacency_eq_large_add_small,
      map_add, LinearMap.add_apply]
  change P (H u) = H u
  rw [hsplit, map_add, hLu] at hAu
  exact add_left_cancel hAu

/-- The positive signed source has no discarded zero-mode component. -/
theorem oneExitComplement_kills_positiveZeroSource
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin (oneExitComplementProjection S X)
        (largePrimeZeroModeProjection S X
          (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
            (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a)))) = 0 := by
  have h := oneExitProjection_fixes_spectralComponent S X 0 _
    (oneExitProjection_fixes_positiveStarSource ha hd)
  simpa only [oneExitComplementProjection, map_sub, Matrix.toLpLin_one, LinearMap.sub_apply,
    LinearMap.id_apply, largePrimeZeroModeProjection, sub_eq_zero] using h.symm

/-- Half the difference of the two signed zero-mode sources. The definition
retains the full actual graph source; its down-target identification and divisor
bound are proved below. -/
def signedZeroModeSourceDifference (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) : EuclideanSpace ℂ (PrimeStar.Vertex S X) :=
  (1 / 2 : ℂ) • largePrimeZeroModeProjection S X
    (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
      (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a) -
        PrimeStar.complexifyEuclidean
          (PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a (-1))))

/-- The discarded negative zero-mode source is exactly minus twice the signed
source difference. In particular, it must not be set to zero with the positive
source. This is the finite signed term in the repaired full-star tail. -/
theorem oneExitComplement_negativeZeroSource_eq
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin (oneExitComplementProjection S X)
        (largePrimeZeroModeProjection S X
          (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
            (PrimeStar.complexifyEuclidean
              (PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a (-1))))) =
      (-2 : ℂ) • Matrix.toEuclideanLin (oneExitComplementProjection S X)
        (signedZeroModeSourceDifference S X a) := by
  simp only [signedZeroModeSourceDifference, map_smul, map_sub,
    oneExitComplement_kills_positiveZeroSource ha hd, zero_sub, smul_smul]
  norm_num

end DiscardedFullStarTail

noncomputable section BoundaryKernelTail

/-- Local decidability for the forest adjacency used by the boundary-kernel identities. -/
local instance boundaryKernelTailLargePrimeDecidableAdj (S : Finset ℕ) (X Y : ℕ) :
    DecidableRel (PrimeStar.largePrimeGraph S X Y).Adj := Classical.decRel _

/-- The forest kills a mean-zero leaf vector. Reused from the checked
StarKernelVariance declaration; this concerns the boundary kernel, not yet
the complete discarded molecule. -/
theorem largePrime_apply_actualStarMeanZeroLeafVector
    {S : Finset ℕ} {X Y : ℕ} {c : PrimeStar.Vertex S X}
    (f : PrimeStar.Vertex S X → ℝ)
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y c) :
    Matrix.toEuclideanLin ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ)
        (actualStarMeanZeroLeafVector S X Y c f) = 0 := by
  have hleaves : (PrimeStar.largePrimeLeaves S X Y c).Nonempty := by
    exact Finset.card_pos.mp (by
      simpa [PrimeStar.largePrimeStarDegree] using hd)
  rw [actualStarMeanZeroLeafVector,
    PrimeStar.largePrime_toEuclideanLin_starDataVector hcut hc]
  have hsum := sum_sub_finsetMean_eq_zero hleaves f
  rw [hsum]
  ext v
  by_cases hvc : v = c
  · subst v
    simp
  · by_cases hvleaf : v ∈ PrimeStar.largePrimeLeaves S X Y c
    · rw [PrimeStar.largePrimeStarDataVector_leaf _ _ hvleaf]
      simp
    · rw [PrimeStar.largePrimeStarDataVector_outside _ _ hvc hvleaf]
      simp

/-- The actual full-star boundary kernel is a zero mode of the forest. -/
theorem largePrime_apply_exactPrincipalMoleculeBoundaryKernel
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin
        ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeBoundaryKernel S X a) = 0 := by
  exact largePrime_apply_actualStarMeanZeroLeafVector
    (exactPrincipalMoleculeAmbientVector S X a)
    (PrimeStar.sqrtCutoff_condition X) ha hd

/-- Projecting away the one-exit space preserves the zero-mode property of
the actual boundary kernel. No capture of the signed branch is assumed. -/
theorem largePrime_apply_discardedBoundaryKernel_eq_zero
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
        (Matrix.toEuclideanLin (oneExitComplementProjection S X)
          (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeBoundaryKernel S X a))) = 0 := by
  let k := PrimeStar.complexifyEuclidean (exactPrincipalMoleculeBoundaryKernel S X a)
  have hk : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) k = 0 := by
    rw [oneExitLargePrimeMatrix_complexify,
      largePrime_apply_exactPrincipalMoleculeBoundaryKernel ha hd]
    ext v
    simp [PrimeStar.complexifyEuclidean_apply]
  have hcomm : oneExitLargePrimeMatrix S X * oneExitComplementProjection S X =
      oneExitComplementProjection S X * oneExitLargePrimeMatrix S X := by
    rw [oneExitComplementProjection, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, (oneExitProjection_commutes_largePrime S X).eq]
  have h := congrArg (fun M ↦ Matrix.toEuclideanLin M k) hcomm
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hk, map_zero] using h

/-- The discarded boundary kernel has the already-proved source-weighted
rate and is annihilated by the forest, uniformly on the power range. This
does not bound the additional signed down-target response. -/
theorem eventually_powerRange_discardedBoundaryKernel_zero_and_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in Filter.atTop, ∀ a : PrimeStar.Vertex S X,
        InPowerRange theta X (a : ℕ) →
          let k := Matrix.toEuclideanLin (oneExitComplementProjection S X)
            (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeBoundaryKernel S X a))
          Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) k = 0 ∧
            ‖k‖ ^ 2 ≤ C * (a : ℝ) * Real.log (X : ℝ) ^ 3 /
              ((X : ℝ) * Real.sqrt (X : ℝ)) := by
  obtain ⟨C, hC, hkernel⟩ :=
    eventually_powerRange_exactPrincipalMoleculeBoundaryKernel_sq_le_scale S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hkernel,
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta]
    with X hbound hwindow
  intro a ha
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  refine ⟨largePrime_apply_discardedBoundaryKernel_eq_zero haY hd, ?_⟩
  let F := oneExitComplementProjection S X
  let x := PrimeStar.complexifyEuclidean (exactPrincipalMoleculeBoundaryKernel S X a)
  have hnorm : ‖F‖ ≤ (1 : ℝ) := by
    simpa only [F] using
      IsStarProjection.norm_le _ (oneExitComplementProjection_isStarProjection S X)
  have hproj : ‖Matrix.toEuclideanLin F x‖ ≤ ‖x‖ := by
    change ‖(EuclideanSpace.equiv (PrimeStar.Vertex S X) ℂ).symm
      (F.mulVec x.ofLp)‖ ≤ ‖x‖
    exact (F.l2_opNorm_mulVec x).trans <| by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)
  have hsquared : ‖Matrix.toEuclideanLin F x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hproj 2
  exact hsquared.trans (by simpa only [x, PrimeStar.norm_complexifyEuclidean] using hbound a ha)

end BoundaryKernelTail

noncomputable section DownTargetKernelSource

private theorem complexify_add {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι) :
    PrimeStar.complexifyEuclidean (x + y) =
      PrimeStar.complexifyEuclidean x + PrimeStar.complexifyEuclidean y := by
  ext i
  simp [PrimeStar.complexifyEuclidean_apply]

/-- The actual forest kernel projection kills the range of the forest. -/
theorem largePrimeZeroModeProjection_apply_largePrime
    (S : Finset ℕ) (X : ℕ) (x : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    largePrimeZeroModeProjection S X
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x) = 0 := by
  classical
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix ℂ)
  have horth : L x ∈ (Module.End.eigenspace L 0)ᗮ := by
    intro w hw
    have hwL : L w = 0 := by
      simpa only [Module.End.mem_eigenspace_iff, zero_smul] using hw
    change inner ℂ w (L x) = 0
    rw [← hL w x, hwL, inner_zero_left]
  exact congrArg (fun v : Module.End.eigenspace L 0 ↦
    (v : EuclideanSpace ℂ (PrimeStar.Vertex S X)))
      (Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal horth)

/-- Constant leaves, with zero centre coordinate, have no forest-kernel part. -/
theorem largePrimeZeroModeProjection_uniformLeaves_eq_zero
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X) (t : ℝ) :
    largePrimeZeroModeProjection S X (PrimeStar.complexifyEuclidean
      (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c 0
        (fun _ ↦ t))) = 0 := by
  have h := largePrimeZeroModeProjection_apply_largePrime S X
    (PrimeStar.complexifyEuclidean
      (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t (fun _ ↦ 0)))
  simpa only [oneExitLargePrimeMatrix_complexify,
    PrimeStar.largePrime_toEuclideanLin_starDataVector (PrimeStar.sqrtCutoff_condition X) hc,
    Finset.sum_const_zero] using h

/-- The kernel projection of actual leaf data is exactly its mean-zero leaf
part. This is the literal projection used by each down-target block. -/
theorem largePrimeZeroModeProjection_leafData_eq_meanZero
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c)
    (f : PrimeStar.Vertex S X → ℝ) :
    largePrimeZeroModeProjection S X (PrimeStar.complexifyEuclidean
      (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c 0 f)) =
      PrimeStar.complexifyEuclidean
        (actualStarMeanZeroLeafVector S X (squareRootCutoff X) c f) := by
  let k := actualStarMeanZeroLeafVector S X (squareRootCutoff X) c f
  let m := finsetMean (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c) f
  have hsplit : PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c 0 f =
      k + PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c 0 (fun _ ↦ m) := by
    ext v
    by_cases hvc : v = c
    · subst v
      simp [k, actualStarMeanZeroLeafVector]
    · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c
      · simp only [k, actualStarMeanZeroLeafVector, PiLp.add_apply,
          PrimeStar.largePrimeStarDataVector_leaf _ _ hv, m, sub_add_cancel]
      · simp only [k, actualStarMeanZeroLeafVector, PiLp.add_apply,
          PrimeStar.largePrimeStarDataVector_outside _ _ hvc hv, add_zero]
  have hkL : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
      (PrimeStar.complexifyEuclidean k) = 0 := by
    rw [oneExitLargePrimeMatrix_complexify,
      largePrime_apply_actualStarMeanZeroLeafVector f (PrimeStar.sqrtCutoff_condition X) hc hd]
    ext v
    simp [PrimeStar.complexifyEuclidean_apply]
  have hk : largePrimeZeroModeProjection S X (PrimeStar.complexifyEuclidean k) =
      PrimeStar.complexifyEuclidean k := by
    apply Submodule.starProjection_eq_self_iff.mpr
    simpa only [Module.End.mem_eigenspace_iff, zero_smul] using hkL
  rw [hsplit, complexify_add, map_add, hk,
    largePrimeZeroModeProjection_uniformLeaves_eq_zero hc, add_zero]

/-- Removing the leaf average cannot increase the actual star's squared mass. -/
theorem norm_sq_actualStarMeanZeroLeafVector_le
    {S : Finset ℕ} {X Y : ℕ} {c : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y c)
    (f : PrimeStar.Vertex S X → ℝ) :
    ‖actualStarMeanZeroLeafVector S X Y c f‖ ^ 2 ≤
      ∑ v ∈ PrimeStar.largePrimeLeaves S X Y c, f v ^ 2 := by
  have hne : (PrimeStar.largePrimeLeaves S X Y c).Nonempty :=
    Finset.card_pos.mp hd
  rw [← real_inner_self_eq_norm_sq, actualStarMeanZeroLeafVector,
    PrimeStar.largePrimeStarDataVector_inner]
  simpa only [← pow_two, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] using
    sum_sq_sub_finsetMean_le_sum_sq hne f

/-- A partial constant leaf vector pays only the number of selected leaves,
not the full target degree. -/
theorem norm_sq_actualStarPartialLeafKernel_le
    {S : Finset ℕ} {X Y : ℕ} {c : PrimeStar.Vertex S X}
    (hd : 0 < PrimeStar.largePrimeStarDegree S X Y c)
    (P : Finset (PrimeStar.Vertex S X))
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X Y c) (t : ℝ) :
    ‖actualStarMeanZeroLeafVector S X Y c (fun v ↦ if v ∈ P then t else 0)‖ ^ 2 ≤
      (P.card : ℝ) * t ^ 2 := by
  refine (norm_sq_actualStarMeanZeroLeafVector_le hd _).trans_eq ?_
  calc
    (∑ v ∈ PrimeStar.largePrimeLeaves S X Y c, (if v ∈ P then t else 0) ^ 2) =
        ∑ v ∈ P, (if v ∈ P then t else 0) ^ 2 := by
      symm
      exact Finset.sum_subset hP (by intro v _ hv; simp [hv])
    _ = (P.card : ℝ) * t ^ 2 := by simp

/-- The actual leaf-kernel contribution of one canonical down-prime to the
positive source; its leaf coefficient is the normalized boundary amplitude. -/
def canonicalDownZeroSource (S : Finset ℕ) (X : ℕ)
    (a : PrimeStar.Vertex S X) (q : PrimeStar.CanonicalDownIndex a) : MoleculeAmbient S X :=
  actualStarMeanZeroLeafVector S X (squareRootCutoff X)
    (PrimeStar.canonicalDownTarget a q)
    (fun v ↦ if v ∈ PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q) q then
        moleculePositiveStarMode S X a a / moleculeStarEnergy S X a else 0)

/-- Each canonical down-prime contributes at most one half of squared mass.
The boundary leaf count is used exactly, before any divisor summation. -/
theorem norm_sq_canonicalDownZeroSource_le_half
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a) :
    ‖canonicalDownZeroSource S X a q‖ ^ 2 ≤ 1 / 2 := by
  let P := PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
    (PrimeStar.canonicalDownTarget a q) q
  have hP := PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves
    (S := S) (X := X) (Y := squareRootCutoff X)
    (q := (q : ℕ)) (PrimeStar.canonicalDownTarget a q)
  have hcard : P.card = PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a :=
    PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
  have htarget : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q) :=
    (hcard.symm ▸ hd).trans_le (Finset.card_le_card hP)
  have hbound := norm_sq_actualStarPartialLeafKernel_le htarget P hP
    (moleculePositiveStarMode S X a a / moleculeStarEnergy S X a)
  have hmu : moleculeStarEnergy S X a ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hcenter : moleculePositiveStarMode S X a a ^ 2 = (1 : ℝ) / 2 :=
    PrimeStar.sq_largePrimeNormalizedStarMode_center (by norm_num) hd
  have hd0 : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) ≠ 0 :=
    by exact_mod_cast Nat.ne_of_gt hd
  refine hbound.trans_eq ?_
  rw [hcard, div_pow, hcenter, hmu]
  field_simp

/-- Different down-prime kernel sources lie in disjoint actual stars. -/
theorem inner_canonicalDownZeroSource_eq_zero
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    {q r : PrimeStar.CanonicalDownIndex a} (hqr : q ≠ r) :
    ⟪canonicalDownZeroSource S X a q, canonicalDownZeroSource S X a r⟫_ℝ = 0 := by
  apply PrimeStar.inner_largePrimeStarDataVector_eq_zero_of_disjoint
  exact PrimeStar.disjoint_canonicalExitTarget_starSupport hS
    (PrimeStar.sqrtCutoff_condition X) ha
    (i := Sum.inr q) (j := Sum.inr r) (by simpa using hqr)

/-- The actual down-target kernel sum has squared norm at most omega(a)/2.
Orthogonality retains the divisor count rather than its square. -/
theorem norm_sq_sum_canonicalDownZeroSource_le
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ‖∑ q : PrimeStar.CanonicalDownIndex a, canonicalDownZeroSource S X a q‖ ^ 2 ≤
      ((a : ℕ).primeFactors.card : ℝ) / 2 := by
  have horth : ‖∑ q : PrimeStar.CanonicalDownIndex a, canonicalDownZeroSource S X a q‖ ^ 2 =
      ∑ q : PrimeStar.CanonicalDownIndex a, ‖canonicalDownZeroSource S X a q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_eq_single q]
    · exact real_inner_self_eq_norm_sq _
    · intro r _ hrq
      exact inner_canonicalDownZeroSource_eq_zero hS ha hrq.symm
    · simp
  rw [horth]
  calc
    (∑ q : PrimeStar.CanonicalDownIndex a, ‖canonicalDownZeroSource S X a q‖ ^ 2) ≤
        ∑ q : PrimeStar.CanonicalDownIndex a, (1 : ℝ) / 2 :=
      Finset.sum_le_sum (fun q _ ↦ norm_sq_canonicalDownZeroSource_le_half hS ha hd q)
    _ = ((a : ℕ).primeFactors.card : ℝ) / 2 := by
      simp [PrimeStar.CanonicalDownIndex, div_eq_mul_inv]

end DownTargetKernelSource

noncomputable section SignedDownSourceIdentification

/-- Local adjacency decision procedure for the real small-prime source. -/
local instance signedDownSourceSmallPrimeDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

private theorem smallPrime_complexify (S : Finset ℕ) (X : ℕ)
    (x : MoleculeAmbient S X) :
    Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
        (PrimeStar.complexifyEuclidean x) =
      PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) x) := by
  classical
  apply PiLp.ext
  intro i
  simp only [oneExitSmallPrimeMatrix, Matrix.toLpLin_apply,
    PrimeStar.complexifyEuclidean_apply, Matrix.mulVec, dotProduct,
    SimpleGraph.adjMatrix_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj i j
  · rw [if_pos hij, if_pos hij]
    norm_num
  · rw [if_neg hij, if_neg hij]
    norm_num

private theorem half_sub_starData (S : Finset ℕ) (X Y : ℕ)
    (c : PrimeStar.Vertex S X) (t : ℝ) (f : PrimeStar.Vertex S X → ℝ) :
    (1 / 2 : ℝ) • (PrimeStar.largePrimeStarDataVector S X Y c t f -
      PrimeStar.largePrimeStarDataVector S X Y c t (fun v ↦ -f v)) =
      PrimeStar.largePrimeStarDataVector S X Y c 0 f := by
  ext v
  by_cases hvc : v = c
  · subst v
    simp
  · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X Y c
    · simp only [PiLp.smul_apply, PiLp.sub_apply,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hv, smul_eq_mul]
      ring
    · simp only [PiLp.smul_apply, PiLp.sub_apply,
        PrimeStar.largePrimeStarDataVector_outside _ _ hvc hv, sub_zero, smul_zero]

private theorem half_sub_actualUpSource (S : Finset ℕ) (X Y : ℕ)
    (c : PrimeStar.Vertex S X) (mu t : ℝ) :
    (1 / 2 : ℝ) • (PrimeStar.actualUpStarFirstExit S X Y c mu t -
      PrimeStar.actualUpStarFirstExit S X Y c (-mu) t) =
      PrimeStar.largePrimeStarDataVector S X Y c 0 (fun _ ↦ t / mu) := by
  simpa only [PrimeStar.actualUpStarFirstExit, div_neg] using
    half_sub_starData S X Y c t (fun _ ↦ t / mu)

private theorem half_sub_actualDownSource (S : Finset ℕ) (X Y : ℕ)
    (c : PrimeStar.Vertex S X) (P : Finset (PrimeStar.Vertex S X)) (mu t : ℝ) :
    (1 / 2 : ℝ) • (PrimeStar.actualDownStarFirstExit S X Y c P mu t -
      PrimeStar.actualDownStarFirstExit S X Y c P (-mu) t) =
      PrimeStar.largePrimeStarDataVector S X Y c 0
        (fun v ↦ if v ∈ P then t / mu else 0) := by
  have hf : (fun v : PrimeStar.Vertex S X ↦ if v ∈ P then t / (-mu) else 0) =
      (fun v ↦ -(if v ∈ P then t / mu else 0)) := by
    funext v
    split_ifs <;> simp [div_neg]
  simp only [PrimeStar.actualDownStarFirstExit, hf]
  exact half_sub_starData S X Y c t (fun v ↦ if v ∈ P then t / mu else 0)

private theorem canonicalUp_uniformLeaves_zeroProjection
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a) (t : ℝ) :
    largePrimeZeroModeProjection S X (PrimeStar.complexifyEuclidean
      (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) 0 (fun _ ↦ t))) = 0 := by
  by_cases htarget : (PrimeStar.canonicalUpTarget hS a q : ℕ) ≤ squareRootCutoff X
  · exact largePrimeZeroModeProjection_uniformLeaves_eq_zero htarget t
  · have hqdata := Finset.mem_filter.mp q.property
    have hiso := PrimeStar.canonicalUpTarget_isIsolated_of_cutoff_lt ha
      (PrimeStar.sqrtCutoff_condition X) (Nat.mem_primesLE.mp hqdata.1).2
      (Nat.mem_primesLE.mp hqdata.1).1 (PrimeStar.canonicalUpTarget_coe hS a q).symm
      (Nat.lt_of_not_ge htarget)
    have hz : PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) 0 (fun _ ↦ t) = 0 := by
      ext v
      by_cases hv : v = PrimeStar.canonicalUpTarget hS a q
      · subst v
        simp
      · have hleaf : v ∉ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) :=
          fun h ↦ hiso v (PrimeStar.mem_largePrimeLeaves.mp h)
        exact PrimeStar.largePrimeStarDataVector_outside _ _ hv hleaf
    rw [hz]
    have hc0 : PrimeStar.complexifyEuclidean (0 : MoleculeAmbient S X) = 0 := by
      ext v
      simp [PrimeStar.complexifyEuclidean_apply]
    rw [hc0, map_zero]

/-- The actual signed zero-source difference is precisely the sum of the
canonical down-target leaf kernels. Inactive up-target centres cancel before
projection; no global degree uniqueness is assumed. -/
theorem signedZeroModeSourceDifference_eq_sum_downKernels
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    signedZeroModeSourceDifference S X a =
      PrimeStar.complexifyEuclidean
        (∑ q : PrimeStar.CanonicalDownIndex a, canonicalDownZeroSource S X a q) := by
  let t := moleculePositiveStarMode S X a a
  let mu := moleculeStarEnergy S X a
  have hcenter : PrimeStar.largePrimeNormalizedStarMode S X
      (squareRootCutoff X) a (-1) a = t := by
    dsimp [t, moleculePositiveStarMode]
    rw [largePrimeNormalizedStarMode_center_eq_inv_sqrt_two (by norm_num) hd,
      largePrimeNormalizedStarMode_center_eq_inv_sqrt_two (by norm_num) hd]
  have hsrc : (1 / 2 : ℝ) • (exactBoundaryModeInteriorSource S X a 1 -
      exactBoundaryModeInteriorSource S X a (-1)) =
      (∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
        PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) 0 (fun _ ↦ t / mu)) +
      (∑ q : PrimeStar.CanonicalDownIndex a,
        PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) 0
          (fun v ↦ if v ∈ PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q) q then t / mu else 0)) := by
    rw [exactBoundaryModeInteriorSource_eq_sum_canonicalBlocks hS ha hd (by norm_num),
      exactBoundaryModeInteriorSource_eq_sum_canonicalBlocks hS ha hd (by norm_num)]
    simp only [one_mul, neg_one_mul, hcenter]
    change (1 / 2 : ℝ) • ((_ + _) - (_ + _)) = _
    rw [add_sub_add_comm, smul_add, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.smul_sum, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun q _ ↦ half_sub_actualUpSource _ _ _ _ mu t)
    · exact Finset.sum_congr rfl (fun q _ ↦ half_sub_actualDownSource _ _ _ _ _ mu t)
  have hrewrite : signedZeroModeSourceDifference S X a =
      largePrimeZeroModeProjection S X (PrimeStar.complexifyEuclidean
        ((1 / 2 : ℝ) • (exactBoundaryModeInteriorSource S X a 1 -
          exactBoundaryModeInteriorSource S X a (-1)))) := by
    simp only [signedZeroModeSourceDifference, PrimeStar.complexifyEuclidean_smul,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, map_smul,
      PrimeStar.complexifyEuclidean_sub, exactBoundaryModeInteriorSource_eq_smallPrime,
      smallPrime_complexify, map_sub, moleculePositiveStarMode]
  rw [hrewrite, hsrc, complexify_add, map_add, complexifyEuclidean_sum, complexifyEuclidean_sum,
    map_sum, map_sum]
  have hup : (∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      largePrimeZeroModeProjection S X (PrimeStar.complexifyEuclidean
        (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) 0 (fun _ ↦ t / mu)))) = 0 :=
    Finset.sum_eq_zero (fun q _ ↦ canonicalUp_uniformLeaves_zeroProjection hS ha q _)
  rw [hup, zero_add, complexifyEuclidean_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hqle : (PrimeStar.canonicalDownTarget a q : ℕ) ≤ squareRootCutoff X :=
    (Nat.div_le_self _ _).trans ha
  have hP := PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves
    (S := S) (X := X) (Y := squareRootCutoff X) (q := (q : ℕ))
    (PrimeStar.canonicalDownTarget a q)
  have hcard := PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
  have htarget : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q) :=
    (hcard.symm ▸ hd).trans_le (Finset.card_le_card hP)
  exact largePrimeZeroModeProjection_leafData_eq_meanZero hqle htarget _

/-- The actual signed zero-source difference satisfies the manuscript's
omega(a)/2 bound, with the canonical down-target identification discharged. -/
theorem norm_sq_signedZeroModeSourceDifference_le
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ‖signedZeroModeSourceDifference S X a‖ ^ 2 ≤ ((a : ℕ).primeFactors.card : ℝ) / 2 := by
  rw [signedZeroModeSourceDifference_eq_sum_downKernels hS ha hd,
    PrimeStar.norm_complexifyEuclidean]
  exact norm_sq_sum_canonicalDownZeroSource_le hS ha hd

end SignedDownSourceIdentification

noncomputable section SourceLocalSpectralCapture

/-- Each actual star-data block satisfies the cubic forest relation, also
when its degree is zero. Only the source star, not global simplicity, enters. -/
theorem largePrime_starData_cubic
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X) (t : ℝ)
    (f : PrimeStar.Vertex S X → ℝ) :
    let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
    let x := PrimeStar.complexifyEuclidean
      (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f)
    L (L (L x)) =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℂ) • L x := by
  dsimp only
  simp only [oneExitLargePrimeMatrix_complexify,
    PrimeStar.largePrime_toEuclideanLin_starDataVector (PrimeStar.sqrtCutoff_condition X) hc,
    Finset.sum_const, nsmul_eq_mul]
  ext v
  by_cases hvc : v = c
  · subst v
    simp [PrimeStar.complexifyEuclidean_apply, PrimeStar.largePrimeStarDegree]
  · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c
    · simp [PrimeStar.complexifyEuclidean_apply,
        PrimeStar.largePrimeStarDataVector_leaf _ _ hv, PrimeStar.largePrimeStarDegree]
    · simp [PrimeStar.complexifyEuclidean_apply,
        PrimeStar.largePrimeStarDataVector_outside _ _ hvc hv]

private theorem forest_eigenprojection_apply
    (S : Finset ℕ) (X : ℕ) (lambda : ℂ)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
    let P := (Module.End.eigenspace L lambda).starProjection
    P (L x) = lambda • P x := by
  classical
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let P := (Module.End.eigenspace L lambda).starProjection
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix ℂ)
  have hcomm := LinearMap.congr_fun
    (eigenprojection_commutes_of_commute L L hL (Commute.refl L) lambda).eq x
  change P (L x) = L (P x) at hcomm
  have hmem : P x ∈ Module.End.eigenspace L lambda :=
    Submodule.starProjection_apply_mem _ _
  exact hcomm.trans (Module.End.mem_eigenspace_iff.mp hmem)

/-- A nonzero spectral projection kills a source block of a different degree.
Equal-degree stars elsewhere in the forest need not be simple or separated. -/
theorem largePrime_eigenprojection_starData_eq_zero
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X) (t : ℝ)
    (f : PrimeStar.Vertex S X → ℝ) {lambda : ℂ}
    (hlambda : lambda ≠ 0)
    (hdegree : lambda ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℂ)) :
    (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
        (PrimeStar.complexifyEuclidean
          (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f)) = 0 := by
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let P := (Module.End.eigenspace L lambda).starProjection
  let x := PrimeStar.complexifyEuclidean
    (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f)
  let d : ℂ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c
  have hproj (v : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
      P (L v) = lambda • P v := forest_eigenprojection_apply S X lambda v
  have h := congrArg P (largePrime_starData_cubic hc t f)
  change P (L (L (L x))) = P (d • L x) at h
  simp only [map_smul, hproj, smul_smul] at h
  have hzero : (lambda * (lambda ^ 2 - d)) • P x = 0 := by
    have hsub := sub_eq_zero.mpr h
    rw [← sub_smul] at hsub
    have heq : lambda * (lambda ^ 2 - d) =
        lambda * (lambda * lambda) - d * lambda := by ring
    rw [heq]
    exact hsub
  exact (smul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero hlambda (sub_ne_zero.mpr hdegree))

/-- At either nonzero signed star eigenvalue, the actual spectral component
is a quadratic expression in the forest action. This is local to the source
block and allows arbitrary multiplicity of the global eigenvalue. -/
theorem largePrime_eigenprojection_starData_eq_quadratic
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X) (t : ℝ)
    (f : PrimeStar.Vertex S X → ℝ) {lambda : ℝ}
    (hlambda : lambda ≠ 0)
    (hdegree : lambda ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ)) :
    let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
    let x := PrimeStar.complexifyEuclidean
      (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f)
    (Module.End.eigenspace L (lambda : ℂ)).starProjection x =
      (1 / (2 * (lambda : ℂ) ^ 2)) • (L (L x) + (lambda : ℂ) • L x) := by
  classical
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let x := PrimeStar.complexifyEuclidean
    (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f)
  let z : ℂ := lambda
  let y := (1 / (2 * z ^ 2)) • (L (L x) + z • L x)
  have hz : z ≠ 0 := by
    dsimp only [z]
    exact_mod_cast hlambda
  have hcubic : L (L (L x)) = z ^ 2 • L x := by
    have h := largePrime_starData_cubic hc t f
    have hd : z ^ 2 =
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℂ) := by
      dsimp only [z]
      exact_mod_cast hdegree
    change L (L (L x)) =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℂ) • L x at h
    rw [← hd] at h
    exact h
  have hmem : y ∈ Module.End.eigenspace L z := by
    rw [Module.End.mem_eigenspace_iff]
    dsimp only [y]
    rw [map_smul, map_add, map_smul, hcubic]
    module
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix ℂ)
  apply Submodule.eq_starProjection_of_mem_orthogonal hmem
  intro w hw
  have hwL : L w = z • w := Module.End.mem_eigenspace_iff.mp hw
  have hi (v : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
      inner ℂ w (L v) = z * inner ℂ w v := by
    rw [← hL, hwL, inner_smul_left]
    simp [z]
  simp only [y, inner_sub_right, inner_smul_right, inner_add_right, hi]
  field_simp [hz]
  ring

/-- The charged direction of one source block, with its exact coefficient.
Only the centre coordinate and sum of leaf coordinates enter, even when
the source has a nonzero leaf-kernel component. -/
theorem largePrime_eigenprojection_starData_eq_smul_signedData
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X) (t : ℝ)
    (f : PrimeStar.Vertex S X → ℝ) {lambda : ℝ}
    (hlambda : lambda ≠ 0)
    (hdegree : lambda ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ)) :
    (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
        (PrimeStar.complexifyEuclidean
          (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f)) =
      (((t + (∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c, f v) /
        lambda) / (2 * lambda) : ℝ) : ℂ) •
          PrimeStar.complexifyEuclidean
            (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c lambda
              (fun _ ↦ 1)) := by
  rw [largePrime_eigenprojection_starData_eq_quadratic hc t f hlambda hdegree]
  simp only [oneExitLargePrimeMatrix_complexify,
    PrimeStar.largePrime_toEuclideanLin_starDataVector (PrimeStar.sqrtCutoff_condition X) hc,
    Finset.sum_const, nsmul_eq_mul]
  have hd : ((PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c).card : ℝ) =
      lambda ^ 2 := hdegree.symm
  have hz : (lambda : ℂ) ≠ 0 := by exact_mod_cast hlambda
  ext v
  by_cases hvc : v = c
  · subst v
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
      PrimeStar.complexifyEuclidean_apply, PrimeStar.largePrimeStarDataVector_center]
    rw [hd]
    push_cast
    field_simp [hz]
  · by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c
    · simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
        PrimeStar.complexifyEuclidean_apply, PrimeStar.largePrimeStarDataVector_leaf _ _ hv]
      push_cast
      field_simp [hz]
      ring
    · simp [PrimeStar.complexifyEuclidean_apply,
        PrimeStar.largePrimeStarDataVector_outside _ _ hvc hv]

private theorem largePrime_eigenprojection_isolatedStarData_eq_zero
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hiso : (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).IsIsolated c)
    (t : ℝ) (f : PrimeStar.Vertex S X → ℝ) {lambda : ℂ}
    (hlambda : lambda ≠ 0) :
    (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
        (PrimeStar.complexifyEuclidean
          (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f)) = 0 := by
  classical
  let v := PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f
  have hrestrict : PrimeStar.restrictEuclideanToFinset {c} v = v := by
    ext w
    by_cases hw : w = c
    · subst w
      simp
    · have hleaf : w ∉ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c :=
        fun h ↦ hiso w (PrimeStar.mem_largePrimeLeaves.mp h)
      simp [PrimeStar.restrictEuclideanToFinset_apply, hw, v,
        PrimeStar.largePrimeStarDataVector_outside _ _ hw hleaf]
  have hzero := PrimeStar.largePrime_toEuclideanLin_restrict_isolated_eq_zero
    {c} v (by simpa using hiso)
  rw [hrestrict] at hzero
  have hc : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
      (PrimeStar.complexifyEuclidean v) = 0 := by
    rw [oneExitLargePrimeMatrix_complexify, hzero]
    ext w
    simp [PrimeStar.complexifyEuclidean_apply]
  have h := forest_eigenprojection_apply S X lambda (PrimeStar.complexifyEuclidean v)
  dsimp only at h
  rw [hc, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hlambda

private theorem canonicalUp_eigenprojection_eq_zero
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (mu t : ℝ) {lambda : ℂ} (hlambda : lambda ≠ 0)
    (hdegree : lambda ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) : ℂ)) :
    (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
        (PrimeStar.complexifyEuclidean
          (PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) mu t)) = 0 := by
  by_cases hc : (PrimeStar.canonicalUpTarget hS a q : ℕ) ≤ squareRootCutoff X
  · exact largePrime_eigenprojection_starData_eq_zero hc t _ hlambda hdegree
  · have hqdata := Finset.mem_filter.mp q.property
    have hiso := PrimeStar.canonicalUpTarget_isIsolated_of_cutoff_lt ha
      (PrimeStar.sqrtCutoff_condition X) (Nat.mem_primesLE.mp hqdata.1).2
      (Nat.mem_primesLE.mp hqdata.1).1 (PrimeStar.canonicalUpTarget_coe hS a q).symm
      (Nat.lt_of_not_ge hc)
    exact largePrime_eigenprojection_isolatedStarData_eq_zero hiso t _ hlambda

/-- A selected canonical down-target spectral component is captured when
all other blocks of this particular positive source have different degrees.
No separation from stars outside that source support is required. -/
theorem oneExitProjection_fixes_downSource_spectralComponent
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a) {lambda : ℂ} (hlambda : lambda ≠ 0)
    (hup : ∀ r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      lambda ^ 2 ≠ (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a r) : ℂ))
    (hdown : ∀ r : PrimeStar.CanonicalDownIndex a, r ≠ q →
      lambda ^ 2 ≠ (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a r) : ℂ)) :
    let P := (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
    let v := PrimeStar.complexifyEuclidean
      (PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q)
        (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) q)
        (moleculeStarEnergy S X a) (moleculePositiveStarMode S X a a))
    Matrix.toEuclideanLin (oneExitProjection S X) (P v) = P v := by
  classical
  let P := (Module.End.eigenspace
    (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
  let v := PrimeStar.complexifyEuclidean
    (PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q)
      (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) q)
      (moleculeStarEnergy S X a) (moleculePositiveStarMode S X a a))
  have hsource := oneExitProjection_fixes_spectralComponent S X lambda _
    (oneExitProjection_fixes_positiveStarSource ha hd)
  have hdecomp : P (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
      (PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a))) = P v := by
    rw [smallPrime_complexify, moleculePositiveStarMode,
      ← exactBoundaryModeInteriorSource_eq_smallPrime (eps := 1)]
    rw [exactBoundaryModeInteriorSource_eq_sum_canonicalBlocks hS ha hd (by norm_num)]
    simp only [one_mul, complexify_add, complexifyEuclidean_sum, map_add, map_sum]
    have hu : (∑ r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
        P (PrimeStar.complexifyEuclidean
          (PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a r) (moleculeStarEnergy S X a)
            (moleculePositiveStarMode S X a a)))) = 0 := by
      exact Finset.sum_eq_zero (fun r _ ↦
        canonicalUp_eigenprojection_eq_zero hS ha r _ _ hlambda (hup r))
    simp only [moleculePositiveStarMode] at hu
    rw [hu, zero_add, Finset.sum_eq_single q]
    · rfl
    · intro r _ hrq
      exact largePrime_eigenprojection_starData_eq_zero
        ((Nat.div_le_self _ _).trans ha) _ _ hlambda (hdown r hrq)
    · simp
  change Matrix.toEuclideanLin (oneExitProjection S X) (P _) = P _ at hsource
  rw [hdecomp] at hsource
  exact hsource

end SourceLocalSpectralCapture

noncomputable section CanonicalNegativeModeCapture

/-- The selected down-target's negative spectral coefficient is nonzero
when source and target degrees differ. The sum uses the actual partial
leaf set, whose cardinality equals the boundary degree. -/
theorem canonicalDown_negativeSpectralCoefficient_ne_zero
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a)
    (hne : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a ≠
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q)) :
    let c := PrimeStar.canonicalDownTarget a q
    let t := moleculePositiveStarMode S X a a
    let mu := moleculeStarEnergy S X a
    let lambda := -moleculeStarEnergy S X c
    (t + (∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c,
      if v ∈ PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) c q then
        t / mu else 0) / lambda) / (2 * lambda) ≠ 0 := by
  classical
  let c := PrimeStar.canonicalDownTarget a q
  let t := moleculePositiveStarMode S X a a
  let mu := moleculeStarEnergy S X a
  let nu := moleculeStarEnergy S X c
  let F := PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c
  let P := PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) c q
  have hP : P ⊆ F := PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves c
  have hcard : P.card = PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a :=
    PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
  have hdt : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c :=
    (hcard.symm ▸ hd).trans_le (Finset.card_le_card hP)
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hnu : 0 < nu := Real.sqrt_pos.mpr (by exact_mod_cast hdt)
  have hmuSq : mu ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hnuSq : nu ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have ht : t ≠ 0 := by
    have hs : t ^ 2 = (1 : ℝ) / 2 :=
      PrimeStar.sq_largePrimeNormalizedStarMode_center (by norm_num) hd
    intro h
    rw [h] at hs
    norm_num at hs
  have hsum : (∑ v ∈ F, if v ∈ P then t / mu else 0) = mu * t := by
    calc
      _ = ∑ v ∈ P, (if v ∈ P then t / mu else 0) := by
        symm
        exact Finset.sum_subset hP (by intro v _ hv; simp [hv])
      _ = (P.card : ℝ) * (t / mu) := by simp
      _ = mu * t := by
        rw [hcard, ← hmuSq]
        field_simp [hmu.ne']
  change (t + (∑ v ∈ F, if v ∈ P then t / mu else 0) / (-nu)) /
    (2 * (-nu)) ≠ 0
  rw [hsum]
  intro hz
  have hnum : t + mu * t / (-nu) = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hnu.ne'))
  have heq : mu = nu := by
    field_simp [hnu.ne'] at hnum
    have hprod : t * (mu - nu) = 0 := by nlinarith [hnum]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ht)
  apply hne
  have hsquares := congrArg (fun r : ℝ ↦ r ^ 2) heq
  rw [hmuSq, hnuSq] at hsquares
  exact_mod_cast hsquares

/-- Source-local degree separation and the exact nonzero down coefficient
capture the normalized negative target mode. This finite theorem makes no
global degree-uniqueness assumption. -/
theorem oneExitProjection_fixes_negativeDownMode_of_sourceLocalDegrees
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a)
    (hne : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a ≠
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q))
    (hup : ∀ r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) ≠
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a r))
    (hdown : ∀ r : PrimeStar.CanonicalDownIndex a, r ≠ q →
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) ≠
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a r)) :
    Matrix.toEuclideanLin (oneExitProjection S X)
      (PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q) (-1))) =
      PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q) (-1)) := by
  classical
  let c := PrimeStar.canonicalDownTarget a q
  let mu := moleculeStarEnergy S X c
  let lambda : ℝ := -mu
  let t := moleculePositiveStarMode S X a a
  let f := fun v ↦ if v ∈ PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) c q then
    t / moleculeStarEnergy S X a else 0
  let beta := (t + (∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c, f v) /
    lambda) / (2 * lambda)
  let v := PrimeStar.complexifyEuclidean
    (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c lambda (fun _ ↦ 1))
  let R := Matrix.toEuclideanLin (oneExitProjection S X)
  have hc : (c : ℕ) ≤ squareRootCutoff X := (Nat.div_le_self _ _).trans ha
  have hP := PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves
    (S := S) (X := X) (Y := squareRootCutoff X) (q := (q : ℕ)) c
  have hcard := PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q
  have hdt : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c :=
    (hcard.symm ▸ hd).trans_le (Finset.card_le_card hP)
  have hl : lambda ≠ 0 := neg_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hdt))
  have hlsq : lambda ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ) := by
    dsimp [lambda, mu, moleculeStarEnergy]
    rw [neg_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hlC : (lambda : ℂ) ≠ 0 := by exact_mod_cast hl
  have hlsqC : (lambda : ℂ) ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℂ) := by
    exact_mod_cast hlsq
  have hcapture := oneExitProjection_fixes_downSource_spectralComponent hS ha hd q hlC
    (fun r ↦ by rw [hlsqC]; exact_mod_cast hup r)
    (fun r hr ↦ by rw [hlsqC]; exact_mod_cast hdown r hr)
  have hcomponent := largePrime_eigenprojection_starData_eq_smul_signedData hc t f hl hlsq
  change _ = (beta : ℂ) • v at hcomponent
  simp only [PrimeStar.actualDownStarFirstExit] at hcapture
  change R ((Module.End.eigenspace
    (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
      (PrimeStar.complexifyEuclidean
        (PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f))) = _ at hcapture
  rw [hcomponent, map_smul] at hcapture
  have hbeta : (beta : ℂ) ≠ 0 := by
    have hb : beta ≠ 0 :=
      canonicalDown_negativeSpectralCoefficient_ne_zero hS ha hd q hne
    exact_mod_cast hb
  have hv : R v = v := smul_right_injective _ hbeta hcapture
  let w := PrimeStar.largePrimeEuclideanStarVector S X (squareRootCutoff X) c (-1)
  have hvw : v = (-1 : ℂ) • PrimeStar.complexifyEuclidean w := by
    ext b
    by_cases hb : b = c
    · subst b
      simp [v, w, PrimeStar.largePrimeEuclideanStarVector_eq_starDataVector,
        PrimeStar.complexifyEuclidean_apply, lambda, mu, moleculeStarEnergy]
    · by_cases hleaf : b ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c
      · simp [v, w, PrimeStar.largePrimeEuclideanStarVector_eq_starDataVector,
          PrimeStar.complexifyEuclidean_apply, PrimeStar.largePrimeStarDataVector_leaf _ _ hleaf]
      · simp [v, w, PrimeStar.largePrimeEuclideanStarVector_eq_starDataVector,
          PrimeStar.complexifyEuclidean_apply, PrimeStar.largePrimeStarDataVector_outside _ _ hb hleaf]
  rw [hvw, map_smul] at hv
  have hw : R (PrimeStar.complexifyEuclidean w) = PrimeStar.complexifyEuclidean w :=
    smul_right_injective _ (by norm_num : (-1 : ℂ) ≠ 0) hv
  change R (PrimeStar.complexifyEuclidean (‖w‖⁻¹ • w)) =
    PrimeStar.complexifyEuclidean (‖w‖⁻¹ • w)
  rw [PrimeStar.complexifyEuclidean_smul, map_smul, hw]

end CanonicalNegativeModeCapture

noncomputable section SourceLocalPrimeSeparation

open Filter Topology

/-- Global PNT gives a strict allowed-prime count increase between fixed
integer multiples. This will separate the other down-targets of ell*a;
it is not an adjacent-centre or short-interval estimate. -/
theorem eventually_allowedPrimeCount_mul_lt_succ_mul
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop,
      PrimeStar.allowedPrimeCount S (k * n) <
        PrimeStar.allowedPrimeCount S ((k + 1) * n) := by
  obtain ⟨N, hgap⟩ := eventually_atTop.mp
    (PrimeStar.eventually_allowedPrimeCount_fixedDenominator_gap_ge
      S hS hk (Nat.lt_succ_self k))
  filter_upwards [eventually_ge_atTop (max N 2)] with n hn
  let Z := k * (k + 1) * n
  have hnZ : n ≤ Z := by
    dsimp only [Z]
    have hkprod : 1 ≤ k * (k + 1) := Nat.mul_pos hk (by omega)
    nlinarith
  have hZ : 2 ≤ Z := (le_max_right N 2).trans (hn.trans hnZ)
  have hN : N ≤ Z := (le_max_left N 2).trans (hn.trans hnZ)
  have hdivk : Z / k = (k + 1) * n := by
    dsimp only [Z]
    rw [Nat.mul_assoc, Nat.mul_div_right _ hk]
  have hdivsucc : Z / (k + 1) = k * n := by
    rw [show Z = (k * n) * (k + 1) by dsimp [Z]; ring,
      Nat.mul_div_left _ (by omega)]
  have hcoeff : 0 < (((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) / 2) := by
    apply div_pos _ (by norm_num)
    exact sub_pos.mpr (inv_strictAnti₀ (by exact_mod_cast hk) (by exact_mod_cast Nat.lt_succ_self k))
  have hmain : 0 < (Z : ℝ) / Real.log (Z : ℝ) :=
    div_pos (by positivity) (Real.log_pos (by exact_mod_cast (show 1 < Z by omega)))
  have h := (mul_pos hcoeff hmain).trans_le (hgap Z hN)
  rw [hdivk, hdivsucc] at h
  exact_mod_cast (sub_pos.mp h)

/-- A fixed-multiple prime interval separates two divisor targets. The floor
errors are paid before applying the prime-count gap. -/
private theorem allowedPrimeCount_divisorTarget_lt
    {S : Finset ℕ} {X A ell r : ℕ} (hA : 0 < A) (hell : 0 < ell)
    (hellA : ell ∣ A) (hrA : r ∣ A) (hellr : ell < r)
    (hN : 4 * ell + 4 ≤ X / A)
    (hgap : PrimeStar.allowedPrimeCount S (2 * ell * (X / A / 2 + 1)) <
      PrimeStar.allowedPrimeCount S ((2 * ell + 1) * (X / A / 2 + 1))) :
    PrimeStar.allowedPrimeCount S (X / (A / ell)) <
      PrimeStar.allowedPrimeCount S (X / (A / r)) := by
  have hepos : 0 < A / ell := Nat.div_pos (Nat.le_of_dvd hA hellA) hell
  have hrpos : 0 < A / r := Nat.div_pos (Nat.le_of_dvd hA hrA) (hell.trans hellr)
  have hemul : A / ell * ell = A := Nat.div_mul_cancel hellA
  have hrmul : A / r * r = A := Nat.div_mul_cancel hrA
  have hupper : X / (A / ell) < ell * (X / A + 1) := by
    apply (Nat.div_lt_iff_lt_mul hepos).2
    have hx := Nat.lt_mul_div_succ X hA
    nlinarith [hemul]
  have hlower : r * (X / A) ≤ X / (A / r) := by
    apply (Nat.le_div_iff_mul_le hrpos).2
    have hx := Nat.div_mul_le_self X A
    nlinarith [hrmul]
  have hhalf : X / A + 1 ≤ 2 * (X / A / 2 + 1) := by omega
  have hhalf' : 2 * (X / A / 2 + 1) ≤ X / A + 2 := by omega
  have hleft : X / (A / ell) ≤ 2 * ell * (X / A / 2 + 1) := by
    nlinarith
  have hright : (2 * ell + 1) * (X / A / 2 + 1) ≤ X / (A / r) := by
    have hmid : (2 * ell + 1) * (X / A / 2 + 1) ≤ (ell + 1) * (X / A) := by
      nlinarith
    exact hmid.trans ((Nat.mul_le_mul_right _ (by omega : ell + 1 ≤ r)).trans hlower)
  exact (PrimeStar.allowedPrimeCount_mono (S := S) hleft).trans_lt
    (hgap.trans_le (PrimeStar.allowedPrimeCount_mono (S := S) hright))

/-- For a fixed least allowed prime, its down-target has strictly smaller
degree than every other down-target of a moving power-range source. -/
theorem eventually_powerRange_leastPrime_downDegree_separated
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2)
    {ell : ℕ} (hell : ell.Prime)
    (hmin : ∀ p : ℕ, p.Prime → p ∉ S → ell ≤ p) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ q : PrimeStar.CanonicalDownIndex a, (q : ℕ) = ell →
          ∀ r : PrimeStar.CanonicalDownIndex a, r ≠ q →
            PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
                (PrimeStar.canonicalDownTarget a q) <
              PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
                (PrimeStar.canonicalDownTarget a r) := by
  classical
  obtain ⟨N0, hgap⟩ := eventually_atTop.mp
    (eventually_allowedPrimeCount_mul_lt_succ_mul S hS (k := 2 * ell)
      (Nat.mul_pos (by norm_num) hell.pos))
  filter_upwards [eventually_powerRange_arithmeticStarDegree_bounds S hS htheta,
    eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
    PrimeStar.tendsto_natSqrt_atTop.eventually_ge_atTop (max N0 (4 * ell + 4))]
    with X hdegree hcenter hlarge
  intro a ha q hq r hr
  have haY : (a : ℕ) ≤ squareRootCutoff X := by
    have h := hcenter (a : ℕ) ha
    change (a : ℕ) ≤ Nat.sqrt X
    omega
  have hYN : Nat.sqrt X ≤ X / (a : ℕ) / 2 := (hdegree a ha).1
  have hrprime : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.property
  have hrdvd : (r : ℕ) ∣ (a : ℕ) := Nat.dvd_of_mem_primeFactors r.property
  have hrS : (r : ℕ) ∉ S := fun h ↦ PrimeStar.Vertex.not_dvd_of_mem a h hrdvd
  have hqrdiff : (r : ℕ) ≠ ell := by
    intro h
    apply hr
    exact Subtype.ext (h.trans hq.symm)
  have hellr : ell < (r : ℕ) := lt_of_le_of_ne (hmin r hrprime hrS) hqrdiff.symm
  have hqdvd : ell ∣ (a : ℕ) := hq ▸ Nat.dvd_of_mem_primeFactors q.property
  have hNlarge : 4 * ell + 4 ≤ X / (a : ℕ) :=
    ((le_max_right N0 _).trans hlarge).trans (hYN.trans (Nat.div_le_self _ 2))
  have hm : N0 ≤ X / (a : ℕ) / 2 + 1 := by
    exact ((le_max_left N0 _).trans hlarge).trans (hYN.trans (Nat.le_succ _))
  have hcounts := allowedPrimeCount_divisorTarget_lt (S := S)
    (PrimeStar.Vertex.coe_pos a) hell.pos hqdvd hrdvd hellr hNlarge
    (hgap _ hm)
  let b := PrimeStar.canonicalDownTarget a q
  let c := PrimeStar.canonicalDownTarget a r
  have hbY : (b : ℕ) ≤ squareRootCutoff X := (Nat.div_le_self _ _).trans haY
  have hcY : (c : ℕ) ≤ squareRootCutoff X := (Nat.div_le_self _ _).trans haY
  have hYb : squareRootCutoff X ≤ X / (b : ℕ) := by
    apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos b)).2
    exact (Nat.mul_le_mul_left _ hbY).trans (Nat.sqrt_le X)
  have hYc : squareRootCutoff X ≤ X / (c : ℕ) := by
    apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos c)).2
    exact (Nat.mul_le_mul_left _ hcY).trans (Nat.sqrt_le X)
  have hcounts' : PrimeStar.allowedPrimeCount S (X / (b : ℕ)) <
      PrimeStar.allowedPrimeCount S (X / (c : ℕ)) := by
    simpa only [b, c, PrimeStar.canonicalDownTarget, PrimeStar.vertexDivisorOfDvd,
      hq] using hcounts
  change PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) b <
    PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c
  rw [PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS b hbY hYb,
    PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS c hcY hYc]
  have hbase := PrimeStar.allowedPrimeCount_mono (S := S) hYb
  omega

/-- All local degree premises for the least-prime down-mode capture hold
eventually on a fixed sub-square-root power range. -/
theorem eventually_powerRange_oneExitProjection_fixes_leastPrimeDownMode
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2)
    {ell : ℕ} (hell : ell.Prime)
    (hmin : ∀ p : ℕ, p.Prime → p ∉ S → ell ≤ p) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ q : PrimeStar.CanonicalDownIndex a, (q : ℕ) = ell →
          Matrix.toEuclideanLin (oneExitProjection S X)
            (PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q) (-1))) =
            PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
              (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q) (-1)) := by
  classical
  filter_upwards [eventually_powerRange_leastPrime_downDegree_separated S hS htheta hell hmin,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_actualUpStarRatio_bounds S hS htheta,
    eventually_powerRange_downStarRatio_ge S hS htheta] with X hsep hwindow hup hdown
  intro a ha q hq
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  let d : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a
  let dq : ℝ := PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
    (PrimeStar.canonicalDownTarget a q)
  have hdpos : 0 < d := by
    dsimp only [d]
    exact_mod_cast hd
  have hratio := hdown a ha (q : ℕ) q.property
  change 17 / 16 ≤ PrimeStar.fixedCenterArithmeticDegree S ((a : ℕ) / (q : ℕ)) X /
    PrimeStar.fixedCenterArithmeticDegree S (a : ℕ) X at hratio
  rw [← PrimeStar.canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio hS a haY q] at hratio
  have hdlower : (17 / 16 : ℝ) * d ≤ dq :=
    (le_div_iff₀ hdpos).mp hratio
  have hddq : d < dq := by nlinarith
  apply oneExitProjection_fixes_negativeDownMode_of_sourceLocalDegrees hS haY hd q
  · dsimp only [d, dq] at hddq
    exact_mod_cast hddq.ne
  · intro r
    have hrdata := Finset.mem_filter.mp r.property
    have hrmem : (r : ℕ) ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun p ↦ p ∉ S) :=
      Finset.mem_filter.mpr ⟨hrdata.1, hrdata.2.1⟩
    have hu := (hup a ha (r : ℕ) hrmem).2.1
    change PrimeStar.fixedCenterActualUpRatio S (a : ℕ) X (r : ℕ) ≤ 15 / 16 at hu
    rw [← PrimeStar.canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a haY r] at hu
    have hdu : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a r) : ℝ) ≤ (15 / 16 : ℝ) * d :=
      (div_le_iff₀ hdpos).mp hu
    have hlt : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a r) : ℝ) < dq := by nlinarith
    dsimp only [dq] at hlt
    exact_mod_cast hlt.ne'
  · intro r hr
    exact (hsep a ha q hq r hr).ne

/-- Every negative boundary star mode in a fixed sub-square-root power
range belongs to the actual one-exit space. The least allowed prime and
all source-local degree separations are constructed, not hypotheses. -/
theorem eventually_powerRange_oneExitProjection_fixes_negativeStarMode
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        Matrix.toEuclideanLin (oneExitProjection S X)
          (PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a (-1))) =
          PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a (-1)) := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ p ∉ S := by
    obtain ⟨p, hp, hpprime⟩ := Nat.exists_infinite_primes (S.sup id + 1)
    refine ⟨p, hpprime, ?_⟩
    intro hpS
    have hle : p ≤ S.sup id := Finset.le_sup (f := id) hpS
    omega
  let ell := Nat.find hex
  have hell : ell.Prime := (Nat.find_spec hex).1
  have hellS : ell ∉ S := (Nat.find_spec hex).2
  have hmin : ∀ p : ℕ, p.Prime → p ∉ S → ell ≤ p :=
    fun p hp hpS ↦ Nat.find_min' hex ⟨hp, hpS⟩
  let theta' : ℝ := (theta + 1 / 2) / 2
  have ht' : theta' < 1 / 2 := by dsimp [theta']; linarith
  have hgap : 0 < theta' - theta := by dsimp [theta']; linarith
  have hgapTop : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (theta' - theta)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_powerRange_oneExitProjection_fixes_leastPrimeDownMode
      S hS ht' hell hmin,
    eventually_two_mul_center_le_natSqrt_on_powerRange ht',
    hgapTop.eventually_ge_atTop (ell : ℝ), eventually_gt_atTop 0]
    with X hcapture hcenter hgapX hX
  intro a ha
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hbpower : InPowerRange theta' X ((a : ℕ) * ell) := by
    refine ⟨Nat.mul_pos (PrimeStar.Vertex.coe_pos a) hell.pos, ?_⟩
    calc
      (((a : ℕ) * ell : ℕ) : ℝ) = (a : ℕ) * (ell : ℝ) := by norm_num
      _ ≤ powerScale theta X * (X : ℝ) ^ (theta' - theta) :=
        mul_le_mul ha.2 hgapX (by positivity) (Real.rpow_nonneg hx.le theta)
      _ = powerScale theta' X := by
        rw [powerScale, ← Real.rpow_add hx]
        congr 1
        ring
  have hbX : (a : ℕ) * ell ≤ X := by
    have h := hcenter ((a : ℕ) * ell) hbpower
    have hroot := Nat.sqrt_le_self X
    omega
  let b := PrimeStar.vertexMulAllowedPrimeOfBound hS a ell hell hellS hbX
  have hbcoe : (b : ℕ) = (a : ℕ) * ell := rfl
  let q : PrimeStar.CanonicalDownIndex b := ⟨ell,
    Nat.mem_primeFactors.mpr ⟨hell, by rw [hbcoe]; exact dvd_mul_left _ _,
      (PrimeStar.Vertex.coe_pos b).ne'⟩⟩
  have htarget : PrimeStar.canonicalDownTarget b q = a := by
    apply Subtype.ext
    apply Fin.ext
    change (a : ℕ) * ell / ell = (a : ℕ)
    exact Nat.mul_div_cancel _ hell.pos
  have h := hcapture b hbpower q rfl
  simpa only [htarget] using h

end SourceLocalPrimeSeparation

noncomputable section EqualDegreeTargetResponses

open Filter

/-- Equal-degree lower stars use the same initial segment of allowed large
prime labels. This is a finite order fact, not strict degree monotonicity. -/
theorem largePrimeLabels_eq_of_degree_eq
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {c d : PrimeStar.Vertex S X} (hc : (c : ℕ) ≤ Y) (hd : (d : ℕ) ≤ Y)
    (hdegree : PrimeStar.largePrimeStarDegree S X Y c =
      PrimeStar.largePrimeStarDegree S X Y d) :
    PrimeStar.largePrimeLabels S X Y c = PrimeStar.largePrimeLabels S X Y d := by
  classical
  have hcard : (PrimeStar.largePrimeLabels S X Y c).card =
      (PrimeStar.largePrimeLabels S X Y d).card := by
    simpa only [PrimeStar.largePrimeStarDegree_eq_card_largePrimeLabels hS c hc,
      PrimeStar.largePrimeStarDegree_eq_card_largePrimeLabels hS d hd] using hdegree
  have hmono {b e : PrimeStar.Vertex S X} (hbe : (b : ℕ) ≤ (e : ℕ)) :
      PrimeStar.largePrimeLabels S X Y e ⊆ PrimeStar.largePrimeLabels S X Y b := by
    intro p hp
    simp only [PrimeStar.largePrimeLabels, PrimeStar.allowedPrimeInterval,
      Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
    exact ⟨⟨hp.1.1.trans (Nat.div_le_div_left hbe (PrimeStar.Vertex.coe_pos b)), hp.1.2⟩,
      hp.2⟩
  rcases le_total (c : ℕ) (d : ℕ) with h | h
  · exact (Finset.eq_of_subset_of_card_le (hmono h) hcard.le).symm
  · exact Finset.eq_of_subset_of_card_le (hmono h) hcard.ge

/-- Two active equal-degree up-targets see the identical boundary-leaf
initial segment. Arbitrary boundary-kernel partial sums therefore agree. -/
theorem canonicalUp_boundaryLeafSegments_eq_of_degree_eq
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (q r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (hq : (PrimeStar.canonicalUpTarget hS a q : ℕ) ≤ squareRootCutoff X)
    (hr : (PrimeStar.canonicalUpTarget hS a r : ℕ) ≤ squareRootCutoff X)
    (hdegree : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) =
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a r)) :
    (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a).filter
        (fun v : PrimeStar.Vertex S X ↦ (v : ℕ) * q ≤ X) =
      (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a).filter
        (fun v : PrimeStar.Vertex S X ↦ (v : ℕ) * r ≤ X) := by
  classical
  have hlabels := largePrimeLabels_eq_of_degree_eq hS hq hr hdegree
  ext v
  by_cases hv : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a
  · obtain ⟨p, hp, hpS, hYp, hapv⟩ :=
      (PrimeStar.mem_largePrimeLeaves_iff_child ha).mp hv
    have hmem (s : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a) :
        p ∈ PrimeStar.largePrimeLabels S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a s) ↔ (v : ℕ) * s ≤ X := by
      have hval : p * (PrimeStar.canonicalUpTarget hS a s : ℕ) = (v : ℕ) * s := by
        rw [PrimeStar.canonicalUpTarget_coe, ← hapv]
        ring
      simp only [PrimeStar.largePrimeLabels, PrimeStar.allowedPrimeInterval,
        Finset.mem_filter, Nat.mem_primesLE,
        Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos _), hval,
        hp, hpS, hYp, not_false_eq_true, and_true]
    simp only [Finset.mem_filter, hv, true_and]
    rw [← hmem q, hlabels, hmem r]
  · simp [hv]

/-- On an up-star eigenspace, changing the source sign multiplies the
spectral component by a factor depending only on the target eigenvalue. -/
theorem largePrime_eigenprojection_upSource_neg
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X) (t : ℝ)
    {mu lambda : ℝ} (hmu : mu ≠ 0) (hl : lambda ≠ 0) (hsum : mu + lambda ≠ 0)
    (hd : lambda ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ)) :
    let E := (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
    E (PrimeStar.complexifyEuclidean
      (PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X) c (-mu) t)) =
      (((mu - lambda) / (mu + lambda) : ℝ) : ℂ) •
        E (PrimeStar.complexifyEuclidean
          (PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X) c mu t)) := by
  classical
  dsimp only
  simp only [PrimeStar.actualUpStarFirstExit]
  rw [largePrime_eigenprojection_starData_eq_smul_signedData hc t (fun _ ↦ t / (-mu)) hl hd,
    largePrime_eigenprojection_starData_eq_smul_signedData hc t (fun _ ↦ t / mu) hl hd,
    smul_smul]
  congr 1
  have hcard : ((PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c).card : ℝ) =
      lambda ^ 2 := hd.symm
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp [hmu, hl, hsum]
  ring

/-- A partial-leaf down-source has a different sign factor. Its leaf count
is the boundary degree, rather than the target degree. -/
theorem largePrime_eigenprojection_downSource_neg
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X) (t : ℝ)
    (P : Finset (PrimeStar.Vertex S X))
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c)
    {mu lambda : ℝ} (hl : lambda ≠ 0) (hsum : mu + lambda ≠ 0)
    (hcard : (P.card : ℝ) = mu ^ 2)
    (hd : lambda ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ)) :
    let E := (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
    E (PrimeStar.complexifyEuclidean
      (PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X) c P (-mu) t)) =
      (((lambda - mu) / (mu + lambda) : ℝ) : ℂ) •
        E (PrimeStar.complexifyEuclidean
          (PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X) c P mu t)) := by
  classical
  dsimp only
  simp only [PrimeStar.actualDownStarFirstExit]
  rw [largePrime_eigenprojection_starData_eq_smul_signedData hc t _ hl hd,
    largePrime_eigenprojection_starData_eq_smul_signedData hc t _ hl hd, smul_smul]
  have hsumP (z : ℝ) : (∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c,
      if v ∈ P then z else 0) = (P.card : ℝ) * z := by
    calc
      _ = ∑ v ∈ P, (if v ∈ P then z else 0) := by
        symm
        exact Finset.sum_subset hP (by intro v _ hv; simp [hv])
      _ = _ := by simp
  congr 1
  rw [hsumP, hsumP, hcard, ← Complex.ofReal_mul]
  congr 1
  field_simp [hl, hsum]
  ring

set_option maxHeartbeats 600000 in
/-- Every nonzero spectral component of the negative signed source is
captured when up- and down-degrees lie on opposite sides of the boundary
degree. Repeated degrees within either family are allowed. -/
theorem oneExitProjection_fixes_negativeSource_spectralComponent
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hup : ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) <
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdown : ∀ q : PrimeStar.CanonicalDownIndex a,
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a <
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q))
    {lambda : ℝ} (hl : lambda ≠ 0) :
    let E := (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
    Matrix.toEuclideanLin (oneExitProjection S X)
      (E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a (-1)))) =
      E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a (-1))) := by
  classical
  let E := (Module.End.eigenspace
    (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
  let mu := moleculeStarEnergy S X a
  let t := moleculePositiveStarMode S X a a
  let factor : ℝ := if lambda ^ 2 < mu ^ 2 then
    (mu - lambda) / (mu + lambda) else (lambda - mu) / (mu + lambda)
  let up := fun eps (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a) ↦
    E (PrimeStar.complexifyEuclidean (PrimeStar.actualUpStarFirstExit S X
      (squareRootCutoff X) (PrimeStar.canonicalUpTarget hS a q) (eps * mu) t))
  let down := fun eps (q : PrimeStar.CanonicalDownIndex a) ↦
    E (PrimeStar.complexifyEuclidean (PrimeStar.actualDownStarFirstExit S X
      (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q)
      (PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) q) (eps * mu) t))
  have hmu : mu ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hmusq : mu ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) :=
    moleculeStarEnergy_sq S X a
  have hlC : (lambda : ℂ) ≠ 0 := by exact_mod_cast hl
  have hu (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a) :
      up (-1) q = (factor : ℂ) • up 1 q := by
    simp only [up, neg_one_mul, one_mul]
    by_cases hm : lambda ^ 2 =
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) : ℝ)
    · have hlt : lambda ^ 2 < mu ^ 2 := by
        rw [hm, hmusq]
        exact_mod_cast hup q
      have hs : mu + lambda ≠ 0 := by
        intro h
        have heq : lambda = -mu := by linarith only [h]
        rw [heq, neg_sq] at hlt
        exact (lt_irrefl _ hlt)
      have hc : (PrimeStar.canonicalUpTarget hS a q : ℕ) ≤ squareRootCutoff X := by
        rcases PrimeStar.canonicalExitTarget_le_or_isolated hS
          (PrimeStar.sqrtCutoff_condition X) ha (Sum.inl q) with hc | hi
        · exact hc
        · have hz := PrimeStar.largePrimeStarDegree_eq_zero_iff.mpr hi
          change PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) = 0 at hz
          rw [hz, Nat.cast_zero] at hm
          exact False.elim (hl (sq_eq_zero_iff.mp hm))
      simp only [factor, if_pos hlt]
      exact largePrime_eigenprojection_upSource_neg
        (c := PrimeStar.canonicalUpTarget hS a q) (mu := mu) (lambda := lambda)
        hc t hmu hl hs hm
    · have hmC : (lambda : ℂ) ^ 2 ≠
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) : ℂ) := by exact_mod_cast hm
      rw [canonicalUp_eigenprojection_eq_zero hS ha q (-mu) t hlC hmC,
        canonicalUp_eigenprojection_eq_zero hS ha q mu t hlC hmC, smul_zero]
  have hd' (q : PrimeStar.CanonicalDownIndex a) :
      down (-1) q = (factor : ℂ) • down 1 q := by
    have hc : (PrimeStar.canonicalDownTarget a q : ℕ) ≤ squareRootCutoff X :=
      (Nat.div_le_self _ _).trans ha
    simp only [down, neg_one_mul, one_mul]
    by_cases hm : lambda ^ 2 =
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) : ℝ)
    · have hlt : mu ^ 2 < lambda ^ 2 := by
        rw [hm, hmusq]
        exact_mod_cast hdown q
      have hs : mu + lambda ≠ 0 := by
        intro h
        have heq : lambda = -mu := by linarith only [h]
        rw [heq, neg_sq] at hlt
        exact (lt_irrefl _ hlt)
      have hcard : ((PrimeStar.canonicalDownLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) q).card : ℝ) = mu ^ 2 := by
        rw [PrimeStar.card_canonicalDownLeaves_eq_boundaryDegree hS ha q, hmusq]
      simp only [factor, if_neg (not_lt_of_gt hlt)]
      exact largePrime_eigenprojection_downSource_neg
        (c := PrimeStar.canonicalDownTarget a q) (mu := mu) (lambda := lambda) hc t _
        (PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves _) hl hs hcard hm
    · have hmC : (lambda : ℂ) ^ 2 ≠
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
            (PrimeStar.canonicalDownTarget a q) : ℂ) := by exact_mod_cast hm
      simp only [PrimeStar.actualDownStarFirstExit]
      rw [largePrime_eigenprojection_starData_eq_zero hc t _ hlC hmC,
        largePrime_eigenprojection_starData_eq_zero hc t _ hlC hmC, smul_zero]
  have hsource (eps : ℝ) (heps : eps ^ 2 = 1) :
      E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a eps)) =
        (∑ q, up eps q) + ∑ q, down eps q := by
    have hcenter : PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a eps a = t := by
      dsimp [t, moleculePositiveStarMode]
      rw [largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd,
        largePrimeNormalizedStarMode_center_eq_inv_sqrt_two (by norm_num) hd]
    rw [exactBoundaryModeInteriorSource_eq_sum_canonicalBlocks hS ha hd heps]
    simp only [complexify_add, complexifyEuclidean_sum, map_add, map_sum, hcenter]
    rfl
  have hsame : E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a (-1))) =
      (factor : ℂ) • E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a 1)) := by
    rw [hsource (-1) (by norm_num), hsource 1 (by norm_num), smul_add,
      Finset.smul_sum, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun q _ ↦ hu q)
    · exact Finset.sum_congr rfl (fun q _ ↦ hd' q)
  have hpos : Matrix.toEuclideanLin (oneExitProjection S X)
      (E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a 1))) =
      E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a 1)) := by
    have h := oneExitProjection_fixes_spectralComponent S X (lambda : ℂ) _
      (oneExitProjection_fixes_positiveStarSource ha hd)
    simpa only [E, exactBoundaryModeInteriorSource_eq_smallPrime, smallPrime_complexify,
      moleculePositiveStarMode] using h
  change Matrix.toEuclideanLin (oneExitProjection S X) (_ : EuclideanSpace ℂ _) = _
  rw [hsame, map_smul, hpos]

/-- The actual up/down target degrees straddle the positive boundary degree,
uniformly on every fixed sub-square-root power range. -/
theorem eventually_powerRange_canonicalTargetDegrees_straddle
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        (a : ℕ) ≤ squareRootCutoff X ∧
        0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a ∧
        (∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
          PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) (PrimeStar.canonicalUpTarget hS a q) <
            PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) ∧
        (∀ q : PrimeStar.CanonicalDownIndex a,
          PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a <
            PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q)) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_actualUpStarRatio_bounds S hS htheta,
    eventually_powerRange_downStarRatio_ge S hS htheta] with X hwindow hup hdown
  intro a ha
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  have hdpos : (0 : ℝ) < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a :=
    by exact_mod_cast hd
  refine ⟨haY, hd, ?_, ?_⟩
  · intro q
    have hq := Finset.mem_filter.mp q.property
    have hqmem : (q : ℕ) ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun p ↦ p ∉ S) :=
      Finset.mem_filter.mpr ⟨hq.1, hq.2.1⟩
    have hu := (hup a ha (q : ℕ) hqmem).2.1
    change PrimeStar.fixedCenterActualUpRatio S (a : ℕ) X (q : ℕ) ≤ 15 / 16 at hu
    rw [← PrimeStar.canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a haY q] at hu
    have hb := (div_le_iff₀ hdpos).mp hu
    have hlt : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) : ℝ) <
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a := by nlinarith
    exact_mod_cast hlt
  · intro q
    have hdq := hdown a ha (q : ℕ) q.property
    change 17 / 16 ≤ PrimeStar.fixedCenterArithmeticDegree S ((a : ℕ) / (q : ℕ)) X /
      PrimeStar.fixedCenterArithmeticDegree S (a : ℕ) X at hdq
    rw [← PrimeStar.canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio hS a haY q] at hdq
    have hb := (le_div_iff₀ hdpos).mp hdq
    have hlt : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) <
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalDownTarget a q) := by nlinarith
    exact_mod_cast hlt

/-- The actual power-range ratios discharge signed-source capture hypotheses,
uniformly in every nonzero forest spectral parameter. -/
theorem eventually_powerRange_oneExitProjection_fixes_negativeSource_spectralComponent
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ lambda : ℝ, lambda ≠ 0 →
        let E := (Module.End.eigenspace
          (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
        Matrix.toEuclideanLin (oneExitProjection S X)
          (E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a (-1)))) =
          E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a (-1))) := by
  filter_upwards [eventually_powerRange_canonicalTargetDegrees_straddle S hS htheta] with X h
  intro a ha lambda hl
  obtain ⟨haY, hd, hup, hdown⟩ := h a ha
  exact oneExitProjection_fixes_negativeSource_spectralComponent hS haY hd hup hdown hl

/-- Capture passes from a source to its shifted forest response at every
nonresonant spectral parameter. No new resolvent is constructed. -/
theorem oneExitProjection_fixes_response_spectralComponent
    (S : Finset ℕ) (X : ℕ) (nu lambda : ℂ)
    (x b : EuclideanSpace ℂ (PrimeStar.Vertex S X))
    (hsolve : nu • x - Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x = b)
    (hgap : nu - lambda ≠ 0)
    (hcapture :
      let E := (Module.End.eigenspace
        (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
      Matrix.toEuclideanLin (oneExitProjection S X) (E b) = E b) :
    let E := (Module.End.eigenspace
      (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
    Matrix.toEuclideanLin (oneExitProjection S X) (E x) = E x := by
  let E := (Module.End.eigenspace
    (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) lambda).starProjection
  have heq : (nu - lambda) • E x = E b := by
    have h := congrArg E hsolve
    simpa only [map_sub, map_smul, forest_eigenprojection_apply, sub_smul, E] using h
  have h := congrArg (Matrix.toEuclideanLin (oneExitProjection S X)) heq
  rw [map_smul, hcapture, ← heq] at h
  exact (smul_right_injective _ hgap) h

/-- The negative spectral components of the actual negative signed
first-exit response lie in the one-exit space throughout the power range. -/
theorem eventually_powerRange_oneExitProjection_fixes_negativeResponse_spectralComponent
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ lambda : ℝ, lambda < 0 →
        let E := (Module.End.eigenspace
          (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)) (lambda : ℂ)).starProjection
        Matrix.toEuclideanLin (oneExitProjection S X)
          (E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a (-1)))) =
          E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a (-1))) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    eventually_powerRange_oneExitProjection_fixes_negativeSource_spectralComponent
      S hS htheta] with X hwindow hden hsource
  intro a ha lambda hl
  obtain ⟨_, hd, hshift⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hroot : 0 < exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    linarith
  have hsolve := PrimeStar.firstExitStar_shift_resolventVector
    (exactBoundaryModeInteriorSource S X a (-1)) (PrimeStar.sqrtCutoff_condition X)
    hroot.ne' (hden a ha)
    (fun v hv ↦ exactBoundaryModeInteriorSource_eq_zero_of_not_mem hv)
  apply oneExitProjection_fixes_response_spectralComponent S X
    (exactPrincipalMoleculeRoot S X a : ℂ) (lambda : ℂ) _
    (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a (-1)))
  · simpa only [PrimeStar.complexifyEuclidean_sub, PrimeStar.complexifyEuclidean_smul,
      ← oneExitLargePrimeMatrix_complexify, exactBoundaryModeInteriorVector] using
      congrArg PrimeStar.complexifyEuclidean hsolve
  · exact_mod_cast (sub_pos.mpr (hl.trans hroot)).ne'
  · exact hsource a ha lambda hl.ne

end EqualDegreeTargetResponses

noncomputable section KernelTargetCoefficients

/-- Local decidability for the actual kernel-source adjacency. -/
local instance kernelTargetSmallPrimeDecidableAdj (S : Finset ℕ) (X : ℕ) :
    DecidableRel (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj :=
  Classical.decRel _

private theorem boundaryKernel_supported
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X)
    (v : PrimeStar.Vertex S X)
    (hv : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeBoundaryKernel S X a v = 0 := by
  have hvc : v ≠ a := by
    intro h
    subst v
    exact hv (by simp [PrimeStar.largePrimeStarSupport])
  have hvl : v ∉ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a :=
    fun h ↦ hv (by simp [PrimeStar.largePrimeStarSupport, h])
  exact PrimeStar.largePrimeStarDataVector_outside _ _ hvc hvl

/-- The kernel-generated source is already supported on the actual first-exit
compression; its defining projection does not change the small-prime image. -/
theorem exactPrincipalMoleculeKernelInteriorSource_eq_smallPrime
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) :
    exactPrincipalMoleculeKernelInteriorSource S X a =
      Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeBoundaryKernel S X a) := by
  classical
  ext v
  rw [exactPrincipalMoleculeKernelInteriorSource,
    PrimeStar.firstExitCompressionProjection_apply]
  by_cases hv : v ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
  · simp [hv]
  · have hvExit : v ∉ PrimeStar.smallPrimeFirstExitSupport S X (squareRootCutoff X) a :=
      fun h ↦ hv (PrimeStar.smallPrimeFirstExitSupport_subset_firstExitCompressionSupport
        (PrimeStar.sqrtCutoff_condition X) h)
    rw [if_neg hv, Matrix.toLpLin_toLp 2 2]
    exact (PrimeStar.smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
      (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
      (fun w ↦ exactPrincipalMoleculeBoundaryKernel S X a w)
      (boundaryKernel_supported a) hvExit).symm

private theorem kernelSource_eq_zero_of_not_mem
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) (v : PrimeStar.Vertex S X)
    (hv : v ∉ PrimeStar.smallPrimeFirstExitSupport S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeKernelInteriorSource S X a v = 0 := by
  rw [exactPrincipalMoleculeKernelInteriorSource_eq_smallPrime, Matrix.toLpLin_toLp 2 2]
  exact PrimeStar.smallPrime_mulVec_eq_zero_of_not_mem_firstExitSupport_of_supported
    (S := S) (X := X) (Y := squareRootCutoff X) (c := a)
    (fun w ↦ exactPrincipalMoleculeBoundaryKernel S X a w) (boundaryKernel_supported a) hv

/-- Symmetry identifies a kernel-source coefficient with the reverse signed
source restricted to the original boundary star. -/
theorem real_inner_starMode_kernelSource_eq_reverseRestriction
    {S : Finset ℕ} {X : ℕ} (a c : PrimeStar.Vertex S X) (eps : ℝ) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) c eps,
      exactPrincipalMoleculeKernelInteriorSource S X a⟫_ℝ =
      ⟪exactPrincipalMoleculeBoundaryKernel S X a,
        PrimeStar.restrictEuclideanToFinset
          (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
          (exactBoundaryModeInteriorSource S X c eps)⟫_ℝ := by
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  have hH : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix (R := ℝ))
  rw [PrimeStar.inner_restrictEuclideanToFinset_right_of_supported _ _ _
    (boundaryKernel_supported a), exactPrincipalMoleculeKernelInteriorSource_eq_smallPrime,
    exactBoundaryModeInteriorSource_eq_smallPrime]
  exact (hH _ _).symm.trans (real_inner_comm _ _)

private theorem real_inner_boundaryKernel_downSource
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) (mu t : ℝ)
    (P : Finset (PrimeStar.Vertex S X))
    (hP : P ⊆ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a) :
    ⟪exactPrincipalMoleculeBoundaryKernel S X a,
      PrimeStar.actualDownStarFirstExit S X (squareRootCutoff X) a P mu t⟫_ℝ =
      (t / mu) * ∑ v ∈ P, exactPrincipalMoleculeBoundaryKernel S X a v := by
  classical
  let f := fun v ↦ exactPrincipalMoleculeAmbientVector S X a v -
    finsetMean (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a)
      (exactPrincipalMoleculeAmbientVector S X a)
  change ⟪PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) a 0 f,
    PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) a t
      (fun v ↦ if v ∈ P then t / mu else 0)⟫_ℝ = _
  rw [PrimeStar.largePrimeStarDataVector_inner, zero_mul, zero_add]
  calc
    _ = ∑ v ∈ P, f v * (if v ∈ P then t / mu else 0) := by
      symm
      exact Finset.sum_subset hP (by intro v _ hv; simp [hv])
    _ = (t / mu) * ∑ v ∈ P, exactPrincipalMoleculeBoundaryKernel S X a v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [if_pos hv]
      have hk : exactPrincipalMoleculeBoundaryKernel S X a v = f v :=
        PrimeStar.largePrimeStarDataVector_leaf _ _ (hP hv)
      rw [hk, mul_comm]

private theorem real_inner_boundaryKernel_upSource_eq_zero
    {S : Finset ℕ} {X : ℕ} (a : PrimeStar.Vertex S X) (mu t : ℝ)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ⟪exactPrincipalMoleculeBoundaryKernel S X a,
      PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X) a mu t⟫_ℝ = 0 := by
  have hleaves : (PrimeStar.largePrimeLeaves S X (squareRootCutoff X) a).Nonempty :=
    Finset.card_pos.mp hd
  rw [exactPrincipalMoleculeBoundaryKernel, actualStarMeanZeroLeafVector,
    PrimeStar.actualUpStarFirstExit, PrimeStar.largePrimeStarDataVector_inner,
    zero_mul, zero_add, ← Finset.sum_mul, sum_sub_finsetMean_eq_zero hleaves, zero_mul]

/-- An active up-target sees precisely the kernel sum on its initial segment
of boundary leaves. This is an exact coefficient of the actual kernel source. -/
theorem real_inner_upTargetMode_kernelSource
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (hc : (PrimeStar.canonicalUpTarget hS a q : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalUpTarget hS a q))
    {eps : ℝ} (heps : eps ^ 2 = 1) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) eps,
      exactPrincipalMoleculeKernelInteriorSource S X a⟫_ℝ =
      (PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) eps (PrimeStar.canonicalUpTarget hS a q) /
        (eps * moleculeStarEnergy S X (PrimeStar.canonicalUpTarget hS a q))) *
        ∑ v ∈ PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) a q,
          exactPrincipalMoleculeBoundaryKernel S X a v := by
  have hq := Finset.mem_filter.mp q.property
  rw [real_inner_starMode_kernelSource_eq_reverseRestriction,
    restrict_exactBoundaryModeInteriorSource_eq_actualDownStar hS hc ha hd heps
      (Nat.mem_primesLE.mp hq.1).2 hq.2.1 (Nat.mem_primesLE.mp hq.1).1
      (PrimeStar.canonicalUpTarget_coe hS a q).symm,
    real_inner_boundaryKernel_downSource _ _ _ _
      (PrimeStar.canonicalDownLeaves_subset_largePrimeLeaves a)]

/-- Every active down-target has zero kernel-source coefficient: the reverse
up-source is constant on the entire boundary-leaf segment. -/
theorem real_inner_downTargetMode_kernelSource_eq_zero
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalDownIndex a)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q))
    {eps : ℝ} (heps : eps ^ 2 = 1) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) eps,
      exactPrincipalMoleculeKernelInteriorSource S X a⟫_ℝ = 0 := by
  have hp : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.property
  have hqdvd : (q : ℕ) ∣ (a : ℕ) := Nat.dvd_of_mem_primeFactors q.property
  have hqS : (q : ℕ) ∉ S := fun h ↦ PrimeStar.Vertex.not_dvd_of_mem a h hqdvd
  have hqY : (q : ℕ) ≤ squareRootCutoff X :=
    (Nat.le_of_dvd (PrimeStar.Vertex.coe_pos a) hqdvd).trans ha
  have hc : (PrimeStar.canonicalDownTarget a q : ℕ) ≤ squareRootCutoff X :=
    (Nat.div_le_self _ _).trans ha
  rw [real_inner_starMode_kernelSource_eq_reverseRestriction,
    restrict_exactBoundaryModeInteriorSource_eq_actualUpStar hS hc ha hd heps hp hqS hqY
      (PrimeStar.canonicalDownTarget_mul_coe a q),
    real_inner_boundaryKernel_upSource_eq_zero _ _ _ hda]

/-- Repeated active up-target degrees give exactly equal kernel-source
coefficients, not merely comparable magnitudes. -/
theorem real_inner_upTargetMode_kernelSource_eq_of_degree_eq
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (q r : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (hq : (PrimeStar.canonicalUpTarget hS a q : ℕ) ≤ squareRootCutoff X)
    (hr : (PrimeStar.canonicalUpTarget hS a r : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalUpTarget hS a q))
    (hdegree : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) =
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a r))
    {eps : ℝ} (heps : eps ^ 2 = 1) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) eps,
      exactPrincipalMoleculeKernelInteriorSource S X a⟫_ℝ =
    ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a r) eps,
      exactPrincipalMoleculeKernelInteriorSource S X a⟫_ℝ := by
  have hdr : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalUpTarget hS a r) := hdegree ▸ hd
  have hsets := canonicalUp_boundaryLeafSegments_eq_of_degree_eq hS ha q r hq hr hdegree
  change PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) a q =
    PrimeStar.canonicalDownLeaves S X (squareRootCutoff X) a r at hsets
  rw [real_inner_upTargetMode_kernelSource hS ha q hq hd heps,
    real_inner_upTargetMode_kernelSource hS ha r hr hdr heps,
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd,
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hdr, hsets]
  simp only [moleculeStarEnergy, hdegree]

end KernelTargetCoefficients

noncomputable section KernelSpectralCapture

open Filter

private theorem boundaryProjection_eq_restrict
    {S : Finset ℕ} {X Y : ℕ} (c : PrimeStar.Vertex S X) (x : MoleculeAmbient S X) :
    PrimeStar.primeStarBoundaryProjection S X Y c x =
      PrimeStar.restrictEuclideanToFinset (PrimeStar.largePrimeStarSupport S X Y c) x := by
  ext v
  rw [PrimeStar.primeStarBoundaryProjection_apply, PrimeStar.restrictEuclideanToFinset_apply]

/-- On one nonempty star, the negative forest spectral component of an
ambient vector restricted to that star is its scalar inner product with
the normalized negative mode. Other stars may have the same degree. -/
theorem largePrime_negativeEigenprojection_boundary_eq_inner_smul
    {S : Finset ℕ} {X : ℕ} {c : PrimeStar.Vertex S X}
    (hc : (c : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c)
    (x : MoleculeAmbient S X) :
    let u := PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) c (-1)
    let lambda := -moleculeStarEnergy S X c
    (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
      (lambda : ℂ)).starProjection
        (PrimeStar.complexifyEuclidean
          (PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) c x)) =
      ((⟪u, x⟫_ℝ : ℝ) : ℂ) • PrimeStar.complexifyEuclidean u := by
  classical
  let u := PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) c (-1)
  let lambda := -moleculeStarEnergy S X c
  let t := u c
  let v := PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c lambda (fun _ ↦ 1)
  have hl : lambda ≠ 0 := neg_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd))
  have hlsq : lambda ^ 2 =
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ) := by
    dsimp [lambda, moleculeStarEnergy]
    rw [neg_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  have ht : t ^ 2 = 1 / 2 := PrimeStar.sq_largePrimeNormalizedStarMode_center
    (by norm_num) hd
  have hu : u = PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t
      (fun _ ↦ t / lambda) := by
    ext w
    by_cases hw : w = c
    · subst w
      simp [t]
    · by_cases hwleaf : w ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c
      · rw [PrimeStar.largePrimeStarDataVector_leaf _ _ hwleaf]
        simpa only [u, t, lambda, moleculeStarEnergy, neg_one_mul] using
          largePrimeNormalizedStarMode_leaf_eq_center_div_signedEnergy
            (eps := (-1 : ℝ)) (by norm_num) hd hwleaf
      · rw [PrimeStar.largePrimeStarDataVector_outside _ _ hw hwleaf]
        exact PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem
          (by simp [PrimeStar.largePrimeStarSupport, hw, hwleaf])
  have huv : u = (t / lambda) • v := by
    rw [hu]
    ext w
    by_cases hw : w = c
    · subst w
      simp [v, PiLp.smul_apply, div_mul_cancel₀ _ hl]
    · by_cases hwleaf : w ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c
      · simp [v, PrimeStar.largePrimeStarDataVector_leaf _ _ hwleaf, PiLp.smul_apply]
      · simp [v, PrimeStar.largePrimeStarDataVector_outside _ _ hw hwleaf, PiLp.smul_apply]
  have hi : ⟪u, x⟫_ℝ = t *
      (x c + (∑ w ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c, x w) / lambda) := by
    rw [← real_inner_largePrimeNormalizedStarMode_boundaryProjection (-1) x,
      primeStarBoundaryProjection_eq_largePrimeStarDataVector]
    change ⟪u, PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c (x c) x⟫_ℝ = _
    rw [hu, PrimeStar.largePrimeStarDataVector_inner, ← Finset.mul_sum]
    ring
  change _ = ((⟪u, x⟫_ℝ : ℝ) : ℂ) • PrimeStar.complexifyEuclidean u
  rw [primeStarBoundaryProjection_eq_largePrimeStarDataVector,
    largePrime_eigenprojection_starData_eq_smul_signedData hc (x c) x hl hlsq,
    hi, huv, PrimeStar.complexifyEuclidean_smul, smul_smul, ← Complex.ofReal_mul]
  congr 1
  congr 1
  field_simp [hl]
  rw [ht]
  ring

private theorem real_inner_negativeStarMode_starData
    {S : Finset ℕ} {X : ℕ} (c : PrimeStar.Vertex S X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c)
    (t : ℝ) (f : PrimeStar.Vertex S X → ℝ) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) c (-1),
      PrimeStar.largePrimeStarDataVector S X (squareRootCutoff X) c t f⟫_ℝ =
      (Real.sqrt 2)⁻¹ * (t -
        (∑ w ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c, f w) /
          moleculeStarEnergy S X c) := by
  let v := PrimeStar.largePrimeEuclideanStarVector S X (squareRootCutoff X) c (-1)
  have hm : moleculeStarEnergy S X c ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have ht := largePrimeNormalizedStarMode_center_eq_inv_sqrt_two
    (eps := (-1 : ℝ)) (by norm_num) hd
  have ht' : ‖v‖⁻¹ * moleculeStarEnergy S X c = (Real.sqrt 2)⁻¹ := by
    simpa only [PrimeStar.largePrimeNormalizedStarMode, NormedSpace.normalize,
      PiLp.smul_apply, smul_eq_mul, PrimeStar.largePrimeEuclideanStarVector,
      PrimeStar.largePrimeSignedStarVector_center, moleculeStarEnergy, v] using ht
  rw [PrimeStar.largePrimeNormalizedStarMode, NormedSpace.normalize, real_inner_smul_left,
    PrimeStar.largePrimeEuclideanStarVector_eq_starDataVector,
    PrimeStar.largePrimeStarDataVector_inner]
  simp only [neg_one_mul, Finset.sum_neg_distrib]
  rw [← ht']
  change ‖v‖⁻¹ * (moleculeStarEnergy S X c * t + -(_ : ℝ)) = _
  field_simp [hm]
  ring

/-- The captured positive boundary source has a strictly positive coefficient
on each negative up-target mode below the boundary degree. Its value depends
only on the two degrees, so repeated target degrees cause no ambiguity. -/
theorem real_inner_negativeUpTargetMode_positiveSource
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hda : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalUpTarget hS a q)) :
    ⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) (-1),
      exactBoundaryModeInteriorSource S X a 1⟫_ℝ =
      (1 / 2 : ℝ) * (1 - moleculeStarEnergy S X (PrimeStar.canonicalUpTarget hS a q) /
        moleculeStarEnergy S X a) := by
  let c := PrimeStar.canonicalUpTarget hS a q
  have hr := restrict_exactBoundaryModeInteriorSource_eq_canonicalUpStar hS ha hda
    (eps := (1 : ℝ)) (by norm_num) q
  have hr' : PrimeStar.primeStarBoundaryProjection S X (squareRootCutoff X) c
      (exactBoundaryModeInteriorSource S X a 1) =
      PrimeStar.actualUpStarFirstExit S X (squareRootCutoff X) c
        (moleculeStarEnergy S X a)
        (PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a 1 a) := by
    rw [boundaryProjection_eq_restrict]
    simpa only [one_mul, c] using hr
  rw [← real_inner_largePrimeNormalizedStarMode_boundaryProjection (-1)
      (exactBoundaryModeInteriorSource S X a 1), hr', PrimeStar.actualUpStarFirstExit,
    real_inner_negativeStarMode_starData c hd,
    largePrimeNormalizedStarMode_center_eq_inv_sqrt_two (by norm_num) hda]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hma : moleculeStarEnergy S X a ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hda)
  have hmc : moleculeStarEnergy S X c ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hdC : ((PrimeStar.largePrimeLeaves S X (squareRootCutoff X) c).card : ℝ) =
      moleculeStarEnergy S X c ^ 2 := (moleculeStarEnergy_sq S X c).symm
  rw [hdC]
  have htwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hma, hmc]
  rw [htwo]
  change _ = 2 * (moleculeStarEnergy S X a - moleculeStarEnergy S X c)
  ring

private theorem canonicalExit_negative_projection_formula
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a)
    {lambda : ℝ} (hl : lambda < 0) (x : MoleculeAmbient S X) :
    let c := PrimeStar.canonicalExitTarget hS a i
    let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
      (lambda : ℂ)).starProjection
    E (PrimeStar.complexifyEuclidean (PrimeStar.restrictEuclideanToFinset
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) c) x)) =
      if lambda ^ 2 = (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ)
      then ((⟪PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) c (-1), x⟫_ℝ : ℝ) : ℂ) •
        PrimeStar.complexifyEuclidean
          (PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) c (-1))
      else 0 := by
  classical
  let c := PrimeStar.canonicalExitTarget hS a i
  dsimp only
  rw [← boundaryProjection_eq_restrict]
  split
  next hm =>
    have hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c := by
      have h : (0 : ℝ) < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c := by
        rw [← hm]
        exact sq_pos_of_ne_zero hl.ne
      exact_mod_cast h
    have hc : (c : ℕ) ≤ squareRootCutoff X := by
      rcases PrimeStar.canonicalExitTarget_le_or_isolated hS (PrimeStar.sqrtCutoff_condition X)
        ha i with hc | hi
      · exact hc
      · exact False.elim ((Nat.ne_of_gt hd) (PrimeStar.largePrimeStarDegree_eq_zero_iff.mpr hi))
    have henergy : -moleculeStarEnergy S X c = lambda := by
      dsimp only [moleculeStarEnergy]
      rw [← hm, Real.sqrt_sq_eq_abs, abs_of_neg hl, neg_neg]
    simpa only [henergy, c] using
      largePrime_negativeEigenprojection_boundary_eq_inner_smul hc hd x
  next hm =>
    rw [primeStarBoundaryProjection_eq_largePrimeStarDataVector]
    have hlC : (lambda : ℂ) ≠ 0 := by exact_mod_cast hl.ne
    have hmC : (lambda : ℂ) ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℂ) := by exact_mod_cast hm
    rcases PrimeStar.canonicalExitTarget_le_or_isolated hS (PrimeStar.sqrtCutoff_condition X)
      ha i with hc | hi
    · exact largePrime_eigenprojection_starData_eq_zero hc _ _ hlC hmC
    · exact largePrime_eigenprojection_isolatedStarData_eq_zero hi _ _ hlC

set_option maxHeartbeats 600000 in
/-- All negative spectral components of the actual kernel source are captured.
Repeated up-degrees are handled by their equal partial kernel sums; the down
coefficients vanish. No global eigenvalue simplicity is assumed. -/
theorem oneExitProjection_fixes_kernelSource_negativeSpectralComponent
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hup : ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) (PrimeStar.canonicalUpTarget hS a q) <
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hdown : ∀ q : PrimeStar.CanonicalDownIndex a,
      PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a <
        PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) (PrimeStar.canonicalDownTarget a q))
    {lambda : ℝ} (hl : lambda < 0) :
    let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
      (lambda : ℂ)).starProjection
    Matrix.toEuclideanLin (oneExitProjection S X)
      (E (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeKernelInteriorSource S X a))) =
      E (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeKernelInteriorSource S X a)) := by
  classical
  let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
    (lambda : ℂ)).starProjection
  let K := exactPrincipalMoleculeKernelInteriorSource S X a
  let p := exactBoundaryModeInteriorSource S X a 1
  let u := fun c : PrimeStar.Vertex S X ↦
    PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) c (-1)
  let block := fun (i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a)
      (x : MoleculeAmbient S X) ↦ E (PrimeStar.complexifyEuclidean
        (PrimeStar.restrictEuclideanToFinset
          (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
            (PrimeStar.canonicalExitTarget hS a i)) x))
  have hsupportK : ∀ v, v ∉ PrimeStar.smallPrimeFirstExitSupport S X
      (squareRootCutoff X) a → K v = 0 := by
    exact kernelSource_eq_zero_of_not_mem a
  have hsum (x : MoleculeAmbient S X)
      (hx : ∀ v, v ∉ PrimeStar.smallPrimeFirstExitSupport S X (squareRootCutoff X) a → x v = 0) :
      E (PrimeStar.complexifyEuclidean x) = ∑ i, block i x := by
    have h := congrArg (fun y ↦ E (PrimeStar.complexifyEuclidean y))
      (PrimeStar.euclidean_eq_sum_canonicalExitStarBlocks hS (PrimeStar.sqrtCutoff_condition X)
        ha hd x hx)
    simpa only [complexifyEuclidean_sum, map_sum, block] using h
  have hformula i x := canonicalExit_negative_projection_formula hS ha i hl x
  change ∀ i x, block i x = _ at hformula
  have hmatched (i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a)
      (hm : lambda ^ 2 = (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalExitTarget hS a i) : ℝ)) :
      (PrimeStar.canonicalExitTarget hS a i : ℕ) ≤ squareRootCutoff X ∧
      0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalExitTarget hS a i) := by
    have hd' : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalExitTarget hS a i) := by
      have h : (0 : ℝ) < _ := hm ▸ sq_pos_of_ne_zero hl.ne
      exact_mod_cast h
    refine ⟨?_, hd'⟩
    rcases PrimeStar.canonicalExitTarget_le_or_isolated hS (PrimeStar.sqrtCutoff_condition X)
      ha i with hc | hi
    · exact hc
    · exact False.elim ((Nat.ne_of_gt hd') (PrimeStar.largePrimeStarDegree_eq_zero_iff.mpr hi))
  by_cases hex : ∃ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
      lambda ^ 2 = (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) : ℝ)
  · obtain ⟨q0, hq0⟩ := hex
    obtain ⟨hc0, hd0⟩ := hmatched (Sum.inl q0) hq0
    let c0 := PrimeStar.canonicalUpTarget hS a q0
    let beta : ℝ := ⟪u c0, K⟫_ℝ / ⟪u c0, p⟫_ℝ
    have hp0 : ⟪u c0, p⟫_ℝ ≠ 0 := by
      have henergy : moleculeStarEnergy S X c0 < moleculeStarEnergy S X a :=
        Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (by exact_mod_cast hup q0)
      have hma : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
      rw [real_inner_negativeUpTargetMode_positiveSource hS ha hd q0 hd0]
      exact (mul_pos (by norm_num) (sub_pos.mpr ((div_lt_one hma).mpr henergy))).ne'
    have hblock (i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a) :
        block i K = (beta : ℂ) • block i p := by
      rw [hformula, hformula]
      split
      next hm =>
        rcases i with q | q
        · obtain ⟨hcq, hdq⟩ := hmatched (Sum.inl q) hm
          have hdegrees : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
              (PrimeStar.canonicalUpTarget hS a q) =
              PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c0 := by
            exact_mod_cast hm.symm.trans hq0
          have hk := real_inner_upTargetMode_kernelSource_eq_of_degree_eq hS ha q q0
            hcq hc0 hdq hdegrees (eps := (-1 : ℝ)) (by norm_num)
          have hp : ⟪u (PrimeStar.canonicalUpTarget hS a q), p⟫_ℝ = ⟪u c0, p⟫_ℝ := by
            rw [real_inner_negativeUpTargetMode_positiveSource hS ha hd q hdq,
              real_inner_negativeUpTargetMode_positiveSource hS ha hd q0 hd0]
            simp only [moleculeStarEnergy, hdegrees, c0]
          have hcoef : ⟪u (PrimeStar.canonicalUpTarget hS a q), K⟫_ℝ =
              beta * ⟪u (PrimeStar.canonicalUpTarget hS a q), p⟫_ℝ := by
            calc
              _ = ⟪u c0, K⟫_ℝ := hk
              _ = beta * ⟪u c0, p⟫_ℝ := (div_mul_cancel₀ _ hp0).symm
              _ = _ := congrArg (fun z : ℝ ↦ beta * z) hp.symm
          simp only [PrimeStar.canonicalExitTarget, smul_smul]
          congr 1
          simpa only [u, Complex.ofReal_mul] using congrArg Complex.ofReal hcoef
        · have hlt : lambda ^ 2 < (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
              (PrimeStar.canonicalDownTarget a q) : ℝ) := by
            rw [hq0]
            exact_mod_cast (hup q0).trans (hdown q)
          exact False.elim (hlt.ne hm)
      next hm => simp only [smul_zero]
    have hsame : E (PrimeStar.complexifyEuclidean K) =
        (beta : ℂ) • E (PrimeStar.complexifyEuclidean p) := by
      rw [hsum K hsupportK, hsum p (fun v hv ↦ exactBoundaryModeInteriorSource_eq_zero_of_not_mem hv),
        Finset.smul_sum]
      exact Finset.sum_congr rfl (fun i _ ↦ hblock i)
    have hpCapture := oneExitProjection_fixes_spectralComponent S X (lambda : ℂ) _
      (oneExitProjection_fixes_positiveStarSource ha hd)
    have hpCapture' : Matrix.toEuclideanLin (oneExitProjection S X)
        (E (PrimeStar.complexifyEuclidean p)) = E (PrimeStar.complexifyEuclidean p) := by
      simpa only [E, p, exactBoundaryModeInteriorSource_eq_smallPrime, smallPrime_complexify,
        moleculePositiveStarMode] using hpCapture
    change Matrix.toEuclideanLin (oneExitProjection S X) (E (PrimeStar.complexifyEuclidean K)) = _
    rw [hsame, map_smul, hpCapture']
  · have hz : E (PrimeStar.complexifyEuclidean K) = 0 := by
      rw [hsum K hsupportK]
      apply Finset.sum_eq_zero
      intro i _
      rw [hformula]
      split
      next hm =>
        rcases i with q | q
        · exact False.elim (hex ⟨q, hm⟩)
        · obtain ⟨_, hdq⟩ := hmatched (Sum.inr q) hm
          simp only [PrimeStar.canonicalExitTarget, K,
            real_inner_downTargetMode_kernelSource_eq_zero hS ha hd q hdq
              (eps := (-1 : ℝ)) (by norm_num), Complex.ofReal_zero, zero_smul]
      next hm => rfl
    change Matrix.toEuclideanLin (oneExitProjection S X) (E (PrimeStar.complexifyEuclidean K)) = _
    rw [hz, map_zero]

/-- The actual kernel source has captured negative spectral components on
every fixed power range below one half. No degree conditions remain as premises. -/
theorem eventually_powerRange_oneExitProjection_fixes_kernelSource_negativeSpectralComponent
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ lambda : ℝ, lambda < 0 →
        let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
          (lambda : ℂ)).starProjection
        Matrix.toEuclideanLin (oneExitProjection S X)
          (E (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeKernelInteriorSource S X a))) =
          E (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeKernelInteriorSource S X a)) := by
  filter_upwards [eventually_powerRange_canonicalTargetDegrees_straddle S hS htheta] with X h
  intro a ha lambda hl
  obtain ⟨haY, hd, hup, hdown⟩ := h a ha
  exact oneExitProjection_fixes_kernelSource_negativeSpectralComponent hS haY hd hup hdown hl

/-- Every negative spectral component of the actual kernel-driven response
is captured. The existing shifted forest equation supplies the transfer. -/
theorem eventually_powerRange_oneExitProjection_fixes_kernelResponse_negativeSpectralComponent
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ lambda : ℝ, lambda < 0 →
        let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
          (lambda : ℂ)).starProjection
        Matrix.toEuclideanLin (oneExitProjection S X)
          (E (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeKernelInteriorVector S X a))) =
          E (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeKernelInteriorVector S X a)) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    eventually_powerRange_oneExitProjection_fixes_kernelSource_negativeSpectralComponent
      S hS htheta] with X hwindow hden hsource
  intro a ha lambda hl
  obtain ⟨_, hd, hshift⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hroot : 0 < exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    linarith
  have hsolve := PrimeStar.firstExitStar_shift_resolventVector
    (exactPrincipalMoleculeKernelInteriorSource S X a) (PrimeStar.sqrtCutoff_condition X)
    hroot.ne' (hden a ha) (kernelSource_eq_zero_of_not_mem a)
  apply oneExitProjection_fixes_response_spectralComponent S X
    (exactPrincipalMoleculeRoot S X a : ℂ) (lambda : ℂ) _
    (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeKernelInteriorSource S X a))
  · simpa only [PrimeStar.complexifyEuclidean_sub, PrimeStar.complexifyEuclidean_smul,
      ← oneExitLargePrimeMatrix_complexify, exactPrincipalMoleculeKernelInteriorVector] using
      congrArg PrimeStar.complexifyEuclidean hsolve
  · exact_mod_cast (sub_pos.mpr (hl.trans hroot)).ne'
  · exact hsource a ha lambda hl

end KernelSpectralCapture

noncomputable section FullMoleculeTail

open Filter

/-- Once the negative spectral components of a vector are captured, its
discarded part is a forest zero mode. Positive components are already in
the positive-star space; repeated eigenvalues require no simplicity. -/
theorem largePrime_apply_oneExitComplement_eq_zero_of_negativeCapture
    (S : Finset ℕ) (X : ℕ) (x : EuclideanSpace ℂ (PrimeStar.Vertex S X))
    (hneg : ∀ lambda : ℝ, lambda < 0 →
      let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
        (lambda : ℂ)).starProjection
      Matrix.toEuclideanLin (oneExitProjection S X) (E x) = E x) :
    Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
      (Matrix.toEuclideanLin (oneExitComplementProjection S X) x) = 0 := by
  classical
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  let Q := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix ℂ)
  have hP : P.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hcomm : Commute P L := by
    change P * L = L * P
    have h := congrArg Matrix.toEuclideanLin (oneExitProjection_commutes_largePrime S X).eq
    simpa only [Matrix.toLpLin_mul_same, ← Module.End.mul_eq_comp] using h
  have hQ (v : EuclideanSpace ℂ (PrimeStar.Vertex S X)) : Q v = v - P v := by
    simp only [Q, P, oneExitComplementProjection, map_sub,
      LinearMap.sub_apply, Matrix.toLpLin_one, LinearMap.id_apply]
  have hcomp (lambda : ℝ) :
      (Module.End.eigenspace L (lambda : ℂ)).starProjection (L (Q x)) = 0 := by
    let E := (Module.End.eigenspace L (lambda : ℂ)).starProjection
    rw [forest_eigenprojection_apply]
    by_cases hl0 : lambda = 0
    · simp [hl0]
    have hfix : P (E x) = E x := by
      rcases lt_or_gt_of_ne hl0 with hl | hl
      · exact hneg lambda hl
      · have heig : L (E x) = (lambda : ℂ) • E x :=
          Module.End.mem_eigenspace_iff.mp (Submodule.starProjection_apply_mem _ _)
        have hp := positiveStarProjection_fixes_positive_forest_eigenvector hl heig
        have hmul : oneExitProjection S X * positiveStarProjection S X =
            positiveStarProjection S X := by
          rw [oneExitProjection, Matrix.add_mul,
            (positiveStarProjection_isStarProjection S X).isIdempotentElem,
            oneExitCyclicProjection_mul_positiveStarProjection, add_zero]
        have h := congrArg (fun M ↦ Matrix.toEuclideanLin M (E x)) hmul
        simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hp] using h
    have heq : E (Q x) = 0 := by
      have h := LinearMap.congr_fun
        (eigenprojection_commutes_of_commute L P hP hcomm (lambda : ℂ)).eq x
      change E (P x) = P (E x) at h
      rw [hQ, map_sub, h, hfix, sub_self]
    change (lambda : ℂ) • E (Q x) = 0
    rw [heq, smul_zero]
  let b := hL.eigenvectorBasis rfl
  change L (Q x) = 0
  rw [← b.sum_repr' (L (Q x))]
  apply Finset.sum_eq_zero
  intro i _
  have hi := (hL.hasEigenvector_eigenvectorBasis rfl i).1
  have hz := (Module.End.eigenspace L (hL.eigenvalues rfl i : ℂ)).starProjection_inner_eq_zero
    (L (Q x)) (b i) hi
  rw [hcomp, sub_zero] at hz
  rw [inner_eq_zero_symm.mp hz, zero_smul]

private theorem eventually_positiveResponse_negativeCapture
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ lambda : ℝ, lambda < 0 →
        let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
          (lambda : ℂ)).starProjection
        Matrix.toEuclideanLin (oneExitProjection S X)
          (E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a 1))) =
          E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a 1)) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta]
      with X hwindow hden
  intro a ha lambda hl
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hroot : 0 < exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    linarith
  have hsolve := PrimeStar.firstExitStar_shift_resolventVector
    (exactBoundaryModeInteriorSource S X a 1) (PrimeStar.sqrtCutoff_condition X)
    hroot.ne' (hden a ha)
    (fun v hv ↦ exactBoundaryModeInteriorSource_eq_zero_of_not_mem hv)
  apply oneExitProjection_fixes_response_spectralComponent S X
    (exactPrincipalMoleculeRoot S X a : ℂ) (lambda : ℂ) _
    (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a 1))
  · simpa only [PrimeStar.complexifyEuclidean_sub, PrimeStar.complexifyEuclidean_smul,
      ← oneExitLargePrimeMatrix_complexify, exactBoundaryModeInteriorVector] using
      congrArg PrimeStar.complexifyEuclidean hsolve
  · exact_mod_cast (sub_pos.mpr (hl.trans hroot)).ne'
  · have hsource := oneExitProjection_fixes_spectralComponent S X (lambda : ℂ) _
      (oneExitProjection_fixes_positiveStarSource haY hd)
    simpa only [exactBoundaryModeInteriorSource_eq_smallPrime, smallPrime_complexify,
      moleculePositiveStarMode] using hsource

/-- The full actual molecule, not just its boundary kernel, has only zero
forest modes outside the one-exit space. Both signed responses and the
kernel response are retained in the decomposition. -/
theorem eventually_powerRange_largePrime_discardedFullMolecule_eq_zero
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
          (Matrix.toEuclideanLin (oneExitComplementProjection S X)
            (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a))) = 0 := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap S hS htheta,
    eventually_powerRange_oneExitProjection_fixes_negativeStarMode S hS htheta,
    eventually_positiveResponse_negativeCapture S hS htheta,
    eventually_powerRange_oneExitProjection_fixes_negativeResponse_spectralComponent S hS htheta,
    eventually_powerRange_oneExitProjection_fixes_kernelResponse_negativeSpectralComponent
      S hS htheta] with X hwindow hden hgap hminus hplusResp hminusResp hkernelResp
  intro a ha
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hroot : 0 < exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    linarith
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let Q := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  have hQfix (v : EuclideanSpace ℂ (PrimeStar.Vertex S X))
      (hv : Matrix.toEuclideanLin (oneExitProjection S X) v = v) : L (Q v) = 0 := by
    have hq : Q v = 0 := by
      simp only [Q, oneExitComplementProjection, map_sub, LinearMap.sub_apply,
        Matrix.toLpLin_one, LinearMap.id_apply, hv, sub_self]
    rw [hq, map_zero]
  have hup := hQfix _ (oneExitProjection_fixes_positiveStarMode haY hd)
  have hum := hQfix _ (hminus a ha)
  have hkernel : L (Q (PrimeStar.complexifyEuclidean
      (exactPrincipalMoleculeBoundaryKernel S X a))) = 0 :=
    largePrime_apply_discardedBoundaryKernel_eq_zero haY hd
  have hpr : L (Q (PrimeStar.complexifyEuclidean
      (exactBoundaryModeInteriorVector S X a 1))) = 0 :=
    largePrime_apply_oneExitComplement_eq_zero_of_negativeCapture S X _ (hplusResp a ha)
  have hmr : L (Q (PrimeStar.complexifyEuclidean
      (exactBoundaryModeInteriorVector S X a (-1)))) = 0 :=
    largePrime_apply_oneExitComplement_eq_zero_of_negativeCapture S X _ (hminusResp a ha)
  have hkr : L (Q (PrimeStar.complexifyEuclidean
      (exactPrincipalMoleculeKernelInteriorVector S X a))) = 0 :=
    largePrime_apply_oneExitComplement_eq_zero_of_negativeCapture S X _ (hkernelResp a ha)
  have hboundary : exactPrincipalMoleculeBoundaryVector S X a =
      exactPrincipalMoleculeSignedBoundaryVector S X a +
        exactPrincipalMoleculeBoundaryKernel S X a := by
    simp [exactPrincipalMoleculeSignedBoundaryVector]
  have hadd (v w : MoleculeAmbient S X) :
      PrimeStar.complexifyEuclidean (v + w) =
        PrimeStar.complexifyEuclidean v + PrimeStar.complexifyEuclidean w := by
    ext i
    simp [PrimeStar.complexifyEuclidean_apply]
  change L (Q (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a))) = 0
  rw [← exactPrincipalMolecule_boundary_add_interior haY, hboundary,
    exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hd,
    exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel hS haY hroot.ne'
      (moleculeStarEnergy S X a / 100) (by positivity) (hgap a ha) (hden a ha),
    exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [hadd, PrimeStar.complexifyEuclidean_smul,
    map_add, map_smul, hkernel, hpr, hmr, hkr, hum,
    show L (Q (PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
      (squareRootCutoff X) a 1))) = 0 from hup,
    smul_zero, add_zero]

/-- Every complete power-prefix tail is killed by the forest. Consequently
the adjacency-on-tail term in the projected residual is exactly H Z. -/
theorem eventually_powerRange_fullStarFrameTail_largePrime_zero
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      oneExitLargePrimeMatrix S X * fullStarFrameTail S X K = 0 ∧
        moleculeFamilyComplexAdjacency S X * fullStarFrameTail S X K =
          oneExitSmallPrimeMatrix S X * fullStarFrameTail S X K := by
  filter_upwards [eventually_powerRange_largePrime_discardedFullMolecule_eq_zero S hS htheta]
    with X htail
  intro K hK
  have hz : oneExitLargePrimeMatrix S X * fullStarFrameTail S X K = 0 := by
    ext v a
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
    have h : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
        (Matrix.toEuclideanLin (oneExitComplementProjection S X)
          (phasedFullStarMolecule S X a.1)) = 0 := by
      simp only [phasedFullStarMolecule, map_smul, htail a.1 ha, smul_zero]
    exact congrArg (fun u : EuclideanSpace ℂ (PrimeStar.Vertex S X) ↦ u v) h
  refine ⟨hz, ?_⟩
  rw [moleculeFamilyComplexAdjacency_eq_large_add_small, Matrix.add_mul, hz, zero_add]

end FullMoleculeTail

noncomputable section QuantitativeFullTail

open Filter
open scoped Classical

/-- A discarded response which is a forest zero mode is exactly the
inverse-root response to the discarded zero-mode source. This retains
the signed down-kernel term rather than setting it to zero. -/
theorem oneExitComplement_response_eq_zeroModeSource
    (S : Finset ℕ) (X : ℕ) (nu : ℂ) (hnu : nu ≠ 0)
    (x b : EuclideanSpace ℂ (PrimeStar.Vertex S X))
    (hsolve : nu • x - Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x = b)
    (hzero : Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
      (Matrix.toEuclideanLin (oneExitComplementProjection S X) x) = 0) :
    Matrix.toEuclideanLin (oneExitComplementProjection S X) x =
      nu⁻¹ • Matrix.toEuclideanLin (oneExitComplementProjection S X)
        (largePrimeZeroModeProjection S X b) := by
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  let Q := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  let E := largePrimeZeroModeProjection S X
  have hP : P.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hcomm : Commute P L := by
    change P * L = L * P
    have h := congrArg Matrix.toEuclideanLin (oneExitProjection_commutes_largePrime S X).eq
    simpa only [Matrix.toLpLin_mul_same, ← Module.End.mul_eq_comp] using h
  have hEP := LinearMap.congr_fun (eigenprojection_commutes_of_commute L P hP hcomm 0).eq x
  change E (P x) = P (E x) at hEP
  have hQE : Q (E x) = E (Q x) := by
    simp only [Q, oneExitComplementProjection, map_sub, LinearMap.sub_apply,
      Matrix.toLpLin_one, LinearMap.id_apply]
    exact congrArg (fun v ↦ E x - v) hEP.symm
  have hfix : E (Q x) = Q x := by
    apply Submodule.starProjection_eq_self_iff.mpr
    apply Module.End.mem_eigenspace_iff.mpr
    simpa only [zero_smul] using hzero
  have h := congrArg (fun v ↦ Q (E v)) hsolve
  have hEL : E (L x) = 0 := by
    simpa only [E, L, largePrimeZeroModeProjection, zero_smul] using
      forest_eigenprojection_apply S X 0 x
  change Q (E (nu • x - L x)) = Q (E b) at h
  rw [map_sub, map_smul, hEL, sub_zero, map_smul, hQE, hfix] at h
  have hinv := congrArg (fun v ↦ nu⁻¹ • v) h
  simpa only [smul_smul, inv_mul_cancel₀ hnu, one_smul] using hinv

/-- The actual positive signed response is entirely retained. The negative
signed response has exactly the repaired inverse-root down-kernel tail. -/
theorem eventually_powerRange_discardedSignedResponses_eq
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        let Q := Matrix.toEuclideanLin (oneExitComplementProjection S X)
        Q (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a 1)) = 0 ∧
        Q (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a (-1))) =
          (-2 / (exactPrincipalMoleculeRoot S X a : ℂ)) •
            Q (signedZeroModeSourceDifference S X a) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    eventually_positiveResponse_negativeCapture S hS htheta,
    eventually_powerRange_oneExitProjection_fixes_negativeResponse_spectralComponent S hS htheta]
      with X hwindow hden hplus hminus
  intro a ha
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hroot : 0 < exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    linarith
  let Q := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  have hresponse (eps : ℝ)
      (hcapture : ∀ lambda : ℝ, lambda < 0 →
        let E := (Module.End.eigenspace (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X))
          (lambda : ℂ)).starProjection
        Matrix.toEuclideanLin (oneExitProjection S X)
          (E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a eps))) =
          E (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a eps))) :
      Q (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a eps)) =
        (exactPrincipalMoleculeRoot S X a : ℂ)⁻¹ •
          Q (largePrimeZeroModeProjection S X
            (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorSource S X a eps))) := by
    have hsolve := PrimeStar.firstExitStar_shift_resolventVector
      (exactBoundaryModeInteriorSource S X a eps) (PrimeStar.sqrtCutoff_condition X)
      hroot.ne' (hden a ha)
      (fun v hv ↦ exactBoundaryModeInteriorSource_eq_zero_of_not_mem hv)
    apply oneExitComplement_response_eq_zeroModeSource S X _
      (by exact_mod_cast hroot.ne')
    · simpa only [PrimeStar.complexifyEuclidean_sub, PrimeStar.complexifyEuclidean_smul,
        ← oneExitLargePrimeMatrix_complexify, exactBoundaryModeInteriorVector] using
        congrArg PrimeStar.complexifyEuclidean hsolve
    · exact largePrime_apply_oneExitComplement_eq_zero_of_negativeCapture S X _ hcapture
  constructor
  · rw [hresponse 1 (hplus a ha)]
    have hz := oneExitComplement_kills_positiveZeroSource haY hd
    simpa only [exactBoundaryModeInteriorSource_eq_smallPrime, smallPrime_complexify,
      moleculePositiveStarMode, Q, hz, smul_zero] using
      congrArg (fun v ↦ (exactPrincipalMoleculeRoot S X a : ℂ)⁻¹ • v) hz
  · rw [hresponse (-1) (hminus a ha)]
    have hsource := oneExitComplement_negativeZeroSource_eq haY hd
    simp only [exactBoundaryModeInteriorSource_eq_smallPrime, ← smallPrime_complexify]
    rw [show Q (largePrimeZeroModeProjection S X
        (Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
          (PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
            (squareRootCutoff X) a (-1))))) =
        (-2 : ℂ) • Q (signedZeroModeSourceDifference S X a) from hsource, smul_smul]
    congr 1
    ring

/-- The negative boundary coefficient pays both the first-exit gap and the
distance from the negative boundary mode. This is the scalar equation,
not a bound on the whole molecule by the residual norm. -/
theorem gap_mul_energy_mul_abs_negativeBoundaryCoefficient_le
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (gamma eta : ℝ) (hgamma : 0 ≤ gamma) (heta : 0 ≤ eta)
    (hroot : 0 ≤ exactPrincipalMoleculeRoot S X a)
    (hgap : ∀ x : MoleculeAmbient S X, gamma * ‖x‖ ≤
      ‖exactPrincipalMoleculeRoot S X a • x -
        PrimeStar.firstExitLargePrimeCompressionOperator S X (squareRootCutoff X) a x‖)
    (hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) x‖ ≤ eta * ‖x‖) :
    gamma * moleculeStarEnergy S X a *
      |exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)| ≤ eta ^ 2 := by
  classical
  let x := exactPrincipalMoleculeInteriorVector S X a
  let F := exactPrincipalMoleculeBoundaryFeedback S X a
  let H := Matrix.toEuclideanLin
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
  let u := PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a (-1)
  have hx : gamma * ‖x‖ ≤ eta :=
    gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_smallPrime
      hS ha gamma eta heta hgap hH
  have hF : ‖F‖ ≤ ‖H x‖ := by
    dsimp [F, exactPrincipalMoleculeBoundaryFeedback]
    exact PrimeStar.norm_euclideanCoordinateProjection_le _ _
  have hfeedback : gamma * ‖F‖ ≤ eta ^ 2 := by
    calc
      gamma * ‖F‖ ≤ gamma * ‖H x‖ := by gcongr
      _ ≤ gamma * (eta * ‖x‖) := by gcongr; exact hH x
      _ = eta * (gamma * ‖x‖) := by ring
      _ ≤ eta * eta := by gcongr
      _ = eta ^ 2 := by ring
  have hu : ‖u‖ = 1 := PrimeStar.norm_largePrimeNormalizedStarMode hd
  have hinner := abs_real_inner_le_norm u F
  rw [hu, one_mul] at hinner
  have hscalar := congrArg abs (exactPrincipalMolecule_negativeMode_scalarEquation hS ha)
  rw [abs_mul] at hscalar
  have hcoeff : |exactPrincipalMoleculeRoot S X a + moleculeStarEnergy S X a| *
      |exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)| ≤ ‖F‖ :=
    hscalar.trans_le hinner
  have hmu : moleculeStarEnergy S X a ≤
      |exactPrincipalMoleculeRoot S X a + moleculeStarEnergy S X a| :=
    (le_add_of_nonneg_left hroot).trans (le_abs_self _)
  calc
    gamma * moleculeStarEnergy S X a *
        |exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)| =
      gamma * (moleculeStarEnergy S X a *
        |exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)|) := by ring
    _ ≤ gamma * (|exactPrincipalMoleculeRoot S X a + moleculeStarEnergy S X a| *
        |exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)|) := by gcongr
    _ ≤ gamma * ‖F‖ := by gcongr
    _ ≤ eta ^ 2 := hfeedback

/-- On the actual power range the negative coefficient has its squared
residual gain, and the kernel-driven response is no larger than its
boundary kernel. All gap and residual premises are instantiated. -/
theorem eventually_powerRange_negativeCoefficient_and_kernelResponse_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        |exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)| ≤
          100 * PrimeStar.sqrtCutoffResidualScale X ^ 2 / moleculeStarEnergy S X a ^ 2 ∧
        ‖exactPrincipalMoleculeKernelInteriorVector S X a‖ ≤
          ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
  classical
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall
      S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned]
    with X hwindow hgap hden hresidual
  intro a ha
  obtain ⟨haY, hd, hshift, hsmall⟩ := hwindow a ha
  let mu := moleculeStarEnergy S X a
  let eta := PrimeStar.sqrtCutoffResidualScale X
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
    (PrimeStar.tunedSchurScale_nonneg _)
  have hroot : 0 < exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    change 0 < moleculeStarEnergy S X a at hmu
    linarith
  have hH : ∀ x : MoleculeAmbient S X,
      ‖Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) x‖ ≤ eta * ‖x‖ := by
    intro x
    simpa [eta, PrimeStar.sqrtCutoffResidualScale,
      PrimeStar.sqrtCutoffResidualConstant] using hresidual S x
  have hgamma : 0 < mu / 100 := by positivity
  have hcoef := gap_mul_energy_mul_abs_negativeBoundaryCoefficient_le
    hS haY hd (mu / 100) eta hgamma.le heta hroot.le (hgap a ha) hH
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hmu)).mpr
    dsimp only [mu, eta] at hcoef ⊢
    nlinarith
  · have hk := gamma_mul_norm_exactPrincipalMoleculeKernelInteriorVector_le
      hS haY hroot.ne' (mu / 100) hgamma (hgap a ha) (hden a ha)
    have hsource := norm_exactPrincipalMoleculeKernelInteriorSource_le (a := a) eta hH
    have hetaGap : eta ≤ mu / 100 := by
      change 1000000 * eta ^ 2 ≤ mu ^ 2 at hsmall
      nlinarith [sq_nonneg (mu - 100 * eta)]
    have hbound := hk.trans (hsource.trans
      (mul_le_mul_of_nonneg_right hetaGap (norm_nonneg _)))
    exact (mul_le_mul_iff_right₀ hgamma).mp hbound

private theorem norm_discarded_apply_le (S : Finset ℕ) (X : ℕ)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X)) :
    ‖Matrix.toEuclideanLin (oneExitComplementProjection S X) x‖ ≤ ‖x‖ := by
  let F := oneExitComplementProjection S X
  have hnorm : ‖F‖ ≤ (1 : ℝ) :=
    IsStarProjection.norm_le _ (oneExitComplementProjection_isStarProjection S X)
  change ‖(EuclideanSpace.equiv (PrimeStar.Vertex S X) ℂ).symm
    (F.mulVec x.ofLp)‖ ≤ ‖x‖
  exact (F.l2_opNorm_mulVec x).trans <| by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)

set_option maxHeartbeats 800000 in
/-- Quantitative tail of the entire actual full-star molecule. The second
term is essential: a negative signed response can leave an uncharged
down-star zero mode even when the boundary kernel vanishes. -/
theorem eventually_powerRange_discardedFullMolecule_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ‖Matrix.toEuclideanLin (oneExitComplementProjection S X)
          (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a))‖ ^ 2 ≤
        8 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 +
          8 * (|exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)| /
            exactPrincipalMoleculeRoot S X a) ^ 2 * ((a : ℕ).primeFactors.card : ℝ) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    eventually_powerRange_oneExitProjection_fixes_negativeStarMode S hS htheta,
    eventually_powerRange_discardedSignedResponses_eq S hS htheta,
    eventually_powerRange_negativeCoefficient_and_kernelResponse_bound S hS htheta]
    with X hwindow hgap hden hnegative hsigned hresponse
  intro a ha
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hroot : 0 < exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    linarith
  let Q := Matrix.toEuclideanLin (oneExitComplementProjection S X)
  let k := exactPrincipalMoleculeBoundaryKernel S X a
  let u := exactPrincipalMoleculeKernelInteriorVector S X a
  let beta := exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)
  let nu := exactPrincipalMoleculeRoot S X a
  let D := signedZeroModeSourceDifference S X a
  let v := (beta : ℂ) • ((-2 / (nu : ℂ)) • Q D)
  have hQfix (x : EuclideanSpace ℂ (PrimeStar.Vertex S X))
      (hx : Matrix.toEuclideanLin (oneExitProjection S X) x = x) : Q x = 0 := by
    simp only [Q, oneExitComplementProjection, map_sub, LinearMap.sub_apply,
      Matrix.toLpLin_one, LinearMap.id_apply, hx, sub_self]
  have hup := hQfix _ (oneExitProjection_fixes_positiveStarMode haY hd)
  have hum := hQfix _ (hnegative a ha)
  obtain ⟨hpr, hmr⟩ := hsigned a ha
  change Q (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a 1)) = 0 at hpr
  change Q (PrimeStar.complexifyEuclidean (exactBoundaryModeInteriorVector S X a (-1))) =
    (-2 / (nu : ℂ)) • Q D at hmr
  have hboundary : exactPrincipalMoleculeBoundaryVector S X a =
      exactPrincipalMoleculeSignedBoundaryVector S X a + k := by
    simp [exactPrincipalMoleculeSignedBoundaryVector, k]
  have hdecomp : Q (PrimeStar.complexifyEuclidean
      (exactPrincipalMoleculeAmbientVector S X a)) =
      Q (PrimeStar.complexifyEuclidean k) + (v + Q (PrimeStar.complexifyEuclidean u)) := by
    rw [← exactPrincipalMolecule_boundary_add_interior haY, hboundary,
      exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hd,
      exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel hS haY hroot.ne'
        (moleculeStarEnergy S X a / 100) (by positivity) (hgap a ha) (hden a ha),
      exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
    simp only [complexify_add, PrimeStar.complexifyEuclidean_smul, map_add, map_smul,
      show Q (PrimeStar.complexifyEuclidean (PrimeStar.largePrimeNormalizedStarMode S X
        (squareRootCutoff X) a 1)) = 0 from hup, hum, hpr, hmr,
      smul_zero, zero_add, v, beta, nu, D, u]
  have hk : ‖Q (PrimeStar.complexifyEuclidean k)‖ ≤ ‖k‖ := by
    simpa only [PrimeStar.norm_complexifyEuclidean] using
      norm_discarded_apply_le S X (PrimeStar.complexifyEuclidean k)
  have hu : ‖Q (PrimeStar.complexifyEuclidean u)‖ ≤ ‖k‖ := by
    have h : ‖Q (PrimeStar.complexifyEuclidean u)‖ ≤ ‖u‖ := by
      simpa only [PrimeStar.norm_complexifyEuclidean] using
        norm_discarded_apply_le S X (PrimeStar.complexifyEuclidean u)
    exact h.trans (hresponse a ha).2
  have hQD : ‖Q D‖ ^ 2 ≤ ((a : ℕ).primeFactors.card : ℝ) / 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_discarded_apply_le S X D) 2).trans
      (norm_sq_signedZeroModeSourceDifference_le hS haY hd)
  have hvnorm : ‖v‖ = (2 * (|beta| / nu)) * ‖Q D‖ := by
    dsimp only [v]
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_div,
      norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hroot]
    ring
  have hv : ‖v‖ ^ 2 ≤
      2 * (|beta| / nu) ^ 2 * ((a : ℕ).primeFactors.card : ℝ) := by
    rw [hvnorm, mul_pow]
    calc
      (2 * (|beta| / nu)) ^ 2 * ‖Q D‖ ^ 2 ≤
          (2 * (|beta| / nu)) ^ 2 * (((a : ℕ).primeFactors.card : ℝ) / 2) := by gcongr
      _ = _ := by ring
  have hnorm : ‖Q (PrimeStar.complexifyEuclidean
      (exactPrincipalMoleculeAmbientVector S X a))‖ ≤ 2 * ‖k‖ + ‖v‖ := by
    rw [hdecomp]
    have h := (norm_add_le (Q (PrimeStar.complexifyEuclidean k))
      (v + Q (PrimeStar.complexifyEuclidean u))).trans
        (add_le_add le_rfl (norm_add_le v (Q (PrimeStar.complexifyEuclidean u))))
    linarith only [h, hk, hu]
  have hnormSq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  change ‖Q (PrimeStar.complexifyEuclidean
    (exactPrincipalMoleculeAmbientVector S X a))‖ ^ 2 ≤ _
  change _ ≤ 8 * ‖k‖ ^ 2 +
    8 * (|beta| / nu) ^ 2 * ((a : ℕ).primeFactors.card : ℝ)
  nlinarith only [hnormSq, hv, sq_nonneg (2 * ‖k‖ - ‖v‖),
    mul_nonneg (sq_nonneg (|beta| / nu)) (Nat.cast_nonneg (a : ℕ).primeFactors.card)]

private theorem negativeCoefficientRatio_sq_le_rate {x a L mu nu beta eta C : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hL : 0 < L) (hmu : 0 < mu)
    (hnu : mu / 2 ≤ nu)
    (hb : |beta| ≤ 100 * eta ^ 2 / mu ^ 2)
    (hs : eta ^ 4 / mu ^ 2 ≤ 128 * C ^ 4 * (a / L))
    (hm : x / (8 * a * L) ≤ mu ^ 2) :
    (|beta| / nu) ^ 2 ≤ 327680000 * C ^ 4 * a ^ 3 * L / x ^ 2 := by
  have hnuPos : 0 < nu := lt_of_lt_of_le (by positivity) hnu
  have hbdiv : |beta| / nu ≤ 200 * eta ^ 2 / mu ^ 3 := by
    calc
      |beta| / nu ≤ (100 * eta ^ 2 / mu ^ 2) / (mu / 2) :=
        div_le_div₀ (by positivity) hb (by positivity) hnu
      _ = _ := by field_simp; ring
  have hinv : 1 / mu ^ 2 ≤ 8 * a * L / x := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hmu) hx).mpr
    have h := (div_le_iff₀ (show 0 < 8 * a * L by positivity)).mp hm
    nlinarith
  calc
    (|beta| / nu) ^ 2 ≤ (200 * eta ^ 2 / mu ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbdiv 2
    _ = 40000 * (eta ^ 4 / mu ^ 2) * (1 / mu ^ 2) ^ 2 := by field_simp; ring
    _ ≤ 40000 * (128 * C ^ 4 * (a / L)) * (8 * a * L / x) ^ 2 := by gcongr
    _ = _ := by field_simp; ring

/-- The actual full-molecule tail has a uniform quantitative rate on every
fixed sub-square-root power prefix. The first term retains the log-cubed
rate of the existing boundary-kernel producer; the signed down-kernel term
has its separate a-cubed omega(a) rate. No capture, gap or norm premise remains. -/
theorem eventually_powerRange_discardedFullMolecule_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
        InPowerRange theta X (a : ℕ) →
          ‖Matrix.toEuclideanLin (oneExitComplementProjection S X)
            (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a))‖ ^ 2 ≤
          C * ((a : ℝ) * Real.log (X : ℝ) ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ)) +
            (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * Real.log (X : ℝ) / (X : ℝ) ^ 2) := by
  obtain ⟨Ck, hCk, hkernel⟩ :=
    eventually_powerRange_exactPrincipalMoleculeBoundaryKernel_sq_le_scale S hS htheta
  let Cb := 327680000 * PrimeStar.sqrtCutoffResidualConstant ^ 4
  let C := 8 * Ck + 8 * Cb
  have hCb : 0 < Cb := mul_pos (by norm_num)
    (pow_pos PrimeStar.sqrtCutoffResidualConstant_pos 4)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hkernel, eventually_powerRange_discardedFullMolecule_sq_le S hS htheta,
    eventually_powerRange_negativeCoefficient_and_kernelResponse_bound S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 4] with X hk htail hcoef hscale hwindow hX
  intro a ha
  obtain ⟨_, hd, hshift⟩ := hwindow a ha
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have haPos : 0 < (a : ℝ) := by exact_mod_cast a.property.1
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hnu : moleculeStarEnergy S X a / 2 ≤ exactPrincipalMoleculeRoot S X a := by
    have h := (abs_le.mp hshift).1
    linarith
  have hratio := negativeCoefficientRatio_sq_le_rate hx haPos hL hmu hnu
    (hcoef a ha).1 (hscale a ha).2 (hscale a ha).1
  let t1 := (a : ℝ) * Real.log (X : ℝ) ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ))
  let t2 := (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * Real.log (X : ℝ) / (X : ℝ) ^ 2
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  change _ ≤ C * (t1 + t2)
  calc
    _ ≤ 8 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 +
        8 * (|exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)| /
          exactPrincipalMoleculeRoot S X a) ^ 2 * ((a : ℕ).primeFactors.card : ℝ) := htail a ha
    _ ≤ 8 * (Ck * (a : ℝ) * Real.log (X : ℝ) ^ 3 /
          ((X : ℝ) * Real.sqrt (X : ℝ))) +
        8 * (Cb * (a : ℝ) ^ 3 * Real.log (X : ℝ) / (X : ℝ) ^ 2) *
          ((a : ℕ).primeFactors.card : ℝ) := by
      gcongr
      exact hk a ha
    _ = 8 * Ck * t1 + 8 * Cb * t2 := by dsimp [t1, t2]; ring
    _ ≤ C * (t1 + t2) := by
      dsimp only [C]
      nlinarith only [mul_nonneg hCk.le ht2, mul_nonneg hCb.le ht1]

end QuantitativeFullTail

noncomputable section SourceContinuation

open Filter
open scoped Classical

/-- An upward step into the full first-exit support, from outside the
original boundary star, has a prime label dividing the source centre.
The excluded boundary returns are exactly where this assertion fails. -/
theorem prime_dvd_source_of_upward_exterior_firstExit_step
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a v w : PrimeStar.Vertex S X} {r : ℕ}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hr : r.Prime) (hrY : r ≤ squareRootCutoff X)
    (hw : w ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a)
    (hv : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
    (hstep : (v : ℕ) * r = (w : ℕ)) : r ∣ (a : ℕ) := by
  have hbase {b q : ℕ} (hq : q.Prime)
      (hrel : (a : ℕ) * q = b ∨ b * q = (a : ℕ)) (hrb : r ∣ b) :
      r ∣ (a : ℕ) ∨ b = (a : ℕ) * r := by
    rcases hrel with hup | hdown
    · have hdiv : r ∣ (a : ℕ) * q := hup.symm ▸ hrb
      rcases hr.dvd_mul.mp hdiv with hra | hrq
      · exact Or.inl hra
      · exact Or.inr (by rw [← hup, (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq])
    · exact Or.inl (dvd_trans hrb ⟨q, hdown.symm⟩)
  have hcenter (q : ℕ) (hq : q.Prime)
      (hrel : (a : ℕ) * q = (w : ℕ) ∨ (w : ℕ) * q = (a : ℕ)) : r ∣ (a : ℕ) := by
    have hrw : r ∣ (w : ℕ) := ⟨(v : ℕ), by rw [← hstep, Nat.mul_comm]⟩
    rcases hbase hq hrel hrw with h | h
    · exact h
    · have hva : v = a := Subtype.ext (Fin.ext
        (Nat.eq_of_mul_eq_mul_right hr.pos (hstep.trans h)))
      exact False.elim (hv (by simp [hva, PrimeStar.largePrimeStarSupport]))
  rw [PrimeStar.firstExitCompressionSupport, Finset.mem_union] at hw
  rcases hw with hw | hw
  · obtain ⟨b, hb, hwb⟩ := PrimeStar.mem_largePrimeStarUnionSupport.mp hw
    obtain ⟨q, hq, _, _, hrel⟩ := PrimeStar.mem_firstExitLowerCenters_arithmetic
      (PrimeStar.sqrtCutoff_condition X) ha hb
    rw [PrimeStar.mem_largePrimeStarSupport] at hwb
    rcases hwb with hwb | hwb
    · subst w
      exact hcenter q hq hrel
    · have hbY := (PrimeStar.mem_firstExitLowerCenters.mp hb).1
      obtain ⟨p, hp, hpS, hYp, hbp⟩ :=
        PrimeStar.isLargePrimeChild_of_largePrimeAdj_of_le hbY hwb
      have hrbp : r ∣ (b : ℕ) * p := ⟨(v : ℕ), by
        rw [hbp, ← hstep, Nat.mul_comm]⟩
      have hrb : r ∣ (b : ℕ) := by
        rcases hr.dvd_mul.mp hrbp with h | h
        · exact h
        · have hrp := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
          exact False.elim (not_lt_of_ge hrY (hrp.symm ▸ hYp))
      rcases hbase hq hrel hrb with hra | hba
      · exact hra
      · have hav : (a : ℕ) * p = (v : ℕ) := by
          apply Nat.eq_of_mul_eq_mul_right hr.pos
          calc
            (a : ℕ) * p * r = ((a : ℕ) * r) * p := by ac_rfl
            _ = (b : ℕ) * p := by rw [hba]
            _ = (w : ℕ) := hbp
            _ = (v : ℕ) * r := hstep.symm
        apply False.elim
        apply hv
        exact PrimeStar.mem_largePrimeStarSupport.mpr (Or.inr
          (PrimeStar.isLargePrimeChild_largePrimeAdj ⟨p, hp, hpS, hYp, hav⟩))
  · obtain ⟨q, hq, _, _, hrel⟩ :=
      PrimeStar.mem_firstExitIsolatedVertices_arithmetic hS ha hw
    exact hcenter q hq hrel

/-- Once boundary returns are removed, the incoming multiplicity is at
most omega(source)+omega(output). This finite bound avoids paying the
full small-prime degree when a residual coordinate is squared. -/
theorem card_exterior_firstExit_neighbors_le_primeFactors
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a v : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hv : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a) :
    (((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).neighborFinset v) ∩
      PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a).card ≤
        (a : ℕ).primeFactors.card + (v : ℕ).primeFactors.card := by
  let N := ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).neighborFinset v) ∩
    PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
  have hsub : N.image (fun w : PrimeStar.Vertex S X ↦ (w : ℕ)) ⊆
      (a : ℕ).primeFactors.image (fun r ↦ (v : ℕ) * r) ∪
        (v : ℕ).primeFactors.image (fun r ↦ (v : ℕ) / r) := by
    intro n hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hadj, hwi⟩ := Finset.mem_inter.mp hw
    obtain ⟨r, hr, _, hrY, hstep⟩ :=
      PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp
        (((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).mem_neighborFinset v w).mp hadj)
    rcases hstep with hup | hdown
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨r, hr.mem_primeFactors
        (prime_dvd_source_of_upward_exterior_firstExit_step hS ha hr hrY hwi hv hup)
        (PrimeStar.Vertex.coe_pos a).ne', hup⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨r, hr.mem_primeFactors ⟨(w : ℕ), by rw [← hdown, Nat.mul_comm]⟩
        (PrimeStar.Vertex.coe_pos v).ne', ?_⟩
      rw [← hdown, Nat.mul_div_cancel _ hr.pos]
  have hinj : Function.Injective (fun w : PrimeStar.Vertex S X ↦ (w : ℕ)) := by
    intro b c h
    exact Subtype.ext (Fin.ext h)
  calc
    N.card = (N.image (fun w : PrimeStar.Vertex S X ↦ (w : ℕ))).card :=
      (Finset.card_image_of_injective N hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ((a : ℕ).primeFactors.image (fun r ↦ (v : ℕ) * r)).card +
        ((v : ℕ).primeFactors.image (fun r ↦ (v : ℕ) / r)).card := Finset.card_union_le _ _
    _ ≤ _ := add_le_add (Finset.card_image_le) (Finset.card_image_le)

/-- Squaring an exterior coordinate costs only its source/output divisor
multiplicity. The entries are still literal first-exit response values;
no coefficient envelope is assumed here. -/
theorem exterior_firstExit_apply_sq_le_weighted_neighbors
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a v : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hv : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a)
    (y : MoleculeAmbient S X)
    (hy : ∀ w, w ∉ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a → y w = 0) :
    (Matrix.toEuclideanLin
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) y v) ^ 2 ≤
      (((a : ℕ).primeFactors.card : ℝ) + ((v : ℕ).primeFactors.card : ℝ)) *
        ∑ w ∈ (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).neighborFinset v, (y w) ^ 2 := by
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let N := G.neighborFinset v ∩
    PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
  have hsum : ∑ w ∈ G.neighborFinset v, y w = ∑ w ∈ N, y w := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro w hw hwn
    exact hy w (fun hwi ↦ hwn (Finset.mem_inter.mpr ⟨hw, hwi⟩))
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq N (fun _ ↦ (1 : ℝ)) (fun w ↦ y w)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCauchy
  have hcard : (N.card : ℝ) ≤
      ((a : ℕ).primeFactors.card : ℝ) + ((v : ℕ).primeFactors.card : ℝ) := by
    exact_mod_cast card_exterior_firstExit_neighbors_le_primeFactors hS ha hv
  have hsquares : ∑ w ∈ N, (y w) ^ 2 ≤ ∑ w ∈ G.neighborFinset v, (y w) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left)
      (fun _ _ _ ↦ sq_nonneg _)
  rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
  change ((G.adjMatrix ℝ *ᵥ y.ofLp) v) ^ 2 ≤ _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  change (∑ w ∈ G.neighborFinset v, y w) ^ 2 ≤ _
  rw [hsum]
  exact hCauchy.trans (mul_le_mul hcard hsquares (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    (by positivity))

/-- A finite, source-weighted bound for the actual raw molecule residual.
The logarithm comes from proved incoming multiplicity, not the global
operator norm. The remaining consumer is the degree-weighted response sum. -/
theorem exactPrincipalMoleculeResidual_sq_le_degreeWeightedInterior
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hX : 2 ≤ X) :
    ‖exactPrincipalMoleculeResidual S X a‖ ^ 2 ≤
      (2 * Real.log (X : ℝ) / Real.log 2) *
        ∑ w : PrimeStar.Vertex S X,
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree w : ℝ) *
            (exactPrincipalMoleculeInteriorVector S X a w) ^ 2 := by
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let y := exactPrincipalMoleculeInteriorVector S X a
  let R := 2 * Real.log (X : ℝ) / Real.log 2
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have homega (w : PrimeStar.Vertex S X) :
      ((w : ℕ).primeFactors.card : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
    apply (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos w)).trans
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    exact Real.log_le_log (by exact_mod_cast PrimeStar.Vertex.coe_pos w)
      (by exact_mod_cast PrimeStar.Vertex.coe_le w)
  have hy : ∀ w, w ∉ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a → y w = 0 := by
    intro w hw
    simp [y, exactPrincipalMoleculeInteriorVector, PrimeStar.firstExitCompressionProjection_apply, hw]
  have hpoint (v : PrimeStar.Vertex S X) :
      (exactPrincipalMoleculeResidual S X a v) ^ 2 ≤ R * ∑ w ∈ G.neighborFinset v, (y w) ^ 2 := by
    by_cases hv : v ∈ exactPrincipalMoleculeSupport S X a
    · rw [exactPrincipalMoleculeResidual_apply_coordinate_eq_zero hS ha ⟨v, hv⟩]
      simpa using mul_nonneg hR (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg (y _)))
    · have hvB : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a :=
        fun h ↦ hv (Finset.mem_union_left _ h)
      rw [exactPrincipalMoleculeResidual_eq_exterior_smallPrime_interior hS ha,
        PrimeStar.euclideanCoordinateComplementProjection_apply, if_neg hv]
      apply (exterior_firstExit_apply_sq_le_weighted_neighbors hS ha hvB y hy).trans
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
      dsimp [R]
      have h1 := homega a
      have h2 := homega v
      calc
        _ ≤ Real.log (X : ℝ) / Real.log 2 + Real.log (X : ℝ) / Real.log 2 :=
          add_le_add h1 h2
        _ = _ := by ring
  have hswap : ∑ v : PrimeStar.Vertex S X, ∑ w ∈ G.neighborFinset v, (y w) ^ 2 =
      ∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) * (y w) ^ 2 := by
    simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    simp_rw [G.adj_comm _ w]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ v : PrimeStar.Vertex S X, R * ∑ w ∈ G.neighborFinset v, (y w) ^ 2 :=
      Finset.sum_le_sum (fun v _ ↦ hpoint v)
    _ = _ := by rw [← Finset.mul_sum, hswap]

/-- Down-star degree growth retains the dividing prime, uniformly in the
moving centre. This supplies the reciprocal-prime gain in the down-centre
response, which a constant separation bound alone would discard. -/
theorem eventually_powerRange_downStarDegree_mul_prime_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ q : PrimeStar.CanonicalDownIndex a,
          (q : ℝ) *
              (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ) ≤
            48 * (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
              (PrimeStar.canonicalDownTarget a q) : ℝ) := by
  filter_upwards [eventually_powerRange_arithmeticStarDegree_bounds S hS htheta,
    eventually_squareRootRange_allowedPrime_bounds S hS,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta]
    with X hdegree hprime hwindow
  intro a ha q
  let b := PrimeStar.canonicalDownTarget a q
  let N := X / (a : ℕ)
  let Nb := X / (b : ℕ)
  have hbpos : 0 < (b : ℕ) := PrimeStar.Vertex.coe_pos b
  have hble : (b : ℕ) ≤ (a : ℕ) := Nat.div_le_self _ _
  have hbRange : InPowerRange theta X (b : ℕ) :=
    ⟨hbpos, (show (b : ℝ) ≤ (a : ℝ) by exact_mod_cast hble).trans ha.2⟩
  have haData := hdegree a ha
  have hbData := hdegree b hbRange
  have hNY : Nat.sqrt X ≤ N := haData.1.trans (Nat.div_le_self _ 2)
  have hNbY : Nat.sqrt X ≤ Nb := hbData.1.trans (Nat.div_le_self _ 2)
  have hNprime := hprime N hNY (Nat.div_le_self _ _)
  have hNbprime := hprime Nb hNbY (Nat.div_le_self _ _)
  have hlogN : 0 < Real.log (N : ℝ) := hNprime.2.2.1
  have hlogNb : 0 < Real.log (Nb : ℝ) := hNbprime.2.2.1
  have hlogs : Real.log (Nb : ℝ) ≤ 3 * Real.log (N : ℝ) :=
    hNbprime.2.2.2.1.trans hNprime.2.2.2.2
  have hdiv : Nb / (q : ℕ) = N := by
    dsimp [Nb, N]
    rw [Nat.div_div_eq_div_mul]
    rw [show (b : ℕ) * (q : ℕ) = (a : ℕ) from
      PrimeStar.canonicalDownTarget_mul_coe a q]
  have hsize : (q : ℝ) * (N : ℝ) ≤ (Nb : ℝ) := by
    exact_mod_cast (show (q : ℕ) * N ≤ Nb by
      rw [← hdiv, Nat.mul_comm]
      exact Nat.div_mul_le_self _ _)
  have hmain : (q : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤
      3 * ((Nb : ℝ) / Real.log (Nb : ℝ)) := by
    calc
      _ = ((q : ℝ) * N) / Real.log (N : ℝ) := by ring
      _ ≤ (Nb : ℝ) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hsize hlogN.le
      _ ≤ (Nb : ℝ) / (Real.log (Nb : ℝ) / 3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = _ := by ring
  have hbound : (q : ℝ) * arithmeticStarDegree S (a : ℕ) X ≤
      48 * arithmeticStarDegree S (b : ℕ) X := by
    calc
      _ ≤ (q : ℝ) * (4 * ((N : ℝ) / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left haData.2.2.2 (by positivity)
      _ = 4 * ((q : ℝ) * ((N : ℝ) / Real.log (N : ℝ))) := by ring
      _ ≤ 12 * ((Nb : ℝ) / Real.log (Nb : ℝ)) := by nlinarith only [hmain]
      _ ≤ 48 * arithmeticStarDegree S (b : ℕ) X := by
        nlinarith only [hbData.2.2.1]
  have haY := (hwindow a ha).1
  have hbY : (b : ℕ) ≤ squareRootCutoff X := hble.trans haY
  have hgraph (c : PrimeStar.Vertex S X) (hc : (c : ℕ) ≤ squareRootCutoff X)
      (hY : squareRootCutoff X ≤ X / (c : ℕ)) :
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) c : ℝ) =
        arithmeticStarDegree S (c : ℕ) X := by
    rw [PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS c hc hY,
      Nat.cast_sub (PrimeStar.allowedPrimeCount_mono (S := S) hY)]
    rfl
  rw [hgraph a haY hNY, hgraph b hbY hNbY]
  exact hbound

private theorem downCenter_scalar_bound
    {z s mu q alpha beta : ℝ}
    (hmu : 0 < mu) (hq : 0 < q)
    (hzLower : 99 / 100 ≤ z) (hzUpper : z ≤ 101 / 100)
    (hs : 17 / 16 ≤ s) (hqS : q ≤ 48 * s)
    (halpha : |alpha| ≤ 2) (hbeta : |beta| ≤ 2) :
    |(z * alpha + beta) / (mu * (z ^ 2 - s))| ≤ 10000 / (q * mu) := by
  have hz : |z| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hzsq : z ^ 2 ≤ (101 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by norm_num)).mpr hzUpper
  have hsep : q / 1536 ≤ s - z ^ 2 := by nlinarith
  have hden : z ^ 2 - s < 0 := by
    have := div_pos hq (by norm_num : (0 : ℝ) < 1536)
    linarith
  have hnum : |z * alpha + beta| ≤ 6 := by
    calc
      _ ≤ |z| * |alpha| + |beta| := by simpa [abs_mul] using abs_add_le (z * alpha) beta
      _ ≤ 6 := by nlinarith [abs_nonneg z, abs_nonneg alpha]
  rw [abs_div, abs_mul, abs_of_pos hmu, abs_of_neg hden]
  calc
    _ ≤ 6 / (mu * (q / 1536)) :=
      div_le_div₀ (by norm_num) hnum (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith : q / 1536 ≤ -(z ^ 2 - s)) hmu.le)
    _ ≤ 10000 / (q * mu) := by
      field_simp
      nlinarith

/-- The actual signed response at each down-star centre retains a factor
reciprocal to its dividing prime. All moving degree and root-window
conditions are supplied, rather than exposed as coefficient assumptions. -/
theorem eventually_powerRange_signedDownCenter_abs_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ q : PrimeStar.CanonicalDownIndex a,
          |exactPrincipalMoleculeSignedInteriorVector S X a
            (PrimeStar.canonicalDownTarget a q)| ≤
              10000 / ((q : ℝ) * moleculeStarEnergy S X a) := by
  filter_upwards [eventually_powerRange_downStarDegree_mul_prime_le S hS htheta,
    eventually_powerRange_downStarRatio_ge S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta]
    with X hweighted hratio hwindow
  intro a ha q
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  let mu := moleculeStarEnergy S X a
  let z := exactPrincipalMoleculeRoot S X a / mu
  let s := (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
    (PrimeStar.canonicalDownTarget a q) : ℝ) / mu ^ 2
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors q.property).pos
  have hzLower : 99 / 100 ≤ z := by
    apply (le_div_iff₀ hmu).mpr
    have := (abs_le.mp hshift).1
    dsimp only [mu]
    linarith
  have hzUpper : z ≤ 101 / 100 := by
    apply (div_le_iff₀ hmu).mpr
    have := (abs_le.mp hshift).2
    dsimp only [mu]
    linarith
  have hratioGraph := PrimeStar.canonicalDownDegreeRatio_eq_fixedCenterActualDownRatio
    hS a haY q
  have hs : 17 / 16 ≤ s := by
    have h := hratio a ha (q : ℕ) q.property
    change 17 / 16 ≤ PrimeStar.fixedCenterArithmeticDegree S ((a : ℕ) / (q : ℕ)) X /
      PrimeStar.fixedCenterArithmeticDegree S (a : ℕ) X at h
    rw [← hratioGraph] at h
    simpa [s, mu, moleculeStarEnergy_sq] using h
  have hqs : (q : ℝ) ≤ 48 * s := by
    have h := hweighted a ha q
    rw [← moleculeStarEnergy_sq] at h
    dsimp only [s]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hmu)).mpr
    simpa only [mul_div_assoc] using h
  have hz : z ≠ 0 := ne_of_gt (by linarith : 0 < z)
  have hsep : z ^ 2 - s ≠ 0 := by
    have hzsq := (sq_le_sq₀ (by linarith : 0 ≤ z)
      (by norm_num : (0 : ℝ) ≤ 101 / 100)).mpr hzUpper
    nlinarith
  have hrootEq : exactPrincipalMoleculeRoot S X a = z * mu := by
    dsimp [z]
    rw [div_mul_cancel₀ _ hmu.ne']
  have hdegree : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q) : ℝ) = s * mu ^ 2 := by
    dsimp [s]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hmu).ne']
  rw [exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownTarget
    hS haY hd q hrootEq hdegree hz hsep]
  apply downCenter_scalar_bound hmu hq hzLower hzUpper hs hqs
  · exact (abs_add_le _ _).trans (by
      have hp := abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd
        (show (1 : ℝ) ^ 2 = 1 by norm_num)
      have hm := abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd
        (show (-1 : ℝ) ^ 2 = 1 by norm_num)
      linarith)
  · exact (abs_sub _ _).trans (by
      have hp := abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd
        (show (1 : ℝ) ^ 2 = 1 by norm_num)
      have hm := abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd
        (show (-1 : ℝ) ^ 2 = 1 by norm_num)
      linarith)

/-- The degree-weighted kernel response is already logarithmic. The
existing boundary-kernel rate pays even the full finite degree bound;
only the signed response requires the refined continuation weights. -/
theorem eventually_powerRange_degreeWeightedKernel_le_logCube
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        (∑ w : PrimeStar.Vertex S X,
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree w : ℝ) *
            (exactPrincipalMoleculeKernelInteriorVector S X a w) ^ 2) ≤
          C * Real.log (X : ℝ) ^ 3 := by
  obtain ⟨C, hC, hkernel⟩ :=
    eventually_powerRange_exactPrincipalMoleculeBoundaryKernel_sq_le_scale S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hkernel,
    eventually_powerRange_negativeCoefficient_and_kernelResponse_bound S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 2] with X hkernelX hresponse hwindow hX
  intro a ha
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let k := exactPrincipalMoleculeKernelInteriorVector S X a
  have hx : (0 : ℝ) < X := by positivity
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hcard : Fintype.card (PrimeStar.Vertex S X) ≤ X + 1 := by
    simpa using Fintype.card_le_of_injective
      (fun v : PrimeStar.Vertex S X ↦ v.1) Subtype.val_injective
  have hdeg (w : PrimeStar.Vertex S X) : (G.degree w : ℝ) ≤ X := by
    exact_mod_cast Nat.le_of_lt_succ ((G.degree_lt_card_verts w).trans_le hcard)
  have haY := (hwindow a ha).1
  have hasqrt : (a : ℝ) ≤ Real.sqrt (X : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show (a : ℕ) ^ 2 ≤ X by
      have hsq := Nat.sqrt_le X
      change (a : ℕ) ≤ Nat.sqrt X at haY
      nlinarith)
  have hk : ‖k‖ ^ 2 ≤ ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hresponse a ha).2
  calc
    _ ≤ ∑ w : PrimeStar.Vertex S X, (X : ℝ) * (k w) ^ 2 :=
      Finset.sum_le_sum (fun w _ ↦ mul_le_mul_of_nonneg_right (hdeg w) (sq_nonneg _))
    _ = (X : ℝ) * ‖k‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    _ ≤ (X : ℝ) * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 := by gcongr
    _ ≤ (X : ℝ) * (C * (a : ℝ) * Real.log (X : ℝ) ^ 3 /
        ((X : ℝ) * Real.sqrt (X : ℝ))) := by gcongr; exact hkernelX a ha
    _ = C * Real.log (X : ℝ) ^ 3 * ((a : ℝ) / Real.sqrt (X : ℝ)) := by
      field_simp
    _ ≤ C * Real.log (X : ℝ) ^ 3 := by
      have hratio : (a : ℝ) / Real.sqrt (X : ℝ) ≤ 1 :=
        (div_le_one (Real.sqrt_pos.mpr hx)).mpr hasqrt
      nlinarith [mul_nonneg hC.le (pow_nonneg hlog 3)]

/-- The actual residual now consumes only the signed degree-weighted
response. The kernel contribution is discharged at a fixed logarithmic
cost; no kernel, gap or collision premise remains in this reduction. -/
theorem eventually_powerRange_residual_sq_le_signedWeighted_add_logFourth
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        ‖exactPrincipalMoleculeResidual S X a‖ ^ 2 ≤
          (4 * Real.log (X : ℝ) / Real.log 2) *
            (∑ w : PrimeStar.Vertex S X,
              ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree w : ℝ) *
                (exactPrincipalMoleculeSignedInteriorVector S X a w) ^ 2) +
          C * Real.log (X : ℝ) ^ 4 := by
  obtain ⟨Ck, hCk, hkernel⟩ :=
    eventually_powerRange_degreeWeightedKernel_le_logCube S hS htheta
  refine ⟨4 * Ck / Real.log 2, by positivity, ?_⟩
  filter_upwards [hkernel,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    eventually_ge_atTop 2] with X hkernelX hwindow hgap hden hX
  intro a ha
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let i := exactPrincipalMoleculeSignedInteriorVector S X a
  let k := exactPrincipalMoleculeKernelInteriorVector S X a
  let R := 2 * Real.log (X : ℝ) / Real.log 2
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hmu : 0 < moleculeStarEnergy S X a :=
    Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hroot : exactPrincipalMoleculeRoot S X a ≠ 0 := by
    apply ne_of_gt
    have := (abs_le.mp hshift).1
    linarith
  have hsplit := exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel
    hS haY hroot (moleculeStarEnergy S X a / 100) (by positivity)
    (hgap a ha) (hden a ha)
  have hsum :
      (∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) *
        (exactPrincipalMoleculeInteriorVector S X a w) ^ 2) ≤
      2 * (∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) * (i w) ^ 2) +
      2 * (∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) * (k w) ^ 2) := by
    rw [hsplit]
    simp only [PiLp.add_apply]
    calc
      _ ≤ ∑ w : PrimeStar.Vertex S X,
          (2 * ((G.degree w : ℝ) * (i w) ^ 2) +
            2 * ((G.degree w : ℝ) * (k w) ^ 2)) := by
        apply Finset.sum_le_sum
        intro w _
        have hsq := mul_nonneg (show (0 : ℝ) ≤ G.degree w by positivity)
          (sq_nonneg (i w - k w))
        dsimp only [i, k] at hsq ⊢
        nlinarith
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ ≤ R * (∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) *
        (exactPrincipalMoleculeInteriorVector S X a w) ^ 2) :=
      exactPrincipalMoleculeResidual_sq_le_degreeWeightedInterior hS haY hX
    _ ≤ R * (2 * (∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) * (i w) ^ 2) +
        2 * (∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) * (k w) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum hR
    _ ≤ R * (2 * (∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) * (i w) ^ 2) +
        2 * (Ck * Real.log (X : ℝ) ^ 3)) := by
      gcongr
      exact hkernelX a ha
    _ = _ := by dsimp only [R, i, G]; ring

/-- Each small-prime neighbor is either an upward multiple or a downward
prime quotient. This finite degree bound keeps the reciprocal vertex weight
needed when summing actual first-exit responses. -/
theorem smallPrimeGraph_degree_le_div_add_primeFactors
    {S : Finset ℕ} {X Y : ℕ} (v : PrimeStar.Vertex S X) :
    (PrimeStar.smallPrimeGraph S X Y).degree v ≤
      X / (v : ℕ) + (v : ℕ).primeFactors.card := by
  let G := PrimeStar.smallPrimeGraph S X Y
  let N := G.neighborFinset v
  have hsub : N.image (fun w : PrimeStar.Vertex S X ↦ (w : ℕ)) ⊆
      (Finset.Icc 1 (X / (v : ℕ))).image (fun p ↦ (v : ℕ) * p) ∪
        (v : ℕ).primeFactors.image (fun p ↦ (v : ℕ) / p) := by
    intro n hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨p, hp, _, _, hstep⟩ :=
      PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp ((G.mem_neighborFinset v w).mp hw)
    rcases hstep with hup | hdown
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_Icc.mpr ⟨hp.one_le, ?_⟩, hup⟩
      apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos v)).mpr
      rw [Nat.mul_comm, hup]
      exact PrimeStar.Vertex.coe_le w
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨p, hp.mem_primeFactors ⟨(w : ℕ), by rw [← hdown, Nat.mul_comm]⟩
        (PrimeStar.Vertex.coe_pos v).ne', ?_⟩
      rw [← hdown, Nat.mul_div_cancel _ hp.pos]
  have hinj : Function.Injective (fun w : PrimeStar.Vertex S X ↦ (w : ℕ)) :=
    fun _ _ h ↦ Subtype.ext (Fin.ext h)
  calc
    G.degree v = N.card := (SimpleGraph.card_neighborFinset_eq_degree G v).symm
    _ = (N.image (fun w : PrimeStar.Vertex S X ↦ (w : ℕ))).card :=
      (Finset.card_image_of_injective N hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 (X / (v : ℕ))).image (fun p ↦ (v : ℕ) * p)).card +
        ((v : ℕ).primeFactors.image (fun p ↦ (v : ℕ) / p)).card := Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (X / (v : ℕ))).card + (v : ℕ).primeFactors.card :=
      add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp

/-- Real-valued degree majorant for summing response coefficients. It holds
at every nonempty vertex and every prime cutoff, with no PNT premise. -/
theorem smallPrimeGraph_degree_le_div_add_log
    {S : Finset ℕ} {X Y : ℕ} (v : PrimeStar.Vertex S X) :
    ((PrimeStar.smallPrimeGraph S X Y).degree v : ℝ) ≤
      (X : ℝ) / (v : ℝ) + Real.log (X : ℝ) / Real.log 2 := by
  have hlog : Real.log (v : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast PrimeStar.Vertex.coe_pos v)
      (by exact_mod_cast PrimeStar.Vertex.coe_le v)
  calc
    _ ≤ (X / (v : ℕ) : ℕ) + ((v : ℕ).primeFactors.card : ℝ) := by
      exact_mod_cast smallPrimeGraph_degree_le_div_add_primeFactors (Y := Y) v
    _ ≤ (X : ℝ) / (v : ℝ) + Real.log (v : ℝ) / Real.log 2 :=
      add_le_add Nat.cast_div_le (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos v))
    _ ≤ _ := add_le_add (le_refl _) (div_le_div_of_nonneg_right hlog
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))

private theorem downWeighted_scalar
    {x a q mu ell h v : ℝ}
    (ha : 0 < a) (hq : 1 ≤ q) (hmu : 0 < mu) (hmuOne : 1 ≤ mu ^ 2)
    (hh : 0 < h)
    (hscale : x / (8 * a * ell) ≤ mu ^ 2)
    (hellPos : 0 < ell)
    (hv : |v| ≤ 10000 / (q * mu)) :
    (x * q / a + ell / h) * v ^ 2 ≤
      10000 ^ 2 * (8 + 1 / h) * ell := by
  have hqpos : 0 < q := by linarith
  have hx : x ≤ 8 * a * ell * mu ^ 2 := by
    have := (div_le_iff₀ (by positivity : 0 < 8 * a * ell)).mp hscale
    nlinarith only [this]
  have hvsq : v ^ 2 ≤ (10000 / (q * mu)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg v) (by positivity)).mpr hv
  have hcoef : x * q / a + ell / h ≤ (8 + 1 / h) * ell * (q * mu) ^ 2 := by
    have hxq : x * q / a ≤ 8 * ell * mu ^ 2 * q := by
      apply (div_le_iff₀ ha).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hx hqpos.le]
    have hq2 : 1 ≤ q ^ 2 := by nlinarith
    have hproduct : 1 ≤ (q * mu) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hmuOne (sq_nonneg q)]
    have hfirst : 8 * ell * mu ^ 2 * q ≤ 8 * ell * (q * mu) ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ 8 * ell * mu ^ 2 * q by positivity) (show 0 ≤ q - 1 by linarith)]
    have hsecond := mul_le_mul_of_nonneg_left hproduct (show 0 ≤ ell / h by positivity)
    calc
      _ ≤ 8 * ell * (q * mu) ^ 2 + ell / h * (q * mu) ^ 2 :=
        add_le_add (hxq.trans hfirst) (by simpa using hsecond)
      _ = _ := by ring
  calc
    _ ≤ ((8 + 1 / h) * ell * (q * mu) ^ 2) * v ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ ((8 + 1 / h) * ell * (q * mu) ^ 2) * (10000 / (q * mu)) ^ 2 :=
      mul_le_mul_of_nonneg_left hvsq (by positivity)
    _ = _ := by field_simp

/-- The entire degree-weighted down-centre row is logarithmic, uniformly
in moving centres and their prime divisors. The reciprocal-prime response
gain cancels the increasing degree of the target at source divided by prime. -/
theorem eventually_powerRange_degreeWeightedDownCenters_le_logSq
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        (∑ q : PrimeStar.CanonicalDownIndex a,
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree
            (PrimeStar.canonicalDownTarget a q) : ℝ) *
            (exactPrincipalMoleculeSignedInteriorVector S X a
              (PrimeStar.canonicalDownTarget a q)) ^ 2) ≤
          C * Real.log (X : ℝ) ^ 2 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨10000 ^ 2 * (8 + 1 / Real.log 2) / Real.log 2, by positivity, ?_⟩
  filter_upwards [eventually_powerRange_signedDownCenter_abs_le S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 2] with X hresponse hscale hwindow hX
  intro a ha
  have haPos : 0 < (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hd := (hwindow a ha).2.1
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hmuOne : 1 ≤ moleculeStarEnergy S X a ^ 2 := by
    rw [moleculeStarEnergy_sq]
    exact_mod_cast hd
  have hpoint (q : PrimeStar.CanonicalDownIndex a) :
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree
        (PrimeStar.canonicalDownTarget a q) : ℝ) *
        (exactPrincipalMoleculeSignedInteriorVector S X a
          (PrimeStar.canonicalDownTarget a q)) ^ 2 ≤
        10000 ^ 2 * (8 + 1 / Real.log 2) * Real.log (X : ℝ) := by
    have hq : 1 ≤ (q : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors q.property).one_le
    have hqPos : 0 < (q : ℝ) := by linarith
    have hbPos : 0 < ((PrimeStar.canonicalDownTarget a q : PrimeStar.Vertex S X) : ℝ) := by
      exact_mod_cast PrimeStar.Vertex.coe_pos (PrimeStar.canonicalDownTarget a q)
    have hbq : ((PrimeStar.canonicalDownTarget a q : PrimeStar.Vertex S X) : ℝ) *
        (q : ℝ) = (a : ℝ) := by
      exact_mod_cast PrimeStar.canonicalDownTarget_mul_coe a q
    have hdiv : (X : ℝ) / ((PrimeStar.canonicalDownTarget a q : PrimeStar.Vertex S X) : ℝ) =
        (X : ℝ) * (q : ℝ) / (a : ℝ) := by
      apply (div_eq_div_iff hbPos.ne' haPos.ne').mpr
      nlinarith only [hbq]
    have hdegree := smallPrimeGraph_degree_le_div_add_log
      (Y := squareRootCutoff X) (PrimeStar.canonicalDownTarget a q)
    rw [hdiv] at hdegree
    exact (mul_le_mul_of_nonneg_right hdegree (sq_nonneg _)).trans
      (downWeighted_scalar haPos hq hmu hmuOne hlogTwo (hscale a ha).1 hlog (hresponse a ha q))
  have hcard : (Fintype.card (PrimeStar.CanonicalDownIndex a) : ℝ) ≤
      Real.log (X : ℝ) / Real.log 2 := by
    rw [Fintype.card_coe]
    exact (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos a)).trans
      (div_le_div_of_nonneg_right
        (Real.log_le_log haPos (by exact_mod_cast PrimeStar.Vertex.coe_le a)) hlogTwo.le)
  calc
    _ ≤ ∑ _q : PrimeStar.CanonicalDownIndex a,
        10000 ^ 2 * (8 + 1 / Real.log 2) * Real.log (X : ℝ) :=
      Finset.sum_le_sum (fun q _ ↦ hpoint q)
    _ = (Fintype.card (PrimeStar.CanonicalDownIndex a) : ℝ) *
        (10000 ^ 2 * (8 + 1 / Real.log 2) * Real.log (X : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Real.log (X : ℝ) / Real.log 2) *
        (10000 ^ 2 * (8 + 1 / Real.log 2) * Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- The literal up-star centre response, including a zero-degree target.
This is the centre counterpart of the existing constant-leaf formula. -/
theorem shiftedActualUpStarResolvent_apply_center
    {S : Finset ℕ} {X Y : ℕ} (target : PrimeStar.Vertex S X)
    (lambda mu c0 : ℝ) :
    shiftedActualUpStarResolvent S X Y target lambda mu c0 target =
      (lambda * c0 + (PrimeStar.largePrimeStarDegree S X Y target : ℝ) * (c0 / mu)) /
        (lambda ^ 2 - (PrimeStar.largePrimeStarDegree S X Y target : ℝ)) := by
  rw [shiftedActualUpStarResolvent, PrimeStar.largePrimeStarResolventOfVector,
    PrimeStar.largePrimeStarDataVector_center]
  have hsum : (∑ w ∈ PrimeStar.largePrimeLeaves S X Y target,
      PrimeStar.actualUpStarFirstExit S X Y target mu c0 w) =
      (PrimeStar.largePrimeStarDegree S X Y target : ℝ) * (c0 / mu) := by
    calc
      _ = ∑ _w ∈ PrimeStar.largePrimeLeaves S X Y target, c0 / mu := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [PrimeStar.actualUpStarFirstExit, PrimeStar.largePrimeStarDataVector_leaf _ _ hw]
      _ = _ := by simp [PrimeStar.largePrimeStarDegree]
  rw [hsum, PrimeStar.actualUpStarFirstExit, PrimeStar.largePrimeStarDataVector_center]

/-- Recombining both boundary modes gives the actual up-centre response.
The isolated-target branch is included; no target is discarded at the cutoff. -/
theorem exactPrincipalMoleculeSignedInteriorVector_apply_canonicalUpTarget
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a) :
    exactPrincipalMoleculeSignedInteriorVector S X a (PrimeStar.canonicalUpTarget hS a q) =
      (exactPrincipalMoleculeRoot S X a *
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 +
            exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) +
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) : ℝ) / moleculeStarEnergy S X a *
          (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1 -
            exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1))) /
        (exactPrincipalMoleculeRoot S X a ^ 2 -
          (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
            (PrimeStar.canonicalUpTarget hS a q) : ℝ)) := by
  let target := PrimeStar.canonicalUpTarget hS a q
  rcases PrimeStar.canonicalExitTarget_mem_lower_or_isolated hS
      (PrimeStar.sqrtCutoff_condition X) ha
      (Sum.inl q : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a)
      with hlower | hiso
  · have hmode (eps : ℝ) (heps : eps ^ 2 = 1) :
        exactBoundaryModeInteriorVector S X a eps target =
          shiftedActualUpStarResolvent S X (squareRootCutoff X) target
            (exactPrincipalMoleculeRoot S X a) (eps * moleculeStarEnergy S X a)
            (Real.sqrt 2)⁻¹ target := by
      rw [exactBoundaryModeInteriorVector,
        firstExitStarResolventVector_apply_of_mem_selectedStar
          (exactBoundaryModeInteriorSource S X a eps)
          (PrimeStar.sqrtCutoff_condition X) hlower
          (by simp [target, PrimeStar.largePrimeStarSupport]),
        PrimeStar.canonicalExitTarget_inl,
        restrict_exactBoundaryModeInteriorSource_eq_canonicalUpStar hS ha hd heps q,
        largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd]
      rfl
    rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hmode 1 (by norm_num), hmode (-1) (by norm_num),
      shiftedActualUpStarResolvent_apply_center, shiftedActualUpStarResolvent_apply_center]
    unfold exactPrincipalMoleculeBoundarySourceAmplitude
    dsimp only [target]
    simp only [div_eq_mul_inv, inv_neg, one_mul, neg_one_mul]
    ring
  · have hiso' : target ∈ PrimeStar.firstExitIsolatedVertices S X (squareRootCutoff X) a := hiso
    have hd0 : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) target = 0 :=
      PrimeStar.largePrimeStarDegree_eq_zero_iff.mpr
        (PrimeStar.mem_firstExitIsolatedVertices.mp hiso').2
    rw [exactPrincipalMoleculeSignedInteriorVector_apply_isolatedCanonicalUpTarget
      hS ha hd q hiso' hroot, hd0, Nat.cast_zero, zero_div, zero_mul, add_zero, sub_zero]
    field_simp

private theorem upCenter_scalar
    {mu lambda d alpha beta : ℝ}
    (hmu : 0 < mu) (hlambda : |lambda| ≤ 2 * mu)
    (hd : 0 ≤ d) (hdUpper : d ≤ mu ^ 2)
    (hgap : mu ^ 2 / 100 ≤ |lambda ^ 2 - d|)
    (ha : |alpha| ≤ 1) (hb : |beta| ≤ 1) :
    |(lambda * (alpha + beta) + d / mu * (alpha - beta)) /
      (lambda ^ 2 - d)| ≤ 600 / mu := by
  have hsum : |alpha + beta| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hdiff : |alpha - beta| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hdmu : d / mu ≤ mu := (div_le_iff₀ hmu).mpr (by nlinarith only [hdUpper])
  have hnumerator : |lambda * (alpha + beta) + d / mu * (alpha - beta)| ≤ 6 * mu := by
    calc
      _ ≤ |lambda| * |alpha + beta| + |d / mu| * |alpha - beta| := by
        simpa only [abs_mul] using abs_add_le (lambda * (alpha + beta)) (d / mu * (alpha - beta))
      _ ≤ (2 * mu) * 2 + mu * 2 := by
        apply add_le_add
        · exact mul_le_mul hlambda hsum (abs_nonneg _) (by positivity)
        · rw [abs_of_nonneg (div_nonneg hd hmu.le)]
          exact mul_le_mul hdmu hdiff (abs_nonneg _) hmu.le
      _ = _ := by ring
  have hgapPos : 0 < |lambda ^ 2 - d| := lt_of_lt_of_le (by positivity) hgap
  rw [abs_div]
  calc
    _ ≤ (6 * mu) / |lambda ^ 2 - d| := div_le_div_of_nonneg_right hnumerator hgapPos.le
    _ ≤ (6 * mu) / (mu ^ 2 / 100) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hgap
    _ = _ := by field_simp; ring

/-- Uniform up-centre coefficient bound on the power prefix. All denominator
and root margins come from the already proved actual response window. -/
theorem eventually_powerRange_signedUpCenter_abs_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
          |exactPrincipalMoleculeSignedInteriorVector S X a
            (PrimeStar.canonicalUpTarget hS a q)| ≤ 600 / moleculeStarEnergy S X a := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_responseWindow S hS htheta,
    eventually_powerRange_actualUpStarRatio_bounds S hS htheta]
    with X hwindow hresponse hratio
  intro a ha q
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  obtain ⟨hroot, hlambda, hden⟩ := hresponse a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hqData := Finset.mem_filter.mp q.property
  have hqMem : (q : ℕ) ∈ (Nat.primesLE (Nat.sqrt X)).filter (fun q ↦ q ∉ S) :=
    Finset.mem_filter.mpr ⟨hqData.1, hqData.2.1⟩
  have hr := (hratio a ha (q : ℕ) hqMem).2.1
  change PrimeStar.fixedCenterActualUpRatio S (a : ℕ) X (q : ℕ) ≤ 15 / 16 at hr
  rw [← PrimeStar.canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a haY q] at hr
  have hdegree : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalUpTarget hS a q) : ℝ) ≤ moleculeStarEnergy S X a ^ 2 := by
    rw [← moleculeStarEnergy_sq S X a] at hr
    have := (div_le_iff₀ (sq_pos_of_pos hmu)).mp hr
    nlinarith [sq_nonneg (moleculeStarEnergy S X a)]
  rw [exactPrincipalMoleculeSignedInteriorVector_apply_canonicalUpTarget hS haY hd hroot q]
  exact upCenter_scalar hmu hlambda (by positivity) hdegree (hden q)
    (abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd (by norm_num))
    (abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd (by norm_num))

/-- The whole actual up-centre weighted row is logarithmic. The reciprocal
target weight is summed before using the cutoff bound, avoiding a loss
proportional to the number of allowed small primes. -/
theorem eventually_powerRange_degreeWeightedUpCenters_le_logSq
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        (∑ q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a,
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree
            (PrimeStar.canonicalUpTarget hS a q) : ℝ) *
            (exactPrincipalMoleculeSignedInteriorVector S X a
              (PrimeStar.canonicalUpTarget hS a q)) ^ 2) ≤
          C * Real.log (X : ℝ) ^ 2 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨600 ^ 2 * (16 + 8 / Real.log 2), by positivity, ?_⟩
  filter_upwards [eventually_powerRange_signedUpCenter_abs_le S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 4]
    with X hresponse hscale hwindow hlogOne hX
  intro a ha
  let mu := moleculeStarEnergy S X a
  let Y := squareRootCutoff X
  let L := Real.log (X : ℝ)
  have haPos : 0 < (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hlog : 0 < L := by dsimp only [L]; linarith
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have haYX : (a : ℕ) * Y ≤ X :=
    (Nat.mul_le_mul_right Y haY).trans (Nat.sqrt_le X)
  have hXbudget : (X : ℝ) / (a : ℝ) ≤ 8 * L * mu ^ 2 := by
    apply (div_le_iff₀ haPos).mpr
    have h := (div_le_iff₀ (by positivity : 0 < 8 * (a : ℝ) * L)).mp (hscale a ha).1
    nlinarith only [h]
  have hYbudget : (Y : ℝ) ≤ 8 * L * mu ^ 2 := by
    have hay : (a : ℝ) * (Y : ℝ) ≤ (X : ℝ) := by exact_mod_cast haYX
    have hx := (div_le_iff₀ haPos).mp hXbudget
    nlinarith only [hay, hx, haPos]
  have hYPos : 0 < (Y : ℝ) := by
    exact_mod_cast (show 0 < Y from Nat.sqrt_pos.mpr (by omega))
  have hrecip : (∑ q : PrimeStar.CanonicalUpIndex S X Y a, (q : ℝ)⁻¹) ≤ 2 * L := by
    rw [Finset.sum_coe_sort (PrimeStar.canonicalUpPrimeLabels S X Y a)
      (fun q : ℕ ↦ (q : ℝ)⁻¹), PrimeStar.canonicalUpPrimeLabels_eq_allowedPrimeSet haYX]
    have hlogY : Real.log (Y : ℝ) ≤ L :=
      Real.log_le_log hYPos (by exact_mod_cast Nat.sqrt_le_self X)
    exact (sum_allowedPrime_reciprocal_le_one_add_log S Y).trans (by dsimp only [L] at *; linarith)
  have hcard : (Fintype.card (PrimeStar.CanonicalUpIndex S X Y a) : ℝ) ≤ (Y : ℝ) := by
    have hsub : PrimeStar.canonicalUpPrimeLabels S X Y a ⊆ Finset.Icc 1 Y := by
      intro q hq
      have hp := Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1
      exact Finset.mem_Icc.mpr ⟨hp.2.one_le, hp.1⟩
    rw [Fintype.card_coe]
    exact_mod_cast (show (PrimeStar.canonicalUpPrimeLabels S X Y a).card ≤ Y by
      simpa using Finset.card_le_card hsub)
  have hdegreeSum :
      (∑ q : PrimeStar.CanonicalUpIndex S X Y a,
        ((PrimeStar.smallPrimeGraph S X Y).degree (PrimeStar.canonicalUpTarget hS a q) : ℝ)) ≤
        (16 + 8 / Real.log 2) * L ^ 2 * mu ^ 2 := by
    calc
      _ ≤ ∑ q : PrimeStar.CanonicalUpIndex S X Y a,
          ((X : ℝ) / (a : ℝ) * (q : ℝ)⁻¹ + L / Real.log 2) := by
        apply Finset.sum_le_sum
        intro q _
        have h := smallPrimeGraph_degree_le_div_add_log (Y := Y) (PrimeStar.canonicalUpTarget hS a q)
        calc
          _ ≤ (X : ℝ) / ((PrimeStar.canonicalUpTarget hS a q : PrimeStar.Vertex S X) : ℝ) +
              L / Real.log 2 := h
          _ = _ := by
            simp only [PrimeStar.canonicalUpTarget_coe, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
            ring
      _ = (X : ℝ) / (a : ℝ) * (∑ q : PrimeStar.CanonicalUpIndex S X Y a, (q : ℝ)⁻¹) +
          (Fintype.card (PrimeStar.CanonicalUpIndex S X Y a) : ℝ) * (L / Real.log 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (X : ℝ) / (a : ℝ) * (2 * L) + (Y : ℝ) * (L / Real.log 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hrecip (by positivity))
          (mul_le_mul_of_nonneg_right hcard (by positivity))
      _ ≤ (8 * L * mu ^ 2) * (2 * L) + (8 * L * mu ^ 2) * (L / Real.log 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hXbudget (by positivity))
          (mul_le_mul_of_nonneg_right hYbudget (by positivity))
      _ = _ := by ring
  calc
    _ ≤ ∑ q : PrimeStar.CanonicalUpIndex S X Y a,
        ((PrimeStar.smallPrimeGraph S X Y).degree (PrimeStar.canonicalUpTarget hS a q) : ℝ) *
          (600 / mu) ^ 2 := by
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hresponse a ha q)
    _ = (∑ q : PrimeStar.CanonicalUpIndex S X Y a,
        ((PrimeStar.smallPrimeGraph S X Y).degree (PrimeStar.canonicalUpTarget hS a q) : ℝ)) *
          (600 / mu) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ((16 + 8 / Real.log 2) * L ^ 2 * mu ^ 2) * (600 / mu) ^ 2 :=
      mul_le_mul_of_nonneg_right hdegreeSum (sq_nonneg _)
    _ = _ := by dsimp only [L]; field_simp

/-- The actual signed response on an up-star leaf is the exact two-mode local coefficient. -/
theorem exactPrincipalMoleculeSignedInteriorVector_apply_canonicalUpLeaf
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (q : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a)
    {v : PrimeStar.Vertex S X}
    (hv : v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
      (PrimeStar.canonicalUpTarget hS a q))
    (hroot : exactPrincipalMoleculeRoot S X a ≠ 0)
    (hden : exactPrincipalMoleculeRoot S X a ^ 2 ≠
      (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) : ℝ)) :
    exactPrincipalMoleculeSignedInteriorVector S X a v =
      shiftedCanonicalTwoModeUpLeafCoefficient hS a
        (exactPrincipalMoleculeRoot S X a) (moleculeStarEnergy S X a)
        (exactPrincipalMoleculeBoundarySourceAmplitude S X a 1)
        (exactPrincipalMoleculeBoundarySourceAmplitude S X a (-1)) q := by
  have hlow : PrimeStar.canonicalUpTarget hS a q ∈
      PrimeStar.firstExitLowerCenters S X (squareRootCutoff X) a := by
    rcases PrimeStar.canonicalExitTarget_mem_lower_or_isolated hS
      (PrimeStar.sqrtCutoff_condition X) ha
      (Sum.inl q : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a) with h | h
    · exact h
    · exact False.elim ((PrimeStar.mem_firstExitIsolatedVertices.mp h).2 v
        (PrimeStar.mem_largePrimeLeaves.mp hv))
  have hmu : moleculeStarEnergy S X a ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have hmode (eps : ℝ) (heps : eps ^ 2 = 1) :
      exactBoundaryModeInteriorVector S X a eps v =
        shiftedCanonicalUpLeafCoefficient hS a (exactPrincipalMoleculeRoot S X a)
          (eps * moleculeStarEnergy S X a) (Real.sqrt 2)⁻¹ q := by
    have heps0 : eps ≠ 0 := by intro h; simp [h] at heps
    rw [exactBoundaryModeInteriorVector,
      firstExitStarResolventVector_apply_of_mem_selectedStar
        (exactBoundaryModeInteriorSource S X a eps)
        (PrimeStar.sqrtCutoff_condition X) hlow (Finset.mem_insert_of_mem hv),
      restrict_exactBoundaryModeInteriorSource_eq_canonicalUpStar hS ha hd heps q,
      largePrimeNormalizedStarMode_center_eq_inv_sqrt_two heps hd]
    change shiftedActualUpStarResolvent S X (squareRootCutoff X)
        (PrimeStar.canonicalUpTarget hS a q) (exactPrincipalMoleculeRoot S X a)
        (eps * moleculeStarEnergy S X a) (Real.sqrt 2)⁻¹ v = _
    rw [shiftedActualUpStarResolvent_apply_leaf hv hroot (mul_ne_zero heps0 hmu) hden]
    rfl
  rw [exactPrincipalMoleculeSignedInteriorVector_eq_modeSynthesis hd]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hmode 1 (by norm_num), hmode (-1) (by norm_num)]
  unfold shiftedCanonicalTwoModeUpLeafCoefficient shiftedCanonicalUpLeafCoefficient
    exactPrincipalMoleculeBoundarySourceAmplitude
  simp only [div_eq_mul_inv, one_mul, neg_one_mul]
  ring

/-- Every actual canonical leaf, including unselected down-star leaves, has signed response
at most 2000/mu^2. The power-window producers discharge the denominator margins. -/
theorem eventually_powerRange_signedCanonicalLeaf_abs_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        ∀ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
          ∀ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalExitTarget hS a i),
            |exactPrincipalMoleculeSignedInteriorVector S X a v| ≤
              2000 / moleculeStarEnergy S X a ^ 2 := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_responseWindow S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_downResponseWindow S hS htheta]
    with X hwindow hup hdown
  intro a ha i v hv
  obtain ⟨haY, hd, hshift⟩ := hwindow a ha
  obtain ⟨hroot, hlambda, hgapUp⟩ := hup a ha
  let mu := moleculeStarEnergy S X a
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  rcases i with q | q
  · have hden : exactPrincipalMoleculeRoot S X a ^ 2 ≠
        (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
          (PrimeStar.canonicalUpTarget hS a q) : ℝ) := by
      intro heq
      have h := hgapUp q
      rw [heq, sub_self, abs_zero] at h
      have hmuSq := sq_pos_of_pos hmu
      dsimp only [mu] at hmuSq
      linarith
    rw [exactPrincipalMoleculeSignedInteriorVector_apply_canonicalUpLeaf
      hS haY hd q hv hroot hden]
    exact (abs_shiftedCanonicalTwoModeUpLeafCoefficient_le hS a _ _ _ _ q hmu
      (abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd (by norm_num))
      (abs_exactPrincipalMoleculeBoundarySourceAmplitude_le_one hd (by norm_num))
      hlambda (hgapUp q)).trans (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _))
  · let z := exactPrincipalMoleculeRoot S X a / mu
    let s := (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
      (PrimeStar.canonicalDownTarget a q) : ℝ) / mu ^ 2
    have hrootEq : exactPrincipalMoleculeRoot S X a = z * mu := by
      dsimp [z]; rw [div_mul_cancel₀ _ hmu.ne']
    have hdegree : (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X)
        (PrimeStar.canonicalDownTarget a q) : ℝ) = s * mu ^ 2 := by
      dsimp [s]; rw [div_mul_cancel₀ _ (sq_pos_of_pos hmu).ne']
    have hzLower : (1 : ℝ) / 2 ≤ |z| := by
      apply (le_abs_self z).trans'
      apply (le_div_iff₀ hmu).mpr
      have := (abs_le.mp hshift).1
      dsimp only [mu]
      linarith
    have hzUpper : |z| ≤ 2 := by
      dsimp [z]
      rw [abs_div, abs_of_pos hmu]
      exact (div_le_iff₀ hmu).mpr hlambda
    have hgap : (1 : ℝ) / 100 ≤ |z ^ 2 - s| := by
      have h := hdown a ha q
      rw [hrootEq, hdegree, mul_pow, ← sub_mul, abs_mul,
        abs_of_nonneg (sq_nonneg mu)] at h
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hmu)).mp
      dsimp only [mu] at h ⊢
      nlinarith only [h]
    have h := abs_exactPrincipalMoleculeSignedInteriorVector_apply_canonicalDownLeaf_le
      hS haY hd q hv hrootEq hdegree (delta := 1 / 100)
      (by norm_num) (by norm_num) hzLower hzUpper hgap
    convert h using 1; ring

/-- Summing small-prime degrees on one lower star retains the reciprocal leaf multiplier.
The harmonic majorant avoids a minimum-prime times leaf-count loss. -/
theorem sum_smallPrimeDegree_largePrimeLeaves_le
    {S : Finset ℕ} {X Y : ℕ} (c : PrimeStar.Vertex S X)
    (hc : (c : ℕ) ≤ Y) (hL : 1 ≤ Real.log (X : ℝ)) :
    (∑ v ∈ PrimeStar.largePrimeLeaves S X Y c,
      ((PrimeStar.smallPrimeGraph S X Y).degree v : ℝ)) ≤
        (2 + 1 / Real.log 2) * ((X : ℝ) / (c : ℝ)) * Real.log (X : ℝ) := by
  let F := PrimeStar.largePrimeLeaves S X Y c
  let N := X / (c : ℕ)
  let g := fun v : PrimeStar.Vertex S X ↦ (v : ℕ) / (c : ℕ)
  let f := fun p : ℕ ↦ (X : ℝ) / (c : ℝ) * (p : ℝ)⁻¹ + Real.log (X : ℝ) / Real.log 2
  have hcPos : 0 < (c : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos c
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 < Real.log (X : ℝ) := by linarith
  have hdata (v : PrimeStar.Vertex S X) (hv : v ∈ F) :
      0 < g v ∧ (c : ℕ) * g v = (v : ℕ) ∧ g v ≤ N := by
    obtain ⟨p, hp, _, _, hcp⟩ := (PrimeStar.mem_largePrimeLeaves_iff_child hc).mp hv
    have hgp : g v = p := by
      dsimp only [g]
      rw [← hcp, Nat.mul_div_cancel_left _ (PrimeStar.Vertex.coe_pos c)]
    rw [hgp]
    refine ⟨hp.pos, hcp, ?_⟩
    apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos c)).mpr
    rw [Nat.mul_comm, hcp]
    exact PrimeStar.Vertex.coe_le v
  have hsub : F.image g ⊆ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_Icc.mpr ⟨(hdata v hv).1, (hdata v hv).2.2⟩
  have hinj : ∀ v ∈ F, ∀ w ∈ F, g v = g w → v = w := by
    intro v hv w hw h
    apply Subtype.ext
    apply Fin.ext
    rw [← (hdata v hv).2.1, ← (hdata w hw).2.1, h]
  have hpoint (v : PrimeStar.Vertex S X) (hv : v ∈ F) :
      ((PrimeStar.smallPrimeGraph S X Y).degree v : ℝ) ≤ f (g v) := by
    have hcv : (c : ℝ) * (g v : ℝ) = (v : ℝ) := by exact_mod_cast (hdata v hv).2.1
    calc
      _ ≤ (X : ℝ) / (v : ℝ) + Real.log (X : ℝ) / Real.log 2 :=
        smallPrimeGraph_degree_le_div_add_log (Y := Y) v
      _ = _ := by rw [← hcv]; dsimp [f]; simp only [div_mul_eq_div_mul_one_div, one_div]
  have hNpos : 0 < (N : ℝ) := by
    have hN : 1 ≤ N := (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos c)).mpr
      (by simp [PrimeStar.Vertex.coe_le c])
    exact_mod_cast (show 0 < N by omega)
  have hrecip : (∑ p ∈ Finset.Icc 1 N, (p : ℝ)⁻¹) ≤ 2 * Real.log (X : ℝ) := by
    have heq : (∑ p ∈ Finset.Icc 1 N, (p : ℝ)⁻¹) = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [heq]
    have hlogN : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hNpos (by exact_mod_cast Nat.div_le_self X (c : ℕ))
    exact (harmonic_le_one_add_log N).trans (by linarith)
  calc
    _ ≤ ∑ v ∈ F, f (g v) := Finset.sum_le_sum (fun v hv ↦ hpoint v hv)
    _ = ∑ p ∈ F.image g, f p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ Finset.Icc 1 N, f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by dsimp [f]; positivity)
    _ = (X : ℝ) / (c : ℝ) * (∑ p ∈ Finset.Icc 1 N, (p : ℝ)⁻¹) +
        (N : ℝ) * (Real.log (X : ℝ) / Real.log 2) := by
      dsimp only [f]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ (X : ℝ) / (c : ℝ) * (2 * Real.log (X : ℝ)) +
        ((X : ℝ) / (c : ℝ)) * (Real.log (X : ℝ) / Real.log 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hrecip (by positivity))
        (mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity))
    _ = _ := by ring

/-- The leaf-degree budget applies to every canonical target; isolated up-targets contribute
an empty leaf sum. -/
theorem sum_smallPrimeDegree_canonicalLeaves_le
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hL : 1 ≤ Real.log (X : ℝ))
    (i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a) :
    (∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
        (PrimeStar.canonicalExitTarget hS a i),
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ)) ≤
        (2 + 1 / Real.log 2) *
          ((X : ℝ) / ((PrimeStar.canonicalExitTarget hS a i : PrimeStar.Vertex S X) : ℝ)) *
          Real.log (X : ℝ) := by
  rcases PrimeStar.canonicalExitTarget_le_or_isolated hS
      (PrimeStar.sqrtCutoff_condition X) ha i with h | h
  · exact sum_smallPrimeDegree_largePrimeLeaves_le _ h hL
  · have hempty : PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
        (PrimeStar.canonicalExitTarget hS a i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact h v (PrimeStar.mem_largePrimeLeaves.mp hv)
    rw [hempty, Finset.sum_empty]
    have hlog : 0 < Real.log (X : ℝ) := by linarith
    positivity

/-- Canonical target reciprocals have logarithmic total mass: the up-primes use a harmonic
sum, and the down-targets use the number of distinct prime divisors. -/
theorem sum_canonicalExitTarget_reciprocal_le_log
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hL : 1 ≤ Real.log (X : ℝ)) :
    (∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
      (((PrimeStar.canonicalExitTarget hS a i : PrimeStar.Vertex S X) : ℝ))⁻¹) ≤
        (2 + 1 / Real.log 2) * Real.log (X : ℝ) := by
  let Y := squareRootCutoff X
  let L := Real.log (X : ℝ)
  have haPos : 0 < (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have haOne : 1 ≤ (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hlog : 0 < L := by dsimp [L]; linarith
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have haYX : (a : ℕ) * Y ≤ X :=
    (Nat.mul_le_mul_right Y ha).trans (Nat.sqrt_le X)
  have hYPos : 0 < (Y : ℝ) := by
    have : 0 < Y := lt_of_lt_of_le (PrimeStar.Vertex.coe_pos a) ha
    exact_mod_cast this
  have hrecip : (∑ q : PrimeStar.CanonicalUpIndex S X Y a, (q : ℝ)⁻¹) ≤ 2 * L := by
    rw [Finset.sum_coe_sort (PrimeStar.canonicalUpPrimeLabels S X Y a)
      (fun q : ℕ ↦ (q : ℝ)⁻¹), PrimeStar.canonicalUpPrimeLabels_eq_allowedPrimeSet haYX]
    have hlogY : Real.log (Y : ℝ) ≤ L :=
      Real.log_le_log hYPos (by exact_mod_cast Nat.sqrt_le_self X)
    exact (sum_allowedPrime_reciprocal_le_one_add_log S Y).trans (by dsimp [L] at *; linarith)
  have hup : (∑ q : PrimeStar.CanonicalUpIndex S X Y a,
      (((PrimeStar.canonicalUpTarget hS a q : PrimeStar.Vertex S X) : ℝ))⁻¹) ≤ 2 * L := by
    calc
      _ = (a : ℝ)⁻¹ * (∑ q : PrimeStar.CanonicalUpIndex S X Y a, (q : ℝ)⁻¹) := by
        simp only [PrimeStar.canonicalUpTarget_coe, Nat.cast_mul, mul_inv_rev]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ (a : ℝ)⁻¹ * (2 * L) := mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ ≤ 2 * L := by
        have : (a : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ haPos).mpr haOne
        nlinarith
  have hdown : (∑ q : PrimeStar.CanonicalDownIndex a,
      (((PrimeStar.canonicalDownTarget a q : PrimeStar.Vertex S X) : ℝ))⁻¹) ≤ L / Real.log 2 := by
    calc
      _ ≤ ∑ _q : PrimeStar.CanonicalDownIndex a, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q _
        have hc : 0 < ((PrimeStar.canonicalDownTarget a q : PrimeStar.Vertex S X) : ℝ) := by
          exact_mod_cast PrimeStar.Vertex.coe_pos (PrimeStar.canonicalDownTarget a q)
        exact (inv_le_one₀ hc).mpr (by
          exact_mod_cast (PrimeStar.Vertex.coe_pos (PrimeStar.canonicalDownTarget a q)))
      _ = ((a : ℕ).primeFactors.card : ℝ) := by simp [PrimeStar.CanonicalDownIndex]
      _ ≤ Real.log (a : ℝ) / Real.log 2 := primeFactors_card_le_log_div_log_two
          (PrimeStar.Vertex.coe_pos a)
      _ ≤ L / Real.log 2 := div_le_div_of_nonneg_right
          (Real.log_le_log haPos (by exact_mod_cast PrimeStar.Vertex.coe_le a)) hlogTwo.le
  change (∑ i : PrimeStar.CanonicalUpIndex S X Y a ⊕ PrimeStar.CanonicalDownIndex a,
    (((PrimeStar.canonicalExitTarget hS a i : PrimeStar.Vertex S X) : ℝ))⁻¹) ≤ _
  rw [Fintype.sum_sum_type]
  calc
    _ ≤ 2 * L + L / Real.log 2 := add_le_add hup hdown
    _ = _ := by dsimp [L]; ring

/-- The complete degree-weighted signed leaf response is O(log^4 X), uniformly over the
power window. No local response or degree estimate remains as a premise. -/
theorem eventually_powerRange_degreeWeightedCanonicalLeaves_le_logFourth
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        (∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
          ∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalExitTarget hS a i),
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ) *
              (exactPrincipalMoleculeSignedInteriorVector S X a v) ^ 2) ≤
          C * Real.log (X : ℝ) ^ 4 := by
  let C0 : ℝ := 2 + 1 / Real.log 2
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨2000 ^ 2 * 64 * C0 ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_powerRange_signedCanonicalLeaf_abs_le S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    hlogTop.eventually_ge_atTop 1] with X hresponse hscale hwindow hL
  intro a ha
  let mu := moleculeStarEnergy S X a
  let L := Real.log (X : ℝ)
  let I := PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have haPos : 0 < (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have hX : 0 < (X : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (PrimeStar.Vertex.coe_pos a) (PrimeStar.Vertex.coe_le a)
  have hlog : 0 < L := by dsimp [L]; linarith
  have haSq : (a : ℝ) ^ 2 ≤ (X : ℝ) := by
    exact_mod_cast (show (a : ℕ) ^ 2 ≤ X from
      (Nat.pow_le_pow_left haY 2).trans (by simpa [pow_two] using Nat.sqrt_le X))
  have hrecip := sum_canonicalExitTarget_reciprocal_le_log hS haY hL
  have hdegree : (∑ i : I,
      ∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
        (PrimeStar.canonicalExitTarget hS a i),
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ)) ≤
      C0 ^ 2 * (X : ℝ) * L ^ 2 := by
    calc
      _ ≤ ∑ i : I, C0 * ((X : ℝ) /
          ((PrimeStar.canonicalExitTarget hS a i : PrimeStar.Vertex S X) : ℝ)) * L :=
        Finset.sum_le_sum (fun i _ ↦ sum_smallPrimeDegree_canonicalLeaves_le hS haY hL i)
      _ = (C0 * (X : ℝ) * L) * (∑ i : I,
          (((PrimeStar.canonicalExitTarget hS a i : PrimeStar.Vertex S X) : ℝ))⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [L]
        rw [div_eq_mul_inv]
        ring
      _ ≤ (C0 * (X : ℝ) * L) * (C0 * L) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = _ := by ring
  have hscaleSq : (X : ℝ) ≤ 64 * L ^ 2 * mu ^ 4 := by
    have h := (div_le_iff₀ (by positivity : 0 < 8 * (a : ℝ) * L)).mp (hscale a ha).1
    have hs := (sq_le_sq₀ hX.le (by positivity)).mpr h
    have hm := mul_le_mul_of_nonneg_right haSq (by positivity : 0 ≤ 64 * L ^ 2 * mu ^ 4)
    have hxprod : (X : ℝ) * (X : ℝ) ≤ (64 * L ^ 2 * mu ^ 4) * (X : ℝ) := by
      dsimp only [mu, L] at *
      nlinarith only [hs, hm]
    exact (mul_le_mul_iff_left₀ hX).mp hxprod
  calc
    _ ≤ ∑ i : I, ∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalExitTarget hS a i),
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ) *
            (2000 / mu ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
        (hresponse a ha i v hv)
    _ = (∑ i : I, ∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalExitTarget hS a i),
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ)) *
            (2000 / mu ^ 2) ^ 2 := by simp only [Finset.sum_mul]
    _ ≤ (C0 ^ 2 * (X : ℝ) * L ^ 2) * (2000 / mu ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hdegree (sq_nonneg _)
    _ ≤ (C0 ^ 2 * (64 * L ^ 2 * mu ^ 4) * L ^ 2) * (2000 / mu ^ 2) ^ 2 := by
      gcongr
    _ = _ := by dsimp only [L]; field_simp

/-- Every coordinate of the full first-exit compression lies in a canonical arithmetic star,
not merely the coordinates of the first-exit source. -/
theorem exists_canonicalExitIndex_of_mem_compression
    {S : Finset ℕ} {X Y : ℕ} {a v : PrimeStar.Vertex S X}
    (hS : ∀ p ∈ S, p.Prime) (hcut : X < (Y + 1) * (Y + 1))
    (ha : (a : ℕ) ≤ Y) (hd : 0 < PrimeStar.largePrimeStarDegree S X Y a)
    (hv : v ∈ PrimeStar.firstExitCompressionSupport S X Y a) :
    ∃ i : PrimeStar.CanonicalExitIndex S X Y a,
      v ∈ PrimeStar.largePrimeStarSupport S X Y (PrimeStar.canonicalExitTarget hS a i) := by
  rcases Finset.mem_union.mp hv with hvStars | hvIso
  · obtain ⟨k, hk, hvk⟩ := PrimeStar.mem_largePrimeStarUnionSupport.mp hvStars
    obtain ⟨hkY, w, hwExit, hwNoniso, hwk⟩ := PrimeStar.mem_firstExitLowerCenters.mp hk
    obtain ⟨i, hwi⟩ := PrimeStar.exists_canonicalExitIndex_of_mem_smallPrimeFirstExitSupport
      hS hcut ha hd hwExit
    refine ⟨i, ?_⟩
    have htarget : k = PrimeStar.canonicalExitTarget hS a i := by
      rcases PrimeStar.canonicalExitTarget_le_or_isolated hS hcut ha i with hiY | hiIso
      · by_contra hne
        exact (Finset.disjoint_left.mp
          (PrimeStar.disjoint_largePrimeStarSupport hcut hkY hiY hne)) hwk hwi
      · rcases PrimeStar.mem_largePrimeStarSupport.mp hwi with heq | hadj
        · exact False.elim (hwNoniso (heq ▸ hiIso))
        · exact False.elim (hiIso _ hadj)
    simpa [← htarget] using hvk
  · exact PrimeStar.exists_canonicalExitIndex_of_mem_smallPrimeFirstExitSupport
      hS hcut ha hd (PrimeStar.mem_firstExitIsolatedVertices.mp hvIso).1

/-- The actual signed weighted response is bounded by the canonical centre and leaf rows.
Nonnegative overcounting suffices; no arbitrary support certificate is assumed. -/
theorem signedInterior_degreeWeighted_le_canonicalRows
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    (∑ v : PrimeStar.Vertex S X,
      ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ) *
        (exactPrincipalMoleculeSignedInteriorVector S X a v) ^ 2) ≤
      (∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree
          (PrimeStar.canonicalExitTarget hS a i) : ℝ) *
          (exactPrincipalMoleculeSignedInteriorVector S X a
            (PrimeStar.canonicalExitTarget hS a i)) ^ 2) +
      (∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
        ∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
          (PrimeStar.canonicalExitTarget hS a i),
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ) *
            (exactPrincipalMoleculeSignedInteriorVector S X a v) ^ 2) := by
  let I := PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a
  let F := fun i : I ↦ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
    (PrimeStar.canonicalExitTarget hS a i)
  let f := fun v : PrimeStar.Vertex S X ↦
    ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ) *
      (exactPrincipalMoleculeSignedInteriorVector S X a v) ^ 2
  have hf : ∀ v, 0 ≤ f v := fun _ ↦ by dsimp [f]; positivity
  have hpoint (v : PrimeStar.Vertex S X) : f v ≤ ∑ i : I, if v ∈ F i then f v else 0 := by
    by_cases hzero : exactPrincipalMoleculeSignedInteriorVector S X a v = 0
    · simp [f, hzero]
    · have hv : v ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a := by
        by_contra hnot
        exact hzero (PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem
          (exactPrincipalMoleculeSignedInteriorSource S X a) hnot)
      obtain ⟨i, hi⟩ := exists_canonicalExitIndex_of_mem_compression
        hS (PrimeStar.sqrtCutoff_condition X) ha hd hv
      change v ∈ F i at hi
      have h := Finset.single_le_sum
        (s := Finset.univ) (f := fun i : I ↦ if v ∈ F i then f v else 0)
        (fun j _ ↦ by split_ifs <;> positivity) (Finset.mem_univ i)
      simpa only [if_pos hi] using h
  calc
    _ ≤ ∑ v : PrimeStar.Vertex S X, ∑ i : I, if v ∈ F i then f v else 0 :=
      Finset.sum_le_sum (fun v _ ↦ hpoint v)
    _ = ∑ i : I, ∑ v ∈ F i, f v := by
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      have heq (i : I) : (∑ v ∈ F i, f v) =
          f (PrimeStar.canonicalExitTarget hS a i) +
          ∑ v ∈ PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalExitTarget hS a i), f v := by
        change (∑ v ∈ insert (PrimeStar.canonicalExitTarget hS a i)
          (PrimeStar.largePrimeLeaves S X (squareRootCutoff X)
            (PrimeStar.canonicalExitTarget hS a i)), f v) = _
        apply Finset.sum_insert
        intro hmem
        exact (PrimeStar.largePrimeGraph S X (squareRootCutoff X)).loopless.irrefl
          (PrimeStar.canonicalExitTarget hS a i) (PrimeStar.mem_largePrimeLeaves.mp hmem)
      simp_rw [heq]
      rw [Finset.sum_add_distrib]

/-- All signed response rows are assembled on the actual graph. The centre rows cost log^2 X
and the complete leaf row costs log^4 X. -/
theorem eventually_powerRange_signedDegreeWeighted_le_logFourth
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        (∑ v : PrimeStar.Vertex S X,
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree v : ℝ) *
            (exactPrincipalMoleculeSignedInteriorVector S X a v) ^ 2) ≤
          C * Real.log (X : ℝ) ^ 4 := by
  obtain ⟨Cu, hCu, hup⟩ := eventually_powerRange_degreeWeightedUpCenters_le_logSq S hS htheta
  obtain ⟨Cd, hCd, hdown⟩ := eventually_powerRange_degreeWeightedDownCenters_le_logSq S hS htheta
  obtain ⟨Cl, hCl, hleaf⟩ :=
    eventually_powerRange_degreeWeightedCanonicalLeaves_le_logFourth S hS htheta
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨Cu + Cd + Cl, by positivity, ?_⟩
  filter_upwards [hup, hdown, hleaf,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    hlogTop.eventually_ge_atTop 1] with X hu hd hl hw hL
  intro a ha
  obtain ⟨haY, hda, _⟩ := hw a ha
  have hcentres :
      (∑ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree
          (PrimeStar.canonicalExitTarget hS a i) : ℝ) *
          (exactPrincipalMoleculeSignedInteriorVector S X a
            (PrimeStar.canonicalExitTarget hS a i)) ^ 2) ≤
          (Cu + Cd) * Real.log (X : ℝ) ^ 2 := by
    rw [Fintype.sum_sum_type]
    have h := add_le_add (hu a ha) (hd a ha)
    convert h using 1 <;> first | rfl | ring
  have hpow : Real.log (X : ℝ) ^ 2 ≤ Real.log (X : ℝ) ^ 4 :=
    pow_le_pow_right₀ hL (by omega)
  calc
    _ ≤ _ := signedInterior_degreeWeighted_le_canonicalRows hS haY hda
    _ ≤ (Cu + Cd) * Real.log (X : ℝ) ^ 2 + Cl * Real.log (X : ℝ) ^ 4 :=
      add_le_add hcentres (hl a ha)
    _ ≤ (Cu + Cd) * Real.log (X : ℝ) ^ 4 + Cl * Real.log (X : ℝ) ^ 4 := by
      gcongr
    _ = _ := by ring

/-- R4b one-source continuation: the actual full-star molecule residual has squared norm
O(log^5 X), uniformly for moving centres below every fixed sub-square-root power. This
is not the collective residual operator bound. -/
theorem eventually_powerRange_exactPrincipalMoleculeResidual_sq_le_logFifth
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        ‖exactPrincipalMoleculeResidual S X a‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 5 := by
  obtain ⟨Cr, hCr, hr⟩ :=
    eventually_powerRange_residual_sq_le_signedWeighted_add_logFourth S hS htheta
  obtain ⟨Cs, hCs, hs⟩ := eventually_powerRange_signedDegreeWeighted_le_logFourth S hS htheta
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨4 * Cs / Real.log 2 + Cr, by positivity, ?_⟩
  filter_upwards [hr, hs, hlogTop.eventually_ge_atTop 1] with X hrX hsX hL
  intro a ha
  have hpow : Real.log (X : ℝ) ^ 4 ≤ Real.log (X : ℝ) ^ 5 :=
    pow_le_pow_right₀ hL (by omega)
  calc
    _ ≤ _ := hrX a ha
    _ ≤ (4 * Real.log (X : ℝ) / Real.log 2) * (Cs * Real.log (X : ℝ) ^ 4) +
        Cr * Real.log (X : ℝ) ^ 4 := by
      gcongr
      exact hsX a ha
    _ ≤ (4 * Real.log (X : ℝ) / Real.log 2) * (Cs * Real.log (X : ℝ) ^ 4) +
        Cr * Real.log (X : ℝ) ^ 5 := by gcongr
    _ = _ := by ring

end SourceContinuation

noncomputable section CollectiveResidual

open Filter
open scoped Classical InnerProductSpace Matrix Matrix.Norms.L2Operator

/-- The pinned real Schur bound controls the actual complex small-prime action. This
deliberately coarser square-root estimate is sufficient for the discarded-tail consumer. -/
theorem eventually_oneExitSmallPrime_apply_sq_le_sqrt (S : Finset ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
      ‖Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) x‖ ^ 2 ≤
        (16 * PrimeStar.sqrtCutoffResidualConstant ^ 2) * Real.sqrt (X : ℝ) * ‖x‖ ^ 2 := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [PrimeStar.eventually_sqrtCutoff_smallPrimeGraph_l2_opNorm_le_tuned,
    PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
    hlogTop.eventually_ge_atTop 1] with X hreal hscale hL
  intro x
  let eta := PrimeStar.sqrtCutoffResidualScale X
  have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
    (PrimeStar.tunedSchurScale_nonneg _)
  have hop : matrixL2OperatorNorm (oneExitSmallPrimeMatrix S X) ≤ 2 * eta :=
    oneExitSmallPrimeMatrix_l2OperatorNorm_le_two_mul_real S X heta (by
      simpa [eta, PrimeStar.sqrtCutoffResidualScale, PrimeStar.sqrtCutoffResidualConstant]
        using hreal S)
  have happly : ‖Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) x‖ ≤ 2 * eta * ‖x‖ := by
    have h := (oneExitSmallPrimeMatrix S X).l2_opNorm_mulVec x
    exact h.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
  have hetaSq : eta ^ 2 ≤ 4 * PrimeStar.sqrtCutoffResidualConstant ^ 2 * Real.sqrt (X : ℝ) := by
    apply hscale.trans
    gcongr
    exact div_le_self (Real.sqrt_nonneg _) hL
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr happly
  calc
    _ ≤ (2 * eta * ‖x‖) ^ 2 := hs
    _ = 4 * eta ^ 2 * ‖x‖ ^ 2 := by ring
    _ ≤ 4 * (4 * PrimeStar.sqrtCutoffResidualConstant ^ 2 * Real.sqrt (X : ℝ)) * ‖x‖ ^ 2 := by
      gcongr
    _ = _ := by ring

/-- Adjacency acting on the full phase-fixed discarded molecule costs O(log^3 X). The proof
uses the actual forest-zero identity, so the action is H rather than the full adjacency
norm. -/
theorem eventually_powerRange_adjacency_discardedFullMolecule_sq_le_logCube
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
          (Matrix.toEuclideanLin (oneExitComplementProjection S X)
            (phasedFullStarMolecule S X a))‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 3 := by
  obtain ⟨Ct, hCt, htail⟩ := eventually_powerRange_discardedFullMolecule_sq_le_scale S hS htheta
  let Ch := 16 * PrimeStar.sqrtCutoffResidualConstant ^ 2
  have hCh : 0 < Ch := mul_pos (by norm_num)
    (sq_pos_of_pos PrimeStar.sqrtCutoffResidualConstant_pos)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨Ch * Ct * (1 + 1 / Real.log 2), by positivity, ?_⟩
  filter_upwards [htail, eventually_oneExitSmallPrime_apply_sq_le_sqrt S,
    eventually_powerRange_largePrime_discardedFullMolecule_eq_zero S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 4] with X ht hH hz hw hL hX
  intro a ha
  let L := Real.log (X : ℝ)
  let Z := Matrix.toEuclideanLin (oneExitComplementProjection S X)
    (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a))
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsqrt : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hx
  have hsqrtSq : Real.sqrt (X : ℝ) ^ 2 = (X : ℝ) := Real.sq_sqrt hx.le
  have hlog : 0 < L := by dsimp [L]; linarith
  have haPos : 0 < (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have haX : (a : ℝ) ≤ (X : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_le a
  have haSqrt : (a : ℝ) ≤ Real.sqrt (X : ℝ) := by
    have h : (a : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast (hw a ha).1
    exact h.trans Real.nat_sqrt_le_real_sqrt
  have homega : ((a : ℕ).primeFactors.card : ℝ) ≤ L / Real.log 2 :=
    (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos a)).trans
      (div_le_div_of_nonneg_right (Real.log_le_log haPos haX) hlogTwo.le)
  have hscalar : Real.sqrt (X : ℝ) *
      ((a : ℝ) * L ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ)) +
        (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L / (X : ℝ) ^ 2) ≤
      (1 + 1 / Real.log 2) * L ^ 3 := by
    have har : (a : ℝ) / Real.sqrt (X : ℝ) ≤ 1 := (div_le_one hsqrt).mpr haSqrt
    have har3 : ((a : ℝ) / Real.sqrt (X : ℝ)) ^ 3 ≤ 1 :=
      by simpa using pow_le_pow_left₀ (by positivity) har 3
    calc
      _ = ((a : ℝ) / (X : ℝ)) * L ^ 3 +
          ((a : ℝ) / Real.sqrt (X : ℝ)) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L := by
        rw [← hsqrtSq]
        simp only [Real.sqrt_sq hsqrt.le]
        field_simp
      _ ≤ L ^ 3 + ((a : ℕ).primeFactors.card : ℝ) * L := by
        have harX : (a : ℝ) / (X : ℝ) ≤ 1 := (div_le_one hx).mpr haX
        nlinarith [mul_le_mul_of_nonneg_right harX (pow_nonneg hlog.le 3),
          mul_le_mul_of_nonneg_right har3 (by positivity : 0 ≤ ((a : ℕ).primeFactors.card : ℝ) * L)]
      _ ≤ L ^ 3 + L / Real.log 2 * L := by gcongr
      _ ≤ L ^ 3 + L ^ 3 / Real.log 2 := by
        have hp : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by omega)
        have h := div_le_div_of_nonneg_right hp hlogTwo.le
        convert add_le_add_left h (L ^ 3) using 1 <;> first | rfl | ring
      _ = _ := by ring
  have hAZ : Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) Z =
      Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) Z := by
    rw [moleculeFamilyComplexAdjacency_eq_large_add_small, map_add, LinearMap.add_apply]
    rw [show Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) Z = 0 from hz a ha, zero_add]
  have hphase : ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
      (Matrix.toEuclideanLin (oneExitComplementProjection S X)
        (phasedFullStarMolecule S X a))‖ =
      ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) Z‖ := by
    simp only [phasedFullStarMolecule, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_fullStarMoleculePhase, one_mul, Z]
  rw [hphase, hAZ]
  calc
    _ ≤ Ch * Real.sqrt (X : ℝ) * ‖Z‖ ^ 2 := hH Z
    _ ≤ Ch * Real.sqrt (X : ℝ) * (Ct *
        ((a : ℝ) * L ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ)) +
          (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L / (X : ℝ) ^ 2)) := by
      gcongr
      exact ht a ha
    _ = Ch * Ct * (Real.sqrt (X : ℝ) *
        ((a : ℝ) * L ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ)) +
          (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L / (X : ℝ) ^ 2)) := by ring
    _ ≤ Ch * Ct * ((1 + 1 / Real.log 2) * L ^ 3) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by dsimp [L]; ring

/-- Complexification and the chosen unit phase preserve the literal full-molecule residual
norm. -/
theorem norm_phasedFullStarMolecule_residual
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X) :
    ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) (phasedFullStarMolecule S X a) -
      (exactPrincipalMoleculeRoot S X a : ℂ) • phasedFullStarMolecule S X a‖ =
      ‖exactPrincipalMoleculeResidual S X a‖ := by
  have hcomplex : Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
      (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a)) =
      PrimeStar.complexifyEuclidean (primeCoverAdjacencyOperator S X
        (exactPrincipalMoleculeAmbientVector S X a)) := by
    ext v
    simp only [moleculeFamilyComplexAdjacency, primeCoverAdjacencyOperator,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      complexifyRealMatrix_apply, PrimeStar.complexifyEuclidean_apply]
    push_cast
    rfl
  rw [phasedFullStarMolecule, map_smul, hcomplex, smul_comm
    (exactPrincipalMoleculeRoot S X a : ℂ), ← smul_sub,
    ← PrimeStar.complexifyEuclidean_smul, ← PrimeStar.complexifyEuclidean_sub]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_fullStarMoleculePhase,
    one_mul, PrimeStar.norm_complexifyEuclidean]
  rfl

/-- Finite projected-column comparison: normalization costs at most two, the orthogonal
projection is contractive, and both the raw residual and adjacency-on-tail are retained. -/
theorem normalizedProjectedFullStarMolecule_residual_sq_le
    (S : Finset ℕ) (X : ℕ) (a : PrimeStar.Vertex S X)
    (hnorm : 1 / 2 ≤ ‖projectedFullStarMolecule S X a‖) :
    ‖Matrix.toEuclideanLin (oneExitCompression S X) (normalizedProjectedFullStarMolecule S X a) -
      (exactPrincipalMoleculeRoot S X a : ℂ) • normalizedProjectedFullStarMolecule S X a‖ ^ 2 ≤
      8 * (‖exactPrincipalMoleculeResidual S X a‖ ^ 2 +
        ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
          (Matrix.toEuclideanLin (oneExitComplementProjection S X)
            (phasedFullStarMolecule S X a))‖ ^ 2) := by
  let P := Matrix.toEuclideanLin (oneExitProjection S X)
  let T := Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
  let G := Matrix.toEuclideanLin (oneExitCompression S X)
  let x := phasedFullStarMolecule S X a
  let nu : ℂ := exactPrincipalMoleculeRoot S X a
  let n := ‖projectedFullStarMolecule S X a‖
  have hn : 0 < n := by dsimp [n]; linarith
  have hnInv : n⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hn).mpr
    dsimp [n]
    linarith
  have hP (v : EuclideanSpace ℂ (PrimeStar.Vertex S X)) : P (P v) = P v := by
    have h := congrArg (fun M ↦ Matrix.toEuclideanLin M v)
      (oneExitProjection_isStarProjection S X).isIdempotentElem
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h
  have hG (v : EuclideanSpace ℂ (PrimeStar.Vertex S X)) : G v = P (T (P v)) := by
    simp only [G, P, T, oneExitCompression, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  have hQ : Matrix.toEuclideanLin (oneExitComplementProjection S X) x = x - P x := by
    simp only [oneExitComplementProjection, map_sub, LinearMap.sub_apply,
      Matrix.toLpLin_one, LinearMap.id_apply, P]
  have hexact : G (normalizedProjectedFullStarMolecule S X a) -
      nu • normalizedProjectedFullStarMolecule S X a =
      (n⁻¹ : ℂ) • P ((T x - nu • x) -
        T (Matrix.toEuclideanLin (oneExitComplementProjection S X) x)) := by
    change G ((n⁻¹ : ℂ) • P x) - nu • ((n⁻¹ : ℂ) • P x) = _
    rw [hG, hQ]
    simp only [map_smul, map_sub, hP, smul_sub, smul_smul]
    rw [mul_comm nu]
    abel
  have hbound : ‖G (normalizedProjectedFullStarMolecule S X a) -
      nu • normalizedProjectedFullStarMolecule S X a‖ ≤
      2 * (‖exactPrincipalMoleculeResidual S X a‖ +
        ‖T (Matrix.toEuclideanLin (oneExitComplementProjection S X) x)‖) := by
    rw [hexact, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    calc
      _ ≤ n⁻¹ * ‖(T x - nu • x) -
          T (Matrix.toEuclideanLin (oneExitComplementProjection S X) x)‖ :=
        mul_le_mul_of_nonneg_left (norm_oneExitProjection_apply_le S X _) (by positivity)
      _ ≤ n⁻¹ * (‖T x - nu • x‖ +
          ‖T (Matrix.toEuclideanLin (oneExitComplementProjection S X) x)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ 2 * (‖T x - nu • x‖ +
          ‖T (Matrix.toEuclideanLin (oneExitComplementProjection S X) x)‖) := by gcongr
      _ = _ := by rw [show ‖T x - nu • x‖ = ‖exactPrincipalMoleculeResidual S X a‖ from
          norm_phasedFullStarMolecule_residual S X a]
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbound
  change _ ≤ 8 * (‖exactPrincipalMoleculeResidual S X a‖ ^ 2 +
    ‖T (Matrix.toEuclideanLin (oneExitComplementProjection S X) x)‖ ^ 2)
  nlinarith only [hs, sq_nonneg (‖exactPrincipalMoleculeResidual S X a‖ -
    ‖T (Matrix.toEuclideanLin (oneExitComplementProjection S X) x)‖)]

/-- The actual normalized projected column has squared residual O(log^5 X), with all
normalization and tail hypotheses discharged on the power window. -/
theorem eventually_powerRange_projectedFullStarMolecule_residual_sq_le_logFifth
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        ‖Matrix.toEuclideanLin (oneExitCompression S X) (normalizedProjectedFullStarMolecule S X a) -
          (exactPrincipalMoleculeRoot S X a : ℂ) • normalizedProjectedFullStarMolecule S X a‖ ^ 2 ≤
          C * Real.log (X : ℝ) ^ 5 := by
  obtain ⟨Cg, hCg, hg⟩ := eventually_powerRange_exactPrincipalMoleculeResidual_sq_le_logFifth S hS htheta
  obtain ⟨Cz, hCz, hz⟩ :=
    eventually_powerRange_adjacency_discardedFullMolecule_sq_le_logCube S hS htheta
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨8 * (Cg + Cz), by positivity, ?_⟩
  filter_upwards [hg, hz, eventually_powerRange_projectedFullStarMolecule_norm_bounds S hS htheta,
    hlogTop.eventually_ge_atTop 1] with X hgX hzX hn hL
  intro a ha
  have hpow : Real.log (X : ℝ) ^ 3 ≤ Real.log (X : ℝ) ^ 5 := pow_le_pow_right₀ hL (by omega)
  calc
    _ ≤ _ := normalizedProjectedFullStarMolecule_residual_sq_le S X a (hn a ha).1
    _ ≤ 8 * (Cg * Real.log (X : ℝ) ^ 5 + Cz * Real.log (X : ℝ) ^ 3) := by
      gcongr
      · exact hgX a ha
      · exact hzX a ha
    _ ≤ 8 * (Cg * Real.log (X : ℝ) ^ 5 + Cz * Real.log (X : ℝ) ^ 5) := by gcongr
    _ = _ := by ring

/-- A complete prefix of positive allowed centres has at most K elements, including the
empty prefix K=0. -/
theorem card_moleculeCenter_le (S : Finset ℕ) (X K : ℕ) :
    Fintype.card (MoleculeCenter S X K) ≤ K := by
  let f : MoleculeCenter S X K → Fin K := fun a ↦
    ⟨(a.1 : ℕ) - 1, by have := PrimeStar.Vertex.coe_pos a.1; have := a.2; omega⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have heq : (a.1 : ℕ) - 1 = (b.1 : ℕ) - 1 := Fin.mk.inj hab
    have ha := PrimeStar.Vertex.coe_pos a.1
    have hb := PrimeStar.Vertex.coe_pos b.1
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hinj

/-- The actual complete-prefix projected residual has squared Hilbert--Schmidt norm at most
C K log^5 X. This proves the HS half of R4c; it does not assert the sharper collective
operator bound or Gram smallness. -/
theorem eventually_powerRange_projectedFullStarFrameResidual_hsSq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
        matrixFrobeniusNorm (projectedFullStarFrameResidual S X K) ^ 2 ≤
          C * (K : ℝ) * Real.log (X : ℝ) ^ 5 := by
  obtain ⟨C, hC, hcol⟩ :=
    eventually_powerRange_projectedFullStarMolecule_residual_sq_le_logFifth S hS htheta
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcol, hlogTop.eventually_ge_atTop 1] with X hcolumn hL
  intro K hK
  have heq (a : MoleculeCenter S X K) :
      (∑ v : PrimeStar.Vertex S X, ‖projectedFullStarFrameResidual S X K v a‖ ^ 2) =
        ‖Matrix.toEuclideanLin (oneExitCompression S X) (normalizedProjectedFullStarMolecule S X a.1) -
          (exactPrincipalMoleculeRoot S X a.1 : ℂ) • normalizedProjectedFullStarMolecule S X a.1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro v _
    have hentry : projectedFullStarFrameResidual S X K v a =
        (Matrix.toEuclideanLin (oneExitCompression S X) (normalizedProjectedFullStarMolecule S X a.1) -
          (exactPrincipalMoleculeRoot S X a.1 : ℂ) • normalizedProjectedFullStarMolecule S X a.1) v := by
      simp only [projectedFullStarFrameResidual, Matrix.sub_apply, Matrix.mul_apply,
        complexifyRealMatrix, exactMoleculeFamilyRootMatrix, Matrix.diagonal,
        Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, projectedFullStarFrame_apply,
        PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      simp [apply_ite, mul_comm]
    rw [hentry]
  rw [matrixFrobeniusNorm_sq, Finset.sum_comm]
  calc
    _ = ∑ a : MoleculeCenter S X K,
        ‖Matrix.toEuclideanLin (oneExitCompression S X) (normalizedProjectedFullStarMolecule S X a.1) -
          (exactPrincipalMoleculeRoot S X a.1 : ℂ) • normalizedProjectedFullStarMolecule S X a.1‖ ^ 2 :=
      Finset.sum_congr rfl (fun a _ ↦ heq a)
    _ ≤ ∑ _a : MoleculeCenter S X K, C * Real.log (X : ℝ) ^ 5 := by
      apply Finset.sum_le_sum
      intro a _
      exact hcolumn a.1 ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) * (C * Real.log (X : ℝ) ^ 5) := by simp
    _ ≤ (K : ℝ) * (C * Real.log (X : ℝ) ^ 5) := by
      apply mul_le_mul_of_nonneg_right _ (by
        have : 0 ≤ Real.log (X : ℝ) := by linarith
        positivity)
      exact_mod_cast card_moleculeCenter_le S X K
    _ = _ := by ring

end CollectiveResidual

noncomputable section ResidualLeafGram

open Filter
open scoped Classical BigOperators Matrix

/-- Small-prime edges preserve divisibility by a prime above the cutoff. -/
theorem largePrime_dvd_of_smallPrimeAdj
    {S : Finset ℕ} {X Y p : ℕ} {v w : PrimeStar.Vertex S X}
    (hp : p.Prime) (hYp : Y < p)
    (hadj : (PrimeStar.smallPrimeGraph S X Y).Adj v w)
    (hpv : p ∣ (v : ℕ)) : p ∣ (w : ℕ) := by
  obtain ⟨r, hr, _, hrY, hstep⟩ :=
    PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hadj
  rcases hstep with hup | hdown
  · exact hup ▸ dvd_trans hpv ⟨r, rfl⟩
  · have hdiv : p ∣ (w : ℕ) * r := hdown.symm ▸ hpv
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact h
    · have heq := (Nat.prime_dvd_prime_iff_eq hp hr).mp h
      omega

/-- Canonical first-exit centres have no prime divisor above the cutoff,
including inactive up-targets whose numerical value exceeds it. -/
theorem largePrime_not_dvd_canonicalExitTarget
    {S : Finset ℕ} {X Y p : ℕ} (hS : ∀ r ∈ S, r.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ Y)
    (hp : p.Prime) (hYp : Y < p)
    (i : PrimeStar.CanonicalExitIndex S X Y a) :
    ¬p ∣ (PrimeStar.canonicalExitTarget hS a i : ℕ) := by
  have hpa : ¬p ∣ (a : ℕ) := fun h ↦
    (not_le_of_gt (lt_of_le_of_lt ha hYp)) (Nat.le_of_dvd (PrimeStar.Vertex.coe_pos a) h)
  rcases i with q | q
  · change ¬p ∣ (a : ℕ) * (q : ℕ)
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hpa h
    · have hq := Nat.mem_primesLE.mp (Finset.mem_filter.mp q.property).1
      have heq := (Nat.prime_dvd_prime_iff_eq hp hq.2).mp h
      omega
  · intro h
    apply hpa
    exact dvd_trans h ⟨q, (PrimeStar.canonicalDownTarget_mul_coe a q).symm⟩

/-- A large-prime coordinate of the signed response is a genuine leaf, never
an inactive up-centre. This discharges the leaf/centre separation arithmetically. -/
theorem eventually_powerRange_signedLargePrimeCoordinate_abs_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ v : PrimeStar.Vertex S X,
      (∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)) →
      |exactPrincipalMoleculeSignedInteriorVector S X a v| ≤
        2000 / moleculeStarEnergy S X a ^ 2 := by
  filter_upwards [eventually_powerRange_signedCanonicalLeaf_abs_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta]
    with X hleaf hwindow
  intro a ha v hv
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  obtain ⟨p, hp, hYp, hpv⟩ := hv
  by_cases hzero : exactPrincipalMoleculeSignedInteriorVector S X a v = 0
  · rw [hzero, abs_zero]
    positivity
  · have hsupport : v ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a := by
      by_contra hnot
      exact hzero (PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem
        (exactPrincipalMoleculeSignedInteriorSource S X a) hnot)
    obtain ⟨i, hi⟩ := exists_canonicalExitIndex_of_mem_compression hS
      (PrimeStar.sqrtCutoff_condition X) haY hd hsupport
    rcases PrimeStar.mem_largePrimeStarSupport.mp hi with heq | hleafAdj
    · exact False.elim (largePrime_not_dvd_canonicalExitTarget hS haY hp hYp i
        (heq ▸ hpv))
    · exact hleaf a ha i v (by simpa [PrimeStar.largePrimeLeaves] using hleafAdj)

/-- An exterior large-prime signed residual coordinate costs only logarithmic
incoming multiplicity. The global degree of the output is not used. -/
theorem eventually_powerRange_signedExteriorLeaf_abs_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ v : PrimeStar.Vertex S X,
      (∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)) →
      |PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X a)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X a)) v| ≤
        (4000 / Real.log 2) * Real.log (X : ℝ) / moleculeStarEnergy S X a ^ 2 := by
  filter_upwards [eventually_powerRange_signedLargePrimeCoordinate_abs_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 2] with X hleaf hwindow hX
  intro a ha v hv
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  rw [PrimeStar.euclideanCoordinateComplementProjection_apply]
  split_ifs with hvSupport
  · rw [abs_zero]
    positivity
  · let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
    let N := G.neighborFinset v ∩
      PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
    let y := exactPrincipalMoleculeSignedInteriorVector S X a
    have hsum : ∑ w ∈ G.neighborFinset v, y w = ∑ w ∈ N, y w := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro w hw hwn
      exact PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem
        (exactPrincipalMoleculeSignedInteriorSource S X a)
        (fun h ↦ hwn (Finset.mem_inter.mpr ⟨hw, h⟩))
    have homega (w : PrimeStar.Vertex S X) :
        ((w : ℕ).primeFactors.card : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
      apply (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos w)).trans
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      exact Real.log_le_log (by exact_mod_cast PrimeStar.Vertex.coe_pos w)
        (by exact_mod_cast PrimeStar.Vertex.coe_le w)
    have hcard : (N.card : ℝ) ≤ 2 * Real.log (X : ℝ) / Real.log 2 := by
      have hn : N.card ≤ (a : ℕ).primeFactors.card + (v : ℕ).primeFactors.card :=
        card_exterior_firstExit_neighbors_le_primeFactors hS haY
          (fun h ↦ hvSupport (Finset.mem_union_left _ h))
      have hnR : (N.card : ℝ) ≤
          ((a : ℕ).primeFactors.card : ℝ) + ((v : ℕ).primeFactors.card : ℝ) := by exact_mod_cast hn
      calc
        _ ≤ Real.log (X : ℝ) / Real.log 2 + Real.log (X : ℝ) / Real.log 2 :=
          hnR.trans (add_le_add (homega a) (homega v))
        _ = _ := by ring
    rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
    change |(G.adjMatrix ℝ *ᵥ y.ofLp) v| ≤ _
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change |∑ w ∈ G.neighborFinset v, y w| ≤ _
    rw [hsum]
    calc
      _ ≤ ∑ w ∈ N, |y w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w ∈ N, 2000 / moleculeStarEnergy S X a ^ 2 := by
        apply Finset.sum_le_sum
        intro w hw
        obtain ⟨p, hp, hYp, hpv⟩ := hv
        exact hleaf a ha w ⟨p, hp, hYp,
          largePrime_dvd_of_smallPrimeAdj hp hYp
            ((G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1) hpv⟩
      _ = (N.card : ℝ) * (2000 / moleculeStarEnergy S X a ^ 2) := by simp
      _ ≤ (2 * Real.log (X : ℝ) / Real.log 2) *
          (2000 / moleculeStarEnergy S X a ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring

/-- The leaf part of a pair of actual signed residuals is bounded by the
number of graph coordinates, not by an unproved collision-multiplicity estimate. -/
theorem eventually_powerRange_signedExteriorLeaf_pair_sum_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a b : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → InPowerRange theta X (b : ℕ) →
      let g := fun c : PrimeStar.Vertex S X ↦
        PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X c)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X c))
      ∑ v ∈ Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
          ∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)),
        |g a v * g b v| ≤
          2 * (4000 / Real.log 2) ^ 2 * (X : ℝ) * Real.log (X : ℝ) ^ 2 /
            (moleculeStarEnergy S X a ^ 2 * moleculeStarEnergy S X b ^ 2) := by
  filter_upwards [eventually_powerRange_signedExteriorLeaf_abs_le S hS htheta,
    eventually_ge_atTop 2] with X hleaf hX
  intro a b ha hb g
  let V := Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
    ∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ))
  let C := 4000 / Real.log 2
  let L := Real.log (X : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcard : (V.card : ℝ) ≤ 2 * (X : ℝ) := by
    have hinj : Function.Injective (fun v : PrimeStar.Vertex S X ↦ v.val) :=
      fun _ _ h ↦ Subtype.ext h
    have hn := Fintype.card_le_of_injective _ hinj
    have hvn : V.card ≤ X + 1 := (Finset.card_le_univ V).trans (by simpa using hn)
    have hvR : (V.card : ℝ) ≤ (X : ℝ) + 1 := by exact_mod_cast hvn
    have hxR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    linarith
  calc
    _ ≤ ∑ _v ∈ V,
        (C * L / moleculeStarEnergy S X a ^ 2) *
          (C * L / moleculeStarEnergy S X b ^ 2) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [abs_mul]
      exact mul_le_mul (hleaf a ha v (Finset.mem_filter.mp hv).2)
        (hleaf b hb v (Finset.mem_filter.mp hv).2) (abs_nonneg _)
        (div_nonneg (mul_nonneg hC hL) (sq_nonneg _))
    _ = (V.card : ℝ) *
        ((C * L / moleculeStarEnergy S X a ^ 2) *
          (C * L / moleculeStarEnergy S X b ^ 2)) := by simp
    _ ≤ (2 * (X : ℝ)) *
        ((C * L / moleculeStarEnergy S X a ^ 2) *
          (C * L / moleculeStarEnergy S X b ^ 2)) := by
      apply mul_le_mul_of_nonneg_right hcard
      exact mul_nonneg (div_nonneg (mul_nonneg hC hL) (sq_nonneg _))
        (div_nonneg (mul_nonneg hC hL) (sq_nonneg _))
    _ = _ := by dsimp only [C, L]; ring

/-- Summing the leaf part of the actual signed residual Gram over the entire
positive prefix gives the K^3/X contribution. No distinct-source premise or
pointwise collision hypothesis is needed for this half of the Schur row. -/
theorem eventually_powerRange_signedExteriorLeaf_gramRow_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∀ a : MoleculeCenter S X K,
      let g := fun c : PrimeStar.Vertex S X ↦
        PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X c)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X c))
      ∑ b : MoleculeCenter S X K,
        ∑ v ∈ Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
            ∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)),
          |g a.1 v * g b.1 v| ≤
            128 * (4000 / Real.log 2) ^ 2 * (K : ℝ) ^ 3 * Real.log (X : ℝ) ^ 4 /
              (X : ℝ) := by
  filter_upwards [eventually_powerRange_signedExteriorLeaf_pair_sum_le S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_ge_atTop 2] with X hpair hscale hX
  intro K hK a g
  let C := 4000 / Real.log 2
  let L := Real.log (X : ℝ)
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hwindow (b : MoleculeCenter S X K) : InPowerRange theta X (b.1 : ℕ) :=
    ⟨PrimeStar.Vertex.coe_pos b.1, (by exact_mod_cast b.2 : (b.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
  have hinv (b : MoleculeCenter S X K) :
      1 / moleculeStarEnergy S X b.1 ^ 2 ≤ 8 * (b.1 : ℝ) * L / (X : ℝ) := by
    have hb : 0 < (b.1 : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos b.1
    calc
      _ ≤ 1 / ((X : ℝ) / (8 * (b.1 : ℝ) * L)) :=
        one_div_le_one_div_of_le (by positivity) (hscale b.1 (hwindow b)).1
      _ = _ := by field_simp
  have hpairBound (b : MoleculeCenter S X K) :
      2 * C ^ 2 * (X : ℝ) * L ^ 2 /
          (moleculeStarEnergy S X a.1 ^ 2 * moleculeStarEnergy S X b.1 ^ 2) ≤
        128 * C ^ 2 * (K : ℝ) ^ 2 * L ^ 4 / (X : ℝ) := by
    have haK : (a.1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast a.2
    have hbK : (b.1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast b.2
    calc
      _ = (2 * C ^ 2 * (X : ℝ) * L ^ 2) *
          ((1 / moleculeStarEnergy S X a.1 ^ 2) * (1 / moleculeStarEnergy S X b.1 ^ 2)) := by ring
      _ ≤ (2 * C ^ 2 * (X : ℝ) * L ^ 2) *
          ((8 * (a.1 : ℝ) * L / (X : ℝ)) * (8 * (b.1 : ℝ) * L / (X : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (hinv a) (hinv b) (by positivity) (by positivity)
      _ ≤ (2 * C ^ 2 * (X : ℝ) * L ^ 2) *
          ((8 * (K : ℝ) * L / (X : ℝ)) * (8 * (K : ℝ) * L / (X : ℝ))) := by
        gcongr
      _ = _ := by field_simp; ring
  calc
    _ ≤ ∑ b : MoleculeCenter S X K,
        2 * C ^ 2 * (X : ℝ) * L ^ 2 /
          (moleculeStarEnergy S X a.1 ^ 2 * moleculeStarEnergy S X b.1 ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      exact hpair a.1 b.1 (hwindow a) (hwindow b)
    _ ≤ ∑ _b : MoleculeCenter S X K,
        128 * C ^ 2 * (K : ℝ) ^ 2 * L ^ 4 / (X : ℝ) :=
      Finset.sum_le_sum (fun b _ ↦ hpairBound b)
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) *
        (128 * C ^ 2 * (K : ℝ) ^ 2 * L ^ 4 / (X : ℝ)) := by simp
    _ ≤ (K : ℝ) * (128 * C ^ 2 * (K : ℝ) ^ 2 * L ^ 4 / (X : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_moleculeCenter_le S X K
    _ = _ := by dsimp only [C, L]; ring

end ResidualLeafGram

noncomputable section ResidualCentreGram

open Filter
open scoped Classical BigOperators Matrix

private theorem source_eq_of_twoStep_to_free_product
    {a b p q r s u v : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpb : ¬p ∣ b) (hqb : ¬q ∣ b)
    (hv : a * p * q = v)
    (hbu : b * r = u ∨ u * r = b)
    (huv : u * s = v ∨ v * s = u) : a = b := by
  have hupup {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
      (heq : a * p * q = b * r * s) : a = b := by
    have hpdiv : p ∣ b * r * s := by
      rw [← heq]
      exact ⟨a * q, by ac_rfl⟩
    rcases hp.dvd_mul.mp hpdiv with hpr | hps
    · have hpr' : p = r :=
        (Nat.prime_dvd_prime_iff_eq hp hr).mp ((hp.dvd_mul.mp hpr).resolve_left hpb)
      subst r
      have hrest : a * q = b * s := by
        apply Nat.eq_of_mul_eq_mul_right hp.pos
        calc
          a * q * p = a * p * q := by ac_rfl
          _ = b * p * s := heq
          _ = b * s * p := by ac_rfl
      have hqdiv : q ∣ b * s := hrest ▸ dvd_mul_left q a
      have hqs : q = s :=
        (Nat.prime_dvd_prime_iff_eq hq hs).mp ((hq.dvd_mul.mp hqdiv).resolve_left hqb)
      subst s
      exact Nat.eq_of_mul_eq_mul_right hq.pos hrest
    · have hps' := (Nat.prime_dvd_prime_iff_eq hp hs).mp hps
      subst s
      have hrest : a * q = b * r := by
        apply Nat.eq_of_mul_eq_mul_right hp.pos
        calc
          a * q * p = a * p * q := by ac_rfl
          _ = b * r * p := heq
      have hqdiv : q ∣ b * r := hrest ▸ dvd_mul_left q a
      have hqr : q = r :=
        (Nat.prime_dvd_prime_iff_eq hq hr).mp ((hq.dvd_mul.mp hqdiv).resolve_left hqb)
      subst r
      exact Nat.eq_of_mul_eq_mul_right hq.pos hrest
  have hmixed {r s : ℕ} (hr : r.Prime)
      (heq : a * p * q * s = b * r) : False := by
    have hpdiv : p ∣ b * r := by
      rw [← heq]
      exact ⟨a * q * s, by ac_rfl⟩
    have hpr : p = r :=
      (Nat.prime_dvd_prime_iff_eq hp hr).mp ((hp.dvd_mul.mp hpdiv).resolve_left hpb)
    subst r
    have hrest : a * q * s = b := by
      apply Nat.eq_of_mul_eq_mul_right hp.pos
      calc
        a * q * s * p = a * p * q * s := by ac_rfl
        _ = b * p := heq
    exact hqb ⟨a * s, by rw [← hrest]; ac_rfl⟩
  rcases hbu with hbu | hbu <;> rcases huv with huv | huv
  · apply hupup hr hs
    calc
      a * p * q = v := hv
      _ = u * s := huv.symm
      _ = b * r * s := by rw [hbu]
  · exact False.elim (hmixed hr (by rw [hv, huv, hbu]))
  · apply False.elim
    apply hmixed hs
    calc
      a * p * q * r = v * r := by rw [hv]
      _ = u * s * r := by rw [huv]
      _ = u * r * s := by ac_rfl
      _ = b * s := by rw [hbu]
  · apply False.elim
    apply hpb
    refine ⟨a * q * s * r, ?_⟩
    calc
      b = u * r := hbu.symm
      _ = v * s * r := by rw [huv]
      _ = a * p * q * s * r := by rw [hv]
      _ = p * (a * q * s * r) := by ac_rfl

/-- In a nonreturning two-step collision of distinct sources, at least one
prime on the first path divides an endpoint. The other prime remains free. -/
theorem prime_dvd_endpoints_of_twoStep_collision
    {a b p q r s t u v : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hab : a ≠ b) (hva : v ≠ a)
    (hat : a * p = t ∨ t * p = a)
    (htv : t * q = v ∨ v * q = t)
    (hbu : b * r = u ∨ u * r = b)
    (huv : u * s = v ∨ v * s = u) :
    p ∣ a ∨ p ∣ b ∨ q ∣ a ∨ q ∣ b := by
  by_contra h
  push Not at h
  obtain ⟨hpa, hpb, hqa, hqb⟩ := h
  have ht : a * p = t := hat.resolve_right (fun heq ↦ hpa ⟨t, by rw [← heq]; ac_rfl⟩)
  have hv : t * q = v := by
    rcases htv with hup | hdown
    · exact hup
    · have hqdiv : q ∣ a * p := by rw [ht]; exact ⟨v, by rw [← hdown]; ac_rfl⟩
      have hqp := (Nat.prime_dvd_prime_iff_eq hq hp).mp
        ((hq.dvd_mul.mp hqdiv).resolve_left hqa)
      subst q
      exact False.elim (hva (Nat.eq_of_mul_eq_mul_right hp.pos (hdown.trans ht.symm)))
  exact hab (source_eq_of_twoStep_to_free_product hp hq hr hs hpb hqb
    (by rw [ht, hv]) hbu huv)

/-- The four oriented two-step values, with exact natural-number divisions. -/
private theorem mem_fourValues_of_twoStep
    {a p q t v : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hat : a * p = t ∨ t * p = a)
    (htv : t * q = v ∨ v * q = t) :
    v ∈ ({a * p * q, a * p / q, a / p * q, a / p / q} : Finset ℕ) := by
  rcases hat with hat | hat <;> rcases htv with htv | htv
  · have heq : v = a * p * q := by rw [hat, htv]
    simp [heq]
  · have heq : v = a * p / q := by rw [hat, ← htv, Nat.mul_div_cancel _ hq]
    simp [heq]
  · have heq : v = a / p * q := by rw [← hat, Nat.mul_div_cancel _ hp, htv]
    simp [heq]
  · have heq : v = a / p / q := by
      rw [← hat, Nat.mul_div_cancel _ hp, ← htv, Nat.mul_div_cancel _ hq]
    simp [heq]

/-- Distinct actual sources have at most a cutoff times an endpoint-divisor
count of common two-step outputs, after excluding the return to the first source.
The free common small prime is retained in the factor Y. -/
theorem card_common_twoStep_outputs_le
    {S : Finset ℕ} {X Y : ℕ} {a b : PrimeStar.Vertex S X} (hab : a ≠ b) :
    (Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦ v ≠ a ∧
      ∃ t u : PrimeStar.Vertex S X,
        (PrimeStar.smallPrimeGraph S X Y).Adj a t ∧
        (PrimeStar.smallPrimeGraph S X Y).Adj t v ∧
        (PrimeStar.smallPrimeGraph S X Y).Adj b u ∧
        (PrimeStar.smallPrimeGraph S X Y).Adj u v)).card ≤
      8 * Y * ((a : ℕ).primeFactors.card + (b : ℕ).primeFactors.card) := by
  let G := PrimeStar.smallPrimeGraph S X Y
  let N := Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦ v ≠ a ∧
    ∃ t u : PrimeStar.Vertex S X, G.Adj a t ∧ G.Adj t v ∧ G.Adj b u ∧ G.Adj u v)
  let F := (a : ℕ).primeFactors ∪ (b : ℕ).primeFactors
  let P := Nat.primesLE Y
  let W := fun p q : ℕ ↦ ({(a : ℕ) * p * q, (a : ℕ) * p / q,
    (a : ℕ) / p * q, (a : ℕ) / p / q, (a : ℕ) * q * p, (a : ℕ) * q / p,
    (a : ℕ) / q * p, (a : ℕ) / q / p} : Finset ℕ)
  let T := F.biUnion (fun p ↦ P.biUnion (W p))
  have hinj : Function.Injective (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) :=
    fun _ _ h ↦ Subtype.ext (Fin.ext h)
  have habNat : (a : ℕ) ≠ (b : ℕ) := fun h ↦ hab (hinj h)
  have hsub : N.image (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) ⊆ T := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hva, t, u, hat, htv, hbu, huv⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨p, hp, _, hpY, hat'⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hat
    obtain ⟨q, hq, _, hqY, htv'⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp htv
    obtain ⟨r, hr, _, _, hbu'⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hbu
    obtain ⟨s, hs, _, _, huv'⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp huv
    have hanchor := prime_dvd_endpoints_of_twoStep_collision hp hq hr hs habNat
      (fun h ↦ hva (hinj h)) hat' htv' hbu' huv'
    have hfour := mem_fourValues_of_twoStep hp.pos hq.pos hat' htv'
    have hleft (hpF : p ∈ F) : (v : ℕ) ∈ T := by
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hpF, Finset.mem_biUnion.mpr ⟨q, Nat.mem_primesLE.mpr ⟨hqY, hq⟩, ?_⟩⟩
      dsimp only [W]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfour ⊢
      rcases hfour with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    have hright (hqF : q ∈ F) : (v : ℕ) ∈ T := by
      apply Finset.mem_biUnion.mpr
      refine ⟨q, hqF, Finset.mem_biUnion.mpr ⟨p, Nat.mem_primesLE.mpr ⟨hpY, hp⟩, ?_⟩⟩
      dsimp only [W]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfour ⊢
      exact Or.inr (Or.inr (Or.inr (Or.inr hfour)))
    rcases hanchor with hpa | hpb | hqa | hqb
    · exact hleft (Finset.mem_union_left _ (hp.mem_primeFactors hpa (PrimeStar.Vertex.coe_pos a).ne'))
    · exact hleft (Finset.mem_union_right _ (hp.mem_primeFactors hpb (PrimeStar.Vertex.coe_pos b).ne'))
    · exact hright (Finset.mem_union_left _ (hq.mem_primeFactors hqa (PrimeStar.Vertex.coe_pos a).ne'))
    · exact hright (Finset.mem_union_right _ (hq.mem_primeFactors hqb (PrimeStar.Vertex.coe_pos b).ne'))
  have hW (p q : ℕ) : (W p q).card ≤ 8 := by
    convert ([(a : ℕ) * p * q, (a : ℕ) * p / q, (a : ℕ) / p * q,
      (a : ℕ) / p / q, (a : ℕ) * q * p, (a : ℕ) * q / p,
      (a : ℕ) / q * p, (a : ℕ) / q / p].toFinset_card_le) using 1 <;> simp [W]
  have hP : P.card ≤ Y := by
    have hsubset : P ⊆ Finset.Icc 1 Y := by
      intro p hp
      obtain ⟨hpY, hp⟩ := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr ⟨hp.one_le, hpY⟩
    simpa using Finset.card_le_card hsubset
  calc
    N.card = (N.image (fun v : PrimeStar.Vertex S X ↦ (v : ℕ))).card :=
      (Finset.card_image_of_injective N hinj).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ F.card * (P.card * 8) :=
      Finset.card_biUnion_le_card_mul F _ _ (fun p _ ↦
        Finset.card_biUnion_le_card_mul P _ _ (fun q _ ↦ hW p q))
    _ ≤ ((a : ℕ).primeFactors.card + (b : ℕ).primeFactors.card) * (Y * 8) :=
      Nat.mul_le_mul (Finset.card_union_le _ _) (Nat.mul_le_mul_right 8 hP)
    _ = _ := by ring

private theorem canonicalExitTarget_smallPrimeAdj
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ Y)
    (i : PrimeStar.CanonicalExitIndex S X Y a) :
    (PrimeStar.smallPrimeGraph S X Y).Adj a (PrimeStar.canonicalExitTarget hS a i) := by
  apply PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
  rcases i with q | q
  · have hq := Finset.mem_filter.mp q.property
    exact ⟨q, (Nat.mem_primesLE.mp hq.1).2, hq.2.1,
      (Nat.mem_primesLE.mp hq.1).1, Or.inl (PrimeStar.canonicalUpTarget_coe hS a q)⟩
  · have hq := Nat.prime_of_mem_primeFactors q.property
    have hdiv := Nat.dvd_of_mem_primeFactors q.property
    exact ⟨q, hq, (fun h ↦ PrimeStar.Vertex.not_dvd_of_mem a h hdiv),
      (Nat.le_of_mem_primeFactors q.property).trans ha,
      Or.inr (PrimeStar.canonicalDownTarget_mul_coe a q)⟩

/-- A nonzero signed interior coordinate with no large prime factor is
an actual canonical centre. This includes the inactive up-targets. -/
theorem exists_canonicalCenter_of_signedInterior_ne_zero
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a w : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hw : ¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (w : ℕ))
    (hzero : exactPrincipalMoleculeSignedInteriorVector S X a w ≠ 0) :
    ∃ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
      w = PrimeStar.canonicalExitTarget hS a i := by
  have hsupport : w ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a := by
    by_contra hnot
    exact hzero (PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem
      (exactPrincipalMoleculeSignedInteriorSource S X a) hnot)
  obtain ⟨i, hi⟩ := exists_canonicalExitIndex_of_mem_compression hS
    (PrimeStar.sqrtCutoff_condition X) ha hd hsupport
  rcases PrimeStar.mem_largePrimeStarSupport.mp hi with heq | hadj
  · exact ⟨i, heq⟩
  · obtain ⟨p, hp, _, hYp, hrel⟩ := hadj
    rcases hrel with hup | hdown
    · exact False.elim (hw ⟨p, hp, hYp, ⟨(PrimeStar.canonicalExitTarget hS a i : ℕ), by
        rw [← hup]; ac_rfl⟩⟩)
    · exact False.elim (largePrime_not_dvd_canonicalExitTarget hS ha hp hYp i
        ⟨(w : ℕ), by rw [← hdown]; ac_rfl⟩)

/-- Uniform signed response bound on all coordinates without a large prime
factor. Canonical-centre identification and both coefficient producers are supplied. -/
theorem eventually_powerRange_signedSmallPrimeCoordinate_abs_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ w : PrimeStar.Vertex S X,
      (¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (w : ℕ)) →
      |exactPrincipalMoleculeSignedInteriorVector S X a w| ≤
        10000 / moleculeStarEnergy S X a := by
  filter_upwards [eventually_powerRange_signedUpCenter_abs_le S hS htheta,
    eventually_powerRange_signedDownCenter_abs_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta]
    with X hup hdown hwindow
  intro a ha w hw
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  by_cases hzero : exactPrincipalMoleculeSignedInteriorVector S X a w = 0
  · rw [hzero, abs_zero]
    positivity
  · obtain ⟨i, rfl⟩ := exists_canonicalCenter_of_signedInterior_ne_zero hS haY hd hw hzero
    rcases i with q | q
    · exact (hup a ha q).trans (div_le_div_of_nonneg_right (by norm_num) hmu.le)
    · have hq : (1 : ℝ) ≤ q := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors q.property).one_le
      exact (hdown a ha q).trans (div_le_div_of_nonneg_left (by norm_num) hmu
        (by nlinarith))

/-- A signed exterior output without a large prime factor is bounded by
the canonical-centre coefficient times its actual logarithmic incoming multiplicity. -/
theorem eventually_powerRange_signedExteriorCentre_abs_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → ∀ v : PrimeStar.Vertex S X,
      (¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)) →
      |PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X a)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X a)) v| ≤
        (20000 / Real.log 2) * Real.log (X : ℝ) / moleculeStarEnergy S X a := by
  filter_upwards [eventually_powerRange_signedSmallPrimeCoordinate_abs_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 2] with X hcentre hwindow hX
  intro a ha v hv
  obtain ⟨haY, hd, _⟩ := hwindow a ha
  have hmu : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  rw [PrimeStar.euclideanCoordinateComplementProjection_apply]
  split_ifs with hvSupport
  · rw [abs_zero]
    positivity
  · let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
    let N := G.neighborFinset v ∩
      PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
    let y := exactPrincipalMoleculeSignedInteriorVector S X a
    have hsum : ∑ w ∈ G.neighborFinset v, y w = ∑ w ∈ N, y w := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro w hw hwn
      exact PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem
        (exactPrincipalMoleculeSignedInteriorSource S X a)
        (fun h ↦ hwn (Finset.mem_inter.mpr ⟨hw, h⟩))
    have homega (w : PrimeStar.Vertex S X) :
        ((w : ℕ).primeFactors.card : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
      apply (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos w)).trans
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      exact Real.log_le_log (by exact_mod_cast PrimeStar.Vertex.coe_pos w)
        (by exact_mod_cast PrimeStar.Vertex.coe_le w)
    have hcard : (N.card : ℝ) ≤ 2 * Real.log (X : ℝ) / Real.log 2 := by
      have hn : N.card ≤ (a : ℕ).primeFactors.card + (v : ℕ).primeFactors.card :=
        card_exterior_firstExit_neighbors_le_primeFactors hS haY
          (fun h ↦ hvSupport (Finset.mem_union_left _ h))
      have hnR : (N.card : ℝ) ≤
          ((a : ℕ).primeFactors.card : ℝ) + ((v : ℕ).primeFactors.card : ℝ) := by exact_mod_cast hn
      calc
        _ ≤ Real.log (X : ℝ) / Real.log 2 + Real.log (X : ℝ) / Real.log 2 :=
          hnR.trans (add_le_add (homega a) (homega v))
        _ = _ := by ring
    rw [Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
    change |(G.adjMatrix ℝ *ᵥ y.ofLp) v| ≤ _
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change |∑ w ∈ G.neighborFinset v, y w| ≤ _
    rw [hsum]
    calc
      _ ≤ ∑ w ∈ N, |y w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w ∈ N, 10000 / moleculeStarEnergy S X a := by
        apply Finset.sum_le_sum
        intro w hw
        apply hcentre a ha w
        rintro ⟨p, hp, hYp, hpw⟩
        apply hv
        exact ⟨p, hp, hYp, largePrime_dvd_of_smallPrimeAdj hp hYp
          (G.adj_symm ((G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1)) hpw⟩
      _ = (N.card : ℝ) * (10000 / moleculeStarEnergy S X a) := by simp
      _ ≤ (2 * Real.log (X : ℝ) / Real.log 2) *
          (10000 / moleculeStarEnergy S X a) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring

/-- Every nonzero centre-type signed exterior residual has a nonreturning
literal two-small-prime-step path from its source. -/
theorem exists_twoStep_of_signedExteriorCentre_ne_zero
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a v : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a)
    (hv : ¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ))
    (hg : PrimeStar.euclideanCoordinateComplementProjection
      (exactPrincipalMoleculeSupport S X a)
      (Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeSignedInteriorVector S X a)) v ≠ 0) :
    v ≠ a ∧ ∃ w : PrimeStar.Vertex S X,
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a w ∧
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj w v := by
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let y := exactPrincipalMoleculeSignedInteriorVector S X a
  have hvOut : v ∉ exactPrincipalMoleculeSupport S X a := by
    intro hvIn
    exact hg (by simp [PrimeStar.euclideanCoordinateComplementProjection_apply, hvIn])
  have hsum : ∑ w ∈ G.neighborFinset v, y w ≠ 0 := by
    rw [PrimeStar.euclideanCoordinateComplementProjection_apply, if_neg hvOut,
      Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply] at hg
    change (G.adjMatrix ℝ *ᵥ y.ofLp) v ≠ 0 at hg
    simpa only [SimpleGraph.adjMatrix_mulVec_apply] using hg
  obtain ⟨w, hw, hwy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hadj := (G.mem_neighborFinset v w).mp hw
  have hwSmooth : ¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (w : ℕ) := by
    rintro ⟨p, hp, hYp, hpw⟩
    exact hv ⟨p, hp, hYp, largePrime_dvd_of_smallPrimeAdj hp hYp (G.adj_symm hadj) hpw⟩
  obtain ⟨i, hwi⟩ := exists_canonicalCenter_of_signedInterior_ne_zero hS ha hd hwSmooth hwy
  refine ⟨?_, w, ?_, G.adj_symm hadj⟩
  · intro hva
    apply hvOut
    rw [hva]
    exact Finset.mem_union_left _ (by simp [PrimeStar.largePrimeStarSupport])
  · rw [hwi]
    exact canonicalExitTarget_smallPrimeAdj hS ha i

/-- The off-diagonal centre part of the actual signed residual Gram retains
one free common prime, hence the factor sqrtCutoff X in the bound. -/
theorem eventually_powerRange_signedExteriorCentre_pair_sum_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a b : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → InPowerRange theta X (b : ℕ) → a ≠ b →
      let g := fun c : PrimeStar.Vertex S X ↦
        PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X c)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X c))
      ∑ v ∈ Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
          ¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)),
        |g a v * g b v| ≤
          (16 / Real.log 2) * (20000 / Real.log 2) ^ 2 *
            (squareRootCutoff X : ℝ) * Real.log (X : ℝ) ^ 3 /
              (moleculeStarEnergy S X a * moleculeStarEnergy S X b) := by
  filter_upwards [eventually_powerRange_signedExteriorCentre_abs_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 2] with X hcentre hwindow hX
  intro a b ha hb hab g
  obtain ⟨haY, hda, _⟩ := hwindow a ha
  obtain ⟨hbY, hdb, _⟩ := hwindow b hb
  have hma : 0 < moleculeStarEnergy S X a := Real.sqrt_pos.mpr (by exact_mod_cast hda)
  have hmb : 0 < moleculeStarEnergy S X b := Real.sqrt_pos.mpr (by exact_mod_cast hdb)
  let U := Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
    ¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ))
  let N := U.filter (fun v ↦ g a v ≠ 0 ∧ g b v ≠ 0)
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let T := Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦ v ≠ a ∧
    ∃ t u : PrimeStar.Vertex S X, G.Adj a t ∧ G.Adj t v ∧ G.Adj b u ∧ G.Adj u v)
  let C := 20000 / Real.log 2
  let L := Real.log (X : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : ∑ v ∈ U, |g a v * g b v| = ∑ v ∈ N, |g a v * g b v| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hvN
    have hn : ¬(g a v ≠ 0 ∧ g b v ≠ 0) :=
      fun h ↦ hvN (Finset.mem_filter.mpr ⟨hv, h⟩)
    by_cases hga : g a v = 0
    · simp [hga]
    · have hgb : g b v = 0 := by
        by_contra hgb
        exact hn ⟨hga, hgb⟩
      simp [hgb]
  have hsub : N ⊆ T := by
    intro v hv
    obtain ⟨hvU, hga, hgb⟩ := Finset.mem_filter.mp hv
    have hvSmooth := (Finset.mem_filter.mp hvU).2
    obtain ⟨hva, t, hat, htv⟩ :=
      exists_twoStep_of_signedExteriorCentre_ne_zero hS haY hda hvSmooth hga
    obtain ⟨_, u, hbu, huv⟩ :=
      exists_twoStep_of_signedExteriorCentre_ne_zero hS hbY hdb hvSmooth hgb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hva, t, u, hat, htv, hbu, huv⟩
  have homega (w : PrimeStar.Vertex S X) :
      ((w : ℕ).primeFactors.card : ℝ) ≤ L / Real.log 2 := by
    apply (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos w)).trans
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    exact Real.log_le_log (by exact_mod_cast PrimeStar.Vertex.coe_pos w)
      (by exact_mod_cast PrimeStar.Vertex.coe_le w)
  have hcard : (N.card : ℝ) ≤ (16 / Real.log 2) * (squareRootCutoff X : ℝ) * L := by
    have hn : N.card ≤ 8 * squareRootCutoff X *
        ((a : ℕ).primeFactors.card + (b : ℕ).primeFactors.card) :=
      (Finset.card_le_card hsub).trans (card_common_twoStep_outputs_le hab)
    have hnR : (N.card : ℝ) ≤ 8 * (squareRootCutoff X : ℝ) *
        (((a : ℕ).primeFactors.card : ℝ) + ((b : ℕ).primeFactors.card : ℝ)) := by exact_mod_cast hn
    calc
      _ ≤ 8 * (squareRootCutoff X : ℝ) * (L / Real.log 2 + L / Real.log 2) :=
        hnR.trans (mul_le_mul_of_nonneg_left (add_le_add (homega a) (homega b)) (by positivity))
      _ = _ := by ring
  change (∑ v ∈ U, |g a v * g b v|) ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ N, (C * L / moleculeStarEnergy S X a) * (C * L / moleculeStarEnergy S X b) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvSmooth := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
      rw [abs_mul]
      exact mul_le_mul (hcentre a ha v hvSmooth) (hcentre b hb v hvSmooth)
        (abs_nonneg _) (by positivity)
    _ = (N.card : ℝ) * ((C * L / moleculeStarEnergy S X a) * (C * L / moleculeStarEnergy S X b)) := by simp
    _ ≤ ((16 / Real.log 2) * (squareRootCutoff X : ℝ) * L) *
        ((C * L / moleculeStarEnergy S X a) * (C * L / moleculeStarEnergy S X b)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by dsimp only [C, L]; ring

/-- The complete-prefix off-diagonal signed centre-Gram row has the
coherent K^2/sqrt X scale, with no free collision or coefficient assumptions. -/
theorem eventually_powerRange_signedExteriorCentre_gramRow_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∀ a : MoleculeCenter S X K,
      let g := fun c : PrimeStar.Vertex S X ↦
        PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X c)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X c))
      ∑ b ∈ Finset.univ.erase a,
        ∑ v ∈ Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
            ¬∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)),
          |g a.1 v * g b.1 v| ≤
            (128 / Real.log 2) * (20000 / Real.log 2) ^ 2 *
              (K : ℝ) ^ 2 * Real.log (X : ℝ) ^ 4 / Real.sqrt (X : ℝ) := by
  filter_upwards [eventually_powerRange_signedExteriorCentre_pair_sum_le S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_ge_atTop 2] with X hpair hscale hX
  intro K hK a g
  let C := (16 / Real.log 2) * (20000 / Real.log 2) ^ 2
  let L := Real.log (X : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hwindow (b : MoleculeCenter S X K) : InPowerRange theta X (b.1 : ℕ) :=
    ⟨PrimeStar.Vertex.coe_pos b.1, (by exact_mod_cast b.2 : (b.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
  have hinv (b : MoleculeCenter S X K) :
      1 / moleculeStarEnergy S X b.1 ^ 2 ≤ 8 * (K : ℝ) * L / (X : ℝ) := by
    have hb : 0 < (b.1 : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos b.1
    calc
      _ ≤ 1 / ((X : ℝ) / (8 * (b.1 : ℝ) * L)) :=
        one_div_le_one_div_of_le (by positivity) (hscale b.1 (hwindow b)).1
      _ = 8 * (b.1 : ℝ) * L / (X : ℝ) := by field_simp
      _ ≤ _ := by gcongr; exact_mod_cast b.2
  have hinvPair (b : MoleculeCenter S X K) :
      1 / (moleculeStarEnergy S X a.1 * moleculeStarEnergy S X b.1) ≤
        8 * (K : ℝ) * L / (X : ℝ) := by
    have haInv := hinv a
    have hbInv := hinv b
    have hs := sq_nonneg ((moleculeStarEnergy S X a.1)⁻¹ - (moleculeStarEnergy S X b.1)⁻¹)
    rw [one_div, ← inv_pow] at haInv hbInv
    rw [one_div, mul_inv]
    nlinarith
  have hY : (squareRootCutoff X : ℝ) / (X : ℝ) ≤ 1 / Real.sqrt (X : ℝ) := by
    have hsqrt : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hx
    apply (div_le_iff₀ hx).mpr
    have hcut : (squareRootCutoff X : ℝ) ≤ Real.sqrt (X : ℝ) := Real.nat_sqrt_le_real_sqrt
    have hsq := Real.sq_sqrt hx.le
    have heq : (1 / Real.sqrt (X : ℝ)) * (X : ℝ) = Real.sqrt (X : ℝ) := by
      calc
        _ = (X : ℝ) / Real.sqrt (X : ℝ) := by ring
        _ = _ := (div_eq_iff hsqrt.ne').mpr (by nlinarith only [hsq])
    rw [heq]
    exact hcut
  calc
    _ ≤ ∑ _b ∈ Finset.univ.erase a, 8 * C * (K : ℝ) * L ^ 4 / Real.sqrt (X : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hab : a.1 ≠ b.1 := fun h ↦ (Finset.mem_erase.mp hb).1 (Subtype.ext h.symm)
      apply (hpair a.1 b.1 (hwindow a) (hwindow b) hab).trans
      calc
        _ = (C * (squareRootCutoff X : ℝ) * L ^ 3) *
            (1 / (moleculeStarEnergy S X a.1 * moleculeStarEnergy S X b.1)) := by dsimp [C, L]; ring
        _ ≤ (C * (squareRootCutoff X : ℝ) * L ^ 3) * (8 * (K : ℝ) * L / (X : ℝ)) :=
          mul_le_mul_of_nonneg_left (hinvPair b) (by positivity)
        _ = (8 * C * (K : ℝ) * L ^ 4) * ((squareRootCutoff X : ℝ) / (X : ℝ)) := by ring
        _ ≤ (8 * C * (K : ℝ) * L ^ 4) * (1 / Real.sqrt (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hY (by positivity)
        _ = _ := by ring
    _ = ((Finset.univ.erase a).card : ℝ) * (8 * C * (K : ℝ) * L ^ 4 / Real.sqrt (X : ℝ)) := by simp
    _ ≤ (K : ℝ) * (8 * C * (K : ℝ) * L ^ 4 / Real.sqrt (X : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_le_univ (Finset.univ.erase a)).trans (card_moleculeCenter_le S X K)
    _ = _ := by dsimp only [C, L]; ring

end ResidualCentreGram

section SignedResidualOperator

open Filter Topology
open scoped Classical

/-- Signed exterior diagonal, retaining the actual compression support. -/
theorem signedExterior_sq_le_degreeWeightedInterior
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hX : 2 ≤ X) :
    let g := PrimeStar.euclideanCoordinateComplementProjection
      (exactPrincipalMoleculeSupport S X a)
      (Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeSignedInteriorVector S X a))
    ‖g‖ ^ 2 ≤
      (2 * Real.log (X : ℝ) / Real.log 2) *
        ∑ w : PrimeStar.Vertex S X,
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).degree w : ℝ) *
            (exactPrincipalMoleculeSignedInteriorVector S X a w) ^ 2 := by
  intro g
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let y := exactPrincipalMoleculeSignedInteriorVector S X a
  let R := 2 * Real.log (X : ℝ) / Real.log 2
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have homega (w : PrimeStar.Vertex S X) :
      ((w : ℕ).primeFactors.card : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
    apply (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos w)).trans
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    exact Real.log_le_log (by exact_mod_cast PrimeStar.Vertex.coe_pos w)
      (by exact_mod_cast PrimeStar.Vertex.coe_le w)
  have hy : ∀ w, w ∉ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a → y w = 0 := by
    intro w hw
    exact PrimeStar.firstExitStarResolventVector_eq_zero_of_not_mem
      (exactPrincipalMoleculeSignedInteriorSource S X a) hw
  have hpoint (v : PrimeStar.Vertex S X) :
      (g v) ^ 2 ≤ R * ∑ w ∈ G.neighborFinset v, (y w) ^ 2 := by
    by_cases hv : v ∈ exactPrincipalMoleculeSupport S X a
    · rw [show g v = 0 by simp [g, PrimeStar.euclideanCoordinateComplementProjection_apply, hv]]
      simpa using mul_nonneg hR (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg (y _)))
    · have hvB : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a :=
        fun h ↦ hv (Finset.mem_union_left _ h)
      dsimp only [g]
      rw [PrimeStar.euclideanCoordinateComplementProjection_apply, if_neg hv]
      apply (exterior_firstExit_apply_sq_le_weighted_neighbors hS ha hvB y hy).trans
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
      dsimp [R]
      have h1 := homega a
      have h2 := homega v
      calc
        _ ≤ Real.log (X : ℝ) / Real.log 2 + Real.log (X : ℝ) / Real.log 2 :=
          add_le_add h1 h2
        _ = _ := by ring
  have hswap : ∑ v : PrimeStar.Vertex S X, ∑ w ∈ G.neighborFinset v, (y w) ^ 2 =
      ∑ w : PrimeStar.Vertex S X, (G.degree w : ℝ) * (y w) ^ 2 := by
    simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    simp_rw [G.adj_comm _ w]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ v : PrimeStar.Vertex S X, R * ∑ w ∈ G.neighborFinset v, (y w) ^ 2 :=
      Finset.sum_le_sum (fun v _ ↦ hpoint v)
    _ = _ := by rw [← Finset.mul_sum, hswap]

/-- The signed exterior diagonal has a uniform logarithmic bound. -/
theorem eventually_powerRange_signedExterior_sq_le_logFifth
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
      let g := PrimeStar.euclideanCoordinateComplementProjection
        (exactPrincipalMoleculeSupport S X a)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeSignedInteriorVector S X a))
      ‖g‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 5 := by
  obtain ⟨C, hC, hbound⟩ := eventually_powerRange_signedDegreeWeighted_le_logFourth S hS htheta
  refine ⟨2 * C / Real.log 2, by positivity, ?_⟩
  filter_upwards [hbound, eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 2] with X hb hw hX
  intro a ha g
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  calc
    _ ≤ _ := signedExterior_sq_le_degreeWeightedInterior hS (hw a ha).1 hX
    _ ≤ (2 * Real.log (X : ℝ) / Real.log 2) * (C * Real.log (X : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left (hb a ha) (by positivity)
    _ = _ := by ring

/-- The diagonal and the two complementary off-diagonal rows assemble on the
complete prefix; the coherent contribution is retained as K^2/sqrt X. -/
theorem eventually_powerRange_signedExterior_absoluteGramRow_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X → ∀ a : MoleculeCenter S X K,
      let g := fun c : PrimeStar.Vertex S X ↦
        PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X c)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X c))
      ∑ b : MoleculeCenter S X K, ∑ v : PrimeStar.Vertex S X,
        |g a.1 v * g b.1 v| ≤
          C * Real.log (X : ℝ) ^ 5 * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
  obtain ⟨Cd, hCd, hd⟩ := eventually_powerRange_signedExterior_sq_le_logFifth S hS htheta
  let Cl : ℝ := 128 * (4000 / Real.log 2) ^ 2
  let Cc : ℝ := (128 / Real.log 2) * (20000 / Real.log 2) ^ 2
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨Cd + Cl + Cc, by positivity, ?_⟩
  filter_upwards [hd, eventually_powerRange_signedExteriorLeaf_gramRow_le S hS htheta,
    eventually_powerRange_signedExteriorCentre_gramRow_le S hS htheta,
    eventually_ge_atTop 2, hlogTop.eventually_ge_atTop 1] with X hd hl hc hX hL
  intro K hK a g
  let L := Real.log (X : ℝ)
  let leaf := fun v : PrimeStar.Vertex S X ↦
    ∃ p : ℕ, p.Prime ∧ squareRootCutoff X < p ∧ p ∣ (v : ℕ)
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsqrt : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hx
  have hKs : (K : ℝ) ≤ Real.sqrt (X : ℝ) := by
    apply hK.trans
    dsimp [powerScale]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ X by omega)) htheta.le
  have hleafScale : (K : ℝ) ^ 3 / (X : ℝ) ≤ (K : ℝ) ^ 2 / Real.sqrt (X : ℝ) := by
    apply (div_le_div_iff₀ hx hsqrt).mpr
    have hsq := Real.sq_sqrt hx.le
    have h := mul_le_mul_of_nonneg_left hKs (show 0 ≤ (K : ℝ) ^ 2 * Real.sqrt (X : ℝ) by positivity)
    nlinarith only [h, hsq]
  have hdiag : (∑ v : PrimeStar.Vertex S X, |g a.1 v * g a.1 v|) ≤ Cd * L ^ 5 := by
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨PrimeStar.Vertex.coe_pos a.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
    simpa only [EuclideanSpace.real_norm_sq_eq, ← sq, abs_pow, sq_abs] using hd a.1 ha
  have hsplit (b : MoleculeCenter S X K) :
      (∑ v : PrimeStar.Vertex S X, |g a.1 v * g b.1 v|) =
        (∑ v ∈ Finset.univ.filter leaf, |g a.1 v * g b.1 v|) +
        (∑ v ∈ Finset.univ.filter (fun v ↦ ¬leaf v), |g a.1 v * g b.1 v|) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : leaf v <;> simp [hv]
  have hleaf : (∑ b ∈ Finset.univ.erase a,
      ∑ v ∈ Finset.univ.filter leaf, |g a.1 v * g b.1 v|) ≤
        Cl * (K : ℝ) ^ 2 * L ^ 4 / Real.sqrt (X : ℝ) := by
    calc
      _ ≤ ∑ b : MoleculeCenter S X K,
          ∑ v ∈ Finset.univ.filter leaf, |g a.1 v * g b.1 v| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
      _ ≤ Cl * (K : ℝ) ^ 3 * L ^ 4 / (X : ℝ) := hl K hK a
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hleafScale (show 0 ≤ Cl * L ^ 4 by positivity) using 1 <;>
          first | rfl | ring
  have hcentre := hc K hK a
  change (∑ b ∈ Finset.univ.erase a,
    ∑ v ∈ Finset.univ.filter (fun v ↦ ¬leaf v), |g a.1 v * g b.1 v|) ≤
      Cc * (K : ℝ) ^ 2 * L ^ 4 / Real.sqrt (X : ℝ) at hcentre
  have hpow : L ^ 4 ≤ L ^ 5 := pow_le_pow_right₀ hL (by omega)
  calc
    _ = (∑ v, |g a.1 v * g a.1 v|) + ∑ b ∈ Finset.univ.erase a,
        ∑ v, |g a.1 v * g b.1 v| :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
    _ ≤ Cd * L ^ 5 +
        (Cl * (K : ℝ) ^ 2 * L ^ 4 / Real.sqrt (X : ℝ) +
         Cc * (K : ℝ) ^ 2 * L ^ 4 / Real.sqrt (X : ℝ)) := by
      apply add_le_add hdiag
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      exact add_le_add hleaf hcentre
    _ = Cd * L ^ 5 + (Cl + Cc) * ((K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) * L ^ 4 := by ring
    _ ≤ Cd * L ^ 5 + (Cl + Cc) * ((K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) * L ^ 5 := by gcongr
    _ ≤ _ := by
      have hratio : 0 ≤ (K : ℝ) ^ 2 / Real.sqrt (X : ℝ) := by positivity
      dsimp only [L]
      have hL0 : 0 ≤ Real.log (X : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans hL
      nlinarith [mul_nonneg hCd.le hratio, mul_nonneg (add_nonneg hCl hCc) (pow_nonneg hL0 5),
        mul_nonneg (mul_nonneg hCd.le hratio) (pow_nonneg hL0 5)]

private theorem symmetric_l2_opNorm_le_weightedAbsoluteRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, A i j = A j i) (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, |A i j| * w j ≤ C * w i) : ‖A‖ ≤ C := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
  have hTsymm : (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι).IsSymmetric := by
    change (Matrix.toEuclideanLin A).IsSymmetric
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext fun i j ↦ hA j i
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  rw [T.norm_eq_iSup_rayleighQuotient hTsymm]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx, hC]
  · rw [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply]
    have hquad := PrimeStar.abs_dotProduct_mulVec_le_of_weighted_row
      (fun i j ↦ |A i j|) w (fun i ↦ |x i|) C
      (fun _ _ ↦ abs_nonneg _) (fun i j ↦ congrArg abs (hA i j)) hw hrow
    have hdom : |dotProduct (fun i ↦ x i) (A.mulVec (fun i ↦ x i))| ≤
        |dotProduct (fun i ↦ |x i|) (Matrix.mulVec (fun i j ↦ |A i j|) (fun i ↦ |x i|))| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      calc
        _ ≤ ∑ i, ∑ j, |x i * (A i j * x j)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
            Finset.abs_sum_le_sum_abs _ _)
        _ = _ := by
          simp only [abs_mul]
          exact (abs_of_nonneg (show (0 : ℝ) ≤
            ∑ i, ∑ j, |x i| * (|A i j| * |x j|) by positivity)).symm
    have hinterReal : ⟪T x, x⟫_ℝ =
        dotProduct (fun i ↦ x i) (A.mulVec (fun i ↦ x i)) := by
      rw [real_inner_comm]
      simpa [T] using Matrix.inner_toEuclideanCLM A x x
    simp only [RCLike.re_to_real]
    rw [hinterReal, abs_div, abs_of_nonneg (sq_nonneg ‖x‖)]
    apply (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))).mpr
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [sq_abs] using hdom.trans hquad

private theorem symmetric_l2_opNorm_le_absoluteRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, A i j = A j i) (hrow : ∀ i, ∑ j, |A i j| ≤ C) :
    ‖A‖ ≤ C := by
  exact symmetric_l2_opNorm_le_weightedAbsoluteRow A (fun _ ↦ 1) C hC hA
    (fun _ ↦ by norm_num) (fun i ↦ by simpa using hrow i)

/-- Complete-prefix signed residual operator bound. This concerns the signed
exterior columns, before kernel restoration, projection and whitening. -/
theorem eventually_powerRange_signedExterior_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ := fun v a ↦
        PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X a.1)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeSignedInteriorVector S X a.1)) v
      ‖J‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 5 *
        (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := eventually_powerRange_signedExterior_absoluteGramRow_le S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrow, eventually_ge_atTop 1] with X hr hX
  intro K hK J
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self]
  apply symmetric_l2_opNorm_le_absoluteRow (J.conjTranspose * J) _ (by positivity)
  · intro a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro v _
    ring
  · intro a
    calc
      _ ≤ ∑ b : MoleculeCenter S X K, ∑ v : PrimeStar.Vertex S X,
          |J v a * J v b| := by
        apply Finset.sum_le_sum
        intro b _
        simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial] using
          Finset.abs_sum_le_sum_abs (fun v ↦ J v a * J v b) Finset.univ
      _ ≤ _ := hr K hK a

end SignedResidualOperator

noncomputable section ProjectedResidualOperator

open Filter Topology
open scoped Classical

private theorem rectangular_operatorNorm_sq_le_sum
    {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  let C := ∑ i, ∑ j, ‖A i j‖ ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hnorm : ‖A‖ ≤ Real.sqrt C := by
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hC]
    change ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ C * ‖x‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h : ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
          simpa only [norm_mul] using norm_sum_le (s := Finset.univ) (fun j ↦ A i j * x j)
        have hs := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ by positivity)).mpr h
        simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
        apply hs.trans
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ ‖A i j‖) (fun j ↦ ‖x j‖)
      _ = _ := by rw [← Finset.sum_mul]
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mpr hnorm
  simpa only [Real.sq_sqrt hC] using hs

private theorem rectangular_complexification_operatorNorm_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : matrixL2OperatorNorm (complexifyRealMatrix A) ≤ 2 * ‖A‖ := by
  let T := (Matrix.toEuclideanLin (𝕜 := ℂ) (m := m) (n := n)).trans
    LinearMap.toContinuousLinearMap (complexifyRealMatrix A)
  have hmap (x : EuclideanSpace ℝ n) :
      Matrix.toEuclideanLin (complexifyRealMatrix A) (PrimeStar.complexifyEuclidean x) =
        PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin A x) := by
    ext i
    simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      complexifyRealMatrix_apply, PrimeStar.complexifyEuclidean_apply]
    push_cast
    rfl
  change ‖T‖ ≤ 2 * ‖A‖
  apply T.opNorm_le_bound (by positivity)
  intro x
  have hre : ‖complexEuclideanRealPart x‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change (x i).re ^ 2 ≤ ‖x i‖ ^ 2
    nlinarith [Complex.sq_norm_sub_sq_re (x i), sq_nonneg (x i).im]
  have him : ‖complexEuclideanImagPart x‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change (x i).im ^ 2 ≤ ‖x i‖ ^ 2
    nlinarith [Complex.sq_norm_sub_sq_im (x i), sq_nonneg (x i).re]
  have hsplit : T x =
      PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin A (complexEuclideanRealPart x)) +
        Complex.I • PrimeStar.complexifyEuclidean
          (Matrix.toEuclideanLin A (complexEuclideanImagPart x)) := by
    change Matrix.toEuclideanLin (complexifyRealMatrix A) x = _
    conv_lhs => rw [← complexify_realPart_add_I_imagPart x]
    rw [map_add, map_smul, hmap, hmap]
  rw [hsplit]
  calc
    _ ≤ ‖Matrix.toEuclideanLin A (complexEuclideanRealPart x)‖ +
        ‖Matrix.toEuclideanLin A (complexEuclideanImagPart x)‖ := by
      simpa only [norm_smul, Complex.norm_I, one_mul, PrimeStar.norm_complexifyEuclidean] using
        norm_add_le (PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin A (complexEuclideanRealPart x)))
          (Complex.I • PrimeStar.complexifyEuclidean (Matrix.toEuclideanLin A (complexEuclideanImagPart x)))
    _ ≤ ‖A‖ * ‖complexEuclideanRealPart x‖ + ‖A‖ * ‖complexEuclideanImagPart x‖ :=
      add_le_add (A.l2_opNorm_mulVec (complexEuclideanRealPart x))
        (A.l2_opNorm_mulVec (complexEuclideanImagPart x))
    _ ≤ ‖A‖ * ‖x‖ + ‖A‖ * ‖x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hre (norm_nonneg A))
        (mul_le_mul_of_nonneg_left him (norm_nonneg A))
    _ = _ := by ring

/-- The kernel exterior residual retains a/X before prefix summation. -/
theorem eventually_powerRange_kernelExterior_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
      let g := PrimeStar.euclideanCoordinateComplementProjection
        (exactPrincipalMoleculeSupport S X a)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
          (exactPrincipalMoleculeKernelInteriorVector S X a))
      ‖g‖ ^ 2 ≤ C * (a : ℝ) * Real.log (X : ℝ) ^ 3 / (X : ℝ) := by
  obtain ⟨Ck, hCk, hk⟩ :=
    eventually_powerRange_exactPrincipalMoleculeBoundaryKernel_sq_le_scale S hS htheta
  let Ch := 4 * PrimeStar.sqrtCutoffResidualConstant ^ 2
  have hCh : 0 < Ch := mul_pos (by norm_num)
    (sq_pos_of_pos PrimeStar.sqrtCutoffResidualConstant_pos)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨Ch * Ck, by positivity, ?_⟩
  filter_upwards [hk, eventually_powerRange_negativeCoefficient_and_kernelResponse_bound S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned,
    PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 2] with X hkX hr hH he hL hX
  intro a ha g
  let eta := PrimeStar.sqrtCutoffResidualScale X
  have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
    (PrimeStar.tunedSchurScale_nonneg _)
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hs : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hx
  have hL0 : 0 ≤ Real.log (X : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans hL
  have hetaSq : eta ^ 2 ≤ Ch * Real.sqrt (X : ℝ) := by
    apply he.trans
    dsimp [Ch]
    gcongr
    exact div_le_self (Real.sqrt_nonneg _) hL
  have hnorm : ‖g‖ ≤ eta * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ := by
    apply (PrimeStar.norm_euclideanCoordinateComplementProjection_le _ _).trans
    apply (show ‖Matrix.toEuclideanLin
        ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
        (exactPrincipalMoleculeKernelInteriorVector S X a)‖ ≤
        eta * ‖exactPrincipalMoleculeKernelInteriorVector S X a‖ by
      simpa [eta, PrimeStar.sqrtCutoffResidualScale, PrimeStar.sqrtCutoffResidualConstant] using
        hH S (exactPrincipalMoleculeKernelInteriorVector S X a)).trans
    exact mul_le_mul_of_nonneg_left (hr a ha).2 heta
  calc
    _ ≤ eta ^ 2 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ ^ 2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
    _ ≤ (Ch * Real.sqrt (X : ℝ)) *
        (Ck * (a : ℝ) * Real.log (X : ℝ) ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ))) :=
      mul_le_mul hetaSq (hkX a ha) (sq_nonneg _) (by positivity)
    _ = _ := by field_simp

/-- The adjacency-on-tail bound retains a/sqrt X for the operator consumer. -/
theorem eventually_powerRange_adjacency_discardedFullMolecule_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a : PrimeStar.Vertex S X, InPowerRange theta X (a : ℕ) →
        ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
          (Matrix.toEuclideanLin (oneExitComplementProjection S X)
            (phasedFullStarMolecule S X a))‖ ^ 2 ≤ C * (a : ℝ) * Real.log (X : ℝ) ^ 3 / Real.sqrt (X : ℝ) := by
  obtain ⟨Ct, hCt, htail⟩ := eventually_powerRange_discardedFullMolecule_sq_le_scale S hS htheta
  let Ch := 16 * PrimeStar.sqrtCutoffResidualConstant ^ 2
  have hCh : 0 < Ch := mul_pos (by norm_num)
    (sq_pos_of_pos PrimeStar.sqrtCutoffResidualConstant_pos)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨Ch * Ct * (1 + 1 / Real.log 2), by positivity, ?_⟩
  filter_upwards [htail, eventually_oneExitSmallPrime_apply_sq_le_sqrt S,
    eventually_powerRange_largePrime_discardedFullMolecule_eq_zero S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 4] with X ht hH hz hw hL hX
  intro a ha
  let L := Real.log (X : ℝ)
  let Z := Matrix.toEuclideanLin (oneExitComplementProjection S X)
    (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a))
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsqrt : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hx
  have hsqrtSq : Real.sqrt (X : ℝ) ^ 2 = (X : ℝ) := Real.sq_sqrt hx.le
  have hlog : 0 < L := by dsimp [L]; linarith
  have haPos : 0 < (a : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_pos a
  have haX : (a : ℝ) ≤ (X : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_le a
  have haSqrt : (a : ℝ) ≤ Real.sqrt (X : ℝ) := by
    have h : (a : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast (hw a ha).1
    exact h.trans Real.nat_sqrt_le_real_sqrt
  have homega : ((a : ℕ).primeFactors.card : ℝ) ≤ L / Real.log 2 :=
    (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos a)).trans
      (div_le_div_of_nonneg_right (Real.log_le_log haPos haX) hlogTwo.le)
  have hscalar : Real.sqrt (X : ℝ) *
      ((a : ℝ) * L ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ)) +
        (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L / (X : ℝ) ^ 2) ≤
      (1 + 1 / Real.log 2) * ((a : ℝ) / Real.sqrt (X : ℝ)) * L ^ 3 := by
    have har : (a : ℝ) / Real.sqrt (X : ℝ) ≤ 1 := (div_le_one hsqrt).mpr haSqrt
    have har0 : 0 ≤ (a : ℝ) / Real.sqrt (X : ℝ) := by positivity
    have har3 : ((a : ℝ) / Real.sqrt (X : ℝ)) ^ 3 ≤
        (a : ℝ) / Real.sqrt (X : ℝ) := by
      have hsq := pow_le_pow_left₀ har0 har 2
      have h := mul_le_mul_of_nonneg_left hsq har0
      nlinarith
    have harX : (a : ℝ) / (X : ℝ) ≤ (a : ℝ) / Real.sqrt (X : ℝ) := by
      apply div_le_div_of_nonneg_left haPos.le hsqrt
      have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
      nlinarith [sq_nonneg (Real.sqrt (X : ℝ) - 1)]
    calc
      _ = ((a : ℝ) / (X : ℝ)) * L ^ 3 +
          ((a : ℝ) / Real.sqrt (X : ℝ)) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L := by
        rw [← hsqrtSq]
        simp only [Real.sqrt_sq hsqrt.le]
        field_simp
      _ ≤ ((a : ℝ) / Real.sqrt (X : ℝ)) * L ^ 3 +
          ((a : ℝ) / Real.sqrt (X : ℝ)) * ((a : ℕ).primeFactors.card : ℝ) * L := by
        exact add_le_add (mul_le_mul_of_nonneg_right harX (pow_nonneg hlog.le 3))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right har3 (by positivity)) hlog.le)
      _ ≤ ((a : ℝ) / Real.sqrt (X : ℝ)) * L ^ 3 +
          ((a : ℝ) / Real.sqrt (X : ℝ)) * (L / Real.log 2) * L := by gcongr
      _ ≤ ((a : ℝ) / Real.sqrt (X : ℝ)) * L ^ 3 +
          ((a : ℝ) / Real.sqrt (X : ℝ)) * (L ^ 3 / Real.log 2) := by
        have hp : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by omega)
        have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hlogTwo.le) har0
        convert add_le_add_left h (((a : ℝ) / Real.sqrt (X : ℝ)) * L ^ 3) using 1 <;>
          first | rfl | ring
      _ = _ := by ring
  have hAZ : Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) Z =
      Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X) Z := by
    rw [moleculeFamilyComplexAdjacency_eq_large_add_small, map_add, LinearMap.add_apply]
    rw [show Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) Z = 0 from hz a ha, zero_add]
  have hphase : ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
      (Matrix.toEuclideanLin (oneExitComplementProjection S X)
        (phasedFullStarMolecule S X a))‖ =
      ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) Z‖ := by
    simp only [phasedFullStarMolecule, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_fullStarMoleculePhase, one_mul, Z]
  rw [hphase, hAZ]
  calc
    _ ≤ Ch * Real.sqrt (X : ℝ) * ‖Z‖ ^ 2 := hH Z
    _ ≤ Ch * Real.sqrt (X : ℝ) * (Ct *
        ((a : ℝ) * L ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ)) +
          (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L / (X : ℝ) ^ 2)) := by
      gcongr
      exact ht a ha
    _ = Ch * Ct * (Real.sqrt (X : ℝ) *
        ((a : ℝ) * L ^ 3 / ((X : ℝ) * Real.sqrt (X : ℝ)) +
          (a : ℝ) ^ 3 * ((a : ℕ).primeFactors.card : ℝ) * L / (X : ℝ) ^ 2)) := by ring
    _ ≤ Ch * Ct * ((1 + 1 / Real.log 2) * ((a : ℝ) / Real.sqrt (X : ℝ)) * L ^ 3) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by dsimp [L]; ring
/-- The kernel exterior matrix is controlled by its column-square sum,
retaining K^2/X rather than paying a constant for every source. -/
theorem eventually_powerRange_kernelExterior_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ := fun v a ↦
        PrimeStar.euclideanCoordinateComplementProjection
          (exactPrincipalMoleculeSupport S X a.1)
          (Matrix.toEuclideanLin
            ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ)
            (exactPrincipalMoleculeKernelInteriorVector S X a.1)) v
      ‖J‖ ^ 2 ≤ C * (K : ℝ) ^ 2 * Real.log (X : ℝ) ^ 3 / (X : ℝ) := by
  obtain ⟨C, hC, hcol⟩ := eventually_powerRange_kernelExterior_sq_le_scale S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcol, eventually_ge_atTop 1] with X hc hX
  intro K hK J
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  calc
    _ ≤ ∑ v, ∑ a, ‖J v a‖ ^ 2 := rectangular_operatorNorm_sq_le_sum J
    _ = ∑ a : MoleculeCenter S X K, ∑ v : PrimeStar.Vertex S X, (J v a) ^ 2 := by
      rw [Finset.sum_comm]
      simp only [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ _a : MoleculeCenter S X K, C * (K : ℝ) * Real.log (X : ℝ) ^ 3 / (X : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have ha : InPowerRange theta X (a.1 : ℕ) :=
        ⟨PrimeStar.Vertex.coe_pos a.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
      have h := hc a.1 ha
      dsimp only at h
      rw [EuclideanSpace.real_norm_sq_eq] at h
      apply h.trans
      gcongr
      exact_mod_cast a.2
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) *
        (C * (K : ℝ) * Real.log (X : ℝ) ^ 3 / (X : ℝ)) := by simp
    _ ≤ (K : ℝ) * (C * (K : ℝ) * Real.log (X : ℝ) ^ 3 / (X : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_moleculeCenter_le S X K) (by positivity)
    _ = _ := by ring

/-- Restoring the actual kernel leaves the complete raw full-molecule
residual at the same coherent operator scale. -/
theorem eventually_powerRange_fullMoleculeResidual_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
        fun v a ↦ exactPrincipalMoleculeResidual S X a.1 v
      ‖J‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 5 * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
  obtain ⟨Cs, hCs, hs⟩ := eventually_powerRange_signedExterior_operatorNorm_sq_le S hS htheta
  obtain ⟨Ck, hCk, hk⟩ := eventually_powerRange_kernelExterior_operatorNorm_sq_le S hS htheta
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨2 * (Cs + Ck), by positivity, ?_⟩
  filter_upwards [hs, hk, eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitNonresonant S hS htheta,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 2] with X hs hk hw hg hn hL hX
  intro K hK J
  let exterior := fun (y : PrimeStar.Vertex S X → MoleculeAmbient S X) ↦
    (fun v (a : MoleculeCenter S X K) ↦
      PrimeStar.euclideanCoordinateComplementProjection (exactPrincipalMoleculeSupport S X a.1)
        (Matrix.toEuclideanLin
          ((PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).adjMatrix ℝ) (y a.1)) v :
        Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ)
  let Js : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
    exterior (exactPrincipalMoleculeSignedInteriorVector S X)
  let Jk : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
    exterior (exactPrincipalMoleculeKernelInteriorVector S X)
  have heq : J = Js + Jk := by
    ext v a
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨PrimeStar.Vertex.coe_pos a.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
    obtain ⟨haY, hd, hshift⟩ := hw a.1 ha
    have hmu : 0 < moleculeStarEnergy S X a.1 := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have hroot : exactPrincipalMoleculeRoot S X a.1 ≠ 0 := by
      have h := (abs_le.mp hshift).1
      exact ne_of_gt (by linarith)
    have hsplit := exactPrincipalMoleculeInteriorVector_eq_signed_add_kernel hS haY hroot
      (moleculeStarEnergy S X a.1 / 100) (by positivity) (hg a.1 ha) (hn a.1 ha)
    change exactPrincipalMoleculeResidual S X a.1 v = _
    rw [exactPrincipalMoleculeResidual_eq_exterior_smallPrime_interior hS haY, hsplit]
    simp only [map_add, PiLp.add_apply]
    rfl
  have hks : ‖Jk‖ ^ 2 ≤ Ck * Real.log (X : ℝ) ^ 5 *
      (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
    apply (hk K hK).trans
    have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hsq : Real.sqrt (X : ℝ) ≤ (X : ℝ) := by
      have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
      nlinarith [Real.sq_sqrt hx.le, sq_nonneg (Real.sqrt (X : ℝ) - 1)]
    have hratio : (K : ℝ) ^ 2 / (X : ℝ) ≤ (K : ℝ) ^ 2 / Real.sqrt (X : ℝ) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.mpr hx) hsq
    have hp : Real.log (X : ℝ) ^ 3 ≤ Real.log (X : ℝ) ^ 5 := pow_le_pow_right₀ hL (by omega)
    have hL0 : 0 ≤ Real.log (X : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans hL
    calc
      _ = Ck * Real.log (X : ℝ) ^ 3 * ((K : ℝ) ^ 2 / (X : ℝ)) := by ring
      _ ≤ Ck * Real.log (X : ℝ) ^ 5 * ((K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by gcongr
      _ ≤ _ := by gcongr; linarith
  have hsn := hs K hK
  change ‖Js‖ ^ 2 ≤ _ at hsn
  have hsum : ‖J‖ ^ 2 ≤ 2 * (‖Js‖ ^ 2 + ‖Jk‖ ^ 2) := by
    rw [heq]
    have h := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg Js) (norm_nonneg Jk))).mpr
      (norm_add_le Js Jk)
    nlinarith [sq_nonneg (‖Js‖ - ‖Jk‖)]
  apply hsum.trans
  convert mul_le_mul_of_nonneg_left (add_le_add hsn hks) (by norm_num : (0 : ℝ) ≤ 2) using 1
  first | rfl | ring

/-- Adjacency acting on the actual complete discarded frame is small at
the collective operator scale, by the retained per-source tail factor. -/
theorem eventually_powerRange_adjacency_fullStarFrameTail_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixL2OperatorNorm (moleculeFamilyComplexAdjacency S X * fullStarFrameTail S X K) ^ 2 ≤
        C * (K : ℝ) ^ 2 * Real.log (X : ℝ) ^ 3 / Real.sqrt (X : ℝ) := by
  obtain ⟨C, hC, hcol⟩ := eventually_powerRange_adjacency_discardedFullMolecule_sq_le_scale S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcol, eventually_ge_atTop 1] with X hc hX
  intro K hK
  let E := moleculeFamilyComplexAdjacency S X * fullStarFrameTail S X K
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hentry (v : PrimeStar.Vertex S X) (a : MoleculeCenter S X K) :
      E v a = (Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
        (Matrix.toEuclideanLin (oneExitComplementProjection S X) (phasedFullStarMolecule S X a.1))) v := by
    simp only [E, fullStarFrameTail, oneExitComplementProjection, phasedFullStarFrame,
      Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  change ‖E‖ ^ 2 ≤ _
  calc
    _ ≤ ∑ v, ∑ a, ‖E v a‖ ^ 2 := rectangular_operatorNorm_sq_le_sum E
    _ = ∑ a : MoleculeCenter S X K,
        ‖Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
          (Matrix.toEuclideanLin (oneExitComplementProjection S X) (phasedFullStarMolecule S X a.1))‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [hentry, EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ _a : MoleculeCenter S X K,
        C * (K : ℝ) * Real.log (X : ℝ) ^ 3 / Real.sqrt (X : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have ha : InPowerRange theta X (a.1 : ℕ) :=
        ⟨PrimeStar.Vertex.coe_pos a.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
      apply (hc a.1 ha).trans
      gcongr
      exact_mod_cast a.2
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) *
        (C * (K : ℝ) * Real.log (X : ℝ) ^ 3 / Real.sqrt (X : ℝ)) := by simp
    _ ≤ (K : ℝ) * (C * (K : ℝ) * Real.log (X : ℝ) ^ 3 / Real.sqrt (X : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_moleculeCenter_le S X K) (by positivity)
    _ = _ := by ring

/-- The phase-fixed complex residual inherits the real raw operator bound;
unit phases do not accumulate with the number of columns. -/
theorem eventually_powerRange_phasedFullStarFrameResidual_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixL2OperatorNorm
        (moleculeFamilyComplexAdjacency S X * phasedFullStarFrame S X K -
          phasedFullStarFrame S X K * complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)) ^ 2 ≤
        C * Real.log (X : ℝ) ^ 5 * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
  obtain ⟨C, hC, hraw⟩ := eventually_powerRange_fullMoleculeResidual_operatorNorm_sq_le S hS htheta
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [hraw] with X hr
  intro K hK
  let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
    fun v a ↦ exactPrincipalMoleculeResidual S X a.1 v
  let D : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
    Matrix.diagonal fun a ↦ (fullStarMoleculePhase S X a.1 : ℂ)
  have hD : ‖D‖ ≤ 1 := by
    change ‖Matrix.diagonal (fun a : MoleculeCenter S X K ↦
      (fullStarMoleculePhase S X a.1 : ℂ))‖ ≤ 1
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro a
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_fullStarMoleculePhase, le_refl]
  have hcol (a : MoleculeCenter S X K) :
      Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) (phasedFullStarMolecule S X a.1) -
        (exactPrincipalMoleculeRoot S X a.1 : ℂ) • phasedFullStarMolecule S X a.1 =
      (fullStarMoleculePhase S X a.1 : ℂ) •
        PrimeStar.complexifyEuclidean (exactPrincipalMoleculeResidual S X a.1) := by
    have hcomplex : Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
        (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a.1)) =
      PrimeStar.complexifyEuclidean (primeCoverAdjacencyOperator S X
        (exactPrincipalMoleculeAmbientVector S X a.1)) := by
      ext v
      simp only [moleculeFamilyComplexAdjacency, primeCoverAdjacencyOperator,
        Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
        complexifyRealMatrix_apply, PrimeStar.complexifyEuclidean_apply]
      push_cast
      rfl
    rw [phasedFullStarMolecule, map_smul, hcomplex, smul_comm
      (exactPrincipalMoleculeRoot S X a.1 : ℂ), ← smul_sub,
      ← PrimeStar.complexifyEuclidean_smul, ← PrimeStar.complexifyEuclidean_sub]
    rfl
  have heq : moleculeFamilyComplexAdjacency S X * phasedFullStarFrame S X K -
      phasedFullStarFrame S X K * complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K) =
      complexifyRealMatrix J * D := by
    ext v a
    have h := congrArg (fun x ↦ x v) (hcol a)
    simp only [Matrix.sub_apply, Matrix.mul_apply, phasedFullStarFrame,
      complexifyRealMatrix, exactMoleculeFamilyRootMatrix, Matrix.diagonal,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul, PrimeStar.complexifyEuclidean_apply] at h ⊢
    simpa [D, J, Matrix.diagonal, apply_ite, mul_comm] using h
  rw [heq]
  have hnorm : matrixL2OperatorNorm (complexifyRealMatrix J * D) ≤ 2 * ‖J‖ := by
    let JC : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ := complexifyRealMatrix J
    have hJC : ‖JC‖ ≤ 2 * ‖J‖ := rectangular_complexification_operatorNorm_le J
    change ‖JC * D‖ ≤ _
    calc
      _ ≤ ‖JC‖ * ‖D‖ := Matrix.l2_opNorm_mul JC D
      _ ≤ (2 * ‖J‖) * 1 := mul_le_mul hJC hD (norm_nonneg D) (by positivity)
      _ = _ := mul_one _
  have hs := (sq_le_sq₀ (by exact norm_nonneg _) (by positivity)).mpr hnorm
  have hb := hr K hK
  change ‖J‖ ^ 2 ≤ _ at hb
  nlinarith

/-- The actual projected, column-normalized full-star residual satisfies
the collective operator bound. Symmetric whitening is not part of this statement. -/
theorem eventually_powerRange_projectedFullStarFrameResidual_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
        matrixL2OperatorNorm (projectedFullStarFrameResidual S X K) ^ 2 ≤
          C * Real.log (X : ℝ) ^ 5 * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
  obtain ⟨Cr, hCr, hr⟩ := eventually_powerRange_phasedFullStarFrameResidual_operatorNorm_sq_le S hS htheta
  obtain ⟨Ct, hCt, ht⟩ := eventually_powerRange_adjacency_fullStarFrameTail_operatorNorm_sq_le S hS htheta
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨8 * (Cr + Ct), by positivity, ?_⟩
  filter_upwards [hr, ht, eventually_powerRange_projectedFullStarMolecule_norm_bounds S hS htheta,
    hlogTop.eventually_ge_atTop 1] with X hr ht hn hL
  intro K hK
  let P : Matrix (PrimeStar.Vertex S X) (PrimeStar.Vertex S X) ℂ := oneExitProjection S X
  let N := projectedFullStarNormalization S X K
  let R : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
    moleculeFamilyComplexAdjacency S X * phasedFullStarFrame S X K -
      phasedFullStarFrame S X K * complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)
  let T : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
    moleculeFamilyComplexAdjacency S X * fullStarFrameTail S X K
  have hP : ‖P‖ ≤ 1 := IsStarProjection.norm_le _ (oneExitProjection_isStarProjection S X)
  have hN : ‖N‖ ≤ 2 := by
    change ‖Matrix.diagonal (fun a : MoleculeCenter S X K ↦
      (‖projectedFullStarMolecule S X a.1‖⁻¹ : ℂ))‖ ≤ 2
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro a
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨PrimeStar.Vertex.coe_pos a.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
    have haN := (hn a.1 ha).1
    have hp : 0 < ‖projectedFullStarMolecule S X a.1‖ := by linarith
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hp).mpr (by linarith)
  have hnorm : matrixL2OperatorNorm (projectedFullStarFrameResidual S X K) ≤
      2 * (‖R‖ + ‖T‖) := by
    rw [projectedFullStarFrameResidual_eq]
    change ‖(P * R - P * T) * N‖ ≤ _
    calc
      _ ≤ ‖P * R - P * T‖ * ‖N‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖P * R‖ + ‖P * T‖) * 2 :=
        mul_le_mul (norm_sub_le _ _) hN (norm_nonneg N) (by positivity)
      _ ≤ (‖P‖ * ‖R‖ + ‖P‖ * ‖T‖) * 2 := by
        gcongr
        · exact Matrix.l2_opNorm_mul _ _
        · exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * ‖R‖ + 1 * ‖T‖) * 2 := by gcongr
      _ = _ := by ring
  have hR := hr K hK
  change ‖R‖ ^ 2 ≤ _ at hR
  have hT : ‖T‖ ^ 2 ≤ Ct * Real.log (X : ℝ) ^ 5 *
      (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
    apply (ht K hK).trans
    have hL0 : 0 ≤ Real.log (X : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans hL
    have hp : Real.log (X : ℝ) ^ 3 ≤ Real.log (X : ℝ) ^ 5 := pow_le_pow_right₀ hL (by omega)
    calc
      _ = Ct * Real.log (X : ℝ) ^ 3 * ((K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by ring
      _ ≤ Ct * Real.log (X : ℝ) ^ 5 * ((K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by gcongr
      _ ≤ _ := by gcongr; linarith
  have hs := (sq_le_sq₀ (by exact norm_nonneg _) (by positivity)).mpr hnorm
  have hsum : matrixL2OperatorNorm (projectedFullStarFrameResidual S X K) ^ 2 ≤
      8 * (‖R‖ ^ 2 + ‖T‖ ^ 2) := by nlinarith [sq_nonneg (‖R‖ - ‖T‖)]
  apply hsum.trans
  convert mul_le_mul_of_nonneg_left (add_le_add hR hT) (by norm_num : (0 : ℝ) ≤ 8) using 1
  first | rfl | ring

end ProjectedResidualOperator

noncomputable section ProjectedGramTransfer

open Filter Topology
open scoped Classical

/-- The full discarded mass of the actual phase-fixed prefix is small in
Hilbert--Schmidt norm. The down-star tail is retained before summing. -/
theorem eventually_powerRange_fullStarFrameTail_hsSq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
        matrixFrobeniusNorm (fullStarFrameTail S X K) ^ 2 ≤
          C * Real.log (X : ℝ) ^ 3 * (K : ℝ) ^ 2 / (X : ℝ) := by
  obtain ⟨Ct, hCt, htail⟩ :=
    eventually_powerRange_discardedFullMolecule_sq_le_scale S hS htheta
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨Ct * (1 + 1 / Real.log 2), by positivity, ?_⟩
  filter_upwards [htail, eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 4] with X ht hw hL hX
  intro K hK
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hxOne : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hL0 : 0 ≤ Real.log (X : ℝ) := by linarith
  have hsqrt : 1 ≤ Real.sqrt (X : ℝ) :=
    (Real.le_sqrt (by norm_num) hx.le).mpr (by simpa only [one_pow] using hxOne)
  have hcolumn (a : MoleculeCenter S X K) :
      (∑ v : PrimeStar.Vertex S X, ‖fullStarFrameTail S X K v a‖ ^ 2) ≤
        Ct * (1 + 1 / Real.log 2) * Real.log (X : ℝ) ^ 3 * (K : ℝ) / (X : ℝ) := by
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
    have hap : 0 < (a.1 : ℝ) := by exact_mod_cast a.1.property.1
    have haX : (a.1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast PrimeStar.Vertex.coe_le a.1
    have hasq : (a.1 : ℝ) ^ 2 ≤ (X : ℝ) := by
      have h : (a.1 : ℝ) ≤ Real.sqrt (X : ℝ) :=
        (show (a.1 : ℝ) ≤ (Nat.sqrt X : ℝ) by exact_mod_cast (hw a.1 ha).1).trans
          Real.nat_sqrt_le_real_sqrt
      nlinarith [Real.sq_sqrt hx.le]
    have homega : ((a.1 : ℕ).primeFactors.card : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 :=
      (primeFactors_card_le_log_div_log_two a.1.property.1).trans
        (div_le_div_of_nonneg_right (Real.log_le_log hap haX) hlogTwo.le)
    have ht1 : (a.1 : ℝ) * Real.log (X : ℝ) ^ 3 /
        ((X : ℝ) * Real.sqrt (X : ℝ)) ≤ (a.1 : ℝ) * Real.log (X : ℝ) ^ 3 / (X : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hx
      nlinarith
    have ht2 : (a.1 : ℝ) ^ 3 * ((a.1 : ℕ).primeFactors.card : ℝ) *
        Real.log (X : ℝ) / (X : ℝ) ^ 2 ≤
        (a.1 : ℝ) * Real.log (X : ℝ) ^ 3 / ((X : ℝ) * Real.log 2) := by
      calc
        _ = ((a.1 : ℝ) ^ 2 / (X : ℝ)) * ((a.1 : ℝ) / (X : ℝ)) *
            ((a.1 : ℕ).primeFactors.card : ℝ) * Real.log (X : ℝ) := by ring
        _ ≤ 1 * ((a.1 : ℝ) / (X : ℝ)) *
            (Real.log (X : ℝ) / Real.log 2) * Real.log (X : ℝ) := by
          gcongr
          exact (div_le_one hx).mpr hasq
        _ = ((a.1 : ℝ) / ((X : ℝ) * Real.log 2)) * Real.log (X : ℝ) ^ 2 := by ring
        _ ≤ ((a.1 : ℝ) / ((X : ℝ) * Real.log 2)) * Real.log (X : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (by positivity)
        _ = _ := by ring
    have heq : (∑ v : PrimeStar.Vertex S X, ‖fullStarFrameTail S X K v a‖ ^ 2) =
        ‖Matrix.toEuclideanLin (oneExitComplementProjection S X)
          (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a.1))‖ ^ 2 := by
      have hphase : ‖Matrix.toEuclideanLin (oneExitComplementProjection S X)
          (phasedFullStarMolecule S X a.1)‖ =
          ‖Matrix.toEuclideanLin (oneExitComplementProjection S X)
          (PrimeStar.complexifyEuclidean (exactPrincipalMoleculeAmbientVector S X a.1))‖ := by
        simp only [phasedFullStarMolecule, map_smul, norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_fullStarMoleculePhase, one_mul]
      rw [← hphase, EuclideanSpace.norm_sq_eq]
      rfl
    rw [heq]
    calc
      _ ≤ _ := ht a.1 ha
      _ ≤ Ct * ((a.1 : ℝ) * Real.log (X : ℝ) ^ 3 / (X : ℝ) +
          (a.1 : ℝ) * Real.log (X : ℝ) ^ 3 / ((X : ℝ) * Real.log 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) hCt.le
      _ = Ct * (1 + 1 / Real.log 2) * Real.log (X : ℝ) ^ 3 * (a.1 : ℝ) / (X : ℝ) := by ring
      _ ≤ _ := by gcongr; exact_mod_cast a.2
  rw [matrixFrobeniusNorm_sq, Finset.sum_comm]
  calc
    _ ≤ ∑ _a : MoleculeCenter S X K,
        Ct * (1 + 1 / Real.log 2) * Real.log (X : ℝ) ^ 3 * (K : ℝ) / (X : ℝ) :=
      Finset.sum_le_sum fun a _ ↦ hcolumn a
    _ = (Fintype.card (MoleculeCenter S X K) : ℝ) *
        (Ct * (1 + 1 / Real.log 2) * Real.log (X : ℝ) ^ 3 * (K : ℝ) / (X : ℝ)) := by simp
    _ ≤ (K : ℝ) *
        (Ct * (1 + 1 / Real.log 2) * Real.log (X : ℝ) ^ 3 * (K : ℝ) / (X : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_moleculeCenter_le S X K
    _ = _ := by ring

/-- The complete-prefix discarded mass tends uniformly to zero; no raw
Gram or independence hypothesis is used. -/
theorem eventually_powerRange_fullStarFrameTail_hsSq_lt
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixFrobeniusNorm (fullStarFrameTail S X K) ^ 2 < δ := by
  obtain ⟨C, hC, hb⟩ := eventually_powerRange_fullStarFrameTail_hsSq_le S hS htheta
  have hlim : Tendsto (fun X : ℕ ↦
      C * Real.log (X : ℝ) ^ 3 * powerScale theta X ^ 2 / (X : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero (3 : ℝ)
      (show theta * 2 < (1 : ℝ) by linarith)).const_mul C
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hx : 0 ≤ (X : ℝ) := by positivity
    rw [Real.rpow_mul hx, Real.rpow_two]
    simp [powerScale, mul_div_assoc]
    ring
  filter_upwards [hb, hlim.eventually_lt_const hδ, eventually_ge_atTop 1]
    with X hbX hsmall hX
  intro K hK
  apply (hbX K hK).trans_lt
  apply lt_of_le_of_lt _ hsmall
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  gcongr

private theorem discarded_column_sq_le_tail_hsSq
    (S : Finset ℕ) (X K : ℕ) (a : MoleculeCenter S X K) :
    ‖phasedFullStarMolecule S X a.1 - projectedFullStarMolecule S X a.1‖ ^ 2 ≤
      matrixFrobeniusNorm (fullStarFrameTail S X K) ^ 2 := by
  have hcol : (∑ v, ‖fullStarFrameTail S X K v a‖ ^ 2) =
      ‖phasedFullStarMolecule S X a.1 - projectedFullStarMolecule S X a.1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro v _
    have heq : fullStarFrameTail S X K v a =
        (phasedFullStarMolecule S X a.1 - projectedFullStarMolecule S X a.1) v := by
      unfold fullStarFrameTail
      rw [Matrix.sub_mul, Matrix.one_mul]
      rfl
    rw [heq]
  rw [← hcol, matrixFrobeniusNorm_sq, Finset.sum_comm]
  exact Finset.single_le_sum
    (f := fun b : MoleculeCenter S X K ↦
      ∑ v : PrimeStar.Vertex S X, ‖fullStarFrameTail S X K v b‖ ^ 2)
    (fun b _ ↦ Finset.sum_nonneg fun v _ ↦ sq_nonneg _)
    (Finset.mem_univ a)

/-- Column normalization changes the identity Gram by at most four times
the actual total discarded mass, not by a dimension-sized constant. -/
theorem eventually_powerRange_projectedFullStarNormalization_gram_sub_one_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixL2OperatorNorm ((projectedFullStarNormalization S X K)ᴴ *
        projectedFullStarNormalization S X K - 1) ≤
          4 * matrixFrobeniusNorm (fullStarFrameTail S X K) ^ 2 := by
  filter_upwards [eventually_powerRange_projectedFullStarMolecule_norm_bounds S hS htheta]
    with X hn
  intro K hK
  have heq : (projectedFullStarNormalization S X K)ᴴ *
      projectedFullStarNormalization S X K - 1 =
      Matrix.diagonal (fun a : MoleculeCenter S X K ↦
        ((‖projectedFullStarMolecule S X a.1‖⁻¹ ^ 2 - 1 : ℝ) : ℂ)) := by
    ext a b
    by_cases hab : a = b <;>
      simp [projectedFullStarNormalization, hab, pow_two]
  rw [heq]
  change ‖Matrix.diagonal _‖ ≤ _
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  let n := ‖projectedFullStarMolecule S X a.1‖
  have ha : InPowerRange theta X (a.1 : ℕ) :=
    ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
  obtain ⟨hlo, hhi⟩ := hn a.1 ha
  change 1 / 2 ≤ n at hlo
  change n ≤ 1 at hhi
  have hn0 : 0 < n := by linarith
  have hi : 1 ≤ n⁻¹ := (one_le_inv₀ hn0).mpr hhi
  have hp := projectedFullStarMolecule_pythagoras S X a.1
  change n ^ 2 + _ = 1 at hp
  have hcol := discarded_column_sq_le_tail_hsSq S X K a
  have hscalar : n⁻¹ ^ 2 - 1 ≤ 4 * (1 - n ^ 2) := by
    have heq : n⁻¹ ^ 2 - 1 = (1 - n ^ 2) / n ^ 2 := by field_simp
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
    have hsq : (1 : ℝ) / 4 ≤ n ^ 2 := by nlinarith
    have hrest : 0 ≤ 1 - n ^ 2 := by nlinarith
    nlinarith [mul_nonneg hrest (sub_nonneg.mpr hsq)]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |n⁻¹ ^ 2 - 1| ≤ _
  rw [abs_of_nonneg (by nlinarith : 0 ≤ n⁻¹ ^ 2 - 1)]
  exact hscalar.trans (by nlinarith)

/-- The actual normalization matrix has operator norm at most two on the
complete prefix, including the empty prefix. -/
theorem eventually_powerRange_projectedFullStarNormalization_norm_le_two
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixL2OperatorNorm (projectedFullStarNormalization S X K) ≤ 2 := by
  filter_upwards [eventually_powerRange_projectedFullStarMolecule_norm_bounds S hS htheta]
    with X hn
  intro K hK
  change ‖Matrix.diagonal (fun a : MoleculeCenter S X K ↦
    (‖projectedFullStarMolecule S X a.1‖⁻¹ : ℂ))‖ ≤ 2
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro a
  have ha : InPowerRange theta X (a.1 : ℕ) :=
    ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ (K : ℝ)).trans hK⟩
  have haN := (hn a.1 ha).1
  have hp : 0 < ‖projectedFullStarMolecule S X a.1‖ := by linarith
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hp).mpr (by linarith)

/-- Projection and the actual normalization add only the total discarded
mass to the raw Gram error. The remaining raw overlap estimate is explicit. -/
theorem eventually_powerRange_projectedFullStarFrame_gram_error_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixL2OperatorNorm ((projectedFullStarFrame S X K)ᴴ *
        projectedFullStarFrame S X K - 1) ≤
          4 * matrixL2OperatorNorm ((phasedFullStarFrame S X K)ᴴ *
            phasedFullStarFrame S X K - 1) +
          8 * matrixFrobeniusNorm (fullStarFrameTail S X K) ^ 2 := by
  filter_upwards [eventually_powerRange_projectedFullStarNormalization_norm_le_two S hS htheta,
    eventually_powerRange_projectedFullStarNormalization_gram_sub_one_le S hS htheta]
    with X hn hg
  intro K hK
  let N := projectedFullStarNormalization S X K
  let W := phasedFullStarFrame S X K
  let Z := fullStarFrameTail S X K
  have hN : ‖N‖ ≤ 2 := hn K hK
  have hNN : ‖Nᴴ * N - 1‖ ≤ 4 * matrixFrobeniusNorm Z ^ 2 := hg K hK
  have htriple (M : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ) :
      ‖Nᴴ * M * N‖ ≤ 4 * ‖M‖ := by
    calc
      _ ≤ ‖Nᴴ * M‖ * ‖N‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Nᴴ‖ * ‖M‖) * ‖N‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖N‖ * ‖M‖ * ‖N‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ 2 * ‖M‖ * 2 := by gcongr
      _ = _ := by ring
  have hZ : ‖Zᴴ * Z‖ ≤ matrixFrobeniusNorm Z ^ 2 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self, matrixFrobeniusNorm_sq]
    simpa only [pow_two] using rectangular_operatorNorm_sq_le_sum Z
  have heq : (projectedFullStarFrame S X K)ᴴ * projectedFullStarFrame S X K - 1 =
      (Nᴴ * (Wᴴ * W - 1) * N - Nᴴ * (Zᴴ * Z) * N) + (Nᴴ * N - 1) := by
    rw [projectedFullStarFrame_gram_eq]
    change Nᴴ * (Wᴴ * W - Zᴴ * Z) * N - 1 = _
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [heq]
  change ‖_ + _‖ ≤ _
  calc
    _ ≤ (‖Nᴴ * (Wᴴ * W - 1) * N‖ + ‖Nᴴ * (Zᴴ * Z) * N‖) +
        ‖Nᴴ * N - 1‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ (4 * ‖Wᴴ * W - 1‖ + 4 * ‖Zᴴ * Z‖) +
        4 * matrixFrobeniusNorm Z ^ 2 := by gcongr <;> exact htriple _
    _ ≤ (4 * ‖Wᴴ * W - 1‖ + 4 * matrixFrobeniusNorm Z ^ 2) +
        4 * matrixFrobeniusNorm Z ^ 2 := by gcongr
    _ = _ := by
      change (4 * ‖Wᴴ * W - 1‖ + 4 * matrixFrobeniusNorm Z ^ 2) +
        4 * matrixFrobeniusNorm Z ^ 2 =
        4 * ‖Wᴴ * W - 1‖ + 8 * matrixFrobeniusNorm Z ^ 2
      ring

end ProjectedGramTransfer

noncomputable section AdjacentMoleculeOverlap

open Filter Topology
open scoped Classical

/-- A small-prime-adjacent centre contributes its entire closed star to
the other centre's first-exit compression, also when that star is isolated. -/
theorem adjacent_starSupport_subset_firstExitCompression
    {S : Finset ℕ} {X Y : ℕ} {a b : PrimeStar.Vertex S X}
    (hb : (b : ℕ) ≤ Y)
    (hab : (PrimeStar.smallPrimeGraph S X Y).Adj a b) :
    PrimeStar.largePrimeStarSupport S X Y b ⊆
      PrimeStar.firstExitCompressionSupport S X Y a := by
  have hexit : b ∈ PrimeStar.smallPrimeFirstExitSupport S X Y a :=
    PrimeStar.mem_smallPrimeFirstExitSupport.mpr
      ⟨a, by simp [PrimeStar.largePrimeStarSupport], hab⟩
  intro v hv
  by_cases hiso : (PrimeStar.largePrimeGraph S X Y).IsIsolated b
  · rcases PrimeStar.mem_largePrimeStarSupport.mp hv with rfl | hv
    · exact Finset.mem_union_right _ (PrimeStar.mem_firstExitIsolatedVertices.mpr ⟨hexit, hiso⟩)
    · exact False.elim (hiso v hv)
  · apply Finset.mem_union_left
    apply PrimeStar.mem_largePrimeStarUnionSupport.mpr
    exact ⟨b, PrimeStar.mem_firstExitLowerCenters.mpr
      ⟨hb, b, hexit, hiso, by simp [PrimeStar.largePrimeStarSupport]⟩, hv⟩

/-- The full residual pairs trivially with an adjacent molecule's boundary.
This is support vanishing on the actual full-star principal matrix. -/
theorem real_inner_boundary_residual_eq_zero_of_adjacent
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hab : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b) :
    ⟪exactPrincipalMoleculeBoundaryVector S X b,
      exactPrincipalMoleculeResidual S X a⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) b
  · have hu := adjacent_starSupport_subset_firstExitCompression hb hab hv
    have hm : v ∈ exactPrincipalMoleculeSupport S X a := Finset.mem_union_right _ hu
    rw [exactPrincipalMoleculeResidual_apply_coordinate_eq_zero hS ha ⟨v, hm⟩]
    simp
  · simp [exactPrincipalMoleculeBoundaryVector, hv]

/-- Self-adjointness converts the overlap of two actual molecules into
their residual pairings, with the signed difference of roots retained. -/
theorem roots_sub_mul_inner_fullMolecules_eq_residual_pairings
    (S : Finset ℕ) (X : ℕ) (a b : PrimeStar.Vertex S X) :
    (exactPrincipalMoleculeRoot S X a - exactPrincipalMoleculeRoot S X b) *
      ⟪exactPrincipalMoleculeAmbientVector S X b,
        exactPrincipalMoleculeAmbientVector S X a⟫_ℝ =
      ⟪exactPrincipalMoleculeResidual S X b, exactPrincipalMoleculeAmbientVector S X a⟫_ℝ -
        ⟪exactPrincipalMoleculeAmbientVector S X b, exactPrincipalMoleculeResidual S X a⟫_ℝ := by
  have hsym : (primeCoverAdjacencyOperator S X).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((PrimeStar.primeCoverGraph S X).isHermitian_adjMatrix (R := ℝ))
  have h := hsym (exactPrincipalMoleculeAmbientVector S X b)
    (exactPrincipalMoleculeAmbientVector S X a)
  simp only [exactPrincipalMoleculeResidual, inner_sub_left, inner_sub_right,
    real_inner_smul_left, inner_smul_right]
  rw [h]
  ring

/-- For adjacent centres the root-gap overlap is paid only by first-exit
interiors, not by the unit boundary mass. -/
theorem abs_roots_sub_mul_abs_inner_fullMolecules_le_of_adjacent
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hab : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b) :
    |exactPrincipalMoleculeRoot S X a - exactPrincipalMoleculeRoot S X b| *
      |⟪exactPrincipalMoleculeAmbientVector S X b,
        exactPrincipalMoleculeAmbientVector S X a⟫_ℝ| ≤
      ‖exactPrincipalMoleculeResidual S X b‖ * ‖exactPrincipalMoleculeInteriorVector S X a‖ +
        ‖exactPrincipalMoleculeInteriorVector S X b‖ * ‖exactPrincipalMoleculeResidual S X a‖ := by
  have hab0 := real_inner_boundary_residual_eq_zero_of_adjacent hS ha hb hab
  have hba0 := real_inner_boundary_residual_eq_zero_of_adjacent hS hb ha hab.symm
  rw [real_inner_comm] at hba0
  have hleft : ⟪exactPrincipalMoleculeResidual S X b,
      exactPrincipalMoleculeAmbientVector S X a⟫_ℝ =
      ⟪exactPrincipalMoleculeResidual S X b, exactPrincipalMoleculeInteriorVector S X a⟫_ℝ := by
    rw [← exactPrincipalMolecule_boundary_add_interior ha, inner_add_right, hba0, zero_add]
  have hright : ⟪exactPrincipalMoleculeAmbientVector S X b,
      exactPrincipalMoleculeResidual S X a⟫_ℝ =
      ⟪exactPrincipalMoleculeInteriorVector S X b, exactPrincipalMoleculeResidual S X a⟫_ℝ := by
    rw [← exactPrincipalMolecule_boundary_add_interior hb, inner_add_left, hab0, zero_add]
  rw [← abs_mul, roots_sub_mul_inner_fullMolecules_eq_residual_pairings, hleft, hright]
  exact (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))

/-- The actual interior retains one inverse source energy uniformly on
every complete power prefix; all first-exit gap premises are discharged. -/
theorem eventually_powerRange_energy_mul_norm_fullInterior_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        moleculeStarEnergy S X a * ‖exactPrincipalMoleculeInteriorVector S X a‖ ≤
          100 * PrimeStar.sqrtCutoffResidualScale X := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned] with X hw hg hH
  intro a ha
  have heta : 0 ≤ PrimeStar.sqrtCutoffResidualScale X :=
    mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le (PrimeStar.tunedSchurScale_nonneg _)
  have h := gamma_mul_norm_exactPrincipalMoleculeInteriorVector_le_smallPrime
    hS (hw a ha).1 (moleculeStarEnergy S X a / 100)
    (PrimeStar.sqrtCutoffResidualScale X) heta (hg a ha) (fun x ↦ by
      simpa [PrimeStar.sqrtCutoffResidualScale, PrimeStar.sqrtCutoffResidualConstant] using hH S x)
  linarith

/-- Prime-adjacent centres have a fixed relative gap between their actual
molecule roots. This is not an adjacent-rank isolation assertion. -/
theorem eventually_powerRange_adjacent_fullMoleculeRoots_gap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a b : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → InPowerRange theta X (b : ℕ) →
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b →
        max (moleculeStarEnergy S X a) (moleculeStarEnergy S X b) / 100 ≤
          |exactPrincipalMoleculeRoot S X a - exactPrincipalMoleculeRoot S X b| := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_actualUpStarRatio_bounds S hS htheta] with X hw hr
  have horiented (a b : PrimeStar.Vertex S X)
      (ha : InPowerRange theta X (a : ℕ)) (hb : InPowerRange theta X (b : ℕ))
      (hab : (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b)
      (hle : (a : ℕ) ≤ (b : ℕ)) :
      moleculeStarEnergy S X b ≤ moleculeStarEnergy S X a ∧
        moleculeStarEnergy S X a / 100 ≤
          exactPrincipalMoleculeRoot S X a - exactPrincipalMoleculeRoot S X b := by
    obtain ⟨haY, hda, hsa⟩ := hw a ha
    obtain ⟨hbY, hdb, hsb⟩ := hw b hb
    obtain ⟨q, hq, hqS, hqY, hrel⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hab
    have hprod : (a : ℕ) * q = (b : ℕ) := by
      rcases hrel with h | h
      · exact h
      · have hlt : (b : ℕ) < (b : ℕ) * q :=
          lt_mul_of_one_lt_right (PrimeStar.Vertex.coe_pos b) hq.one_lt
        omega
    let qi : PrimeStar.CanonicalUpIndex S X (squareRootCutoff X) a :=
      ⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqY, hq⟩,
        hqS, by rw [hprod]; exact PrimeStar.Vertex.coe_le b⟩⟩
    have ht : PrimeStar.canonicalUpTarget hS a qi = b := by
      apply Subtype.ext
      apply Fin.ext
      exact (PrimeStar.canonicalUpTarget_coe hS a qi).trans hprod
    have hratio := (hr a ha q (Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hqY, hq⟩, hqS⟩)).2.1
    change PrimeStar.fixedCenterActualUpRatio S (a : ℕ) X q ≤ 15 / 16 at hratio
    rw [← PrimeStar.canonicalUpDegreeRatio_eq_fixedCenterActualUpRatio hS a haY qi] at hratio
    have hmap : 0 < moleculeStarEnergy S X a :=
      Real.sqrt_pos.mpr (by exact_mod_cast hda)
    have hmbp : 0 < moleculeStarEnergy S X b :=
      Real.sqrt_pos.mpr (by exact_mod_cast hdb)
    have hsq : moleculeStarEnergy S X b ^ 2 ≤
        (15 / 16 : ℝ) * moleculeStarEnergy S X a ^ 2 := by
      rw [moleculeStarEnergy_sq, moleculeStarEnergy_sq]
      apply (div_le_iff₀ (by exact_mod_cast hda :
        (0 : ℝ) < (PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a : ℝ))).mp
      simpa [ht] using hratio
    have hstrong : moleculeStarEnergy S X b ≤ (31 / 32 : ℝ) * moleculeStarEnergy S X a := by
      apply (sq_le_sq₀ hmbp.le (by positivity)).mp
      nlinarith [sq_nonneg (moleculeStarEnergy S X a)]
    constructor
    · nlinarith
    · have hlo := (abs_le.mp hsa).1
      have hhi := (abs_le.mp hsb).2
      linarith
  intro a b ha hb hab
  rcases le_total (a : ℕ) (b : ℕ) with hle | hle
  · obtain ⟨hm, hg⟩ := horiented a b ha hb hab hle
    rw [max_eq_left hm]
    exact hg.trans (le_abs_self _)
  · obtain ⟨hm, hg⟩ := horiented b a hb ha hab.symm hle
    rw [max_eq_right hm, abs_sub_comm]
    exact hg.trans (le_abs_self _)

private theorem overlap_energyProduct_bound
    {ma mb gap u ga gb ia ib R T : ℝ}
    (hma : 0 < ma) (hmb : 0 < mb) (hu : 0 ≤ u)
    (hga : ga ≤ R) (hgb : gb ≤ R) (hia : 0 ≤ ia) (hib : 0 ≤ ib)
    (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hgap : max ma mb / 100 ≤ gap)
    (ha : ma * ia ≤ T) (hb : mb * ib ≤ T)
    (hpair : gap * u ≤ gb * ia + ib * ga) :
    ma * mb * u ≤ 200 * R * T := by
  let M := max ma mb
  have hM : 0 < M := lt_of_lt_of_le hma (le_max_left _ _)
  have hs : ma + mb ≤ 2 * M := by
    have := le_max_left ma mb
    have := le_max_right ma mb
    dsimp [M]
    linarith
  have hiA : ia ≤ T / ma := (le_div_iff₀ hma).mpr (by nlinarith)
  have hiB : ib ≤ T / mb := (le_div_iff₀ hmb).mpr (by nlinarith)
  have hstep : M / 100 * u ≤ R * (T / ma + T / mb) := by
    calc
      _ ≤ gap * u := mul_le_mul_of_nonneg_right hgap hu
      _ ≤ gb * ia + ib * ga := hpair
      _ ≤ R * ia + ib * R := add_le_add
        (mul_le_mul_of_nonneg_right hgb hia) (mul_le_mul_of_nonneg_left hga hib)
      _ ≤ R * (T / ma) + (T / mb) * R := by gcongr
      _ = _ := by ring
  have hmajor : R * (T / ma + T / mb) ≤ 2 * R * T * M / (ma * mb) := by
    calc
      _ = R * T * (ma + mb) / (ma * mb) := by field_simp; ring
      _ ≤ R * T * (2 * M) / (ma * mb) := by gcongr
      _ = _ := by ring
  have hclear := (le_div_iff₀ (mul_pos hma hmb)).mp (hstep.trans hmajor)
  have hfinal : M * (ma * mb * u) ≤ M * (200 * R * T) := by nlinarith [hclear]
  exact (mul_le_mul_iff_right₀ hM).mp hfinal

/-- The adjacent part of the actual raw Gram retains both inverse source
energies. The residual, interior and relative root-gap inputs are all produced
uniformly; no overlap or collision budget is a hypothesis. -/
theorem eventually_powerRange_adjacent_fullMoleculeOverlap_energyProduct_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ a b : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → InPowerRange theta X (b : ℕ) →
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b →
        moleculeStarEnergy S X a * moleculeStarEnergy S X b *
          |⟪exactPrincipalMoleculeAmbientVector S X b,
            exactPrincipalMoleculeAmbientVector S X a⟫_ℝ| ≤
          C * PrimeStar.sqrtCutoffResidualScale X * Real.log (X : ℝ) ^ 3 := by
  obtain ⟨Cr, hCr, hr⟩ := eventually_powerRange_exactPrincipalMoleculeResidual_sq_le_logFifth S hS htheta
  refine ⟨20000 * Real.sqrt Cr, by positivity, ?_⟩
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hr, eventually_powerRange_adjacent_fullMoleculeRoots_gap S hS htheta,
    eventually_powerRange_energy_mul_norm_fullInterior_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    hlogTop.eventually_ge_atTop 1] with X hrX hgap hi hw hL
  intro a b ha hb hab
  have hL0 : 0 ≤ Real.log (X : ℝ) := by linarith
  have hma : 0 < moleculeStarEnergy S X a :=
    Real.sqrt_pos.mpr (by exact_mod_cast (hw a ha).2.1)
  have hmb : 0 < moleculeStarEnergy S X b :=
    Real.sqrt_pos.mpr (by exact_mod_cast (hw b hb).2.1)
  have heta : 0 ≤ PrimeStar.sqrtCutoffResidualScale X :=
    mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le (PrimeStar.tunedSchurScale_nonneg _)
  have hres (c : PrimeStar.Vertex S X) (hc : InPowerRange theta X (c : ℕ)) :
      ‖exactPrincipalMoleculeResidual S X c‖ ≤ Real.sqrt Cr * Real.log (X : ℝ) ^ 3 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      _ ≤ Cr * Real.log (X : ℝ) ^ 5 := hrX c hc
      _ ≤ Cr * Real.log (X : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) hCr.le
      _ = _ := by rw [mul_pow, Real.sq_sqrt hCr.le]; ring
  have h := overlap_energyProduct_bound hma hmb (abs_nonneg _)
    (hres a ha) (hres b hb) (norm_nonneg _) (norm_nonneg _) (by positivity)
    (show 0 ≤ 100 * PrimeStar.sqrtCutoffResidualScale X by positivity)
    (hgap a b ha hb hab) (hi a ha) (hi b hb)
    (abs_roots_sub_mul_abs_inner_fullMolecules_le_of_adjacent hS (hw a ha).1 (hw b hb).1 hab)
  convert h using 1
  ring

end AdjacentMoleculeOverlap

noncomputable section SharedMoleculeTargets

open scoped Classical

/-- A shared one-step target of distinct sources uses an endpoint prime.
There is no free-prime factor in this count. -/
theorem prime_dvd_endpoint_of_commonTarget
    {a b p q v : ℕ} (hp : p.Prime) (hq : q.Prime) (hab : a ≠ b)
    (hav : a * p = v ∨ v * p = a) (hbv : b * q = v ∨ v * q = b) :
    p ∣ a ∨ p ∣ b := by
  rcases hav with hav | hav
  · right
    rcases hbv with hbv | hbv
    · have hdiv : p ∣ b * q := by rw [hbv, ← hav]; exact dvd_mul_left p a
      rcases hp.dvd_mul.mp hdiv with h | h
      · exact h
      · have heq := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
        subst q
        exact False.elim (hab (Nat.eq_of_mul_eq_mul_right hp.pos (hav.trans hbv.symm)))
    · exact ⟨a * q, by rw [← hbv, ← hav]; ac_rfl⟩
  · exact Or.inl ⟨v, by rw [← hav]; ac_rfl⟩

/-- The endpoint-divisor majorant for common target centres. This logarithmic
overcount is sufficient for the complete-prefix Gram estimate. -/
theorem card_common_smallPrimeTargets_le
    {S : Finset ℕ} {X Y : ℕ} {a b : PrimeStar.Vertex S X} (hab : a ≠ b) :
    (Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
      (PrimeStar.smallPrimeGraph S X Y).Adj a v ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj b v)).card ≤
      2 * ((a : ℕ).primeFactors.card + (b : ℕ).primeFactors.card) := by
  let N := Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
    (PrimeStar.smallPrimeGraph S X Y).Adj a v ∧
    (PrimeStar.smallPrimeGraph S X Y).Adj b v)
  let F := (a : ℕ).primeFactors ∪ (b : ℕ).primeFactors
  let W := fun p : ℕ ↦ ({(a : ℕ) * p, (a : ℕ) / p} : Finset ℕ)
  let T := F.biUnion W
  have hinj : Function.Injective (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) :=
    fun _ _ h ↦ Subtype.ext (Fin.ext h)
  have hsub : N.image (fun v : PrimeStar.Vertex S X ↦ (v : ℕ)) ⊆ T := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hav, hbv⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨p, hp, _, _, hpv⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hav
    obtain ⟨q, hq, _, _, hqv⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hbv
    have hdiv := prime_dvd_endpoint_of_commonTarget hp hq (fun h ↦ hab (hinj h)) hpv hqv
    have hpF : p ∈ F := by
      rcases hdiv with h | h
      · exact Finset.mem_union_left _ (hp.mem_primeFactors h (PrimeStar.Vertex.coe_pos a).ne')
      · exact Finset.mem_union_right _ (hp.mem_primeFactors h (PrimeStar.Vertex.coe_pos b).ne')
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpF, ?_⟩
    rcases hpv with h | h
    · simp [W, h]
    · have heq : (a : ℕ) / p = (v : ℕ) := by rw [← h, Nat.mul_div_cancel _ hp.pos]
      simp [W, heq]
  calc
    N.card = (N.image (fun v : PrimeStar.Vertex S X ↦ (v : ℕ))).card :=
      (Finset.card_image_of_injective N hinj).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ F.card * 2 := Finset.card_biUnion_le_card_mul F W 2 (fun p _ ↦ by
      simpa [W] using (Finset.card_insert_le ((a : ℕ) * p) {(a : ℕ) / p}))
    _ ≤ ((a : ℕ).primeFactors.card + (b : ℕ).primeFactors.card) * 2 :=
      Nat.mul_le_mul_right 2 (Finset.card_union_le _ _)
    _ = _ := by ring

/-- Every target component is represented by a neighbouring centre, including
isolated inactive up-targets. Reuses the finite full-star support argument. -/
theorem exists_neighboringStar_of_mem_firstExitCompression
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {c v : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (hc : (c : ℕ) ≤ Y)
    (hv : v ∈ PrimeStar.firstExitCompressionSupport S X Y c) :
    ∃ k : PrimeStar.Vertex S X,
      v ∈ PrimeStar.largePrimeStarSupport S X Y k ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj c k ∧
      ((k : ℕ) ≤ Y ∨ (PrimeStar.largePrimeGraph S X Y).IsIsolated k) := by
  rcases Finset.mem_union.mp hv with hvStars | hvIso
  · obtain ⟨k, hkLower, hvk⟩ := PrimeStar.mem_largePrimeStarUnionSupport.mp hvStars
    obtain ⟨q, hq, hqS, hqY, hrel⟩ :=
      PrimeStar.mem_firstExitLowerCenters_arithmetic hcut hc hkLower
    exact ⟨k, hvk, PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr
      ⟨q, hq, hqS, hqY, hrel⟩,
      Or.inl (PrimeStar.mem_firstExitLowerCenters.mp hkLower).1⟩
  · obtain ⟨q, hq, hqS, hqY, hrel⟩ :=
      PrimeStar.mem_firstExitIsolatedVertices_arithmetic hS hc hvIso
    exact ⟨v, by simp [PrimeStar.largePrimeStarSupport],
      PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mpr ⟨q, hq, hqS, hqY, hrel⟩,
      Or.inr (PrimeStar.mem_firstExitIsolatedVertices.mp hvIso).2⟩

/-- Lower stars and isolated target singletons identify their centre uniquely
from an intersecting coordinate. -/
theorem targetCenters_eq_of_starSupport_inter
    {S : Finset ℕ} {X Y : ℕ} {a b v : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1))
    (ha : (a : ℕ) ≤ Y ∨ (PrimeStar.largePrimeGraph S X Y).IsIsolated a)
    (hb : (b : ℕ) ≤ Y ∨ (PrimeStar.largePrimeGraph S X Y).IsIsolated b)
    (hva : v ∈ PrimeStar.largePrimeStarSupport S X Y a)
    (hvb : v ∈ PrimeStar.largePrimeStarSupport S X Y b) : a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · by_contra hne
    exact Finset.disjoint_left.mp (PrimeStar.disjoint_largePrimeStarSupport hcut ha hb hne) hva hvb
  · rcases PrimeStar.mem_largePrimeStarSupport.mp hvb with rfl | hvb
    · rcases PrimeStar.mem_largePrimeStarSupport.mp hva with h | h
      · exact h.symm
      · exact False.elim (hb _ (show (PrimeStar.largePrimeGraph S X Y).Adj a v from h).symm)
    · exact False.elim (hb _ hvb)
  · rcases PrimeStar.mem_largePrimeStarSupport.mp hva with rfl | hva
    · rcases PrimeStar.mem_largePrimeStarSupport.mp hvb with h | h
      · exact h
      · exact False.elim (ha _ (show (PrimeStar.largePrimeGraph S X Y).Adj b v from h).symm)
    · exact False.elim (ha _ hva)
  · rcases PrimeStar.mem_largePrimeStarSupport.mp hva with rfl | hva
    · rcases PrimeStar.mem_largePrimeStarSupport.mp hvb with h | h
      · exact h
      · exact False.elim (hb _ h)
    · exact False.elim (ha _ hva)

/-- Intersecting full interiors share a literal target star adjacent to both
sources. This excludes spurious overlap from different target components. -/
theorem exists_commonTarget_of_mem_firstExitCompressions
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b v : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (ha : (a : ℕ) ≤ Y) (hb : (b : ℕ) ≤ Y)
    (hva : v ∈ PrimeStar.firstExitCompressionSupport S X Y a)
    (hvb : v ∈ PrimeStar.firstExitCompressionSupport S X Y b) :
    ∃ k : PrimeStar.Vertex S X,
      v ∈ PrimeStar.largePrimeStarSupport S X Y k ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj a k ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj b k := by
  obtain ⟨k, hvk, hak, hk⟩ := exists_neighboringStar_of_mem_firstExitCompression hS hcut ha hva
  obtain ⟨l, hvl, hbl, hl⟩ := exists_neighboringStar_of_mem_firstExitCompression hS hcut hb hvb
  have heq := targetCenters_eq_of_starSupport_inter hcut hk hl hvk hvl
  exact ⟨k, hvk, hak, heq ▸ hbl⟩

/-- For non-adjacent centres a boundary star cannot meet the other interior. -/
theorem disjoint_boundary_firstExitCompression_of_not_adjacent
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (ha : (a : ℕ) ≤ Y) (hb : (b : ℕ) ≤ Y)
    (hab : ¬(PrimeStar.smallPrimeGraph S X Y).Adj a b) :
    Disjoint (PrimeStar.largePrimeStarSupport S X Y a)
      (PrimeStar.firstExitCompressionSupport S X Y b) := by
  rw [Finset.disjoint_left]
  intro v hva hvb
  obtain ⟨k, hvk, hbk, hk⟩ := exists_neighboringStar_of_mem_firstExitCompression hS hcut hb hvb
  have heq := targetCenters_eq_of_starSupport_inter hcut (Or.inl ha) hk hva hvk
  exact hab (heq ▸ hbk.symm)

/-- Non-adjacent raw overlap has no boundary contribution; only the full
interiors remain. Neither a signed-mode truncation nor a root gap is used. -/
theorem inner_fullMolecules_eq_inner_interiors_of_not_adjacent
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hab : a ≠ b)
    (hnot : ¬(PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b) :
    ⟪exactPrincipalMoleculeAmbientVector S X a, exactPrincipalMoleculeAmbientVector S X b⟫_ℝ =
      ⟪exactPrincipalMoleculeInteriorVector S X a, exactPrincipalMoleculeInteriorVector S X b⟫_ℝ := by
  have hBA := disjoint_boundary_firstExitCompression_of_not_adjacent
    hS (PrimeStar.sqrtCutoff_condition X) ha hb hnot
  have hAB := disjoint_boundary_firstExitCompression_of_not_adjacent
    hS (PrimeStar.sqrtCutoff_condition X) hb ha (fun h ↦ hnot h.symm)
  have hBB := PrimeStar.disjoint_largePrimeStarSupport (PrimeStar.sqrtCutoff_condition X) ha hb hab
  rw [← exactPrincipalMolecule_boundary_add_interior ha,
    ← exactPrincipalMolecule_boundary_add_interior hb,
    inner_add_left, inner_add_right, inner_add_right]
  have hboundary (c d : PrimeStar.Vertex S X)
      (hdj : Disjoint (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) c)
        (PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) d)) :
      ⟪exactPrincipalMoleculeBoundaryVector S X c,
        exactPrincipalMoleculeInteriorVector S X d⟫_ℝ = 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : v ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) c
    · have hnotv : v ∉ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) d :=
        fun h ↦ Finset.disjoint_left.mp hdj hv h
      simp [exactPrincipalMoleculeInteriorVector, PrimeStar.firstExitCompressionProjection_apply, hnotv]
    · simp [exactPrincipalMoleculeBoundaryVector, hv]
  have hbb : ⟪exactPrincipalMoleculeBoundaryVector S X a,
      exactPrincipalMoleculeBoundaryVector S X b⟫_ℝ = 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : v ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a
    · have hnotv : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) b :=
        fun h ↦ Finset.disjoint_left.mp hBB hv h
      simp [exactPrincipalMoleculeBoundaryVector, hnotv]
    · simp [exactPrincipalMoleculeBoundaryVector, hv]
  have hab0 := hboundary a b hBA
  have hba0 := hboundary b a hAB
  rw [real_inner_comm] at hba0
  rw [hbb, hab0, hba0]
  simp

/-- The shared-target count has a uniform logarithmic bound on actual graph
vertices, without any prime-counting asymptotic or spectral hypothesis. -/
theorem card_common_smallPrimeTargets_le_log
    {S : Finset ℕ} {X Y : ℕ} {a b : PrimeStar.Vertex S X} (hab : a ≠ b) :
    ((Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
      (PrimeStar.smallPrimeGraph S X Y).Adj a v ∧
      (PrimeStar.smallPrimeGraph S X Y).Adj b v)).card : ℝ) ≤
      4 * Real.log (X : ℝ) / Real.log 2 := by
  have homega (w : PrimeStar.Vertex S X) :
      ((w : ℕ).primeFactors.card : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
    apply (primeFactors_card_le_log_div_log_two (PrimeStar.Vertex.coe_pos w)).trans
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    exact Real.log_le_log (by exact_mod_cast PrimeStar.Vertex.coe_pos w)
      (by exact_mod_cast PrimeStar.Vertex.coe_le w)
  have hcount :
      ((Finset.univ.filter (fun v : PrimeStar.Vertex S X ↦
        (PrimeStar.smallPrimeGraph S X Y).Adj a v ∧
        (PrimeStar.smallPrimeGraph S X Y).Adj b v)).card : ℝ) ≤
        2 * (((a : ℕ).primeFactors.card : ℝ) + ((b : ℕ).primeFactors.card : ℝ)) := by
    exact_mod_cast card_common_smallPrimeTargets_le (S := S) (Y := Y) hab
  calc
    _ ≤ 2 * (((a : ℕ).primeFactors.card : ℝ) + ((b : ℕ).primeFactors.card : ℝ)) := hcount
    _ ≤ 2 * (Real.log (X : ℝ) / Real.log 2 + Real.log (X : ℝ) / Real.log 2) := by
      gcongr
      · exact homega a
      · exact homega b
    _ = _ := by ring

/-- Distinct non-adjacent full molecules with no common target are exactly
orthogonal, including their kernel components. -/
theorem inner_fullMolecules_eq_zero_of_no_commonTarget
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X) (hb : (b : ℕ) ≤ squareRootCutoff X)
    (hab : a ≠ b)
    (hnot : ¬(PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b)
    (hcommon : ¬∃ k : PrimeStar.Vertex S X,
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a k ∧
      (PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj b k) :
    ⟪exactPrincipalMoleculeAmbientVector S X a,
      exactPrincipalMoleculeAmbientVector S X b⟫_ℝ = 0 := by
  rw [inner_fullMolecules_eq_inner_interiors_of_not_adjacent hS ha hb hab hnot, PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hva : v ∈ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) a
  · have hvb : v ∉ PrimeStar.firstExitCompressionSupport S X (squareRootCutoff X) b := by
      intro hvb
      obtain ⟨k, _, hak, hbk⟩ := exists_commonTarget_of_mem_firstExitCompressions
        hS (PrimeStar.sqrtCutoff_condition X) ha hb hva hvb
      exact hcommon ⟨k, hak, hbk⟩
    simp [exactPrincipalMoleculeInteriorVector, PrimeStar.firstExitCompressionProjection_apply, hvb]
  · simp [exactPrincipalMoleculeInteriorVector, PrimeStar.firstExitCompressionProjection_apply, hva]

end SharedMoleculeTargets

noncomputable section TargetResponseOverlap

open scoped Classical

private theorem sum_sq_partialMatching_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ι → Prop) [DecidableRel R] (x : ι → ℝ)
    (hrow : ∀ v w t, R v w → R v t → w = t)
    (hcol : ∀ w v t, R v w → R t w → v = t) :
    (∑ v, (∑ w, if R v w then x w else 0) ^ 2) ≤ ∑ w, (x w) ^ 2 := by
  have hrowBound (v : ι) :
      (∑ w, if R v w then x w else 0) ^ 2 ≤ ∑ w, if R v w then (x w) ^ 2 else 0 := by
    let F := Finset.univ.filter (R v)
    have hc : (F.card : ℝ) ≤ 1 := by
      exact_mod_cast (Finset.card_le_one.mpr (fun w hw t ht ↦
        hrow v w t (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp ht).2))
    calc
      _ = (∑ w ∈ F, x w) ^ 2 := by simp [F, Finset.sum_filter]
      _ ≤ (F.card : ℝ) * ∑ w ∈ F, (x w) ^ 2 := by
        simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq F x (fun _ ↦ (1 : ℝ))
      _ ≤ 1 * ∑ w ∈ F, (x w) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
      _ = _ := by simp [F, Finset.sum_filter]
  calc
    _ ≤ ∑ v, ∑ w, if R v w then (x w) ^ 2 else 0 := Finset.sum_le_sum (fun v _ ↦ hrowBound v)
    _ = ∑ w, ∑ v, if R v w then (x w) ^ 2 else 0 := Finset.sum_comm
    _ ≤ ∑ w, (x w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w _
      let F := Finset.univ.filter (fun v ↦ R v w)
      have hc : (F.card : ℝ) ≤ 1 := by
        exact_mod_cast (Finset.card_le_one.mpr (fun v hv t ht ↦
          hcol w v t (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp ht).2))
      calc
        _ = (F.card : ℝ) * (x w) ^ 2 := by simp [F, ← Finset.sum_filter]
        _ ≤ 1 * (x w) ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ = _ := one_mul _

/-- Small-prime coupling between one lower source star and one target star
is a partial coordinate matching. Its Euclidean norm is at most one,
including an isolated target. -/
theorem norm_targetProjection_smallPrime_boundaryProjection_le
    {S : Finset ℕ} {X Y : ℕ} {a b : PrimeStar.Vertex S X}
    (hcut : X < (Y + 1) * (Y + 1)) (ha : (a : ℕ) ≤ Y)
    (hb : (b : ℕ) ≤ Y ∨ (PrimeStar.largePrimeGraph S X Y).IsIsolated b)
    (x : MoleculeAmbient S X) :
    ‖PrimeStar.euclideanCoordinateProjection (PrimeStar.largePrimeStarSupport S X Y b)
      (Matrix.toEuclideanLin ((PrimeStar.smallPrimeGraph S X Y).adjMatrix ℝ)
        (PrimeStar.euclideanCoordinateProjection (PrimeStar.largePrimeStarSupport S X Y a) x))‖ ≤ ‖x‖ := by
  let G := PrimeStar.smallPrimeGraph S X Y
  let F := PrimeStar.largePrimeStarSupport S X Y a
  let T := PrimeStar.largePrimeStarSupport S X Y b
  let R := fun v w : PrimeStar.Vertex S X ↦ v ∈ T ∧ w ∈ F ∧ G.Adj v w
  have hrow (v w t : PrimeStar.Vertex S X) (hw : R v w) (ht : R v t) : w = t :=
    PrimeStar.unique_smallPrime_neighbor_in_largePrimeStar hcut ha hw.2.1 ht.2.1 hw.2.2.symm ht.2.2.symm
  have hcol (w v t : PrimeStar.Vertex S X) (hv : R v w) (ht : R t w) : v = t := by
    rcases hb with hb | hb
    · exact PrimeStar.unique_smallPrime_neighbor_in_largePrimeStar
        hcut hb hv.1 ht.1 hv.2.2 ht.2.2
    · have heq (k : PrimeStar.Vertex S X) (hk : k ∈ T) : k = b := by
        rcases PrimeStar.mem_largePrimeStarSupport.mp hk with h | h
        · exact h
        · exact False.elim (hb _ h)
      exact (heq v hv.1).trans (heq t ht.1).symm
  let y := PrimeStar.euclideanCoordinateProjection T
    (Matrix.toEuclideanLin (G.adjMatrix ℝ) (PrimeStar.euclideanCoordinateProjection F x))
  have hy (v : PrimeStar.Vertex S X) : y v = ∑ w, if R v w then x w else 0 := by
    dsimp only [y]
    rw [PrimeStar.euclideanCoordinateProjection_apply]
    by_cases hv : v ∈ T
    · rw [if_pos hv, Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
      change (G.adjMatrix ℝ).mulVec (fun w ↦
        PrimeStar.euclideanCoordinateProjection F x w) v = _
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w ∈ F <;> by_cases hadj : G.Adj v w <;>
        simp [R, hv, hw, hadj, SimpleGraph.adjMatrix_apply, PrimeStar.euclideanCoordinateProjection_apply]
    · simp [R, hv]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖y‖ ^ 2 ≤ ‖x‖ ^ 2
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [hy]
  exact sum_sq_partialMatching_le R (fun w ↦ x w) hrow hcol

private theorem coordinateProjection_largePrime_commute
    {S : Finset ℕ} {X Y : ℕ} {F : Finset (PrimeStar.Vertex S X)}
    (hF : PrimeStar.LargePrimeClosed (S := S) (X := X) (Y := Y) F)
    (x : MoleculeAmbient S X) :
    PrimeStar.euclideanCoordinateProjection F
      (Matrix.toEuclideanLin ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ) x) =
    Matrix.toEuclideanLin ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ)
      (PrimeStar.euclideanCoordinateProjection F x) := by
  ext v
  rw [PrimeStar.euclideanCoordinateProjection_apply]
  by_cases hv : v ∈ F
  · rw [if_pos hv, Matrix.toLpLin_toLp 2 2, Matrix.toLin'_apply]
    change ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ).mulVec (fun w ↦ x w) v =
      ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ).mulVec
        (fun w ↦ PrimeStar.euclideanCoordinateProjection F x w) v
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hadj : (PrimeStar.largePrimeGraph S X Y).Adj v w
    · have hw := hF hv hadj
      simp [PrimeStar.euclideanCoordinateProjection_apply, hw]
    · change ¬PrimeStar.LargePrimeAdj S Y v w at hadj
      simp [SimpleGraph.adjMatrix_apply, hadj]
  · rw [if_neg hv]
    exact (PrimeStar.largePrime_toEuclideanLin_preserves_closedSupport hF _
      (fun w hw ↦ by simp [PrimeStar.euclideanCoordinateProjection_apply, hw]) hv).symm

/-- A canonical target response is charged by its unit boundary coupling,
not by the global small-prime operator norm. -/
theorem gamma_mul_norm_fullInterior_on_canonicalTarget_le_one
    {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a : PrimeStar.Vertex S X} (ha : (a : ℕ) ≤ squareRootCutoff X)
    (i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a)
    (gamma : ℝ)
    (hgap : ∀ y : MoleculeAmbient S X,
      gamma * ‖y‖ ≤ ‖exactPrincipalMoleculeRoot S X a • y -
        PrimeStar.firstExitLargePrimeCompressionOperator S X (squareRootCutoff X) a y‖) :
    gamma * ‖PrimeStar.euclideanCoordinateProjection
      (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) (PrimeStar.canonicalExitTarget hS a i))
      (exactPrincipalMoleculeInteriorVector S X a)‖ ≤ 1 := by
  let Y := squareRootCutoff X
  let b := PrimeStar.canonicalExitTarget hS a i
  let F := PrimeStar.largePrimeStarSupport S X Y b
  let P := PrimeStar.euclideanCoordinateProjection F
  let L := Matrix.toEuclideanLin ((PrimeStar.largePrimeGraph S X Y).adjMatrix ℝ)
  let x := exactPrincipalMoleculeInteriorVector S X a
  have hb : (b : ℕ) ≤ Y ∨ (PrimeStar.largePrimeGraph S X Y).IsIsolated b :=
    PrimeStar.canonicalExitTarget_le_or_isolated hS (PrimeStar.sqrtCutoff_condition X) ha i
  have hF : PrimeStar.LargePrimeClosed (S := S) (X := X) (Y := Y) F := by
    intro v w hv hadj
    rcases hb with hb | hb
    · exact PrimeStar.largePrimeStarSupport_closed (PrimeStar.sqrtCutoff_condition X) hb hv hadj
    · rcases PrimeStar.mem_largePrimeStarSupport.mp hv with rfl | hv
      · exact False.elim (hb w hadj)
      · exact False.elim (hb v hv)
  have hsub : F ⊆ PrimeStar.firstExitCompressionSupport S X Y a :=
    PrimeStar.canonicalExitTarget_starSupport_subset_firstExitCompression
      hS (PrimeStar.sqrtCutoff_condition X) ha i
  have hcomp : PrimeStar.firstExitLargePrimeCompressionOperator S X Y a (P x) = L (P x) :=
    PrimeStar.firstExitLargePrimeCompressionOperator_eq_of_supported
      (PrimeStar.sqrtCutoff_condition X) (P x) (fun v hv ↦ by
        have hnot : v ∉ F := fun h ↦ hv (hsub h)
        simp [P, PrimeStar.euclideanCoordinateProjection_apply, hnot])
  have hshift : exactPrincipalMoleculeRoot S X a • P x - L (P x) =
      P (exactPrincipalMoleculeInteriorSource S X a) := by
    rw [← coordinateProjection_largePrime_commute hF x]
    rw [← map_smul, ← map_sub]
    exact congrArg P (exactPrincipalMoleculeInterior_shift_largePrime hS ha)
  have hsource : P (exactPrincipalMoleculeInteriorSource S X a) =
      P (Matrix.toEuclideanLin ((PrimeStar.smallPrimeGraph S X Y).adjMatrix ℝ)
        (exactPrincipalMoleculeBoundaryVector S X a)) := by
    ext v
    by_cases hv : v ∈ F
    · have hvU := hsub hv
      simp [P, exactPrincipalMoleculeInteriorSource,
        PrimeStar.euclideanCoordinateProjection_apply, PrimeStar.firstExitCompressionProjection_apply,
        hv, hvU, Y]
    · simp [P, PrimeStar.euclideanCoordinateProjection_apply, hv]
  calc
    gamma * ‖P x‖ ≤ ‖exactPrincipalMoleculeRoot S X a • P x -
        PrimeStar.firstExitLargePrimeCompressionOperator S X Y a (P x)‖ := hgap (P x)
    _ = ‖P (Matrix.toEuclideanLin ((PrimeStar.smallPrimeGraph S X Y).adjMatrix ℝ)
        (exactPrincipalMoleculeBoundaryVector S X a))‖ := by rw [hcomp, hshift, hsource]
    _ ≤ ‖exactPrincipalMoleculeAmbientVector S X a‖ :=
      norm_targetProjection_smallPrime_boundaryProjection_le (PrimeStar.sqrtCutoff_condition X)
        ha hb (exactPrincipalMoleculeAmbientVector S X a)
    _ = 1 := norm_exactPrincipalMoleculeAmbientVector S X a

/-- Uniform full-response bound on every canonical target, with the actual
first-exit gap supplied. Both signed modes and the kernel are retained. -/
theorem eventually_powerRange_energy_mul_norm_fullInterior_on_target_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
      ∀ i : PrimeStar.CanonicalExitIndex S X (squareRootCutoff X) a,
        moleculeStarEnergy S X a * ‖PrimeStar.euclideanCoordinateProjection
          (PrimeStar.largePrimeStarSupport S X (squareRootCutoff X)
            (PrimeStar.canonicalExitTarget hS a i))
          (exactPrincipalMoleculeInteriorVector S X a)‖ ≤ 100 := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_firstExitCompressionGap S hS htheta]
    with X hw hg
  intro a ha i
  have h := gamma_mul_norm_fullInterior_on_canonicalTarget_le_one hS (hw a ha).1 i
    (moleculeStarEnergy S X a / 100) (hg a ha)
  nlinarith

/-- Every small-prime neighbour is the centre of its actual canonical target,
not merely a point somewhere in a target support. -/
theorem exists_canonicalExitTarget_eq_of_smallPrimeAdj
    {S : Finset ℕ} {X Y : ℕ} (hS : ∀ p ∈ S, p.Prime)
    {a b : PrimeStar.Vertex S X}
    (hab : (PrimeStar.smallPrimeGraph S X Y).Adj a b) :
    ∃ i : PrimeStar.CanonicalExitIndex S X Y a, PrimeStar.canonicalExitTarget hS a i = b := by
  obtain ⟨q, hq, hqS, hqY, hrel⟩ := PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp hab
  rcases hrel with hrel | hrel
  · let i : PrimeStar.CanonicalUpIndex S X Y a :=
      ⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqY, hq⟩,
        hqS, by rw [hrel]; exact PrimeStar.Vertex.coe_le b⟩⟩
    refine ⟨Sum.inl i, Subtype.ext (Fin.ext ?_)⟩
    exact (PrimeStar.canonicalUpTarget_coe hS a i).trans hrel
  · have hdiv : q ∣ (a : ℕ) := ⟨(b : ℕ), by rw [← hrel]; ac_rfl⟩
    let i : PrimeStar.CanonicalDownIndex a :=
      ⟨q, hq.mem_primeFactors hdiv (PrimeStar.Vertex.coe_pos a).ne'⟩
    refine ⟨Sum.inr i, Subtype.ext (Fin.ext ?_)⟩
    exact Nat.eq_of_mul_eq_mul_right hq.pos
      ((PrimeStar.canonicalDownTarget_mul_coe a i).trans hrel.symm)

private theorem sum_abs_mul_le_projectionNorm_mul
    {S : Finset ℕ} {X : ℕ} (F : Finset (PrimeStar.Vertex S X))
    (x y : MoleculeAmbient S X) :
    (∑ v ∈ F, |x v| * |y v|) ≤
      ‖PrimeStar.euclideanCoordinateProjection F x‖ *
        ‖PrimeStar.euclideanCoordinateProjection F y‖ := by
  have hn (z : MoleculeAmbient S X) :
      ‖PrimeStar.euclideanCoordinateProjection F z‖ ^ 2 = ∑ v ∈ F, (z v) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [PrimeStar.euclideanCoordinateProjection_apply]
  have h := Finset.sum_mul_sq_le_sq_mul_sq F (fun v ↦ |x v|) (fun v ↦ |y v|)
  simp only [sq_abs] at h
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, hn, hn]
  exact h

private theorem abs_inner_le_sum_projectionNorms
    {S : Finset ℕ} {X : ℕ} (x y : MoleculeAmbient S X)
    (K : Finset (PrimeStar.Vertex S X))
    (F : PrimeStar.Vertex S X → Finset (PrimeStar.Vertex S X))
    (hcover : ∀ v, x v ≠ 0 → y v ≠ 0 → ∃ k ∈ K, v ∈ F k) :
    |⟪x, y⟫_ℝ| ≤ ∑ k ∈ K,
      ‖PrimeStar.euclideanCoordinateProjection (F k) x‖ *
        ‖PrimeStar.euclideanCoordinateProjection (F k) y‖ := by
  have hpoint (v : PrimeStar.Vertex S X) :
      |x v| * |y v| ≤ ∑ k ∈ K, if v ∈ F k then |x v| * |y v| else 0 := by
    by_cases hx : x v = 0
    · simp [hx]
    by_cases hy : y v = 0
    · simp [hy]
    obtain ⟨k, hk, hv⟩ := hcover v hx hy
    have hs : (if v ∈ F k then |x v| * |y v| else (0 : ℝ)) ≤
        ∑ j ∈ K, if v ∈ F j then |x v| * |y v| else 0 :=
      Finset.single_le_sum (f := fun j ↦ if v ∈ F j then |x v| * |y v| else (0 : ℝ))
        (fun j _ ↦ by positivity) hk
    simpa only [if_pos hv] using hs
  calc
    _ = |∑ v, x v * y v| := by simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    _ ≤ ∑ v, |x v| * |y v| := by
      simpa only [abs_mul] using
        Finset.abs_sum_le_sum_abs (fun v ↦ x v * y v) Finset.univ
    _ ≤ ∑ v, ∑ k ∈ K, if v ∈ F k then |x v| * |y v| else 0 :=
      Finset.sum_le_sum (fun v _ ↦ hpoint v)
    _ = ∑ k ∈ K, ∑ v ∈ F k, |x v| * |y v| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      simp
    _ ≤ _ := Finset.sum_le_sum (fun k _ ↦ sum_abs_mul_le_projectionNorm_mul (F k) x y)

/-- Distinct full interiors have only a logarithmic shared-target cost.
This estimate also includes adjacent source centres: their boundary cross
terms do not occur in an interior--interior pairing. -/
theorem eventually_powerRange_fullInteriorOverlap_energyProduct_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ a b : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → InPowerRange theta X (b : ℕ) → a ≠ b →
        moleculeStarEnergy S X a * moleculeStarEnergy S X b *
          |⟪exactPrincipalMoleculeInteriorVector S X a,
            exactPrincipalMoleculeInteriorVector S X b⟫_ℝ| ≤
            (40000 / Real.log 2) * Real.log (X : ℝ) := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_energy_mul_norm_fullInterior_on_target_le S hS htheta]
    with X hw hr
  intro a b ha hb hab
  let Y := squareRootCutoff X
  let K := Finset.univ.filter (fun k : PrimeStar.Vertex S X ↦
    (PrimeStar.smallPrimeGraph S X Y).Adj a k ∧ (PrimeStar.smallPrimeGraph S X Y).Adj b k)
  let F := PrimeStar.largePrimeStarSupport S X Y
  let x := exactPrincipalMoleculeInteriorVector S X a
  let y := exactPrincipalMoleculeInteriorVector S X b
  let ma := moleculeStarEnergy S X a
  let mb := moleculeStarEnergy S X b
  have hma : 0 < ma := Real.sqrt_pos.mpr (by exact_mod_cast (hw a ha).2.1)
  have hmb : 0 < mb := Real.sqrt_pos.mpr (by exact_mod_cast (hw b hb).2.1)
  have hcover : ∀ v, x v ≠ 0 → y v ≠ 0 → ∃ k ∈ K, v ∈ F k := by
    intro v hx hy
    have hva : v ∈ PrimeStar.firstExitCompressionSupport S X Y a := by
      by_contra h
      exact hx (by simp [x, exactPrincipalMoleculeInteriorVector,
        PrimeStar.firstExitCompressionProjection_apply, h, Y])
    have hvb : v ∈ PrimeStar.firstExitCompressionSupport S X Y b := by
      by_contra h
      exact hy (by simp [y, exactPrincipalMoleculeInteriorVector,
        PrimeStar.firstExitCompressionProjection_apply, h, Y])
    obtain ⟨k, hvk, hak, hbk⟩ := exists_commonTarget_of_mem_firstExitCompressions
      hS (PrimeStar.sqrtCutoff_condition X) (hw a ha).1 (hw b hb).1 hva hvb
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hak, hbk⟩, hvk⟩
  have hlocal (k : PrimeStar.Vertex S X) (hk : k ∈ K) :
      ma * mb * (‖PrimeStar.euclideanCoordinateProjection (F k) x‖ *
        ‖PrimeStar.euclideanCoordinateProjection (F k) y‖) ≤ 10000 := by
    obtain ⟨hak, hbk⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨i, hi⟩ := exists_canonicalExitTarget_eq_of_smallPrimeAdj hS hak
    obtain ⟨j, hj⟩ := exists_canonicalExitTarget_eq_of_smallPrimeAdj hS hbk
    have hx := hr a ha i
    have hy := hr b hb j
    rw [hi] at hx
    rw [hj] at hy
    have hprod := mul_le_mul hx hy
      (mul_nonneg hmb.le (norm_nonneg _)) (by norm_num : (0 : ℝ) ≤ 100)
    dsimp only [ma, mb, F, x, y, Y]
    nlinarith [hprod]
  calc
    ma * mb * |⟪x, y⟫_ℝ| ≤ ma * mb * (∑ k ∈ K,
        ‖PrimeStar.euclideanCoordinateProjection (F k) x‖ *
          ‖PrimeStar.euclideanCoordinateProjection (F k) y‖) :=
      mul_le_mul_of_nonneg_left (abs_inner_le_sum_projectionNorms x y K F hcover)
        (mul_nonneg hma.le hmb.le)
    _ = ∑ k ∈ K, ma * mb * (‖PrimeStar.euclideanCoordinateProjection (F k) x‖ *
        ‖PrimeStar.euclideanCoordinateProjection (F k) y‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ _k ∈ K, (10000 : ℝ) := Finset.sum_le_sum hlocal
    _ = (K.card : ℝ) * 10000 := by simp
    _ ≤ (4 * Real.log (X : ℝ) / Real.log 2) * 10000 :=
      mul_le_mul_of_nonneg_right (card_common_smallPrimeTargets_le_log hab) (by norm_num)
    _ = _ := by ring

/-- The actual non-adjacent overlap has only a logarithmic shared-target cost.
All local full-response and root-gap inputs are discharged on the power range. -/
theorem eventually_powerRange_nonadjacent_fullMoleculeOverlap_energyProduct_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ a b : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) → InPowerRange theta X (b : ℕ) → a ≠ b →
      ¬(PrimeStar.smallPrimeGraph S X (squareRootCutoff X)).Adj a b →
        moleculeStarEnergy S X a * moleculeStarEnergy S X b *
          |⟪exactPrincipalMoleculeAmbientVector S X a,
            exactPrincipalMoleculeAmbientVector S X b⟫_ℝ| ≤
            (40000 / Real.log 2) * Real.log (X : ℝ) := by
  filter_upwards [eventually_powerRange_fullInteriorOverlap_energyProduct_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta] with X hi hw
  intro a b ha hb hab hnot
  rw [inner_fullMolecules_eq_inner_interiors_of_not_adjacent hS (hw a ha).1 (hw b hb).1 hab hnot]
  exact hi a b ha hb hab

end TargetResponseOverlap

noncomputable section CollectiveGram

open Filter Topology
open scoped Classical

/-- Prefix neighbours retain the cutoff `K`, not the full graph cutoff `X`. -/
theorem card_prefix_smallPrimeNeighbors_le
    {S : Finset ℕ} {X Y K : ℕ} (v : PrimeStar.Vertex S X) :
    (Finset.univ.filter (fun w : MoleculeCenter S X K ↦
      (PrimeStar.smallPrimeGraph S X Y).Adj v w.1)).card ≤
      K / (v : ℕ) + (v : ℕ).primeFactors.card := by
  let N := Finset.univ.filter (fun w : MoleculeCenter S X K ↦
    (PrimeStar.smallPrimeGraph S X Y).Adj v w.1)
  have hsub : N.image (fun w : MoleculeCenter S X K ↦ (w.1 : ℕ)) ⊆
      (Finset.Icc 1 (K / (v : ℕ))).image (fun p ↦ (v : ℕ) * p) ∪
        (v : ℕ).primeFactors.image (fun p ↦ (v : ℕ) / p) := by
    intro n hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨p, hp, _, _, hstep⟩ :=
      PrimeStar.smallPrimeGraph_adj_iff_smallPrimeAdj.mp (Finset.mem_filter.mp hw).2
    rcases hstep with hup | hdown
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_Icc.mpr ⟨hp.one_le, ?_⟩, hup⟩
      apply (Nat.le_div_iff_mul_le (PrimeStar.Vertex.coe_pos v)).mpr
      rw [Nat.mul_comm, hup]
      exact w.2
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨p, hp.mem_primeFactors ⟨(w.1 : ℕ), by rw [← hdown, Nat.mul_comm]⟩
        (PrimeStar.Vertex.coe_pos v).ne', ?_⟩
      rw [← hdown, Nat.mul_div_cancel _ hp.pos]
  have hinj : Function.Injective (fun w : MoleculeCenter S X K ↦ (w.1 : ℕ)) :=
    fun _ _ h ↦ Subtype.ext (Subtype.ext (Fin.ext h))
  calc
    N.card = (N.image (fun w : MoleculeCenter S X K ↦ (w.1 : ℕ))).card :=
      (Finset.card_image_of_injective N hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 (K / (v : ℕ))).image (fun p ↦ (v : ℕ) * p)).card +
        ((v : ℕ).primeFactors.image (fun p ↦ (v : ℕ) / p)).card := Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (K / (v : ℕ))).card + (v : ℕ).primeFactors.card :=
      add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp

private theorem weighted_row_scale
    {x a k ell h mu D N U : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hak : a ≤ k)
    (hell : 0 < ell) (hh : 0 < h) (hmu : 0 < mu)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hU : 0 ≤ U)
    (hscale : x / (8 * a * ell) ≤ mu ^ 2)
    (hrow : mu * U ≤ D * (k / a + ell / h) + N * k) :
    U ≤ (8 * ell / x * (D * k * (1 + ell / h) + N * k ^ 2)) * mu := by
  have hk : 0 ≤ k := ha.le.trans hak
  have hb : a * (D * (k / a + ell / h) + N * k) ≤
      D * k * (1 + ell / h) + N * k ^ 2 := by
    calc
      _ = D * k + D * a * (ell / h) + N * k * a := by field_simp
      _ ≤ D * k + D * k * (ell / h) + N * k * k := by gcongr
      _ = _ := by ring
  have hs : x ≤ 8 * a * ell * mu ^ 2 := by
    have := (div_le_iff₀ (by positivity : 0 < 8 * a * ell)).mp hscale
    nlinarith only [this]
  have hb' := (mul_le_mul_of_nonneg_left hrow ha.le).trans hb
  have ht : x * U ≤ 8 * ell * (D * k * (1 + ell / h) + N * k ^ 2) * mu := by
    have hp := mul_le_mul_of_nonneg_right hs hU
    have hq := mul_le_mul_of_nonneg_right hb' (show 0 ≤ 8 * ell * mu by positivity)
    nlinarith only [hp, hq]
  have hu : U ≤ (8 * ell * (D * k * (1 + ell / h) + N * k ^ 2) * mu) / x :=
    (le_div_iff₀ hx).mpr (by nlinarith only [ht])
  convert hu using 1
  ring

/-- The energy-weighted row of the actual real Gram defect, summed over the
complete prefix. Both overlap bounds and the restricted neighbour count are
discharged; no Gram hypothesis occurs in this statement. -/
theorem eventually_powerRange_fullMoleculeGram_weightedRow_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∀ a : MoleculeCenter S X K,
        ∑ b : MoleculeCenter S X K,
          |⟪exactPrincipalMoleculeAmbientVector S X a.1,
            exactPrincipalMoleculeAmbientVector S X b.1⟫_ℝ -
              (if a = b then 1 else 0)| * moleculeStarEnergy S X b.1 ≤
          (C * Real.log (X : ℝ) ^ 5 *
            (PrimeStar.sqrtCutoffResidualScale X * (K : ℝ) / (X : ℝ) +
              (K : ℝ) ^ 2 / (X : ℝ))) * moleculeStarEnergy S X a.1 := by
  obtain ⟨Ca, hCa, hadj⟩ :=
    eventually_powerRange_adjacent_fullMoleculeOverlap_energyProduct_le S hS htheta
  let N := 40000 / Real.log 2
  let C := 8 * (Ca * (1 + 1 / Real.log 2) + N)
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN : 0 < N := by dsimp [N]; positivity
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hadj,
    eventually_powerRange_nonadjacent_fullMoleculeOverlap_energyProduct_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 2]
    with X hadjX hn hw hs hL hX
  intro K hK a
  let L := Real.log (X : ℝ)
  let eta := PrimeStar.sqrtCutoffResidualScale X
  let D := Ca * eta * L ^ 3
  let G := PrimeStar.smallPrimeGraph S X (squareRootCutoff X)
  let f := fun b : MoleculeCenter S X K ↦ exactPrincipalMoleculeAmbientVector S X b.1
  let mu := fun b : MoleculeCenter S X K ↦ moleculeStarEnergy S X b.1
  let e := fun b : MoleculeCenter S X K ↦ |⟪f a, f b⟫_ℝ -
    (if a = b then 1 else 0)| * mu b
  have hrange (b : MoleculeCenter S X K) : InPowerRange theta X (b.1 : ℕ) :=
    ⟨b.1.property.1, (by exact_mod_cast b.2 : (b.1 : ℝ) ≤ K).trans hK⟩
  have hmu (b : MoleculeCenter S X K) : 0 < mu b :=
    Real.sqrt_pos.mpr (by exact_mod_cast (hw b.1 (hrange b)).2.1)
  have he (b : MoleculeCenter S X K) : 0 ≤ e b :=
    mul_nonneg (abs_nonneg _) (hmu b).le
  have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
    (PrimeStar.tunedSchurScale_nonneg _)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint (b : MoleculeCenter S X K) :
      mu a * e b ≤ (if G.Adj a.1 b.1 then D else 0) + N * L := by
    by_cases hab : a = b
    · subst b
      simp only [e, f, ↓reduceIte, real_inner_self_eq_norm_sq,
        norm_exactPrincipalMoleculeAmbientVector, one_pow, sub_self, abs_zero,
        zero_mul, mul_zero]
      positivity
    have habv : a.1 ≠ b.1 := fun h ↦ hab (Subtype.ext h)
    by_cases hg : G.Adj a.1 b.1
    · have h := hadjX a.1 b.1 (hrange a) (hrange b) hg
      rw [real_inner_comm] at h
      simp only [e, if_neg hab, sub_zero]
      dsimp only [mu, f]
      rw [if_pos hg]
      have : moleculeStarEnergy S X a.1 *
          (|⟪exactPrincipalMoleculeAmbientVector S X a.1,
            exactPrincipalMoleculeAmbientVector S X b.1⟫_ℝ| *
              moleculeStarEnergy S X b.1) ≤ D := by
        dsimp [D, eta, L]
        nlinarith only [h]
      exact this.trans (le_add_of_nonneg_right (by positivity))
    · have h := hn a.1 b.1 (hrange a) (hrange b) habv hg
      simp only [e, if_neg hab, sub_zero, if_neg hg, zero_add]
      dsimp only [mu, f, N, L]
      nlinarith only [h]
  have hcount : ((Finset.univ.filter (fun b : MoleculeCenter S X K ↦
      G.Adj a.1 b.1)).card : ℝ) ≤
      (K : ℝ) / (a.1 : ℝ) + L / Real.log 2 := by
    calc
      _ ≤ (K / (a.1 : ℕ) : ℕ) + ((a.1 : ℕ).primeFactors.card : ℝ) := by
        exact_mod_cast card_prefix_smallPrimeNeighbors_le (Y := squareRootCutoff X) a.1
      _ ≤ (K : ℝ) / (a.1 : ℝ) + Real.log (a.1 : ℝ) / Real.log 2 :=
        add_le_add Nat.cast_div_le (primeFactors_card_le_log_div_log_two a.1.property.1)
      _ ≤ _ := by
        gcongr
        exact Real.log_le_log (by exact_mod_cast a.1.property.1)
          (by exact_mod_cast PrimeStar.Vertex.coe_le a.1)
  have hsum : mu a * ∑ b, e b ≤
      D * ((K : ℝ) / (a.1 : ℝ) + L / Real.log 2) + N * L * K := by
    calc
      _ = ∑ b, mu a * e b := Finset.mul_sum _ _ _
      _ ≤ ∑ b, ((if G.Adj a.1 b.1 then D else 0) + N * L) :=
        Finset.sum_le_sum fun b _ ↦ hpoint b
      _ = ((Finset.univ.filter (fun b : MoleculeCenter S X K ↦ G.Adj a.1 b.1)).card : ℝ) * D +
          (Fintype.card (MoleculeCenter S X K) : ℝ) * (N * L) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp
      _ ≤ ((K : ℝ) / (a.1 : ℝ) + L / Real.log 2) * D + (K : ℝ) * (N * L) :=
        add_le_add (mul_le_mul_of_nonneg_right hcount hD)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast card_moleculeCenter_le S X K)
            (by positivity))
      _ = _ := by ring
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hap : 0 < (a.1 : ℝ) := by exact_mod_cast a.1.property.1
  have hak : (a.1 : ℝ) ≤ K := by exact_mod_cast a.2
  have hscale := weighted_row_scale hx hap hak hLpos hh (hmu a) hD
    (show 0 ≤ N * L by positivity) (Finset.sum_nonneg fun b _ ↦ he b)
    (hs a.1 (hrange a)).1 hsum
  have hcoef : 8 * L / (X : ℝ) *
      (D * (K : ℝ) * (1 + L / Real.log 2) + (N * L) * (K : ℝ) ^ 2) ≤
      C * L ^ 5 * (eta * (K : ℝ) / (X : ℝ) + (K : ℝ) ^ 2 / (X : ℝ)) := by
    have hfactor : 1 + L / Real.log 2 ≤ (1 + 1 / Real.log 2) * L := by
      calc
        _ ≤ L + L / Real.log 2 := add_le_add hL le_rfl
        _ = _ := by ring
    calc
      _ ≤ 8 * L / (X : ℝ) *
          (D * (K : ℝ) * ((1 + 1 / Real.log 2) * L) + N * L * (K : ℝ) ^ 2) := by gcongr
      _ = 8 * Ca * (1 + 1 / Real.log 2) * L ^ 5 * (eta * K / (X : ℝ)) +
          8 * N * L ^ 2 * ((K : ℝ) ^ 2 / (X : ℝ)) := by dsimp [D]; ring
      _ ≤ 8 * Ca * (1 + 1 / Real.log 2) * L ^ 5 * (eta * K / (X : ℝ)) +
          8 * N * L ^ 5 * ((K : ℝ) ^ 2 / (X : ℝ)) := by
        gcongr
        norm_num
      _ ≤ _ := by
        dsimp [C]
        nlinarith [mul_nonneg (show 0 ≤ 8 * N * L ^ 5 by positivity)
          (show 0 ≤ eta * K / (X : ℝ) by positivity),
          mul_nonneg (show 0 ≤ 8 * Ca * (1 + 1 / Real.log 2) * L ^ 5 by positivity)
          (show 0 ≤ (K : ℝ) ^ 2 / (X : ℝ) by positivity)]
  exact hscale.trans (mul_le_mul_of_nonneg_right hcoef (hmu a).le)

/-- The actual phase-fixed raw Gram is small at an explicit collective scale.
The Schur weights are the source-star energies, rather than the constant weight. -/
theorem eventually_powerRange_phasedFullStarFrame_gram_error_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
        matrixL2OperatorNorm ((phasedFullStarFrame S X K)ᴴ *
          phasedFullStarFrame S X K - 1) ≤
          C * Real.log (X : ℝ) ^ 5 *
            (PrimeStar.sqrtCutoffResidualScale X * (K : ℝ) / (X : ℝ) +
              (K : ℝ) ^ 2 / (X : ℝ)) := by
  obtain ⟨C, hC, hr⟩ := eventually_powerRange_fullMoleculeGram_weightedRow_le S hS htheta
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hr, eventually_powerRange_exactPrincipalMoleculeRoot_window S hS htheta,
    eventually_ge_atTop 2] with X hrX hw hX
  intro K hK
  let f := fun a : MoleculeCenter S X K ↦ exactPrincipalMoleculeAmbientVector S X a.1
  let p := fun a : MoleculeCenter S X K ↦ fullStarMoleculePhase S X a.1
  let A : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℝ := fun a b ↦
    p a * p b * (⟪f a, f b⟫_ℝ - if a = b then 1 else 0)
  let T := C * Real.log (X : ℝ) ^ 5 *
    (PrimeStar.sqrtCutoffResidualScale X * (K : ℝ) / (X : ℝ) +
      (K : ℝ) ^ 2 / (X : ℝ))
  have hphase (a : MoleculeCenter S X K) : |p a| = 1 := abs_fullStarMoleculePhase S X a.1
  have hAabs (a b : MoleculeCenter S X K) :
      |A a b| = |⟪f a, f b⟫_ℝ - if a = b then 1 else 0| := by
    simp only [A, abs_mul, hphase, one_mul]
  have hAnorm : ‖A‖ ≤ T := by
    apply symmetric_l2_opNorm_le_weightedAbsoluteRow A
      (fun a ↦ moleculeStarEnergy S X a.1) T
    · have heta : 0 ≤ PrimeStar.sqrtCutoffResidualScale X :=
        mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le (PrimeStar.tunedSchurScale_nonneg _)
      have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
      dsimp [T]
      positivity
    · intro a b
      dsimp [A]
      rw [real_inner_comm (f a) (f b)]
      simp only [eq_comm]
      ring
    · intro a
      have ha : InPowerRange theta X (a.1 : ℕ) :=
        ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ K).trans hK⟩
      exact Real.sqrt_pos.mpr (by exact_mod_cast (hw a.1 ha).2.1)
    · intro a
      simp only [hAabs]
      exact hrX K hK a
  have hgram : (phasedFullStarFrame S X K)ᴴ * phasedFullStarFrame S X K - 1 =
      complexifyRealMatrix A := by
    ext a b
    have hinner : ((phasedFullStarFrame S X K)ᴴ * phasedFullStarFrame S X K) a b =
        ⟪phasedFullStarMolecule S X a.1, phasedFullStarMolecule S X b.1⟫_ℂ := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, phasedFullStarFrame,
        PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    rw [Matrix.sub_apply, hinner]
    simp only [phasedFullStarMolecule, inner_smul_left, inner_smul_right,
      PrimeStar.inner_complexifyEuclidean, Complex.conj_ofReal, complexifyRealMatrix_apply]
    by_cases hab : a = b
    · subst b
      have hp : p a * p a = 1 := by
        nlinarith [sq_abs (p a), hphase a]
      have hpc : (p a : ℂ) * (p a : ℂ) = 1 := by exact_mod_cast hp
      simp only [A, Matrix.one_apply_eq]
      push_cast
      dsimp only [p, f] at *
      linear_combination hpc
    · simp only [A, if_neg hab, Matrix.one_apply_ne hab, sub_zero]
      push_cast
      dsimp only [p, f]
      ring
  rw [hgram]
  have h := (rectangular_complexification_operatorNorm_le A).trans
    (mul_le_mul_of_nonneg_left hAnorm (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [T, mul_assoc] using h

/-- The phase-fixed raw Gram tends uniformly to the identity on every
complete prefix below a fixed sub-square-root power. -/
theorem eventually_powerRange_phasedFullStarFrame_gram_error_lt
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixL2OperatorNorm ((phasedFullStarFrame S X K)ᴴ *
        phasedFullStarFrame S X K - 1) < δ := by
  obtain ⟨C, hC, hb⟩ := eventually_powerRange_phasedFullStarFrame_gram_error_le S hS htheta
  let H := 2 * PrimeStar.sqrtCutoffResidualConstant
  have hH : 0 < H := mul_pos (by norm_num) PrimeStar.sqrtCutoffResidualConstant_pos
  have hlim1 : Tendsto (fun X : ℕ ↦ C * H * Real.log (X : ℝ) ^ 5 *
      Real.sqrt (X : ℝ) * powerScale theta X / (X : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero (5 : ℝ)
      (show (1 / 2 : ℝ) + theta < 1 by linarith)).const_mul (C * H)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hx : 0 < (X : ℝ) := by exact_mod_cast hX
    rw [Real.rpow_add hx, Real.rpow_one]
    simp [powerScale, Real.sqrt_eq_rpow, mul_div_assoc]
    ring
  have hlim2 : Tendsto (fun X : ℕ ↦ C * Real.log (X : ℝ) ^ 5 *
      powerScale theta X ^ 2 / (X : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero (5 : ℝ)
      (show theta * 2 < (1 : ℝ) by linarith)).const_mul C
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hx : 0 ≤ (X : ℝ) := by positivity
    rw [Real.rpow_mul hx, Real.rpow_two]
    simp [powerScale, mul_div_assoc]
    ring
  have hlim := hlim1.add hlim2
  simp only [add_zero] at hlim
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hb, PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
    hlim.eventually_lt_const hδ, hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with X hbX he hsmall hL hX
  intro K hK
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hsqrt : Real.sqrt (X : ℝ) ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by nlinarith⟩
  have heta : 0 ≤ PrimeStar.sqrtCutoffResidualScale X :=
    mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le (PrimeStar.tunedSchurScale_nonneg _)
  have hEta : PrimeStar.sqrtCutoffResidualScale X ≤ H * Real.sqrt (X : ℝ) := by
    apply (sq_le_sq₀ heta (by positivity)).mp
    calc
      _ ≤ 4 * PrimeStar.sqrtCutoffResidualConstant ^ 2 *
          (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := he
      _ ≤ 4 * PrimeStar.sqrtCutoffResidualConstant ^ 2 * (X : ℝ) := by
        gcongr
        exact (div_le_self (Real.sqrt_nonneg _) hL).trans hsqrt
      _ = _ := by dsimp [H]; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  apply (hbX K hK).trans_lt
  apply lt_of_le_of_lt _ hsmall
  calc
    _ ≤ C * Real.log (X : ℝ) ^ 5 *
        (H * Real.sqrt (X : ℝ) * powerScale theta X / (X : ℝ) +
          powerScale theta X ^ 2 / (X : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- Collective Gram smallness for the actual projected and column-normalized
prefix. This discharges the Gram input of symmetric reorthonormalization. -/
theorem eventually_powerRange_projectedFullStarFrame_gram_error_lt
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      matrixL2OperatorNorm ((projectedFullStarFrame S X K)ᴴ *
        projectedFullStarFrame S X K - 1) < δ := by
  filter_upwards [eventually_powerRange_projectedFullStarFrame_gram_error_le S hS htheta,
    eventually_powerRange_phasedFullStarFrame_gram_error_lt S hS htheta
      (show 0 < δ / 8 by positivity),
    eventually_powerRange_fullStarFrameTail_hsSq_lt S hS htheta
      (show 0 < δ / 16 by positivity)] with X hb hr ht
  intro K hK
  have h := hb K hK
  have h1 := hr K hK
  have h2 := ht K hK
  linarith

end CollectiveGram

noncomputable section FrameWhitening

open scoped ComplexOrder MatrixOrder

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- Gram matrix of a rectangular frame matrix. -/
def frameGram (V : Matrix n m ℂ) : Matrix m m ℂ :=
  Vᴴ * V

/-- Reorthonormalized frame obtained from a right normalizer `W`. -/
def normalizedFrame (V : Matrix n m ℂ) (W : Matrix m m ℂ) : Matrix n m ℂ :=
  V * W

/-- Canonical right normalizer of a positive-definite Gram matrix. -/
noncomputable def inverseSqrtNormalizer [DecidableEq m]
    (G : Matrix m m ℂ) : Matrix m m ℂ :=
  (CFC.sqrt G)⁻¹

/-- A frame with injective synthesis map has positive-definite Gram matrix.
This is the finite-dimensional form of the full-column-rank hypothesis in
manuscript Lemma 5.1. -/
theorem frameGram_posDef_of_mulVec_injective
    [DecidableEq m] {V : Matrix n m ℂ}
    (hV : Function.Injective fun x : m → ℂ ↦ V *ᵥ x) :
    (frameGram V).PosDef := by
  have hGramInjective :
      Function.Injective fun x : m → ℂ ↦ frameGram V *ᵥ x := by
    intro x y hxy
    have hzero : frameGram V *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hxy
    have hVzero : V *ᵥ (x - y) = 0 := by
      exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero V (x - y)).mp
        (by simpa [frameGram] using hzero)
    apply hV
    simpa [Matrix.mulVec_sub, sub_eq_zero] using hVzero
  have hGramUnit : IsUnit (frameGram V) :=
    Matrix.mulVec_injective_iff_isUnit.mp hGramInjective
  exact (Matrix.posSemidef_conjTranspose_mul_self V).posDef_iff_isUnit.mpr hGramUnit

/-- The inverse square root of a positive-definite Gram matrix normalizes it
exactly.

This closes the construction and isometry assertion in manuscript (5.3).
The dimension-free commutator estimate in (5.4) is a separate theorem.
-/
theorem inverseSqrtNormalizer_normalizes
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef) :
    (inverseSqrtNormalizer G)ᴴ * G * inverseSqrtNormalizer G = 1 := by
  have hstrict : IsStrictlyPositive G :=
    hG.isStrictlyPositive
  have hsqrtUnit : IsUnit (CFC.sqrt G) :=
    CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hstrict
  have hsqrtDetUnit : IsUnit (CFC.sqrt G).det :=
    (Matrix.isUnit_iff_isUnit_det (CFC.sqrt G)).mp hsqrtUnit
  have hsqrtStar : (CFC.sqrt G)ᴴ = CFC.sqrt G :=
    (CFC.sqrt_nonneg G).star_eq
  have hsqrtInvStar : ((CFC.sqrt G)⁻¹)ᴴ = (CFC.sqrt G)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hsqrtStar]
  rw [inverseSqrtNormalizer, hsqrtInvStar]
  calc
    (CFC.sqrt G)⁻¹ * G * (CFC.sqrt G)⁻¹ =
        (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G) *
          (CFC.sqrt G)⁻¹ := by
            rw [CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
    _ = ((CFC.sqrt G)⁻¹ * CFC.sqrt G) *
          (CFC.sqrt G * (CFC.sqrt G)⁻¹) := by
            simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ hsqrtDetUnit,
        Matrix.mul_nonsing_inv _ hsqrtDetUnit, Matrix.one_mul]

/-- A frame with positive-definite Gram matrix becomes an isometry after
canonical inverse-square-root normalization. -/
theorem normalizedFrame_inverseSqrt_isometry
    [DecidableEq m] {V : Matrix n m ℂ} (hG : (frameGram V).PosDef) :
    (normalizedFrame V (inverseSqrtNormalizer (frameGram V)))ᴴ *
        normalizedFrame V (inverseSqrtNormalizer (frameGram V)) = 1 := by
  calc
    (normalizedFrame V (inverseSqrtNormalizer (frameGram V)))ᴴ *
          normalizedFrame V (inverseSqrtNormalizer (frameGram V)) =
        (inverseSqrtNormalizer (frameGram V))ᴴ * frameGram V *
          inverseSqrtNormalizer (frameGram V) := by
            simp only [normalizedFrame, frameGram, Matrix.conjTranspose_mul,
              Matrix.mul_assoc]
    _ = 1 := inverseSqrtNormalizer_normalizes hG

/-- Exact frame commutator, manuscript equation (5.2). -/
theorem frame_commutator
    {T : Matrix n n ℂ} {V : Matrix n m ℂ}
    {D : Matrix m m ℂ} {J : Matrix n m ℂ}
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hTV : T * V = V * D + J) :
    D * frameGram V - frameGram V * D = Vᴴ * J - Jᴴ * V := by
  rw [frameGram]
  have hstar : Vᴴ * T = D * Vᴴ + Jᴴ := by
    have h := congrArg Matrix.conjTranspose hTV
    simpa [Matrix.conjTranspose_mul, hT.eq, hD.eq] using h
  calc
    D * (Vᴴ * V) - (Vᴴ * V) * D
        = (D * Vᴴ) * V - Vᴴ * (V * D) := by
            simp only [Matrix.mul_assoc]
    _ = (Vᴴ * T - Jᴴ) * V - Vᴴ * (T * V - J) := by
          rw [eq_sub_iff_add_eq.mpr hstar.symm,
            eq_sub_iff_add_eq.mpr hTV.symm]
    _ = Vᴴ * J - Jᴴ * V := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
          exact sub_sub_sub_cancel_left (Jᴴ * V) (Vᴴ * J) (Vᴴ * (T * V))

/-- Exact residual formula after right reorthonormalization. -/
theorem normalizedFrame_residual_eq
    {T : Matrix n n ℂ} {V : Matrix n m ℂ}
    {D W : Matrix m m ℂ} {J : Matrix n m ℂ}
    (hTV : T * V = V * D + J) :
    T * normalizedFrame V W - normalizedFrame V W * D =
      V * (D * W - W * D) + J * W := by
  rw [normalizedFrame]
  calc
    T * (V * W) - (V * W) * D = (T * V) * W - V * (W * D) := by
      simp only [Matrix.mul_assoc]
    _ = (V * D + J) * W - V * (W * D) := by rw [hTV]
    _ = V * (D * W - W * D) + J * W := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
      rw [sub_add_eq_add_sub]

/-- Algebraic operator-norm estimate behind the inverse-square-root
commutator.  Here `G = S²`, `W = S⁻¹`, `S` is within `1/2` of the identity,
and `W` has norm at most `2`.

The constant `4` is deliberately non-sharp and dimension-free. -/
theorem inverse_commutator_l2_opNorm_le_of_square_near_one
    [DecidableEq m] (D G S W : Matrix m m ℂ)
    (hG : G = S * S)
    (hSW : S * W = 1) (hWS : W * S = 1)
    (hnear : ‖S - 1‖ ≤ (1 : ℝ) / 2)
    (hWnorm : ‖W‖ ≤ 2) :
    ‖D * W - W * D‖ ≤ 4 * ‖D * G - G * D‖ := by
  let X : Matrix m m ℂ := D * S - S * D
  let B : Matrix m m ℂ := D * G - G * D
  let E : Matrix m m ℂ := S - 1
  have hB : B = X * S + S * X := by
    simp only [B, X, hG]
    noncomm_ring
  have hS : S = 1 + E := by
    simp [E]
  have hBexpand : B = (X + X) + (X * E + E * X) := by
    rw [hB, hS]
    noncomm_ring
  have hrest : ‖X * E + E * X‖ ≤ ‖X‖ := by
    calc
      ‖X * E + E * X‖ ≤ ‖X * E‖ + ‖E * X‖ := norm_add_le _ _
      _ ≤ ‖X‖ * ‖E‖ + ‖E‖ * ‖X‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖X‖ := by
        have hE : ‖E‖ ≤ (1 : ℝ) / 2 := by simpa [E] using hnear
        nlinarith [norm_nonneg X, norm_nonneg E]
  have hdouble : ‖X + X‖ = 2 * ‖X‖ := by
    rw [← two_smul ℂ X, norm_smul]
    norm_num
  have hXle : ‖X‖ ≤ ‖B‖ := by
    have hrearr : X + X = B - (X * E + E * X) := by
      rw [hBexpand]
      abel
    have htriangle : ‖X + X‖ ≤ ‖B‖ + ‖X * E + E * X‖ := by
      rw [hrearr]
      exact norm_sub_le _ _
    rw [hdouble] at htriangle
    nlinarith [hrest, norm_nonneg X, norm_nonneg B]
  have hcommW : D * W - W * D = -(W * X * W) := by
    have hWXW :
        W * X * W = W * D * (S * W) - (W * S) * D * W := by
      simp only [X, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [hWXW, hSW, hWS]
    simp only [Matrix.mul_one, Matrix.one_mul]
    abel
  calc
    ‖D * W - W * D‖ = ‖W * X * W‖ := by rw [hcommW, norm_neg]
    _ ≤ (‖W‖ * ‖X‖) * ‖W‖ := by
      exact (norm_mul_le (W * X) W).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le W X) (norm_nonneg W))
    _ ≤ 4 * ‖B‖ := by
      have hleft : ‖W‖ * ‖X‖ ≤ 2 * ‖X‖ :=
        mul_le_mul_of_nonneg_right hWnorm (norm_nonneg X)
      calc
        (‖W‖ * ‖X‖) * ‖W‖ ≤ (2 * ‖X‖) * 2 :=
          mul_le_mul hleft hWnorm (norm_nonneg W) (by positivity)
        _ = 4 * ‖X‖ := by ring
        _ ≤ 4 * ‖B‖ := mul_le_mul_of_nonneg_left hXle (by positivity)
    _ = 4 * ‖D * G - G * D‖ := by rfl

/-- Canonical square-root adapter for the algebraic commutator estimate.
The two norm bounds are separated explicitly so that the matrix algebra is
independent of the later spectral localization argument. -/
theorem inverseSqrtNormalizer_commutator_l2_opNorm_le_of_sqrt_bounds
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef)
    (D : Matrix m m ℂ)
    (hnear : ‖CFC.sqrt G - 1‖ ≤ (1 : ℝ) / 2)
    (hWnorm : ‖inverseSqrtNormalizer G‖ ≤ 2) :
    ‖D * inverseSqrtNormalizer G - inverseSqrtNormalizer G * D‖ ≤
      4 * ‖D * G - G * D‖ := by
  have hsqrtUnit : IsUnit (CFC.sqrt G) :=
    CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hG.isStrictlyPositive
  have hdet : IsUnit (CFC.sqrt G).det :=
    (Matrix.isUnit_iff_isUnit_det (CFC.sqrt G)).mp hsqrtUnit
  apply inverse_commutator_l2_opNorm_le_of_square_near_one
    D G (CFC.sqrt G) (inverseSqrtNormalizer G)
  · exact (CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg).symm
  · simpa [inverseSqrtNormalizer] using Matrix.mul_nonsing_inv (CFC.sqrt G) hdet
  · simpa [inverseSqrtNormalizer] using Matrix.nonsing_inv_mul (CFC.sqrt G) hdet
  · exact hnear
  · exact hWnorm

/-- Every eigenvalue of a positive Gram matrix lies in the same scalar
neighbourhood of `1` as the matrix itself in operator norm. -/
theorem gram_eigenvalue_abs_sub_one_le
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef)
    (hnear : ‖G - 1‖ ≤ (1 : ℝ) / 2) (i : m) :
    |hG.isHermitian.eigenvalues i - 1| ≤ (1 : ℝ) / 2 := by
  have hspec := norm_apply_le_norm_cfc (fun x : ℝ ↦ x - 1) G
    (hG.isHermitian.eigenvalues_mem_spectrum_real i)
  have hcfc : cfc (fun x : ℝ ↦ x - 1) G = G - 1 := by
    rw [cfc_sub (fun x : ℝ ↦ x) (fun _ : ℝ ↦ 1) G,
      cfc_id' ℝ G, cfc_const_one ℝ G]
  rw [Real.norm_eq_abs, hcfc] at hspec
  exact hspec.trans hnear

/-- Operator norm is invariant under unitary conjugation. -/
theorem l2_opNorm_unitary_conjugation
    [DecidableEq m] (U : unitary (Matrix m m ℂ)) (A : Matrix m m ℂ) :
    ‖(U : Matrix m m ℂ) * A * (U : Matrix m m ℂ)ᴴ‖ = ‖A‖ := by
  rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star]
  exact (CStarRing.norm_mul_coe_unitary ((U : Matrix m m ℂ) * A) (star U)).trans
    (CStarRing.norm_coe_unitary_mul U A)

/-- Spectral diagonalization of the CFC square root of a positive-definite
matrix. -/
theorem cfcSqrt_eq_unitary_diagonal
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef) :
    CFC.sqrt G =
      (hG.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *
        Matrix.diagonal (fun i ↦
          ((Real.sqrt (hG.isHermitian.eigenvalues i) : ℝ) : ℂ)) *
        (hG.isHermitian.eigenvectorUnitary : Matrix m m ℂ)ᴴ := by
  let hH : G.IsHermitian := hG.isHermitian
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ G, hH.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose]
  simp [Function.comp_def, Real.coe_sqrt,
    hG.posSemidef.eigenvalues_nonneg]

/-- The CFC square root remains within `1/2` of the identity whenever its
positive input is within `1/2` of the identity. -/
theorem cfcSqrt_sub_one_l2_opNorm_le
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef)
    (hnear : ‖G - 1‖ ≤ (1 : ℝ) / 2) :
    ‖CFC.sqrt G - 1‖ ≤ (1 : ℝ) / 2 := by
  let Uu := hG.isHermitian.eigenvectorUnitary
  let U : Matrix m m ℂ := Uu
  let lam := hG.isHermitian.eigenvalues
  let A : Matrix m m ℂ := Matrix.diagonal fun i ↦
    ((Real.sqrt (lam i) : ℝ) : ℂ)
  have hrow : U * Uᴴ = 1 := by
    have hu := Unitary.coe_mul_star_self Uu
    rw [Unitary.coe_star, Matrix.star_eq_conjTranspose] at hu
    exact hu
  have hsqrt : CFC.sqrt G = U * A * Uᴴ := by
    simpa only [Uu, U, A, lam] using cfcSqrt_eq_unitary_diagonal hG
  have hdiff : CFC.sqrt G - 1 = U * (A - 1) * Uᴴ := by
    rw [hsqrt]
    calc
      U * A * Uᴴ - 1 = U * A * Uᴴ - U * Uᴴ := by rw [hrow]
      _ = U * (A - 1) * Uᴴ := by noncomm_ring
  rw [hdiff]
  have hnorm : ‖U * (A - 1) * Uᴴ‖ = ‖A - 1‖ := by
    simpa only [U] using l2_opNorm_unitary_conjugation Uu (A - 1)
  rw [hnorm]
  have hAdiag : A - 1 = Matrix.diagonal fun i ↦
      (((Real.sqrt (lam i) - 1 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A]
    · simp [A, hij]
  rw [hAdiag, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  have hclose := gram_eigenvalue_abs_sub_one_le hG hnear i
  have hlam0 : 0 ≤ lam i := hG.posSemidef.eigenvalues_nonneg i
  have hsqrt0 : 0 ≤ Real.sqrt (lam i) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (lam i)) ^ 2 = lam i := Real.sq_sqrt hlam0
  have hlamLow : (1 : ℝ) / 2 ≤ lam i := by
    rw [abs_le] at hclose
    linarith
  have hlamHigh : lam i ≤ (3 : ℝ) / 2 := by
    rw [abs_le] at hclose
    linarith
  have hsqrtLow : (1 : ℝ) / 2 ≤ Real.sqrt (lam i) := by nlinarith
  have hsqrtHigh : Real.sqrt (lam i) ≤ (3 : ℝ) / 2 := by nlinarith
  norm_cast
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- A frame whose Gram matrix is within `1/2` of the identity has operator
norm at most `2`.  The constant is deliberately non-sharp. -/
theorem frame_l2_opNorm_le_two_of_gram_near
    [DecidableEq m] (V : Matrix n m ℂ)
    (hnear : ‖frameGram V - 1‖ ≤ (1 : ℝ) / 2) :
    ‖V‖ ≤ 2 := by
  have hGram : ‖frameGram V‖ ≤ (3 : ℝ) / 2 := by
    have hdecomp : frameGram V = (frameGram V - 1) + 1 := by abel
    have hone : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
      have honeDiag : (1 : Matrix m m ℂ) = Matrix.diagonal fun _ ↦ (1 : ℂ) := by
        ext i j
        simp [Matrix.one_apply]
      rw [honeDiag, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ by simp
    calc
      ‖frameGram V‖ = ‖(frameGram V - 1) + 1‖ := congrArg norm hdecomp
      _ ≤ ‖frameGram V - 1‖ + ‖(1 : Matrix m m ℂ)‖ := norm_add_le _ _
      _ ≤ (1 : ℝ) / 2 + 1 := by
        linarith
      _ = (3 : ℝ) / 2 := by ring
  have hsq : ‖V‖ * ‖V‖ = ‖frameGram V‖ := by
    simpa [frameGram] using (Matrix.l2_opNorm_conjTranspose_mul_self V).symm
  nlinarith [norm_nonneg V]

/-- A frame whose Gram matrix is strictly less than one operator-norm unit
from the identity has injective synthesis.  This removes a separate
full-column-rank hypothesis from collision certificates. -/
theorem frame_mulVec_injective_of_gram_sub_one_norm_lt_one
    [DecidableEq m] (V : Matrix n m ℂ)
    (hnear : ‖frameGram V - 1‖ < 1) :
    Function.Injective fun x : m → ℂ ↦ V *ᵥ x := by
  classical
  cases isEmpty_or_nonempty m with
  | inl _ =>
      intro x y _hxy
      exact Subsingleton.elim x y
  | inr hm =>
      letI : Nonempty m := hm
      have hnorm : ‖1 - frameGram V‖ < 1 := by
        have hneg : 1 - frameGram V = -(frameGram V - 1) := by abel
        rw [hneg, norm_neg]
        exact hnear
      have hunit : IsUnit (frameGram V) := by
        have h := isUnit_one_sub_of_norm_lt_one hnorm
        simpa only [sub_sub_cancel] using h
      have hGramInj : Function.Injective
          (fun x : m → ℂ ↦ frameGram V *ᵥ x) :=
        Matrix.mulVec_injective_iff_isUnit.mpr hunit
      intro x y hxy
      apply hGramInj
      change (Vᴴ * V) *ᵥ x = (Vᴴ * V) *ᵥ y
      rw [← Matrix.mulVec_mulVec x Vᴴ V,
        ← Matrix.mulVec_mulVec y Vᴴ V]
      change V *ᵥ x = V *ᵥ y at hxy
      exact congrArg (fun z ↦ Vᴴ *ᵥ z) hxy

/-- The Gram commutator is controlled in operator norm by the approximate
intertwining residual. -/
theorem frame_commutator_l2_opNorm_le
    [DecidableEq m] [DecidableEq n]
    {T : Matrix n n ℂ} {V : Matrix n m ℂ}
    {D : Matrix m m ℂ} {J : Matrix n m ℂ}
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hTV : T * V = V * D + J)
    (hnear : ‖frameGram V - 1‖ ≤ (1 : ℝ) / 2) :
    ‖D * frameGram V - frameGram V * D‖ ≤ 4 * ‖J‖ := by
  have hV : ‖V‖ ≤ 2 := frame_l2_opNorm_le_two_of_gram_near V hnear
  rw [frame_commutator hT hD hTV]
  calc
    ‖Vᴴ * J - Jᴴ * V‖ ≤ ‖Vᴴ * J‖ + ‖Jᴴ * V‖ := norm_sub_le _ _
    _ ≤ ‖Vᴴ‖ * ‖J‖ + ‖Jᴴ‖ * ‖V‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = ‖V‖ * ‖J‖ + ‖J‖ * ‖V‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    _ ≤ 4 * ‖J‖ := by nlinarith [norm_nonneg J, norm_nonneg V]

theorem matrixL2OperatorNorm_nonneg [DecidableEq n] (A : Matrix m n ℂ) :
    0 ≤ matrixL2OperatorNorm A := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.instL2OpNormedAddCommGroup
  exact norm_nonneg A

theorem matrixFrobeniusNorm_conjTranspose (A : Matrix m n ℂ) :
    matrixFrobeniusNorm Aᴴ = matrixFrobeniusNorm A := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  letI : NormedAddCommGroup (Matrix n m ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  exact Matrix.frobenius_norm_conjTranspose A

theorem matrixL2OperatorNorm_conjTranspose
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    matrixL2OperatorNorm Aᴴ = matrixL2OperatorNorm A := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.instL2OpNormedAddCommGroup
  letI : NormedAddCommGroup (Matrix n m ℂ) :=
    Matrix.instL2OpNormedAddCommGroup
  exact Matrix.l2_opNorm_conjTranspose A

theorem matrixFrobeniusNorm_sub_le (A B : Matrix m n ℂ) :
    matrixFrobeniusNorm (A - B) ≤
      matrixFrobeniusNorm A + matrixFrobeniusNorm B := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  exact norm_sub_le A B

theorem matrixFrobeniusNorm_neg (A : Matrix m n ℂ) :
    matrixFrobeniusNorm (-A) = matrixFrobeniusNorm A := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  exact norm_neg A

theorem matrixFrobeniusNorm_smul (c : ℂ) (A : Matrix m n ℂ) :
    matrixFrobeniusNorm (c • A) = ‖c‖ * matrixFrobeniusNorm A := by
  letI : NormedAddCommGroup (Matrix m n ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℂ (Matrix m n ℂ) := Matrix.frobeniusNormedSpace
  exact norm_smul c A

/-- Left multiplication is bounded by operator norm times Hilbert--Schmidt
norm. -/
theorem matrixFrobeniusNorm_mul_le_operator_left
    [DecidableEq m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    matrixFrobeniusNorm (A * B) ≤
      matrixL2OperatorNorm A * matrixFrobeniusNorm B := by
  have hcol : ∀ j,
      (∑ i, ‖(A * B) i j‖ ^ 2) ≤
        matrixL2OperatorNorm A ^ 2 * (∑ k, ‖B k j‖ ^ 2) := by
    intro j
    let x : EuclideanSpace ℂ m :=
      (EuclideanSpace.equiv m ℂ).symm (fun k ↦ B k j)
    have hop := Matrix.l2_opNorm_mulVec A x
    change ‖(EuclideanSpace.equiv l ℂ).symm <| A *ᵥ x‖ ≤
      matrixL2OperatorNorm A * ‖x‖ at hop
    have hop' :
        ‖(EuclideanSpace.equiv l ℂ).symm <| A *ᵥ x‖ ^ 2 ≤
          (matrixL2OperatorNorm A * ‖x‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
        (matrixL2OperatorNorm_nonneg A) (norm_nonneg x))).2 hop
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hop'
    simpa [x, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_pow,
      Finset.mul_sum] using hop'
  have hsum :
      (∑ i, ∑ j, ‖(A * B) i j‖ ^ 2) ≤
        matrixL2OperatorNorm A ^ 2 * (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, ‖(A * B) i j‖ ^ 2) ≤
          ∑ j, matrixL2OperatorNorm A ^ 2 * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun j _ ↦ hcol j
      _ = matrixL2OperatorNorm A ^ 2 * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        rw [Finset.mul_sum]
      _ = matrixL2OperatorNorm A ^ 2 * (∑ k, ∑ j, ‖B k j‖ ^ 2) := by
        rw [Finset.sum_comm]
  have hsq : matrixFrobeniusNorm (A * B) ^ 2 ≤
      (matrixL2OperatorNorm A * matrixFrobeniusNorm B) ^ 2 := by
    rw [matrixFrobeniusNorm_sq, mul_pow, matrixFrobeniusNorm_sq]
    exact hsum
  exact (sq_le_sq₀ (matrixFrobeniusNorm_nonneg _)
    (mul_nonneg (matrixL2OperatorNorm_nonneg A)
      (matrixFrobeniusNorm_nonneg B))).mp hsq

/-- Right multiplication is bounded by Hilbert--Schmidt norm times operator
norm. -/
theorem matrixFrobeniusNorm_mul_le_operator_right
    [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    matrixFrobeniusNorm (A * B) ≤
      matrixFrobeniusNorm A * matrixL2OperatorNorm B := by
  calc
    matrixFrobeniusNorm (A * B) = matrixFrobeniusNorm (A * B)ᴴ :=
      (matrixFrobeniusNorm_conjTranspose (A * B)).symm
    _ = matrixFrobeniusNorm (Bᴴ * Aᴴ) := by
      rw [Matrix.conjTranspose_mul]
    _ ≤ matrixL2OperatorNorm Bᴴ * matrixFrobeniusNorm Aᴴ :=
      matrixFrobeniusNorm_mul_le_operator_left Bᴴ Aᴴ
    _ = matrixFrobeniusNorm A * matrixL2OperatorNorm B := by
      rw [matrixL2OperatorNorm_conjTranspose,
        matrixFrobeniusNorm_conjTranspose, mul_comm]

/-- The inverse square root is bounded using the square-root neighbourhood
and its exact inverse equation. No separate spectral inverse API is needed. -/
theorem inverseSqrtNormalizer_l2_opNorm_le
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef)
    (hnear : ‖G - 1‖ ≤ (1 : ℝ) / 2) :
    ‖inverseSqrtNormalizer G‖ ≤ 2 := by
  let S := CFC.sqrt G
  let W := inverseSqrtNormalizer G
  have hS : ‖S - 1‖ ≤ (1 : ℝ) / 2 := cfcSqrt_sub_one_l2_opNorm_le hG hnear
  have hunit : IsUnit S := CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hG.isStrictlyPositive
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hunit
  have hSW : S * W = 1 := Matrix.mul_nonsing_inv S hdet
  have heq : W = 1 - (S - 1) * W := by rw [Matrix.sub_mul, hSW, Matrix.one_mul]; abel
  have hone : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
    have hdiag : (1 : Matrix m m ℂ) = Matrix.diagonal fun _ ↦ (1 : ℂ) := by
      ext i j
      simp [Matrix.one_apply]
    rw [hdiag, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ by simp
  have ht : ‖W‖ ≤ 1 + (1 / 2 : ℝ) * ‖W‖ := by
    calc
      ‖W‖ = ‖1 - (S - 1) * W‖ := congrArg norm heq
      _ ≤ ‖(1 : Matrix m m ℂ)‖ + ‖(S - 1) * W‖ := norm_sub_le _ _
      _ ≤ 1 + ‖S - 1‖ * ‖W‖ := add_le_add hone (Matrix.l2_opNorm_mul _ _)
      _ ≤ _ := by gcongr
  change ‖W‖ ≤ 2
  linarith

/-- Operator-norm commutator bound on a near-identity positive Gram. -/
theorem inverseSqrtNormalizer_commutator_l2_opNorm_le
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef)
    (D : Matrix m m ℂ) (hnear : ‖G - 1‖ ≤ (1 : ℝ) / 2) :
    ‖D * inverseSqrtNormalizer G - inverseSqrtNormalizer G * D‖ ≤
      4 * ‖D * G - G * D‖ :=
  inverseSqrtNormalizer_commutator_l2_opNorm_le_of_sqrt_bounds hG D
    (cfcSqrt_sub_one_l2_opNorm_le hG hnear) (inverseSqrtNormalizer_l2_opNorm_le hG hnear)

/-- The same square-root Sylvester argument in Hilbert--Schmidt norm uses
operator bounds on the multipliers, so it has no dimension factor. -/
theorem inverse_commutator_frobeniusNorm_le_of_square_near_one
    [DecidableEq m] (D G S W : Matrix m m ℂ)
    (hG : G = S * S) (hSW : S * W = 1) (hWS : W * S = 1)
    (hnear : ‖S - 1‖ ≤ (1 : ℝ) / 2) (hWnorm : ‖W‖ ≤ 2) :
    matrixFrobeniusNorm (D * W - W * D) ≤
      4 * matrixFrobeniusNorm (D * G - G * D) := by
  let X : Matrix m m ℂ := D * S - S * D
  let B : Matrix m m ℂ := D * G - G * D
  let E : Matrix m m ℂ := S - 1
  have hB : B = X * S + S * X := by simp only [B, X, hG]; noncomm_ring
  have hS : S = 1 + E := by simp [E]
  have hBexpand : B = (X + X) + (X * E + E * X) := by rw [hB, hS]; noncomm_ring
  have hrest : matrixFrobeniusNorm (X * E + E * X) ≤ matrixFrobeniusNorm X := by
    calc
      _ ≤ matrixFrobeniusNorm (X * E) + matrixFrobeniusNorm (E * X) :=
        matrixFrobeniusNorm_add_le _ _
      _ ≤ matrixFrobeniusNorm X * ‖E‖ + ‖E‖ * matrixFrobeniusNorm X :=
        add_le_add (matrixFrobeniusNorm_mul_le_operator_right _ _)
          (matrixFrobeniusNorm_mul_le_operator_left _ _)
      _ ≤ _ := by
        have hE : ‖E‖ ≤ (1 : ℝ) / 2 := hnear
        nlinarith [matrixFrobeniusNorm_nonneg X]
  have hdouble : matrixFrobeniusNorm (X + X) = 2 * matrixFrobeniusNorm X := by
    rw [← two_smul ℂ X, matrixFrobeniusNorm_smul]
    norm_num
  have hXle : matrixFrobeniusNorm X ≤ matrixFrobeniusNorm B := by
    have heq : X + X = B - (X * E + E * X) := by rw [hBexpand]; abel
    have ht : matrixFrobeniusNorm (X + X) ≤
        matrixFrobeniusNorm B + matrixFrobeniusNorm (X * E + E * X) := by
      rw [heq]
      exact matrixFrobeniusNorm_sub_le _ _
    rw [hdouble] at ht
    linarith
  have hcomm : D * W - W * D = -(W * X * W) := by
    have heq : W * X * W = W * D * (S * W) - (W * S) * D * W := by
      simp only [X, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [heq, hSW, hWS]
    simp only [Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hcomm, matrixFrobeniusNorm_neg]
  calc
    _ ≤ matrixFrobeniusNorm (W * X) * ‖W‖ := matrixFrobeniusNorm_mul_le_operator_right _ _
    _ ≤ (‖W‖ * matrixFrobeniusNorm X) * ‖W‖ :=
      mul_le_mul_of_nonneg_right (matrixFrobeniusNorm_mul_le_operator_left _ _) (norm_nonneg W)
    _ ≤ (2 * matrixFrobeniusNorm B) * 2 := by
      have hX0 := matrixFrobeniusNorm_nonneg X
      have hB0 := matrixFrobeniusNorm_nonneg B
      gcongr
    _ = _ := by ring

/-- Hilbert--Schmidt commutator bound with exactly the same Gram hypothesis
as the operator estimate. -/
theorem inverseSqrtNormalizer_commutator_frobeniusNorm_le
    [DecidableEq m] {G : Matrix m m ℂ} (hG : G.PosDef)
    (D : Matrix m m ℂ) (hnear : ‖G - 1‖ ≤ (1 : ℝ) / 2) :
    matrixFrobeniusNorm (D * inverseSqrtNormalizer G - inverseSqrtNormalizer G * D) ≤
      4 * matrixFrobeniusNorm (D * G - G * D) := by
  have hunit : IsUnit (CFC.sqrt G) :=
    CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hG.isStrictlyPositive
  have hdet := (Matrix.isUnit_iff_isUnit_det (CFC.sqrt G)).mp hunit
  apply inverse_commutator_frobeniusNorm_le_of_square_near_one
    D G (CFC.sqrt G) (inverseSqrtNormalizer G)
  · exact (CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg).symm
  · exact Matrix.mul_nonsing_inv (CFC.sqrt G) hdet
  · exact Matrix.nonsing_inv_mul (CFC.sqrt G) hdet
  · exact cfcSqrt_sub_one_l2_opNorm_le hG hnear
  · exact inverseSqrtNormalizer_l2_opNorm_le hG hnear

/-- Operator-norm quantitative reorthonormalization.  If `T V = V D + J`,
the canonical isometric frame `Q = V (VᴴV)⁻¹ᐟ²` satisfies
`‖TQ-QD‖ ≤ 34 ‖J‖` in the near-identity Gram regime.

This is the operator-norm assertion in manuscript Lemma 5.1, with an
explicit non-sharp absolute constant. -/
theorem normalizedFrame_inverseSqrt_residual_l2_opNorm_le
    [DecidableEq m] [DecidableEq n]
    {T : Matrix n n ℂ} {V : Matrix n m ℂ}
    {D : Matrix m m ℂ} {J : Matrix n m ℂ}
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hTV : T * V = V * D + J)
    (hVinj : Function.Injective fun x : m → ℂ ↦ V *ᵥ x)
    (hnear : ‖frameGram V - 1‖ ≤ (1 : ℝ) / 2) :
    ‖T * normalizedFrame V (inverseSqrtNormalizer (frameGram V)) -
        normalizedFrame V (inverseSqrtNormalizer (frameGram V)) * D‖ ≤
      34 * ‖J‖ := by
  let G : Matrix m m ℂ := frameGram V
  let W : Matrix m m ℂ := inverseSqrtNormalizer G
  have hG : G.PosDef := by
    simpa only [G] using frameGram_posDef_of_mulVec_injective hVinj
  have hWnorm : ‖W‖ ≤ 2 := by
    apply inverseSqrtNormalizer_l2_opNorm_le hG
    simpa only [G] using hnear
  have hGramComm : ‖D * G - G * D‖ ≤ 4 * ‖J‖ := by
    simpa only [G] using frame_commutator_l2_opNorm_le hT hD hTV hnear
  have hWcomm : ‖D * W - W * D‖ ≤ 16 * ‖J‖ := by
    calc
      ‖D * W - W * D‖ ≤ 4 * ‖D * G - G * D‖ := by
        simpa only [W] using
          inverseSqrtNormalizer_commutator_l2_opNorm_le hG D
            (by simpa only [G] using hnear)
      _ ≤ 4 * (4 * ‖J‖) := mul_le_mul_of_nonneg_left hGramComm (by positivity)
      _ = 16 * ‖J‖ := by ring
  have hVnorm : ‖V‖ ≤ 2 := frame_l2_opNorm_le_two_of_gram_near V hnear
  rw [normalizedFrame_residual_eq hTV]
  change ‖V * (D * W - W * D) + J * W‖ ≤ 34 * ‖J‖
  calc
    ‖V * (D * W - W * D) + J * W‖ ≤
        ‖V * (D * W - W * D)‖ + ‖J * W‖ := norm_add_le _ _
    _ ≤ ‖V‖ * ‖D * W - W * D‖ + ‖J‖ * ‖W‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ 2 * (16 * ‖J‖) + ‖J‖ * 2 := by
      gcongr
    _ = 34 * ‖J‖ := by ring

/-- The Gram commutator is controlled in Hilbert--Schmidt norm by the
approximate intertwining residual, using only an operator bound on the frame. -/
theorem frame_commutator_frobeniusNorm_le
    [DecidableEq m] [DecidableEq n]
    {T : Matrix n n ℂ} {V : Matrix n m ℂ}
    {D : Matrix m m ℂ} {J : Matrix n m ℂ}
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hTV : T * V = V * D + J)
    (hnear : matrixL2OperatorNorm (frameGram V - 1) ≤ (1 : ℝ) / 2) :
    matrixFrobeniusNorm (D * frameGram V - frameGram V * D) ≤
      4 * matrixFrobeniusNorm J := by
  have hV : matrixL2OperatorNorm V ≤ 2 := by
    simpa only [matrixL2OperatorNorm] using
      frame_l2_opNorm_le_two_of_gram_near V hnear
  rw [frame_commutator hT hD hTV]
  calc
    matrixFrobeniusNorm (Vᴴ * J - Jᴴ * V) ≤
        matrixFrobeniusNorm (Vᴴ * J) + matrixFrobeniusNorm (Jᴴ * V) :=
      matrixFrobeniusNorm_sub_le _ _
    _ ≤ matrixL2OperatorNorm Vᴴ * matrixFrobeniusNorm J +
        matrixFrobeniusNorm Jᴴ * matrixL2OperatorNorm V :=
      add_le_add
        (matrixFrobeniusNorm_mul_le_operator_left Vᴴ J)
        (matrixFrobeniusNorm_mul_le_operator_right Jᴴ V)
    _ = matrixL2OperatorNorm V * matrixFrobeniusNorm J +
        matrixFrobeniusNorm J * matrixL2OperatorNorm V := by
      rw [matrixL2OperatorNorm_conjTranspose,
        matrixFrobeniusNorm_conjTranspose]
    _ ≤ 4 * matrixFrobeniusNorm J := by
      nlinarith [matrixFrobeniusNorm_nonneg J,
        matrixL2OperatorNorm_nonneg V]

/-- Hilbert--Schmidt quantitative reorthonormalization with the same explicit
constant as the operator estimate. -/
theorem normalizedFrame_inverseSqrt_residual_frobeniusNorm_le
    [DecidableEq m] [DecidableEq n]
    {T : Matrix n n ℂ} {V : Matrix n m ℂ}
    {D : Matrix m m ℂ} {J : Matrix n m ℂ}
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hTV : T * V = V * D + J)
    (hVinj : Function.Injective fun x : m → ℂ ↦ V *ᵥ x)
    (hnear : matrixL2OperatorNorm (frameGram V - 1) ≤ (1 : ℝ) / 2) :
    matrixFrobeniusNorm
        (T * normalizedFrame V (inverseSqrtNormalizer (frameGram V)) -
          normalizedFrame V (inverseSqrtNormalizer (frameGram V)) * D) ≤
      34 * matrixFrobeniusNorm J := by
  let G : Matrix m m ℂ := frameGram V
  let W : Matrix m m ℂ := inverseSqrtNormalizer G
  have hG : G.PosDef := by
    simpa only [G] using frameGram_posDef_of_mulVec_injective hVinj
  have hWnorm : matrixL2OperatorNorm W ≤ 2 := by
    simpa only [matrixL2OperatorNorm, W] using
      inverseSqrtNormalizer_l2_opNorm_le hG
        (by simpa only [matrixL2OperatorNorm, G] using hnear)
  have hVnorm : matrixL2OperatorNorm V ≤ 2 := by
    simpa only [matrixL2OperatorNorm] using
      frame_l2_opNorm_le_two_of_gram_near V
        (by simpa only [matrixL2OperatorNorm] using hnear)
  have hGramComm :
      matrixFrobeniusNorm (D * G - G * D) ≤
        4 * matrixFrobeniusNorm J := by
    simpa only [G] using frame_commutator_frobeniusNorm_le hT hD hTV hnear
  have hWcomm :
      matrixFrobeniusNorm (D * W - W * D) ≤
        16 * matrixFrobeniusNorm J := by
    calc
      matrixFrobeniusNorm (D * W - W * D) ≤
          4 * matrixFrobeniusNorm (D * G - G * D) := by
        simpa only [matrixFrobeniusNorm, W] using
          inverseSqrtNormalizer_commutator_frobeniusNorm_le hG D hnear
      _ ≤ 4 * (4 * matrixFrobeniusNorm J) :=
        mul_le_mul_of_nonneg_left hGramComm (by positivity)
      _ = 16 * matrixFrobeniusNorm J := by ring
  rw [normalizedFrame_residual_eq hTV]
  change matrixFrobeniusNorm (V * (D * W - W * D) + J * W) ≤
    34 * matrixFrobeniusNorm J
  calc
    matrixFrobeniusNorm (V * (D * W - W * D) + J * W) ≤
        matrixFrobeniusNorm (V * (D * W - W * D)) +
          matrixFrobeniusNorm (J * W) := matrixFrobeniusNorm_add_le _ _
    _ ≤ matrixL2OperatorNorm V * matrixFrobeniusNorm (D * W - W * D) +
        matrixFrobeniusNorm J * matrixL2OperatorNorm W :=
      add_le_add
        (matrixFrobeniusNorm_mul_le_operator_left V (D * W - W * D))
        (matrixFrobeniusNorm_mul_le_operator_right J W)
    _ ≤ 2 * (16 * matrixFrobeniusNorm J) +
        matrixFrobeniusNorm J * 2 := by
      apply add_le_add
      · calc
          matrixL2OperatorNorm V *
                matrixFrobeniusNorm (D * W - W * D) ≤
              2 * matrixFrobeniusNorm (D * W - W * D) :=
            mul_le_mul_of_nonneg_right hVnorm
              (matrixFrobeniusNorm_nonneg _)
          _ ≤ 2 * (16 * matrixFrobeniusNorm J) :=
            mul_le_mul_of_nonneg_left hWcomm (by positivity)
      · exact mul_le_mul_of_nonneg_left hWnorm
          (matrixFrobeniusNorm_nonneg J)
    _ = 34 * matrixFrobeniusNorm J := by ring

end FrameWhitening

noncomputable section ActualWhitenedFrame

open Filter Topology

open scoped Classical

/-- Symmetric whitening of the actual normalized projected complete prefix.
Near-identity Gram smallness is proved separately before asserting isometry. -/
def whitenedProjectedFullStarFrame (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  normalizedFrame (projectedFullStarFrame S X K)
    (inverseSqrtNormalizer (frameGram (projectedFullStarFrame S X K)))

/-- The signed one-exit residual of the whitened frame, against the original
exact-molecule root diagonal. Whitening does not relabel or sort roots. -/
def whitenedProjectedFullStarFrameResidual (S : Finset ℕ) (X K : ℕ) :
    Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
  oneExitCompression S X * whitenedProjectedFullStarFrame S X K -
    whitenedProjectedFullStarFrame S X K *
      complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)

/-- Right normalization preserves membership in the actual one-exit space. -/
theorem oneExitProjection_mul_whitenedProjectedFullStarFrame (S : Finset ℕ) (X K : ℕ) :
    oneExitProjection S X * whitenedProjectedFullStarFrame S X K =
      whitenedProjectedFullStarFrame S X K := by
  unfold whitenedProjectedFullStarFrame normalizedFrame
  rw [← Matrix.mul_assoc, oneExitProjection_mul_projectedFullStarFrame]

/-- The actual whitened prefix is an isometry, and both residual norms are
bounded by 34 times the corresponding pre-whitening norm. All finite Gram
and injectivity hypotheses are discharged on the complete power prefix. -/
theorem eventually_powerRange_whitenedProjectedFullStarFrame_isometry_and_residuals
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      (whitenedProjectedFullStarFrame S X K)ᴴ * whitenedProjectedFullStarFrame S X K = 1 ∧
      matrixL2OperatorNorm (whitenedProjectedFullStarFrameResidual S X K) ≤
        34 * matrixL2OperatorNorm (projectedFullStarFrameResidual S X K) ∧
      matrixFrobeniusNorm (whitenedProjectedFullStarFrameResidual S X K) ≤
        34 * matrixFrobeniusNorm (projectedFullStarFrameResidual S X K) := by
  filter_upwards [eventually_powerRange_projectedFullStarFrame_gram_error_lt S hS htheta
    (show (0 : ℝ) < 1 / 2 by norm_num)] with X hgram
  intro K hK
  let V := projectedFullStarFrame S X K
  let D := complexifyRealMatrix (exactMoleculeFamilyRootMatrix S X K)
  let T := oneExitCompression S X
  let J := projectedFullStarFrameResidual S X K
  have hnear : ‖frameGram V - 1‖ ≤ (1 : ℝ) / 2 := (hgram K hK).le
  have hVinj : Function.Injective fun x : MoleculeCenter S X K → ℂ ↦ V *ᵥ x :=
    frame_mulVec_injective_of_gram_sub_one_norm_lt_one V (lt_of_le_of_lt hnear (by norm_num))
  have hT : T.IsHermitian := oneExitCompression_isHermitian S X
  have hD : D.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro a b
    by_cases hab : a = b
    · subst b
      simp [D, complexifyRealMatrix, exactMoleculeFamilyRootMatrix]
    · simp [D, complexifyRealMatrix, exactMoleculeFamilyRootMatrix, Matrix.diagonal, hab, Ne.symm hab]
  have hTV : T * V = V * D + J := by
    dsimp [T, V, D, J, projectedFullStarFrameResidual]
    abel
  exact ⟨normalizedFrame_inverseSqrt_isometry (frameGram_posDef_of_mulVec_injective hVinj),
    normalizedFrame_inverseSqrt_residual_l2_opNorm_le hT hD hTV hVinj hnear,
    normalizedFrame_inverseSqrt_residual_frobeniusNorm_le hT hD hTV hVinj hnear⟩

/-- The whitened actual prefix retains the complete-prefix Hilbert--Schmidt
budget, with a constant independent of the moving prefix length. -/
theorem eventually_powerRange_whitenedProjectedFullStarFrameResidual_hsSq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
        matrixFrobeniusNorm (whitenedProjectedFullStarFrameResidual S X K) ^ 2 ≤
          C * (K : ℝ) * Real.log (X : ℝ) ^ 5 := by
  obtain ⟨C, hC, hb⟩ := eventually_powerRange_projectedFullStarFrameResidual_hsSq_le S hS htheta
  refine ⟨34 ^ 2 * C, by positivity, ?_⟩
  filter_upwards [hb,
    eventually_powerRange_whitenedProjectedFullStarFrame_isometry_and_residuals S hS htheta]
    with X hbX hw
  intro K hK
  have ht := (hw K hK).2.2
  have hsq := (sq_le_sq₀ (matrixFrobeniusNorm_nonneg _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 34) (matrixFrobeniusNorm_nonneg _))).mpr ht
  calc
    _ ≤ (34 * matrixFrobeniusNorm (projectedFullStarFrameResidual S X K)) ^ 2 := hsq
    _ = 34 ^ 2 * matrixFrobeniusNorm (projectedFullStarFrameResidual S X K) ^ 2 := mul_pow _ _ _
    _ ≤ 34 ^ 2 * (C * (K : ℝ) * Real.log (X : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_left (hbX K hK) (by norm_num)
    _ = _ := by ring

/-- Symmetric whitening retains the corrected collective operator budget;
the coherent term K^2/sqrt(X) is not discarded. -/
theorem eventually_powerRange_whitenedProjectedFullStarFrameResidual_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
        matrixL2OperatorNorm (whitenedProjectedFullStarFrameResidual S X K) ^ 2 ≤
          C * Real.log (X : ℝ) ^ 5 * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
  obtain ⟨C, hC, hb⟩ :=
    eventually_powerRange_projectedFullStarFrameResidual_operatorNorm_sq_le S hS htheta
  refine ⟨34 ^ 2 * C, by positivity, ?_⟩
  filter_upwards [hb,
    eventually_powerRange_whitenedProjectedFullStarFrame_isometry_and_residuals S hS htheta]
    with X hbX hw
  intro K hK
  have ht := (hw K hK).2.1
  have hsq := (sq_le_sq₀ (matrixL2OperatorNorm_nonneg _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 34) (matrixL2OperatorNorm_nonneg _))).mpr ht
  calc
    _ ≤ (34 * matrixL2OperatorNorm (projectedFullStarFrameResidual S X K)) ^ 2 := hsq
    _ = 34 ^ 2 * matrixL2OperatorNorm (projectedFullStarFrameResidual S X K) ^ 2 := mul_pow _ _ _
    _ ≤ 34 ^ 2 * (C * Real.log (X : ℝ) ^ 5 * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbX K hK) (by norm_num)
    _ = _ := by ring

/-- The matrix isometry is exposed in the exact linear-isometry type consumed
by the finite same-index comparison, with its synthesis map identified. -/
theorem eventually_powerRange_whitenedProjectedFullStarFrame_linearIsometry
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∃ Q : EuclideanSpace ℂ (MoleculeCenter S X K) →ₗᵢ[ℂ]
          EuclideanSpace ℂ (PrimeStar.Vertex S X),
        Q.toLinearMap = Matrix.toEuclideanLin (whitenedProjectedFullStarFrame S X K) := by
  filter_upwards [eventually_powerRange_whitenedProjectedFullStarFrame_isometry_and_residuals
    S hS htheta] with X hw
  intro K hK
  let W := whitenedProjectedFullStarFrame S X K
  let L := Matrix.toEuclideanLin W
  have hinner : ∀ x y, ⟪L x, L y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    rw [← LinearMap.adjoint_inner_right]
    change ⟪x, (Matrix.toEuclideanLin W).adjoint (Matrix.toEuclideanLin W y)⟫_ℂ = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x, (Matrix.toEuclideanLin Wᴴ ∘ₗ Matrix.toEuclideanLin W) y⟫_ℂ = _
    rw [← Matrix.toLpLin_mul_same, (hw K hK).1]
    simp
  exact ⟨L.isometryOfInner hinner, rfl⟩

end ActualWhitenedFrame

section WeightedComplement

variable {V U : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]

/-- An energy-weighted frame error controls the forest form on the
orthogonal complement of the frame. No graph-map inverse is required. -/
theorem re_inner_le_of_weighted_frame_error
    (L : V →ₗ[ℂ] V) (hL : L.IsSymmetric)
    (U₀ : U →ₗᵢ[ℂ] V) (F : U →ₗ[ℂ] V) (W : U →ₗ[ℂ] U)
    {beta tau : ℝ} (hbeta : 0 ≤ beta) (htau : 0 ≤ tau)
    (hLU : ∀ v, L (U₀ v) = U₀ (W.adjoint (W v)))
    (hcomp : ∀ y : V, U₀.toLinearMap.adjoint y = 0 →
      RCLike.re ⟪y, L y⟫_ℂ ≤ beta * ‖y‖ ^ 2)
    (hweighted : ∀ x : V,
      ‖W ((F - U₀.toLinearMap).adjoint x)‖ ≤ tau * ‖x‖)
    (x : V) (hx : F.adjoint x = 0) :
    RCLike.re ⟪x, L x⟫_ℂ ≤ (beta + tau ^ 2) * ‖x‖ ^ 2 := by
  let p := U₀.toLinearMap.adjoint
  let v := p x
  let y := x - U₀ v
  have hpU (u : U) : p (U₀ u) = u :=
    congrArg (fun f : U →ₗ[ℂ] U ↦ f u) U₀.adjoint_comp_self'
  have hy : p y = 0 := by simp [y, v, map_sub, hpU]
  have horth (u : U) : ⟪U₀ u, y⟫_ℂ = 0 := by
    calc
      _ = ⟪u, p y⟫_ℂ := (LinearMap.adjoint_inner_right U₀.toLinearMap u y).symm
      _ = 0 := by rw [hy, inner_zero_right]
  have hsplit : x = U₀ v + y := by dsimp [y]; abel
  have hnorm : ‖x‖ ^ 2 = ‖v‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [hsplit, norm_add_sq (𝕜 := ℂ), horth v, map_zero, U₀.norm_map]
    ring
  have hcross : ⟪U₀ v, L y⟫_ℂ = 0 := by
    rw [← hL, hLU, horth]
  have hcross' : RCLike.re ⟪y, L (U₀ v)⟫_ℂ = 0 := by
    rw [inner_re_symm, hLU, horth, map_zero]
  have hmain : RCLike.re ⟪U₀ v, L (U₀ v)⟫_ℂ = ‖W v‖ ^ 2 := by
    rw [hLU, U₀.inner_map_map, LinearMap.adjoint_inner_right]
    exact (norm_sq_eq_re_inner (W v)).symm
  have hform : RCLike.re ⟪x, L x⟫_ℂ =
      ‖W v‖ ^ 2 + RCLike.re ⟪y, L y⟫_ℂ := by
    conv_lhs => rw [hsplit, map_add, inner_add_left, inner_add_right,
      inner_add_right, map_add, map_add, map_add]
    rw [hmain, hcross, map_zero, hcross']
    ring
  have herror : (F - U₀.toLinearMap).adjoint x = -v := by
    simp [map_sub, hx, v, p]
  have hw : ‖W v‖ ≤ tau * ‖x‖ := by
    have ht := hweighted x
    rw [herror, map_neg, norm_neg] at ht
    exact ht
  have hwsq : ‖W v‖ ^ 2 ≤ tau ^ 2 * ‖x‖ ^ 2 := by
    simpa [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg htau (norm_nonneg x))).mpr hw
  have hbetaNorm : beta * ‖y‖ ^ 2 ≤ beta * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖v‖]) hbeta
  rw [hform]
  have hybound := (hcomp y hy).trans hbetaNorm
  nlinarith

/-- Add a bounded perturbation after the weighted forest-complement bound.
This is the finite quadratic-form consumer used before one-exit compression. -/
theorem re_inner_add_le_of_weighted_frame_error
    (L H : V →ₗ[ℂ] V) (hL : L.IsSymmetric)
    (U₀ : U →ₗᵢ[ℂ] V) (F : U →ₗ[ℂ] V) (W : U →ₗ[ℂ] U)
    {beta tau eta : ℝ} (hbeta : 0 ≤ beta) (htau : 0 ≤ tau)
    (hLU : ∀ v, L (U₀ v) = U₀ (W.adjoint (W v)))
    (hcomp : ∀ y : V, U₀.toLinearMap.adjoint y = 0 →
      RCLike.re ⟪y, L y⟫_ℂ ≤ beta * ‖y‖ ^ 2)
    (hweighted : ∀ x : V,
      ‖W ((F - U₀.toLinearMap).adjoint x)‖ ≤ tau * ‖x‖)
    (hH : ∀ x : V, ‖H x‖ ≤ eta * ‖x‖)
    (x : V) (hx : F.adjoint x = 0) :
    RCLike.re ⟪x, (L + H) x⟫_ℂ ≤ (beta + tau ^ 2 + eta) * ‖x‖ ^ 2 := by
  have hf := re_inner_le_of_weighted_frame_error L hL U₀ F W hbeta htau hLU hcomp hweighted x hx
  have hh := abs_re_inner_apply_le_of_pointwise_norm_bound H eta hH x
  have hhi := (le_abs_self (RCLike.re ⟪x, H x⟫_ℂ)).trans hh
  simp only [LinearMap.add_apply, inner_add_right, map_add]
  nlinarith

end WeightedComplement

noncomputable section WhiteningComplement

open Filter Topology
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Invertible right whitening leaves the orthogonal complement of the
frame range unchanged, including in dimension zero. -/
theorem normalizedFrame_inverseSqrt_adjoint_eq_zero_iff
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (V : Matrix n m ℂ) (hG : (frameGram V).PosDef)
    (x : EuclideanSpace ℂ n) :
    (Matrix.toEuclideanLin
      (normalizedFrame V (inverseSqrtNormalizer (frameGram V)))).adjoint x = 0 ↔
      (Matrix.toEuclideanLin V).adjoint x = 0 := by
  let S := CFC.sqrt (frameGram V)
  let Q := normalizedFrame V (inverseSqrtNormalizer (frameGram V))
  have hu : IsUnit S := CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hG.isStrictlyPositive
  have hd := (Matrix.isUnit_iff_isUnit_det S).mp hu
  have hQS : Q * S = V := by
    change V * S⁻¹ * S = V
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hd, Matrix.mul_one]
  have hV : Matrix.toEuclideanLin V =
      Matrix.toEuclideanLin Q ∘ₗ Matrix.toEuclideanLin S := by
    rw [← Matrix.toLpLin_mul_same, hQS]
  constructor
  · intro hx
    rw [hV, LinearMap.adjoint_comp, LinearMap.comp_apply, hx, map_zero]
  · intro hx
    change (Matrix.toEuclideanLin
      (V * inverseSqrtNormalizer (frameGram V))).adjoint x = 0
    rw [Matrix.toLpLin_mul_same, LinearMap.adjoint_comp, LinearMap.comp_apply, hx, map_zero]

/-- The complement used by the ordered comparison is literally the
orthogonal complement of the actual unwhitened projected prefix. -/
theorem eventually_powerRange_whitenedFrame_adjoint_eq_zero_iff
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
        (Matrix.toEuclideanLin (whitenedProjectedFullStarFrame S X K)).adjoint x = 0 ↔
          (Matrix.toEuclideanLin (projectedFullStarFrame S X K)).adjoint x = 0 := by
  filter_upwards [eventually_powerRange_projectedFullStarFrame_gram_error_lt S hS htheta
    (show (0 : ℝ) < 1 / 2 by norm_num)] with X hgram
  intro K hK x
  have hi := frame_mulVec_injective_of_gram_sub_one_norm_lt_one
    (projectedFullStarFrame S X K) ((hgram K hK).trans (by norm_num))
  exact normalizedFrame_inverseSqrt_adjoint_eq_zero_iff _
    (frameGram_posDef_of_mulVec_injective hi) x

end WhiteningComplement


noncomputable section EnergyWeightedInterior

open Filter Topology
open scoped Classical

private theorem energyWeightedFamily_operatorNorm_sq_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (f : n → EuclideanSpace ℝ m) (mu : n → ℝ) (D N lower : ℝ)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hlower : 0 < lower)
    (hmu : ∀ a, lower ≤ mu a)
    (hdiag : ∀ a, mu a ^ 2 * ‖f a‖ ^ 2 ≤ D)
    (hpair : ∀ a b, a ≠ b → mu a * mu b * |⟪f a, f b⟫_ℝ| ≤ N) :
    let J : Matrix m n ℝ := fun v a ↦ Real.sqrt (mu a) * f a v
    ‖J‖ ^ 2 ≤ (D + Fintype.card n * N) / lower := by
  let J : Matrix m n ℝ := fun v a ↦ Real.sqrt (mu a) * f a v
  let C := D + Fintype.card n * N
  have hmp (a : n) : 0 < mu a := hlower.trans_le (hmu a)
  have hsp (a : n) : 0 < Real.sqrt (mu a) := Real.sqrt_pos.mpr (hmp a)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hentry (a b : n) :
      (J.conjTranspose * J) a b =
        Real.sqrt (mu a) * Real.sqrt (mu b) * ⟪f a, f b⟫_ℝ := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      J, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hrow (a : n) :
      mu a * (∑ b, mu b * |⟪f a, f b⟫_ℝ|) ≤ C := by
    rw [Finset.mul_sum]
    calc
      _ = mu a * (mu a * |⟪f a, f a⟫_ℝ|) +
          ∑ b ∈ Finset.univ.erase a, mu a * (mu b * |⟪f a, f b⟫_ℝ|) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
      _ ≤ D + ∑ _b ∈ Finset.univ.erase a, N := by
        apply add_le_add
        · simpa [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖f a‖), sq,
            mul_assoc] using hdiag a
        · apply Finset.sum_le_sum
          intro b hb
          simpa only [mul_assoc] using hpair a b (Finset.ne_of_mem_erase hb).symm
      _ ≤ C := by
        dsimp [C]
        apply add_le_add_right
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc : ((Finset.univ.erase a).card : ℝ) ≤ Fintype.card n := by
          exact_mod_cast (Finset.card_le_card (Finset.erase_subset (a := a) (s := Finset.univ)))
        exact mul_le_mul_of_nonneg_right hc hN
  change ‖J‖ ^ 2 ≤ _
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self]
  apply symmetric_l2_opNorm_le_weightedAbsoluteRow (J.conjTranspose * J)
    (fun a ↦ Real.sqrt (mu a)) (C / lower) (div_nonneg hC hlower.le)
  · intro a b
    rw [hentry, hentry, real_inner_comm (f a) (f b)]
    ring
  · exact hsp
  · intro a
    have hs : (∑ b, mu b * |⟪f a, f b⟫_ℝ|) ≤ C / lower := by
      apply (le_div_iff₀ hlower).mpr
      have hsum : 0 ≤ ∑ b, mu b * |⟪f a, f b⟫_ℝ| :=
        Finset.sum_nonneg fun b _ ↦ mul_nonneg (hmp b).le (abs_nonneg _)
      nlinarith [hrow a, mul_le_mul_of_nonneg_right (hmu a) hsum]
    calc
      _ = Real.sqrt (mu a) * ∑ b, mu b * |⟪f a, f b⟫_ℝ| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [hentry, abs_mul, abs_mul, abs_of_pos (hsp a), abs_of_pos (hsp b)]
        calc
          _ = Real.sqrt (mu a) * (Real.sqrt (mu b) ^ 2 * |⟪f a, f b⟫_ℝ|) := by ring
          _ = _ := by rw [Real.sq_sqrt (hmp b).le]
      _ ≤ Real.sqrt (mu a) * (C / lower) := mul_le_mul_of_nonneg_left hs (hsp a).le
      _ = _ := mul_comm _ _

/-- Energy weighting is applied to each actual full-interior column before
taking the operator norm. The bound includes signed and kernel responses
and has no spectral-gap or overlap premises left to instantiate. -/
theorem eventually_powerRange_energyWeightedFullInterior_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
        fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
          exactPrincipalMoleculeInteriorVector S X a.1 v
      ‖J‖ ^ 2 ≤
        (10000 * PrimeStar.sqrtCutoffResidualScale X ^ 2 +
          (40000 / Real.log 2) * K * Real.log (X : ℝ)) /
            Real.sqrt ((X : ℝ) / (8 * K * Real.log (X : ℝ))) := by
  filter_upwards [eventually_powerRange_fullInteriorOverlap_energyProduct_le S hS htheta,
    eventually_powerRange_energy_mul_norm_fullInterior_le S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_ge_atTop 2] with X hp hd hs hX
  intro K hKpos hK J
  let L := Real.log (X : ℝ)
  let eta := PrimeStar.sqrtCutoffResidualScale X
  let lower := Real.sqrt ((X : ℝ) / (8 * K * L))
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hk : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hlower : 0 < lower := Real.sqrt_pos.mpr (by positivity)
  have hrange (a : MoleculeCenter S X K) : InPowerRange theta X (a.1 : ℕ) :=
    ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ K).trans hK⟩
  have hmin (a : MoleculeCenter S X K) : lower ≤ moleculeStarEnergy S X a.1 := by
    apply (sq_le_sq₀ hlower.le (Real.sqrt_nonneg _)).mp
    dsimp only [lower]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ) / (8 * K * L))]
    apply le_trans _ (hs a.1 (hrange a)).1
    apply div_le_div_of_nonneg_left hx.le
      (show 0 < 8 * (a.1 : ℝ) * L by
        have ha : 0 < (a.1 : ℝ) := by exact_mod_cast a.1.property.1
        positivity)
    gcongr
    exact_mod_cast a.2
  have hdiag (a : MoleculeCenter S X K) :
      moleculeStarEnergy S X a.1 ^ 2 *
        ‖exactPrincipalMoleculeInteriorVector S X a.1‖ ^ 2 ≤ 10000 * eta ^ 2 := by
    have h := hd a.1 (hrange a)
    have hm : 0 ≤ moleculeStarEnergy S X a.1 := Real.sqrt_nonneg _
    have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
    have ht := (sq_le_sq₀ (mul_nonneg hm (norm_nonneg _)) (by positivity)).mpr h
    nlinarith only [ht]
  have h := energyWeightedFamily_operatorNorm_sq_le
    (fun a : MoleculeCenter S X K ↦ exactPrincipalMoleculeInteriorVector S X a.1)
    (fun a ↦ moleculeStarEnergy S X a.1)
    (10000 * eta ^ 2) ((40000 / Real.log 2) * L) lower
    (by positivity) (by positivity) hlower hmin hdiag
    (fun a b hab ↦ hp a.1 b.1 (hrange a) (hrange b) (fun heq ↦ hab (Subtype.ext heq)))
  apply h.trans
  apply div_le_div_of_nonneg_right _ hlower.le
  have hcard : (Fintype.card (MoleculeCenter S X K) : ℝ) ≤ K := by
    exact_mod_cast card_moleculeCenter_le S X K
  dsimp only [eta, L, lower] at *
  nlinarith [mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ (40000 / Real.log 2) * Real.log (X : ℝ) by positivity)]

private theorem energyWeightedInterior_scalar_bound {x k ell eta c N : ℝ}
    (hx : 0 < x) (hk : 0 < k) (hell : 1 ≤ ell) (hN : 0 ≤ N)
    (hkx : k ≤ Real.sqrt x)
    (heta : eta ^ 2 ≤ 4 * c ^ 2 * (Real.sqrt x / ell)) :
    (10000 * eta ^ 2 + N * k * ell) / Real.sqrt (x / (8 * k * ell)) ≤
      (120000 * c ^ 2 + 3 * N) * ell ^ 2 * Real.sqrt (k / ell) := by
  have hellp : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsden : 0 < Real.sqrt (8 * k * ell) := Real.sqrt_pos.mpr (by positivity)
  have hratio : Real.sqrt x / ell ≤ Real.sqrt x * ell := by
    apply (div_le_iff₀ hellp).mpr
    nlinarith [sq_nonneg (ell - 1)]
  have hnum : 10000 * eta ^ 2 + N * k * ell ≤
      (40000 * c ^ 2 + N) * Real.sqrt x * ell := by
    have he := heta.trans (mul_le_mul_of_nonneg_left hratio (by positivity))
    nlinarith [mul_le_mul_of_nonneg_left hkx (show 0 ≤ N * ell by positivity)]
  have hs : Real.sqrt (8 * k * ell) ≤ 3 * ell * Real.sqrt (k / ell) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    have heq : (3 * ell) ^ 2 * (k / ell) = 9 * k * ell := by field_simp; ring
    rw [heq]
    nlinarith
  rw [Real.sqrt_div hx.le]
  calc
    _ ≤ ((40000 * c ^ 2 + N) * Real.sqrt x * ell) /
        (Real.sqrt x / Real.sqrt (8 * k * ell)) :=
      div_le_div_of_nonneg_right hnum (div_nonneg hsx.le hsden.le)
    _ = (40000 * c ^ 2 + N) * ell * Real.sqrt (8 * k * ell) := by field_simp
    _ ≤ (40000 * c ^ 2 + N) * ell * (3 * ell * Real.sqrt (k / ell)) := by gcongr
    _ = _ := by ring

/-- The actual energy-weighted full-interior synthesis has the native
square-root prefix scale, up to two logarithms. No maximum source energy
is applied to an unweighted frame bound. -/
theorem eventually_powerRange_energyWeightedFullInterior_operatorNorm_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
        fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
          exactPrincipalMoleculeInteriorVector S X a.1 v
      ‖J‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 2 * Real.sqrt (K / Real.log (X : ℝ)) := by
  let C := 120000 * PrimeStar.sqrtCutoffResidualConstant ^ 2 +
    3 * (40000 / Real.log 2)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_powerRange_energyWeightedFullInterior_operatorNorm_sq_le S hS htheta,
    PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 2] with X hi he hL hX
  intro K hKpos hK J
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hk : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hupper : (K : ℝ) ≤ Real.sqrt (X : ℝ) := by
    apply hK.trans
    simpa only [powerScale, Real.sqrt_eq_rpow] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ X by omega)) htheta.le
  exact (hi K hKpos hK).trans
    (energyWeightedInterior_scalar_bound hx hk hL (by positivity) hupper he)

end EnergyWeightedInterior

section EnergyWeightedBoundary

open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical

/-- Unit normalization bounds the phase-aligned boundary error by the
negative mode, boundary kernel and full interior. -/
theorem norm_phaseAlignedBoundary_sub_positiveStar_le
    {S : Finset ℕ} {X : ℕ} {a : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hd : 0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a) :
    ‖fullStarMoleculePhase S X a • exactPrincipalMoleculeBoundaryVector S X a -
        moleculePositiveStarMode S X a‖ ≤
      2 * |exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)| +
        2 * ‖exactPrincipalMoleculeBoundaryKernel S X a‖ +
          ‖exactPrincipalMoleculeInteriorVector S X a‖ := by
  let alpha := exactPrincipalMoleculeBoundaryModeCoefficient S X a 1
  let beta := exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)
  let p := fullStarMoleculePhase S X a
  let u := moleculePositiveStarMode S X a
  let w := PrimeStar.largePrimeNormalizedStarMode S X (squareRootCutoff X) a (-1)
  let k := exactPrincipalMoleculeBoundaryKernel S X a
  let b := exactPrincipalMoleculeBoundaryVector S X a
  let i := exactPrincipalMoleculeInteriorVector S X a
  have hu : ‖u‖ = 1 := norm_moleculePositiveStarMode hd
  have hw : ‖w‖ = 1 := PrimeStar.norm_largePrimeNormalizedStarMode hd
  have hp : |p| = 1 := abs_fullStarMoleculePhase S X a
  have hpa : p * alpha = |alpha| := by
    dsimp [p, alpha, fullStarMoleculePhase]
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (le_of_not_gt h), one_mul]
  have ha1 : |alpha| ≤ 1 := abs_exactPrincipalMoleculeBoundaryModeCoefficient_le_one hd (by norm_num)
  have hb : b = alpha • u + beta • w + k := by
    have h : b - k = alpha • u + beta • w :=
      exactPrincipalMoleculeSignedBoundaryVector_eq_modeSynthesis hd
    exact (sub_eq_iff_eq_add).mp h
  have hbn : ‖b‖ ≤ |alpha| + |beta| + ‖k‖ := by
    rw [hb]
    calc
      _ ≤ (‖alpha • u‖ + ‖beta • w‖) + ‖k‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ = _ := by simp [norm_smul, Real.norm_eq_abs, hu, hw]
  have hunit : 1 ≤ |alpha| + |beta| + ‖k‖ + ‖i‖ := by
    have heq : b + i = exactPrincipalMoleculeAmbientVector S X a :=
      exactPrincipalMolecule_boundary_add_interior ha
    calc
      _ = ‖b + i‖ := by rw [heq, norm_exactPrincipalMoleculeAmbientVector]
      _ ≤ ‖b‖ + ‖i‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hbn le_rfl
  have hsplit : p • b - u = (|alpha| - 1) • u + (p * beta) • w + p • k := by
    rw [hb, smul_add, smul_add, smul_smul, smul_smul, hpa]
    module
  change ‖p • b - u‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖(|alpha| - 1) • u‖ + ‖(p * beta) • w‖ + ‖p • k‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ = (1 - |alpha|) + |beta| + ‖k‖ := by
      simp only [norm_smul, Real.norm_eq_abs, hu, hw, mul_one, abs_mul, hp, one_mul,
        abs_of_nonpos (sub_nonpos.mpr ha1)]
      ring
    _ ≤ _ := by nlinarith only [hunit]

/-- The actual phase-aligned boundary discrepancy retains its source energy.
All gap, root and small-prime hypotheses are supplied on the power range. -/
theorem eventually_powerRange_energy_mul_norm_boundaryDiscrepancy_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ a : PrimeStar.Vertex S X,
      InPowerRange theta X (a : ℕ) →
        moleculeStarEnergy S X a *
          ‖fullStarMoleculePhase S X a • exactPrincipalMoleculeBoundaryVector S X a -
            moleculePositiveStarMode S X a‖ ≤ 700 * PrimeStar.sqrtCutoffResidualScale X := by
  filter_upwards [eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta,
    eventually_powerRange_energy_mul_norm_fullInterior_le S hS htheta,
    eventually_powerRange_negativeCoefficient_and_kernelResponse_bound S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrime_apply_le_tuned]
    with X hw hi hn hH
  intro a ha
  obtain ⟨haY, hd, hroot, hsmall⟩ := hw a ha
  let mu := moleculeStarEnergy S X a
  let eta := PrimeStar.sqrtCutoffResidualScale X
  let nu := exactPrincipalMoleculeRoot S X a
  let k := exactPrincipalMoleculeBoundaryKernel S X a
  let i := exactPrincipalMoleculeInteriorVector S X a
  let F := exactPrincipalMoleculeBoundaryFeedback S X a
  let beta := exactPrincipalMoleculeBoundaryModeCoefficient S X a (-1)
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
    (PrimeStar.tunedSchurScale_nonneg _)
  have hem : eta ≤ mu := by
    dsimp [eta, mu] at *
    nlinarith [sq_nonneg (PrimeStar.sqrtCutoffResidualScale X)]
  have hnu : mu / 2 ≤ nu := by
    have h := (abs_le.mp hroot).1
    dsimp [nu, mu]
    linarith
  have hi' : mu * ‖i‖ ≤ 100 * eta := hi a ha
  have hF : ‖F‖ ≤ eta * ‖i‖ := by
    apply (PrimeStar.norm_euclideanCoordinateProjection_le _ _).trans
    simpa [eta, i, PrimeStar.sqrtCutoffResidualScale, PrimeStar.sqrtCutoffResidualConstant]
      using hH S i
  have hkroot : |nu| * ‖k‖ ≤ ‖F‖ := by
    rw [← Real.norm_eq_abs, ← norm_smul]
    have heq := exactPrincipalMoleculeRoot_smul_boundaryKernel_eq_feedbackKernel hS haY hd
    change ‖nu • k‖ ≤ ‖F‖
    rw [heq]
    exact norm_actualStarMeanZeroLeafVector_le F hd
  have hk : mu ^ 2 * ‖k‖ ≤ 200 * eta ^ 2 := by
    have hnua : mu / 2 ≤ |nu| := hnu.trans (le_abs_self _)
    have hfirst : mu * ‖k‖ ≤ 2 * eta * ‖i‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hnua (norm_nonneg k), hkroot.trans hF]
    have hp := mul_le_mul_of_nonneg_left hfirst hmu.le
    have hq := mul_le_mul_of_nonneg_left hi' (show 0 ≤ 2 * eta by positivity)
    nlinarith only [hp, hq]
  have hk' : mu * ‖k‖ ≤ 200 * eta := by
    have he : eta ^ 2 ≤ eta * mu := by nlinarith
    nlinarith [hk]
  have hb : mu * |beta| ≤ 100 * eta := by
    have h := (le_div_iff₀ (sq_pos_of_pos hmu)).mp (hn a ha).1
    have he : eta ^ 2 ≤ eta * mu := by nlinarith
    dsimp [mu, eta, beta] at *
    nlinarith only [h, he, hmu]
  have h := mul_le_mul_of_nonneg_left (norm_phaseAlignedBoundary_sub_positiveStar_le haY hd) hmu.le
  change mu * _ ≤ _ at h
  nlinarith only [h, hk', hb, hi']

/-- Boundary discrepancies on distinct large-prime stars are orthogonal. -/
theorem inner_boundaryDiscrepancy_eq_zero
    {S : Finset ℕ} {X : ℕ} {a b : PrimeStar.Vertex S X}
    (ha : (a : ℕ) ≤ squareRootCutoff X)
    (hb : (b : ℕ) ≤ squareRootCutoff X) (hab : a ≠ b) :
    ⟪fullStarMoleculePhase S X a • exactPrincipalMoleculeBoundaryVector S X a -
        moleculePositiveStarMode S X a,
      fullStarMoleculePhase S X b • exactPrincipalMoleculeBoundaryVector S X b -
        moleculePositiveStarMode S X b⟫_ℝ = 0 := by
  have hz (c v : PrimeStar.Vertex S X)
      (hv : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) c) :
      (fullStarMoleculePhase S X c • exactPrincipalMoleculeBoundaryVector S X c -
        moleculePositiveStarMode S X c) v = 0 := by
    have hu := PrimeStar.largePrimeNormalizedStarMode_eq_zero_of_not_mem
      (eps := (1 : ℝ)) hv
    simp [exactPrincipalMoleculeBoundaryVector, PrimeStar.primeStarBoundaryProjection,
      moleculePositiveStarMode, hv, hu]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) a
  · have hvb : v ∉ PrimeStar.largePrimeStarSupport S X (squareRootCutoff X) b :=
      fun h ↦ Finset.disjoint_left.mp
        (PrimeStar.disjoint_largePrimeStarSupport (PrimeStar.sqrtCutoff_condition X) ha hb hab) hv h
    simp [hz b v hvb]
  · have h := hz a v hv
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
    simp [h]

/-- Disjoint boundary supports turn the source-energy estimate into a
weighted operator estimate with no prefix-cardinality loss. -/
theorem eventually_powerRange_energyWeightedBoundaryDiscrepancy_operatorNorm_sq_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
        fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
          (fullStarMoleculePhase S X a.1 • exactPrincipalMoleculeBoundaryVector S X a.1 -
            moleculePositiveStarMode S X a.1) v
      ‖J‖ ^ 2 ≤ 490000 * PrimeStar.sqrtCutoffResidualScale X ^ 2 /
        Real.sqrt ((X : ℝ) / (8 * K * Real.log (X : ℝ))) := by
  filter_upwards [eventually_powerRange_energy_mul_norm_boundaryDiscrepancy_le S hS htheta,
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta,
    eventually_powerRange_moleculeStarEnergy_residualScaleBundle S hS htheta,
    eventually_ge_atTop 2] with X hd hw hs hX
  intro K hKpos hK J
  let L := Real.log (X : ℝ)
  let eta := PrimeStar.sqrtCutoffResidualScale X
  let lower := Real.sqrt ((X : ℝ) / (8 * K * L))
  let f (a : MoleculeCenter S X K) :=
    fullStarMoleculePhase S X a.1 • exactPrincipalMoleculeBoundaryVector S X a.1 -
      moleculePositiveStarMode S X a.1
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hk : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hlower : 0 < lower := Real.sqrt_pos.mpr (by positivity)
  have hrange (a : MoleculeCenter S X K) : InPowerRange theta X (a.1 : ℕ) :=
    ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ K).trans hK⟩
  have hmin (a : MoleculeCenter S X K) : lower ≤ moleculeStarEnergy S X a.1 := by
    apply (sq_le_sq₀ hlower.le (Real.sqrt_nonneg _)).mp
    dsimp only [lower]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ) / (8 * K * L))]
    apply le_trans _ (hs a.1 (hrange a)).1
    apply div_le_div_of_nonneg_left hx.le
      (show 0 < 8 * (a.1 : ℝ) * L by
        have ha : 0 < (a.1 : ℝ) := by exact_mod_cast a.1.property.1
        positivity)
    gcongr
    exact_mod_cast a.2
  have hdiag (a : MoleculeCenter S X K) :
      moleculeStarEnergy S X a.1 ^ 2 * ‖f a‖ ^ 2 ≤ 490000 * eta ^ 2 := by
    have h := hd a.1 (hrange a)
    have hm : 0 ≤ moleculeStarEnergy S X a.1 := Real.sqrt_nonneg _
    have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
      (PrimeStar.tunedSchurScale_nonneg _)
    have ht := (sq_le_sq₀ (mul_nonneg hm (norm_nonneg _)) (by positivity)).mpr h
    change (moleculeStarEnergy S X a.1 * ‖f a‖) ^ 2 ≤ _ at ht
    nlinarith only [ht]
  have h := energyWeightedFamily_operatorNorm_sq_le f
    (fun a ↦ moleculeStarEnergy S X a.1) (490000 * eta ^ 2) 0 lower
    (by positivity) le_rfl hlower hmin hdiag (by
      intro a b hab
      have hz := inner_boundaryDiscrepancy_eq_zero
        (hw a.1 (hrange a)).1 (hw b.1 (hrange b)).1
        (fun heq ↦ hab (Subtype.ext heq))
      change ⟪f a, f b⟫_ℝ = 0 at hz
      simp [hz])
  simpa only [mul_zero, add_zero] using h

/-- The boundary part of the actual energy-weighted frame discrepancy has
the square-root prefix scale, with the source energies retained. -/
theorem eventually_powerRange_energyWeightedBoundaryDiscrepancy_operatorNorm_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
        fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
          (fullStarMoleculePhase S X a.1 • exactPrincipalMoleculeBoundaryVector S X a.1 -
            moleculePositiveStarMode S X a.1) v
      ‖J‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 2 * Real.sqrt (K / Real.log (X : ℝ)) := by
  let C := 120000 * (7 * PrimeStar.sqrtCutoffResidualConstant) ^ 2
  have hc := PrimeStar.sqrtCutoffResidualConstant_pos
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_powerRange_energyWeightedBoundaryDiscrepancy_operatorNorm_sq_le S hS htheta,
    PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
    hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 2] with X hi he hL hX
  intro K hKpos hK J
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hk : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hupper : (K : ℝ) ≤ Real.sqrt (X : ℝ) := by
    apply hK.trans
    simpa only [powerScale, Real.sqrt_eq_rpow] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ X by omega)) htheta.le
  have he' : (7 * PrimeStar.sqrtCutoffResidualScale X) ^ 2 ≤
      4 * (7 * PrimeStar.sqrtCutoffResidualConstant) ^ 2 *
        (Real.sqrt (X : ℝ) / Real.log (X : ℝ)) := by nlinarith only [he]
  have h := energyWeightedInterior_scalar_bound hx hk hL (N := 0) le_rfl hupper he'
  have heq : 10000 * (7 * PrimeStar.sqrtCutoffResidualScale X) ^ 2 =
      490000 * PrimeStar.sqrtCutoffResidualScale X ^ 2 := by ring
  rw [heq] at h
  exact (hi K hKpos hK).trans (by simpa only [zero_mul, add_zero, mul_zero] using h)

/-- The actual phase-aligned raw frame, including both boundary modes and
the full first-exit interior, is close to the star frame in source-energy
weighted operator norm. -/
theorem eventually_powerRange_energyWeightedRawFrameError_operatorNorm_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
        fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
          (fullStarMoleculePhase S X a.1 • exactPrincipalMoleculeAmbientVector S X a.1 -
            moleculePositiveStarMode S X a.1) v
      ‖J‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 2 * Real.sqrt (K / Real.log (X : ℝ)) := by
  obtain ⟨Cb, hCb, hb⟩ :=
    eventually_powerRange_energyWeightedBoundaryDiscrepancy_operatorNorm_sq_le_scale S hS htheta
  obtain ⟨Ci, hCi, hi⟩ :=
    eventually_powerRange_energyWeightedFullInterior_operatorNorm_sq_le_scale S hS htheta
  refine ⟨2 * (Cb + Ci), by positivity, ?_⟩
  filter_upwards [hb, hi,
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta]
    with X hb hi hw
  intro K hKpos hK J
  let Jb : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
    fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
      (fullStarMoleculePhase S X a.1 • exactPrincipalMoleculeBoundaryVector S X a.1 -
        moleculePositiveStarMode S X a.1) v
  let Ji : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
    fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
      exactPrincipalMoleculeInteriorVector S X a.1 v
  let P : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℝ :=
    Matrix.diagonal fun a ↦ fullStarMoleculePhase S X a.1
  have hP : ‖P‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro a
    simp only [Real.norm_eq_abs, abs_fullStarMoleculePhase]
    rfl
  have hsplit : J = Jb + Ji * P := by
    ext v a
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ K).trans hK⟩
    have heq := exactPrincipalMolecule_boundary_add_interior (hw a.1 ha).1
    dsimp only [J, Jb, Ji, P]
    rw [← heq]
    simp only [Matrix.add_apply, Matrix.mul_diagonal, PiLp.sub_apply,
      PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    ring
  have hn : ‖J‖ ≤ ‖Jb‖ + ‖Ji‖ := by
    rw [hsplit]
    apply (norm_add_le _ _).trans
    have h := (Matrix.l2_opNorm_mul Ji P).trans
      (mul_le_mul_of_nonneg_left hP (norm_nonneg Ji))
    simpa only [mul_one] using add_le_add le_rfl h
  have hbs : ‖Jb‖ ^ 2 ≤ Cb * Real.log (X : ℝ) ^ 2 *
      Real.sqrt (K / Real.log (X : ℝ)) := hb K hKpos hK
  have his : ‖Ji‖ ^ 2 ≤ Ci * Real.log (X : ℝ) ^ 2 *
      Real.sqrt (K / Real.log (X : ℝ)) := hi K hKpos hK
  nlinarith [sq_nonneg (‖Jb‖ - ‖Ji‖), norm_nonneg J, norm_nonneg Jb, norm_nonneg Ji]

/-- Nonzero column normalization preserves the projected raw frame's
orthogonal complement. The actual normalizers are discharged on the
power range, not assumed as an extra spectral premise. -/
theorem eventually_powerRange_projectedFrame_adjoint_eq_zero_iff_raw
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
        (Matrix.toEuclideanLin (projectedFullStarFrame S X K)).adjoint x = 0 ↔
          (Matrix.toEuclideanLin
            (oneExitProjection S X * phasedFullStarFrame S X K)).adjoint x = 0 := by
  filter_upwards [eventually_powerRange_projectedFullStarMolecule_norm_bounds S hS htheta]
    with X hn
  intro K hK x
  let V := projectedFullStarFrame S X K
  let F := oneExitProjection S X * phasedFullStarFrame S X K
  let D : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
    Matrix.diagonal fun a ↦ (‖projectedFullStarMolecule S X a.1‖ : ℂ)
  have hND : projectedFullStarNormalization S X K * D = 1 := by
    dsimp only [projectedFullStarNormalization, D]
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ K).trans hK⟩
    have hp : 0 < ‖projectedFullStarMolecule S X a.1‖ :=
      lt_of_lt_of_le (by norm_num) (hn a.1 ha).1
    by_cases hab : a = b
    · subst b
      simp [hp.ne']
    · simp [hab]
  have hVD : V * D = F := by
    change (F * projectedFullStarNormalization S X K) * D = F
    rw [Matrix.mul_assoc, hND, Matrix.mul_one]
  constructor
  · intro hx
    change (Matrix.toEuclideanLin F).adjoint x = 0
    change (Matrix.toEuclideanLin V).adjoint x = 0 at hx
    rw [← hVD, Matrix.toLpLin_mul_same, LinearMap.adjoint_comp,
      LinearMap.comp_apply, hx, map_zero]
  · intro hx
    change (Matrix.toEuclideanLin (F * projectedFullStarNormalization S X K)).adjoint x = 0
    rw [Matrix.toLpLin_mul_same, LinearMap.adjoint_comp, LinearMap.comp_apply, hx, map_zero]

/-- Both actual whitening and actual column normalization can be removed
from the complement condition before the weighted quadratic comparison. -/
theorem eventually_powerRange_whitenedFrame_adjoint_eq_zero_iff_projectedRaw
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ powerScale theta X →
      ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
        (Matrix.toEuclideanLin (whitenedProjectedFullStarFrame S X K)).adjoint x = 0 ↔
          (Matrix.toEuclideanLin
            (oneExitProjection S X * phasedFullStarFrame S X K)).adjoint x = 0 := by
  filter_upwards [eventually_powerRange_whitenedFrame_adjoint_eq_zero_iff S hS htheta,
    eventually_powerRange_projectedFrame_adjoint_eq_zero_iff_raw S hS htheta]
    with X hwh hraw
  intro K hK x
  exact (hwh K hK x).trans (hraw K hK x)

/-- Projection contracts the actual energy-weighted raw discrepancy while
fixing the positive star frame. This is the weighted input needed on the
orthogonal complement, before column normalization or whitening. -/
theorem eventually_powerRange_projectedRaw_weightedError_operatorNorm_sq_le_scale
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      let U : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
        fun v a ↦ PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a.1) v
      let D : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
        Matrix.diagonal fun a ↦ (Real.sqrt (moleculeStarEnergy S X a.1) : ℂ)
      matrixL2OperatorNorm
        ((oneExitProjection S X * phasedFullStarFrame S X K - U) * D) ^ 2 ≤
          C * Real.log (X : ℝ) ^ 2 * Real.sqrt (K / Real.log (X : ℝ)) := by
  obtain ⟨Cr, hCr, hr⟩ :=
    eventually_powerRange_energyWeightedRawFrameError_operatorNorm_sq_le_scale S hS htheta
  refine ⟨4 * Cr, by positivity, ?_⟩
  filter_upwards [hr,
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta]
    with X hr hw
  intro K hKpos hK U D
  let P := oneExitProjection S X
  let R := phasedFullStarFrame S X K
  let J : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℝ :=
    fun v a ↦ Real.sqrt (moleculeStarEnergy S X a.1) *
      (fullStarMoleculePhase S X a.1 • exactPrincipalMoleculeAmbientVector S X a.1 -
        moleculePositiveStarMode S X a.1) v
  have hPU : P * U = U := by
    ext v a
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ K).trans hK⟩
    obtain ⟨haY, hd, _⟩ := hw a.1 ha
    have h := congrArg (fun y ↦ y v) (oneExitProjection_fixes_positiveStarMode haY hd)
    simpa only [P, U, Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct] using h
  have hraw : (R - U) * D = complexifyRealMatrix J := by
    ext v a
    simp only [R, U, D, J, Matrix.mul_diagonal, Matrix.sub_apply,
      phasedFullStarFrame, phasedFullStarMolecule, complexifyRealMatrix_apply,
      PiLp.sub_apply, PiLp.smul_apply, PrimeStar.complexifyEuclidean_apply, smul_eq_mul]
    push_cast
    ring
  have hfactor : (P * R - U) * D = P * complexifyRealMatrix J := by
    rw [← hraw, ← Matrix.mul_assoc, Matrix.mul_sub, hPU]
  have hP : ‖P‖ ≤ 1 := IsStarProjection.norm_le _ (oneExitProjection_isStarProjection S X)
  have hn : matrixL2OperatorNorm ((P * R - U) * D) ≤ 2 * ‖J‖ := by
    rw [hfactor]
    change ‖P * complexifyRealMatrix J‖ ≤ _
    calc
      _ ≤ ‖P‖ * ‖complexifyRealMatrix J‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * (2 * ‖J‖) := mul_le_mul hP
        (rectangular_complexification_operatorNorm_le J) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hs := (sq_le_sq₀ (by exact norm_nonneg _) (by positivity)).mpr hn
  have hb : ‖J‖ ^ 2 ≤ Cr * Real.log (X : ℝ) ^ 2 *
      Real.sqrt (K / Real.log (X : ℝ)) := hr K hKpos hK
  change matrixL2OperatorNorm ((P * R - U) * D) ^ 2 ≤ _
  nlinarith only [hs, hb]

end EnergyWeightedBoundary


section ActualPrefixComplement

open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical

/-- Both terms of the corrected terminal Schur majorant vanish below the
square-root endpoint, after any fixed logarithmic loss. -/
theorem tendsto_terminalBufferedSchurMajorant_zero
    (D : ℕ) {θ : ℝ} (hθpos : 0 < θ) (hθhigh : θ < (1 : ℝ) / 2) :
    Filter.Tendsto
      (fun X : ℕ ↦
        Real.log (X : ℝ) ^ D *
          (Real.log (X : ℝ) / powerScale θ X +
            powerScale θ X / Real.sqrt (X : ℝ)))
      Filter.atTop (nhds 0) := by
  have hfirstRaw :=
    tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero
      ((D + 1 : ℕ) : ℝ) (show (0 : ℝ) < θ from hθpos)
  have hfirst : Filter.Tendsto
      (fun X : ℕ ↦
        Real.log (X : ℝ) ^ (D + 1) / powerScale θ X)
      Filter.atTop (nhds 0) := by
    refine hfirstRaw.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1] with X hX
    have hlog : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    rw [powerScale, Real.rpow_zero, Real.rpow_natCast]
    ring
  have hsecondRaw :=
    tendsto_log_rpow_mul_rpow_div_rpow_natCast_zero
      (D : ℝ) hθhigh
  have hsecond : Filter.Tendsto
      (fun X : ℕ ↦
        Real.log (X : ℝ) ^ D * powerScale θ X /
          Real.sqrt (X : ℝ))
      Filter.atTop (nhds 0) := by
    refine hsecondRaw.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1] with X hX
    have hx : 0 < (X : ℝ) := by
      exact_mod_cast (show 0 < X by omega)
    have hlog : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    rw [powerScale, Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hadd := hfirst.add hsecond
  convert hadd using 1 <;> ring

/-- Uniform epsilon form of `tendsto_terminalBufferedSchurMajorant_zero`.
This is the exact scalar absorption required after an exterior self-energy is
bounded by a fixed polylogarithmic multiple of `1 / B + B / sqrt X`. -/
theorem eventually_terminalScale_polylog_schurFactor_lt
    (D : ℕ) {θ C ε : ℝ} (hθpos : 0 < θ)
    (hθhigh : θ < (1 : ℝ) / 2) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ B : ℕ,
      powerScale θ X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale θ X →
      C * Real.log (X : ℝ) ^ D *
          ((B : ℝ)⁻¹ + (B : ℝ) / Real.sqrt (X : ℝ)) < ε := by
  have hlim : Filter.Tendsto
      (fun X : ℕ ↦ C * (Real.log (X : ℝ) ^ D *
        (Real.log (X : ℝ) / powerScale θ X +
          powerScale θ X / Real.sqrt (X : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_terminalBufferedSchurMajorant_zero D hθpos hθhigh).const_mul C
  have hsmall : ∀ᶠ X : ℕ in Filter.atTop,
      C * (Real.log (X : ℝ) ^ D *
        (Real.log (X : ℝ) / powerScale θ X +
          powerScale θ X / Real.sqrt (X : ℝ))) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  filter_upwards [hsmall, Filter.eventually_gt_atTop 1] with X hsmallX hX
  intro B hBLower hBUpper
  have hx : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hscale : 0 < powerScale θ X :=
    Real.rpow_pos_of_pos hx θ
  have hrecip : (B : ℝ)⁻¹ ≤
      Real.log (X : ℝ) / powerScale θ X := by
    have hdivPos : 0 < powerScale θ X / Real.log (X : ℝ) :=
      div_pos hscale hlog
    have h := one_div_le_one_div_of_le hdivPos hBLower
    calc
      (B : ℝ)⁻¹ ≤ (powerScale θ X / Real.log (X : ℝ))⁻¹ := by
        simpa [one_div] using h
      _ = Real.log (X : ℝ) / powerScale θ X := by
        rw [inv_div]
  have hsqrt : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.2 hx
  have hratio : (B : ℝ) / Real.sqrt (X : ℝ) ≤
      powerScale θ X / Real.sqrt (X : ℝ) :=
    div_le_div_of_nonneg_right hBUpper hsqrt.le
  have hlogPow : 0 ≤ Real.log (X : ℝ) ^ D := by positivity
  have hfactor :
      (B : ℝ)⁻¹ + (B : ℝ) / Real.sqrt (X : ℝ) ≤
        Real.log (X : ℝ) / powerScale θ X +
          powerScale θ X / Real.sqrt (X : ℝ) :=
    add_le_add hrecip hratio
  calc
    C * Real.log (X : ℝ) ^ D *
          ((B : ℝ)⁻¹ + (B : ℝ) / Real.sqrt (X : ℝ)) ≤
        C * Real.log (X : ℝ) ^ D *
          (Real.log (X : ℝ) / powerScale θ X +
            powerScale θ X / Real.sqrt (X : ℝ)) := by
      gcongr
    _ = C * (Real.log (X : ℝ) ^ D *
          (Real.log (X : ℝ) / powerScale θ X +
            powerScale θ X / Real.sqrt (X : ℝ))) := by ring
    _ < ε := hsmallX


/-- The corrected coherent residual budget is small at both consumed scales. -/
theorem eventually_terminalScale_residualBudget_lt
    (D : ℕ) {θ C P ε : ℝ} (hθpos : 0 < θ) (hθhigh : θ < 1 / 2)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ B K : ℕ,
      powerScale θ X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale θ X → (K : ℝ) ≤ P * B →
      C * Real.log (X : ℝ) ^ D * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) <
          ε * ((B : ℝ) / Real.log (X : ℝ)) ∧
      C * Real.log (X : ℝ) ^ D * (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) <
          ε * ((X : ℝ) / (B * Real.log (X : ℝ))) := by
  filter_upwards [eventually_terminalScale_polylog_schurFactor_lt (D + 1)
    hθpos hθhigh (C := C * (1 + P ^ 2)) (by positivity) hε,
    eventually_gt_atTop 1] with X hs hX
  intro B K hlo hhi hK
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < (B : ℝ) :=
    lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hx θ) hL) hlo
  have hroot : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hx
  have hbroot : (B : ℝ) ≤ Real.sqrt (X : ℝ) := by
    apply hhi.trans
    simpa only [powerScale, Real.sqrt_eq_rpow] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX.le) hθhigh.le
  have hbX : (B : ℝ) ^ 2 ≤ X := by nlinarith [Real.sq_sqrt hx.le]
  have hk2 : (K : ℝ) ^ 2 ≤ P ^ 2 * (B : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (by positivity) (mul_nonneg hP hb.le)).mpr hK
    simpa only [mul_pow] using h
  have hfactor : 1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ) ≤
      (1 + P ^ 2) * (1 + (B : ℝ) ^ 2 / Real.sqrt (X : ℝ)) := by
    have hd := div_le_div_of_nonneg_right hk2 hroot.le
    have hn : 0 ≤ (B : ℝ) ^ 2 / Real.sqrt (X : ℝ) := by positivity
    calc
      _ ≤ 1 + P ^ 2 * (B : ℝ) ^ 2 / Real.sqrt (X : ℝ) := add_le_add le_rfl hd
      _ ≤ _ := by
        simp only [mul_div_assoc]
        nlinarith [sq_nonneg P]
  have heq : C * (1 + P ^ 2) * Real.log (X : ℝ) ^ D *
      (1 + (B : ℝ) ^ 2 / Real.sqrt (X : ℝ)) =
      (C * (1 + P ^ 2) * Real.log (X : ℝ) ^ (D + 1) *
        ((B : ℝ)⁻¹ + (B : ℝ) / Real.sqrt (X : ℝ))) *
        ((B : ℝ) / Real.log (X : ℝ)) := by
    rw [pow_succ]
    field_simp
    ring
  have hfirst : C * Real.log (X : ℝ) ^ D *
      (1 + (K : ℝ) ^ 2 / Real.sqrt (X : ℝ)) <
        ε * ((B : ℝ) / Real.log (X : ℝ)) := by
    calc
      _ ≤ C * Real.log (X : ℝ) ^ D *
          ((1 + P ^ 2) * (1 + (B : ℝ) ^ 2 / Real.sqrt (X : ℝ))) := by gcongr
      _ = _ := by rw [← heq]; ring
      _ < _ := mul_lt_mul_of_pos_right (hs B hlo hhi) (div_pos hb hL)
  refine ⟨hfirst, hfirst.trans_le ?_⟩
  apply mul_le_mul_of_nonneg_left _ hε.le
  apply (div_le_div_iff₀ hL (mul_pos hb hL)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hbX hL.le]

/-- Both smallness conditions hold for the actual whitened prefix residual;
no abstract residual norm or spectral gap is assumed. -/
theorem eventually_terminalScale_whitenedResidual_small
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta P ε : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2)
    (hP : 0 ≤ P) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ B K : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X → (K : ℝ) ≤ P * B →
      matrixL2OperatorNorm (whitenedProjectedFullStarFrameResidual S X K) ^ 2 <
          ε * ((B : ℝ) / Real.log (X : ℝ)) ∧
      matrixL2OperatorNorm (whitenedProjectedFullStarFrameResidual S X K) ^ 2 <
          ε * ((X : ℝ) / (B * Real.log (X : ℝ))) := by
  let theta' := (theta + 1 / 2) / 2
  have ht' : theta' < 1 / 2 := by dsimp [theta']; linarith
  have hgap : 0 < theta' - theta := by dsimp [theta']; linarith
  have hpow : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (theta' - theta)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨C, hC, hres⟩ :=
    eventually_powerRange_whitenedProjectedFullStarFrameResidual_operatorNorm_sq_le S hS ht'
  filter_upwards [hres, eventually_terminalScale_residualBudget_lt 5
    hthetaPos htheta hC.le hP hε,
    hpow.eventually_ge_atTop P, eventually_gt_atTop 0] with X hr hs hp hX
  intro B K hlo hhi hK
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hkpow : (K : ℝ) ≤ powerScale theta' X := by
    calc
      _ ≤ P * B := hK
      _ ≤ (X : ℝ) ^ (theta' - theta) * powerScale theta X :=
        mul_le_mul hp hhi (by positivity) (Real.rpow_nonneg hx.le _)
      _ = powerScale theta' X := by
        rw [powerScale, ← Real.rpow_add hx]
        congr 1
        ring
  exact ⟨(hr K hkpow).trans_lt (hs B K hlo hhi hK).1,
    (hr K hkpow).trans_lt (hs B K hlo hhi hK).2⟩

open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical

private theorem forest_eq_positiveEnergy_add_nonpositiveCore (S : Finset ℕ) (X : ℕ) :
    oneExitLargePrimeMatrix S X = positiveStarFrame S X * positiveStarEnergyMatrix S X *
      (positiveStarFrame S X).conjTranspose + oneExitCoreMatrix S X := by
  let L := oneExitLargePrimeMatrix S X
  let P := positiveStarProjection S X
  let Q := positiveStarComplementProjection S X
  have hQL : Q * L = L * Q :=
    (positiveStarComplement_commutes_oneExitLargePrimeMatrix S X).eq
  have hQQ : Q * Q = Q :=
    (positiveStarComplementProjection_isStarProjection S X).isIdempotentElem.eq
  have hcore : oneExitCoreMatrix S X = L - L * P := by
    change Q * L * Q = _
    rw [hQL, Matrix.mul_assoc, hQQ]
    change L * (1 - P) = _
    rw [Matrix.mul_sub, Matrix.mul_one]
  have hLP : L * P = positiveStarFrame S X * positiveStarEnergyMatrix S X *
      (positiveStarFrame S X).conjTranspose := by
    change L * (positiveStarFrame S X * (positiveStarFrame S X).conjTranspose) = _
    rw [← Matrix.mul_assoc, oneExitLargePrimeMatrix_mul_positiveStarFrame]
  rw [hcore, ← hLP]
  change L = L * P + (L - L * P)
  abel

/-- Removing the positive modes in a complete arithmetic prefix bounds the
remaining forest form, including its negative and zero sectors. -/
theorem re_inner_forest_le_primeCount_of_prefix_orthogonal
    {S : Finset ℕ} {X K : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (x : EuclideanSpace ℂ (PrimeStar.Vertex S X))
    (hx : ∀ a : PrimeStar.Vertex S X, (a : ℕ) ≤ K →
      ⟪PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a), x⟫_ℂ = 0) :
    (⟪x, Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x⟫_ℂ).re ≤
      Real.sqrt (PrimeStar.allowedPrimeCount S (X / (K + 1)) : ℝ) * ‖x‖ ^ 2 := by
  let U := positiveStarFrame S X
  let D := positiveStarEnergyMatrix S X
  let Ul := Matrix.toEuclideanLin U
  let y := Ul.adjoint x
  let beta := Real.sqrt (PrimeStar.allowedPrimeCount S (X / (K + 1)) : ℝ)
  have hinner : ∀ v w, ⟪Ul v, Ul w⟫_ℂ = ⟪v, w⟫_ℂ := by
    intro v w
    rw [← LinearMap.adjoint_inner_right]
    change ⟪v, (Matrix.toEuclideanLin U).adjoint (Matrix.toEuclideanLin U w)⟫_ℂ = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪v, (Matrix.toEuclideanLin U.conjTranspose ∘ₗ Matrix.toEuclideanLin U) w⟫_ℂ = _
    rw [← Matrix.toLpLin_mul_same, positiveStarFrame_conjTranspose_mul_self]
    simp
  have hyn : ‖y‖ ≤ ‖x‖ := norm_isometry_adjoint_apply_le (Ul.isometryOfInner hinner) x
  have hcoeff (a : PositiveStarCenter S X) :
      y a = ⟪PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a.1), x⟫_ℂ := by
    dsimp only [y, Ul]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, U, positiveStarFrame, positiveStarFrameReal,
      complexifyRealMatrix_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro v _
    simp [moleculePositiveStarMode, PrimeStar.complexifyEuclidean_apply, mul_comm]
  have hdiag : (⟪y, Matrix.toEuclideanLin D y⟫_ℂ).re ≤ beta * ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, PiLp.inner_apply, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : (a.1 : ℕ) ≤ K
    · have hy : y a = 0 := (hcoeff a).trans (hx a.1 ha)
      simp [D, positiveStarEnergyMatrix, Matrix.toLpLin_apply,
        Matrix.mulVec_diagonal, hy]
    · have hKa : K + 1 ≤ (a.1 : ℕ) := by omega
      have hYX : squareRootCutoff X ≤ X / (a.1 : ℕ) := by
        apply (Nat.le_div_iff_mul_le a.1.property.1).mpr
        exact (Nat.mul_le_mul_left _ a.2.1).trans (Nat.sqrt_le X)
      have hdeg : PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a.1 ≤
          PrimeStar.allowedPrimeCount S (X / (K + 1)) := by
        rw [PrimeStar.largePrimeStarDegree_eq_allowedPrimeCount_sub hS a.1 a.2.1 hYX]
        exact (Nat.sub_le _ _).trans (PrimeStar.allowedPrimeCount_mono
          (Nat.div_le_div_left hKa (by omega)))
      have henergy : moleculeStarEnergy S X a.1 ≤ beta :=
        Real.sqrt_le_sqrt (by exact_mod_cast hdeg)
      have hmul := mul_le_mul_of_nonneg_right henergy (sq_nonneg ‖y a‖)
      dsimp only [D, positiveStarEnergyMatrix]
      simp only [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
      convert hmul using 1
      simp [moleculeStarEnergy, Complex.sq_norm, Complex.normSq_apply]
      ring
  have hform : (⟪x, Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) x⟫_ℂ).re =
      (⟪y, Matrix.toEuclideanLin D y⟫_ℂ).re +
        (⟪x, Matrix.toEuclideanLin (oneExitCoreMatrix S X) x⟫_ℂ).re := by
    rw [forest_eq_positiveEnergy_add_nonpositiveCore, map_add,
      LinearMap.add_apply, inner_add_right, Complex.add_re]
    congr 1
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same]
    change (⟪x, Ul (Matrix.toEuclideanLin D
      (Matrix.toEuclideanLin U.conjTranspose x))⟫_ℂ).re = _
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.adjoint_inner_left]
  rw [hform]
  have hcore := re_inner_oneExitCoreMatrix_apply_nonpos S X x
  have hnorm := (sq_le_sq₀ (norm_nonneg y) (norm_nonneg x)).mpr hyn
  exact (add_le_of_nonpos_right hcore).trans
    (hdiag.trans (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)))

/-- A valid complete prefix inherits the exact positive-star frame isometry. -/
theorem prefixPositiveStarFrame_conjTranspose_mul_self
    {S : Finset ℕ} {X K : ℕ}
    (hv : ∀ a : MoleculeCenter S X K, (a.1 : ℕ) ≤ squareRootCutoff X ∧
      0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a.1) :
    let U : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
      fun v a ↦ PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a.1) v
    U.conjTranspose * U = 1 := by
  intro U
  let e : MoleculeCenter S X K → PositiveStarCenter S X := fun a ↦ ⟨a.1, hv a⟩
  have he : Function.Injective e := fun a b hab ↦
    Subtype.ext (congrArg (fun c : PositiveStarCenter S X ↦ c.1) hab)
  ext a b
  have h := congrArg (fun M ↦ M (e a) (e b)) (positiveStarFrame_conjTranspose_mul_self S X)
  simp only [Matrix.one_apply, he.eq_iff] at h
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, U, e, positiveStarFrame,
    positiveStarFrameReal, complexifyRealMatrix_apply,
    PrimeStar.complexifyEuclidean_apply, Matrix.one_apply, he.eq_iff] using h

set_option maxHeartbeats 1000000 in
/-- The actual whitened prefix complement is bounded using the remaining
forest energies and the source-energy-weighted frame error. -/
theorem eventually_powerRange_whitenedComplement_quadratic_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
        (Matrix.toEuclideanLin (whitenedProjectedFullStarFrame S X K)).adjoint x = 0 →
        (⟪x, Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) x⟫_ℂ).re ≤
          (Real.sqrt (PrimeStar.allowedPrimeCount S (X / (K + 1)) : ℝ) +
            C * Real.log (X : ℝ) ^ 2 * Real.sqrt (K / Real.log (X : ℝ)) +
            2 * PrimeStar.sqrtCutoffResidualScale X) * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, he⟩ :=
    eventually_powerRange_projectedRaw_weightedError_operatorNorm_sq_le_scale S hS htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [he,
    eventually_powerRange_exactPrincipalMoleculeRoot_window_and_residualSmall S hS htheta,
    eventually_powerRange_whitenedFrame_adjoint_eq_zero_iff_projectedRaw S hS htheta,
    PrimeStar.eventually_sqrtCutoff_smallPrimeGraph_l2_opNorm_le_tuned]
    with X he hv hker hreal
  intro K hKpos hK x hx
  let U : Matrix (PrimeStar.Vertex S X) (MoleculeCenter S X K) ℂ :=
    fun v a ↦ PrimeStar.complexifyEuclidean (moleculePositiveStarMode S X a.1) v
  let D : Matrix (MoleculeCenter S X K) (MoleculeCenter S X K) ℂ :=
    Matrix.diagonal fun a ↦ (Real.sqrt (moleculeStarEnergy S X a.1) : ℂ)
  let F := oneExitProjection S X * phasedFullStarFrame S X K
  let L := Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X)
  let H := Matrix.toEuclideanLin (oneExitSmallPrimeMatrix S X)
  let Ul := Matrix.toEuclideanLin U
  let Fl := Matrix.toEuclideanLin F
  let W := Matrix.toEuclideanLin D
  let E := (F - U) * D
  have hvalid (a : MoleculeCenter S X K) : (a.1 : ℕ) ≤ squareRootCutoff X ∧
      0 < PrimeStar.largePrimeStarDegree S X (squareRootCutoff X) a.1 := by
    have ha : InPowerRange theta X (a.1 : ℕ) :=
      ⟨a.1.property.1, (by exact_mod_cast a.2 : (a.1 : ℝ) ≤ K).trans hK⟩
    exact ⟨(hv a.1 ha).1, (hv a.1 ha).2.1⟩
  have hUU : U.conjTranspose * U = 1 := prefixPositiveStarFrame_conjTranspose_mul_self hvalid
  have hinner : ∀ v w, ⟪Ul v, Ul w⟫_ℂ = ⟪v, w⟫_ℂ := by
    intro v w
    rw [← LinearMap.adjoint_inner_right]
    change ⟪v, (Matrix.toEuclideanLin U).adjoint (Matrix.toEuclideanLin U w)⟫_ℂ = _
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪v, (Matrix.toEuclideanLin U.conjTranspose ∘ₗ Matrix.toEuclideanLin U) w⟫_ℂ = _
    rw [← Matrix.toLpLin_mul_same, hUU]
    simp
  let Ui := Ul.isometryOfInner hinner
  have hD : D.conjTranspose = D := by
    ext a b
    by_cases hab : a = b
    · subst b; simp [D, Matrix.conjTranspose_apply]
    · simp [D, Matrix.conjTranspose_apply, hab, Ne.symm hab]
  have hDD : D.conjTranspose * D =
      Matrix.diagonal (fun a : MoleculeCenter S X K ↦ (moleculeStarEnergy S X a.1 : ℂ)) := by
    rw [hD]
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    norm_cast
    exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hLU : ∀ v, L (Ui v) = Ui (W.adjoint (W v)) := by
    have hm : oneExitLargePrimeMatrix S X * U = U * (D.conjTranspose * D) := by
      rw [hDD]
      ext v a
      rw [Matrix.mul_diagonal]
      have h := congrArg (fun y ↦ y v)
        (oneExitLargePrimeMatrix_apply_complexified_positiveStarMode (hvalid a).1)
      simpa only [U, Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct, PiLp.smul_apply, smul_eq_mul, moleculeStarEnergy, mul_comm] using h
    intro v
    change Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) (Matrix.toEuclideanLin U v) =
      Matrix.toEuclideanLin U ((Matrix.toEuclideanLin D).adjoint (Matrix.toEuclideanLin D v))
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (Matrix.toEuclideanLin (oneExitLargePrimeMatrix S X) ∘ₗ Matrix.toEuclideanLin U) v =
      (Matrix.toEuclideanLin U ∘ₗ (Matrix.toEuclideanLin D.conjTranspose ∘ₗ Matrix.toEuclideanLin D)) v
    rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, hm]
  have hcomp : ∀ y, Ui.toLinearMap.adjoint y = 0 →
      (⟪y, L y⟫_ℂ).re ≤ Real.sqrt (PrimeStar.allowedPrimeCount S (X / (K + 1)) : ℝ) * ‖y‖ ^ 2 := by
    intro y hy
    apply re_inner_forest_le_primeCount_of_prefix_orthogonal hS y
    intro a ha
    have h := congrArg (fun v : EuclideanSpace ℂ (MoleculeCenter S X K) ↦ v ⟨a, ha⟩) hy
    change (Matrix.toEuclideanLin U).adjoint y ⟨a, ha⟩ = 0 at h
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
    simpa only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, U, PiLp.inner_apply, RCLike.inner_apply,
      starRingEnd_apply, mul_comm] using h
  have hweight : ∀ y, ‖W ((Fl - Ui.toLinearMap).adjoint y)‖ ≤ ‖E‖ * ‖y‖ := by
    intro y
    have hdiff : Matrix.toEuclideanLin (F - U) = Fl - Ui.toLinearMap := by
      change Matrix.toEuclideanLin (F - U) = Matrix.toEuclideanLin F - Matrix.toEuclideanLin U
      exact map_sub (Matrix.toLpLin 2 2) F U
    have hid : W ((Fl - Ui.toLinearMap).adjoint y) = (Matrix.toEuclideanLin E).adjoint y := by
      dsimp only [E]
      rw [Matrix.toLpLin_mul_same, LinearMap.adjoint_comp, LinearMap.comp_apply]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hD, hdiff]
    rw [hid, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have hn : ‖Matrix.toEuclideanLin E.conjTranspose y‖ ≤ ‖E.conjTranspose‖ * ‖y‖ :=
      E.conjTranspose.l2_opNorm_mulVec y
    simpa only [Matrix.l2_opNorm_conjTranspose] using hn
  let eta := PrimeStar.sqrtCutoffResidualScale X
  have heta : 0 ≤ eta := mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le
    (PrimeStar.tunedSchurScale_nonneg _)
  have hH : ∀ y, ‖H y‖ ≤ 2 * eta * ‖y‖ := by
    have hop := oneExitSmallPrimeMatrix_l2OperatorNorm_le_two_mul_real S X heta (by
      simpa [eta, PrimeStar.sqrtCutoffResidualScale, PrimeStar.sqrtCutoffResidualConstant]
        using hreal S)
    intro y
    exact ((oneExitSmallPrimeMatrix S X).l2_opNorm_mulVec y).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg y))
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((PrimeStar.largePrimeGraph S X (squareRootCutoff X)).isHermitian_adjMatrix ℂ)
  have hout := re_inner_add_le_of_weighted_frame_error L H hL Ui Fl W
    (Real.sqrt_nonneg _) (norm_nonneg E) hLU hcomp hweight hH x ((hker K hK x).mp hx)
  have hE : ‖E‖ ^ 2 ≤ C * Real.log (X : ℝ) ^ 2 * Real.sqrt (K / Real.log (X : ℝ)) :=
    he K hKpos hK
  have hA : L + H = Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) := by
    rw [← map_add]
    congr 1
    exact (moleculeFamilyComplexAdjacency_eq_large_add_small S X).symm
  rw [hA] at hout
  exact hout.trans (mul_le_mul_of_nonneg_right
    (add_le_add (add_le_add le_rfl hE) le_rfl) (sq_nonneg ‖x‖))

open Filter Topology

/-- Allowed-prime counts past a sub-square-root prefix have inverse-prefix
upper scale, uniformly in the moving prefix size. -/
theorem eventually_powerRange_afterPrefix_primeCount_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ K : ℕ, 0 < K → (K : ℝ) ≤ powerScale theta X →
      (PrimeStar.allowedPrimeCount S (X / (K + 1)) : ℝ) ≤
        12 * (X : ℝ) / (K * Real.log (X : ℝ)) := by
  filter_upwards [eventually_squareRootRange_allowedPrime_bounds S hS,
    eventually_two_mul_center_le_natSqrt_on_powerRange htheta,
    eventually_ge_atTop 4] with X hpi hcenter hX
  intro K hKpos hK
  let N := X / (K + 1)
  have hKY : K + 1 ≤ Nat.sqrt X := by
    have h := hcenter K ⟨hKpos, hK⟩
    omega
  have hYN : Nat.sqrt X ≤ N := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < K + 1)).mpr
    exact (Nat.mul_le_mul_left _ hKY).trans (Nat.sqrt_le X)
  have hNX : N ≤ X := Nat.div_le_self _ _
  obtain ⟨_, hcount, hlogN, _, hlogs⟩ := hpi N hYN hNX
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hk : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hN : (N : ℝ) ≤ (X : ℝ) / K := by
    apply (le_div_iff₀ hk).mpr
    have h := Nat.div_mul_le_self X (K + 1)
    have h' : N * K ≤ X := (Nat.mul_le_mul_left N (by omega : K ≤ K + 1)).trans h
    exact_mod_cast h'
  change (allowedPrimeCount S N : ℝ) ≤ _
  calc
    _ ≤ 4 * ((N : ℝ) / Real.log (N : ℝ)) := hcount
    _ ≤ 12 * (N : ℝ) / Real.log (X : ℝ) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hlogN hlogX]
      nlinarith [mul_le_mul_of_nonneg_left hlogs (show 0 ≤ (N : ℝ) by positivity)]
    _ ≤ 12 * ((X : ℝ) / K) / Real.log (X : ℝ) := by gcongr
    _ = _ := by ring

private theorem weightedPrefix_error_lt
    {X B L C P e d ε : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hL : 0 < L)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (he2 : e ^ 2 ≤ d * Real.sqrt X / L)
    (hfirst : C * Real.sqrt P * L ^ 2 * (B / Real.sqrt X) < ε / 2)
    (hsecond : 4 * d * B / Real.sqrt X < (ε / 2) ^ 2) :
    C * L ^ 2 * Real.sqrt (P * B / L) + 2 * e <
      ε * Real.sqrt (X / (B * L)) := by
  let mu := Real.sqrt (X / (B * L))
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by positivity)
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hmusq : mu ^ 2 = X / (B * L) := Real.sq_sqrt (by positivity)
  have hsquare := Real.sq_sqrt hX.le
  have hidentity : Real.sqrt (P * B / L) = Real.sqrt P * (B / Real.sqrt X) * mu := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hP,
      div_pow, hsquare, hmusq]
    field_simp
  have hweighted : C * L ^ 2 * Real.sqrt (P * B / L) < (ε / 2) * mu := by
    rw [hidentity]
    calc
      _ = (C * Real.sqrt P * L ^ 2 * (B / Real.sqrt X)) * mu := by ring
      _ < _ := mul_lt_mul_of_pos_right hfirst hmu
  have hsecond' := mul_lt_mul_of_pos_right hsecond (sq_pos_of_pos hmu)
  have hcancel : (4 * d * B / Real.sqrt X) * mu ^ 2 = 4 * (d * Real.sqrt X / L) := by
    rw [hmusq]
    field_simp
    nlinarith only [congrArg (fun t : ℝ ↦ d * t) hsquare]
  rw [hcancel] at hsecond'
  have heSmall : 2 * e < (ε / 2) * mu := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    calc
      (2 * e) ^ 2 ≤ 4 * (d * Real.sqrt X / L) := by nlinarith only [he2]
      _ < ((ε / 2) * mu) ^ 2 := by simpa only [mul_pow] using hsecond'
  dsimp only [mu] at hweighted heSmall
  linarith

/-- A fixed complete-prefix buffer puts the actual whitened-frame complement
below one sixteenth of the terminal energy. -/
theorem eventually_terminalScale_whitenedComplement_gap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
        (Matrix.toEuclideanLin (whitenedProjectedFullStarFrame S X (12288 * B))).adjoint x = 0 →
        (⟪x, Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X) x⟫_ℂ).re ≤
          (Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ))) / 16) * ‖x‖ ^ 2 := by
  let theta' := (theta + 1 / 2) / 2
  have ht' : theta' < 1 / 2 := by dsimp [theta']; linarith
  have hgap : 0 < theta' - theta := by dsimp [theta']; linarith
  have hpow : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (theta' - theta)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨C, hC, hform⟩ := eventually_powerRange_whitenedComplement_quadratic_le S hS ht'
  let d := 4 * PrimeStar.sqrtCutoffResidualConstant ^ 2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hw := eventually_terminalScale_polylog_schurFactor_lt 2 hthetaPos htheta
    (C := C * Real.sqrt 12288) (ε := (1 / 32) / 2) (by positivity) (by norm_num)
  have hh := eventually_terminalScale_polylog_schurFactor_lt 0 hthetaPos htheta
    (C := 4 * d) (ε := ((1 / 32) / 2) ^ 2) (by positivity) (by norm_num)
  filter_upwards [hform, eventually_powerRange_afterPrefix_primeCount_le S hS ht', hw, hh,
    PrimeStar.eventually_sqrtCutoffResidualScale_sq_le,
    hpow.eventually_ge_atTop 12288, eventually_gt_atTop 1]
    with X hf hp hw hh he hpowX hX
  intro B hlo hhi x hx
  have hxr : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hb : 0 < (B : ℝ) :=
    lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hxr theta) hL) hlo
  have hbn : 0 < B := by exact_mod_cast hb
  let K := 12288 * B
  have hk : 0 < K := Nat.mul_pos (by norm_num) hbn
  have hkpow : (K : ℝ) ≤ powerScale theta' X := by
    calc
      _ = 12288 * (B : ℝ) := by simp only [K, Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ (X : ℝ) ^ (theta' - theta) * powerScale theta X :=
        mul_le_mul hpowX hhi hb.le (Real.rpow_nonneg hxr.le _)
      _ = powerScale theta' X := by
        rw [powerScale, ← Real.rpow_add hxr]
        congr 1
        ring
  let mu := Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ)))
  have hmu : 0 < mu := Real.sqrt_pos.mpr (by positivity)
  have hbeta : Real.sqrt (PrimeStar.allowedPrimeCount S (X / (K + 1)) : ℝ) ≤ mu / 32 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), div_pow]
    dsimp only [mu]
    rw [Real.sq_sqrt (by positivity)]
    exact (hp K hk hkpow).trans_eq (by
      dsimp only [K]
      push_cast
      ring)
  have hfirst : C * Real.sqrt 12288 * Real.log (X : ℝ) ^ 2 *
      ((B : ℝ) / Real.sqrt (X : ℝ)) < (1 / 32) / 2 := by
    apply lt_of_le_of_lt _ (hw B hlo hhi)
    gcongr
    exact le_add_of_nonneg_left (by positivity)
  have hsecond : 4 * d * (B : ℝ) / Real.sqrt (X : ℝ) < ((1 / 32) / 2) ^ 2 := by
    have hbnd := hh B hlo hhi
    simp only [pow_zero, mul_one] at hbnd
    apply lt_of_le_of_lt _ hbnd
    rw [mul_div_assoc]
    gcongr
    exact le_add_of_nonneg_left (by positivity)
  have heta : 0 ≤ PrimeStar.sqrtCutoffResidualScale X :=
    mul_nonneg PrimeStar.sqrtCutoffResidualConstant_pos.le (PrimeStar.tunedSchurScale_nonneg _)
  have he2 : PrimeStar.sqrtCutoffResidualScale X ^ 2 ≤
      d * Real.sqrt (X : ℝ) / Real.log (X : ℝ) := by
    simpa only [d, mul_div_assoc] using he
  have hwerr := weightedPrefix_error_lt hxr hb hL (by norm_num : (0 : ℝ) ≤ 12288)
    heta (by norm_num : (0 : ℝ) < 1 / 32) he2 hfirst hsecond
  have hout := hf K hk hkpow x hx
  apply hout.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖x‖)
  have hcast : (K : ℝ) = 12288 * (B : ℝ) := by simp [K]
  rw [hcast]
  change _ ≤ mu / 16
  change _ < (1 / 32) * mu at hwerr
  linarith


/-- The actual one-exit operator has the same low-complement bound on the
whitened complete prefix used by the ordered residual comparison. -/
theorem eventually_terminalScale_oneExit_whitenedComplement_gap
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {theta : ℝ} (hthetaPos : 0 < theta) (htheta : theta < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ B : ℕ,
      powerScale theta X / Real.log (X : ℝ) ≤ (B : ℝ) →
      (B : ℝ) ≤ powerScale theta X →
      ∀ x : EuclideanSpace ℂ (PrimeStar.Vertex S X),
        (Matrix.toEuclideanLin (whitenedProjectedFullStarFrame S X (12288 * B))).adjoint x = 0 →
        (⟪x, Matrix.toEuclideanLin (oneExitCompression S X) x⟫_ℂ).re ≤
          (Real.sqrt ((X : ℝ) / (B * Real.log (X : ℝ))) / 16) * ‖x‖ ^ 2 := by
  filter_upwards [eventually_terminalScale_whitenedComplement_gap S hS hthetaPos htheta]
    with X hg
  intro B hlo hhi x hx
  let Q := whitenedProjectedFullStarFrame S X (12288 * B)
  let P := oneExitProjection S X
  have hP : P.conjTranspose = P :=
    (oneExitProjection_isStarProjection S X).isSelfAdjoint.isHermitian
  have hQP : Q.conjTranspose * P = Q.conjTranspose := by
    have h := congrArg Matrix.conjTranspose
      (oneExitProjection_mul_whitenedProjectedFullStarFrame S X (12288 * B))
    change (P * Q).conjTranspose = Q.conjTranspose at h
    simpa only [Matrix.conjTranspose_mul, hP] using h
  have hker : (Matrix.toEuclideanLin Q).adjoint (Matrix.toEuclideanLin P x) = 0 := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (Matrix.toEuclideanLin Q.conjTranspose ∘ₗ Matrix.toEuclideanLin P) x = 0
    rw [← Matrix.toLpLin_mul_same, hQP, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact hx
  rw [show (⟪x, Matrix.toEuclideanLin (oneExitCompression S X) x⟫_ℂ).re =
    (⟪Matrix.toEuclideanLin P x, Matrix.toEuclideanLin (moleculeFamilyComplexAdjacency S X)
      (Matrix.toEuclideanLin P x)⟫_ℂ).re from oneExitCompression_quadraticForm_eq S X x]
  apply (hg B hlo hhi (Matrix.toEuclideanLin P x) hker).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_oneExitProjection_apply_le S X x)

end ActualPrefixComplement

end PrimeCoverPowerBand
