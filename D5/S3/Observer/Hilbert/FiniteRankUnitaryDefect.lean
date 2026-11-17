/- GID: D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/FiniteRankUnitaryDefect
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: Finite-rank projection defects have their genuine ambient Hilbert-Schmidt square sums. -/

import D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut
import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Trace

/-! Finite-rank operators are measured on arbitrary, possibly uncountable Hilbert bases. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Hilbert.FiniteRankUnitaryDefect

open scoped InnerProductSpace
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite sum of genuine ambient rank-one operators. -/
def finiteOperator {ι : Type*} [Fintype ι] (v w : ι → H) : H →L[ℂ] H :=
  ∑ i, rankOne ℂ (v i) (w i)

private theorem finite_operator_energy {ι β : Type*} [Fintype ι]
    (v w : ι → H) (b : HilbertBasis β ℂ H) :
    HasSum (fun l => ‖finiteOperator v w (b l)‖ ^ 2)
      (Complex.re (∑ i, ∑ j, inner ℂ (v i) (v j) * inner ℂ (w j) (w i))) := by
  classical
  have hp (i j : ι) :=
    ((b.hasSum_inner_mul_inner (w j) (w i)).mul_left (inner ℂ (v i) (v j)))
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => hp i j))
  have he (l : β) :
      inner ℂ (finiteOperator v w (b l)) (finiteOperator v w (b l)) =
        ∑ i, ∑ j, inner ℂ (v i) (v j) *
          (inner ℂ (w j) (b l) * inner ℂ (b l) (w i)) := by
    simp only [finiteOperator, sum_apply, rankOne_apply,
      sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← inner_conj_symm (b l) (w i)]
    ring
  have hself (z : H) : (inner ℂ z z).re = ‖z‖ ^ 2 := by
    change RCLike.re (inner ℂ z z) = _
    exact inner_self_eq_norm_sq z
  have hh := hs.mapL Complex.reCLM
  simpa only [Complex.reCLM_apply, ← he, hself] using hh

private theorem orthonormal_pair_energy {ι β : Type*} [Fintype ι]
    (u v : ι → H) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (b : HilbertBasis β ℂ H) :
    HasSum (fun l => ‖(finiteOperator u u - finiteOperator v v) (b l)‖ ^ 2)
      (2 * Fintype.card ι - 2 * ∑ i, ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2) := by
  classical
  let x : Sum ι ι → H := Sum.elim u (fun j => -v j)
  let y : Sum ι ι → H := Sum.elim u v
  have hp := finite_operator_energy x y b
  have heq : finiteOperator x y = finiteOperator u u - finiteOperator v v := by
    ext z
    simp [finiteOperator, x, y, Fintype.sum_sum_type, rankOne_apply,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [heq] at hp
  have hreal : Complex.re (∑ i, ∑ j, inner ℂ (x i) (x j) * inner ℂ (y j) (y i)) =
      2 * Fintype.card ι - 2 * ∑ i, ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2 := by
    simp only [x, y, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      inner_neg_left, inner_neg_right, neg_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Complex.re_sum, Complex.add_re, Complex.neg_re]
    have hm (a c : H) : (inner ℂ a c * inner ℂ c a).re = ‖inner ℂ a c‖ ^ 2 := by
      change RCLike.re (inner ℂ a c * inner ℂ c a) = _
      rw [inner_mul_symm_re_eq_norm, norm_mul, norm_inner_symm c a, pow_two]
    simp_rw [hm]
    have hd (w : ι → H) (hw : Orthonormal ℂ w) :
        ∑ i, ∑ j, ‖inner ℂ (w i) (w j)‖ ^ 2 = Fintype.card ι := by
      have hh (i j : ι) : ‖inner ℂ (w i) (w j)‖ ^ 2 =
          if i = j then 1 else 0 := by
        by_cases hij : i = j
        · subst j
          simp only [orthonormal_iff_ite.mp hw, ite_true, norm_one, one_pow]
        · simp only [orthonormal_iff_ite.mp hw, if_neg hij, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      simp_rw [hh]
      simp
    rw [hd u hu, hd v hv]
    have hc : (∑ i, ∑ j, ‖inner ℂ (v i) (u j)‖ ^ 2) =
        ∑ i, ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [norm_inner_symm (v _) (u _)]
    rw [hc]
    ring
  rwa [hreal] at hp


/-- Conjugating a finite-rank orthogonal projection has exactly twice the
cross-block energy, measured on any ambient Hilbert basis. -/
theorem unitary_projection_defect_hasSum {ι β : Type*} [Fintype ι]
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (c : OrthonormalBasis ι ℂ S) (U : H ≃ₗᵢ[ℂ] H) (b : HilbertBasis β ℂ H) :
    HasSum (fun l => ‖(U.toLinearIsometry.toContinuousLinearMap.comp
      (S.starProjection.comp U.symm.toLinearIsometry.toContinuousLinearMap) - S.starProjection) (b l)‖ ^ 2)
      (2 * ∑ i, ‖Sᗮ.starProjection (U (c i : H))‖ ^ 2) := by
  classical
  let v : ι → H := fun i => c i
  let u : ι → H := fun i => U (v i)
  have hv : Orthonormal ℂ v := c.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  have hu : Orthonormal ℂ u := hv.comp_linearIsometryEquiv U
  have hp := orthonormal_pair_energy u v hu hv b
  have hvp : finiteOperator v v = S.starProjection := by
    exact c.starProjection_eq_sum_rankOne.symm
  have hup : finiteOperator u u = U.toLinearIsometry.toContinuousLinearMap.comp
      (S.starProjection.comp U.symm.toLinearIsometry.toContinuousLinearMap) := by
    rw [← hvp]
    ext z
    simp only [finiteOperator, ContinuousLinearMap.comp_apply, sum_apply, rankOne_apply,
      map_sum, map_smul, u]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (U (v i)) z • U (v i) = inner ℂ (v i) (U.symm z) • U (v i)
    rw [U.inner_map_eq_flip]
  rw [hup, hvp] at hp
  have he (i : ι) :
      ‖Sᗮ.starProjection (u i)‖ ^ 2 =
        1 - ∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2 := by
    have hpy := S.norm_sq_eq_add_norm_sq_starProjection (u i)
    have hparse := c.sum_sq_norm_inner_left (S.orthogonalProjectionOnto (u i))
    have hparse' : (∑ j, ‖inner ℂ (u i) (v j)‖ ^ 2) =
        ‖S.starProjection (u i)‖ ^ 2 := by
      calc
        _ = ‖S.orthogonalProjectionOnto (u i)‖ ^ 2 := by
          simpa only [v, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hparse
        _ = _ := rfl
    rw [hu.1 i, one_pow] at hpy
    linarith
  change HasSum _ (2 * ∑ i, ‖Sᗮ.starProjection (u i)‖ ^ 2)
  simp_rw [he]
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, mul_sub] using hp

#print axioms unitary_projection_defect_hasSum


/-- The actual ambient conjugation defect of an orthogonal projection. -/
def projectionDefect (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  U.toLinearIsometry.toContinuousLinearMap.comp (S.starProjection.comp U.symm.toLinearIsometry.toContinuousLinearMap) -
    S.starProjection

private theorem defect_square_le {β : Type*} (b : HilbertBasis β ℂ H)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (U : H ≃ₗᵢ[ℂ] H) (L : ℝ)
    (h : ∀ y ∈ S, ‖Sᗮ.starProjection (U y)‖ ≤ L * ‖y‖) :
    Summable (fun l => ‖projectionDefect S U (b l)‖ ^ 2) ∧
      (∑' l, ‖projectionDefect S U (b l)‖ ^ 2) ≤
        2 * Module.finrank ℂ S * L ^ 2 := by
  let c := stdOrthonormalBasis ℂ S
  have hp := unitary_projection_defect_hasSum S c U b
  change HasSum (fun l => ‖projectionDefect S U (b l)‖ ^ 2) _ at hp
  refine ⟨hp.summable, ?_⟩
  rw [hp.tsum_eq]
  have hc : ∑ i, ‖Sᗮ.starProjection (U (c i : H))‖ ^ 2 ≤
      Module.finrank ℂ S * L ^ 2 := by
    calc
      _ ≤ ∑ i : Fin (Module.finrank ℂ S), L ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := h (c i) (c i).property
        rw [show ‖(c i : H)‖ = 1 from c.norm_eq_one i, mul_one] at hi
        exact pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ = _ := by simp
  nlinarith

private theorem pair_defect_bound {β : Type*} (b : HilbertBasis β ℂ H)
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : Module.finrank ℂ S ≤ 24)
    (U : Fin 2 → H ≃ₗᵢ[ℂ] H) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ g y, y ∈ S → ‖Sᗮ.starProjection (U g y)‖ ≤ L * ‖y‖) :
    (∀ g, Summable (fun l => ‖projectionDefect S (U g) (b l)‖ ^ 2)) ∧
      Real.sqrt ((1 / 2 : ℝ) * ∑ g : Fin 2,
        ∑' l, ‖projectionDefect S (U g) (b l)‖ ^ 2) ≤ 7 * L := by
  have hg := fun g => defect_square_le b S (U g) L (h g)
  refine ⟨fun g => (hg g).1, ?_⟩
  have hsum : (∑ g : Fin 2, ∑' l, ‖projectionDefect S (U g) (b l)‖ ^ 2) ≤
      2 * (2 * Module.finrank ℂ S * L ^ 2) := by
    calc
      _ ≤ ∑ _ : Fin 2, 2 * Module.finrank ℂ S * L ^ 2 :=
        Finset.sum_le_sum fun g _ => (hg g).2
      _ = _ := by simp
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hSr : (Module.finrank ℂ S : ℝ) ≤ 24 := by exact_mod_cast hS
    nlinarith [sq_nonneg L, mul_le_mul_of_nonneg_right hSr (sq_nonneg L)]

/-- A condition-free finite-synthesis bridge on an arbitrary ambient Hilbert space.
The numerical hypotheses are operator-norm intertwining bounds, with no spectral,
independence, invariance or Gram-invertibility premise. -/
private theorem exists_rank_twentyfour_projection_bound_positive {β : Type*} (b : HilbertBasis β ℂ H)
    (T : EuclideanSpace ℂ (Fin 24) →L[ℂ] H)
    (hT : ∃ z : EuclideanSpace ℂ (Fin 24), ‖z‖ = 1 ∧ 1 ≤ ‖T z‖)
    (U : Fin 2 → H ≃ₗᵢ[ℂ] H)
    (M : Fin 2 → EuclideanSpace ℂ (Fin 24) →L[ℂ] EuclideanSpace ℂ (Fin 24))
    (δ : ℝ) (hδ : 0 < δ)
    (hM : ∀ g, ‖M g‖ ≤ 85)
    (hZ : ∀ g, ‖(U g).toLinearIsometry.toContinuousLinearMap.comp T - T.comp (M g)‖ ≤ 95 * δ) :
    ∃ S : Submodule ℂ H, ∃ _ : FiniteDimensional ℂ S,
      1 ≤ Module.finrank ℂ S ∧ Module.finrank ℂ S ≤ 24 ∧
      (∀ g, Summable (fun l => ‖projectionDefect S (U g) (b l)‖ ^ 2)) ∧
      Real.sqrt ((1 / 2 : ℝ) * ∑ g : Fin 2,
        ∑' l, ‖projectionDefect S (U g) (b l)‖ ^ 2) ≤ 785 * δ ^ (1 / 24 : ℝ) := by
  let r : ℝ := δ ^ (1 / 24 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hδ _
  have hrpow : r ^ 24 = δ := by
    simpa [r] using Real.rpow_inv_natCast_pow hδ.le (by norm_num : (24 : ℕ) ≠ 0)
  by_cases hrsmall : r < 5 / 6
  · let η : ℝ := (6 / 5) * r
    have hη : 0 < η := by dsimp [η]; positivity
    have hη1 : η < 1 := by dsimp [η]; linarith
    obtain ⟨k, hr1, hrn, hframe, hcut⟩ :=
      D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut.exists_cut_intertwining_bound
        T hT η hη hη1
    let S := D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut.imageCut T k
    let L : ℝ := 85 * η + 95 * δ * (η ^ 23)⁻¹
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hleak : ∀ g y, y ∈ S → ‖Sᗮ.starProjection (U g y)‖ ≤ L * ‖y‖ := by
      intro g y hy
      have hc := hcut (U g).toLinearIsometry.toContinuousLinearMap (M g) y hy
      simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] at hc
      rw [← Submodule.starProjection_orthogonal_val] at hc
      calc
        _ ≤ (η * ‖M g‖ + (η ^ 23)⁻¹ *
          ‖(U g).toLinearIsometry.toContinuousLinearMap.comp T - T.comp (M g)‖) * ‖y‖ := hc
        _ ≤ L * ‖y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
          have ha := mul_le_mul_of_nonneg_left (hM g) hη.le
          have hz := mul_le_mul_of_nonneg_left (hZ g)
            (inv_nonneg.mpr (pow_nonneg hη.le 23))
          dsimp [L]
          nlinarith
    have hbound := pair_defect_bound b S (by simpa [S] using hrn) U L hL hleak
    refine ⟨S, inferInstance, hr1, by simpa [S] using hrn, hbound.1, hbound.2.trans ?_⟩
    have hscale : δ * (η ^ 23)⁻¹ = r / (6 / 5 : ℝ) ^ 23 := by
      rw [← hrpow]
      dsimp [η]
      field_simp
    have hten : (10 : ℝ) ≤ (6 / 5 : ℝ) ^ 23 := by norm_num
    have hfrac : r / (6 / 5 : ℝ) ^ 23 ≤ r / 10 :=
      div_le_div_of_nonneg_left hr.le (by norm_num) hten
    dsimp [L, η]
    rw [mul_assoc (95 : ℝ) δ _, hscale]
    change 7 * (85 * ((6 / 5) * r) + 95 * (r / (6 / 5 : ℝ) ^ 23)) ≤ 785 * r
    nlinarith
  · obtain ⟨k, hr1, hrn, _, _⟩ :=
      D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut.exists_cut_intertwining_bound
        T hT (1 / 2) (by norm_num) (by norm_num)
    let S := D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut.imageCut T k
    have hleak : ∀ g y, y ∈ S → ‖Sᗮ.starProjection (U g y)‖ ≤ (1 : ℝ) * ‖y‖ := by
      intro g y _
      simpa only [one_mul, LinearIsometryEquiv.norm_map] using
        Sᗮ.norm_starProjection_apply_le (U g y)
    have hb := pair_defect_bound b S (by simpa [S] using hrn) U 1 (by norm_num) hleak
    refine ⟨S, inferInstance, hr1, by simpa [S] using hrn, hb.1, hb.2.trans ?_⟩
    dsimp only [r] at hrsmall ⊢
    push Not at hrsmall
    linarith




private theorem projection_defect_isHilbertSchmidt
    (S : Submodule ℂ H) [FiniteDimensional ℂ S] (U : H ≃ₗᵢ[ℂ] H) :
    HilbertSchmidt.IsHilbertSchmidt (projectionDefect S U) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, b, (unitary_projection_defect_hasSum S (stdOrthonormalBasis ℂ S) U b).summable⟩

private theorem range_projection_defect_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →L[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) (M : E →L[ℂ] E)
    (h : U.toLinearIsometry.toContinuousLinearMap.comp T = T.comp M) :
    projectionDefect T.range U = 0 := by
  let S : Submodule ℂ H := T.range
  let f : H →ₗ[ℂ] H := U.toLinearEquiv.toLinearMap
  have hinv : S.map f ≤ S := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    refine ⟨M z, ?_⟩
    exact (congrArg (fun A : E →L[ℂ] H => A z) h).symm
  have heq : S.map f = S :=
    Submodule.eq_of_le_of_finrank_eq hinv (U.toLinearEquiv.finrank_map_eq S)
  letI : FiniteDimensional ℂ (S.map f) := Module.Finite.map S f
  have hc (x : H) : U (S.starProjection (U.symm x)) = S.starProjection x := by
    have hh := U.toLinearIsometry.map_starProjection S (U.symm x)
    change U (S.starProjection (U.symm x)) = (S.map f).starProjection (U (U.symm x)) at hh
    simpa only [heq, U.apply_symm_apply] using hh
  ext x
  exact sub_eq_zero.mpr (hc x)

/-- The finite-synthesis projection theorem, including the exact zero case.
All projections act on the original arbitrary complex Hilbert ambient space. -/
theorem exists_rank_twentyfour_projection_bound {β : Type*} (b : HilbertBasis β ℂ H)
    (T : EuclideanSpace ℂ (Fin 24) →L[ℂ] H)
    (hT : ∃ z : EuclideanSpace ℂ (Fin 24), ‖z‖ = 1 ∧ 1 ≤ ‖T z‖)
    (U : Fin 2 → H ≃ₗᵢ[ℂ] H)
    (M : Fin 2 → EuclideanSpace ℂ (Fin 24) →L[ℂ] EuclideanSpace ℂ (Fin 24))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ g, ‖M g‖ ≤ 85)
    (hZ : ∀ g, ‖(U g).toLinearIsometry.toContinuousLinearMap.comp T - T.comp (M g)‖ ≤ 95 * δ) :
    ∃ S : Submodule ℂ H, ∃ _ : FiniteDimensional ℂ S,
      1 ≤ Module.finrank ℂ S ∧ Module.finrank ℂ S ≤ 24 ∧
      (∀ g, HilbertSchmidt.IsHilbertSchmidt (projectionDefect S (U g))) ∧
      (∀ g, Summable (fun l => ‖projectionDefect S (U g) (b l)‖ ^ 2)) ∧
      Real.sqrt ((1 / 2 : ℝ) * ∑ g : Fin 2,
        ∑' l, ‖projectionDefect S (U g) (b l)‖ ^ 2) ≤ 785 * δ ^ (1 / 24 : ℝ) ∧
      (δ = 0 → ∀ g, projectionDefect S (U g) = 0) := by
  by_cases hzero : δ = 0
  · subst δ
    let S : Submodule ℂ H := T.range
    have hrn : Module.finrank ℂ S ≤ 24 := by
      simpa [S] using T.toLinearMap.finrank_range_le
    have hr1 : 1 ≤ Module.finrank ℂ S := by
      apply Submodule.one_le_finrank_iff.mpr
      intro heq
      obtain ⟨z, _, hz⟩ := hT
      have hm : T z ∈ S := ⟨z, rfl⟩
      rw [heq, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hz
      norm_num at hz
    have hg (g : Fin 2) : projectionDefect S (U g) = 0 := by
      apply range_projection_defect_zero T (U g) (M g)
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa using hZ g) (norm_nonneg _)
    refine ⟨S, inferInstance, hr1, hrn, fun g => projection_defect_isHilbertSchmidt S (U g),
      ?_, ?_, fun _ => hg⟩
    · intro g
      simp only [hg, ContinuousLinearMap.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact summable_zero
    · simp [hg, Real.zero_rpow (by norm_num : (1 / 24 : ℝ) ≠ 0)]
  · obtain ⟨S, hS, hr1, hrn, hs, hb⟩ :=
      exists_rank_twentyfour_projection_bound_positive b T hT U M δ
        (lt_of_le_of_ne hδ (Ne.symm hzero)) hM hZ
    letI := hS
    exact ⟨S, hS, hr1, hrn, fun g => projection_defect_isHilbertSchmidt S (U g),
      hs, hb, fun h => (hzero h).elim⟩

#print axioms exists_rank_twentyfour_projection_bound

end D5.S3.Observer.Hilbert.FiniteRankUnitaryDefect
