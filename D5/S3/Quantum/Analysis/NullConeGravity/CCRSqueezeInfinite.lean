/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-summable mode squeezes give a unit Fock vector with diagonal Weyl covariance. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
import D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeSingle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
Finite occupation products and their norm limit give a Fock vector for a
square-summable family of one-mode squeezes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Complex
open scoped BigOperators ComplexConjugate InnerProductSpace Topology

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeInfinite

open CCRFockOccupation CCRFockWeyl CCRSqueezeSingle

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def oneOccupation : Occupation Unit ≃ ℕ :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)

private theorem oneOccupation_symm (n : ℕ) : oneOccupation.symm n = Finsupp.single () n := by
  apply Finsupp.ext
  intro i
  cases i
  simp [oneOccupation, Equiv.funUnique, Equiv.piUnique]

private def supportedOccupation (F : Finset ι) :
    (F → ℕ) ≃ {α : Occupation ι // α.support ⊆ F} where
  toFun n := ⟨(Finsupp.equivFunOnFinite.symm n).embDomain (Function.Embedding.subtype (· ∈ F)),
    fun i hi => by
      rw [Finsupp.support_embDomain] at hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.property⟩
  invFun α i := α.1 i
  left_inv n := by
    ext i
    exact Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∈ F))
      (Finsupp.equivFunOnFinite.symm n) i
  right_inv α := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ F
    · exact Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∈ F))
        (Finsupp.equivFunOnFinite.symm (fun j : F => α.1 j)) ⟨i, hi⟩
    · rw [Finsupp.embDomain_of_notMem_range]
      · exact (Finsupp.notMem_support_iff.mp (fun h => hi (α.2 h))).symm
      · rintro ⟨j, rfl⟩
        exact hi j.property

set_option maxHeartbeats 800000 in
-- Reindexing function spaces through finite-type equivalences requires extra elaboration.
private theorem hasSum_prod {J : Type*} [Fintype J] (f : J → ℕ → ℂ) (c : J → ℂ)
    (hf : ∀ j, HasSum (f j) (c j)) (hn : ∀ j, Summable (fun n => ‖f j n‖)) :
    HasSum (fun n : J → ℕ => ∏ j, f j (n j)) (∏ j, c j) := by
  classical
  revert f c
  refine Fintype.induction_empty_option (P := fun J [Fintype J] =>
    ∀ (f : J → ℕ → ℂ) (c : J → ℂ), (∀ j, HasSum (f j) (c j)) →
      (∀ j, Summable (fun n => ‖f j n‖)) →
        HasSum (fun n : J → ℕ => ∏ j, f j (n j)) (∏ j, c j)) ?_ ?_ ?_ J
  · intro A B _ e ih f c hf hn
    let : Fintype A := Fintype.ofEquiv B e.symm
    let en := Equiv.arrowCongr e (Equiv.refl ℕ)
    apply en.hasSum_iff.mp
    rw [← Fintype.prod_equiv e (c ∘ e) c (fun _ => rfl)]
    refine (ih (f ∘ e) (c ∘ e) (fun j => hf (e j)) (fun j => hn (e j))).congr_fun fun n => ?_
    symm
    exact Fintype.prod_equiv e _ _ (fun j => by simp [en])
  · intro f c _ _
    simp
  · intro J _ ih f c hf hn
    rw [Fintype.prod_option]
    let e := Equiv.piOptionEquivProd (β := fun _ : Option J => ℕ)
    apply e.symm.hasSum_iff.mp
    simp only [Fintype.prod_option]
    let g (n : J → ℕ) : ℂ := ∏ j, f (some j) (n j)
    have hg : HasSum g (∏ j, c (some j)) := ih _ _ (fun j => hf (some j)) (fun j => hn (some j))
    have hgn : Summable (fun n => ‖g n‖) := by
      have h := (ih (fun j n => (‖f (some j) n‖ : ℂ)) (fun j => (∑' n, ‖f (some j) n‖ : ℝ))
        (fun j => (hn (some j)).hasSum.map Complex.ofRealCLM Complex.ofRealCLM.continuous)
        (fun j => by simpa using hn (some j))).map Complex.reCLM Complex.reCLM.continuous
      refine h.summable.congr fun n => ?_
      change (∏ j, (‖f (some j) (n j)‖ : ℂ)).re = ‖g n‖
      dsimp [g]
      rw [← Complex.ofReal_prod, ofReal_re, norm_prod]
    exact (hf none).mul (f := f none) (g := g) hg
      (summable_mul_of_summable_norm (hn none) hgn)

private def tensorCoeff (F : Finset ι) (v : ι → BosonFock Unit) (α : Occupation ι) : ℂ :=
  by classical exact if α.support ⊆ F then ∏ i ∈ F, v i (Finsupp.single () (α i)) else 0

private theorem tensorCoeff_inner (F : Finset ι) (v w : ι → BosonFock Unit) :
    HasSum (fun α => conj (tensorCoeff F v α) * tensorCoeff F w α) (∏ i ∈ F, ⟪v i, w i⟫_ℂ) := by
  classical
  apply (hasSum_subtype_iff_of_support_subset
    (s := {α : Occupation ι | α.support ⊆ F}) ?_).mp
  · apply (supportedOccupation F).hasSum_iff.mp
    rw [← Finset.prod_attach]
    refine (hasSum_prod
      (fun (i : F) n => conj (v i (Finsupp.single () n)) * w i (Finsupp.single () n))
      (fun i => ⟪v i, w i⟫_ℂ) (fun i => ?_) (fun i => ?_)).congr_fun fun n => ?_
    · simpa [Function.comp_def, oneOccupation_symm, RCLike.inner_apply, mul_comm] using
        oneOccupation.symm.hasSum_iff.mpr (lp.hasSum_inner (𝕜 := ℂ) (v i) (w i))
    · simpa [Function.comp_def, oneOccupation_symm, norm_mul, Complex.norm_conj] using
        oneOccupation.symm.summable_iff.mpr (lp.summable_mul
          (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two) (v i) (w i))
    · simp only [Function.comp_apply, tensorCoeff, (supportedOccupation F n).2, ite_true,
        map_prod, ← Finset.prod_mul_distrib]
      rw [← Finset.prod_attach]
      apply Finset.prod_congr rfl
      intro i _
      have hi : ((supportedOccupation F n).1) i = n i :=
        congrFun ((supportedOccupation F).left_inv n) i
      rw [hi]
  · intro α h
    by_contra ha
    change ¬ α.support ⊆ F at ha
    exact h (by simp [tensorCoeff, ha])

private def finiteTensor (F : Finset ι) (v : ι → BosonFock Unit) : BosonFock ι :=
  ⟨tensorCoeff F v, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine ((tensorCoeff_inner F v v).map Complex.reCLM Complex.reCLM.continuous).summable.congr ?_
    intro α
    change (conj (tensorCoeff F v α) * tensorCoeff F v α).re = _
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]⟩

private theorem finiteTensor_inner (F : Finset ι) (v w : ι → BosonFock Unit) :
    ⟪finiteTensor F v, finiteTensor F w⟫_ℂ = ∏ i ∈ F, ⟪v i, w i⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, mul_comm _ (conj _)]
  change (∑' α, conj (tensorCoeff F v α) * tensorCoeff F w α) = _
  exact (tensorCoeff_inner F v w).tsum_eq

/-- Product of the specified squeezed vacua, with zero occupation off the finite set. -/
def finiteSqueeze (r : ι → ℝ) (F : Finset ι) : BosonFock ι :=
  finiteTensor F (fun i => squeezeVacuum (r i))

theorem finiteSqueeze_apply (r : ι → ℝ) (F : Finset ι) (α : Occupation ι) :
    finiteSqueeze r F α =
      @ite ℂ (α.support ⊆ F) (Classical.propDecidable _)
        (∏ i ∈ F, squeezeVacuum (r i) (Finsupp.single () (α i))) 0 := by
  change tensorCoeff F (fun i => squeezeVacuum (r i)) α = _
  unfold tensorCoeff
  split_ifs <;> rfl

theorem finiteSqueeze_norm (r : ι → ℝ) (F : Finset ι) : ‖finiteSqueeze r F‖ = 1 := by
  have h : ⟪finiteSqueeze r F, finiteSqueeze r F⟫_ℂ = 1 := by
    rw [finiteSqueeze, finiteTensor_inner]
    simp [inner_self_eq_norm_sq_to_K, squeezeVacuum_norm]
  have hn : ‖finiteSqueeze r F‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, h]
    rfl
  exact (sq_eq_one_iff.mp hn).resolve_right (by linarith [norm_nonneg (finiteSqueeze r F)])

private theorem vacuum_single (n : ℕ) :
    fockVacuum Unit (Finsupp.single () n) = if n = 0 then 1 else 0 := by
  classical
  simp [fockVacuum, lp.single_apply, Pi.single_apply, Finsupp.single_eq_zero]

open Classical in
private theorem finiteTensor_extend (F G : Finset ι) (hFG : F ⊆ G) (v : ι → BosonFock Unit) :
    finiteTensor F v = finiteTensor G (fun i => if i ∈ F then v i else fockVacuum Unit) := by
  classical
  apply lp.ext
  funext α
  change tensorCoeff F v α = tensorCoeff G _ α
  by_cases hF : α.support ⊆ F
  · simp only [tensorCoeff, hF, hF.trans hFG, ite_true]
    rw [← Finset.prod_sdiff hFG]
    rw [Finset.prod_eq_one (s := G \ F), one_mul]
    · exact Finset.prod_congr rfl fun i hi => by simp [hi]
    · intro i hi
      have hi' := (Finset.mem_sdiff.mp hi).2
      have hzero : α i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi' (hF h))
      rw [ite_eq_right hi', vacuum_single, hzero, ite_eq_left rfl]
  · by_cases hG : α.support ⊆ G
    · obtain ⟨i, hi, hi'⟩ := Finset.not_subset.mp hF
      simp only [tensorCoeff, hF, hG, ite_true, ite_false]
      exact (Finset.prod_eq_zero (hG hi) (by
        simp [hi', vacuum_single, Finsupp.mem_support_iff.mp hi])).symm
    · simp [tensorCoeff, hF, hG]

open Classical in
theorem finiteSqueeze_inner (r : ι → ℝ) (F G : Finset ι) (hFG : F ⊆ G) :
    ⟪finiteSqueeze r F, finiteSqueeze r G⟫_ℂ =
      ∏ i ∈ G \ F, ((1 / Real.sqrt (Real.cosh (r i)) : ℝ) : ℂ) := by
  classical
  unfold finiteSqueeze
  rw [finiteTensor_extend F G hFG, finiteTensor_inner, ← Finset.prod_sdiff hFG]
  rw [Finset.prod_eq_one (s := F), mul_one]
  · exact Finset.prod_congr rfl fun i hi => by
      simp [(Finset.mem_sdiff.mp hi).2, squeezeVacuum_vacuum_inner]
  · intro i hi
    simp [hi, inner_self_eq_norm_sq_to_K, squeezeVacuum_norm]

private theorem overlap_eq_exp (r : ℝ) :
    1 / Real.sqrt (Real.cosh r) = Real.exp (-(Real.log (Real.cosh r) / 2)) := by
  rw [Real.exp_neg, Real.exp_half, Real.exp_log (Real.cosh_pos r), one_div]

open Classical in
theorem finiteSqueeze_sub_norm_sq_le (r : ι → ℝ) (F G : Finset ι) (hFG : F ⊆ G) :
    ‖finiteSqueeze r F - finiteSqueeze r G‖ ^ 2 ≤ (1 / 2) * ∑ i ∈ G \ F, (r i) ^ 2 := by
  classical
  rw [@norm_sub_sq ℂ, finiteSqueeze_inner r F G hFG, finiteSqueeze_norm, finiteSqueeze_norm]
  simp_rw [overlap_eq_exp, ← Complex.ofReal_prod, ← Real.exp_sum]
  change 1 ^ 2 - 2 * Real.exp (∑ i ∈ G \ F, -(Real.log (Real.cosh (r i)) / 2)) + 1 ^ 2 ≤ _
  let S := ∑ i ∈ G \ F, (r i) ^ 2
  have hl (i : ι) : Real.log (Real.cosh (r i)) ≤ (r i) ^ 2 / 2 :=
    (Real.log_le_iff_le_exp (Real.cosh_pos _)).mpr (Real.cosh_le_exp_half_sq _)
  have he : Real.exp (-(S / 4)) ≤ Real.exp (∑ i ∈ G \ F, -(Real.log (Real.cosh (r i)) / 2)) := by
    apply Real.exp_monotone
    rw [show -(S / 4) = ∑ i ∈ G \ F, -((r i) ^ 2 / 4) by
      simp [S, Finset.sum_neg_distrib, Finset.sum_div]]
    exact Finset.sum_le_sum fun i _ => by linarith [hl i]
  linarith [Real.one_sub_le_exp_neg (S / 4)]

theorem finiteSqueeze_cauchy (r : ι → ℝ) (hr : Summable (fun i => (r i) ^ 2)) :
    Cauchy (map (finiteSqueeze r) atTop) := by
  classical
  change CauchySeq (finiteSqueeze r)
  refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
  have he : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨F₀, hF₀⟩ := Metric.cauchySeq_iff.mp hr.hasSum.cauchySeq _ he
  refine ⟨F₀, fun F hF G hG => ?_⟩
  have step (A B : Finset ι) (hA : F₀ ⊆ A) (hAB : A ⊆ B) :
      dist (finiteSqueeze r A) (finiteSqueeze r B) < ε / 2 := by
    have ht := hF₀ B (hA.trans hAB) A hA
    rw [Real.dist_eq, ← Finset.sum_sdiff hAB] at ht
    have htail : ∑ i ∈ B \ A, (r i) ^ 2 < ε ^ 2 / 2 := by
      rw [add_sub_cancel_right] at ht
      exact (le_abs_self _).trans_lt ht
    have hn := finiteSqueeze_sub_norm_sq_le r A B hAB
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (finiteSqueeze r A - finiteSqueeze r B)]
  have h₁ := step F (F ∪ G) hF Finset.subset_union_left
  have h₂ := step G (F ∪ G) hG Finset.subset_union_right
  have ht := dist_triangle (finiteSqueeze r F) (finiteSqueeze r (F ∪ G)) (finiteSqueeze r G)
  rw [dist_comm (finiteSqueeze r (F ∪ G))] at ht
  linarith

/-- Norm limit over finite subsets of the index type. -/
def infiniteSqueeze (r : ι → ℝ) (_hr : Summable (fun i => (r i) ^ 2)) : BosonFock ι :=
  limUnder atTop (finiteSqueeze r)

theorem finiteSqueeze_tendsto (r : ι → ℝ) (hr : Summable (fun i => (r i) ^ 2)) :
    Tendsto (finiteSqueeze r) atTop (𝓝 (infiniteSqueeze r hr)) :=
  CauchySeq.tendsto_limUnder (finiteSqueeze_cauchy r hr)

theorem infiniteSqueeze_norm (r : ι → ℝ) (hr : Summable (fun i => (r i) ^ 2)) :
    ‖infiniteSqueeze r hr‖ = 1 := by
  apply tendsto_nhds_unique (finiteSqueeze_tendsto r hr).norm
  simpa only [finiteSqueeze_norm] using
    (tendsto_const_nhds : Tendsto (fun _ : Finset ι => (1 : ℝ)) atTop (𝓝 1))

private theorem oneExponential_apply (w : ℂ) (n : ℕ) :
    fockExponential singleModeBasis w (Finsupp.single () n) =
      w ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ) := by
  rw [fockExponential_apply]
  by_cases h : n = 0
  · simp [h]
  · simp [Finsupp.support_single () h]

private theorem finiteTensor_exponential_inner (b : HilbertBasis ι ℂ H)
    (F : Finset ι) (v : ι → BosonFock Unit) (w : H) :
    ⟪finiteTensor F v, fockExponential b w⟫_ℂ =
      ∏ i ∈ F, ⟪v i, fockExponential singleModeBasis (b.repr w i)⟫_ℂ := by
  rw [← finiteTensor_inner, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro α
  change (fockExponential b w α) * conj (tensorCoeff F v α) =
    tensorCoeff F (fun i => fockExponential singleModeBasis (b.repr w i)) α *
      conj (tensorCoeff F v α)
  classical
  by_cases h : α.support ⊆ F
  · congr 1
    rw [fockExponential_apply, tensorCoeff, ite_eq_left h]
    simp only [oneExponential_apply]
    exact Finsupp.prod_of_support_subset α h
      (fun i n => (b.repr w i) ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ)) (by simp)
  · simp [tensorCoeff, h]

private theorem inner_on_support (b : HilbertBasis ι ℂ H) (F : Finset ι) (z w : H)
    (hz : ∀ i ∉ F, b.repr z i = 0) :
    ⟪z, w⟫_ℂ = ∑ i ∈ F, ⟪b.repr z i, b.repr w i⟫_ℂ := by
  classical
  rw [← b.repr.inner_map_map, lp.inner_eq_tsum]
  exact tsum_eq_sum fun i hi => by simp [hz i hi]

private theorem finiteTensor_weyl (b : HilbertBasis ι ℂ H) (F : Finset ι)
    (v : ι → BosonFock Unit) (z : H) (hz : ∀ i ∉ F, b.repr z i = 0) :
    fockWeyl b z (finiteTensor F v) =
      finiteTensor F (fun i => fockWeyl singleModeBasis (b.repr z i) (v i)) := by
  let K := Submodule.span ℂ (Set.range (fockExponential b))
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
  let d := fockWeyl b z (finiteTensor F v) -
    finiteTensor F (fun i => fockWeyl singleModeBasis (b.repr z i) (v i))
  change ⟪d, d⟫_ℂ = 0
  have closed : IsClosed {u : BosonFock ι | ⟪d, u⟫_ℂ = 0} :=
    isClosed_eq (innerSL ℂ d).continuous continuous_const
  have hspan : ∀ u ∈ K, ⟪d, u⟫_ℂ = 0 := by
    change ∀ u ∈ K, (innerSL ℂ d) u = (0 : BosonFock ι →L[ℂ] ℂ) u
    apply LinearMap.eqOn_span (f := (innerSL ℂ d).toLinearMap)
      (g := (0 : BosonFock ι →L[ℂ] ℂ).toLinearMap)
    rintro _ ⟨w, rfl⟩
    change ⟪d, fockExponential b w⟫_ℂ = 0
    have hfac (u t : ℂ) (x : BosonFock Unit) :
        ⟪fockWeyl singleModeBasis u x, fockExponential singleModeBasis t⟫_ℂ =
        exp (-(‖u‖ : ℂ) ^ 2 / 2 + ⟪u, t⟫_ℂ) *
          ⟪x, fockExponential singleModeBasis (-u + t)⟫_ℂ := by
      rw [LinearIsometryEquiv.inner_map_eq_flip, fockWeyl_symm, fockWeyl_exponential,
        inner_smul_right, norm_neg, inner_neg_left, sub_neg_eq_add]
    have hn : (‖z‖ : ℂ) ^ 2 = ∑ i ∈ F, (‖b.repr z i‖ : ℂ) ^ 2 := by
      calc
        _ = ⟪z, z⟫_ℂ := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z).symm
        _ = ∑ i ∈ F, ⟪b.repr z i, b.repr z i⟫_ℂ := inner_on_support b F z z hz
        _ = _ := Finset.sum_congr rfl fun i _ => inner_self_eq_norm_sq_to_K (b.repr z i)
    simp only [d, inner_sub_left, sub_eq_zero, LinearIsometryEquiv.inner_map_eq_flip (fockWeyl b z),
      fockWeyl_symm, fockWeyl_exponential, inner_smul_right, norm_neg, inner_neg_left, sub_neg_eq_add,
      finiteTensor_exponential_inner, hfac, hn, inner_on_support b F z w hz]
    simp only [map_add, map_neg, lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply,
      Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_add_distrib]
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  have htotal : ∀ u : BosonFock ι, ⟪d, u⟫_ℂ = 0 :=
    (fockExponential_dense_span b).induction hspan closed
  exact htotal d

private def covarianceTerm (r : ℝ) (z : ℂ) : ℝ :=
  Real.exp (2 * r) * z.re ^ 2 + Real.exp (-2 * r) * z.im ^ 2

private theorem finiteSqueeze_weyl (b : HilbertBasis ι ℂ H) (r : ι → ℝ)
    (F : Finset ι) (z : H) (hz : ∀ i ∉ F, b.repr z i = 0) :
    ⟪finiteSqueeze r F, fockWeyl b z (finiteSqueeze r F)⟫_ℂ =
      exp (-((∑ i ∈ F, covarianceTerm (r i) (b.repr z i) : ℝ) : ℂ) / 2) := by
  rw [finiteSqueeze, finiteTensor_weyl b F _ z hz, finiteTensor_inner]
  simp only [squeezeVacuum_weyl_inner, ← Complex.exp_sum, covarianceTerm,
    Complex.ofReal_sum]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]

private theorem covariance_summable (b : HilbertBasis ι ℂ H) (z : H) (r : ι → ℝ)
    (hr : Summable (fun i => (r i) ^ 2)) :
    Summable (fun i => covarianceTerm (r i) (b.repr z i)) := by
  let M := ∑' i, (r i) ^ 2
  have hM : 0 ≤ M := tsum_nonneg fun i => sq_nonneg (r i)
  have hrM (i : ι) : |r i| ≤ Real.sqrt M := by
    rw [← sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _), sq_abs, Real.sq_sqrt hM]
    simpa using hr.sum_le_tsum ({i} : Finset ι) (fun j _ => sq_nonneg (r j))
  have hz := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp (b.repr z).property
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hz
  refine Summable.of_nonneg_of_le (fun i => by unfold covarianceTerm; positivity) (fun i => ?_)
    (hz.mul_left (Real.exp (2 * Real.sqrt M)))
  have h₁ := (Real.exp_monotone (show 2 * r i ≤ 2 * Real.sqrt M by
    linarith [(le_abs_self (r i)).trans (hrM i)]))
  have h₂ := (Real.exp_monotone (show -2 * r i ≤ 2 * Real.sqrt M by
    linarith [(neg_le_abs (r i)).trans (hrM i)]))
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [covarianceTerm, pow_two, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right h₁ (mul_self_nonneg _))
    (mul_le_mul_of_nonneg_right h₂ (mul_self_nonneg _))

private theorem projection_repr (b : HilbertBasis ι ℂ H) (z : H) (F : Finset ι) (i : ι) :
    b.repr (∑ j ∈ F, b.repr z j • b j) i =
      @ite ℂ (i ∈ F) (Classical.propDecidable _) (b.repr z i) 0 := by
  classical
  simp only [map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, b.repr_self, lp.single_apply, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq]

theorem infiniteSqueeze_weyl_inner (b : HilbertBasis ι ℂ H) (r : ι → ℝ)
    (hr : Summable (fun i => (r i) ^ 2)) (z : H) :
    ⟪infiniteSqueeze r hr, fockWeyl b z (infiniteSqueeze r hr)⟫_ℂ =
      exp (-((∑' i, (Real.exp (2 * r i) * (b.repr z i).re ^ 2 +
        Real.exp (-2 * r i) * (b.repr z i).im ^ 2) : ℝ) : ℂ) / 2) := by
  classical
  let zF (F : Finset ι) : H := ∑ i ∈ F, b.repr z i • b i
  let ψ := infiniteSqueeze r hr
  have hp : Tendsto zF atTop (𝓝 z) := b.hasSum_repr z
  have hs : Tendsto (finiteSqueeze r) atTop (𝓝 ψ) := finiteSqueeze_tendsto r hr
  have hw : Tendsto (fun F => fockWeyl b (zF F) (finiteSqueeze r F)) atTop
      (𝓝 (fockWeyl b z ψ)) := by
    have h := ((fockWeyl_strongContinuous b ψ).tendsto z).comp hp
    have hd : Tendsto (fun F => fockWeyl b (zF F) (finiteSqueeze r F - ψ)) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [LinearIsometryEquiv.norm_map, sub_self, norm_zero] using
        (hs.sub (tendsto_const_nhds (x := ψ))).norm
    convert hd.add h using 1
    · funext F
      dsimp [Function.comp_def]
      rw [map_sub, sub_add_cancel]
    · simp
  have hl := hs.inner hw (𝕜 := ℂ)
  have hcov := (covariance_summable b z r hr).hasSum
  have he := ((hcov.ofReal.neg.div_const (2 : ℂ)).cexp)
  apply tendsto_nhds_unique hl
  refine he.congr fun F => ?_
  rw [finiteSqueeze_weyl b r F (zF F) (fun i hi => by
    dsimp only [zF]
    rw [projection_repr, ite_eq_right hi])]
  congr 3
  apply congrArg Complex.ofReal
  exact Finset.sum_congr rfl fun i hi => by
    dsimp only [zF]
    rw [projection_repr, ite_eq_left hi]

end D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeInfinite
