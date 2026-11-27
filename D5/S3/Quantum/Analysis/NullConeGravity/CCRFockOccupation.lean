/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-summable finite occupations, the coherent Gram formula and totality. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
The coherent exponential vectors in occupation coordinates have an exponential Gram kernel.
Finite-mode power series give totality, and analytic continuation along complex lines gives
totality for real subspaces with dense complex span.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped BigOperators ComplexConjugate InnerProductSpace Topology

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation

abbrev Occupation (I : Type*) := I →₀ ℕ

abbrev BosonFock (I : Type*) := lp (fun _ : Occupation I => ℂ) 2

variable {I : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def factorialTerm (x : I → ℂ) (α : Occupation I) : ℂ :=
  α.prod fun i n => x i ^ n / (n.factorial : ℂ)

private theorem expSeries (x : ℂ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x) := by
  simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp x

set_option maxHeartbeats 500000 in
-- Reindexing finite products elaborates across two finite-type instances.
private theorem finite_expSeries {J : Type*} [Fintype J] (x : J → ℂ) :
    HasSum (fun n : J → ℕ => ∏ i, x i ^ n i / ((n i).factorial : ℂ))
      (Complex.exp (∑ i, x i)) := by
  classical
  revert x
  refine Fintype.induction_empty_option (P := fun J [Fintype J] =>
    ∀ x : J → ℂ, HasSum (fun n : J → ℕ => ∏ i, x i ^ n i / ((n i).factorial : ℂ))
      (Complex.exp (∑ i, x i))) ?_ ?_ ?_ J
  · intro A B _ e ih x
    let : Fintype A := Fintype.ofEquiv B e.symm
    let en : (A → ℕ) ≃ (B → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
    have he : ∑ i : A, x (e i) = ∑ i : B, x i :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    apply en.hasSum_iff.mp
    rw [← he]
    refine (ih (x ∘ e)).congr_fun fun n => ?_
    change (∏ i : B, x i ^ en n i / ((en n i).factorial : ℂ)) = _
    symm
    apply Fintype.prod_equiv e
    intro i
    have hn : en n (e i) = n i := by simp [en]
    simp only [Function.comp_apply, hn]
  · intro x; simp
  · intro J _ ih x
    rw [Fintype.sum_option, Complex.exp_add]
    let e := Equiv.piOptionEquivProd (β := fun _ : Option J => ℕ)
    apply e.symm.hasSum_iff.mp
    change HasSum (fun p : ℕ × (J → ℕ) =>
      ∏ i, x i ^ e.symm p i / ((e.symm p i).factorial : ℂ)) _
    simp only [Fintype.prod_option]
    have one (a : ℂ) : Summable (fun n : ℕ => ‖a ^ n / (n.factorial : ℂ)‖) := by
      convert (NormedSpace.expSeries_div_hasSum_exp ‖a‖).summable using 1
      ext n
      simp [norm_pow]
    have rest : Summable (fun n : J → ℕ => ‖∏ i, x (some i) ^ n i / ((n i).factorial : ℂ)‖) := by
      convert ((ih (fun i => (‖x (some i)‖ : ℂ))).map Complex.reCLM
        Complex.reCLM.continuous).summable using 1
      ext n
      simp only [Function.comp_apply, Complex.reCLM_apply, ← Complex.ofReal_natCast,
        ← Complex.ofReal_pow, ← Complex.ofReal_div, ← Complex.ofReal_prod, Complex.ofReal_re,
        Complex.norm_prod, norm_div, norm_pow, Complex.norm_real, Real.norm_natCast]
    let f (n : ℕ) : ℂ := x none ^ n / (n.factorial : ℂ)
    let g (n : J → ℕ) : ℂ := ∏ i, x (some i) ^ n i / ((n i).factorial : ℂ)
    have hf : HasSum f (Complex.exp (x none)) := expSeries (x none)
    have hg : HasSum g (Complex.exp (∑ i, x (some i))) := ih (fun i => x (some i))
    have hmul : Summable (fun p : ℕ × (J → ℕ) => f p.1 * g p.2) :=
      summable_mul_of_summable_norm (f := f) (g := g) (one (x none)) rest
    have htarget : HasSum (fun p : ℕ × (J → ℕ) => f p.1 * g p.2)
        (Complex.exp (x none) * Complex.exp (∑ i, x (some i))) :=
      HasSum.mul (f := f) (g := g) hf hg hmul
    exact htarget.congr_fun fun _ => rfl

private def supportedOccupation (s : Finset I) :
    (s → ℕ) ≃ {α : Occupation I // α.support ⊆ s} where
  toFun n := ⟨(Finsupp.equivFunOnFinite.symm n).embDomain (Function.Embedding.subtype (· ∈ s)),
    fun i hi => by
      rw [Finsupp.support_embDomain] at hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.property⟩
  invFun α i := α.1 i
  left_inv n := by
    ext i
    change (Finsupp.equivFunOnFinite.symm n).embDomain
      (Function.Embedding.subtype (· ∈ s)) ((Function.Embedding.subtype (· ∈ s)) i) = _
    rw [Finsupp.embDomain_apply_self]
    rfl
  right_inv α := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ s
    · simpa using Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∈ s))
          (Finsupp.equivFunOnFinite.symm (fun j : s => α.1 j)) ⟨i, hi⟩
    · rw [Finsupp.embDomain_of_notMem_range]
      · exact (Finsupp.notMem_support_iff.mp (fun h => hi (α.2 h))).symm
      · rintro ⟨j, rfl⟩
        exact hi j.property

private theorem prod_supportedOccupation {M : Type*} [CommMonoid M]
    (s : Finset I) (n : s → ℕ) (f : I → ℕ → M) (h₀ : ∀ i, f i 0 = 1) :
    (supportedOccupation s n).1.prod f = ∏ i : s, f i (n i) := by
  classical
  change ((Finsupp.equivFunOnFinite.symm n).embDomain _).prod f = _
  rw [Finsupp.prod_embDomain, Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _]
  · simp
  · exact fun i _ => h₀ i

private theorem supported_expSeries (s : Finset I) (x : I → ℂ) :
    HasSum (fun α : {α : Occupation I // α.support ⊆ s} => factorialTerm x α)
      (Complex.exp (∑ i ∈ s, x i)) := by
  apply (supportedOccupation s).hasSum_iff.mp
  classical
  rw [← Finset.sum_attach s x]
  refine (finite_expSeries (fun i : s => x i)).congr_fun fun n => ?_
  exact prod_supportedOccupation s n (fun i k => x i ^ k / (k.factorial : ℂ))
    (fun _ => by simp)

private theorem norm_factorialTerm (x : I → ℂ) (α : Occupation I) :
    ‖factorialTerm x α‖ = (factorialTerm (fun i => (‖x i‖ : ℂ)) α).re := by
  simp only [factorialTerm, Finsupp.prod, Complex.norm_prod, norm_div, norm_pow,
    ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    ← Complex.ofReal_prod, Complex.ofReal_re, Complex.norm_real, Real.norm_natCast]

private theorem occupation_expSeries (x : I → ℂ) (hx : Summable (fun i => ‖x i‖)) :
    HasSum (factorialTerm x) (Complex.exp (∑' i, x i)) := by
  classical
  have hn : Summable (fun α => ‖factorialTerm x α‖) := by
    apply summable_of_sum_le (c := Real.exp (∑' i, ‖x i‖)) (fun _ => norm_nonneg _)
    intro t
    let s := t.biUnion Finsupp.support
    let e (α : t) : {α : Occupation I // α.support ⊆ s} :=
      ⟨α, fun i hi => Finset.mem_biUnion.mpr ⟨α, α.property, hi⟩⟩
    have hs : HasSum (fun α : {α : Occupation I // α.support ⊆ s} => ‖factorialTerm x α‖)
        (Real.exp (∑ i ∈ s, ‖x i‖)) := by
      convert (supported_expSeries s (fun i => (‖x i‖ : ℂ))).map Complex.reCLM
        Complex.reCLM.continuous using 1
      · ext α
        exact norm_factorialTerm x α
      · simp [← Complex.ofReal_sum, ← Complex.ofReal_exp]
    calc
      ∑ α ∈ t, ‖factorialTerm x α‖ =
          ∑ α ∈ t.attach.image e, ‖factorialTerm x α‖ := by
            have he : Function.Injective e := fun _ _ h =>
              Subtype.ext (congrArg (fun a : {α : Occupation I // α.support ⊆ s} => a.1) h)
            rw [Finset.sum_image (g := e) (fun _ _ _ _ h => he h)]
            exact (Finset.sum_attach _ _).symm
      _ ≤ Real.exp (∑ i ∈ s, ‖x i‖) :=
        hs.tsum_eq ▸ hs.summable.sum_le_tsum _ (fun _ _ => norm_nonneg _)
      _ ≤ _ := Real.exp_le_exp.mpr (hx.sum_le_tsum _ (fun _ _ => norm_nonneg _))
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter (Finset I)))
    (f := fun (s : Finset I) (α : Occupation I) =>
      if α.support ⊆ s then factorialTerm x α else 0)
    (g := factorialTerm x) hn (fun α => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop α.support] with s hs
      simp [hs])) (Eventually.of_forall fun s α => by
        split <;> simp)
  have hc : Tendsto (fun s : Finset I => ∑' α : Occupation I,
      if α.support ⊆ s then factorialTerm x α else 0)
      atTop (𝓝 (Complex.exp (∑' i, x i))) := by
    apply (Complex.continuous_exp.continuousAt.tendsto.comp hx.of_norm.hasSum).congr
    intro s
    change Complex.exp (∑ i ∈ s, x i) = _
    rw [← (supported_expSeries s x).tsum_eq]
    refine (tsum_subtype {α : Occupation I | α.support ⊆ s} (factorialTerm x)).trans ?_
    congr 1
    funext α
    by_cases h : α.support ⊆ s <;> simp [h]
  rw [← tendsto_nhds_unique ht hc]
  exact hn.of_norm.hasSum

private def coefficient (x : I → ℂ) (α : Occupation I) : ℂ :=
  α.prod fun i n => x i ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ)

private theorem coefficient_mul (x y : I → ℂ) (α : Occupation I) :
    conj (coefficient x α) * coefficient y α =
      factorialTerm (fun i => conj (x i) * y i) α := by
  simp only [coefficient, factorialTerm, Finsupp.prod, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hs : (Real.sqrt ((α i).factorial : ℝ) : ℂ) ^ 2 = ((α i).factorial : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  rw [map_div₀, map_pow, Complex.conj_ofReal, mul_pow, div_mul_div_comm, ← pow_two, hs]

private theorem coefficient_memℓp (x : lp (fun _ : I => ℂ) 2) :
    Memℓp (coefficient x) 2 := by
  have hs := lp.summable_mul (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two) x x
  have hx : Summable (fun i => ‖conj (x i) * x i‖) := by simpa [norm_mul] using hs
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine ((occupation_expSeries _ hx).map Complex.reCLM Complex.reCLM.continuous).summable.congr ?_
  intro α
  rw [Function.comp_apply, Complex.reCLM_apply, ← coefficient_mul, RCLike.conj_mul]
  exact Complex.ofReal_pow _ 2 ▸ Complex.ofReal_re _

/-- The vector supported at the zero occupation, with value one. -/
def fockVacuum (I : Type*) : BosonFock I :=
  by classical exact lp.single 2 0 1

/-- The coherent exponential vector in the occupation coordinates of a Hilbert basis. -/
def fockExponential (b : HilbertBasis I ℂ H) (z : H) : BosonFock I :=
  ⟨coefficient (b.repr z), coefficient_memℓp (b.repr z)⟩

theorem fockExponential_apply (b : HilbertBasis I ℂ H) (z : H) (α : Occupation I) :
    fockExponential b z α =
      ∏ i ∈ α.support, (b.repr z i) ^ (α i) / (Real.sqrt ((α i).factorial : ℝ) : ℂ) :=
  rfl

theorem fockVacuum_norm (I : Type*) : ‖fockVacuum I‖ = 1 := by
  classical
  rw [fockVacuum, lp.norm_single (by norm_num)]
  simp

private theorem coefficient_zero (α : Occupation I) :
    coefficient (fun _ => 0) α = @ite ℂ (α = 0) (Classical.propDecidable _) 1 0 := by
  classical
  split_ifs with h
  · simp [h, coefficient]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun he => h (Finsupp.support_eq_empty.mp he))
    exact Finset.prod_eq_zero hi (by simp [Finsupp.mem_support_iff.mp hi])

theorem fockExponential_zero (b : HilbertBasis I ℂ H) :
    fockExponential b 0 = fockVacuum I := by
  classical
  apply lp.ext
  funext α
  change coefficient (b.repr 0) α = (fockVacuum I) α
  simp only [map_zero, lp.coeFn_zero, fockVacuum, lp.single_apply, Pi.single_apply]
  change coefficient (fun _ => 0) α = _
  by_cases h : α = 0 <;> simpa [h] using coefficient_zero α

theorem fockExponential_inner (b : HilbertBasis I ℂ H) (z w : H) :
    ⟪fockExponential b z, fockExponential b w⟫_ℂ = Complex.exp ⟪z, w⟫_ℂ := by
  rw [← b.repr.inner_map_map z w, lp.inner_eq_tsum (b.repr z), lp.inner_eq_tsum]
  simp only [fockExponential, RCLike.inner_apply, mul_comm _ (conj _), coefficient_mul]
  apply (occupation_expSeries _ ?_).tsum_eq
  simpa [norm_mul] using lp.summable_mul (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two) (b.repr z) (b.repr w)

theorem fockExponential_norm_sq (b : HilbertBasis I ℂ H) (z : H) :
    ‖fockExponential b z‖ ^ 2 = Real.exp (‖z‖ ^ 2) := by
  have h := fockExponential_inner b z z
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  change ((‖fockExponential b z‖ : ℂ) ^ 2).re = (Complex.exp ((‖z‖ : ℂ) ^ 2)).re at hr
  simpa only [← Complex.ofReal_pow, Complex.exp_ofReal_re, Complex.ofReal_re] using hr

theorem fockExponential_continuous (b : HilbertBasis I ℂ H) :
    Continuous (fockExponential b) := by
  have h (z w : H) :
      ‖fockExponential b z - fockExponential b w‖ ^ 2 =
        Real.exp (‖z‖ ^ 2) - 2 * (Complex.exp ⟪z, w⟫_ℂ).re + Real.exp (‖w‖ ^ 2) := by
    rw [norm_sub_sq (𝕜 := ℂ), fockExponential_inner,
      fockExponential_norm_sq, fockExponential_norm_sq]
    rfl
  rw [continuous_iff_continuousAt]
  intro w
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [dist_eq_norm]
  have hn : ContinuousAt (fun z => ‖fockExponential b z - fockExponential b w‖ ^ 2) w := by
    simp_rw [h]
    fun_prop
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hn.tendsto
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using ht

set_option maxHeartbeats 650000 in
-- The finite-mode induction includes absolute convergence and power-series coefficient extraction.
private theorem finite_monomial_unique {J : Type*} [Fintype J] :
    ∀ a : (J → ℕ) → ℂ,
      (∀ x : J → ℂ, Summable (fun n => ‖a n * ∏ i, x i ^ n i‖)) →
      (∀ x : J → ℂ, HasSum (fun n => a n * ∏ i, x i ^ n i) 0) →
      ∀ n, a n = 0 := by
  classical
  refine Fintype.induction_empty_option (P := fun J [Fintype J] =>
    ∀ a : (J → ℕ) → ℂ,
      (∀ x : J → ℂ, Summable (fun n => ‖a n * ∏ i, x i ^ n i‖)) →
      (∀ x : J → ℂ, HasSum (fun n => a n * ∏ i, x i ^ n i) 0) →
      ∀ n, a n = 0) ?_ ?_ ?_ J
  · intro A B _ e ih a ha hs n
    let : Fintype A := Fintype.ofEquiv B e.symm
    let en : (A → ℕ) ≃ (B → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
    have h (x : A → ℂ) (m : A → ℕ) :
        (∏ j : B, x (e.symm j) ^ en m j) = ∏ i : A, x i ^ m i := by
      symm
      apply Fintype.prod_equiv e
      intro i
      simp [en]
    rw [← en.apply_symm_apply n]
    apply ih (a ∘ en)
    · intro x
      have hx := en.summable_iff.mpr (ha (fun j => x (e.symm j)))
      change Summable (fun m : A → ℕ => ‖a (en m) * ∏ j : B, x (e.symm j) ^ en m j‖) at hx
      simpa only [Function.comp_apply, h] using hx
    · intro x
      have hx := en.hasSum_iff.mpr (hs (fun j => x (e.symm j)))
      change HasSum (fun m : A → ℕ => a (en m) * ∏ j : B, x (e.symm j) ^ en m j) 0 at hx
      simpa only [Function.comp_apply, h] using hx
  · intro a _ hs n
    have hz := (hs (fun _ => 0)).tsum_eq
    simp only [tsum_fintype, Fintype.sum_unique, Fintype.prod_empty, mul_one] at hz
    exact (congrArg a (Subsingleton.elim n _)).trans hz
  · intro J _ ih a ha hs n
    let e := Equiv.piOptionEquivProd (β := fun _ : Option J => ℕ)
    let c (m : ℕ) (k : J → ℕ) : ℂ := a (e.symm (m, k))
    let y (z : ℂ) (x : J → ℂ) : Option J → ℂ :=
      (Equiv.piOptionEquivProd (β := fun _ : Option J => ℂ)).symm (z, x)
    have h (z : ℂ) (x : J → ℂ) (p : ℕ × (J → ℕ)) :
        a (e.symm p) * (∏ i, y z x i ^ e.symm p i) =
          (c p.1 p.2 * ∏ i, x i ^ p.2 i) * z ^ p.1 := by
      rw [Fintype.prod_option]
      change c p.1 p.2 * (z ^ p.1 * ∏ i, x i ^ p.2 i) = _
      ring
    have habs (m : ℕ) (x : J → ℂ) :
        Summable (fun k => ‖c m k * ∏ i, x i ^ k i‖) := by
      have hh := (e.symm.summable_iff.mpr (ha (y 1 x))).comp_injective
        (i := fun k : J → ℕ => (m, k)) (fun _ _ he => congrArg Prod.snd he)
      change Summable (fun k => ‖a (e.symm (m, k)) * ∏ i, y 1 x i ^ e.symm (m, k) i‖) at hh
      simpa only [h, one_pow, mul_one] using hh
    have hzero (m : ℕ) (x : J → ℂ) :
        HasSum (fun k => c m k * ∏ i, x i ^ k i) 0 := by
      let series := FormalMultilinearSeries.ofScalars ℂ
        (fun m : ℕ => ∑' k : J → ℕ, c m k * ∏ i, x i ^ k i)
      have hf : HasFPowerSeriesAt (0 : ℂ → ℂ) series 0 := by
        apply hasFPowerSeriesAt_iff.mpr
        filter_upwards [] with z
        simp only [Pi.zero_apply, series, FormalMultilinearSeries.coeff_ofScalars,
          smul_eq_mul]
        have hh := e.symm.hasSum_iff.mpr (hs (y z x))
        have hp : HasSum (fun p : ℕ × (J → ℕ) =>
            (c p.1 p.2 * ∏ i, x i ^ p.2 i) * z ^ p.1) 0 := hh.congr_fun
              (fun p => (h z x p).symm)
        let g (k : ℕ) : ℂ := (∑' j : J → ℕ, c k j * ∏ i, x i ^ j i) * z ^ k
        have hfiber (k : ℕ) : HasSum (fun j : J → ℕ =>
            (c k j * ∏ i, x i ^ j i) * z ^ k) (g k) :=
          (habs k x).of_norm.hasSum.mul_right (z ^ k)
        refine (hp.prod_fiberwise (g := g) hfiber).congr_fun fun k => ?_
        exact mul_comm _ _
      have hz := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff m) hf.eq_zero
      have hm : (∑' k : J → ℕ, c m k * ∏ i, x i ^ k i) = 0 := by
        have h0 : (0 : FormalMultilinearSeries ℂ ℂ ℂ).coeff m = 0 := rfl
        simpa only [series, FormalMultilinearSeries.coeff_ofScalars, h0] using hz
      exact hm ▸ (habs m x).of_norm.hasSum
    have hc := ih (c (e n).1) (habs _) (hzero _) (e n).2
    simpa only [c, Prod.mk.eta, Equiv.symm_apply_apply] using hc

private theorem coefficient_zero_of_not_supported (x : I → ℂ) (s : Finset I)
    (hx : ∀ i ∉ s, x i = 0) (α : Occupation I) (hα : ¬ α.support ⊆ s) :
    coefficient x α = 0 := by
  obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hα
  exact Finset.prod_eq_zero hi (by simp [hx i hni, Finsupp.mem_support_iff.mp hi])

private theorem exponential_total (b : HilbertBasis I ℂ H) (v : BosonFock I)
    (hv : ∀ z, ⟪v, fockExponential b z⟫_ℂ = 0) : v = 0 := by
  classical
  apply lp.ext
  funext α
  let s := α.support
  let e := supportedOccupation s
  let d (n : s → ℕ) : ℂ :=
    ∏ i : s, ((Real.sqrt ((n i).factorial : ℝ) : ℂ)⁻¹)
  let a (n : s → ℕ) : ℂ := conj (v (e n).1) * d n
  let y (x : s → ℂ) : lp (fun _ : I => ℂ) 2 :=
    ∑ i ∈ s.attach, lp.single 2 (i : I) (x i)
  have hy (x : s → ℂ) (i : I) :
      y x i = if hi : i ∈ s then x ⟨i, hi⟩ else 0 := by
    simp only [y, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro j _ hj
        exact ite_eq_right (fun h => hj (Subtype.ext h.symm))
      · simp
    · apply Finset.sum_eq_zero
      intro j _
      have hj : i ≠ (j : I) := fun he => hi (he.symm ▸ j.property)
      simp [hj]
  have hprod (x : s → ℂ) (n : s → ℕ) :
      conj (v (e n).1) * coefficient (y x) (e n).1 = a n * ∏ i, x i ^ n i := by
    change _ * (e n).1.prod _ = _
    rw [prod_supportedOccupation s n _ (fun _ => by simp)]
    simp only [hy, dite_eq_left, Subtype.property, a, d, div_eq_mul_inv, Finset.prod_mul_distrib]
    ring
  have hsum (x : s → ℂ) :
      HasSum (fun n => a n * ∏ i, x i ^ n i) 0 := by
    have he := lp.hasSum_inner (𝕜 := ℂ) v (fockExponential b (b.repr.symm (y x)))
    rw [hv] at he
    have hcoef : HasSum (fun β : Occupation I => conj (v β) * coefficient (y x) β) 0 :=
      he.congr_fun (fun β => by
        simp only [RCLike.inner_apply, fockExponential, b.repr.apply_symm_apply, mul_comm])
    have hsupport : Function.support (fun β : Occupation I =>
        conj (v β) * coefficient (y x) β) ⊆ {β | β.support ⊆ s} := by
      intro β hβ
      by_contra hn
      exact hβ (mul_eq_zero_of_right _
        (coefficient_zero_of_not_supported (y x) s (fun i hi => by simp [hy, hi]) β hn))
    have hf := e.hasSum_iff.mpr (hasSum_subtype_iff_of_support_subset hsupport |>.mpr hcoef)
    exact hf.congr_fun (fun n => (hprod x n).symm)
  have habs (x : s → ℂ) : Summable (fun n => ‖a n * ∏ i, x i ^ n i‖) := by
    have hn := lp.summable_mul (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two)
      v (fockExponential b (b.repr.symm (y x)))
    refine (hn.comp_injective (i := fun n => (e n).1)
      (fun _ _ h => e.injective (Subtype.ext h))).congr ?_
    intro n
    rw [← hprod, norm_mul, Complex.norm_conj]
    simp only [fockExponential, b.repr.apply_symm_apply, Function.comp_apply]
  let n := e.symm ⟨α, Finset.Subset.rfl⟩
  have hn := finite_monomial_unique a habs hsum n
  have hd : d n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ =>
    inv_ne_zero (by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < ((n i).factorial : ℝ))).ne'))
  have ha := (mul_eq_zero.mp hn).resolve_right hd
  simpa only [n, e.apply_symm_apply, map_eq_zero, lp.coeFn_zero, Pi.zero_apply] using ha

theorem fockExponential_dense_span (b : HilbertBasis I ℂ H) :
    Dense (Submodule.span ℂ (Set.range (fockExponential b)) : Set (BosonFock I)) := by
  let K := Submodule.span ℂ (Set.range (fockExponential b))
  change Dense (K : Set (BosonFock I))
  rw [dense_iff_closure_eq, ← K.topologicalClosure_coe,
    ← Submodule.top_coe (R := ℂ), SetLike.coe_set_eq, K.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_bot]
  apply exponential_total b v
  intro z
  have hz : fockExponential b z ∈ K := Submodule.subset_span ⟨z, rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal hz hv

/-- Pairing with a coherent vector is entire along every affine complex line. -/
private theorem exponential_pairing_analytic (b : HilbertBasis I ℂ H) (v : BosonFock I)
    (x y : H) : AnalyticOnNhd ℂ (fun c : ℂ => ⟪v, fockExponential b (x + c • y)⟫_ℂ) univ := by
  classical
  apply (Complex.analyticOnNhd_iff_differentiableOn isOpen_univ).2
  apply Differentiable.differentiableOn
  intro z
  let R := ‖z‖ + 1
  let B := ‖x‖ + R * ‖y‖
  let C := Real.exp (B ^ 2 / 2)
  have hC : 0 < C := Real.exp_pos _
  let vFin (s : Finset (Occupation I)) : BosonFock I := ∑ α ∈ s, lp.single 2 α (v α)
  let f (s : Finset (Occupation I)) (c : ℂ) := ⟪vFin s, fockExponential b (x + c • y)⟫_ℂ
  have hf (s : Finset (Occupation I)) : Differentiable ℂ (f s) := by
    simp only [f, vFin, sum_inner, lp.inner_single_left, fockExponential_apply, RCLike.inner_apply]
    refine Differentiable.fun_sum fun α _ => Differentiable.mul ?_ (differentiable_const _)
    refine Differentiable.fun_finsetProd fun i _ => ?_
    have he (c : ℂ) : b.repr (x + c • y) i = b.repr x i + c * b.repr y i := by
      rw [map_add, map_smul]
      rfl
    simp_rw [he]
    fun_prop
  have hv : Tendsto vFin atTop (𝓝 v) := lp.hasSum_single ENNReal.ofNat_ne_top v
  have hU : TendstoUniformlyOn f (fun c => ⟪v, fockExponential b (x + c • y)⟫_ℂ)
      atTop (Metric.ball 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hv (ε / C) (div_pos hε hC)] with s hs c hc
    have hc' : ‖c‖ ≤ R := (mem_ball_zero_iff.mp hc).le
    have hB : ‖x + c • y‖ ≤ B := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      exact add_le_add_right (mul_le_mul_of_nonneg_right hc' (norm_nonneg y)) _
    have hnorm : ‖fockExponential b (x + c • y)‖ ≤ C := by
      have hsq : ‖fockExponential b (x + c • y)‖ ^ 2 ≤ C ^ 2 := by
        rw [fockExponential_norm_sq, show C ^ 2 = Real.exp (B ^ 2) by
          simp only [C, pow_two, ← Real.exp_add]
          congr 1
          ring]
        exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (norm_nonneg _) hB 2)
      nlinarith [norm_nonneg (fockExponential b (x + c • y))]
    change dist ⟪v, fockExponential b (x + c • y)⟫_ℂ
      ⟪vFin s, fockExponential b (x + c • y)⟫_ℂ < ε
    rw [dist_eq_norm, ← inner_sub_left]
    refine (norm_inner_le_norm _ _).trans_lt ?_
    calc
      ‖v - vFin s‖ * ‖fockExponential b (x + c • y)‖ ≤ ‖v - vFin s‖ * C :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ < ε := (lt_div_iff₀ hC).mp (by rwa [dist_eq_norm, norm_sub_rev] at hs)
  refine (hU.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun s => (hf s).differentiableOn) Metric.isOpen_ball).differentiableAt ?_
  exact Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by dsimp [R]; linarith))

private theorem entire_eq_zero_of_real (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (h : ∀ r : ℝ, f r = 0) : f = 0 := by
  have ht : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply (Complex.continuous_ofReal.continuousWithinAt (s := {0}ᶜ) (x := 0))
      |>.tendsto_nhdsWithin
    intro r hr
    simpa using hr
  have hfreq : ∃ᶠ c in 𝓝[≠] (0 : ℂ), f c = 0 :=
    ht.frequently <| (Eventually.of_forall h).frequently
  exact funext fun c => hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ 0) hfreq (mem_univ c)

private theorem complex_span_real_decomposition (E : Submodule ℝ H) {z : H}
    (hz : z ∈ Submodule.span ℂ (E : Set H)) :
    ∃ x ∈ E, ∃ y ∈ E, z = x + Complex.I • y := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨x, hx, 0, E.zero_mem, by simp⟩
  | zero => exact ⟨0, E.zero_mem, 0, E.zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihx
      obtain ⟨c, hc, d, hd, rfl⟩ := ihy
      exact ⟨a + c, E.add_mem ha hc, b + d, E.add_mem hb hd, by
        rw [smul_add]
        abel⟩
  | smul a x hx ih =>
      obtain ⟨r, hr, s, hs, rfl⟩ := ih
      refine ⟨a.re • r - a.im • s, E.sub_mem (E.smul_mem _ hr) (E.smul_mem _ hs),
        a.im • r + a.re • s, E.add_mem (E.smul_mem _ hr) (E.smul_mem _ hs), ?_⟩
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp only [← Complex.coe_smul, smul_add, smul_smul]
      conv_lhs => rw [← Complex.re_add_im a]
      rw [add_smul, add_mul, add_smul, mul_assoc, hI, mul_neg, mul_one, neg_smul]
      simp only [mul_comm Complex.I]
      abel

/-- A real subspace with dense complex span has total coherent exponential vectors. -/
theorem fockExponential_dense_span_of_dense_real (b : HilbertBasis I ℂ H) (E : Submodule ℝ H)
    (hE : Dense (Submodule.span ℂ (E : Set H) : Set H)) :
    Dense (Submodule.span ℂ (fockExponential b '' (E : Set H)) : Set (BosonFock I)) := by
  let K := Submodule.span ℂ (fockExponential b '' (E : Set H))
  change Dense (K : Set (BosonFock I))
  rw [dense_iff_closure_eq, ← K.topologicalClosure_coe,
    ← Submodule.top_coe (R := ℂ), SetLike.coe_set_eq, K.topologicalClosure_eq_top_iff]
  refine le_antisymm (fun v hv => ?_) bot_le
  have hzero (x : H) (hx : x ∈ E) : ⟪v, fockExponential b x⟫_ℂ = 0 := by
    have hm : fockExponential b x ∈ K := Submodule.subset_span ⟨x, hx, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal hm hv
  have hspan (z : H) (hz : z ∈ Submodule.span ℂ (E : Set H)) :
      ⟪v, fockExponential b z⟫_ℂ = 0 := by
    obtain ⟨x, hx, y, hy, rfl⟩ := complex_span_real_decomposition E hz
    have hline := entire_eq_zero_of_real _ (exponential_pairing_analytic b v x y)
      (fun r => hzero _ (by rw [Complex.coe_smul]; exact E.add_mem hx (E.smul_mem r hy)))
    exact congrFun hline Complex.I
  have hclosed : IsClosed {z : H | ⟪v, fockExponential b z⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner (fockExponential_continuous b)) continuous_const
  have hall (z : H) : ⟪v, fockExponential b z⟫_ℂ = 0 :=
    closure_minimal (fun w hw => hspan w hw) hclosed (hE z)
  simpa using exponential_total b v hall

end D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
