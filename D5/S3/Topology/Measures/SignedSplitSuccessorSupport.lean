/- GID: D5/S3/Topology/Measures/SignedSplitSuccessor
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedSplitSuccessor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dynamic signed split geometry, scheduled mass separation and every-choice convergence -/

import D5.S3.Topology.Measures.NormPreservingLifts
import D5.S3.Topology.Measures.NormPreservingLiftExistence
import D5.S3.Topology.Measures.PositiveClopenMass
import D5.S3.Topology.Measures.SignedSplitReferenceConvergence
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Category.Profinite.Product
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Ordered signed split successors

Finite tests are fixed before the index threshold is chosen. Equality of
signed base projections and exact preservation of total variation mass are
used separately: a finite-coordinate projection may cancel opposite masses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Topology.Measures.SignedSplitSuccessor

universe u v w

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {L : Type v} [TopologicalSpace L] [T2Space L]
  [MeasurableSpace L] [BorelSpace L]

/-- Compact separation works on the actual carrier, including an empty one. -/
private lemma exists_finite_clopen_support {Γ : Type*}
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    {A : Set K} (hA : IsClopen A) :
    ∃ D : Finset Γ, ∀ x y, (∀ c ∈ D, coord c x = coord c y) → (x ∈ A ↔ y ∈ A) := by
  classical
  let c : K → (Γ → Bool) := fun x i => coord i x
  have hc : Continuous c := continuous_pi (fun i => (coord i).continuous)
  let e : K ≃ₜ Set.range c := (hc.isClosedEmbedding hsep).isEmbedding.toHomeomorph
  have hC : IsCompact (Set.range c) := isCompact_range hc
  let U : Set (Set.range c) := e.symm ⁻¹' A
  obtain ⟨J, V, _, hU⟩ := Profinite.exists_isClopen_of_cofiltered
    (Profinite.indexCone hC) (Profinite.indexCone_isLimit hC)
    (show IsClopen U from hA.preimage e.symm.continuous)
  refine ⟨Opposite.unop J, ?_⟩
  intro x y hxy
  have hpi : Profinite.IndexFunctor.π_app (Set.range c) (· ∈ Opposite.unop J) (e x) =
      Profinite.IndexFunctor.π_app (Set.range c) (· ∈ Opposite.unop J) (e y) := by
    apply Subtype.ext
    funext i
    exact hxy i.val i.property
  have hmem : e x ∈ U ↔ e y ∈ U := by
    rw [hU]
    exact iff_of_eq (congrArg (fun z => z ∈ V) hpi)
  simpa only [U, mem_preimage, e.symm_apply_apply] using hmem

lemma eventually_clopen_fibre {Γ I : Type*} (l : Filter I)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (p : K → L) (V : I → Set L)
    (hE : ∀ c, ∀ᶠ n in l, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    {A : Set K} (hA : IsClopen A) :
    ∀ᶠ n in l, ∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ A ↔ y ∈ A) := by
  obtain ⟨D, hD⟩ := exists_finite_clopen_support coord hsep hA
  have he : ∀ᶠ n in l, ∀ c ∈ D, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y :=
    (Filter.eventually_all_finset D).mpr (fun c _ => hE c)
  filter_upwards [he] with n hn
  intro x y hx hy hxy
  exact hD x y (fun c hc => hn c hc x y hx hy hxy)

omit [CompactSpace K] [T2Space L] in
lemma support_null (p : K → L) (hp : Continuous p)
    (s : SignedMeasure K) (nu : SignedMeasure L)
    (hmap : s.map p = nu) (hmass : s.totalVariation univ = nu.totalVariation univ)
    {V : Set L} (hV : IsClopen V) (hnull : nu.totalVariation Vᶜ = 0) :
    s.totalVariation (p ⁻¹' V)ᶜ = 0 := by
  have h := NormPreservingLifts.totalVariation_map_of_mass s p hp.measurable
    (by rw [hmap, hmass])
  have hn : s.totalVariation.map p Vᶜ = 0 := by
    rw [← h, hmap]
    exact hnull
  simpa only [Measure.map_apply hp.measurable hV.isClosed.measurableSet.compl,
    preimage_compl] using hn

private lemma finite_map_eq {F : Type w} [TopologicalSpace F] [DiscreteTopology F]
    [MeasurableSpace F] [BorelSpace F]
    (p : K → L) (hp : Continuous p) {V : Set L} (hV : IsClopen V)
    (s t : SignedMeasure K) (hmap : s.map p = t.map p)
    (hs : s.totalVariation (p ⁻¹' V)ᶜ = 0)
    (ht : t.totalVariation (p ⁻¹' V)ᶜ = 0)
    (f : K → F) (hf : Continuous f)
    (hE : ∀ x y, p x ∈ V → p y ∈ V → p x = p y → f x = f y) :
    s.map f = t.map f := by
  ext B hB
  rw [VectorMeasure.map_apply s hf.measurable hB,
    VectorMeasure.map_apply t hf.measurable hB]
  apply NormPreservingLifts.apply_eq_of_supported_clopen p hp hV s t hmap hs ht
  · exact (isClopen_discrete B).preimage hf
  · intro x y hx hy hxy
    simp only [mem_preimage, hE x y hx hy hxy]

private lemma positive_finite_map_eq {F : Type w}
    [TopologicalSpace F] [DiscreteTopology F] [MeasurableSpace F] [BorelSpace F]
    (p : K → L) (hp : Continuous p) {V : Set L} (hV : IsClopen V)
    (s t : SignedMeasure K) (nu : SignedMeasure L)
    (hsmap : s.map p = nu) (htmap : t.map p = nu)
    (hsmass : s.totalVariation univ = nu.totalVariation univ)
    (htmass : t.totalVariation univ = nu.totalVariation univ)
    (hnull : nu.totalVariation Vᶜ = 0)
    (f : K → F) (hf : Continuous f)
    (hE : ∀ x y, p x ∈ V → p y ∈ V → p x = p y → f x = f y) :
    s.totalVariation.map f = t.totalVariation.map f := by
  have hsbase := NormPreservingLifts.totalVariation_map_of_mass s p hp.measurable
    (by rw [hsmap, hsmass])
  have htbase := NormPreservingLifts.totalVariation_map_of_mass t p hp.measurable
    (by rw [htmap, htmass])
  have hbase : s.totalVariation.map p = t.totalVariation.map p := by
    rw [← hsbase, ← htbase, hsmap, htmap]
  have hposmap : s.totalVariation.toSignedMeasure.map p =
      t.totalVariation.toSignedMeasure.map p := by
    ext B hB
    rw [VectorMeasure.map_apply _ hp.measurable hB,
      VectorMeasure.map_apply _ hp.measurable hB,
      Measure.toSignedMeasure_apply_measurable (hp.measurable hB),
      Measure.toSignedMeasure_apply_measurable (hp.measurable hB)]
    change (s.totalVariation (p ⁻¹' B)).toReal =
      (t.totalVariation (p ⁻¹' B)).toReal
    rw [← Measure.map_apply hp.measurable hB,
      ← Measure.map_apply hp.measurable hB, hbase]
  have hsnull := support_null p hp s nu hsmap hsmass hV hnull
  have htnull := support_null p hp t nu htmap htmass hV hnull
  have heq := finite_map_eq p hp hV s.totalVariation.toSignedMeasure
    t.totalVariation.toSignedMeasure hposmap
    (by simpa only [SignedMeasure.totalVariation_eq_variation,
      Measure.variation_toSignedMeasure] using hsnull)
    (by simpa only [SignedMeasure.totalVariation_eq_variation,
      Measure.variation_toSignedMeasure] using htnull) f hf hE
  ext B hB
  have hval := congrArg (fun r : SignedMeasure F => r B) heq
  rw [VectorMeasure.map_apply _ hf.measurable hB,
    VectorMeasure.map_apply _ hf.measurable hB,
    Measure.toSignedMeasure_apply_measurable (hf.measurable hB),
    Measure.toSignedMeasure_apply_measurable (hf.measurable hB)] at hval
  rw [Measure.map_apply hf.measurable hB, Measure.map_apply hf.measurable hB]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hval

private lemma tendsto_clopen_apply {I : Type*} (l : Filter I)
    (s : I → SignedMeasure K) (mu : SignedMeasure K)
    (href : Tendsto (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
      l (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual))
    {A : Set K} (hA : IsClopen A) :
    Tendsto (fun n => s n A) l (𝓝 (mu A)) := by
  let f : C(K, ℝ) := (BoundedContinuousFunction.indicator A hA).toContinuousMap
  have heval (r : SignedMeasure K) :
      NormPreservingLifts.signedFunctional r f = r A := by
    have : IsFiniteMeasure r.variation := by
      rw [← SignedMeasure.totalVariation_eq_variation]
      infer_instance
    change (∫ᵛ x, A.indicator (fun _ : K => (1 : ℝ)) x ∂•r) = r A
    simpa using (VectorMeasure.integral_indicator_const
      (μ := r) (B := ContinuousLinearMap.lsmul ℝ ℝ) (1 : ℝ) hA.isClosed.measurableSet)
  have h := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp href) f
  change Tendsto (fun n => NormPreservingLifts.signedFunctional (s n) f) l
    (𝓝 (NormPreservingLifts.signedFunctional mu f)) at h
  simpa only [heval] using h

/-- Old whole-support coordinate constancy and a signed reference limit give
uniform total-variation control of every lift's fixed finite signed marginal.
The positive variation marginal agrees separately with that of the reference.
The finite coordinate type may be empty. -/
theorem eventually_uniform_finite_marginal {I : Type*} (l : Filter I)
    {C : Type w} [Fintype C]
    (p : K → L) (hp : Continuous p)
    (V : I → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : I → SignedMeasure L) (s : I → SignedMeasure K) (mu : SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (coord : C → C(K, Bool))
    (hE : ∀ c, ∀ᶠ n in l,
      ∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (href : Tendsto (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
      l (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ n in l, ∀ t : SignedMeasure K,
      t.map p = nu n → t.totalVariation univ = (nu n).totalVariation univ →
      ((SignedMeasure.totalVariation
        (t.map (fun x c => coord c x) - mu.map (fun x c => coord c x))).real
        univ < eps) ∧
      t.totalVariation.map (fun x c => coord c x) =
        (s n).totalVariation.map (fun x c => coord c x) := by
  classical
  let f : K → (C → Bool) := fun x c => coord c x
  have hf : Continuous f := continuous_pi (fun c => (coord c).continuous)
  have hEc : ∀ᶠ n in l, ∀ c, ∀ x y, p x ∈ V n → p y ∈ V n →
      p x = p y → coord c x = coord c y := eventually_all.mpr hE
  have hE' : ∀ᶠ n in l, ∀ x y, p x ∈ V n → p y ∈ V n →
      p x = p y → f x = f y := by
    filter_upwards [hEc] with n hn
    intro x y hx hy hxy
    funext c
    exact hn c x y hx hy hxy
  have hatom (b : C → Bool) : Tendsto
      (fun n => |(s n).map f {b} - mu.map f {b}|) l (𝓝 0) := by
    have hcl : IsClopen (f ⁻¹' {b}) := (isClopen_discrete {b}).preimage hf
    have ht := tendsto_clopen_apply l s mu href hcl
    have heq (r : SignedMeasure K) : r.map f {b} = r (f ⁻¹' {b}) :=
      VectorMeasure.map_apply r hf.measurable (measurableSet_singleton b)
    simpa only [heq, sub_self, abs_zero] using (ht.sub_const (mu (f ⁻¹' {b}))).abs
  have hsum : Tendsto
      (fun n => ∑ b : C → Bool, |(s n).map f {b} - mu.map f {b}|) l (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun b _ => hatom b)
  have hmass (r : SignedMeasure (C → Bool)) :
      r.totalVariation.real univ = ∑ b : C → Bool, |r {b}| := by
    have hs : (∑ b : C → Bool, r.totalVariation.real {b}) =
        r.totalVariation.real univ := by
      simpa only [Finset.coe_univ] using
        (sum_measureReal_singleton (μ := r.totalVariation) (Finset.univ : Finset (C → Bool)))
    rw [← hs]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Measure.real, SignedMeasure.totalVariation_eq_variation,
      VectorMeasure.variation_apply_singleton, toReal_enorm, Real.norm_eq_abs]
  intro eps heps
  have hsmall : ∀ᶠ n in l,
      ∑ b : C → Bool, |(s n).map f {b} - mu.map f {b}| < eps :=
    hsum.eventually (gt_mem_nhds heps)
  filter_upwards [hsmall, hE'] with n hn hEn
  intro t htmap htmass
  have htNull := support_null p hp t (nu n) htmap htmass (hV n) (hnull n)
  have hsNull := support_null p hp (s n) (nu n) (hsmap n) (hsmass n) (hV n) (hnull n)
  have heq := finite_map_eq p hp (hV n) t (s n)
    (htmap.trans (hsmap n).symm) htNull hsNull f hf hEn
  refine ⟨?_, positive_finite_map_eq p hp (hV n) t (s n) (nu n)
    htmap (hsmap n) htmass (hsmass n) (hnull n) f hf hEn⟩
  change (SignedMeasure.totalVariation (t.map f - mu.map f)).real univ < eps
  rw [heq, hmass]
  simpa only [_root_.sub_apply] using hn

/-- Once the finite coordinate family is fixed, an arbitrary infinite
reservoir supplies a larger auxiliary index satisfying its whole-fibre and
uniform signed marginal tests and the small-support variation test together.
In particular the reservoir can be either of the original fixed parity pools. -/
theorem exists_auxiliary_index {C : Type w} [Fintype C]
    (S : Set ℕ) (hS : S.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : ℕ → SignedMeasure L) (s : ℕ → SignedMeasure K) (mu : SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (coord : C → C(K, Bool))
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 S,
      ∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (href : Tendsto (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
      (atTop ⊓ 𝓟 S) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual))
    (v : Measure K) [IsFiniteMeasure v]
    (hdis : Pairwise (fun n m => Disjoint (p ⁻¹' V n) (p ⁻¹' V m)))
    (M : ℕ) (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    ∃ m ∈ S, M < m ∧ v.real (p ⁻¹' V m) < delta ∧
      (∀ c x y, p x ∈ V m → p y ∈ V m → p x = p y → coord c x = coord c y) ∧
      ∀ t : SignedMeasure K, t.map p = nu m →
        t.totalVariation univ = (nu m).totalVariation univ →
        ((SignedMeasure.totalVariation
          (t.map (fun x c => coord c x) - mu.map (fun x c => coord c x))).real
          univ < eps) ∧
        t.totalVariation.map (fun x c => coord c x) =
          (s m).totalVariation.map (fun x c => coord c x) := by
  have hfinite := eventually_uniform_finite_marginal (atTop ⊓ 𝓟 S) p hp V hV
    nu s mu hsmap hsmass hnull coord hE href eps heps
  have hfinite' := eventually_inf_principal.mp hfinite
  have hEc := eventually_inf_principal.mp (eventually_all.mpr hE)
  have hsum : Summable (fun n => v.real (p ⁻¹' V n)) :=
    summable_measure_toReal (fun n => hp.measurable (hV n).isClosed.measurableSet) hdis
  have hsmall : ∀ᶠ n : ℕ in atTop, v.real (p ⁻¹' V n) < delta :=
    hsum.tendsto_atTop_zero.eventually (gt_mem_nhds hdelta)
  have hall : ∀ᶠ n : ℕ in atTop, n ∈ S → M < n ∧ v.real (p ⁻¹' V n) < delta ∧
      (∀ c x y, p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y) ∧
      ∀ t : SignedMeasure K, t.map p = nu n →
        t.totalVariation univ = (nu n).totalVariation univ →
        ((SignedMeasure.totalVariation
          (t.map (fun x c => coord c x) - mu.map (fun x c => coord c x))).real
          univ < eps) ∧
        t.totalVariation.map (fun x c => coord c x) =
          (s n).totalVariation.map (fun x c => coord c x) := by
    filter_upwards [hfinite', hEc, hsmall, eventually_gt_atTop M] with n hn hEn hv hMn
    intro hnS
    exact ⟨hMn, hv, hEn hnS, hn hnS⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  obtain ⟨m, hmS, hmN⟩ := (hS.sdiff (Set.finite_Iio N)).nonempty
  exact ⟨m, hmS, hN m (le_of_not_gt hmN) hmS⟩

private lemma positive_clopen_eq
    (p : K → L) (hp : Continuous p) {V : Set L} (hV : IsClopen V)
    (s t : SignedMeasure K) (nu : SignedMeasure L)
    (hsmap : s.map p = nu) (htmap : t.map p = nu)
    (hsmass : s.totalVariation univ = nu.totalVariation univ)
    (htmass : t.totalVariation univ = nu.totalVariation univ)
    (hnull : nu.totalVariation Vᶜ = 0) {A : Set K} (hA : IsClopen A)
    (hE : ∀ x y, p x ∈ V → p y ∈ V → p x = p y → (x ∈ A ↔ y ∈ A)) :
    s.totalVariation.real A = t.totalVariation.real A := by
  classical
  have hf : Continuous A.boolIndicator := continuous_boolIndicator_iff_isClopen A |>.mpr hA
  have hfibre : ∀ x y, p x ∈ V → p y ∈ V → p x = p y →
      A.boolIndicator x = A.boolIndicator y := by
    intro x y hx hy hxy
    have h := hE x y hx hy hxy
    by_cases hxA : x ∈ A
    · have hyA := h.mp hxA
      simp only [Set.boolIndicator, ite_eq_left hxA, ite_eq_left hyA]
    · have hyA : y ∉ A := fun hya => hxA (h.mpr hya)
      simp only [Set.boolIndicator, ite_eq_right hxA, ite_eq_right hyA]
  have heq := positive_finite_map_eq p hp hV s t nu hsmap htmap hsmass htmass
    hnull A.boolIndicator hf hfibre
  have hval := congrArg (fun m : Measure Bool => m {true}) heq
  rw [Measure.map_apply hf.measurable (measurableSet_singleton true),
    Measure.map_apply hf.measurable (measurableSet_singleton true),
    Set.preimage_boolIndicator_true] at hval
  exact congrArg ENNReal.toReal hval

/-- For a fixed finite family of clopen exclusions, the independent positive
variation reference limit gives a single larger target index controlling
every norm-preserving signed lift on every exclusion. The finite family can
be empty. No convergence of signed measures is substituted for this limit. -/
theorem exists_target_index {F : Type w} [Fintype F]
    (S : Set ℕ) (hS : S.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : ℕ → SignedMeasure L) (s : ℕ → SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (A : F → Set K) (hA : ∀ j, IsClopen (A j))
    (hE : ∀ j, ∀ᶠ n in atTop ⊓ 𝓟 S,
      ∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ A j ↔ y ∈ A j))
    (v : Measure K) (href : ∀ j, Tendsto (fun n => (s n).totalVariation.real (A j))
      (atTop ⊓ 𝓟 S) (𝓝 (v.real (A j))))
    (b : F → ℝ) (hmargin : ∀ j, v.real (A j) < b j) (M : ℕ) :
    ∃ n ∈ S, M < n ∧
      (∀ j x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ A j ↔ y ∈ A j)) ∧
      ∀ j, ∀ t : SignedMeasure K,
      t.map p = nu n → t.totalVariation univ = (nu n).totalVariation univ →
      t.totalVariation.real (A j) < b j := by
  have hsmall : ∀ j, ∀ᶠ n in atTop ⊓ 𝓟 S,
      (s n).totalVariation.real (A j) < b j :=
    fun j => (href j).eventually (gt_mem_nhds (hmargin j))
  have hsmall' := eventually_inf_principal.mp (eventually_all.mpr hsmall)
  have hE' := eventually_inf_principal.mp (eventually_all.mpr hE)
  have hall : ∀ᶠ n : ℕ in atTop, n ∈ S → M < n ∧
      (∀ j x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ A j ↔ y ∈ A j)) ∧
      ∀ j, ∀ t : SignedMeasure K,
      t.map p = nu n → t.totalVariation univ = (nu n).totalVariation univ →
      t.totalVariation.real (A j) < b j := by
    filter_upwards [hsmall', hE', eventually_gt_atTop M] with n hn hEn hMn
    intro hnS
    refine ⟨hMn, hEn hnS, ?_⟩
    intro j t htmap htmass
    rw [positive_clopen_eq p hp (hV n) t (s n) (nu n) htmap (hsmap n)
      htmass (hsmass n) (hnull n) (hA j) (hEn hnS j)]
    exact hn hnS j
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  obtain ⟨n, hnS, hnN⟩ := (hS.sdiff (Set.finite_Iio N)).nonempty
  exact ⟨n, hnS, hN n (le_of_not_gt hnN) hnS⟩

/-- A positive target piece remains uniformly large for every signed lift
after deleting a clopen exclusion of variation mass at most one sixteenth. -/
theorem exists_signed_target_piece [CompactSpace L] [ZeroDimensionalSpace L]
    (p : K → L) (hp : Continuous p) (nu : SignedMeasure L)
    (hposreg : Measure.Regular nu.toJordanDecomposition.posPart)
    (hnegreg : Measure.Regular nu.toJordanDecomposition.negPart)
    {V : Set L} (hV : IsClopen V) (hnull : nu.totalVariation Vᶜ = 0)
    (hpos : (1 : ℝ) / 2 ≤ nu.toJordanDecomposition.posPart.real univ)
    {R : Set K} (hR : IsClopen R)
    (hsmall : ∀ t : SignedMeasure K, t.map p = nu →
      t.totalVariation univ = nu.totalVariation univ →
      t.totalVariation.real R ≤ (1 : ℝ) / 16) :
    ∃ H : Set K, IsClopen H ∧ H ⊆ p ⁻¹' V \ R ∧
      (∃ B : Set L, IsClopen B ∧ B ⊆ V ∧ H = p ⁻¹' B \ R) ∧
      ∀ t : SignedMeasure K, t.map p = nu →
        t.totalVariation univ = nu.totalVariation univ →
        (13 : ℝ) / 48 < t H ∧ (1 : ℝ) / 6 < t H := by
  have hposnull : nu.toJordanDecomposition.posPart Vᶜ = 0 := by
    rw [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] at hnull
    exact hnull.1
  have hposV : nu.toJordanDecomposition.posPart.real V =
      nu.toJordanDecomposition.posPart.real univ := by
    have h := measure_inter_conull (μ := nu.toJordanDecomposition.posPart)
      (s := univ) hposnull
    simpa only [univ_inter, Measure.real] using congrArg ENNReal.toReal h
  have hthird : (1 : ℝ) / 3 < nu.toJordanDecomposition.posPart.real V := by
    rw [hposV]
    linarith only [hpos]
  obtain ⟨B, hB, hBV, hBmass⟩ :=
    PositiveClopenMass.exists_isClopen_subset_lt_apply_of_lt_posPart
      nu hposreg hnegreg hV.isOpen hthird
  let A : Set K := p ⁻¹' B
  have hA : IsClopen A := hB.preimage hp
  refine ⟨A \ R, hA.diff hR, ?_, ⟨B, hB, hBV, rfl⟩, ?_⟩
  · intro x hx
    exact ⟨hBV hx.1, hx.2⟩
  · intro t htmap htmass
    have htA : t A = nu B := by
      rw [← htmap, VectorMeasure.map_apply _ hp.measurable hB.isClosed.measurableSet]
    have hsplit : t (A \ R) = t A - t (A ∩ R) := by
      have h := VectorMeasure.of_sdiff (v := t)
        (hA.inter hR).isClosed.measurableSet hA.isClosed.measurableSet inter_subset_left
      have heq : A \ (A ∩ R) = A \ R := by
        ext x
        simp only [Set.mem_sdiff, mem_inter_iff]
        tauto
      simpa only [heq] using h
    have hbound : t (A ∩ R) ≤ (1 : ℝ) / 16 := by
      calc
        t (A ∩ R) ≤ |t (A ∩ R)| := le_abs_self _
        _ ≤ t.totalVariation.real (A ∩ R) := by
          simpa only [Real.norm_eq_abs] using t.norm_le_totalVariation (A ∩ R)
        _ ≤ t.totalVariation.real R := measureReal_mono inter_subset_right
          (measure_ne_top _ _)
        _ ≤ (1 : ℝ) / 16 := hsmall t htmap htmass
    rw [hsplit, htA]
    constructor <;> linarith only [hBmass, hbound]


private lemma finite_column_budget {Rows : Type*} (code : Rows → ℕ)
    (hcode : Function.Injective code) (A : Finset Rows) (q : ℕ) :
    (∑ r ∈ A, ∑ j ∈ Finset.range q,
      (1 : ℝ) / 64 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j) ≤ 1 / 16 := by
  classical
  have hrow : (∑ r ∈ A, (1 / 2 : ℝ) ^ code r) ≤ 2 := by
    rw [← Finset.sum_image (fun r _ s _ hrs => hcode hrs)]
    simpa only [hasSum_geometric_two.tsum_eq] using
      summable_geometric_two.sum_le_tsum (A.image code)
        (fun j _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j)
  have hcol : (∑ j ∈ Finset.range q, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    simpa only [hasSum_geometric_two.tsum_eq] using
      summable_geometric_two.sum_le_tsum (Finset.range q)
        (fun j _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j)
  have hrow0 : 0 ≤ ∑ r ∈ A, (1 / 2 : ℝ) ^ code r :=
    Finset.sum_nonneg (fun r _ => pow_nonneg (by norm_num) _)
  have hcol0 : 0 ≤ ∑ j ∈ Finset.range q, (1 / 2 : ℝ) ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (by norm_num) _)
  have hprod := mul_le_mul hrow hcol hcol0 (by norm_num : (0 : ℝ) ≤ 2)
  have heq : (∑ r ∈ A, ∑ j ∈ Finset.range q,
      (1 : ℝ) / 64 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j) =
      1 / 64 * (∑ r ∈ A, (1 / 2 : ℝ) ^ code r) *
        (∑ j ∈ Finset.range q, (1 / 2 : ℝ) ^ j) := by
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [heq]
  nlinarith only [hprod]

/-- The target part of one ordered column is chosen after its finite earlier
exclusions. Positive-variation convergence controls every signed lift on their
union; its mass budget is derived from the distinct row codes. -/
theorem exists_target_after_finite_exclusion [CompactSpace L] [ZeroDimensionalSpace L]
    {Rows : Type*} (code : Rows → ℕ) (hcode : Function.Injective code)
    (A : Finset Rows) (q : ℕ)
    (S : Set ℕ) (hS : S.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : ℕ → SignedMeasure L) (s : ℕ → SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (hposreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.posPart)
    (hnegreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.negPart)
    (hpos : ∀ n, (1 : ℝ) / 2 ≤ (nu n).toJordanDecomposition.posPart.real univ)
    (W : Rows → ℕ → Set K) (hW : ∀ r j, IsClopen (W r j))
    (hE : ∀ r ∈ A, ∀ j < q, ∀ᶠ n in atTop ⊓ 𝓟 S,
      ∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ W r j ↔ y ∈ W r j))
    (v : Measure K)
    (href : ∀ r ∈ A, ∀ j < q, Tendsto (fun n => (s n).totalVariation.real (W r j))
      (atTop ⊓ 𝓟 S) (𝓝 (v.real (W r j))))
    (hsmall : ∀ r ∈ A, ∀ j < q,
      v.real (W r j) < (1 : ℝ) / 64 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j)
    (M : ℕ) :
    ∃ n ∈ S, M < n ∧ ∃ H : Set K, IsClopen H ∧
      H ⊆ p ⁻¹' V n \ (⋃ r ∈ A, ⋃ j ∈ Finset.range q, W r j) ∧
      (∃ B : Set L, IsClopen B ∧ B ⊆ V n ∧
        H = p ⁻¹' B \ (⋃ r ∈ A, ⋃ j ∈ Finset.range q, W r j)) ∧
      (∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ H ↔ y ∈ H)) ∧
      ∀ t : SignedMeasure K, t.map p = nu n →
        t.totalVariation univ = (nu n).totalVariation univ →
        (13 : ℝ) / 48 < t H ∧ (1 : ℝ) / 6 < t H := by
  classical
  let F := {r // r ∈ A} × Fin q
  let tests : F → Set K := fun f => W f.1.1 f.2
  let budget : F → ℝ := fun f =>
    (1 : ℝ) / 64 * (1 / 2 : ℝ) ^ code f.1.1 * (1 / 2 : ℝ) ^ (f.2 : ℕ)
  obtain ⟨n, hnS, hnM, hnE, hn⟩ := exists_target_index S hS p hp V hV nu s hsmap hsmass
    hnull tests (fun f => hW _ _) (fun f => hE _ f.1.2 _ f.2.2) v
    (fun f => href _ f.1.2 _ f.2.2) budget (fun f => hsmall _ f.1.2 _ f.2.2) M
  let R : Set K := ⋃ r ∈ A, ⋃ j ∈ Finset.range q, W r j
  have hR : IsClopen R :=
    isClopen_biUnion_finset (fun r _ => isClopen_biUnion_finset (fun j _ => hW r j))
  have hRsmall : ∀ t : SignedMeasure K, t.map p = nu n →
      t.totalVariation univ = (nu n).totalVariation univ →
      t.totalVariation.real R ≤ (1 : ℝ) / 16 := by
    intro t htmap htmass
    calc
      t.totalVariation.real R ≤
          ∑ r ∈ A, t.totalVariation.real (⋃ j ∈ Finset.range q, W r j) :=
        measureReal_biUnion_finset_le A _
      _ ≤ ∑ r ∈ A, ∑ j ∈ Finset.range q, t.totalVariation.real (W r j) :=
        Finset.sum_le_sum (fun r _ => measureReal_biUnion_finset_le (Finset.range q) _)
      _ ≤ ∑ r ∈ A, ∑ j ∈ Finset.range q,
          (1 : ℝ) / 64 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro j hj
        exact (hn (⟨r, hr⟩, ⟨j, Finset.mem_range.mp hj⟩) t htmap htmass).le
      _ ≤ 1 / 16 := finite_column_budget code hcode A q
  have hRE : ∀ x y, p x ∈ V n → p y ∈ V n → p x = p y → (x ∈ R ↔ y ∈ R) := by
    intro x y hx hy hxy
    simp only [R, mem_iUnion]
    constructor
    · rintro ⟨r, hr, j, hj, hxW⟩
      exact ⟨r, hr, j, hj,
        (hnE (⟨r, hr⟩, ⟨j, Finset.mem_range.mp hj⟩) x y hx hy hxy).mp hxW⟩
    · rintro ⟨r, hr, j, hj, hyW⟩
      exact ⟨r, hr, j, hj,
        (hnE (⟨r, hr⟩, ⟨j, Finset.mem_range.mp hj⟩) x y hx hy hxy).mpr hyW⟩
  obtain ⟨H, hH, hsub, hliteral, hlarge⟩ := exists_signed_target_piece p hp (nu n)
    (hposreg n) (hnegreg n) (hV n) (hnull n) (hpos n) hR hRsmall
  refine ⟨n, hnS, hnM, H, hH, hsub, hliteral, ?_, hlarge⟩
  obtain ⟨B, _, _, hB⟩ := hliteral
  intro x y hx hy hxy
  rw [hB]
  simp only [Set.mem_sdiff, mem_preimage, hxy, hRE x y hx hy hxy]

/-- The literal closed split inside the product with the new Boolean coordinate. -/
def splitCarrier (Y Z : Set K) : Set (K × Bool) :=
  {p | (p.1 ∈ Y ∧ p.2 = false) ∨ (p.1 ∈ Z ∧ p.2 = true)}

/-- The finite even prefix at the column where an auxiliary support is chosen. -/
def evenPrefix (H : ℕ → Set K) (q : ℕ) : Set K :=
  ⋃ s ∈ Finset.range (q + 1), if s % 2 = 0 then H s else ∅

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
lemma evenPrefix_mono (H : ℕ → Set K) : Monotone (evenPrefix H) := by
  intro q s hqs x hx
  simp only [evenPrefix, mem_iUnion, Finset.mem_range] at hx ⊢
  obtain ⟨j, hj, hxH⟩ := hx
  exact ⟨j, by omega, hxH⟩

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
lemma evenPrefix_clopen (H : ℕ → Set K) (hH : ∀ q, IsClopen (H q))
    (q : ℕ) : IsClopen (evenPrefix H q) := by
  apply isClopen_biUnion_finset
  intro s hs
  split_ifs
  · exact hH s
  · exact isClopen_empty

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
private lemma closure_trace {S A V : Set K} (hA : IsClopen A) (hV : IsClopen V)
    (htrace : S ∩ V = A ∩ V) : closure S ∩ V = A ∩ V := by
  apply Subset.antisymm
  · have hsub : S ⊆ (A ∩ V) ∪ Vᶜ := by
      intro x hx
      by_cases hxV : x ∈ V
      · exact Or.inl (show x ∈ A ∩ V from htrace ▸ ⟨hx, hxV⟩)
      · exact Or.inr hxV
    have hcl := closure_minimal hsub ((hA.inter hV).isClosed.union hV.compl.isClosed)
    intro x hx
    rcases hcl hx.1 with h | h
    · exact h
    · exact (h hx.2).elim
  · intro x hx
    have hxS : x ∈ S ∩ V := htrace.symm ▸ hx
    exact ⟨subset_closure hxS.1, hxS.2⟩

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
private lemma ordered_union_trace {Rows : Type*} (code : Rows → ℕ)
    (H : ℕ → Set K) (W : Rows → ℕ → Set K)
    (havoid : ∀ r q s, code r < q → q < s → Disjoint (H s) (W r q))
    (r : Rows) (q : ℕ) (hq : code r < q) :
    (⋃ s : ℕ, ⋃ (_ : s % 2 = 0), H s) ∩ W r q = evenPrefix H q ∩ W r q := by
  ext x
  constructor
  · rintro ⟨hx, hxW⟩
    obtain ⟨s, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hs, hxH⟩ := mem_iUnion.mp hx
    have hsq : s ≤ q := by
      by_contra h
      exact (Set.disjoint_left.mp (havoid r q s hq (lt_of_not_ge h))) hxH hxW
    refine ⟨?_, hxW⟩
    simp only [evenPrefix, mem_iUnion, Finset.mem_range]
    exact ⟨s, by omega, by simpa only [ite_eq_left hs] using hxH⟩
  · rintro ⟨hx, hxW⟩
    simp only [evenPrefix, mem_iUnion, Finset.mem_range] at hx
    obtain ⟨s, hs, hxH⟩ := hx
    by_cases heven : s % 2 = 0
    · refine ⟨mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨heven, ?_⟩⟩, hxW⟩
      simpa only [ite_eq_left heven] using hxH
    · simpa only [ite_eq_right heven, mem_empty_iff_false] using hxH

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- Future columns avoid each earlier active auxiliary support. Closing the
even union therefore has its exact finite-prefix trace on that whole support.
Both closed sides and the genuine split are constructed; their boundary is
absent from every such support. No infinitude of the row type is required. -/
private lemma closed_split_auxiliary {Rows : Type*}
    (code : Rows → ℕ) (H : ℕ → Set K) (hH : ∀ q, IsClopen (H q))
    (W : Rows → ℕ → Set K) (hW : ∀ r q, IsClopen (W r q))
    (havoid : ∀ r q s, code r < q → q < s → Disjoint (H s) (W r q)) :
    ∃ Y Z : Set K, IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
      Z = closure (⋃ s : ℕ, ⋃ (_ : s % 2 = 0), H s) ∧ Y = closure Zᶜ ∧
      IsClosed (splitCarrier Y Z) ∧
      Function.Surjective (fun x : splitCarrier Y Z => x.1.1) ∧
      ∀ r q, code r < q →
        Z ∩ W r q = evenPrefix H q ∩ W r q ∧
        Y ∩ W r q = (evenPrefix H q)ᶜ ∩ W r q ∧
        Disjoint (Y ∩ Z) (W r q) ∧
        ∀ x : splitCarrier Y Z, x.1.1 ∈ W r q →
          (x.1.2 = true ↔ x.1.1 ∈ evenPrefix H q) := by
  classical
  let Z : Set K := closure (⋃ s : ℕ, ⋃ (_ : s % 2 = 0), H s)
  let Y : Set K := closure Zᶜ
  have hZ : IsClosed Z := isClosed_closure
  have hY : IsClosed Y := isClosed_closure
  have hcover : Y ∪ Z = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ Z
    · exact Or.inr hx
    · exact Or.inl (subset_closure hx)
  have hsplit : IsClosed (splitCarrier Y Z) := by
    have hfalse : IsClosed ({false} : Set Bool) := isClosed_singleton
    have htrue : IsClosed ({true} : Set Bool) := isClosed_singleton
    exact (hY.preimage continuous_fst |>.inter (hfalse.preimage continuous_snd)).union
      (hZ.preimage continuous_fst |>.inter (htrue.preimage continuous_snd))
  have hsurj : Function.Surjective (fun x : splitCarrier Y Z => x.1.1) := by
    intro x
    have hx : x ∈ Y ∪ Z := by rw [hcover]; exact mem_univ x
    rcases hx with hx | hx
    · exact ⟨⟨(x, false), Or.inl ⟨hx, rfl⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inr ⟨hx, rfl⟩⟩, rfl⟩
  refine ⟨Y, Z, hY, hZ, hcover, rfl, rfl, hsplit, hsurj, ?_⟩
  intro r q hq
  have hU := evenPrefix_clopen H hH q
  have htrace : Z ∩ W r q = evenPrefix H q ∩ W r q :=
    closure_trace hU (hW r q) (ordered_union_trace code H W havoid r q hq)
  have hmemZ (x : K) (hx : x ∈ W r q) : x ∈ Z ↔ x ∈ evenPrefix H q := by
    have := Set.ext_iff.mp htrace x
    simpa only [mem_inter_iff, hx, and_true] using this
  have hcompl : Zᶜ ∩ W r q = (evenPrefix H q)ᶜ ∩ W r q := by
    ext x
    by_cases hx : x ∈ W r q
    · simp only [mem_inter_iff, mem_compl_iff, hx, and_true, hmemZ x hx]
    · simp only [mem_inter_iff, hx, and_false]
  have htraceY : Y ∩ W r q = (evenPrefix H q)ᶜ ∩ W r q :=
    closure_trace hU.compl (hW r q) hcompl
  have hmemY (x : K) (hx : x ∈ W r q) : x ∈ Y ↔ x ∉ evenPrefix H q := by
    have := Set.ext_iff.mp htraceY x
    simpa only [mem_inter_iff, mem_compl_iff, hx, and_true] using this
  refine ⟨htrace, htraceY, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxW
    exact (hmemY x hxW).mp hx.1 ((hmemZ x hxW).mp hx.2)
  · intro x hx
    rcases x.property with h | h
    · have hn := (hmemY x.1.1 hx).mp h.1
      simp only [h.2, Bool.false_eq_true, hn]
    · have hy := (hmemZ x.1.1 hx).mp h.1
      simp only [h.2, hy]

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- The ordered auxiliary traces and the pairwise disjoint target supports
are realized by the same closed split, including target column zero. -/
theorem exists_closed_split_of_ordered_exclusion {Rows : Type*}
    (code : Rows → ℕ) (H : ℕ → Set K) (hH : ∀ q, IsClopen (H q))
    (W : Rows → ℕ → Set K) (hW : ∀ r q, IsClopen (W r q))
    (havoid : ∀ r q s, code r < q → q < s → Disjoint (H s) (W r q))
    (T : ℕ → Set K) (hT : ∀ q, IsClopen (T q))
    (hdis : Pairwise (fun q s => Disjoint (T q) (T s))) (hHT : ∀ q, H q ⊆ T q) :
    ∃ Y Z : Set K, IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
      Z = closure (⋃ s : ℕ, ⋃ (_ : s % 2 = 0), H s) ∧ Y = closure Zᶜ ∧
      IsClosed (splitCarrier Y Z) ∧
      Function.Surjective (fun x : splitCarrier Y Z => x.1.1) ∧
      (∀ r q, code r < q →
        Z ∩ W r q = evenPrefix H q ∩ W r q ∧
        Y ∩ W r q = (evenPrefix H q)ᶜ ∩ W r q ∧
        Disjoint (Y ∩ Z) (W r q) ∧
        ∀ x : splitCarrier Y Z, x.1.1 ∈ W r q →
          (x.1.2 = true ↔ x.1.1 ∈ evenPrefix H q)) ∧
      (∀ q, Z ∩ T q = (if q % 2 = 0 then H q else ∅) ∧
        Disjoint (Y ∩ Z) (T q) ∧
        ∀ x : splitCarrier Y Z, x.1.1 ∈ T q →
          (x.1.2 = true ↔ q % 2 = 0 ∧ x.1.1 ∈ H q)) := by
  classical
  let code' : Rows ⊕ ℕ → ℕ := Sum.elim code (fun _ => 0)
  let W' : Rows ⊕ ℕ → ℕ → Set K := fun r k =>
    match r with
    | .inl r => W r k
    | .inr j => if k = j + 1 then T j else ∅
  have hW' : ∀ r k, IsClopen (W' r k) := by
    intro r k
    cases r with
    | inl r => exact hW r k
    | inr j =>
      dsimp only [W']
      split_ifs
      · exact hT j
      · exact isClopen_empty
  have havoid' : ∀ r k s, code' r < k → k < s → Disjoint (H s) (W' r k) := by
    intro r k s hr hs
    cases r with
    | inl r => exact havoid r k s hr hs
    | inr j =>
      dsimp only [W']
      split_ifs with hkj
      · have hsj : s ≠ j := by omega
        exact (hdis hsj).mono_left (hHT s)
      · exact disjoint_empty _
  obtain ⟨Y, Z, hY, hZ, hcover, hZdef, hYdef, hsplit, hsurj, htrace⟩ :=
    closed_split_auxiliary code' H hH W' hW' havoid'
  refine ⟨Y, Z, hY, hZ, hcover, hZdef, hYdef, hsplit, hsurj, ?_, ?_⟩
  · intro r q hq
    exact htrace (.inl r) q hq
  · intro q
    have ht := htrace (.inr q) (q + 1) (by simp [code'])
    have ht' :
        Z ∩ T q = evenPrefix H (q + 1) ∩ T q ∧
        Y ∩ T q = (evenPrefix H (q + 1))ᶜ ∩ T q ∧
        Disjoint (Y ∩ Z) (T q) ∧
        ∀ x : splitCarrier Y Z, x.1.1 ∈ T q →
          (x.1.2 = true ↔ x.1.1 ∈ evenPrefix H (q + 1)) := by
      simpa only [W', ite_eq_left rfl] using ht
    have hpre : evenPrefix H (q + 1) ∩ T q =
        (if q % 2 = 0 then H q else ∅) := by
      ext x
      constructor
      · rintro ⟨hx, hxT⟩
        simp only [evenPrefix, mem_iUnion, Finset.mem_range] at hx
        obtain ⟨s, hs, hxH⟩ := hx
        by_cases heven : s % 2 = 0
        · simp only [ite_eq_left heven] at hxH
          have hsq : s = q := by
            by_contra hsq
            exact (Set.disjoint_left.mp (hdis hsq)) (hHT s hxH) hxT
          subst s
          simpa only [ite_eq_left heven] using hxH
        · simpa only [ite_eq_right heven, mem_empty_iff_false] using hxH
      · intro hx
        by_cases heven : q % 2 = 0
        · simp only [ite_eq_left heven] at hx
          refine ⟨?_, hHT q hx⟩
          simp only [evenPrefix, mem_iUnion, Finset.mem_range]
          exact ⟨q, by omega, by simpa only [ite_eq_left heven] using hx⟩
        · simpa only [ite_eq_right heven, mem_empty_iff_false] using hx
    refine ⟨ht'.1.trans hpre, ht'.2.2.1, ?_⟩
    intro x hx
    rw [ht'.2.2.2 x hx]
    have hmem := Set.ext_iff.mp hpre x.1.1
    by_cases heven : q % 2 = 0
    · simpa [hx, heven] using hmem
    · simpa [hx, heven] using hmem


end D5.S3.Topology.Measures.SignedSplitSuccessor
