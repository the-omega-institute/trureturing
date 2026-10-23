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

private lemma eventually_clopen_fibre {Γ I : Type*} (l : Filter I)
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
private lemma support_null (p : K → L) (hp : Continuous p)
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
private lemma evenPrefix_mono (H : ℕ → Set K) : Monotone (evenPrefix H) := by
  intro q s hqs x hx
  simp only [evenPrefix, mem_iUnion, Finset.mem_range] at hx ⊢
  obtain ⟨j, hj, hxH⟩ := hx
  exact ⟨j, by omega, hxH⟩

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
private lemma evenPrefix_clopen (H : ℕ → Set K) (hH : ∀ q, IsClopen (H q))
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

private lemma apply_error_of_finite_marginal {C : Type*} [Fintype C]
    (f : K → (C → Bool)) (hf : Continuous f) (s t : SignedMeasure K)
    (eps : ℝ)
    (hsmall : (SignedMeasure.totalVariation (s.map f - t.map f)).real univ < eps)
    (A : Set K)
    (hA : ∀ x y, f x = f y → (x ∈ A ↔ y ∈ A)) : |s A - t A| < eps := by
  classical
  let D : Set (C → Bool) := f '' A
  have hpre : f ⁻¹' D = A := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (hA y x hxy).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hm : MeasurableSet D := (isClopen_discrete D).isClosed.measurableSet
  have heval : (s.map f - t.map f) D = s A - t A := by
    rw [_root_.sub_apply, VectorMeasure.map_apply _ hf.measurable hm,
      VectorMeasure.map_apply _ hf.measurable hm, hpre]
  calc
    |s A - t A| = |(s.map f - t.map f) D| := congrArg abs heval.symm
    _ ≤ (SignedMeasure.totalVariation (s.map f - t.map f)).real D := by
      simpa only [Real.norm_eq_abs] using (show SignedMeasure (C → Bool) from s.map f - t.map f).norm_le_totalVariation D
    _ ≤ (SignedMeasure.totalVariation (s.map f - t.map f)).real univ :=
      measureReal_mono (subset_univ D) (measure_ne_top _ _)
    _ < eps := hsmall

/-- Literal finite-depth data; a completed column has one index for every actual row. -/
structure OrderedHistory (Rows : Type w) (K : Type u) [TopologicalSpace K] (q : ℕ) where
  n : Fin q → ℕ
  H : Fin q → TopologicalSpace.Clopens K
  F : Fin q → Finset (TopologicalSpace.Clopens K)
  m : Rows → Fin q → ℕ

/-- One new column, with its clopen tests fixed before its auxiliary choices. -/
structure OrderedColumn (Rows : Type w) (K : Type u) [TopologicalSpace K] where
  n : ℕ
  H : TopologicalSpace.Clopens K
  F : Finset (TopologicalSpace.Clopens K)
  m : Rows → ℕ

/-- Appending uses the literal old data, with no retuning of an earlier entry. -/
def OrderedHistory.append {Rows : Type w} {q : ℕ}
    (h : OrderedHistory Rows K q) (c : OrderedColumn Rows K) : OrderedHistory Rows K (q + 1) where
  n := Fin.snoc h.n c.n
  H := Fin.snoc h.H c.H
  F := Fin.snoc h.F c.F
  m := fun r => Fin.snoc (h.m r) (c.m r)

/-- Exact truncation of all four data families. -/
def OrderedHistory.restrict {Rows : Type w} {q : ℕ}
    (h : OrderedHistory Rows K (q + 1)) : OrderedHistory Rows K q where
  n := fun j => h.n j.castSucc
  H := fun j => h.H j.castSucc
  F := fun j => h.F j.castSucc
  m := fun r j => h.m r j.castSucc

/-- The simultaneous geometric and measured obligations of one literal extension. -/
def OrderedColumn.Spec {Rows : Type w} {q : ℕ}
    (code : Rows → ℕ) (h : OrderedHistory Rows K q)
    (B : ℕ → TopologicalSpace.Clopens K) (S : Set ℕ)
    (p : K → L) (V : ℕ → Set L) (nu : ℕ → SignedMeasure L) (v : Measure K)
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, MeasurableSpace (Base r)]
    (pR : ∀ r, K → Base r) (VR : ∀ r, ℕ → Set (Base r))
    (nuR : ∀ r, ℕ → SignedMeasure (Base r)) (muR : Rows → SignedMeasure K)
    (pool : Rows → Set ℕ) (c : OrderedColumn Rows K) : Prop := by
  classical
  exact
      (h.append c).restrict = h ∧
      c.n ∈ S ∧ (∀ j, h.n j < c.n) ∧
      (∃ A : Finset Rows, (∀ r, r ∈ A ↔ code r < q) ∧
        ∃ R : TopologicalSpace.Clopens K,
          (R : Set K) = ⋃ r ∈ A, ⋃ j : Fin q, pR r ⁻¹' VR r (h.m r j) ∧
          (c.H : Set K) ⊆ p ⁻¹' V c.n \ R ∧
          (∃ D : Set L, IsClopen D ∧ D ⊆ V c.n ∧ (c.H : Set K) = p ⁻¹' D \ R) ∧
          (∀ x y, p x ∈ V c.n → p y ∈ V c.n → p x = p y →
            (x ∈ c.H ↔ y ∈ c.H)) ∧
          c.F = (Finset.univ.biUnion h.F) ∪ {B q, c.H, R}) ∧
      (∀ t : SignedMeasure K, t.map p = nu c.n →
        t.totalVariation univ = (nu c.n).totalVariation univ →
        (13 : ℝ) / 48 < t c.H ∧ (1 : ℝ) / 6 < t c.H) ∧
      ∀ r, c.m r ∈ pool r ∧ (∀ j, h.m r j < c.m r) ∧
        v.real (pR r ⁻¹' VR r (c.m r)) <
          (1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ q ∧
        (∀ A ∈ c.F, ∀ x y,
          pR r x ∈ VR r (c.m r) → pR r y ∈ VR r (c.m r) → pR r x = pR r y →
          (x ∈ A ↔ y ∈ A)) ∧
        ∀ t : SignedMeasure K, t.map (pR r) = nuR r (c.m r) →
          t.totalVariation univ = (nuR r (c.m r)).totalVariation univ →
          (SignedMeasure.totalVariation
            (t.map (fun x (A : {A // A ∈ c.F}) => (A.val : Set K).boolIndicator x) -
              (muR r).map (fun x (A : {A // A ∈ c.F}) => (A.val : Set K).boolIndicator x))).real univ < (1 / 2 : ℝ) ^ q ∧
          ∀ A : Set K,
            (∀ x y, (∀ C ∈ c.F, x ∈ C ↔ y ∈ C) → (x ∈ A ↔ y ∈ A)) →
            |t A - muR r A| < (1 / 2 : ℝ) ^ q

/-- One measured dynamic column is constructed in the order
old history, finite exclusion, target index, literal target slice, clopen tests,
then independently one auxiliary index in every actual row. The input fibre
conditions concern the original separating coordinates, not all clopens or a
moving finite marginal. -/
theorem exists_ordered_signed_column [CompactSpace L] [ZeroDimensionalSpace L]
    {Rows : Type w} {Γ : Type*} {q : ℕ}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (h : OrderedHistory Rows K q)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K)
    (S : Set ℕ) (hS : S.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : ℕ → SignedMeasure L) (s : ℕ → SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (hposreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.posPart)
    (hnegreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.negPart)
    (hpos : ∀ n, (1 : ℝ) / 2 ≤ (nu n).toJordanDecomposition.posPart.real univ)
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 S, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (v : Measure K) [IsFiniteMeasure v]
    (href : ∀ A : Set K, IsClopen A →
      Tendsto (fun n => (s n).totalVariation.real A)
        (atTop ⊓ 𝓟 S) (𝓝 (v.real A)))
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, T2Space (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (nuR : ∀ r, ℕ → SignedMeasure (Base r))
    (sR : Rows → ℕ → SignedMeasure K) (muR : Rows → SignedMeasure K)
    (hsRmap : ∀ r n, (sR r n).map (pR r) = nuR r n)
    (hsRmass : ∀ r n, (sR r n).totalVariation univ = (nuR r n).totalVariation univ)
    (hRnull : ∀ r n, (nuR r n).totalVariation (VR r n)ᶜ = 0)
    (pool : Rows → Set ℕ) (hpool : ∀ r, (pool r).Infinite)
    (hRE : ∀ r c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y →
        coord c x = coord c y)
    (hRref : ∀ r, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r)) (𝓝 (NormPreservingLifts.signedFunctional (muR r)).toWeakDual))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (hsmall : ∀ r (j : Fin q), v.real (pR r ⁻¹' VR r (h.m r j)) ≤
      (1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ (j : ℕ)) :
    ∃ c : OrderedColumn Rows K,
      c.Spec code h B S p V nu v Base pR VR nuR muR pool := by
  classical
  let A : Finset Rows := ((Set.finite_Iio q).preimage hcode.injOn).toFinset
  have hA (r : Rows) : r ∈ A ↔ code r < q := by simp [A]
  let W : Rows → ℕ → Set K := fun r j =>
    if hj : j < q then pR r ⁻¹' VR r (h.m r ⟨j, hj⟩) else ∅
  have hW : ∀ r j, IsClopen (W r j) := by
    intro r j
    dsimp only [W]
    split_ifs with hj
    · exact (hVR r _).preimage (hpR r)
    · exact isClopen_empty
  have hWsmall : ∀ r ∈ A, ∀ j < q,
      v.real (W r j) < (1 : ℝ) / 64 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j := by
    intro r _ j hj
    have hb : 0 < (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j := by positivity
    have hs := hsmall r ⟨j, hj⟩
    dsimp only [W]
    rw [dite_eq_left hj]
    dsimp only at hs
    nlinarith
  obtain ⟨n, hnS, hnM, H, hH, hsub, hliteral, hHE, hlarge⟩ :=
    exists_target_after_finite_exclusion code hcode A q S hS p hp V hV nu s
      hsmap hsmass hnull hposreg hnegreg hpos W hW
      (fun r _ j _ => eventually_clopen_fibre (atTop ⊓ 𝓟 S) coord hsep p V hE (hW r j))
      v (fun r _ j _ => href (W r j) (hW r j)) hWsmall (Finset.univ.sup h.n)
  let R : TopologicalSpace.Clopens K :=
    ⟨⋃ r ∈ A, ⋃ j ∈ Finset.range q, W r j,
      isClopen_biUnion_finset (fun r _ => isClopen_biUnion_finset (fun j _ => hW r j))⟩
  let Hc : TopologicalSpace.Clopens K := ⟨H, hH⟩
  let F : Finset (TopologicalSpace.Clopens K) :=
    (Finset.univ.biUnion h.F) ∪ {B q, Hc, R}
  let test : {A // A ∈ F} → C(K, Bool) := fun A =>
    ⟨(A.val : Set K).boolIndicator,
      (continuous_boolIndicator_iff_isClopen _).mpr A.val.isClopen⟩
  have hex (r : Rows) := exists_auxiliary_index (pool r) (hpool r) (pR r) (hpR r)
    (VR r) (hVR r) (nuR r) (sR r) (muR r) (hsRmap r) (hsRmass r) (hRnull r) test
    (fun A => by
      filter_upwards [eventually_clopen_fibre (atTop ⊓ 𝓟 (pool r)) coord hsep
        (pR r) (VR r) (hRE r) A.val.isClopen] with k hk
      intro x y hx hy hxy
      have heq := hk x y hx hy hxy
      change (A.val : Set K).boolIndicator x = (A.val : Set K).boolIndicator y
      simp only [Set.boolIndicator, heq])
    (hRref r) v (hRdis r) (Finset.univ.sup (h.m r))
    ((1 / 2 : ℝ) ^ q) ((1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ q)
    (by positivity) (by positivity)
  choose m hmPool hmM hmSmall hmE hmMarginal using hex
  let c : OrderedColumn Rows K := ⟨n, Hc, F, m⟩
  refine ⟨c, ?_, hnS, ?_, ⟨A, hA, R, ?_, hsub, hliteral, hHE, rfl⟩, hlarge, ?_⟩
  · cases h
    simp only [OrderedHistory.append, OrderedHistory.restrict, Fin.snoc_castSucc]
  · intro j
    exact (Finset.le_sup (s := Finset.univ) (f := h.n) (Finset.mem_univ j)).trans_lt hnM
  · ext x
    simp only [R, TopologicalSpace.Clopens.coe_mk, mem_iUnion, Finset.mem_range, W]
    constructor
    · rintro ⟨r, hr, j, hj, hx⟩
      exact ⟨r, hr, ⟨j, hj⟩, by simpa only [dite_eq_left hj] using hx⟩
    · rintro ⟨r, hr, j, hx⟩
      exact ⟨r, hr, j.val, j.isLt, by simpa only [dite_eq_left j.isLt] using hx⟩
  · intro r
    refine ⟨hmPool r, ?_, hmSmall r, ?_, ?_⟩
    · intro j
      exact (Finset.le_sup (s := Finset.univ) (f := h.m r)
        (Finset.mem_univ j)).trans_lt (hmM r)
    · intro A hAF x y hx hy hxy
      have hb := hmE r ⟨A, hAF⟩ x y hx hy hxy
      change (A : Set K).boolIndicator x = (A : Set K).boolIndicator y at hb
      change x ∈ (A : Set K) ↔ y ∈ (A : Set K)
      rw [(A : Set K).mem_iff_boolIndicator x, (A : Set K).mem_iff_boolIndicator y, hb]
    · intro t htmap htmass
      refine ⟨(hmMarginal r t htmap htmass).1, ?_⟩
      intro A hgen
      let f : K → ({A // A ∈ F} → Bool) := fun x C => test C x
      have hf : Continuous f := continuous_pi (fun C => (test C).continuous)
      apply apply_error_of_finite_marginal f hf t (muR r) ((1 / 2 : ℝ) ^ q)
        (hmMarginal r t htmap htmass).1 A
      intro x y hxy
      apply hgen x y
      intro C hCF
      have hb := congrFun hxy ⟨C, hCF⟩
      change (C : Set K).boolIndicator x = (C : Set K).boolIndicator y at hb
      change x ∈ (C : Set K) ↔ y ∈ (C : Set K)
      rw [(C : Set K).mem_iff_boolIndicator x, (C : Set K).mem_iff_boolIndicator y, hb]

private lemma map_mass_through_factor {X : Type*} [MeasurableSpace X]
    (f : X → K) (hf : Measurable f) (g : K → L) (hg : Measurable g)
    (t : SignedMeasure X) (nu : SignedMeasure L)
    (hmap : t.map (g ∘ f) = nu) (hmass : t.totalVariation univ = nu.totalVariation univ) :
    (t.map f).map g = nu ∧ (SignedMeasure.totalVariation (t.map f)) univ = nu.totalVariation univ := by
  have hmid : (t.map f).map g = nu := by
    ext A hA
    rw [VectorMeasure.map_apply _ hg hA, VectorMeasure.map_apply _ hf (hg hA)]
    have h := congrArg (fun r : SignedMeasure L => r A) hmap
    rw [VectorMeasure.map_apply _ (hg.comp hf) hA] at h
    exact h
  have hupper := VectorMeasure.variation_map_le (μ := t) (φ := f) univ
  have hlower := VectorMeasure.variation_map_le (μ := t.map f) (φ := g) univ
  simp only [← SignedMeasure.totalVariation_eq_variation,
    Measure.map_apply hf MeasurableSet.univ, preimage_univ] at hupper
  simp only [← SignedMeasure.totalVariation_eq_variation, hmid,
    Measure.map_apply hg MeasurableSet.univ, preimage_univ] at hlower
  exact ⟨hmid, le_antisymm (hupper.trans hmass.le) hlower⟩

private lemma apply_eq_inter_of_null_compl {X : Type*} [MeasurableSpace X]
    (t : SignedMeasure X) {A W : Set X} (hA : MeasurableSet A) (hW : MeasurableSet W)
    (hnull : t.totalVariation Wᶜ = 0) : t A = t (A ∩ W) := by
  have hz : t (A \ W) = 0 := t.null_of_totalVariation_zero
    (measure_mono_null (fun _ hx => hx.2) hnull)
  have hsplit := VectorMeasure.of_add_of_sdiff (v := t) (hA.inter hW) hA
    (inter_subset_left : A ∩ W ⊆ A)
  have heq : A \ (A ∩ W) = A \ W := by ext x; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
  rw [heq, hz, add_zero] at hsplit
  exact hsplit.symm

private lemma bool_eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Inherited reservoirs exist only on old rows. The new row uses its signed
cluster pool and has no inherited parity reservoir at this stage. -/
noncomputable def ordinaryPool {Rows Γ : Type*} (newRow : Rows)
    (oldJ : ∀ r, r ≠ newRow → Γ → Set ℕ)
    (oldN : ∀ r, r ≠ newRow → Γ → Fin 2 → Set ℕ)
    (birthS : Γ → Set ℕ) (rho : ℕ → Γ) (r : Rows) (q : ℕ) : Set ℕ := by
  classical
  exact if hr : r = newRow then birthS (rho q)
    else oldJ r hr (rho q) ∩ oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩

/-- Old signed references have no value on the new row before its cluster is chosen. -/
noncomputable def ordinaryReference {Rows Γ : Type*} (newRow : Rows)
    (oldMu : ∀ r, r ≠ newRow → Γ → SignedMeasure K)
    (birthMu : Γ → SignedMeasure K) (r : Rows) (d : Γ) : SignedMeasure K := by
  classical
  exact if hr : r = newRow then birthMu d else oldMu r hr d

set_option maxHeartbeats 800000 in
/-- Dynamic measured choices and their same-object closed split.
The actual I and J, inherited and birth reservoirs, whole-support E, common
represented every-choice signed F and scheduled signed G are constructed.
The birth signed clusters and the independent target positive-variation
cluster are selected internally. Residual reference selection follows final I. -/
theorem exists_measured_dynamic_split [CompactSpace L] [ZeroDimensionalSpace L]
    [T2Space K] [SecondCountableTopology K]
    [TopologicalSpace.MetrizableSpace K] [TotallyDisconnectedSpace K]
    {Rows : Type w} {Γ : Type*}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (newRow : Rows) (hNewCode : code newRow = 0)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K) (hB : Function.Surjective B) (rho : ℕ → Γ)
    (hRho : ∀ d (e : Fin 2), {q | rho q = d ∧ q % 2 = (e : ℕ)}.Infinite)
    (targetPool : Set ℕ) (hTargetPoolInf : targetPool.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : ℕ → SignedMeasure L) (s : ℕ → SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hTargetMass : ∀ n, (nu n).totalVariation univ = 1)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (hposreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.posPart)
    (hnegreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.negPart)
    (hpos : ∀ n, (1 : ℝ) / 2 ≤ (nu n).toJordanDecomposition.posPart.real univ)
    (hTargetE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 targetPool, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, T2Space (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (hpRsurj : ∀ r, Function.Surjective (pR r))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (targetRow : Rows)
    (hTargetSupport : ∀ n, pR targetRow ⁻¹' VR targetRow n = p ⁻¹' V n)
    (hTargetFibre : ∀ x y, pR targetRow x = pR targetRow y → p x = p y)
    (nuR : ∀ r, Γ → ℕ → SignedMeasure (Base r))
    (hRbound : ∀ r d n, (nuR r d n).totalVariation.real univ ≤ 1)
    (sR : Rows → Γ → ℕ → SignedMeasure K)
    (oldMuR : ∀ r, r ≠ newRow → Γ → SignedMeasure K)
    (hsRmap : ∀ r d n, (sR r d n).map (pR r) = nuR r d n)
    (hsRmass : ∀ r d n, (sR r d n).totalVariation univ = (nuR r d n).totalVariation univ)
    (hRnull : ∀ r d n, (nuR r d n).totalVariation (VR r n)ᶜ = 0)
    (nuA : ∀ r, ℕ → SignedMeasure (Base r))
    (hAbound : ∀ r n, (nuA r n).totalVariation.real univ ≤ 1)
    (hAnull : ∀ r n, (nuA r n).totalVariation (VR r n)ᶜ = 0)
    (oldI : ∀ r, r ≠ newRow → Set ℕ)
    (hTargetPool : ∀ hr : targetRow ≠ newRow, targetPool ⊆ oldI targetRow hr)
    (oldJ : ∀ r, r ≠ newRow → Γ → Set ℕ)
    (oldN : ∀ r, r ≠ newRow → Γ → Fin 2 → Set ℕ)
    (hOldA : ∀ r hr d, oldJ r hr d ⊆ oldI r hr)
    (hOldB : ∀ r hr d, Disjoint (oldN r hr d 0) (oldN r hr d 1))
    (hOldC : ∀ r hr d e, (oldJ r hr d ∩ oldN r hr d e).Infinite)
    (hOldE : ∀ r hr c, ∀ᶠ n in atTop ⊓ 𝓟 (oldI r hr), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y → coord c x = coord c y)
    (hOldRef : ∀ r hr d, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r d n)).toWeakDual)
      (atTop ⊓ 𝓟 (oldJ r hr d)) (𝓝 (NormPreservingLifts.signedFunctional (oldMuR r hr d)).toWeakDual))
    (hNewProjection : Function.Injective (pR newRow))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (hTdis : Pairwise (fun n m => Disjoint (p ⁻¹' V n) (p ⁻¹' V m))) :
    ∃ (S : Set ℕ) (vP : ProbabilityMeasure K),
      S ⊆ targetPool ∧ S.Infinite ∧
      (∀ A : Set K, IsClopen A → Tendsto (fun n => (s n).totalVariation.real A)
        (atTop ⊓ 𝓟 S) (𝓝 ((vP : Measure K).real A))) ∧
      ∃ (birthS : Γ → Set ℕ) (birthMu : Γ → SignedMeasure K),
        (∀ d, (birthS d).Infinite) ∧
        (∀ d, (birthMu d).totalVariation.real univ ≤ 1 ∧
          Measure.Regular (birthMu d).toJordanDecomposition.posPart ∧
          Measure.Regular (birthMu d).toJordanDecomposition.negPart ∧
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sR newRow d n)).toWeakDual)
            (atTop ⊓ 𝓟 (birthS d))
            (𝓝 (NormPreservingLifts.signedFunctional (birthMu d)).toWeakDual)) ∧
    let v : Measure K := vP
    let muR := ordinaryReference newRow oldMuR birthMu
    let pool := ordinaryPool newRow oldJ oldN birthS rho
    ∃ (history : ∀ q, OrderedHistory Rows K q) (c : ℕ → OrderedColumn Rows K),
      (∀ q, history (q + 1) = (history q).append (c q)) ∧
      (∀ q, (c q).Spec code (history q) B S p V nu v Base pR VR
        (fun r => nuR r (rho q)) (fun r => muR r (rho q)) (fun r => pool r q)) ∧
      StrictMono (fun q => (c q).n) ∧ (∀ r, StrictMono (fun q => (c q).m r)) ∧
      (∀ j q, j ≤ q → (c j).H ∈ (c q).F ∧ B j ∈ (c q).F) ∧
      (∀ r q s, code r < q → q < s →
        Disjoint ((c s).H : Set K) (pR r ⁻¹' VR r ((c q).m r))) ∧
      ∃ (Y Z : Set K) (hclosed : IsClosed (splitCarrier Y Z)),
        letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
        IsClosed Y ∧ IsClosed Z ∧ Y ∪ Z = univ ∧
        Z = closure (⋃ s : ℕ, ⋃ (_ : s % 2 = 0), ((c s).H : Set K)) ∧ Y = closure Zᶜ ∧
        IsClosed (splitCarrier Y Z) ∧
        Function.Surjective (fun x : splitCarrier Y Z => x.1.1) ∧
        (∀ r q, code r < q →
          Z ∩ (pR r ⁻¹' VR r ((c q).m r)) =
            evenPrefix (fun s => ((c s).H : Set K)) q ∩ (pR r ⁻¹' VR r ((c q).m r)) ∧
          Y ∩ (pR r ⁻¹' VR r ((c q).m r)) =
            (evenPrefix (fun s => ((c s).H : Set K)) q)ᶜ ∩ (pR r ⁻¹' VR r ((c q).m r)) ∧
          Disjoint (Y ∩ Z) (pR r ⁻¹' VR r ((c q).m r)) ∧
          ∀ x : splitCarrier Y Z, x.1.1 ∈ pR r ⁻¹' VR r ((c q).m r) →
            (x.1.2 = true ↔ x.1.1 ∈ evenPrefix (fun s => ((c s).H : Set K)) q)) ∧
        (∀ q, Z ∩ (p ⁻¹' V (c q).n) = (if q % 2 = 0 then ((c q).H : Set K) else ∅) ∧
          Disjoint (Y ∩ Z) (p ⁻¹' V (c q).n) ∧
          ∀ x : splitCarrier Y Z, x.1.1 ∈ p ⁻¹' V (c q).n →
            (x.1.2 = true ↔ q % 2 = 0 ∧ x.1.1 ∈ (c q).H)) ∧
        (∀ r q, code r < q → ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r ((c q).m r) → pR r y.1.1 ∈ VR r ((c q).m r) →
          pR r x.1.1 = pR r y.1.1 → x.1.2 = y.1.2) ∧
        (∀ q, ∀ x y : splitCarrier Y Z,
          p x.1.1 ∈ V (c q).n → p y.1.1 ∈ V (c q).n →
          p x.1.1 = p y.1.1 → x.1.2 = y.1.2) ∧
        (∀ q (t : SignedMeasure (splitCarrier Y Z)),
          t.map (fun x => p x.1.1) = nu (c q).n →
          t.totalVariation univ = (nu (c q).n).totalVariation univ →
          (q % 2 = 0 → (1 : ℝ) / 6 < t {x | x.1.2 = true}) ∧
          (q % 2 ≠ 0 → t {x | x.1.2 = true} = 0)) ∧
        (∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (fun x => p x.1.1) = nu n) →
          (∀ n, (sigma n).totalVariation univ = (nu n).totalVariation univ) →
          {n | (1 : ℝ) / 6 ≤ sigma n {x | x.1.2 = true}}.Infinite ∧
            {n | sigma n {x | x.1.2 = true} = 0}.Infinite) ∧
        (∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
          (∀ k, rho (phi k) = d) →
          ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
            Measure.Regular mu.toJordanDecomposition.posPart ∧
            Measure.Regular mu.toJordanDecomposition.negPart ∧
            ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
              (∀ k, (sigma k).map (fun x => pR r x.1.1) = nuR r d ((c (phi k)).m r)) →
              (∀ k, (sigma k).totalVariation univ =
                (nuR r d ((c (phi k)).m r)).totalVariation univ) →
              Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
                atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) ∧
        ∃ (I : Rows → Set ℕ) (J : Rows → Γ → Set ℕ) (N : Rows → Γ → Fin 2 → Set ℕ),
          (∀ r, I r = {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
            (r = targetRow ∧ ∃ q, (c q).n = n)}) ∧
          (∀ r d, J r d = {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}) ∧
          (∀ r hr d e, N r d e = oldN r hr d e) ∧
          (∀ d e, N newRow d e =
            {n | ∃ q, code newRow < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧ (c q).m newRow = n}) ∧
          (∀ r d, J r d ⊆ I r) ∧
          (∀ r d, Disjoint (N r d 0) (N r d 1)) ∧
          (∀ r d e, (J r d ∩ N r d e).Infinite) ∧
          (∀ r, (I r).Infinite) ∧
          (∀ r hr, I r ⊆ oldI r hr) ∧
          (∀ r hr d, J r d ⊆ oldJ r hr d) ∧
          (∀ r (A : Set K), IsClopen A → ∀ᶠ n in atTop ⊓ 𝓟 (I r),
            ∀ x y : splitCarrier Y Z,
              pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
              pR r x.1.1 = pR r y.1.1 →
              (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2) ∧
          (∀ r d, ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
            Measure.Regular mu.toJordanDecomposition.posPart ∧
            Measure.Regular mu.toJordanDecomposition.negPart ∧
            ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
              (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuR r d n) →
              (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
              Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                (atTop ⊓ 𝓟 (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) ∧
          (∃ (JA : Rows → Set ℕ) (NA : Rows → Fin 2 → Set ℕ)
              (muA : Rows → SignedMeasure (splitCarrier Y Z)),
            ∀ r, JA r ⊆ I r ∧ Disjoint (NA r 0) (NA r 1) ∧
              (∀ e, NA r e ⊆ JA r) ∧ (∀ e, (JA r ∩ NA r e).Infinite) ∧
              (muA r).totalVariation.real univ ≤ 1 ∧
              Measure.Regular (muA r).toJordanDecomposition.posPart ∧
              Measure.Regular (muA r).toJordanDecomposition.negPart ∧
              ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
                (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuA r n) →
                (∀ n, (sigma n).totalVariation univ = (nuA r n).totalVariation univ) →
                Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                  (atTop ⊓ 𝓟 (JA r))
                  (𝓝 (NormPreservingLifts.signedFunctional (muA r)).toWeakDual)) := by
  classical
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  letI : Infinite targetPool := Set.infinite_coe_iff.mpr hTargetPoolInf
  let tauV : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet targetPool
  have htauVRange : Set.range tauV = targetPool := Nat.orderEmbeddingOfSet_range targetPool
  have htauVMem (k : ℕ) : tauV k ∈ targetPool := htauVRange ▸ Set.mem_range_self k
  let tvProb : ℕ → ProbabilityMeasure K := fun n =>
    ⟨(s n).totalVariation, ⟨by rw [hsmass n, hTargetMass n]⟩⟩
  obtain ⟨vP, phiV, hphiV, hVconv⟩ := CompactSpace.tendsto_subseq (fun k => tvProb (tauV k))
  let psiV : ℕ → ℕ := fun k => tauV (phiV k)
  have hpsiV : StrictMono psiV := tauV.strictMono.comp hphiV
  let S : Set ℕ := Set.range psiV
  have hS : S.Infinite := Set.infinite_range_of_injective hpsiV.injective
  have hSsub : S ⊆ targetPool := by
    rintro _ ⟨k, rfl⟩
    exact htauVMem (phiV k)
  let v : Measure K := vP
  have href (A : Set K) (hA : IsClopen A) :
      Tendsto (fun n => (s n).totalVariation.real A) (atTop ⊓ 𝓟 S) (𝓝 (v.real A)) := by
    have hprob := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hVconv hA
    have hreal := (NNReal.continuous_coe.tendsto (vP A)).comp hprob
    have hconv : Tendsto (fun k => (s (psiV k)).totalVariation.real A) atTop (𝓝 (v.real A)) := by
      exact hreal
    apply Filter.tendsto_def.mpr
    intro T hT
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hconv.eventually hT)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (psiV M)] with n hn hnS
    obtain ⟨k, rfl⟩ := hnS
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hpsiV (lt_of_not_ge hk))
    exact hM k hMk
  have hE (c : Γ) : ∀ᶠ n in atTop ⊓ 𝓟 S, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y :=
    (hTargetE c).filter_mono (inf_le_inf le_rfl (Filter.principal_mono.mpr hSsub))
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  have hBirthBound (d : Γ) (n : ℕ) : (sR newRow d n).totalVariation.real univ ≤ 1 := by
    simpa only [Measure.real, hsRmass] using hRbound newRow d n
  have hBirthCluster (d : Γ) := SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional
    1 (by norm_num) (sR newRow d) (hBirthBound d)
  choose phiBirth birthMu hPhiBirth hMuBirth hConvBirth using hBirthCluster
  let birthS : Γ → Set ℕ := fun d => Set.range (phiBirth d)
  have hBirthS (d : Γ) : (birthS d).Infinite := Set.infinite_range_of_injective (hPhiBirth d).injective
  have hBirthRef (d : Γ) : Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR newRow d n)).toWeakDual)
      (atTop ⊓ 𝓟 (birthS d)) (𝓝 (NormPreservingLifts.signedFunctional (birthMu d)).toWeakDual) := by
    apply Filter.tendsto_def.mpr
    intro A hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((hConvBirth d).eventually hA)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (phiBirth d M)] with n hn hnS
    obtain ⟨k, rfl⟩ := hnS
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hPhiBirth d (lt_of_not_ge hk))
    exact hM k hMk
  have hBirthData (d : Γ) : (birthMu d).totalVariation.real univ ≤ 1 ∧
      Measure.Regular (birthMu d).toJordanDecomposition.posPart ∧
      Measure.Regular (birthMu d).toJordanDecomposition.negPart ∧
      Tendsto (fun n => (NormPreservingLifts.signedFunctional (sR newRow d n)).toWeakDual)
        (atTop ⊓ 𝓟 (birthS d)) (𝓝 (NormPreservingLifts.signedFunctional (birthMu d)).toWeakDual) :=
    ⟨hMuBirth d, inferInstance, inferInstance, hBirthRef d⟩
  let muR : Rows → Γ → SignedMeasure K := ordinaryReference newRow oldMuR birthMu
  let pool : Rows → ℕ → Set ℕ := ordinaryPool newRow oldJ oldN birthS rho
  have hpool : ∀ r q, (pool r q).Infinite := by
    intro r q
    by_cases hr : r = newRow
    · subst r
      simpa [pool, ordinaryPool] using hBirthS (rho q)
    · simpa only [pool, ordinaryPool, dite_eq_right hr] using
        hOldC r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩
  have hRE : ∀ r q c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r q), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y → coord c x = coord c y := by
    intro r q c
    by_cases hr : r = newRow
    · subst r
      exact Filter.Eventually.of_forall (fun _ x y _ _ hxy => congrArg (coord c) (hNewProjection hxy))
    · have hsub : pool r q ⊆ oldI r hr := by
        intro n hn
        have hn' : n ∈ oldJ r hr (rho q) ∩
            oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
          simpa only [pool, ordinaryPool, dite_eq_right hr] using hn
        exact hOldA r hr (rho q) hn'.1
      exact (hOldE r hr c).filter_mono (inf_le_inf le_rfl (Filter.principal_mono.mpr hsub))
  have hRref : ∀ r q, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r (rho q) n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r q)) (𝓝 (NormPreservingLifts.signedFunctional (muR r (rho q))).toWeakDual) := by
    intro r q
    by_cases hr : r = newRow
    · subst r
      simpa [pool, ordinaryPool, muR, ordinaryReference] using hBirthRef (rho q)
    · have hsub : pool r q ⊆ oldJ r hr (rho q) := by
        intro n hn
        have hn' : n ∈ oldJ r hr (rho q) ∩
            oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
          simpa only [pool, ordinaryPool, dite_eq_right hr] using hn
        exact hn'.1
      simpa only [muR, ordinaryReference, dif_neg hr] using
        (hOldRef r hr (rho q)).mono_left (inf_le_inf le_rfl (Filter.principal_mono.mpr hsub))
  let State (q : ℕ) := {h : OrderedHistory Rows K q //
    ∀ r (j : Fin q), v.real (pR r ⁻¹' VR r (h.m r j)) ≤
      (1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ (j : ℕ)}
  have hex (q : ℕ) (x : State q) := exists_ordered_signed_column code hcode x.val
    coord hsep B S hS p hp V hV nu s hsmap hsmass hnull hposreg hnegreg hpos hE v href
    Base pR hpR VR hVR (fun r => nuR r (rho q)) (fun r => sR r (rho q)) (fun r => muR r (rho q))
    (fun r => hsRmap r (rho q)) (fun r => hsRmass r (rho q)) (fun r => hRnull r (rho q))
    (fun r => pool r q) (fun r => hpool r q) (fun r => hRE r q) (fun r => hRref r q)
    hRdis x.property
  choose column hcolumn using hex
  let next (q : ℕ) (x : State q) : State (q + 1) :=
    ⟨x.val.append (column q x), by
      intro r j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [OrderedHistory.append, Fin.snoc_last, Fin.val_last] using
          ((hcolumn q x).2.2.2.2.2 r).2.2.1.le
      · simpa only [OrderedHistory.append, Fin.snoc_castSucc, Fin.val_castSucc] using
          x.property r j⟩
  let empty : State 0 := ⟨⟨Fin.elim0, Fin.elim0, Fin.elim0, fun _ => Fin.elim0⟩,
    fun _ j => Fin.elim0 j⟩
  let hist : ∀ q, State q := fun q => Nat.rec empty next q
  let c : ℕ → OrderedColumn Rows K := fun q => column q (hist q)
  have hsuc (q : ℕ) : (hist (q + 1)).val = (hist q).val.append (c q) := rfl
  have hstep (q : ℕ) : (c q).Spec code (hist q).val B S p V nu v Base pR VR
      (fun r => nuR r (rho q)) (fun r => muR r (rho q)) (fun r => pool r q) := hcolumn q (hist q)
  let get : ∀ {q}, OrderedHistory Rows K q → Fin q → OrderedColumn Rows K :=
    fun {_} h j => ⟨h.n j, h.H j, h.F j, fun r => h.m r j⟩
  have hstable : ∀ q (j : Fin q), get (hist q).val j = c (j : ℕ) := by
    intro q
    induction q with
    | zero => intro j; exact Fin.elim0 j
    | succ q ih =>
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [hsuc]
        change OrderedColumn.mk _ _ _ _ = c q
        simp only [OrderedHistory.append, Fin.snoc_last]
      · rw [hsuc]
        simpa only [get, OrderedHistory.append, Fin.snoc_castSucc, Fin.val_castSucc] using ih j
  have hn : StrictMono (fun q => (c q).n) := by
    intro q s hqs
    have hs := (hstep s).2.2.1 ⟨q, hqs⟩
    have heq := congrArg OrderedColumn.n (hstable s ⟨q, hqs⟩)
    change (hist s).val.n ⟨q, hqs⟩ = (c q).n at heq
    rw [heq] at hs
    exact hs
  have hm : ∀ r, StrictMono (fun q => (c q).m r) := by
    intro r q s hqs
    have hs := ((hstep s).2.2.2.2.2 r).2.1 ⟨q, hqs⟩
    have heq := congrArg (fun t => t.m r) (hstable s ⟨q, hqs⟩)
    change (hist s).val.m r ⟨q, hqs⟩ = (c q).m r at heq
    rw [heq] at hs
    exact hs
  have htests (j q : ℕ) (hjq : j ≤ q) : (c j).H ∈ (c q).F ∧ B j ∈ (c q).F := by
    have hself (k : ℕ) : (c k).H ∈ (c k).F ∧ B k ∈ (c k).F := by
      obtain ⟨_, _, _, _, _, _, _, hF⟩ := (hstep k).2.2.2.1
      rw [hF]
      simp
    rcases eq_or_lt_of_le hjq with rfl | hjq
    · exact hself j
    · obtain ⟨_, _, _, _, _, _, _, hF⟩ := (hstep q).2.2.2.1
      have hsubF : (c j).F ⊆ (c q).F := by
        intro A hAF
        rw [hF]
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        have heq := congrArg OrderedColumn.F (hstable q ⟨j, hjq⟩)
        change (hist q).val.F ⟨j, hjq⟩ = (c j).F at heq
        exact ⟨⟨j, hjq⟩, Finset.mem_univ _, heq.symm ▸ hAF⟩
      exact ⟨hsubF (hself j).1, hsubF (hself j).2⟩
  have havoid : ∀ r q s, code r < q → q < s →
      Disjoint ((c s).H : Set K) (pR r ⁻¹' VR r ((c q).m r)) := by
    intro r q s hr hqs
    obtain ⟨A, hA, R, hR, hsub, _, _, _⟩ := (hstep s).2.2.2.1
    rw [Set.disjoint_left]
    intro x hxH hxW
    apply (hsub hxH).2
    rw [hR]
    have heq := congrArg (fun t => t.m r) (hstable s ⟨q, hqs⟩)
    refine mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨(hA r).mpr (hr.trans hqs),
      mem_iUnion.mpr ⟨⟨q, hqs⟩, ?_⟩⟩⟩
    change pR r x ∈ VR r ((hist s).val.m r ⟨q, hqs⟩)
    change (hist s).val.m r ⟨q, hqs⟩ = (c q).m r at heq
    rwa [heq]
  have hHT (q : ℕ) : ((c q).H : Set K) ⊆ p ⁻¹' V (c q).n := by
    obtain ⟨_, _, _, _, hsub, _, _, _⟩ := (hstep q).2.2.2.1
    exact hsub.trans sdiff_subset
  have hdis : Pairwise (fun q s => Disjoint (p ⁻¹' V (c q).n) (p ⁻¹' V (c s).n)) := by
    intro q s hqs
    exact hTdis (fun h => hqs (hn.injective h))
  obtain ⟨Y, Z, hY, hZ, hcov, hZdef, hYdef, hclosed, hsurj, haux, htarget⟩ :=
    exists_closed_split_of_ordered_exclusion code (fun q => ((c q).H : Set K))
      (fun q => (c q).H.isClopen) (fun r q => pR r ⁻¹' VR r ((c q).m r))
      (fun r q => (hVR r _).preimage (hpR r)) havoid
      (fun q => p ⁻¹' V (c q).n) (fun q => (hV _).preimage hp) hdis hHT
  have hnewAux : ∀ r q, code r < q → ∀ x y : splitCarrier Y Z,
      pR r x.1.1 ∈ VR r ((c q).m r) → pR r y.1.1 ∈ VR r ((c q).m r) →
      pR r x.1.1 = pR r y.1.1 → x.1.2 = y.1.2 := by
    intro r q hr x y hx hy hxy
    have hfinite (j : ℕ) (hj : j ≤ q) :
        (x.1.1 ∈ (c j).H ↔ y.1.1 ∈ (c j).H) :=
      ((hstep q).2.2.2.2.2 r).2.2.2.1 (c j).H (htests j q hj).1 x.1.1 y.1.1 hx hy hxy
    have hU : x.1.1 ∈ evenPrefix (fun s => ((c s).H : Set K)) q ↔
        y.1.1 ∈ evenPrefix (fun s => ((c s).H : Set K)) q := by
      simp only [evenPrefix, mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨j, hj, hxH⟩
        refine ⟨j, hj, ?_⟩
        by_cases heven : j % 2 = 0
        · simp only [ite_eq_left heven] at hxH ⊢
          exact (hfinite j (by omega)).mp hxH
        · simpa only [ite_eq_right heven, mem_empty_iff_false] using hxH
      · rintro ⟨j, hj, hyH⟩
        refine ⟨j, hj, ?_⟩
        by_cases heven : j % 2 = 0
        · simp only [ite_eq_left heven] at hyH ⊢
          exact (hfinite j (by omega)).mpr hyH
        · simpa only [ite_eq_right heven, mem_empty_iff_false] using hyH
    have hb := ((haux r q hr).2.2.2 x hx).trans (hU.trans ((haux r q hr).2.2.2 y hy).symm)
    exact bool_eq_of_true_iff x.1.2 y.1.2 hb
  have hnewTarget : ∀ q, ∀ x y : splitCarrier Y Z,
      p x.1.1 ∈ V (c q).n → p y.1.1 ∈ V (c q).n →
      p x.1.1 = p y.1.1 → x.1.2 = y.1.2 := by
    intro q x y hx hy hxy
    obtain ⟨_, _, _, _, _, _, hHE, _⟩ := (hstep q).2.2.2.1
    have hHxy := hHE x.1.1 y.1.1 hx hy hxy
    change x.1.1 ∈ ((c q).H : Set K) ↔ y.1.1 ∈ ((c q).H : Set K) at hHxy
    have htagX := (htarget q).2.2 x hx
    have htagY := (htarget q).2.2 y hy
    have hb : (x.1.2 = true ↔ y.1.2 = true) := by
      rw [htagX, htagY, hHxy]
    exact bool_eq_of_true_iff x.1.2 y.1.2 hb
  letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let projection : splitCarrier Y Z → K := fun x => x.1.1
  have hprojection : Continuous projection := continuous_fst.comp continuous_subtype_val
  let side : Set (splitCarrier Y Z) := {x | x.1.2 = true}
  have hside : IsClopen side := (isClopen_discrete ({true} : Set Bool)).preimage
    (continuous_snd.comp continuous_subtype_val)
  have hG : ∀ q (t : SignedMeasure (splitCarrier Y Z)),
      t.map (p ∘ projection) = nu (c q).n →
      t.totalVariation univ = (nu (c q).n).totalVariation univ →
      (q % 2 = 0 → (1 : ℝ) / 6 < t side) ∧ (q % 2 ≠ 0 → t side = 0) := by
    intro q t htmap htmass
    let W : Set (splitCarrier Y Z) := (p ∘ projection) ⁻¹' V (c q).n
    have hW : IsClopen W := (hV _).preimage (hp.comp hprojection)
    have htNull : t.totalVariation Wᶜ = 0 := support_null (p ∘ projection)
      (hp.comp hprojection) t (nu (c q).n) htmap htmass (hV _) (hnull _)
    have htcut := apply_eq_inter_of_null_compl t hside.isClosed.measurableSet
      hW.isClosed.measurableSet htNull
    constructor
    · intro heven
      have htrace : side ∩ W = projection ⁻¹' ((c q).H : Set K) := by
        ext x
        constructor
        · rintro ⟨hx, hxW⟩
          exact ((htarget q).2.2 x hxW).mp hx |>.2
        · intro hxH
          have hxW : x ∈ W := hHT q hxH
          exact ⟨((htarget q).2.2 x hxW).mpr ⟨heven, hxH⟩, hxW⟩
      have hmid := map_mass_through_factor projection hprojection.measurable p hp.measurable
        t (nu (c q).n) htmap htmass
      have hlarge := ((hstep q).2.2.2.2.1 (t.map projection) hmid.1 hmid.2).2
      rw [htcut, htrace, ← VectorMeasure.map_apply t hprojection.measurable
        (c q).H.isClopen.isClosed.measurableSet]
      exact hlarge
    · intro hodd
      have htrace : side ∩ W = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxW⟩
        exact hodd (((htarget q).2.2 x hxW).mp hx).1
      rw [htcut, htrace, t.empty]
  have hGinf : ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
      (∀ n, (sigma n).map (p ∘ projection) = nu n) →
      (∀ n, (sigma n).totalVariation univ = (nu n).totalVariation univ) →
      {n | (1 : ℝ) / 6 ≤ sigma n side}.Infinite ∧ {n | sigma n side = 0}.Infinite := by
    intro sigma hmap hmass
    have heven : Function.Injective (fun k => (c (2 * k)).n) :=
      hn.injective.comp (fun a b hab => by omega)
    have hodd : Function.Injective (fun k => (c (2 * k + 1)).n) :=
      hn.injective.comp (fun a b hab => by omega)
    constructor
    · apply (Set.infinite_range_of_injective heven).mono
      rintro _ ⟨k, rfl⟩
      exact ((hG (2 * k) (sigma _) (hmap _) (hmass _)).1 (by omega)).le
    · apply (Set.infinite_range_of_injective hodd).mono
      rintro _ ⟨k, rfl⟩
      exact (hG (2 * k + 1) (sigma _) (hmap _) (hmass _)).2 (by omega)
  let U : ℕ → Set K := evenPrefix (fun q => ((c q).H : Set K))
  have hUclopen (q : ℕ) : IsClopen (U q) :=
    evenPrefix_clopen _ (fun j => (c j).H.isClopen) q
  have hUmono : Monotone U := evenPrefix_mono _
  have hGenU (q : ℕ) (x y : K)
      (hxy : ∀ C ∈ (c q).F, x ∈ C ↔ y ∈ C) : x ∈ U q ↔ y ∈ U q := by
    simp only [U, evenPrefix, mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hxH⟩
      refine ⟨j, hj, ?_⟩
      by_cases heven : j % 2 = 0
      · simp only [ite_eq_left heven] at hxH ⊢
        exact (hxy (c j).H (htests j q (by omega)).1).mp hxH
      · simpa only [ite_eq_right heven, mem_empty_iff_false] using hxH
    · rintro ⟨j, hj, hyH⟩
      refine ⟨j, hj, ?_⟩
      by_cases heven : j % 2 = 0
      · simp only [ite_eq_left heven] at hyH ⊢
        exact (hxy (c j).H (htests j q (by omega)).1).mpr hyH
      · simpa only [ite_eq_right heven, mem_empty_iff_false] using hyH
  have hSideRow (r : Rows) (q : ℕ) (hq : code r < q)
      (t : SignedMeasure (splitCarrier Y Z))
      (htmap : t.map (pR r ∘ projection) = nuR r (rho q) ((c q).m r))
      (htmass : t.totalVariation univ = (nuR r (rho q) ((c q).m r)).totalVariation univ)
      (A : Set K) (hA : IsClopen A) :
      t (side ∩ projection ⁻¹' A) = (t.map projection) (A ∩ U q) := by
    let W : Set (splitCarrier Y Z) := (pR r ∘ projection) ⁻¹' VR r ((c q).m r)
    have hW : IsClopen W := (hVR r _).preimage ((hpR r).comp hprojection)
    have htNull : t.totalVariation Wᶜ = 0 := support_null (pR r ∘ projection)
      ((hpR r).comp hprojection) t (nuR r (rho q) ((c q).m r)) htmap htmass
      (hVR r _) (hRnull r (rho q) _)
    have hLeft : MeasurableSet (side ∩ projection ⁻¹' A) :=
      (hside.inter (hA.preimage hprojection)).isClosed.measurableSet
    have hRight : MeasurableSet (projection ⁻¹' (A ∩ U q)) :=
      ((hA.inter (hUclopen q)).preimage hprojection).isClosed.measurableSet
    have heq : (side ∩ projection ⁻¹' A) ∩ W = projection ⁻¹' (A ∩ U q) ∩ W := by
      ext x
      constructor
      · rintro ⟨⟨hxSide, hxA⟩, hxW⟩
        exact ⟨⟨hxA, ((haux r q hq).2.2.2 x hxW).mp hxSide⟩, hxW⟩
      · rintro ⟨⟨hxA, hxU⟩, hxW⟩
        exact ⟨⟨((haux r q hq).2.2.2 x hxW).mpr hxU, hxA⟩, hxW⟩
    calc
      t (side ∩ projection ⁻¹' A) = t ((side ∩ projection ⁻¹' A) ∩ W) :=
        apply_eq_inter_of_null_compl t hLeft hW.isClosed.measurableSet htNull
      _ = t (projection ⁻¹' (A ∩ U q) ∩ W) := congrArg t heq
      _ = t (projection ⁻¹' (A ∩ U q)) :=
        (apply_eq_inter_of_null_compl t hRight hW.isClosed.measurableSet htNull).symm
      _ = (t.map projection) (A ∩ U q) :=
        (VectorMeasure.map_apply t hprojection.measurable
          (hA.inter (hUclopen q)).isClosed.measurableSet).symm
  have hF : ∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
      (∀ k, rho (phi k) = d) → ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
      (∀ k, (sigma k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r)) →
      (∀ k, (sigma k).totalVariation univ = (nuR r d ((c (phi k)).m r)).totalVariation univ) →
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
          atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    intro r d phi hphi hlabel sigma hmap hmass
    let mid : ℕ → SignedMeasure K := fun k => (sigma k).map projection
    have hmid (k : ℕ) := map_mass_through_factor projection hprojection.measurable
      (pR r) (hpR r).measurable (sigma k) (nuR r d ((c (phi k)).m r)) (hmap k) (hmass k)
    have hmap' (k : ℕ) : (sigma k).map (pR r ∘ projection) =
        nuR r (rho (phi k)) ((c (phi k)).m r) := by rw [hlabel k]; exact hmap k
    have hmass' (k : ℕ) : (sigma k).totalVariation univ =
        (nuR r (rho (phi k)) ((c (phi k)).m r)).totalVariation univ := by
      rw [hlabel k]; exact hmass k
    have herror (k : ℕ) (A : Set K)
        (hgen : ∀ x y, (∀ C ∈ (c (phi k)).F, x ∈ C ↔ y ∈ C) → (x ∈ A ↔ y ∈ A)) :
        |mid k A - muR r d A| < (1 / 2 : ℝ) ^ phi k := by
      have hm := hmid k
      have hmmap : (mid k).map (pR r) = nuR r (rho (phi k)) ((c (phi k)).m r) := by
        rw [hlabel k]; exact hm.1
      have hmmass : (mid k).totalVariation univ =
          (nuR r (rho (phi k)) ((c (phi k)).m r)).totalVariation univ := by
        rw [hlabel k]; exact hm.2
      have he := (((hstep (phi k)).2.2.2.2.2 r).2.2.2.2 (mid k) hmmap hmmass).2 A hgen
      simpa only [hlabel k] using he
    have heps : Tendsto (fun k => (1 / 2 : ℝ) ^ phi k) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).comp hphi.tendsto_atTop
    have hbound : ∀ k, (sigma k).totalVariation.real univ ≤ 1 := by
      intro k
      simpa only [Measure.real, hmass k] using hRbound r d ((c (phi k)).m r)
    letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
    apply SignedSplitReferenceConvergence.exists_signed_limit_of_reference Y Z hY hZ
      1 (by norm_num) sigma hbound (muR r d) (fun k => U (phi k))
      (fun k => (hUclopen _).isClosed.measurableSet) (hUmono.comp hphi.monotone)
      (fun k => (1 / 2 : ℝ) ^ phi k) heps
    · intro A hA
      obtain ⟨j, hj⟩ := hB ⟨A, hA⟩
      have herrorA : ∀ᶠ k in atTop, |mid k A - muR r d A| ≤ (1 / 2 : ℝ) ^ phi k := by
        filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop j)] with k hk
        have hAF : (⟨A, hA⟩ : TopologicalSpace.Clopens K) ∈ (c (phi k)).F := by
          simpa only [hj] using (htests j (phi k) hk).2
        apply (herror k A ?_).le
        intro x y hxy
        exact hxy ⟨A, hA⟩ hAF
      have hz : Tendsto (fun k => mid k A - muR r d A) atTop (𝓝 0) :=
        squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using herrorA) heps
      change Tendsto (fun k => mid k A) atTop (𝓝 (muR r d A))
      simpa only [sub_add_cancel, zero_add] using hz.add_const (muR r d A)
    · intro A hA
      obtain ⟨j, hj⟩ := hB ⟨A, hA⟩
      filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop j),
        hphi.tendsto_atTop.eventually (eventually_gt_atTop (code r))] with k hk hcodek
      have hAF : (⟨A, hA⟩ : TopologicalSpace.Clopens K) ∈ (c (phi k)).F := by
        simpa only [hj] using (htests j (phi k) hk).2
      change |sigma k (side ∩ projection ⁻¹' A) - muR r d (A ∩ U (phi k))| ≤ _
      rw [hSideRow r (phi k) hcodek (sigma k) (hmap' k) (hmass' k) A hA]
      apply (herror k (A ∩ U (phi k)) ?_).le
      intro x y hxy
      exact and_congr (hxy ⟨A, hA⟩ hAF) (hGenU (phi k) x y hxy)
  have hFuniform : ∀ (r : Rows) (d : Γ) (phi : ℕ → ℕ), StrictMono phi →
      (∀ k, rho (phi k) = d) →
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ k, (sigma k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r)) →
          (∀ k, (sigma k).totalVariation univ = (nuR r d ((c (phi k)).m r)).totalVariation univ) →
          Tendsto (fun k => (NormPreservingLifts.signedFunctional (sigma k)).toWeakDual)
            atTop (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    intro r d phi hphi hlabel
    by_cases hex : ∃ ref : ℕ → SignedMeasure (splitCarrier Y Z),
        (∀ k, (ref k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r)) ∧
        (∀ k, (ref k).totalVariation univ = (nuR r d ((c (phi k)).m r)).totalVariation univ)
    · obtain ⟨ref, hrefmap, hrefmass⟩ := hex
      obtain ⟨mu, hbound, hpos, hneg, hrefconv⟩ := hF r d phi hphi hlabel ref hrefmap hrefmass
      refine ⟨mu, hbound, hpos, hneg, ?_⟩
      intro sigma hmap hmass
      obtain ⟨mu', _, _, _, hconv⟩ := hF r d phi hphi hlabel sigma hmap hmass
      let mix : ℕ → SignedMeasure (splitCarrier Y Z) :=
        fun k => if k % 2 = 0 then ref k else sigma k
      have hmixmap (k : ℕ) : (mix k).map (pR r ∘ projection) = nuR r d ((c (phi k)).m r) := by
        dsimp only [mix]
        split_ifs
        · exact hrefmap k
        · exact hmap k
      have hmixmass (k : ℕ) : (mix k).totalVariation univ =
          (nuR r d ((c (phi k)).m r)).totalVariation univ := by
        dsimp only [mix]
        split_ifs
        · exact hrefmass k
        · exact hmass k
      obtain ⟨mixmu, _, _, _, hmixconv⟩ := hF r d phi hphi hlabel mix hmixmap hmixmass
      have heven : StrictMono (fun k : ℕ => 2 * k) := fun a b hab => by
        change 2 * a < 2 * b
        omega
      have hodd : StrictMono (fun k : ℕ => 2 * k + 1) := fun a b hab => by
        change 2 * a + 1 < 2 * b + 1
        omega
      have heq : (NormPreservingLifts.signedFunctional mu).toWeakDual =
          (NormPreservingLifts.signedFunctional mixmu).toWeakDual := by
        apply tendsto_nhds_unique (hrefconv.comp heven.tendsto_atTop)
        simpa only [Function.comp_def, mix, Nat.mul_mod_right, ite_true] using
          hmixconv.comp heven.tendsto_atTop
      have heq' : (NormPreservingLifts.signedFunctional mu').toWeakDual =
          (NormPreservingLifts.signedFunctional mixmu).toWeakDual := by
        apply tendsto_nhds_unique (hconv.comp hodd.tendsto_atTop)
        simpa [Function.comp_def, mix] using hmixconv.comp hodd.tendsto_atTop
      rwa [heq'.trans heq.symm] at hconv
    · refine ⟨0, ?_, ?_, ?_, ?_⟩
      · norm_num [SignedMeasure.totalVariation_zero, Measure.real]
      · simpa only [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_posPart]
          using (inferInstance : Measure.Regular (0 : Measure (splitCarrier Y Z)))
      · simpa only [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_negPart]
          using (inferInstance : Measure.Regular (0 : Measure (splitCarrier Y Z)))
      · intro sigma hmap hmass
        exact (hex ⟨sigma, hmap, hmass⟩).elim
  let I : Rows → Set ℕ := fun r => {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
    (r = targetRow ∧ ∃ q, (c q).n = n)}
  let J : Rows → Γ → Set ℕ := fun r d =>
    {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}
  let N : Rows → Γ → Fin 2 → Set ℕ := fun r d e =>
    if hr : r = newRow then {n | ∃ q, code r < q ∧ rho q = d ∧
      q % 2 = (e : ℕ) ∧ (c q).m r = n}
    else oldN r hr d e
  have hJsub (r : Rows) (d : Γ) : J r d ⊆ I r := by
    rintro n ⟨q, hq, _, rfl⟩
    exact Or.inl ⟨q, hq, rfl⟩
  have hOldPool (r : Rows) (hr : r ≠ newRow) (q : ℕ) :
      (c q).m r ∈ oldJ r hr (rho q) ∩
        oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩ := by
    have hmem := ((hstep q).2.2.2.2.2 r).1
    simpa only [pool, ordinaryPool, dif_neg hr] using hmem
  have hNold (r : Rows) (hr : r ≠ newRow) (d : Γ) (e : Fin 2) :
      N r d e = oldN r hr d e := by simp only [N, dif_neg hr]
  have hNnew (d : Γ) (e : Fin 2) : N newRow d e =
      {n | ∃ q, code newRow < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧ (c q).m newRow = n} := by
    simp only [N, dif_pos rfl]
  have hNdis (r : Rows) (d : Γ) : Disjoint (N r d 0) (N r d 1) := by
    by_cases hr : r = newRow
    · simp only [N, dif_pos hr]
      rw [Set.disjoint_left]
      rintro n ⟨q, _, _, hq, heq⟩ ⟨s, _, _, hs, hes⟩
      have hqs : q = s := (hm r).injective (heq.trans hes.symm)
      subst s
      change q % 2 = 0 at hq
      change q % 2 = 1 at hs
      omega
    · rw [hNold r hr, hNold r hr]
      exact hOldB r hr d
  have hC (r : Rows) (d : Γ) (e : Fin 2) : (J r d ∩ N r d e).Infinite := by
    have hinf : {q | code r < q ∧ rho q = d ∧ q % 2 = (e : ℕ)}.Infinite := by
      have h := (hRho d e).diff (Set.finite_Iic (code r))
      exact h.mono (fun q hq => ⟨by simpa only [Set.mem_Iic, not_le] using hq.2,
        hq.1.1, hq.1.2⟩)
    apply (hinf.image (hm r).injective.injOn).mono
    rintro n ⟨q, ⟨hq, hlabel, hparity⟩, rfl⟩
    refine ⟨⟨q, hq, hlabel, rfl⟩, ?_⟩
    by_cases hr : r = newRow
    · simp only [N, dif_pos hr]
      exact ⟨q, hq, hlabel, hparity, rfl⟩
    · rw [hNold r hr]
      have he : (⟨q % 2, Nat.mod_lt q (by decide)⟩ : Fin 2) = e := Fin.ext hparity
      have hmem := (hOldPool r hr q).2
      simpa only [hlabel, he] using hmem
  have hIinf (r : Rows) : (I r).Infinite :=
    (hC r (rho 0) 0).mono (fun _ hn => hJsub r (rho 0) hn.1)
  have hIold (r : Rows) (hr : r ≠ newRow) : I r ⊆ oldI r hr := by
    rintro n (⟨q, _, rfl⟩ | ⟨rfl, q, rfl⟩)
    · exact hOldA r hr (rho q) (hOldPool r hr q).1
    · exact hTargetPool hr (hSsub (hstep q).2.1)
  have hJold (r : Rows) (hr : r ≠ newRow) (d : Γ) : J r d ⊆ oldJ r hr d := by
    rintro n ⟨q, _, hlabel, rfl⟩
    simpa only [hlabel] using (hOldPool r hr q).1
  have hFullE (r : Rows) (A : Set K) (hA : IsClopen A) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
        pR r x.1.1 = pR r y.1.1 →
        (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2 := by
    obtain ⟨j, hj⟩ := hB ⟨A, hA⟩
    let Q := max j (code r + 1)
    have htargetE := eventually_clopen_fibre (atTop ⊓ 𝓟 S) coord hsep p V hE hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_inf_principal.mp htargetE)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (max M ((c Q).m r))] with n hn hnI
    intro x y hx hy hxy
    rcases hnI with ⟨q, hq, rfl⟩ | ⟨rfl, q, rfl⟩
    · have hQq : Q ≤ q := by
        by_contra hnq
        have hlt := hm r (lt_of_not_ge hnq)
        exact (not_lt_of_ge (le_trans (le_max_right M _) hn)) hlt
      have hAF : (⟨A, hA⟩ : TopologicalSpace.Clopens K) ∈ (c q).F := by
        simpa only [hj] using (htests j q ((le_max_left j _).trans hQq)).2
      refine ⟨?_, hnewAux r q hq x y hx hy hxy⟩
      exact ((hstep q).2.2.2.2.2 r).2.2.2.1 ⟨A, hA⟩ hAF x.1.1 y.1.1 hx hy hxy
    · have hx' : p x.1.1 ∈ V (c q).n := by
        change x.1.1 ∈ p ⁻¹' V (c q).n
        rw [← hTargetSupport]
        exact hx
      have hy' : p y.1.1 ∈ V (c q).n := by
        change y.1.1 ∈ p ⁻¹' V (c q).n
        rw [← hTargetSupport]
        exact hy
      have hxy' := hTargetFibre x.1.1 y.1.1 hxy
      exact ⟨hM _ ((le_max_left M _).trans hn) (hstep q).2.1 x.1.1 y.1.1 hx' hy' hxy',
        hnewTarget q x y hx' hy' hxy'⟩
  have hFJ (r : Rows) (d : Γ) :
      ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (pR r ∘ projection) = nuR r d n) →
          (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    let P : Set ℕ := {q | code r < q ∧ rho q = d}
    have hP : P.Infinite := by
      apply ((hRho d 0).diff (Set.finite_Iic (code r))).mono
      intro q hq
      exact ⟨by simpa only [Set.mem_Iic, not_le] using hq.2, hq.1.1⟩
    letI : Infinite P := Set.infinite_coe_iff.mpr hP
    let phi : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet P
    have hphiRange : Set.range phi = P := Nat.orderEmbeddingOfSet_range P
    have hphiMem (k : ℕ) : phi k ∈ P := hphiRange ▸ Set.mem_range_self k
    have hlabel (k : ℕ) : rho (phi k) = d := (hphiMem k).2
    let psi : ℕ → ℕ := fun k => (c (phi k)).m r
    have hpsi : StrictMono psi := (hm r).comp phi.strictMono
    have hpsiRange : Set.range psi = J r d := by
      ext n
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨phi k, (hphiMem k).1, hlabel k, rfl⟩
      · rintro ⟨q, hq, hlabelq, hqn⟩
        obtain ⟨k, rfl⟩ : q ∈ Set.range phi := hphiRange.symm ▸ ⟨hq, hlabelq⟩
        exact ⟨k, hqn⟩
    obtain ⟨mu, hmu, hpos, hneg, hall⟩ := hFuniform r d phi phi.strictMono hlabel
    refine ⟨mu, hmu, hpos, hneg, ?_⟩
    intro sigma hmap hmass
    have hconv := hall (fun k => sigma (psi k)) (fun k => hmap (psi k))
      (fun k => hmass (psi k))
    apply Filter.tendsto_def.mpr
    intro A hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hconv.eventually hA)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (psi M)] with n hn hnJ
    obtain ⟨k, rfl⟩ : n ∈ Set.range psi := hpsiRange.symm ▸ hnJ
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hpsi (lt_of_not_ge hk))
    exact hM k hMk
  let splitCoord : Option Γ → C(splitCarrier Y Z, Bool) := fun c =>
    match c with
    | none => ⟨fun x => x.1.2, continuous_snd.comp continuous_subtype_val⟩
    | some c => ⟨fun x => coord c x.1.1, (coord c).continuous.comp hprojection⟩
  have hSplitSep : Function.Injective
      (fun x : splitCarrier Y Z => fun c => splitCoord c x) := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · apply hsep
      funext c
      exact congrFun hxy (some c)
    · exact congrFun hxy none
  have hSplitE (r : Rows) (c : Option Γ) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
        pR r x.1.1 = pR r y.1.1 → splitCoord c x = splitCoord c y := by
    cases c with
    | none =>
      filter_upwards [hFullE r ∅ isClopen_empty] with n hn
      intro x y hx hy hxy
      exact (hn x y hx hy hxy).2
    | some c =>
      let A : Set K := coord c ⁻¹' {true}
      have hA : IsClopen A := (isClopen_discrete ({true} : Set Bool)).preimage (coord c).continuous
      filter_upwards [hFullE r A hA] with n hn
      intro x y hx hy hxy
      apply bool_eq_of_true_iff
      change (coord c x.1.1 = true ↔ coord c y.1.1 = true)
      simpa only [A, mem_preimage, mem_singleton_iff] using (hn x y hx hy hxy).1
  have hLocE (r : Rows) (f : LocallyConstant (splitCarrier Y Z) ℝ) :
      ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
        pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
        pR r x.1.1 = pR r y.1.1 → f x = f y := by
    have hpieces : ∀ a ∈ f.range_finite.toFinset,
        ∀ᶠ n in atTop ⊓ 𝓟 (I r), ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
          pR r x.1.1 = pR r y.1.1 → (f x = a ↔ f y = a) := by
      intro a _
      exact eventually_clopen_fibre (atTop ⊓ 𝓟 (I r)) splitCoord hSplitSep
        (pR r ∘ projection) (VR r) (hSplitE r) (f.isLocallyConstant.isClopen_fiber a)
    filter_upwards [(Filter.eventually_all_finset f.range_finite.toFinset).mpr hpieces] with n hn
    intro x y hx hy hxy
    exact ((hn (f x) (f.range_finite.mem_toFinset.mpr ⟨x, rfl⟩) x y hx hy hxy).mp rfl).symm
  letI : MetricSpace (splitCarrier Y Z) := TopologicalSpace.metrizableSpaceMetric _
  have hResidualLifts (r : Rows) (n : ℕ) :=
    NormPreservingLiftExistence.exists_norm_preserving_lift (pR r ∘ projection)
      ((hpR r).comp hprojection) ((hpRsurj r).comp hsurj) (nuA r n)
  choose sA hsAmap hsAmass using hResidualLifts
  have hResidual (r : Rows) :
      ∃ (JA : Set ℕ) (NA : Fin 2 → Set ℕ) (mu : SignedMeasure (splitCarrier Y Z)),
        JA ⊆ I r ∧ Disjoint (NA 0) (NA 1) ∧
        (∀ e, NA e ⊆ JA) ∧ (∀ e, (JA ∩ NA e).Infinite) ∧
        mu.totalVariation.real univ ≤ 1 ∧
        Measure.Regular mu.toJordanDecomposition.posPart ∧
        Measure.Regular mu.toJordanDecomposition.negPart ∧
        ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
          (∀ n, (sigma n).map (pR r ∘ projection) = nuA r n) →
          (∀ n, (sigma n).totalVariation univ = (nuA r n).totalVariation univ) →
          Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
            (atTop ⊓ 𝓟 JA) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
    letI : Infinite (I r) := Set.infinite_coe_iff.mpr (hIinf r)
    let tau : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet (I r)
    have htauRange : Set.range tau = I r := Nat.orderEmbeddingOfSet_range (I r)
    have htauMem (k : ℕ) : tau k ∈ I r := htauRange ▸ Set.mem_range_self k
    have hbound (k : ℕ) : (sA r (tau k)).totalVariation.real univ ≤ 1 := by
      simpa only [Measure.real, hsAmass] using hAbound r (tau k)
    obtain ⟨phi, mu, hphi, hmu, hrefconv⟩ :=
      SignedWeakStarCompactness.exists_subsequence_tendsto_signedFunctional
        1 (by norm_num) (fun k => sA r (tau k)) hbound
    let psi : ℕ → ℕ := fun k => tau (phi k)
    have hpsi : StrictMono psi := tau.strictMono.comp hphi
    let JA : Set ℕ := Set.range psi
    let NA : Fin 2 → Set ℕ := fun e => Set.range (fun k => psi (2 * k + (e : ℕ)))
    have hJAsub : JA ⊆ I r := by
      rintro _ ⟨k, rfl⟩
      exact htauMem (phi k)
    have hNAsub (e : Fin 2) : NA e ⊆ JA := by
      rintro _ ⟨k, rfl⟩
      exact Set.mem_range_self (2 * k + (e : ℕ))
    have hNAinf (e : Fin 2) : (JA ∩ NA e).Infinite := by
      have hinj : Function.Injective (fun k => psi (2 * k + (e : ℕ))) :=
        hpsi.injective.comp (fun a b hab => by omega)
      apply (Set.infinite_range_of_injective hinj).mono
      rintro _ ⟨k, rfl⟩
      exact ⟨Set.mem_range_self (2 * k + (e : ℕ)), Set.mem_range_self k⟩
    have hNAdis : Disjoint (NA 0) (NA 1) := by
      rw [Set.disjoint_left]
      rintro n ⟨k, hk⟩ ⟨j, hj⟩
      have heq := hpsi.injective (hk.trans hj.symm)
      change 2 * k + 0 = 2 * j + 1 at heq
      omega
    refine ⟨JA, NA, mu, hJAsub, hNAdis, hNAsub, hNAinf, hmu, inferInstance, inferInstance, ?_⟩
    intro sigma hmap hmass
    have hfibre (f : LocallyConstant (splitCarrier Y Z) ℝ) :
        ∀ᶠ k in atTop, ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r (psi k) → pR r y.1.1 ∈ VR r (psi k) →
          pR r x.1.1 = pR r y.1.1 → f x = f y := by
      filter_upwards [hpsi.tendsto_atTop.eventually (eventually_inf_principal.mp (hLocE r f))]
        with k hk
      exact hk (hJAsub (Set.mem_range_self k))
    have hconv := NormPreservingLifts.arbitrary_lifts_tendsto atTop
      (pR r ∘ projection) ((hpR r).comp hprojection) (fun k => VR r (psi k))
      (fun k => hVR r (psi k)) (fun k => nuA r (psi k))
      (fun k => sA r (psi k)) (fun k => sigma (psi k))
      (fun k => hsAmap r (psi k)) (fun k => hmap (psi k))
      (fun k => hsAmass r (psi k)) (fun k => hmass (psi k))
      (fun k => hAnull r (psi k)) 1 (by norm_num) (fun k => hAbound r (psi k))
      hfibre (NormPreservingLifts.signedFunctional mu).toWeakDual hrefconv
    apply Filter.tendsto_def.mpr
    intro A hA
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hconv.eventually hA)
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (psi M)] with n hn hnJ
    obtain ⟨k, rfl⟩ := hnJ
    have hMk : M ≤ k := by
      by_contra hk
      exact (not_lt_of_ge hn) (hpsi (lt_of_not_ge hk))
    exact hM k hMk
  choose JA NA muA hJAsub hNAdis hNAsub hNAinf hmuA hmuApos hmuAneg hmuAF using hResidual
  have hBook : ∃ (I : Rows → Set ℕ) (J : Rows → Γ → Set ℕ) (N : Rows → Γ → Fin 2 → Set ℕ),
      (∀ r, I r = {n | (∃ q, code r < q ∧ (c q).m r = n) ∨
        (r = targetRow ∧ ∃ q, (c q).n = n)}) ∧
      (∀ r d, J r d = {n | ∃ q, code r < q ∧ rho q = d ∧ (c q).m r = n}) ∧
      (∀ r hr d e, N r d e = oldN r hr d e) ∧
      (∀ d e, N newRow d e =
        {n | ∃ q, code newRow < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧ (c q).m newRow = n}) ∧
      (∀ r d, J r d ⊆ I r) ∧
      (∀ r d, Disjoint (N r d 0) (N r d 1)) ∧
      (∀ r d e, (J r d ∩ N r d e).Infinite) ∧
      (∀ r, (I r).Infinite) ∧
      (∀ r hr, I r ⊆ oldI r hr) ∧
      (∀ r hr d, J r d ⊆ oldJ r hr d) ∧
      (∀ r (A : Set K), IsClopen A → ∀ᶠ n in atTop ⊓ 𝓟 (I r),
        ∀ x y : splitCarrier Y Z,
          pR r x.1.1 ∈ VR r n → pR r y.1.1 ∈ VR r n →
          pR r x.1.1 = pR r y.1.1 → (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2) ∧
      (∀ r d, ∃ mu : SignedMeasure (splitCarrier Y Z), mu.totalVariation.real univ ≤ 1 ∧
            Measure.Regular mu.toJordanDecomposition.posPart ∧
            Measure.Regular mu.toJordanDecomposition.negPart ∧
            ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
              (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuR r d n) →
              (∀ n, (sigma n).totalVariation univ = (nuR r d n).totalVariation univ) →
              Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                (atTop ⊓ 𝓟 (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)) ∧
          (∃ (JA : Rows → Set ℕ) (NA : Rows → Fin 2 → Set ℕ)
              (muA : Rows → SignedMeasure (splitCarrier Y Z)),
            ∀ r, JA r ⊆ I r ∧ Disjoint (NA r 0) (NA r 1) ∧
              (∀ e, NA r e ⊆ JA r) ∧ (∀ e, (JA r ∩ NA r e).Infinite) ∧
              (muA r).totalVariation.real univ ≤ 1 ∧
              Measure.Regular (muA r).toJordanDecomposition.posPart ∧
              Measure.Regular (muA r).toJordanDecomposition.negPart ∧
              ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
                (∀ n, (sigma n).map (fun x => pR r x.1.1) = nuA r n) →
                (∀ n, (sigma n).totalVariation univ = (nuA r n).totalVariation univ) →
                Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
                  (atTop ⊓ 𝓟 (JA r))
                  (𝓝 (NormPreservingLifts.signedFunctional (muA r)).toWeakDual)) :=
    ⟨I, J, N, fun _ => rfl, fun _ _ => rfl, hNold, hNnew, hJsub, hNdis, hC, hIinf, hIold, hJold, hFullE, hFJ,
      JA, NA, muA, fun r => ⟨hJAsub r, hNAdis r, hNAsub r, hNAinf r,
        hmuA r, hmuApos r, hmuAneg r, hmuAF r⟩⟩
  exact ⟨S, vP, hSsub, hS, href, birthS, birthMu, hBirthS, hBirthData,
    fun q => (hist q).val, c, hsuc, hstep, hn, hm, htests, havoid,
    Y, Z, hclosed, hY, hZ, hcov, hZdef, hYdef, hclosed, hsurj, haux, htarget, hnewAux,
    hnewTarget, hG, hGinf, hFuniform, hBook⟩

end D5.S3.Topology.Measures.SignedSplitSuccessor
