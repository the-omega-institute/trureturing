/- GID: D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native Borel failure composition and repeated early and late marked laws. -/

import D5.S3.Quantum.Fibers.OriginalRepeatedPrefix
import Mathlib.MeasureTheory.Group.LIntegral

noncomputable section
namespace D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw
open Set Filter Topology MeasureTheory intervalIntegral
open OriginalControlComposition OriginalControlMarkedJump OriginalMarkedConcatenation
open OriginalRepeatedPrefix
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The native sum of failure integrals for an actual record event. -/
def F (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) (k : ℝ → ℝ)
    (A : Set Leg.Record) : ℝ≥0∞ :=
  ∑ i : Fin 5, ∫⁻ t in (Ioc 0 T) ∩ {t | Sum.inr (i,t) ∈ A},
    ENNReal.ofReal (failureDensity c a beta m theta k i t)

/-- Pullback of an event by the actual translation of its failure clock. -/
def shift (T : ℝ) (A : Set Leg.Record) : Set Leg.Record :=
  (fun r => r.map id (fun z => (z.1,z.2+T))) ⁻¹' A

private theorem shift_measurable (T : ℝ) {A : Set Leg.Record} (hA : MeasurableSet A) :
    MeasurableSet (shift T A) := by
  apply hA.preimage
  exact measurable_id.sumMap (measurable_fst.prodMk (measurable_snd.add_const T))

private theorem translate_integral (T U : ℝ) (f : ℝ → ℝ≥0∞)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫⁻ t in (Ioc T (T+U)) ∩ A, f (t-T)) =
      ∫⁻ s in (Ioc 0 U) ∩ {s | s+T ∈ A}, f s := by
  rw [← lintegral_indicator (measurableSet_Ioc.inter hA),
    ← lintegral_add_right_eq_self _ T]
  rw [← lintegral_indicator (measurableSet_Ioc.inter (hA.preimage (measurable_id.add_const T)))]
  apply lintegral_congr
  intro s
  have he : s+T ∈ (Ioc T (T+U)) ∩ A ↔ s ∈ (Ioc 0 U) ∩ {s | s+T ∈ A} := by
    simp only [mem_inter_iff,mem_Ioc,mem_setOf_eq]
    constructor <;> rintro ⟨⟨h1,h2⟩,h3⟩ <;> exact ⟨⟨by linarith,by linarith⟩,h3⟩
  simp only [Set.indicator_apply,he,add_sub_cancel_right]

private theorem raw_density (c a k S beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (g : Fin 5 → ℝ) (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (hk : k ∈ Ioo 0 c)
    (hS : 0 ≤ S) (i : Fin 5) :
    Complex.normSq ((jumpKraus c a k S g i *ᵥ source c a beta m theta) 0) =
      (Real.sqrt (g i))^2 * S * p c k i := by
  rw [jump_action]
  simp only [jump,live,Complex.normSq_mul,Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt hS,
    Real.mul_self_sqrt (div_nonneg (p_pos c k hc hk i).le (p_pos c a hc ha i).le),
    source_diagonal c a beta m theta hc ha]
  field_simp [(p_pos c a hc ha i).ne']
  <;> ring

private theorem native_bounds (c U chi : ℝ) (k : ℝ → ℝ)
    (hk : OriginalControl (c,c,1-2*c) U k (fun _ => chi))
    (t : ℝ) (ht : t ∈ Icc 0 U) : k t ∈ Ioo 0 c := by
  have hl : FiniteRectangleTransport.lower (c,c,1-2*c)=0 := by
    dsimp [FiniteRectangleTransport.lower]; ring_nf; simp
  simpa [hl,FiniteRectangleTransport.upper,uIcc_of_le hk.1] using hk.2.2.2.1 t ht

private theorem survival_after (c T U chi : ℝ) (k K : ℝ → ℝ)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hj : k T=K 0)
    (h0 : OriginalControl (c,c,1-2*c) T k (fun _ => chi))
    (h1 : OriginalControl (c,c,1-2*c) U K (fun _ => chi))
    (s : ℝ) (hs : s ∈ Icc 0 U) :
    survival c (concatenate k K T) (T+s)=survival c k T*survival c K s := by
  have hi := hazard_integrable c T chi k h0
  have hI := (hazard_integrable c U chi K h1).mono_set
    (by rw [uIcc_of_le hs.1,uIcc_of_le hU]; exact Icc_subset_Icc le_rfl hs.2)
  rw [survival,hazard_integral c T s k K hT hs.1 hj hi hI,neg_add,Real.exp_add]
  rfl

/-- The actual native failure measure composes with its unnormalized survival
weight and the translated second clock. No density identity is a premise. -/
theorem failure_join (c a b beta T U chi : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k K : ℝ → ℝ) (hc : c<1/2) (ha : a ∈ Ioo 0 c) (hb : b ∈ Ioo 0 c)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hj : k T=K 0)
    (h0 : OriginalControl (c,c,1-2*c) T k (fun _ => chi))
    (h1 : OriginalControl (c,c,1-2*c) U K (fun _ => chi))
    (A : Set Leg.Record) (hA : MeasurableSet A) :
    F c a beta (T+U) m theta (concatenate k K T) A =
      F c a beta T m theta k A + ENNReal.ofReal (survival c k T)*
        F c b beta U m theta K (shift T A) := by
  have hm (i : Fin 5) : MeasurableSet {t : ℝ | Sum.inr (i,t) ∈ A} :=
    hA.preimage (measurable_inr.comp (measurable_const.prodMk measurable_id))
  have split (i : Fin 5) :
      (∫⁻ t in (Ioc 0 (T+U)) ∩ {t | Sum.inr (i,t) ∈ A},
        ENNReal.ofReal (failureDensity c a beta m theta (concatenate k K T) i t)) =
      (∫⁻ t in (Ioc 0 T) ∩ {t | Sum.inr (i,t) ∈ A},
        ENNReal.ofReal (failureDensity c a beta m theta k i t)) +
      ENNReal.ofReal (survival c k T)*
        (∫⁻ s in (Ioc 0 U) ∩ {s | Sum.inr (i,s+T) ∈ A},
          ENNReal.ofReal (failureDensity c b beta m theta K i s)) := by
    rw [show (Ioc 0 (T+U)) ∩ {t | Sum.inr (i,t) ∈ A} =
      ((Ioc 0 T) ∩ {t | Sum.inr (i,t) ∈ A}) ∪
      ((Ioc T (T+U)) ∩ {t | Sum.inr (i,t) ∈ A}) by
        rw [← Ioc_union_Ioc_eq_Ioc hT (le_add_of_nonneg_right hU),union_inter_distrib_right],
      lintegral_union (measurableSet_Ioc.inter (hm i)) (by
        apply Disjoint.mono inter_subset_left inter_subset_left
        exact Ioc_disjoint_Ioc_of_le le_rfl)]
    congr 1
    · apply setLIntegral_congr_fun_ae (measurableSet_Ioc.inter (hm i))
      filter_upwards [volume.ae_ne T] with t ht hmem
      have htT : t<T := lt_of_le_of_ne hmem.1.2 ht
      simp only [failureDensity,survival_before c T t k K hmem.1.1.le hmem.1.2,
        rate_before c T k K t htT,concatenate,if_pos hmem.1.2]
    · rw [← translate_integral T U (fun s => ENNReal.ofReal
        (failureDensity c b beta m theta K i s)) _ (hm i),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun (measurableSet_Ioc.inter (hm i))
      intro t ht
      have hs : t-T ∈ Icc 0 U := ⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩
      have hS := survival_after c T U chi k K hT hU hj h0 h1 (t-T) hs
      rw [add_sub_cancel T t] at hS
      have hh : concatenate k K T t=K (t-T) := by
        simp [concatenate,not_le.mpr ht.1.1,hj]
      simp only [failureDensity,hh,hS,rate_after c T k K hj t ht.1.1]
      rw [raw_density c a _ _ beta m theta _ hc ha (native_bounds c U chi K h1 _ hs)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
        raw_density c b _ _ beta m theta _ hc hb (native_bounds c U chi K h1 _ hs)
        (Real.exp_pos _).le,← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
  unfold F
  simp_rw [split]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  rfl


private theorem native_law_apply (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (hc : c<1/2) (ha : a ∈ Ioo 0 c) (hk : k T ∈ Ioo 0 c)
    (A : Set Leg.Record) (hA : MeasurableSet A) :
    markedLaw c a beta T m theta k A =
      (if Sum.inl () ∈ A then ENNReal.ofReal (survival c k T) else 0)+
        F c a beta T m theta k A := by
  rw [OriginalMarkedConcatenation.markedLaw_apply _ _ _ _ _ _ _ A hA,
    source_live_mass c a (k T) (survival c k T) beta m theta hc ha hk (Real.exp_pos _).le]
  rfl

private def Balance (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) (k : ℝ → ℝ) : Prop :=
  ENNReal.ofReal (survival c k T)+F c a beta T m theta k univ=1

private theorem balance_leg (L : Leg) (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) :
    Balance L.c L.x beta L.duration m theta L.height := by
  have h := (L.affine_marked_probability 0 beta m theta).2.2.2.2.2.2.2
  haveI := h.1
  have he := h.2 univ MeasurableSet.univ
  simp only [measure_univ,mem_univ,if_true] at he
  have hend : L.height L.duration=L.y := by
    dsimp [Leg.height,Leg.speed]
    field_simp [L.duration_pos.ne']
    <;> ring
  rw [source_live_mass L.c L.x L.y (L.survival L.duration) beta m theta L.c_lt
    ⟨L.x_pos,L.x_lt⟩ ⟨L.y_pos,L.y_lt⟩ (Real.exp_pos _).le] at he
  simpa only [Balance,F,leg_survival,hend] using he.symm

private theorem balance_join (c a b beta T U : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k K : ℝ → ℝ) (hc : c<1/2) (ha : a ∈ Ioo 0 c) (hb : b ∈ Ioo 0 c)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hj : k T=K 0)
    (h0 : OriginalControl (c,c,1-2*c) T k (fun _ => (0:ℝ)))
    (h1 : OriginalControl (c,c,1-2*c) U K (fun _ => (0:ℝ)))
    (hB0 : Balance c a beta T m theta k) (hB1 : Balance c b beta U m theta K) :
    Balance c a beta (T+U) m theta (concatenate k K T) := by
  unfold Balance at *
  rw [failure_join c a b beta T U 0 m theta k K hc ha hb hT hU hj h0 h1 univ MeasurableSet.univ]
  have hs := survival_after c T U 0 k K hT hU hj h0 h1 U ⟨hU,le_rfl⟩
  rw [hs,ENNReal.ofReal_mul (Real.exp_pos _).le]
  change ENNReal.ofReal (survival c k T)*ENNReal.ofReal (survival c K U)+
    (F c a beta T m theta k univ+ENNReal.ofReal (survival c k T)*F c b beta U m theta K univ)=1
  calc
    _ = F c a beta T m theta k univ + ENNReal.ofReal (survival c k T)*
        (ENNReal.ofReal (survival c K U)+F c b beta U m theta K univ) := by ring
    _ = 1 := by rw [hB1,mul_one,add_comm,hB0]

namespace Band
private theorem loop_balance (B : Band) (d : ℝ) (hd : 0<d)
    (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) :
    Balance B.c B.a beta (2*d) m theta (B.loop d hd) := by
  have hu := balance_leg (B.up d hd) beta m theta
  have hv := balance_leg (B.down d hd) beta m theta
  have hj : (B.up d hd).height d=(B.down d hd).height 0 := by
    dsimp [Band.up,Band.down,Leg.height,Leg.speed]
    field_simp [hd.ne']
    <;> ring
  have h := balance_join B.c B.a B.b beta d d m theta _ _ B.c_lt
    ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos.trans B.ab,B.bc⟩ hd.le hd.le hj
    ((B.up d hd).affine_marked_probability 0 beta m theta).1
    ((B.down d hd).affine_marked_probability 0 beta m theta).1 hu hv
  simpa only [← two_mul,Band.loop] using h

private theorem prefix_balance (B : Band) (d : ℝ) (hd : 0<d) (j : ℕ)
    (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) :
    Balance B.c B.a beta (2*(j:ℝ)*d) m theta (B.repeated d hd j) := by
  induction j with
  | zero => simp [Balance,F,survival]
  | succ j ih =>
    obtain ⟨hp,hp0,hp1,hps⟩ := B.prefix_facts d 0 hd j
    have hj : B.repeated d hd j (2*(j:ℝ)*d)=B.loop d hd 0 := by rw [hp1,B.loop_zero]
    have he : 2*((j+1:ℕ):ℝ)*d=2*(j:ℝ)*d+2*d := by push_cast; ring
    simpa only [he,Band.repeated] using
      balance_join B.c B.a B.a beta _ (2*d) m theta _ _ B.c_lt
        ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos,B.ab.trans B.bc⟩ (by positivity) (by positivity)
        hj hp (B.loop_control d 0 hd) ih (B.loop_balance d hd beta m theta)

private theorem suffix_balance (B : Band) (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (e : Bool) :
    Balance B.c B.a beta 1 m theta (if e then B.earlySuffix else B.lateSuffix) := by
  have hl := B.loop_balance (1/4) (by norm_num) beta m theta
  have hw := balance_leg B.wait beta m theta
  have hc := B.loop_control (1/4) 0 (by norm_num)
  have hz := B.loop_zero (1/4) (by norm_num)
  have he := B.loop_end (1/4) (by norm_num)
  rw [show (2:ℝ)*(1/4)=1/2 by norm_num] at hl hc he
  obtain ⟨hwo,hw0,hw1,hws⟩ := B.wait_facts 0
  cases e <;> simp only [Bool.false_eq_true,↓reduceIte]
  · have hj := hw1.trans hz.symm
    have h := balance_join B.c B.a B.a beta (1/2) (1/2) m theta _ _ B.c_lt
      ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos,B.ab.trans B.bc⟩ (by norm_num) (by norm_num)
      hj hwo hc hw hl
    norm_num only at h
    exact h
  · have hj := he.trans hw0.symm
    have h := balance_join B.c B.a B.a beta (1/2) (1/2) m theta _ _ B.c_lt
      ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos,B.ab.trans B.bc⟩ (by norm_num) (by norm_num)
      hj hc hwo hl hw
    norm_num only at h
    exact h
end Band

/-- Every n uses the existing repeated heights and native Kraus law. The same
source is retained through the prefix, with its actual q^n survival weight. -/
theorem early_late_marked_probability (B : Band) (n : ℕ) (hn : 1≤n)
    (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) :
    ∀ e : Bool,
      let k := if e then B.early n hn else B.late n hn
      let H := if e then B.earlySuffix else B.lateSuffix
      IsProbabilityMeasure (markedLaw B.c B.a beta 2 m theta k) ∧
      ∀ A : Set Leg.Record, MeasurableSet A →
        markedLaw B.c B.a beta 2 m theta k A =
          (if Sum.inl () ∈ A then ENNReal.ofReal (B.q^(n+1)) else 0)+
          F B.c B.a beta 1 m theta
            (B.repeated (Band.halfStep n) (Band.halfStep_pos n hn) n) A+
          ENNReal.ofReal (B.q^n)*F B.c B.a beta 1 m theta H (shift 1 A) := by
  intro e
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have ht : 2*(n:ℝ)*Band.halfStep n=1 := by dsimp [Band.halfStep]; field_simp
  obtain ⟨hp,hp0,hp1,hps⟩ := B.prefix_facts (Band.halfStep n) 0 (Band.halfStep_pos n hn) n
  rw [ht] at hp hp1 hps
  obtain ⟨hs,hs0,hs1,hss⟩ := B.suffix_facts 0 e
  have hbp := B.prefix_balance (Band.halfStep n) (Band.halfStep_pos n hn) n beta m theta
  rw [ht] at hbp
  have hbs := B.suffix_balance beta m theta e
  have hj := hp1.trans hs0.symm
  have hB := balance_join B.c B.a B.a beta 1 1 m theta _ _ B.c_lt
    ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos,B.ab.trans B.bc⟩ zero_le_one zero_le_one
    hj hp hs hbp hbs
  norm_num only at hB
  have hf := failure_join B.c B.a B.a beta 1 1 0 m theta _ _ B.c_lt
    ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos,B.ab.trans B.bc⟩ zero_le_one zero_le_one hj hp hs
  norm_num only at hf
  have hsall := early_late_native_survival B n hn 0
  have hend : (if e then B.early n hn else B.late n hn) 2=B.a := by
    cases e <;> simp_all only [Bool.false_eq_true,↓reduceIte]
    · exact hsall.2.2.2.2.2.2.2.2.1
    · exact hsall.2.2.2.2.2.2.2.1
  have hsurv : survival B.c (if e then B.early n hn else B.late n hn) 2=B.q^(n+1) := by
    cases e <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact hsall.2.2.2.2.2.2.2.2.2.2.1
    · exact hsall.2.2.2.2.2.2.2.2.2.1
  have hconcat : concatenate (B.repeated (Band.halfStep n) (Band.halfStep_pos n hn) n)
      (if e then B.earlySuffix else B.lateSuffix) 1 =
      (if e then B.early n hn else B.late n hn) := by cases e <;> rfl
  rw [hconcat] at hB hf
  refine ⟨isProbabilityMeasure_iff.mpr ?_,?_⟩
  · rw [native_law_apply _ _ _ _ _ _ _ B.c_lt ⟨B.a_pos,B.ab.trans B.bc⟩
      (by rw [hend]; exact ⟨B.a_pos,B.ab.trans B.bc⟩) univ MeasurableSet.univ]
    exact hB
  · intro A hA
    rw [native_law_apply _ _ _ _ _ _ _ B.c_lt ⟨B.a_pos,B.ab.trans B.bc⟩
      (by rw [hend]; exact ⟨B.a_pos,B.ab.trans B.bc⟩) A hA,hsurv,hf A hA,hps,add_assoc]


/-- Probability total variation is the supremum over all measurable events. -/
def eventTV (mu nu : Measure Leg.Record) : ℝ :=
  sSup {x : ℝ | ∃ A : Set Leg.Record, MeasurableSet A ∧ x=|(mu A).toReal-(nu A).toReal|}

private theorem F_mono (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) {A D : Set Leg.Record} (h : A⊆D) :
    F c a beta T m theta k A ≤ F c a beta T m theta k D := by
  apply Finset.sum_le_sum
  intro i hi
  apply lintegral_mono_set
  rintro t ⟨ht,hA⟩
  exact ⟨ht,h hA⟩

private theorem F_zero (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (A : Set Leg.Record)
    (h : ∀ (i : Fin 5) (t : ℝ), t ∈ Ioc 0 T → Sum.inr (i,t) ∉ A) :
    F c a beta T m theta k A=0 := by
  have he (i : Fin 5) : (Ioc 0 T) ∩ {t | Sum.inr (i,t) ∈ A}=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro t ⟨ht,ha⟩
    exact h i t ht ha
  simp [F,he]

private theorem F_full (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (A : Set Leg.Record)
    (h : ∀ (i : Fin 5) (t : ℝ), t ∈ Ioc 0 T → Sum.inr (i,t) ∈ A) :
    F c a beta T m theta k A=F c a beta T m theta k univ := by
  have he (i : Fin 5) : (Ioc 0 T) ∩ {t | Sum.inr (i,t) ∈ A}=Ioc 0 T := by
    exact inter_eq_left.mpr (fun t ht => h i t ht)
  simp [F,he]

private theorem balance_mass (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (h : Balance c a beta T m theta k) :
    (F c a beta T m theta k univ) ≠ ⊤ ∧
      (F c a beta T m theta k univ).toReal = 1-survival c k T := by
  have hle : F c a beta T m theta k univ ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal (survival c k T)+F c a beta T m theta k univ := le_add_self
      _ = 1 := h
  have hfin := ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have he := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hfin,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,ENNReal.toReal_one] at he
  exact ⟨hfin,by linarith⟩

/-- The actual early failure window, including every original mode. -/
def earlyEvent : Set Leg.Record := Sum.inr '' (univ ×ˢ Ioc (1:ℝ) (3/2))

private theorem earlyEvent_measurable : MeasurableSet earlyEvent :=
  (MeasurableSet.univ.prod measurableSet_Ioc).inr_image

namespace Band
private theorem wait_F (B : Band) (beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (A : Set Leg.Record) : F B.c B.a beta T m theta B.wait.height A=0 := by
  have hh : B.wait.height=(fun _ => B.a) := by
    funext t
    simp [Band.wait,Leg.height,Leg.speed]
  have hd (i : Fin 5) (t : ℝ) : failureDensity B.c B.a beta m theta B.wait.height i t=0 := by
    rw [hh,failureDensity,jump_action]
    simp [jump,live,jumpRate,hazard]
  simp [F,hd]

private theorem suffix_mass (B : Band) (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (e : Bool) :
    let H := if e then B.earlySuffix else B.lateSuffix
    F B.c B.a beta 1 m theta H univ ≠ ⊤ ∧
      (F B.c B.a beta 1 m theta H univ).toReal=1-B.q := by
  have h := balance_mass B.c B.a beta 1 m theta _ (B.suffix_balance beta m theta e)
  rw [(B.suffix_facts 0 e).2.2.2] at h
  exact h

private theorem suffix_early_event (B : Band) (beta : ℝ) (m : ℤ)
    (theta : Fin 5 → ℝ) :
    F B.c B.a beta 1 m theta B.earlySuffix (shift 1 earlyEvent)=
      F B.c B.a beta 1 m theta B.earlySuffix univ ∧
    F B.c B.a beta 1 m theta B.lateSuffix (shift 1 earlyEvent)=0 := by
  have hl := B.loop_control (1/4) 0 (by norm_num)
  have he := B.loop_end (1/4) (by norm_num)
  have hz := B.loop_zero (1/4) (by norm_num)
  rw [show (2:ℝ)*(1/4)=1/2 by norm_num] at hl he
  obtain ⟨hw,hw0,hw1,hws⟩ := B.wait_facts 0
  have hA := shift_measurable 1 earlyEvent_measurable
  have hfirst : F B.c B.a beta (1/2) m theta (B.loop (1/4) (by norm_num))
      (shift 1 earlyEvent)=F B.c B.a beta (1/2) m theta (B.loop (1/4) (by norm_num)) univ := by
    apply F_full
    intro i t ht
    simp only [shift,mem_preimage,Sum.map_inr,id_eq,earlyEvent,mem_image,mem_prod,
      mem_univ,mem_Ioc,true_and]
    exact ⟨(i,t+1),⟨by linarith [ht.1],by linarith [ht.2]⟩,rfl⟩
  have hsecond : F B.c B.a beta (1/2) m theta (B.loop (1/4) (by norm_num))
      (shift (1/2) (shift 1 earlyEvent))=0 := by
    apply F_zero
    intro i t ht
    simp only [shift,mem_preimage,Sum.map_inr,id_eq,earlyEvent,mem_image,mem_prod,
      mem_univ,mem_Ioc,true_and]
    rintro ⟨z,hz,heq⟩
    have hz' : z=(i,t+1/2+1) := Sum.inr.inj heq
    subst z
    linarith [hz.2,ht.1]
  have hE := failure_join B.c B.a B.a beta (1/2) (1/2) 0 m theta _ _ B.c_lt
    ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos,B.ab.trans B.bc⟩ (by norm_num) (by norm_num)
    (he.trans hw0.symm) hl hw
  have hL := failure_join B.c B.a B.a beta (1/2) (1/2) 0 m theta _ _ B.c_lt
    ⟨B.a_pos,B.ab.trans B.bc⟩ ⟨B.a_pos,B.ab.trans B.bc⟩ (by norm_num) (by norm_num)
    (hw1.trans hz.symm) hw hl
  norm_num only at hE hL
  constructor
  · rw [Band.earlySuffix,hE _ hA,hE _ MeasurableSet.univ]
    simp only [B.wait_F,hfirst,mul_zero,add_zero]
  · rw [Band.lateSuffix,hL _ hA,B.wait_F,hsecond,mul_zero,zero_add]
end Band


private theorem event_difference (B : Band) (n : ℕ) (hn : 1≤n)
    (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (A : Set Leg.Record) (hA : MeasurableSet A) :
    (markedLaw B.c B.a beta 2 m theta (B.early n hn) A).toReal-
      (markedLaw B.c B.a beta 2 m theta (B.late n hn) A).toReal =
      B.q^n*((F B.c B.a beta 1 m theta B.earlySuffix (shift 1 A)).toReal-
        (F B.c B.a beta 1 m theta B.lateSuffix (shift 1 A)).toReal) := by
  have he := (early_late_marked_probability B n hn beta m theta true).2 A hA
  have hl := (early_late_marked_probability B n hn beta m theta false).2 A hA
  dsimp only at he hl
  have hT : 2*(n:ℝ)*Band.halfStep n=1 := by
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
    dsimp [Band.halfStep]; field_simp
  have hbp := balance_mass B.c B.a beta _ m theta _
    (B.prefix_balance (Band.halfStep n) (Band.halfStep_pos n hn) n beta m theta)
  rw [hT] at hbp
  have hpf := ne_top_of_le_ne_top hbp.1
    (F_mono B.c B.a beta 1 m theta _ (subset_univ A))
  have hef := ne_top_of_le_ne_top (B.suffix_mass beta m theta true).1
    (F_mono B.c B.a beta 1 m theta B.earlySuffix (subset_univ (shift 1 A)))
  have hlf := ne_top_of_le_ne_top (B.suffix_mass beta m theta false).1
    (F_mono B.c B.a beta 1 m theta B.lateSuffix (subset_univ (shift 1 A)))
  have hc : (if Sum.inl () ∈ A then ENNReal.ofReal (B.q^(n+1)) else 0)≠⊤ := by
    split_ifs <;> simp
  have hq := (early_late_native_survival B n hn 0).1
  rw [he,hl,ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hc,hpf⟩)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hef),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hc,hpf⟩)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlf),
    ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hq.le n)]
  ring

/-- Every measurable event is bounded, and the actual early failure event
attains the bound in the probability convention of total variation. -/
theorem native_marked_tv (B : Band) (n : ℕ) (hn : 1≤n)
    (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) :
    (∀ A : Set Leg.Record, MeasurableSet A →
      |(markedLaw B.c B.a beta 2 m theta (B.early n hn) A).toReal-
        (markedLaw B.c B.a beta 2 m theta (B.late n hn) A).toReal| ≤ B.q^n*(1-B.q)) ∧
    MeasurableSet earlyEvent ∧
    |(markedLaw B.c B.a beta 2 m theta (B.early n hn) earlyEvent).toReal-
      (markedLaw B.c B.a beta 2 m theta (B.late n hn) earlyEvent).toReal|=B.q^n*(1-B.q) ∧
    eventTV (markedLaw B.c B.a beta 2 m theta (B.early n hn))
      (markedLaw B.c B.a beta 2 m theta (B.late n hn))=B.q^n*(1-B.q) := by
  have hq := early_late_native_survival B n hn 0
  have hqn : 0 ≤ B.q^n := pow_nonneg hq.1.le n
  have hmass : 0 ≤ 1-B.q := by linarith [hq.2.1]
  have hb (A : Set Leg.Record) (hA : MeasurableSet A) :
      |(markedLaw B.c B.a beta 2 m theta (B.early n hn) A).toReal-
        (markedLaw B.c B.a beta 2 m theta (B.late n hn) A).toReal| ≤ B.q^n*(1-B.q) := by
    rw [event_difference B n hn beta m theta A hA,abs_mul,abs_of_nonneg hqn]
    have hx := ENNReal.toReal_mono (B.suffix_mass beta m theta true).1
      (F_mono B.c B.a beta 1 m theta B.earlySuffix (subset_univ (shift 1 A)))
    have hy := ENNReal.toReal_mono (B.suffix_mass beta m theta false).1
      (F_mono B.c B.a beta 1 m theta B.lateSuffix (subset_univ (shift 1 A)))
    rw [(B.suffix_mass beta m theta true).2] at hx
    rw [(B.suffix_mass beta m theta false).2] at hy
    apply mul_le_mul_of_nonneg_left _ hqn
    exact abs_sub_le_iff.mpr ⟨by linarith [ENNReal.toReal_nonneg
      (F B.c B.a beta 1 m theta B.lateSuffix (shift 1 A))],by
      linarith [ENNReal.toReal_nonneg (F B.c B.a beta 1 m theta B.earlySuffix (shift 1 A))]⟩
  have he : |(markedLaw B.c B.a beta 2 m theta (B.early n hn) earlyEvent).toReal-
      (markedLaw B.c B.a beta 2 m theta (B.late n hn) earlyEvent).toReal|=B.q^n*(1-B.q) := by
    rw [event_difference B n hn beta m theta earlyEvent earlyEvent_measurable,
      (B.suffix_early_event beta m theta).1,(B.suffix_early_event beta m theta).2,
      ENNReal.toReal_zero,sub_zero,(B.suffix_mass beta m theta true).2,
      abs_of_nonneg (mul_nonneg hqn hmass)]
  refine ⟨hb,earlyEvent_measurable,he,?_⟩
  unfold eventTV
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_,earlyEvent,earlyEvent_measurable,rfl⟩
    · rintro x ⟨A,hA,rfl⟩
      exact hb A hA
  · apply le_csSup
    · exact ⟨_,by rintro x ⟨A,hA,rfl⟩; exact hb A hA⟩
    · exact ⟨earlyEvent,earlyEvent_measurable,he.symm⟩

/-- On the actual all-n original controls the native marked distance tends
to zero while the fixed height gap defeats every modulus at zero. -/
theorem marked_inverse_nonuniformity (B : Band) (beta : ℝ) (m : ℤ)
    (theta : Fin 5 → ℝ) (omega : ℝ → ℝ)
    (homega : Tendsto omega (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ¬ (∀ (n : ℕ) (hn : 1≤n),
      |B.early n hn (5/4)-B.late n hn (5/4)| ≤
        omega (eventTV (markedLaw B.c B.a beta 2 m theta (B.early n hn))
          (markedLaw B.c B.a beta 2 m theta (B.late n hn)))) := by
  intro h
  have hq := early_late_native_survival B 1 (by omega) 0
  have ht : Tendsto (fun n : ℕ => B.q^(n+1)*(1-B.q)) atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2.1
    have hs := hp.comp (tendsto_add_atTop_nat 1)
    simpa using hs.mul_const (1-B.q)
  have hpos : ∀ n : ℕ, 0<B.q^(n+1)*(1-B.q) := by
    intro n
    exact mul_pos (pow_pos hq.1 _) (sub_pos.mpr hq.2.1)
  have ht' : Tendsto (fun n : ℕ => B.q^(n+1)*(1-B.q)) atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Filter.Eventually.of_forall hpos⟩
  have ho := homega.comp ht'
  have hg : ∀ n : ℕ, B.b-B.a ≤ omega (B.q^(n+1)*(1-B.q)) := by
    intro n
    have hn : 1≤n+1 := by omega
    have hx := h (n+1) hn
    have hs := early_late_native_survival B (n+1) hn 0
    rw [hs.2.2.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.2.2,
      abs_of_pos (sub_pos.mpr B.ab),(native_marked_tv B (n+1) hn beta m theta).2.2.2] at hx
    exact hx
  have hz : B.b-B.a ≤ 0 := le_of_tendsto ho (Filter.Eventually.of_forall hg)
  linarith [B.ab]
end D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw
