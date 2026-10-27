/- GID: D5/S3/Quantum/Fibers/OriginalRepeatedResources
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalRepeatedResources
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-piecewise affine controls and their derivative resources. -/

import D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw
import Mathlib.MeasureTheory.Function.EssSup

/-! Exact regularity and derivative resources of the original repeated early/late controls. -/

noncomputable section
namespace D5.S3.Quantum.Fibers.OriginalRepeatedResources
open Set Filter Topology MeasureTheory intervalIntegral
open OriginalControlComposition OriginalControlMarkedJump OriginalMarkedConcatenation
open OriginalRepeatedPrefix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem finite_c1_join (T U chi : ℝ) (f g : ℝ → ℝ)
    (hf : FiniteC1Control T f (fun _ => chi))
    (hg : FiniteC1Control U g (fun _ => chi)) :
    FiniteC1Control (T+U) (concatenate f g T) (fun _ => chi) := by
  obtain ⟨N,u,hu,hu0,huN,huf⟩ := hf
  obtain ⟨M,v,hv,hv0,hvM,hvg⟩ := hg
  let w : ℕ → ℝ := fun j => if j < N then u j else T+v (j-N)
  have wl (j : ℕ) (hj : j ≤ N) : w j=u j := by
    by_cases h : j<N
    · simp [w,h]
    · have he : j=N := by omega
      simp [he,w,hv0,huN]
  have wr (j : ℕ) (hj : N ≤ j) : w j=T+v (j-N) := by
    simp [w,not_lt.mpr hj]
  have wm : Monotone w := by
    intro i j hij
    by_cases hj : j<N
    · rw [wl i (by omega),wl j hj.le]
      exact hu hij
    · by_cases hi : i<N
      · rw [wl i hi.le,wr j (by omega)]
        have h1 : u i ≤ T := huN ▸ hu hi.le
        have h2 : 0 ≤ v (j-N) := hv0 ▸ hv (Nat.zero_le _)
        linarith
      · rw [wr i (by omega),wr j (by omega)]
        exact add_le_add_right (hv (Nat.sub_le_sub_right hij N)) T
  refine ⟨N+M,w,wm,?_,?_,?_⟩
  · rw [wl 0 (Nat.zero_le _)]; exact hu0
  · rw [wr (N+M) (by omega),Nat.add_sub_cancel_left,hvM]
  · intro j hj
    by_cases hl : j<N
    · rw [wl j hl.le,wl (j+1) (by omega)]
      obtain ⟨r,s,hr,hs,hd⟩ := huf j hl
      refine ⟨r,fun _ => 0,hr,continuousOn_const,?_⟩
      intro t ht
      have htT : t<T := ht.2.trans_le (huN ▸ hu (by omega))
      refine ⟨(hd t ht).1.congr_of_eventuallyEq ?_,hasDerivAt_const t chi⟩
      filter_upwards [Iio_mem_nhds htT] with x hx
      exact if_pos hx.le
    · have hNj : N ≤ j := by omega
      rw [wr j hNj,wr (j+1) (by omega)]
      have hlt : j-N<M := by omega
      obtain ⟨r,s,hr,hs,hd⟩ := hvg (j-N) hlt
      have hsub : j+1-N=(j-N)+1 := by omega
      rw [hsub]
      refine ⟨fun t => r (t-T),fun _ => 0,?_,continuousOn_const,?_⟩
      · apply hr.comp (continuous_id.sub continuous_const).continuousOn
        intro t ht
        rw [uIcc_of_le (add_le_add_right (hv (Nat.le_succ _)) T)] at ht
        rw [uIcc_of_le (hv (Nat.le_succ _))]
        change t-T ∈ Icc _ _
        exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
      · intro t ht
        have hts : t-T ∈ Ioo (v (j-N)) (v (j-N+1)) :=
          ⟨by linarith [ht.1],by linarith [ht.2]⟩
        have htT : T<t := by
          have h0 : 0 ≤ v (j-N) := hv0 ▸ hv (Nat.zero_le _)
          linarith [ht.1]
        have hdg := ((hd (t-T) hts).1.comp t ((hasDerivAt_id t).sub_const T)).const_add (f T)
        have hder := hdg.sub_const (g 0)
        refine ⟨?_,hasDerivAt_const t chi⟩
        convert hder.congr_of_eventuallyEq (f₁:=concatenate f g T) ?_ using 1 <;> simp
        filter_upwards [Ioi_mem_nhds htT] with x hx
        exact if_neg (not_le.mpr hx)

private theorem loop_finite (B : Band) (d chi : ℝ) (hd : 0 < d) :
    FiniteC1Control (2*d) (B.loop d hd) (fun _ => chi) := by
  simpa only [two_mul,Band.loop] using finite_c1_join d d chi
    (B.up d hd).height (B.down d hd).height
    ((B.up d hd).affine_marked_probability chi 0 0 (fun _ => 0)).2.2.1
    ((B.down d hd).affine_marked_probability chi 0 0 (fun _ => 0)).2.2.1

private theorem prefix_finite (B : Band) (d chi : ℝ) (hd : 0 < d) (j : ℕ) :
    FiniteC1Control (2*(j:ℝ)*d) (B.repeated d hd j) (fun _ => chi) := by
  induction j with
  | zero =>
    refine ⟨0,fun _ => 0,monotone_const,by rfl,by simp,?_⟩
    intro i hi
    omega
  | succ j ih =>
    convert finite_c1_join (2*(j:ℝ)*d) (2*d) chi _ _ ih (loop_finite B d chi hd) using 1
    · push_cast; ring
    · rfl


private theorem support_margin (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) :
    IsLeast {r : ℝ | ∃ t ∈ Icc (0:ℝ) 2, ∃ i : Fin 5,
      r=p B.c ((if e then B.early n hn else B.late n hn) t) i}
      (min B.a (min (B.c-B.b) (1-2*B.c))) := by
  let k := if e then B.early n hn else B.late n hn
  obtain ⟨_,_,_,_,_,_,_,he,hl,_,_,hep,_⟩ := early_late_native_survival B n hn 0
  have hend : k 2=B.a := by cases e <;> dsimp [k] <;> assumption
  have hpeak : ∃ t ∈ Icc (0:ℝ) 2, k t=B.b := by
    cases e
    · have ht : 2*(n:ℝ)*Band.halfStep n=1 := by
        have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
        dsimp [Band.halfStep]; field_simp
      have hp := (B.prefix_facts (Band.halfStep n) 0 (Band.halfStep_pos n hn) n).2.2.1
      rw [ht] at hp
      refine ⟨7/4,by norm_num,?_⟩
      norm_num [k,Band.late,concatenate,hp,Band.lateSuffix,Band.loop,
        Band.up,Band.down,Band.wait,Leg.height,Leg.speed]
      <;> ring
    · exact ⟨5/4,by norm_num,hep⟩
  have ha : B.a ∈ {r : ℝ | ∃ t ∈ Icc (0:ℝ) 2, ∃ i : Fin 5, r=p B.c (k t) i} := by
    refine ⟨2,by norm_num,0,?_⟩
    simp [hend,p_explicit]
  have hb : B.c-B.b ∈ {r : ℝ | ∃ t ∈ Icc (0:ℝ) 2, ∃ i : Fin 5, r=p B.c (k t) i} := by
    obtain ⟨t,ht,hp⟩ := hpeak
    exact ⟨t,ht,1,by simp [hp,p_explicit]⟩
  have hz : 1-2*B.c ∈ {r : ℝ | ∃ t ∈ Icc (0:ℝ) 2, ∃ i : Fin 5, r=p B.c (k t) i} := by
    exact ⟨2,by norm_num,2,by simp [p_explicit]⟩
  constructor
  · change min B.a (min (B.c-B.b) (1-2*B.c)) ∈ _
    rcases le_total B.a (min (B.c-B.b) (1-2*B.c)) with h | h
    · simpa only [min_eq_left h] using ha
    · rw [min_eq_right h]
      rcases le_total (B.c-B.b) (1-2*B.c) with h' | h'
      · simpa only [min_eq_left h'] using hb
      · simpa only [min_eq_right h'] using hz
  · rintro r ⟨t,ht,i,rfl⟩
    have hr := OriginalRepeatedMarkedLaw.actual_range B n hn e t ht
    have h0 := min_le_left B.a (min (B.c-B.b) (1-2*B.c))
    have h1 := (min_le_right B.a (min (B.c-B.b) (1-2*B.c))).trans (min_le_left _ _)
    have h2 := (min_le_right B.a (min (B.c-B.b) (1-2*B.c))).trans (min_le_right _ _)
    fin_cases i <;> simp only [p_explicit,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> linarith [hr.1,hr.2]

/-- Both literal early/late functions have finite partitions with continuous
rates on each closed piece and their actual derivatives on each open piece. -/
theorem early_late_finite_c1 (B : Band) (n : ℕ) (hn : 1 ≤ n) (chi : ℝ) :
    FiniteC1Control 2 (B.early n hn) (fun _ => chi) ∧
    FiniteC1Control 2 (B.late n hn) (fun _ => chi) ∧
    (∀ e : Bool, IsLeast {r : ℝ | ∃ t ∈ Icc (0:ℝ) 2, ∃ i : Fin 5,
      r=p B.c ((if e then B.early n hn else B.late n hn) t) i}
      (min B.a (min (B.c-B.b) (1-2*B.c)))) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have ht : 2*(n:ℝ)*Band.halfStep n=1 := by dsimp [Band.halfStep]; field_simp
  have hp := prefix_finite B (Band.halfStep n) chi (Band.halfStep_pos n hn) n
  rw [ht] at hp
  have hl := loop_finite B (1/4) chi (by norm_num)
  norm_num only at hl
  have hw := (B.wait.affine_marked_probability chi 0 0 (fun _ => 0)).2.2.1
  have he := finite_c1_join (1/2) (1/2) chi _ _ hl hw
  have hf := finite_c1_join (1/2) (1/2) chi _ _ hw hl
  norm_num only at he hf
  refine ⟨?_,?_,support_margin B n hn⟩
  · simpa only [Band.early,Band.earlySuffix,show (1:ℝ)+1=2 by norm_num] using finite_c1_join 1 1 chi _ _ hp he
  · simpa only [Band.late,Band.lateSuffix,show (1:ℝ)+1=2 by norm_num] using finite_c1_join 1 1 chi _ _ hp hf


private theorem derivative_integral_join (T U : ℝ) (hT : 0≤T) (hU : 0≤U)
    (f g F : ℝ → ℝ)
    (hf : IntervalIntegrable (fun t => F (deriv f t)) volume 0 T)
    (hg : IntervalIntegrable (fun t => F (deriv g t)) volume 0 U) :
    IntervalIntegrable (fun t => F (deriv (concatenate f g T) t)) volume 0 (T+U) ∧
    (∫ t in (0:ℝ)..(T+U), F (deriv (concatenate f g T) t)) =
      (∫ t in (0:ℝ)..T, F (deriv f t)) + (∫ t in (0:ℝ)..U, F (deriv g t)) := by
  have he0 : EqOn (fun t => F (deriv (concatenate f g T) t))
      (fun t => F (deriv f t)) (uIoo 0 T) := by
    intro t ht
    rw [uIoo_of_le hT] at ht
    exact congrArg F (deriv_before f g T t ht.2)
  have he1 : EqOn (fun t => F (deriv (concatenate f g T) t))
      (fun t => F (deriv g (t-T))) (uIoo T (T+U)) := by
    intro t ht
    rw [uIoo_of_le (by linarith : T≤T+U)] at ht
    exact congrArg F (deriv_after f g T t ht.1)
  have h0 := hf.congr_uIoo (fun t ht => (he0 ht).symm)
  have h1s : IntervalIntegrable (fun t => F (deriv g (t-T))) volume T (T+U) := by
    simpa [add_comm] using hg.comp_sub_right T
  have h1 := h1s.congr_uIoo (fun t ht => (he1 ht).symm)
  refine ⟨h0.trans h1,?_⟩
  rw [←integral_add_adjacent_intervals h0 h1,integral_congr_uIoo he0,
    integral_congr_uIoo he1,integral_comp_sub_right (fun t => F (deriv g t)) T,
    sub_self,add_sub_cancel_left]

private theorem leg_resource (L : Leg) (F : ℝ → ℝ) :
    IntervalIntegrable (fun t => F (deriv L.height t)) volume 0 L.duration ∧
    (∫ t in (0:ℝ)..L.duration, F (deriv L.height t))=L.duration*F L.speed := by
  simp only [(L.height_deriv _).deriv]
  exact ⟨intervalIntegrable_const,by simp [mul_comm]⟩

private theorem loop_resource (B : Band) (d : ℝ) (hd : 0 < d) (F : ℝ → ℝ) :
    IntervalIntegrable (fun t => F (deriv (B.loop d hd) t)) volume 0 (2*d) ∧
    (∫ t in (0:ℝ)..(2*d), F (deriv (B.loop d hd) t))=
      d*(F ((B.b-B.a)/d)+F (-((B.b-B.a)/d))) := by
  obtain ⟨hu,he⟩ := leg_resource (B.up d hd) F
  obtain ⟨hv,hf⟩ := leg_resource (B.down d hd) F
  change (∫ t in (0:ℝ)..d,F (deriv (B.up d hd).height t))=d*F ((B.b-B.a)/d) at he
  change (∫ t in (0:ℝ)..d,F (deriv (B.down d hd).height t))=d*F ((B.a-B.b)/d) at hf
  have hj := derivative_integral_join d d hd.le hd.le _ _ F hu hv
  rw [he,hf] at hj
  rw [show (B.a-B.b)/d=-((B.b-B.a)/d) by ring] at hj
  simpa only [Band.loop,two_mul,mul_add] using hj

private theorem prefix_resource (B : Band) (d : ℝ) (hd : 0 < d) (j : ℕ) (F : ℝ → ℝ) :
    IntervalIntegrable (fun t => F (deriv (B.repeated d hd j) t)) volume 0 (2*(j:ℝ)*d) ∧
    (∫ t in (0:ℝ)..(2*(j:ℝ)*d), F (deriv (B.repeated d hd j) t))=
      (j:ℝ)*d*(F ((B.b-B.a)/d)+F (-((B.b-B.a)/d))) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hl,he⟩ := loop_resource B d hd F
    have hj := derivative_integral_join (2*(j:ℝ)*d) (2*d) (by positivity) (by positivity)
      _ _ F ih.1 hl
    rw [ih.2,he] at hj
    have ht : 2*((j+1:ℕ):ℝ)*d=2*(j:ℝ)*d+2*d := by push_cast; ring
    rw [ht]
    refine ⟨hj.1,?_⟩
    change (∫ t in (0:ℝ)..(2*(j:ℝ)*d+2*d), F (deriv (concatenate
      (B.repeated d hd j) (B.loop d hd) (2*(j:ℝ)*d)) t))=_
    rw [hj.2]
    push_cast
    ring

private theorem suffix_resource (B : Band) (F : ℝ → ℝ) (e : Bool) :
    let k := if e then B.earlySuffix else B.lateSuffix
    IntervalIntegrable (fun t => F (deriv k t)) volume 0 1 ∧
    (∫ t in (0:ℝ)..1,F (deriv k t))=
      (1/4)*(F (4*(B.b-B.a))+F (-(4*(B.b-B.a))))+(1/2)*F 0 := by
  have hl := loop_resource B (1/4) (by norm_num) F
  norm_num only at hl
  obtain ⟨hw,he⟩ := leg_resource B.wait F
  have hs0 : B.wait.speed=0 := by simp [Band.wait,Leg.speed]
  rw [hs0] at he
  change (∫ t in (0:ℝ)..(1/2),F (deriv B.wait.height t))=(1/2)*F 0 at he
  cases e
  · have hj := derivative_integral_join (1/2) (1/2) (by norm_num) (by norm_num) _ _ F hw hl.1
    rw [he,hl.2] at hj
    norm_num [Band.lateSuffix,Band.wait,Leg.speed] at hj ⊢
    exact ⟨hj.1,by rw [hj.2]; ring⟩
  · have hj := derivative_integral_join (1/2) (1/2) (by norm_num) (by norm_num) _ _ F hl.1 hw
    rw [hl.2,he] at hj
    norm_num [Band.earlySuffix,Band.wait,Leg.speed] at hj ⊢
    exact hj

private theorem actual_resource (B : Band) (n : ℕ) (hn : 1 ≤ n) (F : ℝ → ℝ) (e : Bool) :
    let k := if e then B.early n hn else B.late n hn
    IntervalIntegrable (fun t => F (deriv k t)) volume 0 2 ∧
    (∫ t in (0:ℝ)..2,F (deriv k t))=
      (1/2)*(F (2*(n:ℝ)*(B.b-B.a))+F (-(2*(n:ℝ)*(B.b-B.a))))+
      (1/4)*(F (4*(B.b-B.a))+F (-(4*(B.b-B.a))))+(1/2)*F 0 := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have ht : 2*(n:ℝ)*Band.halfStep n=1 := by dsimp [Band.halfStep]; field_simp
  have hp := prefix_resource B (Band.halfStep n) (Band.halfStep_pos n hn) n F
  rw [ht] at hp
  have hs := suffix_resource B F e
  dsimp only at hs
  have hj := derivative_integral_join 1 1 zero_le_one zero_le_one _ _ F hp.1 hs.1
  rw [hp.2,hs.2] at hj
  have hv : (B.b-B.a)/Band.halfStep n=2*(n:ℝ)*(B.b-B.a) := by
    dsimp [Band.halfStep]; field_simp <;> ring
  have hc : (n:ℝ)*Band.halfStep n=1/2 := by linarith [ht]
  rw [hv,hc] at hj
  norm_num only at hj
  cases e <;> simpa only [Bool.false_eq_true,↓reduceIte,Band.early,Band.late,add_assoc] using hj

/-- Length and quadratic height energy are interval integrals of the actual
derivatives, and agree for the two controls for every positive repetition count. -/
theorem early_late_integral_resources (B : Band) (n : ℕ) (hn : 1 ≤ n) (chi : ℝ) :
    (∀ e : Bool, let k := if e then B.early n hn else B.late n hn
      IntervalIntegrable (fun t => |deriv k t|) volume 0 2 ∧
      IntervalIntegrable (fun t => (deriv k t)^2) volume 0 2 ∧
      (∫ t in (0:ℝ)..2,Real.sqrt ((deriv k t)^2+(deriv (fun _ : ℝ => chi) t)^2))=
        2*((n:ℝ)+1)*(B.b-B.a) ∧
      (∫ t in (0:ℝ)..2,((deriv k t)^2+(deriv (fun _ : ℝ => chi) t)^2))=
        (4*(n:ℝ)^2+8)*(B.b-B.a)^2) := by
  intro e
  have hl := actual_resource B n hn abs e
  have hq := actual_resource B n hn (fun x => x^2) e
  have hpos : 0≤2*(n:ℝ)*(B.b-B.a) := by have hd := B.ab; positivity
  have hpos' : 0≤4*(B.b-B.a) := by linarith [B.ab]
  dsimp only at hl hq ⊢
  simp only [deriv_const,show (0:ℝ)^2=0 by norm_num,add_zero,Real.sqrt_sq_eq_abs]
  refine ⟨hl.1,hq.1,?_,?_⟩
  · rw [hl.2]
    simp only [abs_of_nonneg hpos,abs_neg,abs_of_nonneg hpos',abs_zero,mul_zero,add_zero]
    ring
  · rw [hq.2]
    ring


private theorem variation_join (T U : ℝ) (hT : 0≤T) (hU : 0≤U)
    (f g : ℝ → ℝ) (hj : f T=g 0) :
    eVariationOn (concatenate f g T) (Icc 0 (T+U)) =
      eVariationOn f (Icc 0 T)+eVariationOn g (Icc 0 U) := by
  have hs := eVariationOn.Icc_add_Icc (concatenate f g T) (s:=univ)
    hT (by linarith : T≤T+U) (mem_univ T)
  simp only [univ_inter] at hs
  rw [←hs]
  congr 1
  · exact eVariationOn.congr (fun t ht => if_pos ht.2)
  · have he : EqOn (concatenate f g T) (fun t => g (t-T)) (Icc T (T+U)) := by
      intro t ht
      by_cases h : t≤T
      · have ht' : t=T := le_antisymm h ht.1
        simp [ht',concatenate,hj]
      · simp [concatenate,h,hj]
    rw [eVariationOn.congr he]
    have him : (fun t : ℝ => t-T) '' Icc T (T+U)=Icc 0 U := by
      ext t
      constructor
      · rintro ⟨s,hs,rfl⟩
        exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
      · intro ht
        exact ⟨t+T,⟨by linarith [ht.1],by linarith [ht.2]⟩,by ring⟩
    simpa only [Function.comp_def,him] using eVariationOn.comp_eq_of_monotoneOn
      g (t:=Icc T (T+U)) (fun t : ℝ => t-T) (fun _ _ _ _ h => sub_le_sub_right h T)

private theorem variation_neg (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun t => -f t) s=eVariationOn f s := by
  unfold eVariationOn
  congr 1
  funext p
  apply Finset.sum_congr rfl
  intro i hi
  simp only [edist_neg_neg]

private theorem affine_variation (a v T : ℝ) (hT : 0≤T) :
    eVariationOn (fun t : ℝ => a+v*t) (Icc 0 T)=ENNReal.ofReal (|v| * T) := by
  by_cases hv : 0≤v
  · have hm : MonotoneOn (fun t : ℝ => a+v*t) (Icc 0 T) := by
      intro s hs t ht hst
      nlinarith
    have he := hm.eVariationOn_eq ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩
    simp only [inter_self,mul_zero,add_zero,add_sub_cancel_left,abs_of_nonneg hv] at he ⊢
    exact he
  · rw [←variation_neg]
    have hm : MonotoneOn (fun t : ℝ => -(a+v*t)) (Icc 0 T) := by
      intro s hs t ht hst
      nlinarith
    have he := hm.eVariationOn_eq ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩
    simp only [inter_self,mul_zero,add_zero,neg_sub_neg,abs_of_neg (lt_of_not_ge hv)] at he ⊢
    convert he using 2 <;> ring

private theorem loop_variation (B : Band) (d : ℝ) (hd : 0 < d) :
    eVariationOn (B.loop d hd) (Icc 0 (2*d))=ENNReal.ofReal (2*(B.b-B.a)) := by
  have hj : (B.up d hd).height d=(B.down d hd).height 0 := by
    dsimp [Band.up,Band.down,Leg.height,Leg.speed]
    field_simp
    <;> ring
  have hs := variation_join d d hd.le hd.le _ _ hj
  have hu := affine_variation (B.up d hd).x (B.up d hd).speed d hd.le
  have hv := affine_variation (B.down d hd).x (B.down d hd).speed d hd.le
  change eVariationOn (B.up d hd).height (Icc 0 d)=_ at hu
  change eVariationOn (B.down d hd).height (Icc 0 d)=_ at hv
  rw [hu,hv] at hs
  have h0 : 0≤(B.b-B.a)/d := div_nonneg (sub_nonneg.mpr B.ab.le) hd.le
  have h1 : (B.a-B.b)/d≤0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr B.ab.le) hd.le
  have hu' : |(B.up d hd).speed| * d=B.b-B.a := by
    change |(B.b-B.a)/d| * d=_
    rw [abs_of_nonneg h0]
    field_simp
  have hv' : |(B.down d hd).speed| * d=B.b-B.a := by
    change |(B.a-B.b)/d| * d=_
    rw [abs_of_nonpos h1]
    field_simp
    <;> ring
  rw [hu',hv',←ENNReal.ofReal_add (sub_nonneg.mpr B.ab.le) (sub_nonneg.mpr B.ab.le)] at hs
  simpa only [Band.loop,two_mul] using hs

private theorem prefix_variation (B : Band) (d : ℝ) (hd : 0 < d) (j : ℕ) :
    eVariationOn (B.repeated d hd j) (Icc 0 (2*(j:ℝ)*d))=
      ENNReal.ofReal (2*(j:ℝ)*(B.b-B.a)) := by
  induction j with
  | zero => simp [Band.repeated,eVariationOn.eq_zero_iff]
  | succ j ih =>
    have hp := Band.prefix_facts B d 0 hd j
    have hj : B.repeated d hd j (2*(j:ℝ)*d)=B.loop d hd 0 := hp.2.2.1.trans (B.loop_zero d hd).symm
    have he := variation_join (2*(j:ℝ)*d) (2*d) (by positivity) (by positivity) _ _ hj
    rw [ih,loop_variation] at he
    rw [←ENNReal.ofReal_add (by have h := B.ab; positivity) (by linarith [B.ab])] at he
    have ht : 2*((j+1:ℕ):ℝ)*d=2*(j:ℝ)*d+2*d := by push_cast; ring
    rw [ht]
    change eVariationOn (concatenate (B.repeated d hd j) (B.loop d hd) (2*(j:ℝ)*d))
      (Icc 0 (2*(j:ℝ)*d+2*d))=_
    rw [he]
    congr 1
    push_cast
    ring

private theorem suffix_variation (B : Band) (e : Bool) :
    eVariationOn (if e then B.earlySuffix else B.lateSuffix) (Icc 0 1)=
      ENNReal.ofReal (2*(B.b-B.a)) := by
  have hl := loop_variation B (1/4) (by norm_num)
  norm_num only at hl
  have hw : B.wait.height=fun _ => B.a := by funext t; simp [Band.wait,Leg.height,Leg.speed]
  have hz : eVariationOn B.wait.height (Icc (0:ℝ) (1/2))=0 := by
    rw [hw]
    exact (eVariationOn.eq_zero_iff _).2 (by intro x hx y hy; simp)
  have hl0 := B.loop_zero (1/4) (by norm_num)
  have hl1 := B.loop_end (1/4) (by norm_num)
  norm_num only at hl1
  cases e
  · have hj : B.wait.height (1/2)=B.loop (1/4) (by norm_num) 0 := by rw [hw,hl0]
    have he := variation_join (1/2) (1/2) (by norm_num) (by norm_num) _ _ hj
    rw [hz,hl,zero_add] at he
    simpa only [Bool.false_eq_true,↓reduceIte,Band.lateSuffix,show (1/2:ℝ)+1/2=1 by ring] using he
  · have hj : B.loop (1/4) (by norm_num) (1/2)=B.wait.height 0 := by rw [hw,hl1]
    have he := variation_join (1/2) (1/2) (by norm_num) (by norm_num) _ _ hj
    rw [hl,hz,add_zero] at he
    simpa only [↓reduceIte,Band.earlySuffix,show (1/2:ℝ)+1/2=1 by ring] using he

/-- Metric total variation of the actual height function agrees with its
computed length, for both positions of the final excursion. -/
theorem early_late_total_variation (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) :
    eVariationOn (if e then B.early n hn else B.late n hn) (Icc 0 2)=
      ENNReal.ofReal (2*((n:ℝ)+1)*(B.b-B.a)) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have ht : 2*(n:ℝ)*Band.halfStep n=1 := by dsimp [Band.halfStep]; field_simp
  have hp := prefix_variation B (Band.halfStep n) (Band.halfStep_pos n hn) n
  rw [ht] at hp
  have hpf := Band.prefix_facts B (Band.halfStep n) 0 (Band.halfStep_pos n hn) n
  rw [ht] at hpf
  have hsf := Band.suffix_facts B 0 e
  dsimp only at hsf
  have hj := hpf.2.2.1.trans hsf.2.1.symm
  have he := variation_join 1 1 zero_le_one zero_le_one _ _ hj
  rw [hp,suffix_variation,←ENNReal.ofReal_add
    (by have h := B.ab; positivity) (by linarith [B.ab])] at he
  have hval : 2*(n:ℝ)*(B.b-B.a)+2*(B.b-B.a)=2*((n:ℝ)+1)*(B.b-B.a) := by ring
  rw [hval] at he
  norm_num only at he
  cases e <;> simpa only [Bool.false_eq_true,↓reduceIte,Band.early,Band.late] using he


private def excess (M v : ℝ) : ℝ := if |v|≤M then 0 else 1

private theorem excess_nonneg (M v : ℝ) : 0≤excess M v := by
  unfold excess
  split_ifs <;> norm_num

/-- Constant real phase has zero metric variation and zero essential derivative
speed on the same duration-two clock. -/
private theorem constant_phase_resources (chi : ℝ) :
    eVariationOn (fun _ : ℝ => chi) (Icc 0 2)=0 ∧
    essSup (fun t => |deriv (fun _ : ℝ => chi) t|)
      (volume.restrict (Ioc (0:ℝ) 2))=0 := by
  constructor
  · exact (eVariationOn.eq_zero_iff _).2 (by intro x hx y hy; simp)
  · simp only [deriv_const,abs_zero]
    apply essSup_const
    intro h
    have hv := congrArg (fun m : Measure ℝ => m univ) h
    norm_num at hv


/-- The essential supremum is taken for the actual derivative on the original
Lebesgue clock; the two nonzero affine rates both occur on positive-duration pieces. -/
theorem early_late_essential_speed (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool) (chi : ℝ) :
    essSup (fun t => |deriv (if e then B.early n hn else B.late n hn) t|)
      (volume.restrict (Ioc 0 2))=max (2*(n:ℝ)) 4*(B.b-B.a) ∧
    eVariationOn (fun _ : ℝ => chi) (Icc 0 2)=0 ∧
    essSup (fun t => |deriv (fun _ : ℝ => chi) t|)
      (volume.restrict (Ioc (0:ℝ) 2))=0 := by
  refine ⟨?_,constant_phase_resources chi⟩
  letI : NeZero (volume.restrict (Ioc (0:ℝ) 2)) := ⟨by
    intro h
    have hv := congrArg (fun m : Measure ℝ => m univ) h
    norm_num at hv⟩
  let k := if e then B.early n hn else B.late n hn
  let A := 2*(n:ℝ)*(B.b-B.a)
  let C := 4*(B.b-B.a)
  let M := max A C
  have hA : 0≤A := by dsimp [A]; have h := B.ab; positivity
  have hC : 0≤C := by dsimp [C]; linarith [B.ab]
  have hM : 0≤M := hA.trans (le_max_left _ _)
  have hcalc := actual_resource B n hn (excess M) e
  change IntervalIntegrable (fun t => excess M (deriv k t)) volume 0 2 ∧
    (∫ t in (0:ℝ)..2,excess M (deriv k t))=
      (1/2)*(excess M A+excess M (-A))+
      (1/4)*(excess M C+excess M (-C))+(1/2)*excess M 0 at hcalc
  have hzero : (∫ t in (0:ℝ)..2,excess M (deriv k t))=0 := by
    rw [hcalc.2]
    simp [excess,abs_of_nonneg hA,abs_of_nonneg hC,abs_neg,
      show A≤M from le_max_left _ _,show C≤M from le_max_right _ _,hM]
  have hz := (integral_eq_zero_iff_of_le_of_nonneg_ae (by norm_num : (0:ℝ)≤2)
    (ae_of_all _ (fun t => excess_nonneg M (deriv k t))) hcalc.1).1 hzero
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 2), |deriv k t|≤M := by
    filter_upwards [hz] with t ht
    by_contra h
    simp [excess,h] at ht
  have hbounded := isBoundedUnder_of_eventually_le hbound
  have hupper : essSup (fun t => |deriv k t|) (volume.restrict (Ioc 0 2))≤M :=
    essSup_le_of_ae_le M hbound (isCoboundedUnder_le_of_le _ (fun t => abs_nonneg (deriv k t)))
  have hlower : M≤essSup (fun t => |deriv k t|) (volume.restrict (Ioc 0 2)) := by
    by_contra h
    have hlt : essSup (fun t => |deriv k t|) (volume.restrict (Ioc 0 2))<M := lt_of_not_ge h
    let r := essSup (fun t => |deriv k t|) (volume.restrict (Ioc 0 2))
    have hr : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 2), excess r (deriv k t)=0 := by
      filter_upwards [ae_le_essSup hbounded] with t ht
      exact if_pos ht
    have hc := actual_resource B n hn (excess r) e
    change IntervalIntegrable (fun t => excess r (deriv k t)) volume 0 2 ∧
      (∫ t in (0:ℝ)..2,excess r (deriv k t))=
        (1/2)*(excess r A+excess r (-A))+
        (1/4)*(excess r C+excess r (-C))+(1/2)*excess r 0 at hc
    have hi := (integral_eq_zero_iff_of_le_of_nonneg_ae (by norm_num : (0:ℝ)≤2)
      (ae_of_all _ (fun t => excess_nonneg r (deriv k t))) hc.1).2 hr
    rw [hi] at hc
    have h0 := excess_nonneg r 0
    have ha := excess_nonneg r A
    have ha' := excess_nonneg r (-A)
    have hb := excess_nonneg r C
    have hb' := excess_nonneg r (-C)
    rcases lt_max_iff.mp hlt with hltA | hltC
    · change r<A at hltA
      have hx : excess r A=1 := by simp [excess,abs_of_nonneg hA,not_le.mpr hltA]
      linarith [hc.2]
    · change r<C at hltC
      have hx : excess r C=1 := by simp [excess,abs_of_nonneg hC,not_le.mpr hltC]
      linarith [hc.2]
  have he : M=max (2*(n:ℝ)) 4*(B.b-B.a) := by
    dsimp [M,A,C]
    exact (max_mul_of_nonneg _ _ (sub_nonneg.mpr B.ab.le)).symm
  exact (le_antisymm hupper hlower).trans he

end D5.S3.Quantum.Fibers.OriginalRepeatedResources
