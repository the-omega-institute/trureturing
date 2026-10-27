/- GID: D5/S3/Quantum/Fibers/OriginalRepeatedResources
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalRepeatedResources
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-piecewise affine controls and their derivative resources. -/

import D5.S3.Quantum.Fibers.OriginalRepeatedMarkedLaw

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
        exact add_le_add_left (hv (Nat.sub_le_sub_right hij N)) T
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
        rw [uIcc_of_le (add_le_add_left (hv (Nat.le_succ _)) T)] at ht
        rw [uIcc_of_le (hv (Nat.le_succ _))]
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

private theorem loop_finite (B : Band) (d chi : ℝ) (hd : 0<d) :
    FiniteC1Control (2*d) (B.loop d hd) (fun _ => chi) := by
  simpa only [two_mul,Band.loop] using finite_c1_join d d chi
    (B.up d hd).height (B.down d hd).height
    ((B.up d hd).affine_marked_probability chi 0 0 (fun _ => 0)).2.2.1
    ((B.down d hd).affine_marked_probability chi 0 0 (fun _ => 0)).2.2.1

private theorem prefix_finite (B : Band) (d chi : ℝ) (hd : 0<d) (j : ℕ) :
    FiniteC1Control (2*(j:ℝ)*d) (B.repeated d hd j) (fun _ => chi) := by
  induction j with
  | zero =>
    refine ⟨0,fun _ => 0,monotone_const,by rfl,by simp,?_⟩
    intro i hi
    omega
  | succ j ih =>
    convert finite_c1_join (2*(j:ℝ)*d) (2*d) chi _ _ ih (loop_finite B d chi hd) using 1
    · push_cast; ring

/-- Both literal early/late functions have finite partitions with continuous
rates on each closed piece and their actual derivatives on each open piece. -/
theorem early_late_finite_c1 (B : Band) (n : ℕ) (hn : 1 ≤ n) (chi : ℝ) :
    FiniteC1Control 2 (B.early n hn) (fun _ => chi) ∧
    FiniteC1Control 2 (B.late n hn) (fun _ => chi) := by
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
  constructor
  · simpa only [Band.early,Band.earlySuffix] using finite_c1_join 1 1 chi _ _ hp he
  · simpa only [Band.late,Band.lateSuffix] using finite_c1_join 1 1 chi _ _ hp hf


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
    rw [deriv_before f g T t ht.2]
  have he1 : EqOn (fun t => F (deriv (concatenate f g T) t))
      (fun t => F (deriv g (t-T))) (uIoo T (T+U)) := by
    intro t ht
    rw [uIoo_of_le (by linarith : T≤T+U)] at ht
    rw [deriv_after f g T t ht.1]
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

private theorem loop_resource (B : Band) (d : ℝ) (hd : 0<d) (F : ℝ → ℝ) :
    IntervalIntegrable (fun t => F (deriv (B.loop d hd) t)) volume 0 (2*d) ∧
    (∫ t in (0:ℝ)..(2*d), F (deriv (B.loop d hd) t))=
      d*(F ((B.b-B.a)/d)+F (-((B.b-B.a)/d))) := by
  obtain ⟨hu,he⟩ := leg_resource (B.up d hd) F
  obtain ⟨hv,hf⟩ := leg_resource (B.down d hd) F
  have hj := derivative_integral_join d d hd.le hd.le _ _ F hu hv
  rw [he,hf] at hj
  simpa [Band.loop,Band.up,Band.down,Leg.speed,neg_div,sub_eq_neg_sub B.a B.b,
    two_mul,mul_add] using hj

private theorem prefix_resource (B : Band) (d : ℝ) (hd : 0<d) (j : ℕ) (F : ℝ → ℝ) :
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
  cases e
  · have hj := derivative_integral_join (1/2) (1/2) (by norm_num) (by norm_num) _ _ F hw hl.1
    rw [he,hl.2] at hj
    norm_num [Band.lateSuffix,Band.wait,Leg.speed] at hj ⊢
    exact ⟨hj.1,by rw [hj.2]; ring⟩
  · have hj := derivative_integral_join (1/2) (1/2) (by norm_num) (by norm_num) _ _ F hl.1 hw
    rw [hl.2,he] at hj
    norm_num [Band.earlySuffix,Band.wait,Leg.speed] at hj ⊢
    exact hj

private theorem actual_resource (B : Band) (n : ℕ) (hn : 1≤n) (F : ℝ → ℝ) (e : Bool) :
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
    dsimp [Band.halfStep]; field_simp; ring
  have hc : (n:ℝ)*Band.halfStep n=1/2 := by linarith [ht]
  rw [hv,hc] at hj
  norm_num only at hj
  cases e <;> simpa only [Bool.false_eq_true,↓reduceIte,Band.early,Band.late] using hj

/-- Length and quadratic height energy are interval integrals of the actual
derivatives, and agree for the two controls for every positive repetition count. -/
theorem early_late_integral_resources (B : Band) (n : ℕ) (hn : 1≤n) :
    (∀ e : Bool, let k := if e then B.early n hn else B.late n hn
      IntervalIntegrable (fun t => |deriv k t|) volume 0 2 ∧
      IntervalIntegrable (fun t => (deriv k t)^2) volume 0 2 ∧
      (∫ t in (0:ℝ)..2,|deriv k t|)=2*((n:ℝ)+1)*(B.b-B.a) ∧
      (∫ t in (0:ℝ)..2,(deriv k t)^2)=(4*(n:ℝ)^2+8)*(B.b-B.a)^2) := by
  intro e
  have hl := actual_resource B n hn abs e
  have hq := actual_resource B n hn (fun x => x^2) e
  have hpos : 0≤2*(n:ℝ)*(B.b-B.a) := by positivity [B.ab]
  have hpos' : 0≤4*(B.b-B.a) := by linarith [B.ab]
  dsimp only at hl hq ⊢
  refine ⟨hl.1,hq.1,?_,?_⟩
  · rw [hl.2]
    simp only [abs_of_nonneg hpos,abs_neg,abs_of_nonneg hpos',abs_zero,mul_zero,add_zero]
    ring
  · rw [hq.2]
    dsimp only
    ring

end D5.S3.Quantum.Fibers.OriginalRepeatedResources
