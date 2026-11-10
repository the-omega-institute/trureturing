/- GID: D5/S3/Quantum/Fibers/OriginalControlComposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalControlComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary finite original controls concatenate with exact additive transport. -/

import D5.S3.Quantum.Fibers.FiniteRectangleTransport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
namespace D5.S3.Quantum.Fibers.OriginalControlComposition
open Set Filter Topology MeasureTheory intervalIntegral
open D5.S3.Quantum.Fibers.FiniteRectangleTransport
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

def FiniteC1Control (T : ℝ) (k chi : ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (time : ℕ → ℝ), Monotone time ∧ time 0 = 0 ∧ time N = T ∧
    ∀ j : ℕ, j < N → ∃ krate crate : ℝ → ℝ,
      ContinuousOn krate (uIcc (time j) (time (j+1))) ∧
      ContinuousOn crate (uIcc (time j) (time (j+1))) ∧
      ∀ t ∈ Ioo (time j) (time (j+1)),
        HasDerivAt k (krate t) t ∧ HasDerivAt chi (crate t) t

def OriginalControl (b : Base) (T : ℝ) (k chi : ℝ → ℝ) : Prop :=
  0 ≤ T ∧ ContinuousOn k (uIcc 0 T) ∧ ContinuousOn chi (uIcc 0 T) ∧
  (∀ t ∈ uIcc 0 T, k t ∈ Ioo (lower b) (upper b)) ∧
  BoundedVariationOn chi (uIcc 0 T) ∧
  ((AbsolutelyContinuousOnInterval k 0 T ∧ AbsolutelyContinuousOnInterval chi 0 T) ∨
    FiniteC1Control T k chi)

def concatenate (f g : ℝ → ℝ) (T : ℝ) (x : ℝ) : ℝ :=
  if x ≤ T then f x else f T + g (x-T) - g 0

private theorem ac_congr (f g : ℝ → ℝ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) (he : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro e hepos
  obtain ⟨d,hd,h⟩ := hf e hepos
  refine ⟨d,hd,fun E hE hdE => ?_⟩
  have hex : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2))=
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [←he (hE.1 i hi).1,←he (hE.1 i hi).2]
  rw [hex]
  exact h E hE hdE

private theorem finite_c1_ac (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℝ)
    (hcont : ContinuousOn f (uIcc 0 T))
    (N : ℕ) (time : ℕ → ℝ) (hm : Monotone time) (hz : time 0=0) (he : time N=T)
    (hc : ∀ j < N, ∃ rate : ℝ → ℝ,
      ContinuousOn rate (uIcc (time j) (time (j+1))) ∧
      ∀ t ∈ Ioo (time j) (time (j+1)), HasDerivAt f (rate t) t) :
    AbsolutelyContinuousOnInterval f 0 T := by
  have hi : ∀ j < N, IntervalIntegrable (deriv f) volume (time j) (time (j+1)) := by
    intro j hj
    obtain ⟨r,hr,hd⟩ := hc j hj
    apply hr.intervalIntegrable.congr_uIoo
    intro t ht
    rw [uIoo_of_le (hm (Nat.le_succ j))] at ht
    exact (hd t ht).deriv.symm
  have hall : IntervalIntegrable (deriv f) volume 0 T := by
    simpa [hz,he] using IntervalIntegrable.trans_iterate hi
  have hp := hall.absolutelyContinuousOnInterval_intervalIntegral (c:=0) (by simp)
  have ha := ((LipschitzWith.const (f 0)).lipschitzOnWith.absolutelyContinuousOnInterval).add hp
  apply ac_congr _ _ 0 T ha
  intro x hx
  change f 0+(∫ t in (0:ℝ)..x, deriv f t)=f x
  rw [uIcc_of_le hT] at hx
  let tx : ℕ → ℝ := fun j => min (time j) x
  have htx : Monotone tx := fun i j hij => min_le_min_right x (hm hij)
  have hxz : tx 0=0 := by simp [tx,hz,hx.1]
  have hxe : tx N=x := by simp [tx,he,hx.2]
  have hs : ∀ j < N, time j ≤ x →
      uIcc (tx j) (tx (j+1)) ⊆ uIcc (time j) (time (j+1)) := by
    intro j hj hleft t ht
    rw [uIcc_of_le (htx (Nat.le_succ j))] at ht
    rw [uIcc_of_le (hm (Nat.le_succ j))]
    exact ⟨by simpa [tx,min_eq_left hleft] using ht.1,
      ht.2.trans (min_le_left _ _)⟩
  have hix : ∀ j < N, IntervalIntegrable (deriv f) volume (tx j) (tx (j+1)) := by
    intro j hj
    by_cases hleft : time j ≤ x
    · exact (hi j hj).mono_set (hs j hj hleft)
    · have hright : x ≤ time (j+1) := (le_of_not_ge hleft).trans (hm (Nat.le_succ j))
      simp [tx,min_eq_right (le_of_not_ge hleft),min_eq_right hright]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hix
  have hval : ∀ j < N, (∫ t in (tx j)..(tx (j+1)), deriv f t)=f (tx (j+1))-f (tx j) := by
    intro j hj
    by_cases hleft : time j ≤ x
    · apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (htx (Nat.le_succ j))
      · apply hcont.mono
        rw [uIcc_of_le hT]
        change Icc (tx j) (tx (j+1)) ⊆ Icc 0 T
        intro t ht
        have hl : 0 ≤ time j := by simpa [hz] using hm (Nat.zero_le j)
        exact ⟨le_trans (by simpa [tx,min_eq_left hleft] using hl) ht.1,
          ht.2.trans ((min_le_right _ _).trans hx.2)⟩
      · intro t ht
        obtain ⟨r,hr,hd⟩ := hc j hj
        have htold : t ∈ Ioo (time j) (time (j+1)) :=
          ⟨by simpa [tx,min_eq_left hleft] using ht.1,ht.2.trans_le (min_le_left _ _)⟩
        exact (hd t htold).congr_deriv (hd t htold).deriv.symm
      · exact hix j hj
    · have hright : x ≤ time (j+1) := (le_of_not_ge hleft).trans (hm (Nat.le_succ j))
      simp [tx,min_eq_right (le_of_not_ge hleft),min_eq_right hright]
  rw [hxz,hxe] at hsum
  rw [←hsum]
  rw [Finset.sum_congr rfl (fun j hj => hval j (Finset.mem_range.mp hj))]
  rw [Finset.sum_range_sub (fun j => f (tx j)) N,hxz,hxe]
  ring


theorem original_ac (b : Base) (T : ℝ) (k chi : ℝ → ℝ)
    (hc : OriginalControl b T k chi) :
    AbsolutelyContinuousOnInterval k 0 T ∧ AbsolutelyContinuousOnInterval chi 0 T := by
  rcases hc.2.2.2.2.2 with h | ⟨N,time,hm,hz,he,hh⟩
  · exact h
  · constructor
    · apply finite_c1_ac T hc.1 k hc.2.1 N time hm hz he
      intro j hj
      obtain ⟨r,c,hr,hc,hd⟩ := hh j hj
      exact ⟨r,hr,fun t ht => (hd t ht).1⟩
    · apply finite_c1_ac T hc.1 chi hc.2.2.1 N time hm hz he
      intro j hj
      obtain ⟨r,c,hr,hc,hd⟩ := hh j hj
      exact ⟨c,hc,fun t ht => (hd t ht).2⟩

private theorem concatenate_ac (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (f g : ℝ → ℝ) (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hg : AbsolutelyContinuousOnInterval g 0 S) :
    AbsolutelyContinuousOnInterval (concatenate f g T) 0 (T+S) := by
  let r : ℝ → ℝ := fun x => if x ≤ T then deriv f x else deriv g (x-T)
  have hi0 : IntervalIntegrable r volume 0 T := by
    apply hf.intervalIntegrable_deriv.congr_uIoo
    intro x hx
    rw [uIoo_of_le hT] at hx
    simp [r,hx.2.le]
  have hi1 : IntervalIntegrable r volume T (T+S) := by
    have hg' := hg.intervalIntegrable_deriv.comp_sub_right T
    simp only [zero_add,sub_neg_eq_add] at hg'
    have hg'' : IntervalIntegrable (fun x => deriv g (x-T)) volume T (T+S) := by
      convert hg' using 1 <;> ring
    apply hg''.congr_uIoo
    intro x hx
    rw [uIoo_of_le (by linarith : T ≤ T+S)] at hx
    simp [r,not_le.mpr hx.1]
  have hi := hi0.trans hi1
  have ha := ((LipschitzWith.const (f 0)).lipschitzOnWith.absolutelyContinuousOnInterval).add
    (hi.absolutelyContinuousOnInterval_intervalIntegral (c:=0) (by simp))
  apply ac_congr _ _ 0 (T+S) ha
  intro x hx
  rw [uIcc_of_le (add_nonneg hT hS)] at hx
  change f 0+(∫ t in (0:ℝ)..x, r t)=concatenate f g T x
  by_cases hxt : x ≤ T
  · have hix : (∫ t in (0:ℝ)..x, r t)=∫ t in (0:ℝ)..x, deriv f t := by
      apply integral_congr
      intro t ht
      rw [uIcc_of_le hx.1] at ht
      simp [r,ht.2.trans hxt]
    have hfm : AbsolutelyContinuousOnInterval f 0 x := hf.mono (by
      rw [uIcc_of_le hT,uIcc_of_le hx.1]
      exact Icc_subset_Icc le_rfl hxt)
    rw [hix,hfm.integral_deriv_eq_sub]
    simp [concatenate,hxt]
  · have htx : T ≤ x := (le_of_not_ge hxt)
    have hi0x := hi0
    have hi1x := hi1.mono_set (show uIcc T x ⊆ uIcc T (T+S) by
      rw [uIcc_of_le htx,uIcc_of_le (by linarith : T ≤ T+S)]
      exact Icc_subset_Icc le_rfl hx.2)
    rw [←integral_add_adjacent_intervals hi0x hi1x]
    have he0 : (∫ t in (0:ℝ)..T,r t)=f T-f 0 := by
      rw [show (∫ t in (0:ℝ)..T,r t)=∫ t in (0:ℝ)..T,deriv f t from
        integral_congr (fun t ht => by
          rw [uIcc_of_le hT] at ht; simp [r,ht.2])]
      exact hf.integral_deriv_eq_sub
    have he1 : (∫ t in T..x,r t)=g (x-T)-g 0 := by
      rw [show (∫ t in T..x,r t)=∫ t in T..x,deriv g (t-T) from
        integral_congr_uIoo (by
          intro t ht
          rw [uIoo_of_le htx] at ht
          simp [r,not_le.mpr ht.1])]
      rw [integral_comp_sub_right,sub_self]
      exact (hg.mono (by
        rw [uIcc_of_le hS,uIcc_of_le (sub_nonneg.mpr htx)]
        exact Icc_subset_Icc le_rfl (by linarith [hx.2]))).integral_deriv_eq_sub
    rw [he0,he1]
    simp [concatenate,hxt]
    ring


private theorem concatenate_integral (b : Base) (T S : ℝ) (k chi K C : ℝ → ℝ)
    (hc : OriginalControl b T k chi) (hd : OriginalControl b S K C)
    (hjoin : k T=K 0) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Ioo (lower b) (upper b))) :
    (∫ t in (0:ℝ)..(T+S), F (concatenate k K T t)*deriv (concatenate chi C T) t)=
      (∫ t in (0:ℝ)..T, F (k t)*deriv chi t)+
      (∫ t in (0:ℝ)..S, F (K t)*deriv C t) := by
  have h0 := (original_ac b T k chi hc).2.intervalIntegrable_deriv.continuousOn_mul
    (hF.comp hc.2.1 hc.2.2.2.1)
  have h1 := (original_ac b S K C hd).2.intervalIntegrable_deriv.continuousOn_mul
    (hF.comp hd.2.1 hd.2.2.2.1)
  have he0 : EqOn (fun t => F (concatenate k K T t)*deriv (concatenate chi C T) t)
      (fun t => F (k t)*deriv chi t) (uIoo 0 T) := by
    intro t ht
    rw [uIoo_of_le hc.1] at ht
    have hd : deriv (concatenate chi C T) t=deriv chi t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Iio_mem_nhds ht.2] with x hx
      change x < T at hx
      simp [concatenate,hx.le]
    simp [concatenate,ht.2.le,hd]
  have he1 : EqOn (fun t => F (concatenate k K T t)*deriv (concatenate chi C T) t)
      (fun t => F (K (t-T))*deriv C (t-T)) (uIoo T (T+S)) := by
    intro t ht
    rw [uIoo_of_le (by linarith [hd.1] : T ≤ T+S)] at ht
    have hder : deriv (concatenate chi C T) t=deriv C (t-T) := by
      calc
        _ = deriv (fun x => chi T+C (x-T)-C 0) t := by
          apply Filter.EventuallyEq.deriv_eq
          filter_upwards [Ioi_mem_nhds ht.1] with x hx
          change T < x at hx
          simp [concatenate,not_le.mpr hx]
        _ = _ := by rw [deriv_sub_const,deriv_const_add,deriv_comp_sub_const]
    simp [concatenate,not_le.mpr ht.1,hjoin,hder]
  have h0' := h0.congr_uIoo (fun t ht => (he0 ht).symm)
  have h1s : IntervalIntegrable (fun t => F (K (t-T))*deriv C (t-T)) volume T (T+S) := by
    simpa [add_comm] using h1.comp_sub_right T
  have h1' := h1s.congr_uIoo (fun t ht => (he1 ht).symm)
  rw [←integral_add_adjacent_intervals h0' h1',integral_congr_uIoo he0,
    integral_congr_uIoo he1]
  rw [integral_comp_sub_right (fun t => F (K t)*deriv C t) T,
    sub_self,add_sub_cancel_left]

/-- The second control is translated in its real phase lift at the join. -/
theorem concatenate_original (b : Base) (T S : ℝ) (k chi K C : ℝ → ℝ)
    (hc : OriginalControl b T k chi) (hd : OriginalControl b S K C)
    (hjoin : k T=K 0) :
    OriginalControl b (T+S) (concatenate k K T) (concatenate chi C T) ∧
    EqOn (concatenate k K T) k (Icc (0:ℝ) T) ∧
    EqOn (concatenate chi C T) chi (Icc (0:ℝ) T) ∧
    (∀ s ∈ Icc (0:ℝ) S, concatenate k K T (T+s)=K s ∧
      concatenate chi C T (T+s)=chi T+C s-C 0) ∧
    concatenate chi C T (T+S)-concatenate chi C T 0=
      (chi T-chi 0)+(C S-C 0) ∧
    (∀ F : ℝ → ℝ, ContinuousOn F (Ioo (lower b) (upper b)) →
      (∫ t in (0:ℝ)..(T+S), F (concatenate k K T t)*deriv (concatenate chi C T) t)=
        (∫ t in (0:ℝ)..T, F (k t)*deriv chi t)+
        (∫ t in (0:ℝ)..S, F (K t)*deriv C t)) := by
  obtain ⟨hka,hca⟩ := original_ac b T k chi hc
  obtain ⟨hKa,hCa⟩ := original_ac b S K C hd
  have hk := concatenate_ac T S hc.1 hd.1 k K hka hKa
  have hchi := concatenate_ac T S hc.1 hd.1 chi C hca hCa
  have htail : ∀ s ∈ Icc (0:ℝ) S, concatenate k K T (T+s)=K s ∧
      concatenate chi C T (T+s)=chi T+C s-C 0 := by
    intro s hs
    by_cases hz : s=0
    · subst s; simp [concatenate,hjoin]
    · have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
      have hne : ¬T+s ≤ T := by linarith
      simp [concatenate,hne,hjoin]
  refine ⟨⟨add_nonneg hc.1 hd.1,hk.continuousOn,hchi.continuousOn,?_,
    hchi.boundedVariationOn,Or.inl ⟨hk,hchi⟩⟩,?_,?_,htail,?_,concatenate_integral b T S k chi K C hc hd hjoin⟩
  · intro x hx
    rw [uIcc_of_le (add_nonneg hc.1 hd.1)] at hx
    by_cases hxt : x ≤ T
    · simp only [concatenate,if_pos hxt]
      exact hc.2.2.2.1 x (by rw [uIcc_of_le hc.1]; exact ⟨hx.1,hxt⟩)
    · have hs : x-T ∈ Icc (0:ℝ) S := ⟨by linarith,by linarith [hx.2]⟩
      have he := (htail (x-T) hs).1
      simp only [add_sub_cancel] at he
      rw [he]
      exact hd.2.2.2.1 (x-T) (by rwa [uIcc_of_le hd.1])
  · intro x hx; simp [concatenate,hx.2]
  · intro x hx; simp [concatenate,hx.2]
  · rw [(htail S ⟨hd.1,le_rfl⟩).2]
    simp [concatenate,hc.1]
    ring

end D5.S3.Quantum.Fibers.OriginalControlComposition
