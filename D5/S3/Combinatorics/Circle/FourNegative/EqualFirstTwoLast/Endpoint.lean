/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoLast/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoLast/Endpoint
   mirror-E: none(waiver:actual-physical-joint-lift)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical joint lift for every natural equal-first-two-last gap pair. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Source
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Endpoint

/-! Source realization from the caller's exact ordinary construction.
The full unrestricted four-gap J and C3.1 remain open. Finite diagnostics are
not premises. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast
open SourceWidth PeriodicShortening RunFirstEarTransport
open private A B L M N Bn Ln Mn Margin UpperBounds LowerBounds upper_chart lower_chart
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Arithmetic
open private oldValue newValue seed native positive_pair gates_of_margins native_inventory realize
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Source
open private Gates four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option maxHeartbeats 2400000 in
private theorem upper (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (hchart : s+2 ≤ t) :
    ∃ sigma : List (Fin (s+t+s+s)),
      OriginalOrder (s+t+s+s) (seed s t) sigma ∧
      OriginalOrder (s+t+s+s+1) (2*seed s t) (earWord (s+t+s+s) sigma (s+1)) := by
  let k := s+t+s+s
  let q : ℤ := 2^s
  let z : ℤ := 2^t
  let f := oldValue s t
  let g := newValue s t
  let h := t-s-2
  let m : ℤ := 2^h
  let v := 3*m
  have he : t=s+h+2 := by dsimp [h]; omega
  have hinside : h+2 ≤ t-1 := by omega
  have hq : 4 ≤ q := by
    simpa [q] using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hs
  have hm : 1 ≤ m := by dsimp [m]; exact one_le_pow₀ (by norm_num)
  have hz : z=4*q*m := by
    change (2:ℤ)^t=4*2^s*2^h
    rw [he,pow_add,pow_add]
    norm_num <;> ring
  have hb : UpperBounds q z v := by
    dsimp only [v]; rw [hz]; exact upper_chart q m hq hm
  rcases hb with ⟨hf1,hf2,hf3,hf4,hg1,hg2,hg3,hg4⟩
  have rows := native s t hs ht
  change Rows s t q z f g at rows
  let Up := List.range' 0 (s-1)
  let Vp := List.range' s (t-1)
  let Wp := List.range' (s+t) (s-1)
  let Xp := List.range' (s+t+s) (s-1)
  -- Relative V mask [0,h) union {h+1}; R is its increasing complement.
  let T := List.range' s h++[s+h+1]
  let R := [s+h]++List.range' (s+h+2) (t-h-3)
  have hsplit : (R++T).Perm Vp := by
    have hreorder : (R++T).Perm
        ((List.range' s h++[s+h])++[s+h+1]++List.range' (s+h+2) (t-h-3)) := by
      apply Multiset.coe_eq_coe.mp
      simp only [R,T,←Multiset.coe_add]
      ac_rfl
    apply hreorder.trans
    apply List.Perm.of_eq
    rw [show List.range' s h++[s+h]=List.range' s (h+1) from
      (List.range'_1_concat (s:=s) (n:=h)).symm]
    rw [show List.range' s (h+1)++[s+h+1]=List.range' s (h+2) by
      simpa only [show s+(h+1)=s+h+1 by omega,show h+1+1=h+2 by omega] using
        (List.range'_1_concat (s:=s) (n:=h+1)).symm]
    simpa only [Vp,show s+(h+2)=s+h+2 by omega,
      show (h+2)+(t-h-3)=t-1 by omega] using
      List.range'_append_1 (s:=s) (m:=h+2) (n:=t-h-3)
  have massT : (T.map f).sum=(v-1)*B q ∧ (T.map g).sum=(v-1)*Bn q := by
    have hsumf := ladder_sum f s h (B q) (fun i hi => (rows.posV i (by omega)).1)
    have hsumg := ladder_sum g s h (Bn q) (fun i hi => (rows.posV i (by omega)).2)
    have hbit := rows.posV (h+1) (by omega)
    simp only [T,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      show s+(h+1)=s+h+1 by omega] at hsumf hsumg hbit ⊢
    rw [hsumf,hsumg,hbit.1,hbit.2]
    dsimp [v,m]; rw [pow_succ]; exact ⟨by ring,by ring⟩
  have splitf := (hsplit.map f).sum_eq
  have splitg := (hsplit.map g).sum_eq
  simp only [List.map_append,List.sum_append,massT.1,Up,Vp] at splitf
  simp only [List.map_append,List.sum_append,massT.2,Up,Vp] at splitg
  have hpU := positive_pair f g (A q z) (2*A q z) 0 (s-1)
    rows.a_nonneg (by have := rows.a_nonneg; omega)
    (by intro i hi; simpa only [Nat.zero_add] using rows.posU i hi)
  have hpV := positive_pair f g (B q) (Bn q) s (t-1)
    rows.b_nonneg rows.bn_nonneg rows.posV
  have hpW := positive_pair f g (L q z) (Ln q z) (s+t) (s-1)
    rows.l_nonneg rows.ln_nonneg rows.posW
  have hpX := positive_pair f g (M q z) (Mn q z) (s+t+s) (s-1)
    rows.m_nonneg rows.mn_nonneg rows.posX
  have hpR : ∀ i∈R, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    exact hpV i (hsplit.mem_iff.mp (List.mem_append_left T hi))
  have hpT : ∀ i∈T, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    exact hpV i (hsplit.mem_iff.mp (List.mem_append_right R hi))
  let P1 := R
  let P2 := Xp
  let P3 := Wp
  let P4 := Up++T
  let P2n := [k]++P2
  have hp4 : ∀ i∈P4, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact hpU i hi
    · exact hpT i hi
  have hp2n : ∀ i∈P2n, 0 ≤ g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · rw [List.mem_singleton.mp hi,rows.fresh]; exact rows.a_nonneg
    · exact (hpX i hi).2
  have gatesf : Gates (N q z/2)
      (P1.map f).sum (f (s+t-1))
      (P2.map f).sum (f (s+t+s+s-1))
      (P3.map f).sum (f (s+t+s-1))
      (P4.map f).sum (f (s-1)) := by
    refine gates_of_margins (D:=N q z)
      (S1:=L q z-v*B q) (S2:=L q z+A q z-M q z-v*B q) (S3:=A q z-v*B q)
      (J1:=L q z) (J2:=A q z) (J3:=M q z) (J4:=B q)
      (by have := rows.mod_nonneg; omega) (by omega) ?_ ?_ ?_ ?_
      rows.stepV.1 rows.stepX.1 rows.stepW.1 rows.stepU.1
      hf1 hf2 hf3 hf4
    · dsimp only [P1,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetV.1,splitf]
    · dsimp only [P2,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetX.1]
    · dsimp only [P3,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetW.1]
    · simp only [P4,Up,Vp,List.map_append,List.sum_append,massT.1]
      nlinarith only [rows.packetU.1]
  have gatesg : Gates (N q z)
      (P1.map g).sum (g (s+t-1))
      (P2n.map g).sum (g (s+t+s+s-1))
      (P3.map g).sum (g (s+t+s-1))
      (P4.map g).sum (g (s-1)) := by
    refine gates_of_margins (D:=2*N q z+1)
      (S1:=Ln q z-v*Bn q) (S2:=Ln q z+2*A q z-Mn q z-v*Bn q) (S3:=2*A q z-v*Bn q)
      (J1:=Ln q z) (J2:=A q z) (J3:=Mn q z) (J4:=Bn q)
      (by have := rows.mod_nonneg; omega) (by omega) ?_ ?_ ?_ ?_
      rows.stepV.2 rows.stepX.2 rows.stepW.2 rows.stepU.2
      hg1 hg2 hg3 hg4
    · dsimp only [P1,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetV.2,splitg]
    · simp only [P2n,P2,Xp,k,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,rows.fresh]
      nlinarith only [rows.packetX.2]
    · dsimp only [P3,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetW.2]
    · simp only [P4,Up,Vp,List.map_append,List.sum_append,massT.2]
      nlinarith only [rows.packetU.2]
  let pre := P1++[s+t-1]
  let post := P2++[s+t+s+s-1]++P3++[s+t+s-1]++P4++[s-1]
  have hold : InStrip f (N q z/2) 0 (pre++post) := by
    simpa only [pre,post,List.append_assoc,List.nil_append] using
    four_strip f (N q z/2) P1 P2 P3 P4 (s+t-1) (s+t+s+s-1) (s+t+s-1) (s-1)
      (fun i hi => (hpR i hi).1) (fun i hi => (hpX i hi).1) (fun i hi => (hpW i hi).1) (fun i hi => (hp4 i hi).1) gatesf
  have hnew : InStrip g (N q z) 0 (pre++k::post) := by
    simpa only [pre,post,P2n,List.append_assoc,List.singleton_append,
      List.cons_append,List.nil_append] using
    four_strip g (N q z) P1 P2n P3 P4 (s+t-1) (s+t+s+s-1) (s+t+s-1) (s-1)
      (fun i hi => (hpR i hi).2) hp2n (fun i hi => (hpW i hi).2) (fun i hi => (hp4 i hi).2) gatesg
  have hperm : (pre++post).Perm (List.range k) := by
    have hreorder : (pre++post).Perm
        ((Up++[s-1])++((R++T)++[s+t-1])++(Wp++[s+t+s-1])++(Xp++[s+t+s+s-1])) := by
      apply Multiset.coe_eq_coe.mp
      simp only [pre,post,P1,P2,P3,P4,←Multiset.coe_add,Multiset.coe_nil,zero_add]
      ac_rfl
    apply hreorder.trans
    have hb := (((List.Perm.refl (Up++[s-1])).append
      (hsplit.append_right [s+t-1])).append (List.Perm.refl (Wp++[s+t+s-1]))).append
      (List.Perm.refl (Xp++[s+t+s+s-1]))
    exact hb.trans (List.Perm.of_eq (native_inventory s t hs ht))
  have hlen : pre.length=s+1 := by
    simp only [pre,P1,R,List.length_append,List.length_singleton,List.length_range']
    omega
  exact realize s t (s+1) hs ht pre post hlen hperm hold hnew

set_option maxHeartbeats 2400000 in
private theorem lower (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (hchart : t+2 ≤ s) :
    ∃ sigma : List (Fin (s+t+s+s)),
      OriginalOrder (s+t+s+s) (seed s t) sigma ∧
      OriginalOrder (s+t+s+s+1) (2*seed s t) (earWord (s+t+s+s) sigma (0)) := by
  let k := s+t+s+s
  let q : ℤ := 2^s
  let z : ℤ := 2^t
  let f := oldValue s t
  let g := newValue s t
  let h := s-t-1
  let m : ℤ := 2^h
  let p := m-1
  have he : s=t+h+1 := by dsimp [h]; omega
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hinside : h ≤ s-3 := by omega
  have hz : 4 ≤ z := by
    simpa [z] using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) ht
  have hm : 2 ≤ m := by
    simpa [m] using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hh
  have hq : q=2*z*m := by
    change (2:ℤ)^s=2*2^t*2^h
    rw [he,pow_add,pow_add]
    norm_num <;> ring
  have hb : LowerBounds q z p := by
    dsimp only [p]; rw [hq]; exact lower_chart z m hz hm
  rcases hb with ⟨hf1,hf2,hf3,hf4,hg1,hg2,hg3,hg4,hfresh0,hfreshN⟩
  have rows := native s t hs ht
  change Rows s t q z f g at rows
  let Up := List.range' 0 (s-1)
  let Vp := List.range' s (t-1)
  let Wp := List.range' (s+t) (s-1)
  let Xp := List.range' (s+t+s) (s-1)
  -- Relative U mask [0,h); no original terminal belongs to it.
  let T := List.range' 0 h
  let R := List.range' h (s-1-h)
  have hsplit : (R++T).Perm Up := by
    apply List.perm_append_comm.trans
    apply List.Perm.of_eq
    simpa only [T,R,Up,Nat.zero_add,show h+(s-1-h)=s-1 by omega] using
      List.range'_append_1 (s:=0) (m:=h) (n:=s-1-h)
  have massT : (T.map f).sum=p*A q z ∧ (T.map g).sum=2*p*A q z := by
    have hf := ladder_sum f 0 h (A q z)
      (by intro i hi; simpa only [Nat.zero_add] using (rows.posU i (by omega)).1)
    have hg := ladder_sum g 0 h (2*A q z)
      (by intro i hi; simpa only [Nat.zero_add] using (rows.posU i (by omega)).2)
    rw [hf,hg]
    dsimp [p,m]; exact ⟨by ring,by ring⟩
  have splitf := (hsplit.map f).sum_eq
  have splitg := (hsplit.map g).sum_eq
  simp only [List.map_append,List.sum_append,massT.1,Up,Vp] at splitf
  simp only [List.map_append,List.sum_append,massT.2,Up,Vp] at splitg
  have hpU := positive_pair f g (A q z) (2*A q z) 0 (s-1)
    rows.a_nonneg (by have := rows.a_nonneg; omega)
    (by intro i hi; simpa only [Nat.zero_add] using rows.posU i hi)
  have hpV := positive_pair f g (B q) (Bn q) s (t-1)
    rows.b_nonneg rows.bn_nonneg rows.posV
  have hpW := positive_pair f g (L q z) (Ln q z) (s+t) (s-1)
    rows.l_nonneg rows.ln_nonneg rows.posW
  have hpX := positive_pair f g (M q z) (Mn q z) (s+t+s) (s-1)
    rows.m_nonneg rows.mn_nonneg rows.posX
  have hpR : ∀ i∈R, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    exact hpU i (hsplit.mem_iff.mp (List.mem_append_left T hi))
  have hpT : ∀ i∈T, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    exact hpU i (hsplit.mem_iff.mp (List.mem_append_right R hi))
  let P1 := Xp
  let P2 := Wp
  let P3 := R
  -- T precedes Vp, so each positive bank is in physical index order.
  let P4 := T++Vp
  let P1n := [k]++P1
  have hp4 : ∀ i∈P4, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact hpT i hi
    · exact hpV i hi
  have hfresh : 0 ≤ g k ∧ g k ≤ N q z := by
    rw [rows.fresh]; exact ⟨hfresh0,by omega⟩
  have hp1n : ∀ i∈P1n, 0 ≤ g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · rw [List.mem_singleton.mp hi]; exact hfresh.1
    · exact (hpX i hi).2
  have gatesf : Gates (N q z/2)
      (P1.map f).sum (f (s+t+s+s-1))
      (P2.map f).sum (f (s+t+s-1))
      (P3.map f).sum (f (s-1))
      (P4.map f).sum (f (s+t-1)) := by
    refine gates_of_margins (D:=N q z)
      (S1:=A q z-M q z) (S2:=A q z-L q z) (S3:=B q-L q z-p*A q z)
      (J1:=A q z) (J2:=M q z) (J3:=B q) (J4:=L q z)
      (by have := rows.mod_nonneg; omega) (by omega) ?_ ?_ ?_ ?_
      rows.stepX.1 rows.stepW.1 rows.stepU.1 rows.stepV.1
      hf1 hf2 hf3 hf4
    · dsimp only [P1,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetX.1]
    · dsimp only [P2,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetW.1]
    · dsimp only [P3,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetU.1,splitf]
    · simp only [P4,Up,Vp,List.map_append,List.sum_append,massT.1]
      nlinarith only [rows.packetV.1]
  have gatesg : Gates (N q z)
      (P1n.map g).sum (g (s+t+s+s-1))
      (P2.map g).sum (g (s+t+s-1))
      (P3.map g).sum (g (s-1))
      (P4.map g).sum (g (s+t-1)) := by
    refine gates_of_margins (D:=2*N q z+1)
      (S1:=2*A q z-Mn q z) (S2:=2*A q z-Ln q z) (S3:=Bn q-Ln q z-2*p*A q z)
      (J1:=A q z) (J2:=Mn q z) (J3:=Bn q) (J4:=Ln q z)
      (by have := rows.mod_nonneg; omega) (by omega) ?_ ?_ ?_ ?_
      rows.stepX.2 rows.stepW.2 rows.stepU.2 rows.stepV.2
      hg1 hg2 hg3 hg4
    · simp only [P1n,P1,Xp,k,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,rows.fresh]
      nlinarith only [rows.packetX.2]
    · dsimp only [P2,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetW.2]
    · dsimp only [P3,Up,Vp,Wp,Xp]
      nlinarith only [rows.packetU.2,splitg]
    · simp only [P4,Up,Vp,List.map_append,List.sum_append,massT.2]
      nlinarith only [rows.packetV.2]
  let pre : List ℕ := []
  let post := P1++[s+t+s+s-1]++P2++[s+t+s-1]++P3++[s-1]++P4++[s+t-1]
  have hold : InStrip f (N q z/2) 0 (pre++post) := by
    simpa only [pre,post,List.append_assoc,List.nil_append] using
    four_strip f (N q z/2) P1 P2 P3 P4 (s+t+s+s-1) (s+t+s-1) (s-1) (s+t-1)
      (fun i hi => (hpX i hi).1) (fun i hi => (hpW i hi).1) (fun i hi => (hpR i hi).1) (fun i hi => (hp4 i hi).1) gatesf
  have hnew : InStrip g (N q z) 0 (pre++k::post) := by
    simpa only [pre,post,P1n,List.append_assoc,List.singleton_append,
      List.cons_append,List.nil_append] using
    four_strip g (N q z) P1n P2 P3 P4 (s+t+s+s-1) (s+t+s-1) (s-1) (s+t-1)
      hp1n (fun i hi => (hpW i hi).2) (fun i hi => (hpR i hi).2) (fun i hi => (hp4 i hi).2) gatesg
  have hperm : (pre++post).Perm (List.range k) := by
    have hreorder : (pre++post).Perm
        (((R++T)++[s-1])++(Vp++[s+t-1])++(Wp++[s+t+s-1])++(Xp++[s+t+s+s-1])) := by
      apply Multiset.coe_eq_coe.mp
      simp only [pre,post,P1,P2,P3,P4,←Multiset.coe_add,Multiset.coe_nil,zero_add]
      ac_rfl
    apply hreorder.trans
    have hb := (((hsplit.append_right [s-1]).append
      (List.Perm.refl (Vp++[s+t-1]))).append (List.Perm.refl (Wp++[s+t+s-1]))).append
      (List.Perm.refl (Xp++[s+t+s+s-1]))
    exact hb.trans (List.Perm.of_eq (native_inventory s t hs ht))
  have hlen : pre.length=0 := by
    rfl
  exact realize s t (0) hs ht pre post hlen hperm hold hnew

/-- All natural s,t≥2, with one permutation of the original physical labels
and one literal ear cut for the two complete actual OriginalOrder predicates. -/
theorem actualSource_equal_first_two_last_joint_lift (s t : ℕ)
    (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∃ sigma : List (Fin (3*s+t)), ∃ cut : ℕ, cut ≤ 3*s+t ∧
      OriginalOrder (3*s+t) (1+2^s+2^(s+s)+2^(s+s+t)) sigma ∧
      OriginalOrder (3*s+t+1) (2*(1+2^s+2^(s+s)+2^(s+s+t)))
        (earWord (3*s+t) sigma cut) := by
  by_cases hu : s+2 ≤ t
  · have hu' : ∃ sigma : List (Fin (3*s+t)),
        OriginalOrder (3*s+t) (1+2^s+2^(s+s)+2^(s+s+t)) sigma ∧
        OriginalOrder (3*s+t+1) (2*(1+2^s+2^(s+s)+2^(s+s+t)))
          (earWord (3*s+t) sigma (s+1)) := by
      have hk : s+t+s+s = 3*s+t := by omega
      have h := upper s t hs ht hu
      rw [hk] at h
      simpa [seed] using h
    obtain ⟨sigma,hold,hnew⟩ := hu'
    exact ⟨sigma,s+1,by omega,hold,hnew⟩
  · by_cases hl : t+2 ≤ s
    · have hl' : ∃ sigma : List (Fin (3*s+t)),
          OriginalOrder (3*s+t) (1+2^s+2^(s+s)+2^(s+s+t)) sigma ∧
          OriginalOrder (3*s+t+1) (2*(1+2^s+2^(s+s)+2^(s+s+t)))
            (earWord (3*s+t) sigma 0) := by
        have hk : s+t+s+s = 3*s+t := by omega
        have h := lower s t hs ht hl
        rw [hk] at h
        simpa [seed] using h
      obtain ⟨sigma,hold,hnew⟩ := hl'
      exact ⟨sigma,0,by omega,hold,hnew⟩
    · have hts : t ≤ s+1 := by omega
      have hst : s ≤ t+1 := by omega
      have hbal : max (max s s) (max t s) ≤ min (min s s) (min t s)+1 := by omega
      have hk : s+s+t+s = 3*s+t := by omega
      have h := BalancedGaps.actualSource_balanced_gaps_joint_lift s s t s hs hs ht hs hbal
      rw [hk] at h
      exact h

#print axioms actualSource_equal_first_two_last_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast
