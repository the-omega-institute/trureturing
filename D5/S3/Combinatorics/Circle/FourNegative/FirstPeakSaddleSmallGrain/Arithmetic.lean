/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Native small-c2 choice, capacities and direct submask construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain.Certificates
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.ModTen

/-! SOURCE_ONLY_UNCOMPILED. No fixed-q, grain bound or anchor is imposed.
The exceptional all-one mask and the even-s/r=1-or-2 submask are retained. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain
open private half_power from D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint
open private phase_cover from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.ModTen
open private
  margin Margins chart_K1_J1_t8 chart_K1_J1_0 chart_K1_J1_1
  chart_K1_J1_2 chart_K1_J1_3 chart_K1_J2_t8 chart_K1_J2_0 chart_K1_J2_1
  chart_K1_J2_2 chart_K1_J2_3 chart_K2_J1_t8 chart_K2_J1_0 chart_K2_J1_1
  chart_K2_J1_2 chart_K2_J1_3
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain.Certificates

private theorem ratio_cases (a b d : ℕ) (hdb : d<b) (hba : b<a) (ha : a≤d+3) :
    (a=d+2 ∧ b=d+1) ∨ (a=d+3 ∧ b=d+1) ∨ (a=d+3 ∧ b=d+2) := by omega

private structure Choice (a b d : ℕ) where
  s : ℕ
  r : ℕ
  h : ℕ
  v : ℕ
  bounds : 1≤r ∧ r≤s ∧ s≤2^(a-1) ∧ v<2^(d-1) ∧ h<2^(b-1)
  submask : ∀ e<a-1, (r-1).testBit e=true → (s-1).testBit e=true
  good : Margins (2^d) (2^a) (2^b) s r h v

private theorem low_submask (s r : ℕ) (hs : 1≤s) (hr : r=1 ∨ r=2)
    (heven : s%2=0) : ∀ e : ℕ, (r-1).testBit e=true → (s-1).testBit e=true := by
  intro e he
  rcases hr with rfl|rfl
  · simp at he
  · by_cases hz : e=0
    · subst e
      have hm : (s-1)%2=1 := by omega
      simp [Nat.testBit_zero,hm]
    · have hp : 1<(2:ℕ)^e := by
        have hp := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤e by omega)
        norm_num at hp
        omega
      have hf : (1:ℕ).testBit e=false := Nat.testBit_eq_false_of_lt hp
      norm_num only [show 2-1=1 by decide] at he
      rw [hf] at he
      contradiction

private def choice_of_margins (a b d s r h v : ℕ) (hd : 3≤d) (hdb : d<b)
    (hba : b<a) (hm : Margins (2^d) (2^a) (2^b) s r h v)
    (hb : ∀ e<a-1, (r-1).testBit e=true → (s-1).testBit e=true) : Choice a b d := by
  have h12 := hm 12
  have h13 := hm 13
  have h14 := hm 14
  have h15 := hm 15
  have h17 := hm 17
  have h18 := hm 18
  dsimp [margin] at h12 h13 h14 h15 h17 h18
  have hx := half_power a (by omega)
  have hy := half_power b (by omega)
  have ht := half_power d (by omega)
  refine ⟨s,r,h,v,?_,hb,hm⟩
  constructor
  · exact_mod_cast (show (1:ℤ)≤r by omega)
  constructor
  · exact_mod_cast (show (r:ℤ)≤s by omega)
  constructor
  · exact_mod_cast (show (s:ℤ)≤2^(a-1) by omega)
  constructor
  · exact_mod_cast (show (v:ℤ)<2^(d-1) by omega)
  · have hh : (0:ℤ)≤h := by positivity
    have hp : (0:ℤ)<2^(b-1) := by positivity
    exact_mod_cast (show (h:ℤ)<2^(b-1) by omega)

private theorem select_chart (a b d K J : ℕ) (hd : 3≤d) (hdb : d<b) (hba : b<a)
    (hpair : (K=1 ∧ J=1) ∨ (K=1 ∧ J=2) ∨ (K=2 ∧ J=1))
    (hx : (2:ℕ)^a=4*K*J*2^d) (hy : (2:ℕ)^b=2*K*2^d) : Nonempty (Choice a b d) := by
  classical
  rcases hpair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases phase_cover d hd with he|⟨T,ht⟩|⟨T,ht⟩|⟨T,ht⟩|⟨T,ht⟩
    · have ht : (2:ℕ)^d=8 := by rw [he]; norm_num
      let s : ℕ := 16
      let r : ℕ := 4
      let h : ℕ := 0
      let v : ℕ := 0
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J1_t8
        have hxi : (2:ℤ)^a = 4*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 8 := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
    · let s : ℕ := 1*(28+20*T)
      let r : ℕ := 1
      let h : ℕ := 1
      let v : ℕ := 2+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J1_0 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 4*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 16+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hs : 1≤s := by dsimp [s]; omega
      have hr : r=1 ∨ r=2 := by dsimp [r]; decide
      have hv : s%2=0 := by dsimp [s]; omega
      intro e _ he
      exact low_submask s r hs hr hv e he
    · let s : ℕ := 1*(60+20*T)
      let r : ℕ := 1
      let h : ℕ := 2
      let v : ℕ := 4+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J1_1 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 4*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 32+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hs : 1≤s := by dsimp [s]; omega
      have hr : r=1 ∨ r=2 := by dsimp [r]; decide
      have hv : s%2=0 := by dsimp [s]; omega
      intro e _ he
      exact low_submask s r hs hr hv e he
    · let s : ℕ := 1*(128+20*T)
      let r : ℕ := 5
      let h : ℕ := 1
      let v : ℕ := 6+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J1_2 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 4*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 64+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
    · let s : ℕ := 1*(256+20*T)
      let r : ℕ := 5
      let h : ℕ := 0
      let v : ℕ := 12+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J1_3 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 4*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 128+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
  · rcases phase_cover d hd with he|⟨T,ht⟩|⟨T,ht⟩|⟨T,ht⟩|⟨T,ht⟩
    · have ht : (2:ℕ)^d=8 := by rw [he]; norm_num
      let s : ℕ := 32
      let r : ℕ := 8
      let h : ℕ := 0
      let v : ℕ := 0
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J2_t8
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 8 := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
    · let s : ℕ := 2*(28+20*T)
      let r : ℕ := 2
      let h : ℕ := 1
      let v : ℕ := 2+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J2_0 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 16+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hs : 1≤s := by dsimp [s]; omega
      have hr : r=1 ∨ r=2 := by dsimp [r]; decide
      have hv : s%2=0 := by dsimp [s]; omega
      intro e _ he
      exact low_submask s r hs hr hv e he
    · let s : ℕ := 2*(60+20*T)
      let r : ℕ := 2
      let h : ℕ := 2
      let v : ℕ := 4+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J2_1 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 32+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hs : 1≤s := by dsimp [s]; omega
      have hr : r=1 ∨ r=2 := by dsimp [r]; decide
      have hv : s%2=0 := by dsimp [s]; omega
      intro e _ he
      exact low_submask s r hs hr hv e he
    · let s : ℕ := 2*(128+20*T)
      let r : ℕ := 10
      let h : ℕ := 1
      let v : ℕ := 6+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J2_2 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 64+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
    · let s : ℕ := 2*(256+20*T)
      let r : ℕ := 10
      let h : ℕ := 0
      let v : ℕ := 12+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K1_J2_3 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 2*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 128+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
  · rcases phase_cover d hd with he|⟨T,ht⟩|⟨T,ht⟩|⟨T,ht⟩|⟨T,ht⟩
    · have ht : (2:ℕ)^d=8 := by rw [he]; norm_num
      let s : ℕ := 32
      let r : ℕ := 8
      let h : ℕ := 0
      let v : ℕ := 0
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K2_J1_t8
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 4*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 8 := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
    · let s : ℕ := 2*(28+20*T)
      let r : ℕ := 1
      let h : ℕ := 2
      let v : ℕ := 2+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K2_J1_0 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 4*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 16+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hs : 1≤s := by dsimp [s]; omega
      have hr : r=1 ∨ r=2 := by dsimp [r]; decide
      have hv : s%2=0 := by dsimp [s]; omega
      intro e _ he
      exact low_submask s r hs hr hv e he
    · let s : ℕ := 2*(60+20*T)
      let r : ℕ := 1
      let h : ℕ := 4
      let v : ℕ := 4+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K2_J1_1 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 4*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 32+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hs : 1≤s := by dsimp [s]; omega
      have hr : r=1 ∨ r=2 := by dsimp [r]; decide
      have hv : s%2=0 := by dsimp [s]; omega
      intro e _ he
      exact low_submask s r hs hr hv e he
    · let s : ℕ := 2*(128+20*T)
      let r : ℕ := 9
      let h : ℕ := 2
      let v : ℕ := 6+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K2_J1_2 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 4*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 64+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]
    · let s : ℕ := 2*(256+20*T)
      let r : ℕ := 9
      let h : ℕ := 0
      let v : ℕ := 12+T
      have hm : Margins (2^d) (2^a) (2^b) s r h v := by
        have hc := chart_K2_J1_3 (T:ℤ) (by positivity)
        have hxi : (2:ℤ)^a = 8*(2:ℤ)^d := by exact_mod_cast hx
        have hyi : (2:ℤ)^b = 4*(2:ℤ)^d := by exact_mod_cast hy
        have hti : (2:ℤ)^d = 128+10*(T:ℤ) := by exact_mod_cast ht
        convert hc using 1 <;> dsimp [s,r,h,v] <;> push_cast <;> (try simp only [hxi,hyi,hti]) <;> ring
      refine ⟨?_⟩
      apply choice_of_margins a b d s r h v hd hdb hba hm
      have hh := half_power a (by omega)
      have hhn : (2:ℕ)^a=2*2^(a-1) := by exact_mod_cast hh
      have hs : s=2^(a-1) := by
        rw [hx,ht] at hhn
        dsimp [s]
        omega
      intro e he _
      rw [hs]
      simp [Nat.testBit_two_pow_sub_one,he]

private theorem arithmetic_choice_exists (a b d : ℕ) (hd : 3≤d) (hdb : d<b)
    (hba : b<a) (ha : a≤d+3) : Nonempty (Choice a b d) := by
  rcases ratio_cases a b d hdb hba ha with ⟨ha',hb'⟩|⟨ha',hb'⟩|⟨ha',hb'⟩
  · apply select_chart a b d 1 1 hd hdb hba (Or.inl ⟨rfl,rfl⟩)
    · rw [ha']; simp only [pow_add]; norm_num; ring
    · rw [hb']; simp only [pow_add]; norm_num; ring
  · apply select_chart a b d 1 2 hd hdb hba (Or.inr (Or.inl ⟨rfl,rfl⟩))
    · rw [ha']; simp only [pow_add]; norm_num; ring
    · rw [hb']; simp only [pow_add]; norm_num; ring
  · apply select_chart a b d 2 1 hd hdb hba (Or.inr (Or.inr ⟨rfl,rfl⟩))
    · rw [ha']; simp only [pow_add]; norm_num; ring
    · rw [hb']; simp only [pow_add]; norm_num; ring

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain
