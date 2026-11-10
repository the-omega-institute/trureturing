/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Small
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Small
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Small and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Masks

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private submask_six from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Masks

private theorem small_odd_first (p q : ℤ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤q) :
    First p q 2 (p*q-p/4) 1 true := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ q=u+64 := ⟨q-64,by omega,by ring⟩
  rcases hp with rfl|rfl|rfl|rfl
  all_goals dsimp [First]
  all_goals refine ⟨?_,?_,?_,?_⟩
  all_goals try simp only [ite_true]
  all_goals apply le_of_sub_nonneg
  all_goals norm_num [R,A,L,K,y,Q,SecondPeakHighD.A,SecondPeakHighD.L,
    SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals ring_nf
  all_goals nlinarith [sq_nonneg u]

private theorem small_six_first (p q : ℤ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤q) :
    First p q 1 (p*q-p/4-3) 6 false := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ q=u+64 := ⟨q-64,by omega,by ring⟩
  rcases hp with rfl|rfl|rfl|rfl
  all_goals dsimp [First]
  all_goals refine ⟨?_,?_,?_,?_⟩
  all_goals try simp only [Bool.false_eq_true,ite_false]
  all_goals apply le_of_sub_nonneg
  all_goals norm_num [R,A,L,K,y,Q,SecondPeakHighD.A,SecondPeakHighD.L,
    SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals ring_nf
  all_goals nlinarith [sq_nonneg u]

private theorem exceptional_first (u : ℤ) (hu : 16≤u) :
    First 4 (4*u) 1 (11*u-1) (8*u+1) true := by
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ u=w+16 := ⟨u-16,by omega,by ring⟩
  dsimp [First]
  refine ⟨?_,?_,?_,?_⟩
  all_goals try simp only [ite_true]
  all_goals apply le_of_sub_nonneg
  all_goals norm_num [R,A,L,K,y,Q,SecondPeakHighD.A,SecondPeakHighD.L,
    SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals ring_nf
  all_goals nlinarith [sq_nonneg w]

/-- h=2, m=1 and an odd M, throughout the infinite small-p sector. -/
private theorem small_odd_exists (p q : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤q) :
    ∃ v m M : ℕ, ∃ before : Bool, Good p q 2 v m M before := by
  obtain ⟨M,hM,hsub,hdlo,hdhi⟩ := odd_mask p q (by omega) hq
  let v := p*q-p/4
  have hv : 1≤v ∧ 2*v≤4*p*q := by
    rcases hp with rfl|rfl|rfl|rfl <;> dsimp [v] <;> omega
  have hcast : (v:ℤ)=(p:ℤ)*q-(p:ℤ)/4 := by
    rcases hp with rfl|rfl|rfl|rfl <;> dsimp [v] <;> norm_num <;> omega
  have hpi : (p:ℤ)=4 ∨ (p:ℤ)=8 ∨ (p:ℤ)=16 ∨ (p:ℤ)=32 := by omega
  have hf := small_odd_first p q hpi (by exact_mod_cast hq)
  rw [←hcast] at hf
  have hhi : 5*(M:ℤ)-(y p q 2-16*(p:ℤ))≤8*(p:ℤ) := by omega
  have hsecond := second_windows p q 2 M (by omega) (by omega) (Or.inr rfl) hdlo hhi
  refine ⟨v,1,M,true,hv.1,hv.2,hM,?_,hsub,?_⟩
  · dsimp [y] at hsecond
    exact_mod_cast hsecond.2.1
  · exact windows_of_first p q 2 v 1 M true (by omega) (by omega)
      (Or.inr rfl) hf hdlo hhi

/-- h=1, m=6, with the exact residue choices valid for arbitrary q. -/
private theorem small_six_exists (p q : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤q)
    (hq8 : q%8=0) (hq5 : q%5≠0) (hex : p=4 → q%5≠1) :
    ∃ v m M : ℕ, ∃ before : Bool, Good p q 1 v m M before := by
  obtain ⟨delta,hd0,hd1,hdiv,hmod⟩ := small_delta p q hp hq hq8 hq5 hex
  let M := (8*p*(q-1)+delta)/5
  let v := p*q-p/4-3
  have heq : 5*(M:ℤ)-(y p q 1-8*(p:ℤ))=delta := by
    dsimp [M,y]
    rcases hp with rfl|rfl|rfl|rfl <;> omega
  have hM : 6<M := by
    rcases hp with rfl|rfl|rfl|rfl <;> dsimp [M] <;> omega
  have hsub : SecondPeakHighD.Submask 6 M := submask_six M hmod
  have hv : 1≤v ∧ 2*v≤4*p*q := by
    rcases hp with rfl|rfl|rfl|rfl <;> dsimp [v] <;> omega
  have hcast : (v:ℤ)=(p:ℤ)*q-(p:ℤ)/4-3 := by
    rcases hp with rfl|rfl|rfl|rfl <;> dsimp [v] <;> norm_num <;> omega
  have hpi : (p:ℤ)=4 ∨ (p:ℤ)=8 ∨ (p:ℤ)=16 ∨ (p:ℤ)=32 := by omega
  have hf := small_six_first p q hpi (by exact_mod_cast hq)
  rw [←hcast] at hf
  have hlo : (2:ℤ)≤5*(M:ℤ)-(y p q 1-8*(p:ℤ)) := by omega
  have hhi : 5*(M:ℤ)-(y p q 1-8*(p:ℤ))≤4*(p:ℤ) := by
    have hdi : (delta:ℤ)≤4*(p:ℤ) := by exact_mod_cast hd1
    omega
  have hsecond := second_windows p q 1 M (by omega) (by omega) (Or.inl rfl) hlo hhi
  refine ⟨v,6,M,false,hv.1,hv.2,hM,?_,hsub,?_⟩
  · dsimp [y] at hsecond
    exact_mod_cast hsecond.2.1
  · exact windows_of_first p q 1 v 6 M false (by omega) (by omega)
      (Or.inl rfl) hf hlo hhi

/-- Exceptional h=1,p=4 sector, with the high/low mask and a literal early ear. -/
private theorem exceptional_exists (s : ℕ) (hq : 64≤2^s) (hr : 2^s%5=1) :
    ∃ v m M : ℕ, ∃ before : Bool, Good 4 (2^s) 1 v m M before := by
  let q := 2^s
  let v := 11*(q/4)-1
  let m := 2*q+1
  let M := (32*q-27)/5
  obtain ⟨hmM,hsub,hdelta⟩ := exceptional_mask s hq hr
  change 5*(M:ℤ)-(y 4 q 1-32)=5 at hdelta
  have hq8 := dyadic_eight s hq
  have hq4 : q=4*(q/4) := by dsimp [q]; omega
  have hu : 16≤q/4 := by dsimp [q] at *; omega
  have hv : 1≤v ∧ 2*v≤4*4*q := by dsimp [v]; omega
  have hvc : (v:ℤ)=11*((q/4:ℕ):ℤ)-1 := by dsimp [v]; omega
  have hqc : (q:ℤ)=4*((q/4:ℕ):ℤ) := by exact_mod_cast hq4
  have hf := exceptional_first ((q/4:ℕ):ℤ) (by exact_mod_cast hu)
  rw [←hqc,←hvc] at hf
  have hmc : (m:ℤ)=8*((q/4:ℕ):ℤ)+1 := by dsimp [m]; push_cast; nlinarith
  rw [←hmc] at hf
  have hlo : (2:ℤ)≤5*(M:ℤ)-(y 4 q 1-32) := by omega
  have hhi : 5*(M:ℤ)-(y 4 q 1-32)≤16 := by omega
  have hsecond := second_windows 4 q 1 M (by norm_num) (by omega) (Or.inl rfl) hlo hhi
  refine ⟨v,m,M,true,hv.1,hv.2,hmM,?_,hsub,?_⟩
  · dsimp [y] at hsecond
    exact_mod_cast hsecond.2.1
  · exact windows_of_first 4 q 1 v m M true (by norm_num) (by omega)
      (Or.inl rfl) hf hlo hhi

/-- All infinite small-p branches, with no assumed certificate or mask. -/
theorem small_exists (p s h : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤2^s) (hh : h=1 ∨ h=2) :
    ∃ v m M : ℕ, ∃ before : Bool, Good p (2^s) h v m M before := by
  rcases hh with rfl|rfl
  · by_cases hex : p=4 ∧ 2^s%5=1
    · rcases hex with ⟨rfl,hr⟩
      exact exceptional_exists s hq hr
    · apply small_six_exists p (2^s) hp hq (dyadic_eight s hq)
      · have := pow_two_mod_five s
        omega
      · intro hp4 hr
        exact hex ⟨hp4,hr⟩
  · exact small_odd_exists p (2^s) hp hq

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
