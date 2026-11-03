import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.AfterW
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

/-! UNELABORATED. Unbounded large-third ceiling selector. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open private A B L K SU SV SW AfterWWindows afterW_windows pow_split pow_lower
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private Joint from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source
open private afterW_realize
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.AfterW
open private floor_bounds
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

set_option maxHeartbeats 2000000 in
private theorem large_slacks (s y m : ℤ) (hs : 2 ≤ s) (hy : 4 ≤ y) (hm : 8 ≤ m) :
    6*s < B (s*y) y ∧ 6*B (s*y) y < A (s*y) y (m*(s*y)) ∧
    A (s*y) y (m*(s*y)) < m*B (s*y) y ∧
    2*L (s*y) (m*(s*y))+1 < (4*s-1)*A (s*y) y (m*(s*y)) ∧
    0 < SW (s*y) y (m*(s*y))-2*A (s*y) y (m*(s*y)) := by
  obtain ⟨S,hS,rfl⟩ : ∃ S : ℤ, 0 ≤ S ∧ s=2+S := ⟨s-2,by omega,by ring⟩
  obtain ⟨Y,hY,rfl⟩ : ∃ Y : ℤ, 0 ≤ Y ∧ y=4+Y := ⟨y-4,by omega,by ring⟩
  obtain ⟨M,hM,rfl⟩ : ∃ M : ℤ, 0 ≤ M ∧ m=8+M := ⟨m-8,by omega,by ring⟩
  repeat' constructor
  all_goals apply sub_pos.mp
  all_goals dsimp [A,B,L,K,SU,SV,SW]
  all_goals ring_nf
  all_goals positivity

private theorem large_selector (s y m : ℤ) (hs : 2 ≤ s) (hy : 4 ≤ y) (hm : 8 ≤ m) :
    ∃ v : ℤ, 1 ≤ v ∧ v < s*m ∧
      AfterWWindows (s*y) y (m*(s*y)) s v := by
  let x := s*y
  let z := m*x
  let AA := A x y z
  let BB := B x y
  let UU := SU x y
  let v := ((4*s-1)*AA)/(2*UU)+1
  obtain ⟨hBs,hAB,hmB,hfirst,hsecond⟩ := large_slacks s y m hs hy hm
  change 6*s < BB at hBs
  change 6*BB < AA at hAB
  change AA < m*BB at hmB
  have hB : 0 < BB := by omega
  have hU : UU=2*BB-1 := rfl
  have hUpos : 0 < UU := by omega
  have hA : 0 < AA := by omega
  have hnum : 0 ≤ (4*s-1)*AA := mul_nonneg (by omega) hA.le
  have hv1 : 1 ≤ v := by
    have := Int.ediv_nonneg hnum (show 0 ≤ 2*UU by omega)
    dsimp [v]; omega
  have hf0 := floor_bounds ((4*s-1)*AA) (2*UU) (by omega)
  have hf : 2*UU*(v-1) ≤ (4*s-1)*AA ∧ (4*s-1)*AA < 2*UU*v := by
    simpa [v] using hf0
  have hlo : (4*s-1)*AA+1 ≤ 2*UU*v := by omega
  have hhi : 2*UU*v < (4*s-1)*AA+1+2*UU := by nlinarith only [hf.1]
  have hAU : 1+2*UU < AA := by omega
  have hp : AA*(BB-2*s) > BB*(1+2*UU) := by
    have hmul := mul_pos (show 0 < AA-6*BB by omega) (show 0 < BB-2*s by omega)
    have htail := mul_pos hB (show 0 < 2*BB-12*s+1 by omega)
    rw [hU]
    nlinarith only [hmul,htail]
  have hvB : v*BB < s*AA := by
    have hhi' := hhi
    rw [hU] at hhi'
    have hh := mul_lt_mul_of_pos_right hhi' hB
    have hp' := hp
    rw [hU] at hp'
    apply (mul_lt_mul_iff_of_pos_left (show 0 < 2*UU by omega)).mp
    rw [hU]
    nlinarith only [hh,hp']
  have hvU : v*UU < 2*s*AA := by nlinarith only [hhi,hAU]
  have he : 2*(2*s*AA-v*UU) ≤ AA-1 := by nlinarith only [hlo]
  have hvstock : v < s*m := by
    have hh := mul_lt_mul_of_pos_left hmB (show 0 < s by omega)
    apply (mul_lt_mul_iff_of_pos_right hB).mp
    nlinarith only [hvB,hh]
  refine ⟨v,hv1,hvstock,?_⟩
  apply afterW_windows s y z s v hs hy (by dsimp [z,x]; nlinarith [mul_nonneg (m-2) (s*y)])
    le_rfl (by omega) (by change 0 < s*AA-v*BB; omega) he
  · change 2*v*UU > 2*L x z+2
    change 2*L x z+1 < (4*s-1)*AA at hfirst
    nlinarith only [hfirst,hlo]
  · change 0 ≤ SW x y z-2*AA+(2*s*AA-v*UU)
    change 0 < SW x y z-2*AA at hsecond
    nlinarith only [hsecond,hvU]

private theorem large_third_joint (a b c : ℕ) (hb : 2 ≤ b) (hba : b < a)
    (hac : a+3 ≤ c) : Joint a b c := by
  let s : ℤ := 2^(a-b)
  let y : ℤ := 2^b
  let m : ℤ := 2^(c-a)
  have hs : 2 ≤ s := by simpa [s] using pow_lower (a-b) 1 (by omega)
  have hy : 4 ≤ y := by simpa [y] using pow_lower b 2 hb
  have hm : 8 ≤ m := by simpa [m] using pow_lower (c-a) 3 (by omega)
  have hx : (2:ℤ)^a=s*y := pow_split a b (by omega)
  have hz : (2:ℤ)^c=m*(s*y) := by rw [pow_split c a (by omega),hx]; rfl
  obtain ⟨v,hv,hvm,hw⟩ := large_selector s y m hs hy hm
  let rn := 2^(a-b)
  let vn := v.toNat
  have er : (rn:ℤ)=s := by simp [rn,s]
  have ev : (vn:ℤ)=v := Int.toNat_of_nonneg (by omega)
  have hrcap : rn ≤ 2^(a-1) := by
    dsimp [rn]
    exact pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) (by omega)
  have hhalf : (2:ℤ)^c=2*2^(c-1) := by
    conv_lhs => rw [show c=(c-1)+1 by omega,pow_succ]
    ring
  have hsm : 2*s*m ≤ (2:ℤ)^c := by
    rw [hz]
    have hsm0 : 0 ≤ s*m := by positivity
    nlinarith only [mul_nonneg (show 0 ≤ y-2 by omega) hsm0]
  have hvcap : vn ≤ 2^(c-1) := by
    have : (vn:ℤ) ≤ (2:ℤ)^(c-1) := by rw [ev]; nlinarith only [hvm,hsm,hhalf]
    exact_mod_cast this
  apply afterW_realize a b c rn vn (by omega) hb (by omega)
    (by dsimp [rn]; have := Nat.two_pow_pos (a-b); omega) hrcap
    (by exact_mod_cast (show (1:ℤ) ≤ vn by omega)) hvcap
  simpa only [hx,hz,er,ev] using hw

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
