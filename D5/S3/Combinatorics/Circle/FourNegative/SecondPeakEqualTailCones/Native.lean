/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Native
   generality: I
   mirror-B: none(waiver:private-consumed-native-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Integral native masks, safe subtractions and dyadic quotients. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private mask_complement from D5.S3.Combinatorics.Circle.ThreeBitSource

private def lambda (a b : ℕ) : ℕ := 2^(b-a-1)
private def epsilon (a b : ℕ) : ℕ := if b=a+1 then 0 else 2^(b-a-2)
private def p0 (b s : ℕ) : ℕ := 2^b/(2*2^s)+2^b/(2^s*2^s)
private def p (a b s : ℕ) : ℕ := p0 b s-1-epsilon a b
private def H (b s : ℕ) : ℕ := 2^(b-s)-1
private def F (b : ℕ) : ℕ := 2^(b-1)-1
private def cutDelta (b s : ℕ) : ℕ := if 3*s+1≤b then 1 else 0
private def C (a b s : ℕ) : ℕ := 2^(a-s-1)-cutDelta b s
private def E (a : ℕ) : ℕ := 2^(a-1)-1

private theorem domain_bounds (a b s : ℕ) (hs : 2≤s)
    (hc : (2*s+2≤a ∧ a+1≤b) ∨ (s+1≤a ∧ max (a+1) (3*s+1)≤b)) :
    s+1≤a ∧ a+1≤b ∧ 2*s≤b := by
  rcases hc with h|h
  · omega
  · have hm := max_le_iff.mp h.2
    omega

private theorem dyadic_factor (n d : ℕ) (h : d≤n) :
    (2:ℕ)^n=2^d*2^(n-d) := by rw [←pow_add,Nat.add_sub_of_le h]

private theorem quotient_identities (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) :
    (2^b:ℕ)/(2*2^s)=2^(b-s-1) ∧
    (2^b:ℕ)/(2^s*2^s)=2^(b-2*s) ∧
    (2^b:ℕ)/2^s=2^(b-s) ∧
    (2^a:ℕ)/(2*2^s)=2^(a-s-1) ∧
    (2*2^s:ℕ) ∣ 2^b ∧ (2^s*2^s:ℕ) ∣ 2^b ∧
    (2*2^s:ℕ) ∣ 2^a ∧
    (2^b:ℕ)/2=2^(b-1) ∧ (2^a:ℕ)/2=2^(a-1) ∧
    (2:ℕ) ∣ 2^b ∧ (2:ℕ) ∣ 2^a := by
  have h1 : (2:ℕ)^b=(2*2^s)*2^(b-s-1) := by
    calc
      2^b=2^(s+1)*2^(b-s-1) := by rw [←pow_add]; congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  have h2 : (2:ℕ)^b=(2^s*2^s)*2^(b-2*s) := by
    rw [←pow_add,←pow_add]; congr 1; omega
  have h3 := dyadic_factor b s (by omega)
  have h4 : (2:ℕ)^a=(2*2^s)*2^(a-s-1) := by
    calc
      2^a=2^(s+1)*2^(a-s-1) := by rw [←pow_add]; congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  have h5 : (2:ℕ)^b=2*2^(b-1) := by
    conv_lhs => rw [show b=b-1+1 by omega,pow_succ]
    ring
  have h6 : (2:ℕ)^a=2*2^(a-1) := by
    conv_lhs => rw [show a=a-1+1 by omega,pow_succ]
    ring
  refine ⟨?_,?_,?_,?_,⟨_,h1⟩,⟨_,h2⟩,⟨_,h4⟩,?_,?_,⟨_,h5⟩,⟨_,h6⟩⟩
  · rw [h1,Nat.mul_div_right _ (by positivity)]
  · rw [h2,Nat.mul_div_right _ (by positivity)]
  · rw [h3,Nat.mul_div_right _ (by positivity)]
  · rw [h4,Nat.mul_div_right _ (by positivity)]
  · rw [h5,Nat.mul_div_right _ (by decide)]
  · rw [h6,Nat.mul_div_right _ (by decide)]

private theorem p0_power (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) :
    p0 b s=2^(b-s-1)+2^(b-2*s) := by
  have h := quotient_identities a b s hs ha hb hbs
  dsimp [p0]
  rw [h.1,h.2.1]

private theorem epsilon_half (a b : ℕ) (hb : a+1≤b) :
    (b=a+1 → epsilon a b=0 ∧ lambda a b=1) ∧
    (b≠a+1 → 2*epsilon a b=lambda a b ∧ epsilon a b=lambda a b/2) := by
  constructor
  · intro h; simp [epsilon,lambda,h]
  · intro h
    have he : b-a-1=(b-a-2)+1 := by omega
    have hp : lambda a b=2*epsilon a b := by
      simp only [lambda,epsilon,if_neg h,he,pow_succ]
      ring
    constructor <;> omega

private theorem native_bounds (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) :
    1+epsilon a b≤p0 b s ∧ p a b s≤H b s ∧
    H b s≤F b ∧ C a b s≤E a ∧
    p a b s<2^(b-s) ∧ H b s<2^(b-1) ∧ C a b s<2^(a-1) := by
  have hl : 1≤lambda a b := by exact Nat.one_le_two_pow
  have he : epsilon a b≤lambda a b := by
    by_cases h : b=a+1
    · have hh := (epsilon_half a b hb).1 h
      omega
    · have hh := (epsilon_half a b hb).2 h
      omega
  have hlow : 2*lambda a b≤2^(b-s-1) := by
    have hp := Nat.pow_le_pow_right Nat.zero_lt_two
      (show b-a-1+1≤b-s-1 by omega)
    simpa [pow_add,lambda,Nat.mul_comm] using hp
  have hsmall : (2:ℕ)^(b-2*s)≤2^(b-s-1) :=
    Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have hhalf : (2:ℕ)^(b-s)=2*2^(b-s-1) := by
    conv_lhs => rw [show b-s=(b-s-1)+1 by omega,pow_succ]
    ring
  have hH := Nat.pow_le_pow_right Nat.zero_lt_two (show b-s≤b-1 by omega)
  have hC : 2*2^(a-s-1)≤(2:ℕ)^(a-1) := by
    have hh := Nat.pow_le_pow_right Nat.zero_lt_two
      (show a-s-1+1≤a-1 by omega)
    simpa only [pow_succ, Nat.mul_comm] using hh
  have hcpos := Nat.one_le_two_pow (n:=a-s-1)
  have hpH := Nat.two_pow_pos (b-s)
  have hpF := Nat.two_pow_pos (b-1)
  have hpE := Nat.two_pow_pos (a-1)
  have hp0 := p0_power a b s hs ha hb hbs
  have hsafe : 1+epsilon a b≤p0 b s := by
    rw [hp0]
    omega
  have hpbound : p a b s≤H b s := by
    dsimp only [p,H]
    rw [hp0]
    omega
  have hc : C a b s≤E a := by
    dsimp only [C,E]
    omega
  refine ⟨hsafe,hpbound,?_,hc,?_,?_,?_⟩
  · dsimp only [H,F]
    omega
  · dsimp only [H] at hpbound
    omega
  · dsimp only [H]
    omega
  · dsimp only [E] at hc
    omega

private theorem mask_casts (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) :
    (p a b s:ℤ)=(2:ℤ)^(b-s-1)+2^(b-2*s)-1-(epsilon a b:ℤ) ∧
    (H b s:ℤ)=(2:ℤ)^(b-s)-1 ∧
    (F b:ℤ)=(2:ℤ)^(b-1)-1 ∧
    (C a b s:ℤ)=(2:ℤ)^(a-s-1)-(cutDelta b s:ℤ) ∧
    (E a:ℤ)=(2:ℤ)^(a-1)-1 := by
  have h := native_bounds a b s hs ha hb hbs
  have h0 : 1≤p0 b s := by omega
  have he : epsilon a b≤p0 b s-1 := by omega
  have hp0 := p0_power a b s hs ha hb hbs
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp only [p]
    rw [Nat.cast_sub he,Nat.cast_sub h0,hp0]
    push_cast
    ring
  · simp only [H,Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  · simp only [F,Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  · have hd : cutDelta b s≤2^(a-s-1) := by
      have hδ : cutDelta b s≤1 := by unfold cutDelta; split_ifs <;> omega
      exact hδ.trans Nat.one_le_two_pow
    simp only [C,Nat.cast_sub hd,Nat.cast_pow,Nat.cast_ofNat]
  · simp only [E,Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]

private theorem submask_low (m d e : ℕ) (hm : m<2^d) (hb : m.testBit e=true) : e<d := by
  by_contra h
  have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show d≤e by omega)
  have hz := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm hp)
  rw [hz] at hb
  contradiction

private theorem all_ones_xor (d m : ℕ) (hm : m≤2^d-1) :
    (2^d-1) ^^^ m=(2^d-1)-m := by
  let n := (2^d-1)-m
  have hsum : m+n=2^d-1 := by dsimp [n]; omega
  have parts := mask_complement d m n hsum
  change (2^d-1) ^^^ m=n
  apply Nat.eq_of_testBit_eq
  intro e
  have hu : (m.testBit e=true ∨ n.testBit e=true) ↔ e<d := by
    have hmem : e∈m.bitIndices.toFinset ∪ n.bitIndices.toFinset ↔ e<d := by
      rw [parts.2]
      exact Finset.mem_range
    simpa only [Finset.mem_union,List.mem_toFinset,Nat.mem_bitIndices] using hmem
  have hd : ¬(m.testBit e=true ∧ n.testBit e=true) := by
    rintro ⟨h1,h2⟩
    exact Finset.disjoint_left.mp parts.1
      (by simpa only [List.mem_toFinset,Nat.mem_bitIndices] using h1)
      (by simpa only [List.mem_toFinset,Nat.mem_bitIndices] using h2)
  rw [Nat.testBit_xor]
  cases h1 : m.testBit e <;> cases h2 : n.testBit e <;>
    simp_all [Nat.testBit_two_pow_sub_one]

private theorem xor_casts (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) :
    H b s ^^^ p a b s=H b s-p a b s ∧
    F b ^^^ H b s=F b-H b s ∧ E a ^^^ C a b s=E a-C a b s ∧
    ((H b s ^^^ p a b s:ℕ):ℤ)=(H b s:ℤ)-(p a b s:ℤ) ∧
    ((F b ^^^ H b s:ℕ):ℤ)=(F b:ℤ)-(H b s:ℤ) ∧
    ((E a ^^^ C a b s:ℕ):ℤ)=(E a:ℤ)-(C a b s:ℤ) := by
  have h := native_bounds a b s hs ha hb hbs
  have h1 := all_ones_xor (b-s) (p a b s) h.2.1
  have h2 := all_ones_xor (b-1) (H b s) h.2.2.1
  have h3 := all_ones_xor (a-1) (C a b s) h.2.2.2.1
  change H b s ^^^ p a b s=H b s-p a b s at h1
  change F b ^^^ H b s=F b-H b s at h2
  change E a ^^^ C a b s=E a-C a b s at h3
  refine ⟨h1,h2,h3,?_,?_,?_⟩
  · rw [h1,Nat.cast_sub h.2.1]
  · rw [h2,Nat.cast_sub h.2.2.1]
  · rw [h3,Nat.cast_sub h.2.2.2.1]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
