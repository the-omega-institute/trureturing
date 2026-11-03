/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Unbounded q-two selector with dyadic proper submasks and exact windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Algebra

/-! Modulus-nine selection and dyadic bit inclusion for exact physical windows. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative

/-- A residue selector for an unbounded p,h sector. No window certificate is
    assumed. The modulus nine comes from the exact equation 9v+5j=16p+3. -/
private theorem q_two_residue_first (p h : ℤ) (hp : 8 ≤ p) (hh : 1 ≤ h) :
    let j := (32*p+6)%9
    let v := (16*p+3-5*j)/9
    First p 2 h v (h*j) true := by
  let j := (32*p+6)%9
  let v := (16*p+3-5*j)/9
  have hj0 : 0 ≤ j := Int.emod_nonneg _ (by norm_num)
  have hj8 : j ≤ 8 := by
    have := Int.emod_lt_of_pos (32*p+6) (by norm_num : (0:ℤ)<9)
    dsimp [j]; omega
  have heq : 9*v+5*j=16*p+3 := by dsimp [v,j]; omega
  have hv0 : 1 ≤ v := by omega
  have hv2 : v ≤ 2*p := by omega
  have hA : A p 2 h=5+576*h*p := by
    dsimp [A,SecondPeakHighD.A,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]; ring
  have hR : R p 2 h v (h*j)=5*v-1+h*(48*p+9*j) := by
    dsimp [R,A,L,K,SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.K,
      SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
    linear_combination 64*h*p*heq
  have hN : 4*R p 2 h v (h*j)+2*((y p 2 h-h*j)*Q 2+1)=
      20*v-2+h*(480*p+18*j) := by rw [hR]; dsimp [y,Q]; ring
  have hc0 : 0 ≤ 48*p+9*j := by omega
  have hc1 : 0 ≤ 480*p-18*j := by omega
  have hc2 : 0 ≤ 480*p+18*j := by omega
  have hc3 : 0 ≤ 96*p-18*j := by omega
  have hprod0 := mul_nonneg (show 0≤h by omega) hc0
  have hprod1 := mul_nonneg (show 0≤h-1 by omega) hc1
  have hprod2 := mul_nonneg (show 0≤h by omega) hc2
  have hprod3 := mul_nonneg (show 0≤h-1 by omega) hc3
  change First p 2 h v (h*j) true
  dsimp only [First]
  simp only [ite_true]
  rw [hN,hR,hA]
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [hp,hj0,hj8,hv0,hv2,hprod0,hprod1,hprod2,hprod3]

/-- Exact physical windows for the selector, including K/SW third heads and
    the separate zero seam, throughout the same unbounded sector. -/
private theorem q_two_residue_windows (p h : ℤ) (hp : 8 ≤ p) (hh : 1 ≤ h) :
    let j := (32*p+6)%9
    let v := (16*p+3-5*j)/9
    Windows p 2 h v (h*j) (h*(2*p-1)) true := by
  let j := (32*p+6)%9
  let v := (16*p+3-5*j)/9
  have hf := q_two_residue_first p h hp hh
  change First p 2 h v (h*j) true at hf
  change Windows p 2 h v (h*j) (h*(2*p-1)) true
  intro r
  fin_cases r
  · have he : SecondPeakHighD.oldEnds 4 p 2 h v (h*j) (h*(2*p-1)) 0=
        2*R p 2 h v (h*j) := by dsimp [SecondPeakHighD.oldEnds,R]; ring
    have hn : SecondPeakHighD.newEnds 4 p 2 h v (h*j) (h*(2*p-1)) true 0=
        4*R p 2 h v (h*j)+2*((y p 2 h-h*j)*Q 2+1) := by
      dsimp [SecondPeakHighD.newEnds,R,A,L,K,y,Q,SecondPeakHighD.A,
        SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SV,
        SecondPeakHighD.SW,SecondPeakHighD.Y,SecondPeakHighD.Z,SecondPeakHighD.T]
      ring
    change (0≤SecondPeakHighD.oldEnds 4 p 2 h v (h*j) (h*(2*p-1)) 0 ∧
      SecondPeakHighD.oldEnds 4 p 2 h v (h*j) (h*(2*p-1)) 0≤A p 2 h-1) ∧
      (0≤SecondPeakHighD.newEnds 4 p 2 h v (h*j) (h*(2*p-1)) true 0 ∧
      SecondPeakHighD.newEnds 4 p 2 h v (h*j) (h*(2*p-1)) true 0≤A p 2 h-1)
    rw [he,hn]
    exact ⟨⟨hf.1,hf.2.1⟩,by simpa only [ite_true,sub_zero] using hf.2.2⟩
  all_goals
    constructor <;> constructor
  all_goals
    apply le_of_sub_nonneg
    obtain ⟨a,ha,hpa⟩ : ∃ a : ℤ, 0≤a ∧ p=a+8 := ⟨p-8,by omega,by ring⟩
    obtain ⟨b,hb,hhb⟩ : ∃ b : ℤ, 0≤b ∧ h=b+1 := ⟨h-1,by omega,by ring⟩
    rw [hpa,hhb]
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> positivity

/-- The arithmetic selector returns all stock bounds and physical windows;
    the dyadic bit bridge supplies Submask. -/
private theorem q_two_arithmetic_selection (p h : ℤ) (hp : 8 ≤ p) (hh : 1 ≤ h) :
    ∃ v m M : ℤ,
      9*v+5*((32*p+6)%9)=16*p+3 ∧
      m=h*((32*p+6)%9) ∧ M=h*(2*p-1) ∧
      1≤v ∧ 2*v≤8*p ∧ 0≤m ∧ m<M ∧ 2*M<16*h*p ∧
      Windows p 2 h v m M true := by
  let j := (32*p+6)%9
  let v := (16*p+3-5*j)/9
  have hj0 : 0≤j := Int.emod_nonneg _ (by norm_num)
  have hj8 : j≤8 := by
    have := Int.emod_lt_of_pos (32*p+6) (by norm_num : (0:ℤ)<9)
    dsimp [j]; omega
  have heq : 9*v+5*j=16*p+3 := by dsimp [v,j]; omega
  have hproper := mul_pos (show 0<h by omega) (show 0<2*p-1-j by omega)
  have hstock := mul_pos (show 0<h by omega) (show 0<12*p+2 by omega)
  refine ⟨v,h*j,h*(2*p-1),heq,rfl,rfl,by omega,by omega,
    mul_nonneg (by omega) hj0,by nlinarith only [hproper],
    by nlinarith only [hstock],q_two_residue_windows p h hp hh⟩

private theorem submask_shift (m M H : ℕ) (hs : SecondPeakHighD.Submask m M) :
    SecondPeakHighD.Submask (2^H*m) (2^H*M) := by
  intro e he
  simp only [Nat.testBit_two_pow_mul, Bool.and_eq_true] at he ⊢
  exact ⟨he.1, hs _ he.2⟩

/-- The modulus-nine selector supplies proper dyadic submasks and every exact window. -/
theorem q_two_dyadic_good (P H : ℕ) (hP : 3 ≤ P) :
    ∃ v m M : ℕ, Good (2^P) 2 (2^H) v m M true := by
  let p : ℕ := 2^P
  let h : ℕ := 2^H
  have hp : 8 ≤ p := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hP
  have hh : 1 ≤ h := Nat.one_le_two_pow
  obtain ⟨v,m,M,heq,hm,hM,hv,hv',hm0,hmM,hstock,hw⟩ :=
    q_two_arithmetic_selection p h (by exact_mod_cast hp) (by exact_mod_cast hh)
  let j : ℤ := (32*(p:ℤ)+6)%9
  have hj0 : 0 ≤ j := Int.emod_nonneg _ (by norm_num)
  have hj8 : j ≤ 8 := by
    have := Int.emod_lt_of_pos (32*(p:ℤ)+6) (by norm_num : (0:ℤ)<9)
    dsimp [j]; omega
  have hjlt : j.toNat < 2^(P+1) := by
    rw [pow_succ]
    change j.toNat < p*2
    have hjcast := Int.toNat_of_nonneg hj0
    omega
  have hs := SecondPeakHighD.submask_predecessor (P+1) 1 j.toNat (by omega) hjlt
  simp only [mul_one] at hs
  have hmask : 2^(P+1)-1 = 2*p-1 := by dsimp [p]; rw [pow_succ]; omega
  rw [hmask] at hs
  have hmcast : (m.toNat:ℤ)=m := Int.toNat_of_nonneg hm0
  have hM0 : 0 ≤ M := by omega
  have hMcast : (M.toNat:ℤ)=M := Int.toNat_of_nonneg hM0
  have hvcast : (v.toNat:ℤ)=v := Int.toNat_of_nonneg (by omega)
  have hmn : m.toNat = h*j.toNat := by
    apply Int.natCast_inj.mp
    push_cast
    rw [hmcast,Int.toNat_of_nonneg hj0]
    exact hm
  have hMn : M.toNat = h*(2*p-1) := by
    apply Int.natCast_inj.mp
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2*p)]
    rw [hMcast]
    exact hM
  rw [←hvcast] at hv hv'
  rw [←hmcast,←hMcast] at hmM
  rw [←hMcast] at hstock
  refine ⟨v.toNat,m.toNat,M.toNat,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast hv
  · have hn : 2*v.toNat ≤ 8*p := by exact_mod_cast hv'
    change 2*v.toNat ≤ 4*p*2
    omega
  · exact_mod_cast hmM
  · have hn : 2*M.toNat < 16*h*p := by exact_mod_cast hstock
    change 2*M.toNat < 8*h*p*2
    nlinarith only [hn]
  · rw [hmn,hMn]
    exact submask_shift _ _ H hs
  · simpa only [hvcast,hmcast,hMcast,Nat.cast_ofNat] using hw

/- The late fresh charge admits one affine selector at every scale, including
   h=1 and h=2. This supplements the modulus-nine p>=8 construction. -/
private theorem q_two_boundary_windows (h : ℤ) (hh : 1 ≤ h) :
    Windows 4 2 h 5 (5*h) (8*h-1) false := by
  intro r
  fin_cases r
  all_goals
    constructor <;> constructor
  all_goals
    dsimp [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
      SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads,SecondPeakHighD.A,
      SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,
      SecondPeakHighD.SV,SecondPeakHighD.SW,SecondPeakHighD.Y,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    <;> ring_nf <;> omega

private theorem q_two_boundary_good (H : ℕ) :
    Good 4 2 (2^H) 5 (5*2^H) (8*2^H-1) false := by
  have hh : 1 ≤ (2:ℕ)^H := Nat.one_le_two_pow
  have hpow : (2:ℕ)^(H+3)=8*2^H := by
    rw [pow_add]
    norm_num
    omega
  have hm : 5*2^H < (2:ℕ)^(H+3) := by rw [hpow]; omega
  have hs := SecondPeakHighD.submask_predecessor (H+3) 1 (5*2^H)
    (by omega) hm
  simp only [mul_one,hpow] at hs
  have hcast : ((8*2^H-1:ℕ):ℤ)=8*((2^H:ℕ):ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 8*2^H)]
    push_cast
    rfl
  refine ⟨by norm_num,by norm_num,by omega,by omega,hs,?_⟩
  have hw := q_two_boundary_windows ((2^H:ℕ):ℤ) (by exact_mod_cast hh)
  simpa only [Nat.cast_ofNat,Nat.cast_mul,hcast] using hw


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
