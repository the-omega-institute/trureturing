/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Choices
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/AscendingD2/Choices
   mirror-E: none(waiver:private-consumed-explicit-masks)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Explicit disjoint dyadic masks for each unbounded ascending chamber. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Arithmetic
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterFirstEarJointLift

/-! Every mask is an actual finite physical support, with no supplied choice premise. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
open private Mask shiftedSupport shifted_disjoint from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private Coeff margins large_margins small_margins tail_margins from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Arithmetic
open private complementary_bits high_bit_disjoint from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterFirstEarJointLift

private def coeff (a b c : ℕ) (m : Mask a b c) : Coeff :=
  (m.1.val,m.2.1.val,m.2.2.val)
private def intMask (a b c : ℕ) (v w x : ℤ)
    (hv : 0≤v ∧ v<(2 : ℤ)^(c-1)) (hw : 0≤w ∧ w<(2 : ℤ)^(b-1))
    (hx : 0≤x ∧ x<(2 : ℤ)^(a-1)) : Mask a b c :=
  (⟨v.toNat,by exact_mod_cast (show (v.toNat : ℤ)<(2 : ℤ)^(c-1) by simpa only [Int.toNat_of_nonneg hv.1] using hv.2)⟩,
   ⟨w.toNat,by exact_mod_cast (show (w.toNat : ℤ)<(2 : ℤ)^(b-1) by simpa only [Int.toNat_of_nonneg hw.1] using hw.2)⟩,
   ⟨x.toNat,by exact_mod_cast (show (x.toNat : ℤ)<(2 : ℤ)^(a-1) by simpa only [Int.toNat_of_nonneg hx.1] using hx.2)⟩)

private theorem coeff_intMask (a b c : ℕ) (v w x : ℤ)
    (hv : 0≤v ∧ v<(2 : ℤ)^(c-1)) (hw : 0≤w ∧ w<(2 : ℤ)^(b-1))
    (hx : 0≤x ∧ x<(2 : ℤ)^(a-1)) :
    coeff a b c (intMask a b c v w x hv hw hx)=(v,w,x) := by
  simp only [coeff,intMask,Int.toNat_of_nonneg hv.1,Int.toNat_of_nonneg hw.1,Int.toNat_of_nonneg hx.1]

private structure Choice (a b c : ℕ) (R T Z : ℤ) where
  p : Mask a b c
  q : Mask a b c
  r : Mask a b c
  pq : Disjoint (shiftedSupport a b c p) (shiftedSupport a b c q)
  pr : Disjoint (shiftedSupport a b c p) (shiftedSupport a b c r)
  qr : Disjoint (shiftedSupport a b c q) (shiftedSupport a b c r)
  good : margins R T Z (coeff a b c p) (coeff a b c q) (coeff a b c r)

private theorem pow_split (n j : ℕ) (h : j≤n) :
    (2 : ℤ)^n=2^j*2^(n-j) := by rw [←pow_add, Nat.add_sub_of_le h]

set_option maxHeartbeats 1200000 in
private def large_choice (a b c : ℕ) (ha : 4≤a) (hab : a<b) (hbc : b<c) :
    Choice a b c (2^a) (2^b) (2^c) := by
  let r : ℤ := 2^(a-4)
  let s : ℤ := 2^(b-a-1)
  let t : ℤ := 2^(c-b-1)
  have hr : 1≤r := by dsimp [r]; positivity
  have hs : 1≤s := by dsimp [s]; positivity
  have ht : 1≤t := by dsimp [t]; positivity
  have hA : (2 : ℤ)^a=16*r := by dsimp [r]; rw [pow_split a 4 ha]; norm_num
  have hB : (2 : ℤ)^b=32*r*s := by
    rw [pow_split b (a+1) (by omega),pow_succ,hA]
    change 16*r*2*(2 : ℤ)^(b-(a+1))=32*r*s
    rw [show b-(a+1)=b-a-1 by omega]; dsimp [s]; ring
  have hC : (2 : ℤ)^c=64*r*s*t := by
    rw [pow_split c (b+1) (by omega),pow_succ,hB]
    change 32*r*s*2*(2 : ℤ)^(c-(b+1))=64*r*s*t
    rw [show c-(b+1)=c-b-1 by omega]; dsimp [t]; ring
  have halves (n : ℕ) (hn : 1≤n) : 2*(2 : ℤ)^(n-1)=2^n := by
    rw [show n=(n-1)+1 by omega,pow_succ]; ring
  have hAh : (2 : ℤ)^(a-1)=8*r := by have := halves a (by omega); rw [hA] at this; omega
  have hBh : (2 : ℤ)^(b-1)=16*r*s := by have := halves b (by omega); rw [hB] at this; omega
  have hCh : (2 : ℤ)^(c-1)=32*r*s*t := by have := halves c (by omega); rw [hC] at this; omega
  have hrS : 1≤r*s := by nlinarith
  have hrST : 1≤r*s*t := by nlinarith
  have hbV : 0≤(16*r*s+1)*t ∧ (16*r*s+1)*t<(2 : ℤ)^(c-1) := by
    rw [hCh]; constructor <;> nlinarith
  have hbWq : 0≤(8*r+1)*s ∧ (8*r+1)*s<(2 : ℤ)^(b-1) := by
    rw [hBh]; constructor <;> nlinarith
  have hbWr : 0≤(8*r-1)*s-1 ∧ (8*r-1)*s-1<(2 : ℤ)^(b-1) := by
    rw [hBh]; constructor <;> nlinarith
  have hbXp : 0≤5*r ∧ 5*r<(2 : ℤ)^(a-1) := by rw [hAh]; omega
  have hbXq : 0≤3*r-1 ∧ 3*r-1<(2 : ℤ)^(a-1) := by rw [hAh]; omega
  have zero (n : ℕ) : 0≤(0 : ℤ) ∧ 0<(2 : ℤ)^n := ⟨le_rfl,by positivity⟩
  let p := intMask a b c 0 0 (5*r) (zero _) (zero _) hbXp
  let q := intMask a b c 0 ((8*r+1)*s) (3*r-1) (zero _) hbWq hbXq
  let z := intMask a b c ((16*r*s+1)*t) ((8*r-1)*s-1) 0 hbV hbWr (zero _)
  have hX := complementary_bits (a-1) (8*r) (5*r) (3*r-1) hAh.symm hbXp.1 hbXq.1 (by ring)
  have hW := complementary_bits (b-1) (16*r*s) ((8*r+1)*s) ((8*r-1)*s-1)
    hBh.symm hbWq.1 hbWr.1 (by ring)
  refine ⟨p,q,z,?_,?_,?_,?_⟩
  · apply shifted_disjoint
    · simp [p,q,intMask]
    · simp [p,q,intMask]
    · exact hX
  · apply shifted_disjoint <;> simp [p,z,intMask]
  · apply shifted_disjoint
    · simp [q,z,intMask]
    · exact hW
    · simp [q,z,intMask]
  · dsimp [p,q,z]
    rw [coeff_intMask,coeff_intMask,coeff_intMask,hA,hB,hC]
    exact large_margins r s t hr hs ht

set_option maxHeartbeats 1200000 in
private def small_choice (a b c : ℕ) (ha : a=2 ∨ a=3) (hb : 4≤b) (hbc : b<c) :
    Choice a b c (2^a) (2^b) (2^c) := by
  let r : ℤ := 2^(a-2)
  let u : ℤ := 2^(b-4)
  let v : ℤ := 2^(c-b-1)
  have hr : r=1 ∨ r=2 := by rcases ha with rfl|rfl <;> norm_num [r]
  have hu : 1≤u := by dsimp [u]; positivity
  have hv : 1≤v := by dsimp [v]; positivity
  have hA : (2 : ℤ)^a=4*r := by rw [pow_split a 2 (by omega)]; norm_num; rfl
  have hB : (2 : ℤ)^b=16*u := by rw [pow_split b 4 hb]; norm_num; rfl
  have hC : (2 : ℤ)^c=32*u*v := by
    rw [pow_split c (b+1) (by omega),pow_succ,hB]
    rw [show c-(b+1)=c-b-1 by omega]; dsimp [v]; ring
  have hAh : (2 : ℤ)^(a-1)=2*r := by rcases ha with rfl|rfl <;> norm_num [r]
  have hBh : (2 : ℤ)^(b-1)=8*u := by
    rw [pow_split (b-1) 3 (by omega)]; rw [show b-1-3=b-4 by omega]; norm_num; rfl
  have hCh : (2 : ℤ)^(c-1)=16*u*v := by
    have he : 2*(2 : ℤ)^(c-1)=2^c := by rw [show c=(c-1)+1 by omega,pow_succ]; ring
    rw [hC] at he; omega
  have htop : (2 : ℤ)^(b-2)=4*u := by
    rw [pow_split (b-2) 2 (by omega)]; rw [show b-2-2=b-4 by omega]; norm_num; rfl
  have zero (n : ℕ) : 0≤(0 : ℤ) ∧ 0<(2 : ℤ)^n := ⟨le_rfl,by positivity⟩
  have bpw : 0≤u ∧ u<(2 : ℤ)^(b-1) := by rw [hBh]; omega
  have bqw : 0≤4*u ∧ 4*u<(2 : ℤ)^(b-1) := by rw [hBh]; omega
  have brw : 0≤3*u-1 ∧ 3*u-1<(2 : ℤ)^(b-1) := by rw [hBh]; omega
  have bpx : 0≤r ∧ r<(2 : ℤ)^(a-1) := by rw [hAh]; omega
  have bqx : 0≤r-1 ∧ r-1<(2 : ℤ)^(a-1) := by rw [hAh]; omega
  have brv : 0≤(8*u+1)*v ∧ (8*u+1)*v<(2 : ℤ)^(c-1) := by
    rw [hCh]; have : 1≤u*v := by nlinarith; constructor <;> nlinarith
  let p := intMask a b c 0 u r (zero _) bpw bpx
  let q := intMask a b c 0 (4*u) (r-1) (zero _) bqw bqx
  let z := intMask a b c ((8*u+1)*v) (3*u-1) 0 brv brw (zero _)
  have hX := complementary_bits (a-1) (2*r) r (r-1) hAh.symm bpx.1 bqx.1 (by ring)
  have hWpr := complementary_bits (b-2) (4*u) u (3*u-1) htop.symm (by omega) (by omega) (by ring)
  have hWqp := high_bit_disjoint (b-2) (4*u) u htop.symm (by omega) (by omega)
  have hWqr := high_bit_disjoint (b-2) (4*u) (3*u-1) htop.symm (by omega) (by omega)
  refine ⟨p,q,z,?_,?_,?_,?_⟩
  · apply shifted_disjoint
    · simp [p,q,intMask]
    · exact hWqp.symm
    · exact hX
  · apply shifted_disjoint
    · simp [p,z,intMask]
    · exact hWpr
    · simp [p,z,intMask]
  · apply shifted_disjoint
    · simp [q,z,intMask]
    · exact hWqr
    · simp [q,z,intMask]
  · dsimp [p,q,z]
    rw [coeff_intMask,coeff_intMask,coeff_intMask,hA,hB,hC]
    exact small_margins r u v hr hu hv

set_option maxHeartbeats 1200000 in
private def tail_choice (c : ℕ) (hc : 7≤c) : Choice 2 3 c 4 8 (2^c) := by
  let z : ℤ := 2^(c-7)
  have hz : 1≤z := by dsimp [z]; positivity
  have hC : (2 : ℤ)^c=128*z := by rw [pow_split c 7 hc]; norm_num; rfl
  have hCh : (2 : ℤ)^(c-1)=64*z := by
    rw [pow_split (c-1) 6 (by omega),show c-1-6=c-7 by omega]; norm_num; rfl
  have hCp : (2 : ℤ)^(c-4)=8*z := by
    rw [pow_split (c-4) 3 (by omega),show c-4-3=c-7 by omega]; norm_num; rfl
  have hCr : (2 : ℤ)^(c-2)=32*z := by
    rw [pow_split (c-2) 5 (by omega),show c-2-5=c-7 by omega]; norm_num; rfl
  have bpv : 0≤8*z ∧ 8*z<(2 : ℤ)^(c-1) := by rw [hCh]; omega
  have bqv : 0≤z ∧ z<(2 : ℤ)^(c-1) := by rw [hCh]; omega
  have brv : 0≤32*z ∧ 32*z<(2 : ℤ)^(c-1) := by rw [hCh]; omega
  let p := intMask 2 3 c (8*z) 0 1 bpv (by norm_num) (by norm_num)
  let q := intMask 2 3 c z 2 0 bqv (by norm_num) (by norm_num)
  let r := intMask 2 3 c (32*z) 1 0 brv (by norm_num) (by norm_num)
  have hpq := high_bit_disjoint (c-4) (8*z) z hCp.symm (by omega) (by omega)
  have hrp := high_bit_disjoint (c-2) (32*z) (8*z) hCr.symm (by omega) (by omega)
  have hrq := high_bit_disjoint (c-2) (32*z) z hCr.symm (by omega) (by omega)
  refine ⟨p,q,r,?_,?_,?_,?_⟩
  · apply shifted_disjoint
    · exact hpq
    · simp [p,q,intMask]
    · simp [p,q,intMask]
  · apply shifted_disjoint
    · exact hrp.symm
    · simp [p,r,intMask]
    · simp [p,r,intMask]
  · apply shifted_disjoint
    · exact hrq.symm
    · decide
    · simp [q,r,intMask]
  · dsimp [p,q,r]
    rw [coeff_intMask,coeff_intMask,coeff_intMask,hC]
    exact tail_margins z hz

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
