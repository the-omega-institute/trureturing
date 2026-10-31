/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoubleSchedule
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoubleSchedule
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Four complementary physical blocks and their exact old and new strips. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleJointLift

/-! Complementary physical inventory and four-block prefix arithmetic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open SourceWidth PeriodicShortening RunFirstEarTransport
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private chains from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleJointLift

private def Gates (C m1 d1 m2 d2 m3 d3 m4 d4 : ℤ) : Prop :=
  0 ≤ C ∧ 0 ≤ m1+d1 ∧ 0 ≤ m1+d1+m2+d2 ∧ 0 ≤ m1+d1+m2+d2+m3+d3 ∧
  m1+d1+m2+d2+m3+d3+m4+d4 = 0 ∧
  m1 ≤ C ∧ m1+d1+m2 ≤ C ∧ m1+d1+m2+d2+m3 ≤ C ∧
  m1+d1+m2+d2+m3+d3+m4 ≤ C

private theorem block (f : ℕ → ℤ) (C a b : ℤ) (L : List ℕ) (v : ℕ)
    (hp : ∀ i ∈ L, 0 ≤ f i) (ha : 0 ≤ a) (hb : 0 ≤ b ∧ b ≤ C)
    (he : a + (L.map f).sum + f v = b) (hpeak : a + (L.map f).sum ≤ C) :
    InStrip f C a (L++[v]) := by
  apply inStrip_append (positive_block_strip hp ha hpeak)
  have hm : 0 ≤ (L.map f).sum := List.sum_nonneg (by simpa using hp)
  simp only [InStrip]
  exact ⟨by omega,hpeak,by omega,by omega⟩

private theorem four_strip (f : ℕ → ℤ) (C : ℤ) (L1 L2 L3 L4 : List ℕ)
    (v1 v2 v3 v4 : ℕ)
    (hp1 : ∀ i ∈ L1, 0 ≤ f i) (hp2 : ∀ i ∈ L2, 0 ≤ f i)
    (hp3 : ∀ i ∈ L3, 0 ≤ f i) (hp4 : ∀ i ∈ L4, 0 ≤ f i)
    (hg : Gates C (L1.map f).sum (f v1) (L2.map f).sum (f v2)
      (L3.map f).sum (f v3) (L4.map f).sum (f v4)) :
    InStrip f C 0 (L1++[v1]++L2++[v2]++L3++[v3]++L4++[v4]) := by
  obtain ⟨hC,h1,h2,h3,hzero,hp1',hp2',hp3',hp4'⟩ := hg
  have hm2 : 0 ≤ (L2.map f).sum := List.sum_nonneg (by simpa using hp2)
  have hm3 : 0 ≤ (L3.map f).sum := List.sum_nonneg (by simpa using hp3)
  have hm4 : 0 ≤ (L4.map f).sum := List.sum_nonneg (by simpa using hp4)
  have b1 := block f C 0 ((L1.map f).sum+f v1) L1 v1 hp1 (by omega)
    ⟨h1,by omega⟩ (by ring) (by omega)
  have b2 := block f C ((L1.map f).sum+f v1)
    ((L1.map f).sum+f v1+(L2.map f).sum+f v2) L2 v2 hp2 h1
    ⟨h2,by omega⟩ rfl hp2'
  have b3 := block f C ((L1.map f).sum+f v1+(L2.map f).sum+f v2)
    ((L1.map f).sum+f v1+(L2.map f).sum+f v2+(L3.map f).sum+f v3)
    L3 v3 hp3 h2 ⟨h3,by omega⟩ rfl hp3'
  have b4 := block f C ((L1.map f).sum+f v1+(L2.map f).sum+f v2+(L3.map f).sum+f v3)
    0 L4 v4 hp4 h3 ⟨by omega,hC⟩ hzero hp4'
  have h34 := inStrip_append b3 (by simpa only [List.map_append,List.map_singleton,
    List.sum_append,List.sum_singleton,add_assoc] using b4)
  have h234 := inStrip_append b2 (by simpa only [List.map_append,List.map_singleton,
    List.sum_append,List.sum_singleton,add_assoc] using h34)
  have hall := inStrip_append b1 (by simpa only [List.map_append,List.map_singleton,
    List.sum_append,List.sum_singleton,zero_add,add_assoc] using h234)
  simpa only [List.append_assoc] using hall

set_option maxHeartbeats 800000 in
-- Exact coupled old and new peak inequalities expand quartic polynomials.
private theorem arithmetic (q : ℤ) (hq : 2 ≤ q) :
    let z := 2*q
    let N := 4*z^4-1
    let A := 4*z^3+4*z^2+2*z+1
    let B := 4*z^3+2*z^2+z+1
    let L := 2*z^3+z^2+z+1
    let M := 2*z^3+2*z^2+2*z+1
    let GV := 2*B-1
    let GW := 2*L-1-z
    let GX := 2*M-1-2*z-2*z^2
    Gates (N/2) (M+(q-1)*B) (-(N-L)/2) ((z-1)*L) (-(N-M)/2)
      ((q-1)*A) (-(N-B)/2) ((z-2)*M) (-(N-A)/2) ∧
    Gates N (GX+(q-1)*GV) (-((2*N+1)-GW)/2) ((z-1)*GW) (-((2*N+1)-GX)/2)
      ((q-1)*(2*A)+A) (-((2*N+1)-GV)/2) ((z-2)*GX) (-((2*N+1)-A)/2) := by
  dsimp only [Gates]
  have hq2 : 2*q ≤ q^2 := by nlinarith
  have hq3 : 2*q^2 ≤ q^3 := by
    nlinarith [mul_nonneg (show 0 ≤ q-2 by omega) (sq_nonneg q)]
  have hq4 : 2*q^3 ≤ q^4 := by
    nlinarith [mul_nonneg (show 0 ≤ q-2 by omega) (show 0 ≤ q^3 by positivity)]
  ring_nf
  omega

private theorem inventory (n : ℕ) (hn : 2 ≤ n) :
    ([2*n+(n+1)] ++ List.range' n (n-1) ++ [2*n-1] ++
      List.range' (2*n) n ++ [3*n] ++ List.range (n-1) ++ [n-1] ++
      List.range' (3*n+2) (n-1) ++ [4*n+1]).Perm (List.range (2*(n+1)+2*n)) := by
  have hU : List.range (n-1) ++ [n-1] = List.range n := by
    simpa only [Nat.succ_eq_add_one,show n-1+1=n by omega] using (List.range_succ (n:=n-1)).symm
  have hV : List.range' n (n-1) ++ [2*n-1] = List.range' n n := by
    simpa only [show n+(n-1)=2*n-1 by omega,show n-1+1=n by omega] using
      (List.range'_1_concat (s:=n) (n:=n-1)).symm
  have hW : List.range' (2*n) n ++ [3*n] = List.range' (2*n) (n+1) := by
    simpa only [show 2*n+n=3*n by omega] using (List.range'_1_concat (s:=2*n) (n:=n)).symm
  have hX : [2*n+(n+1)] ++ List.range' (3*n+2) (n-1) ++ [4*n+1] =
      List.range' (3*n+1) (n+1) := by
    rw [show 2*n+(n+1)=3*n+1 by omega]
    have h1 : [3*n+1] ++ List.range' (3*n+2) (n-1) = List.range' (3*n+1) n := by
      simpa only [List.range'_one,show 3*n+1+1=3*n+2 by omega,show 1+(n-1)=n by omega] using
        (List.range'_append_1 (s:=3*n+1) (m:=1) (n:=n-1))
    rw [h1]
    simpa only [show 3*n+1+n=4*n+1 by omega] using
      (List.range'_1_concat (s:=3*n+1) (n:=n)).symm
  have he : (List.range (n-1)++[n-1]) ++
      (List.range' n (n-1)++[2*n-1]) ++ (List.range' (2*n) n++[3*n]) ++
      ([2*n+(n+1)]++List.range' (3*n+2) (n-1)++[4*n+1]) =
      List.range (2*(n+1)+2*n) := by
    rw [hU,hV,hW,hX,List.range_eq_range']
    have h1 := List.range'_append_1 (s:=0) (m:=n) (n:=n)
    have h2 := List.range'_append_1 (s:=0) (m:=2*n) (n:=n+1)
    have h3 := List.range'_append_1 (s:=0) (m:=3*n+1) (n:=n+1)
    simp only [Nat.zero_add] at h1 h2 h3
    rw [show n+n=2*n by omega] at h1
    rw [show 2*n+(n+1)=3*n+1 by omega] at h2
    calc
      _ = ((List.range' 0 n ++ List.range' n n) ++ List.range' (2*n) (n+1)) ++
          List.range' (3*n+1) (n+1) := by simp only [List.append_assoc]
      _ = List.range' 0 (3*n+1+(n+1)) := by rw [h1,h2,h3]
      _ = _ := by rw [show 3*n+1+(n+1)=2*(n+1)+2*n by omega,←List.range_eq_range']
  rw [← he]
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add]
  ac_rfl

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
