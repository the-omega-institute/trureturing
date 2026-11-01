/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Charts
   generality: I
   mirror-B: none(waiver:private-consumed-exhaustive-coordinates)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Eight exhaustive natural-gap charts, including both new boundary equalities. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.HighAdjacent
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.HighSeparated
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.HighBLowA
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowBAdjacent
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowBSeparated
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowAFirst
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowAMiddle
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowALast
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private epsilon cutDelta domain_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
open private nativeAllocation gate
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams
open private actualPowers chartPowers chartMasks chartEpsilon chartDelta
  pow_monomial native_coordinates
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Dyadic
open private high_a_adjacent_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.HighAdjacent
open private high_a_separated_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.HighSeparated
open private high_b_low_a_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.HighBLowA
open private low_b_adjacent_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowBAdjacent
open private low_b_separated_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowBSeparated
open private a_eq_s_plus1_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowAFirst
open private a_between_s_plus2_and_2s_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowAMiddle
open private a_eq_2s_plus1_gates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowALast

private theorem high_a_adjacent_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : 3*s≤a) (hb : b=a+1) :
    let u : ℤ := 2^(s-2)
    let v : ℤ := 2^(a-3*s)
    let w : ℤ := 2^(0)
    actualPowers a b s=chartPowers 0 u v w ∧
    nativeAllocation a b s=chartMasks 0 u v w := by
  let u : ℤ := 2^(s-2)
  let v : ℤ := 2^(a-3*s)
  let w : ℤ := 2^(0)
  have hp : actualPowers a b s=chartPowers 0 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=64*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (a) 6 (s-2) (a-3*s) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=128*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (b) 7 (s-2) (a-3*s) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=4*u
      dsimp only [u,v,w]
      convert pow_monomial (s) 2 (s-2) (a-3*s) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=2*u
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 1 (s-2) (a-3*s) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=32*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 5 (s-2) (a-3*s) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=16*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 4 (s-2) (a-3*s) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=8*u*v
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 3 (s-2) (a-3*s) (0) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=8*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (a-s-1) 3 (s-2) (a-3*s) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=64*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 6 (s-2) (a-3*s) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=32*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 5 (s-2) (a-3*s) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=1
      convert pow_monomial (b-a-1) 0 (s-2) (a-3*s) (0) 0 0 0
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 0 u v w := by
    simp [epsilon,chartEpsilon,hb]
  have hd : (cutDelta b s:ℤ)=chartDelta 0 := by
    have hbhigh : 3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hbhigh]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    0 u v w hp he hd⟩

private theorem high_a_separated_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : 3*s≤a) (hb : a+2≤b) :
    let u : ℤ := 2^(s-2)
    let v : ℤ := 2^(a-3*s)
    let w : ℤ := 2^(b-a-2)
    actualPowers a b s=chartPowers 1 u v w ∧
    nativeAllocation a b s=chartMasks 1 u v w := by
  let u : ℤ := 2^(s-2)
  let v : ℤ := 2^(a-3*s)
  let w : ℤ := 2^(b-a-2)
  have hp : actualPowers a b s=chartPowers 1 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=64*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (a) 6 (s-2) (a-3*s) (b-a-2) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=256*u^3*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b) 8 (s-2) (a-3*s) (b-a-2) 3 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=4*u
      dsimp only [u,v,w]
      convert pow_monomial (s) 2 (s-2) (a-3*s) (b-a-2) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=2*u
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 1 (s-2) (a-3*s) (b-a-2) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=64*u^2*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 6 (s-2) (a-3*s) (b-a-2) 2 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=32*u^2*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 5 (s-2) (a-3*s) (b-a-2) 2 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=16*u*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 4 (s-2) (a-3*s) (b-a-2) 1 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=8*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (a-s-1) 3 (s-2) (a-3*s) (b-a-2) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=128*u^3*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 7 (s-2) (a-3*s) (b-a-2) 3 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=32*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 5 (s-2) (a-3*s) (b-a-2) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-a-1) 1 (s-2) (a-3*s) (b-a-2) 0 0 1
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 1 u v w := by
    have hne : b≠a+1 := by omega
    simp only [epsilon,if_neg hne,Nat.cast_pow,Nat.cast_ofNat]
    change (2:ℤ)^(b-a-2)=w
    dsimp only [u,v,w]
  have hd : (cutDelta b s:ℤ)=chartDelta 1 := by
    have hbhigh : 3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hbhigh]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    1 u v w hp he hd⟩

private theorem high_b_low_a_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : 2*s+2≤a) (hal : a<3*s) (hb : 3*s+1≤b) :
    let u : ℤ := 2^(a-2*s-2)
    let v : ℤ := 2^(3*s-a-1)
    let w : ℤ := 2^(b-3*s-1)
    actualPowers a b s=chartPowers 2 u v w ∧
    nativeAllocation a b s=chartMasks 2 u v w := by
  let u : ℤ := 2^(a-2*s-2)
  let v : ℤ := 2^(3*s-a-1)
  let w : ℤ := 2^(b-3*s-1)
  have hp : actualPowers a b s=chartPowers 2 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=256*u^3*v^2
      dsimp only [u,v,w]
      convert pow_monomial (a) 8 (a-2*s-2) (3*s-a-1) (b-3*s-1) 3 2 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=1024*u^3*v^3*w
      dsimp only [u,v,w]
      convert pow_monomial (b) 10 (a-2*s-2) (3*s-a-1) (b-3*s-1) 3 3 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=8*u*v
      dsimp only [u,v,w]
      convert pow_monomial (s) 3 (a-2*s-2) (3*s-a-1) (b-3*s-1) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=4*u*v
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 2 (a-2*s-2) (3*s-a-1) (b-3*s-1) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=128*u^2*v^2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 7 (a-2*s-2) (3*s-a-1) (b-3*s-1) 2 2 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=64*u^2*v^2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 6 (a-2*s-2) (3*s-a-1) (b-3*s-1) 2 2 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=16*u*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 4 (a-2*s-2) (3*s-a-1) (b-3*s-1) 1 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=16*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (a-s-1) 4 (a-2*s-2) (3*s-a-1) (b-3*s-1) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=512*u^3*v^3*w
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 9 (a-2*s-2) (3*s-a-1) (b-3*s-1) 3 3 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=128*u^3*v^2
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 7 (a-2*s-2) (3*s-a-1) (b-3*s-1) 3 2 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=2*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b-a-1) 1 (a-2*s-2) (3*s-a-1) (b-3*s-1) 0 1 1
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 2 u v w := by
    have hne : b≠a+1 := by omega
    simp only [epsilon,if_neg hne,Nat.cast_pow,Nat.cast_ofNat]
    change (2:ℤ)^(b-a-2)=v*w
    dsimp only [u,v,w]
    convert pow_monomial (b-a-2) 0 (a-2*s-2) (3*s-a-1) (b-3*s-1) 0 1 1
      (by omega) using 1 <;> norm_num <;> ring
  have hd : (cutDelta b s:ℤ)=chartDelta 2 := by
    have hbhigh : 3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hbhigh]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    2 u v w hp he hd⟩

private theorem low_b_adjacent_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : 2*s+2≤a) (hb : b≤3*s) (hadj : b=a+1) :
    let u : ℤ := 2^(a-2*s-2)
    let v : ℤ := 2^(3*s-b)
    let w : ℤ := 2^(0)
    actualPowers a b s=chartPowers 3 u v w ∧
    nativeAllocation a b s=chartMasks 3 u v w := by
  let u : ℤ := 2^(a-2*s-2)
  let v : ℤ := 2^(3*s-b)
  let w : ℤ := 2^(0)
  have hp : actualPowers a b s=chartPowers 3 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=256*u^3*v^2
      dsimp only [u,v,w]
      convert pow_monomial (a) 8 (a-2*s-2) (3*s-b) (0) 3 2 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=512*u^3*v^2
      dsimp only [u,v,w]
      convert pow_monomial (b) 9 (a-2*s-2) (3*s-b) (0) 3 2 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=8*u*v
      dsimp only [u,v,w]
      convert pow_monomial (s) 3 (a-2*s-2) (3*s-b) (0) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=4*u*v
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 2 (a-2*s-2) (3*s-b) (0) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=64*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 6 (a-2*s-2) (3*s-b) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=32*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 5 (a-2*s-2) (3*s-b) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=8*u
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 3 (a-2*s-2) (3*s-b) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=16*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (a-s-1) 4 (a-2*s-2) (3*s-b) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=256*u^3*v^2
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 8 (a-2*s-2) (3*s-b) (0) 3 2 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=128*u^3*v^2
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 7 (a-2*s-2) (3*s-b) (0) 3 2 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=1
      convert pow_monomial (b-a-1) 0 (a-2*s-2) (3*s-b) (0) 0 0 0
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 3 u v w := by
    simp [epsilon,chartEpsilon,hadj]
  have hd : (cutDelta b s:ℤ)=chartDelta 3 := by
    have hblow : ¬3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hblow]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    3 u v w hp he hd⟩

private theorem low_b_separated_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : 2*s+2≤a) (hb : b≤3*s) (hsep : a+2≤b) :
    let u : ℤ := 2^(a-2*s-2)
    let v : ℤ := 2^(b-a-2)
    let w : ℤ := 2^(3*s-b)
    actualPowers a b s=chartPowers 4 u v w ∧
    nativeAllocation a b s=chartMasks 4 u v w := by
  let u : ℤ := 2^(a-2*s-2)
  let v : ℤ := 2^(b-a-2)
  let w : ℤ := 2^(3*s-b)
  have hp : actualPowers a b s=chartPowers 4 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=1024*u^3*v^2*w^2
      dsimp only [u,v,w]
      convert pow_monomial (a) 10 (a-2*s-2) (b-a-2) (3*s-b) 3 2 2
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=4096*u^3*v^3*w^2
      dsimp only [u,v,w]
      convert pow_monomial (b) 12 (a-2*s-2) (b-a-2) (3*s-b) 3 3 2
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=16*u*v*w
      dsimp only [u,v,w]
      convert pow_monomial (s) 4 (a-2*s-2) (b-a-2) (3*s-b) 1 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=8*u*v*w
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 3 (a-2*s-2) (b-a-2) (3*s-b) 1 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=256*u^2*v^2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 8 (a-2*s-2) (b-a-2) (3*s-b) 2 2 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=128*u^2*v^2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 7 (a-2*s-2) (b-a-2) (3*s-b) 2 2 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=16*u*v
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 4 (a-2*s-2) (b-a-2) (3*s-b) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=32*u^2*v*w
      dsimp only [u,v,w]
      convert pow_monomial (a-s-1) 5 (a-2*s-2) (b-a-2) (3*s-b) 2 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=2048*u^3*v^3*w^2
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 11 (a-2*s-2) (b-a-2) (3*s-b) 3 3 2
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=512*u^3*v^2*w^2
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 9 (a-2*s-2) (b-a-2) (3*s-b) 3 2 2
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-a-1) 1 (a-2*s-2) (b-a-2) (3*s-b) 0 1 0
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 4 u v w := by
    have hne : b≠a+1 := by omega
    simp only [epsilon,if_neg hne,Nat.cast_pow,Nat.cast_ofNat]
    change (2:ℤ)^(b-a-2)=v
    dsimp only [u,v,w]
  have hd : (cutDelta b s:ℤ)=chartDelta 4 := by
    have hblow : ¬3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hblow]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    4 u v w hp he hd⟩

private theorem a_eq_s_plus1_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : a=s+1) (hb : 3*s+1≤b) :
    let u : ℤ := 2^(s-2)
    let v : ℤ := 2^(b-3*s-1)
    let w : ℤ := 2^(0)
    actualPowers a b s=chartPowers 5 u v w ∧
    nativeAllocation a b s=chartMasks 5 u v w := by
  let u : ℤ := 2^(s-2)
  let v : ℤ := 2^(b-3*s-1)
  let w : ℤ := 2^(0)
  have hp : actualPowers a b s=chartPowers 5 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=8*u
      dsimp only [u,v,w]
      convert pow_monomial (a) 3 (s-2) (b-3*s-1) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=128*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (b) 7 (s-2) (b-3*s-1) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=4*u
      dsimp only [u,v,w]
      convert pow_monomial (s) 2 (s-2) (b-3*s-1) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=2*u
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 1 (s-2) (b-3*s-1) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=32*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 5 (s-2) (b-3*s-1) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=16*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 4 (s-2) (b-3*s-1) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=8*u*v
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 3 (s-2) (b-3*s-1) (0) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=1
      convert pow_monomial (a-s-1) 0 (s-2) (b-3*s-1) (0) 0 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=64*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 6 (s-2) (b-3*s-1) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=4*u
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 2 (s-2) (b-3*s-1) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=8*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-a-1) 3 (s-2) (b-3*s-1) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 5 u v w := by
    have hne : b≠a+1 := by omega
    simp only [epsilon,if_neg hne,Nat.cast_pow,Nat.cast_ofNat]
    change (2:ℤ)^(b-a-2)=4*u^2*v
    dsimp only [u,v,w]
    convert pow_monomial (b-a-2) 2 (s-2) (b-3*s-1) (0) 2 1 0
      (by omega) using 1 <;> norm_num <;> ring
  have hd : (cutDelta b s:ℤ)=chartDelta 5 := by
    have hbhigh : 3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hbhigh]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    5 u v w hp he hd⟩

private theorem a_between_s_plus2_and_2s_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : s+2≤a) (hal : a≤2*s) (hb : 3*s+1≤b) :
    let u : ℤ := 2^(a-s-2)
    let v : ℤ := 2^(2*s-a)
    let w : ℤ := 2^(b-3*s-1)
    actualPowers a b s=chartPowers 6 u v w ∧
    nativeAllocation a b s=chartMasks 6 u v w := by
  let u : ℤ := 2^(a-s-2)
  let v : ℤ := 2^(2*s-a)
  let w : ℤ := 2^(b-3*s-1)
  have hp : actualPowers a b s=chartPowers 6 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=16*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (a) 4 (a-s-2) (2*s-a) (b-3*s-1) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=128*u^3*v^3*w
      dsimp only [u,v,w]
      convert pow_monomial (b) 7 (a-s-2) (2*s-a) (b-3*s-1) 3 3 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=4*u*v
      dsimp only [u,v,w]
      convert pow_monomial (s) 2 (a-s-2) (2*s-a) (b-3*s-1) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=2*u*v
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 1 (a-s-2) (2*s-a) (b-3*s-1) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=32*u^2*v^2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 5 (a-s-2) (2*s-a) (b-3*s-1) 2 2 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=16*u^2*v^2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 4 (a-s-2) (2*s-a) (b-3*s-1) 2 2 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=8*u*v*w
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 3 (a-s-2) (2*s-a) (b-3*s-1) 1 1 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=2*u
      dsimp only [u,v,w]
      convert pow_monomial (a-s-1) 1 (a-s-2) (2*s-a) (b-3*s-1) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=64*u^3*v^3*w
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 6 (a-s-2) (2*s-a) (b-3*s-1) 3 3 1
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=8*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 3 (a-s-2) (2*s-a) (b-3*s-1) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=4*u*v^2*w
      dsimp only [u,v,w]
      convert pow_monomial (b-a-1) 2 (a-s-2) (2*s-a) (b-3*s-1) 1 2 1
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 6 u v w := by
    have hne : b≠a+1 := by omega
    simp only [epsilon,if_neg hne,Nat.cast_pow,Nat.cast_ofNat]
    change (2:ℤ)^(b-a-2)=2*u*v^2*w
    dsimp only [u,v,w]
    convert pow_monomial (b-a-2) 1 (a-s-2) (2*s-a) (b-3*s-1) 1 2 1
      (by omega) using 1 <;> norm_num <;> ring
  have hd : (cutDelta b s:ℤ)=chartDelta 6 := by
    have hbhigh : 3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hbhigh]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    6 u v w hp he hd⟩

private theorem a_eq_2s_plus1_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : a=2*s+1) (hb : 3*s+1≤b) :
    let u : ℤ := 2^(s-2)
    let v : ℤ := 2^(b-3*s-1)
    let w : ℤ := 2^(0)
    actualPowers a b s=chartPowers 7 u v w ∧
    nativeAllocation a b s=chartMasks 7 u v w := by
  let u : ℤ := 2^(s-2)
  let v : ℤ := 2^(b-3*s-1)
  let w : ℤ := 2^(0)
  have hp : actualPowers a b s=chartPowers 7 u v w := by
    funext r
    fin_cases r
    · change (2:ℤ)^(a)=32*u^2
      dsimp only [u,v,w]
      convert pow_monomial (a) 5 (s-2) (b-3*s-1) (0) 2 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b)=128*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (b) 7 (s-2) (b-3*s-1) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s)=4*u
      dsimp only [u,v,w]
      convert pow_monomial (s) 2 (s-2) (b-3*s-1) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(s-1)=2*u
      dsimp only [u,v,w]
      convert pow_monomial (s-1) 1 (s-2) (b-3*s-1) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s)=32*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s) 5 (s-2) (b-3*s-1) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-s-1)=16*u^2*v
      dsimp only [u,v,w]
      convert pow_monomial (b-s-1) 4 (s-2) (b-3*s-1) (0) 2 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-2*s)=8*u*v
      dsimp only [u,v,w]
      convert pow_monomial (b-2*s) 3 (s-2) (b-3*s-1) (0) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-s-1)=4*u
      dsimp only [u,v,w]
      convert pow_monomial (a-s-1) 2 (s-2) (b-3*s-1) (0) 1 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-1)=64*u^3*v
      dsimp only [u,v,w]
      convert pow_monomial (b-1) 6 (s-2) (b-3*s-1) (0) 3 1 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(a-1)=16*u^2
      dsimp only [u,v,w]
      convert pow_monomial (a-1) 4 (s-2) (b-3*s-1) (0) 2 0 0
        (by omega) using 1 <;> norm_num <;> ring
    · change (2:ℤ)^(b-a-1)=2*u*v
      dsimp only [u,v,w]
      convert pow_monomial (b-a-1) 1 (s-2) (b-3*s-1) (0) 1 1 0
        (by omega) using 1 <;> norm_num <;> ring
  have he : (epsilon a b:ℤ)=chartEpsilon 7 u v w := by
    have hne : b≠a+1 := by omega
    simp only [epsilon,if_neg hne,Nat.cast_pow,Nat.cast_ofNat]
    change (2:ℤ)^(b-a-2)=u*v
    dsimp only [u,v,w]
    convert pow_monomial (b-a-2) 0 (s-2) (b-3*s-1) (0) 1 1 0
      (by omega) using 1 <;> norm_num <;> ring
  have hd : (cutDelta b s:ℤ)=chartDelta 7 := by
    have hbhigh : 3*s+1≤b := by omega
    simp [cutDelta,chartDelta,hbhigh]
  exact ⟨hp,native_coordinates a b s hs (by omega) (by omega) (by omega)
    7 u v w hp he hd⟩

private theorem all_gates (a b s : ℕ) (hs : 2≤s)
    (hcone : (2*s+2≤a ∧ a+1≤b) ∨ (s+1≤a ∧ max (a+1) (3*s+1)≤b)) :
    ∀ (r : Fin 3) (slot : Fin 4),
      0≤gate (2^a) (2^b) (2^s) (nativeAllocation a b s) r slot := by
  have bd := domain_bounds a b s hs hcone
  have pos (e : ℕ) : (1:ℤ)≤2^e := one_le_pow₀ (by norm_num)
  have useChart (chart : Fin 8) (u v w : ℤ)
      (hc : actualPowers a b s=chartPowers chart u v w ∧
        nativeAllocation a b s=chartMasks chart u v w)
      (hg : ∀ r slot, 0≤gate (chartPowers chart u v w 0)
        (chartPowers chart u v w 1) (chartPowers chart u v w 2)
        (chartMasks chart u v w) r slot) :
      ∀ r slot, 0≤gate (2^a) (2^b) (2^s) (nativeAllocation a b s) r slot := by
    have hx : (2:ℤ)^a=chartPowers chart u v w 0 := congrFun hc.1 0
    have hy : (2:ℤ)^b=chartPowers chart u v w 1 := congrFun hc.1 1
    have hz : (2:ℤ)^s=chartPowers chart u v w 2 := congrFun hc.1 2
    rw [hx,hy,hz,hc.2]
    exact hg
  by_cases ha : 2*s+2≤a
  · by_cases hhigh : 3*s≤a
    · by_cases hadj : b=a+1
      · exact useChart 0 _ _ _ (high_a_adjacent_coordinates a b s hs hhigh hadj)
          (high_a_adjacent_gates _ _ _ (pos _) (pos _) (pos _))
      · exact useChart 1 _ _ _ (high_a_separated_coordinates a b s hs hhigh (by omega))
          (high_a_separated_gates _ _ _ (pos _) (pos _) (pos _))
    · by_cases hbhigh : 3*s+1≤b
      · exact useChart 2 _ _ _ (high_b_low_a_coordinates a b s hs ha (by omega) hbhigh)
          (high_b_low_a_gates _ _ _ (pos _) (pos _) (pos _))
      · by_cases hadj : b=a+1
        · exact useChart 3 _ _ _ (low_b_adjacent_coordinates a b s hs ha (by omega) hadj)
            (low_b_adjacent_gates _ _ _ (pos _) (pos _) (pos _))
        · exact useChart 4 _ _ _ (low_b_separated_coordinates a b s hs ha (by omega) (by omega))
            (low_b_separated_gates _ _ _ (pos _) (pos _) (pos _))
  · have hbhigh : 3*s+1≤b := by
      rcases hcone with h|h
      · omega
      · have hm := max_le_iff.mp h.2
        omega
    by_cases hfirst : a=s+1
    · exact useChart 5 _ _ _ (a_eq_s_plus1_coordinates a b s hs hfirst hbhigh)
        (a_eq_s_plus1_gates _ _ _ (pos _) (pos _) (pos _))
    · by_cases hmiddle : a≤2*s
      · exact useChart 6 _ _ _
          (a_between_s_plus2_and_2s_coordinates a b s hs (by omega) hmiddle hbhigh)
          (a_between_s_plus2_and_2s_gates _ _ _ (pos _) (pos _) (pos _))
      · exact useChart 7 _ _ _ (a_eq_2s_plus1_coordinates a b s hs (by omega) hbhigh)
          (a_eq_2s_plus1_gates _ _ _ (pos _) (pos _) (pos _))

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
