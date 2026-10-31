/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Source
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/AscendingD2/Source
   mirror-E: none(waiver:private-consumed-source-table)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact four-chain centered sources for strict ascending gaps and a first ear. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeBitSource
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! Four exact physical ladders, with no period or coprimality assumption. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
open SourceWidth PeriodicShortening RunFirstEarTransport
open private centered_ladder from D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem pow_ge_four (n : ℕ) (hn : 2 ≤ n) : (4 : ℤ) ≤ 2 ^ n := by
  simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hn

private theorem seed_bounds (p q r s : ℤ) (hp : 4 ≤ p) (hq : 4 ≤ q)
    (hr : 4 ≤ r) (hs : 4 ≤ s) :
    1 ≤ 1 + p + p*q + p*q*r ∧ 1 + p + p*q + p*q*r < p*q*r*s-1 := by
  have hpq : 0 < p*q := by positivity
  have hpqr : 0 < p*q*r := by positivity
  have h1 : 1+p+p*q < 2*(p*q) := by nlinarith
  have h2 : 4*(p*q) ≤ p*q*r := by nlinarith
  have h3 : 4*(p*q*r) ≤ p*q*r*s := by nlinarith
  constructor <;> nlinarith

private theorem shifted (N X Y : ℤ) (e i : ℕ)
    (hrel : (2 : ℤ)^e * X = N+Y) :
    centered N ((2 : ℤ)^(e+i)*X) = centered N ((2 : ℤ)^i*Y) := by
  apply centered_congr
  rw [pow_add]
  rw [show (2 : ℤ)^e * 2^i * X = 2^i * (2^e*X) by ring, hrel]
  rw [mul_add, add_comm, Int.add_mul_emod_self_right]

/-- The four consecutive physical ladders, with their terminal negative representatives. -/
private theorem chains (a b c d : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : 2 ≤ c) (hd : 2 ≤ d) :
    let R : ℤ := 2^a
    let T : ℤ := 2^b
    let Z : ℤ := 2^c
    let H : ℤ := 2^d
    let N := modulus (a+b+c+d)
    let A := 1+R+R*T+R*T*Z
    let B := 1+H+H*R+H*R*T
    let W := 1+Z+Z*H+Z*H*R
    let X := 1+T+T*Z+T*Z*H
    let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
    (1 ≤ A ∧ A < N) ∧
    (∀ i < d, f i = if i+1<d then (2 : ℤ)^i*A else -(N-B)/2) ∧
    (∀ i < c, f (d+i) = if i+1<c then (2 : ℤ)^i*B else -(N-W)/2) ∧
    (∀ i < b, f (d+c+i) = if i+1<b then (2 : ℤ)^i*W else -(N-X)/2) ∧
    (∀ i < a, f (d+c+b+i) = if i+1<a then (2 : ℤ)^i*X else -(N-A)/2) := by
  dsimp only
  let R : ℤ := 2^a
  let T : ℤ := 2^b
  let Z : ℤ := 2^c
  let H : ℤ := 2^d
  let N := modulus (a+b+c+d)
  let A := 1+R+R*T+R*T*Z
  let B := 1+H+H*R+H*R*T
  let W := 1+Z+Z*H+Z*H*R
  let X := 1+T+T*Z+T*Z*H
  have hN : N = R*T*Z*H-1 := by dsimp [N, modulus, R,T,Z,H]; simp only [pow_add] <;> ring
  have hR := pow_ge_four a ha
  have hT := pow_ge_four b hb
  have hZ := pow_ge_four c hc
  have hH := pow_ge_four d hd
  change 4 ≤ R at hR
  change 4 ≤ T at hT
  change 4 ≤ Z at hZ
  change 4 ≤ H at hH
  have hA : 1 ≤ A ∧ A < N := by simpa only [A,hN] using seed_bounds R T Z H hR hT hZ hH
  have hB : 1 ≤ B ∧ B < N := by
    have h := seed_bounds H R T Z hH hR hT hZ
    simpa only [B,hN, mul_comm, mul_left_comm, mul_assoc] using h
  have hW : 1 ≤ W ∧ W < N := by
    have h := seed_bounds Z H R T hZ hH hR hT
    simpa only [W,hN, mul_comm, mul_left_comm, mul_assoc] using h
  have hX : 1 ≤ X ∧ X < N := by
    have h := seed_bounds T Z H R hT hZ hH hR
    simpa only [X,hN, mul_comm, mul_left_comm, mul_assoc] using h
  have hpos : 0 < N := by omega
  have hodd : N % 2 = 1 := by
    have hh : H = 2*(2 : ℤ)^(d-1) := by
      dsimp [H]
      conv_lhs => rw [show d = (d-1)+1 by omega, pow_succ]
      ring
    have he : N = 2 * (R*T*Z*(2 : ℤ)^(d-1)-1)+1 := by rw [hN, hh]; ring
    rw [he]
    omega
  have hAB : (2 : ℤ)^d*A=N+B := by change H*A=N+B; rw [hN]; dsimp [A,B]; ring
  have hBW : (2 : ℤ)^c*B=N+W := by change Z*B=N+W; rw [hN]; dsimp [B,W]; ring
  have hWX : (2 : ℤ)^b*W=N+X := by change T*W=N+X; rw [hN]; dsimp [W,X]; ring
  have hXA : (2 : ℤ)^a*X=N+A := by change R*X=N+A; rw [hN]; dsimp [X,A]; ring
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact centered_ladder N A B d i hpos hodd (by omega) ⟨hB.1,hB.2.le⟩ hi hAB
  · intro i hi
    rw [shifted N A B d i hAB]
    exact centered_ladder N B W c i hpos hodd (by omega) ⟨hW.1,hW.2.le⟩ hi hBW
  · intro i hi
    rw [show d+c+i=d+(c+i) by omega, shifted N A B d (c+i) hAB,
      shifted N B W c i hBW]
    exact centered_ladder N W X b i hpos hodd (by omega) ⟨hX.1,hX.2.le⟩ hi hWX
  · intro i hi
    rw [show d+c+b+i=d+(c+(b+i)) by omega, shifted N A B d (c+(b+i)) hAB,
      shifted N B W c (b+i) hBW, shifted N W X b i hWX]
    exact centered_ladder N X A a i hpos hodd (by omega) ⟨hA.1,hA.2.le⟩ hi hXA

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
