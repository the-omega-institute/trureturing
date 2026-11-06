/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoubleJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoubleJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal four-chain joint order with adjacent gap ratio two. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeBitSource

/-! The adjacent paired-gap branch r=s+1. The other paired-gap branches remain open. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open private centered_ladder positive_block_strip
  from D5.S3.Combinatorics.Circle.ThreeBitSource
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem shift (N u v : ℤ) (len i : ℕ)
    (h : (2 : ℤ)^len * u = N + v) :
    centered N ((2 : ℤ)^(len+i)*u) = centered N ((2 : ℤ)^i*v) := by
  apply centered_congr
  have he : (2 : ℤ)^(len+i)*u = 2^i*v + 2^i*N := by
    calc
      _ = 2^i*(2^len*u) := by rw [pow_add]; ring
      _ = _ := by rw [h]; ring
  rw [he, Int.add_mul_emod_self_right]

set_option maxHeartbeats 800000 in
private theorem chains (n : ℕ) (hn : 2 ≤ n) :
    let z : ℤ := 2^n
    let k := 2*(n+1)+2*n
    let N := modulus k
    let A := 4*z^3+4*z^2+2*z+1
    let B := 4*z^3+2*z^2+z+1
    let L := 2*z^3+z^2+z+1
    let M := 2*z^3+2*z^2+2*z+1
    let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
    let g := fun i : ℕ => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A))
    (∀ i < n, f i = if i+1<n then 2^i*A else -(N-B)/2) ∧
    (∀ i < n, f (n+i) = if i+1<n then 2^i*B else -(N-L)/2) ∧
    (∀ i < n+1, f (2*n+i) = if i+1<n+1 then 2^i*L else -(N-M)/2) ∧
    (∀ i < n+1, f (2*n+(n+1)+i) = if i+1<n+1 then 2^i*M else -(N-A)/2) ∧
    (∀ i < n, g i = if i+1<n then 2^i*(2*A) else -((modulus (k+1))-(2*B-1))/2) ∧
    (∀ i < n, g (n+i) = if i+1<n then 2^i*(2*B-1) else -((modulus (k+1))-(2*L-1-z))/2) ∧
    (∀ i < n+1, g (2*n+i) = if i+1<n+1 then 2^i*(2*L-1-z) else -((modulus (k+1))-(2*M-1-2*z-2*z^2))/2) ∧
    (∀ i < n+1, g (2*n+(n+1)+i) = if i+1<n+1 then 2^i*(2*M-1-2*z-2*z^2) else -((modulus (k+1))-A)/2) ∧
    g k = A := by
  dsimp only
  let z : ℤ := 2^n
  let k := 2*(n+1)+2*n
  let N := modulus k
  let A := 4*z^3+4*z^2+2*z+1
  let B := 4*z^3+2*z^2+z+1
  let L := 2*z^3+z^2+z+1
  let M := 2*z^3+2*z^2+2*z+1
  let NN := modulus (k+1)
  have hz : 4 ≤ z := by simpa [z] using (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hn)
  have hz2 : 4*z ≤ z^2 := by nlinarith
  have hz3 : 4*z^2 ≤ z^3 := by nlinarith [mul_nonneg (show 0 ≤ z-4 by omega) (sq_nonneg z)]
  have hz4 : 4*z^3 ≤ z^4 := by nlinarith [mul_nonneg (show 0 ≤ z-4 by omega) (show 0 ≤ z^3 by positivity)]
  have hN : N = 4*z^4-1 := by
    dsimp [N,k,modulus,z]
    rw [show 2*(n+1)+2*n = n+n+n+n+2 by omega]
    simp only [pow_add]; ring
  have hNN : NN = 2*N+1 := by dsimp [NN,N,modulus]; rw [pow_succ]; ring
  have hbounds : (1 ≤ A ∧ A < N) ∧ (1 ≤ B ∧ B < N) ∧
      (1 ≤ L ∧ L < N) ∧ (1 ≤ M ∧ M < N) := by
    dsimp [A,B,L,M]; rw [hN]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
    all_goals nlinarith only [hz,hz2,hz3,hz4]
  have hpow : (2 : ℤ)^(n+1) = 2*z := by dsimp [z]; rw [pow_succ]; ring
  have hrels : z*A=N+B ∧ z*B=N+L ∧ (2*z)*L=N+M ∧ (2*z)*M=N+A := by
    rw [hN]
    dsimp [A,B,L,M]
    refine ⟨?_,?_,?_,?_⟩ <;> ring
  have hgrels : z*(2*A)=NN+(2*B-1) ∧
      z*(2*B-1)=NN+(2*L-1-z) ∧
      (2*z)*(2*L-1-z)=NN+(2*M-1-2*z-2*z^2) ∧
      (2*z)*(2*M-1-2*z-2*z^2)=NN+A := by
    rw [hNN,hN]
    dsimp [A,B,L,M]
    refine ⟨?_,?_,?_,?_⟩ <;> ring
  have hgbounds : (1 ≤ 2*A ∧ 2*A ≤ NN) ∧ (1 ≤ 2*B-1 ∧ 2*B-1 ≤ NN) ∧
      (1 ≤ 2*L-1-z ∧ 2*L-1-z ≤ NN) ∧
      (1 ≤ 2*M-1-2*z-2*z^2 ∧ 2*M-1-2*z-2*z^2 ≤ NN) := by
    rw [hNN]
    dsimp [A,B,L,M] at *
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
    all_goals nlinarith only [hbounds,hz,hz2,hz3]
  have hNp : 0 < N := by omega
  have hNo : N % 2 = 1 := by
    have hp : (2 : ℤ)^k % 2 = 0 := by
      rw [show k = (k-1)+1 by dsimp [k]; omega, pow_succ]; omega
    dsimp [N,modulus]; omega
  have hNNp : 0 < NN := by omega
  have hNNo : NN % 2 = 1 := by omega
  have fV (i : ℕ) : centered N ((2 : ℤ)^(n+i)*A) = centered N ((2 : ℤ)^i*B) :=
    shift N A B n i hrels.1
  have fW (i : ℕ) : centered N ((2 : ℤ)^(2*n+i)*A) = centered N ((2 : ℤ)^i*L) := by
    rw [show 2*n+i=n+(n+i) by omega, fV]
    exact shift N B L n i hrels.2.1
  have fX (i : ℕ) : centered N ((2 : ℤ)^(2*n+(n+1)+i)*A) = centered N ((2 : ℤ)^i*M) := by
    rw [show 2*n+(n+1)+i=2*n+((n+1)+i) by omega, fW]
    exact shift N L M (n+1) i (by rw [hpow]; exact hrels.2.2.1)
  have gV (i : ℕ) : centered NN ((2 : ℤ)^(n+i)*(2*A)) = centered NN ((2 : ℤ)^i*(2*B-1)) :=
    shift NN (2*A) (2*B-1) n i hgrels.1
  have gW (i : ℕ) : centered NN ((2 : ℤ)^(2*n+i)*(2*A)) = centered NN ((2 : ℤ)^i*(2*L-1-z)) := by
    rw [show 2*n+i=n+(n+i) by omega, gV]
    exact shift NN (2*B-1) (2*L-1-z) n i hgrels.2.1
  have gX (i : ℕ) : centered NN ((2 : ℤ)^(2*n+(n+1)+i)*(2*A)) = centered NN ((2 : ℤ)^i*(2*M-1-2*z-2*z^2)) := by
    rw [show 2*n+(n+1)+i=2*n+((n+1)+i) by omega, gW]
    exact shift NN (2*L-1-z) (2*M-1-2*z-2*z^2) (n+1) i (by rw [hpow]; exact hgrels.2.2.1)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    exact centered_ladder N A B n i hNp hNo (by omega) ⟨hbounds.2.1.1, hbounds.2.1.2.le⟩ hi hrels.1
  · intro i hi; rw [fV]
    exact centered_ladder N B L n i hNp hNo (by omega) ⟨hbounds.2.2.1.1, hbounds.2.2.1.2.le⟩ hi hrels.2.1
  · intro i hi; rw [fW]
    exact centered_ladder N L M (n+1) i hNp hNo (by omega) ⟨hbounds.2.2.2.1, hbounds.2.2.2.2.le⟩ hi (by rw [hpow]; exact hrels.2.2.1)
  · intro i hi; rw [fX]
    exact centered_ladder N M A (n+1) i hNp hNo (by omega) ⟨hbounds.1.1, hbounds.1.2.le⟩ hi (by rw [hpow]; exact hrels.2.2.2)
  · intro i hi
    exact centered_ladder NN (2*A) (2*B-1) n i hNNp hNNo (by omega) hgbounds.2.1 hi hgrels.1
  · intro i hi; rw [gV]
    exact centered_ladder NN (2*B-1) (2*L-1-z) n i hNNp hNNo (by omega) hgbounds.2.2.1 hi hgrels.2.1
  · intro i hi; rw [gW]
    exact centered_ladder NN (2*L-1-z) (2*M-1-2*z-2*z^2) (n+1) i hNNp hNNo (by omega) hgbounds.2.2.2 hi (by rw [hpow]; exact hgrels.2.2.1)
  · intro i hi; rw [gX]
    exact centered_ladder NN (2*M-1-2*z-2*z^2) A (n+1) i hNNp hNNo (by omega) ⟨hbounds.1.1, by omega⟩ hi (by rw [hpow]; exact hgrels.2.2.2)
  · have h : centered NN ((2 : ℤ)^k*(2*A)) = centered NN A := by
      change centered (modulus (k+1)) ((2 : ℤ)^k*(2*A)) = _
      rw [show (2 : ℤ)^k*(2*A) = 2^(k+1)*A by rw [pow_succ]; ring]
      have he : (2 : ℤ)^(k+1)*A = A + A*modulus (k+1) := by dsimp [modulus]; ring
      apply centered_congr
      rw [he, Int.add_mul_emod_self_right]
    rw [h]
    apply centered_unique hNNp hNNo (centered_bounds hNNp hNNo A) ⟨by omega, by omega⟩ (centered_mod NN A)

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleJointLift
