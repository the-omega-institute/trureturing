/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:consumed-doubled-margins)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact doubled packet bounds in all four unbounded equal-last-two families. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Source
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic
/-! Exact physical construction and doubled packet checks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
open private heads newHeads delta from D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Source
open private Checks from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic

-- Normalization expands all sixteen seam and peak polynomials.
set_option maxHeartbeats 2400000 in
private theorem large_checks (u v t : ℤ) (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 4 ≤ t) :
    let y := 4*t*v
    let x := 8*t*v*u
    let m := v*u
    let A := heads x y t 0
    let B := heads x y t 1
    let L := heads x y t 2
    let M := heads x y t 3
    let Bn := newHeads x y t 1
    let Ln := newHeads x y t 2
    let Mn := newHeads x y t 3
    let N := x*y*t*t-1
    let Q := 2*N+1
    Checks (N-1) 0
      [((x-14*m)*M, A-N), ((t-2)*A+4*m*M, B-N), ((t-2)*B+(10*m-2*u)*M, L-N), ((y-2)*L+(2*u-2)*M, M-N)] ∧
    Checks (2*N) 0
      [((x-14*m)*Mn+2*A, A-Q), ((t-2)*(2*A)+4*m*Mn, Bn-Q), ((t-2)*Bn+(10*m-2*u)*Mn, Ln-Q), ((y-2)*Ln+(2*u-2)*Mn, Mn-Q)] := by
  obtain ⟨u0, hu0, rfl⟩ : ∃ z : ℤ, 0 ≤ z ∧ u=z+1 := ⟨u-1,by omega,by ring⟩
  obtain ⟨v0, hv0, rfl⟩ : ∃ z : ℤ, 0 ≤ z ∧ v=z+1 := ⟨v-1,by omega,by ring⟩
  obtain ⟨t0, ht0, rfl⟩ : ∃ z : ℤ, 0 ≤ z ∧ t=z+4 := ⟨t-4,by omega,by ring⟩
  dsimp [Checks,heads,newHeads,delta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

-- Normalization expands all sixteen seam and peak polynomials.
set_option maxHeartbeats 2400000 in
private theorem adjacent_checks (m t : ℤ) (hm : 1 ≤ m) (ht : 4 ≤ t) :
    let y := 2*t
    let x := 16*t*m
    let A := heads x y t 0
    let B := heads x y t 1
    let L := heads x y t 2
    let M := heads x y t 3
    let Bn := newHeads x y t 1
    let Ln := newHeads x y t 2
    let Mn := newHeads x y t 3
    let N := x*y*t*t-1
    let Q := 2*N+1
    Checks (N-1) 0
      [((x-30*m)*M, A-N), ((t-2)*A+4*m*M, B-N), ((t-2)*B+16*m*M, L-N), ((2*t-2)*L+(10*m-2)*M, M-N)] ∧
    Checks (2*N) 0
      [((x-30*m)*Mn+2*A, A-Q), ((t-2)*(2*A)+4*m*Mn, Bn-Q), ((t-2)*Bn+16*m*Mn, Ln-Q), ((2*t-2)*Ln+(10*m-2)*Mn, Mn-Q)] := by
  obtain ⟨m0, hm0, rfl⟩ : ∃ z : ℤ, 0 ≤ z ∧ m=z+1 := ⟨m-1,by omega,by ring⟩
  obtain ⟨t0, ht0, rfl⟩ : ∃ z : ℤ, 0 ≤ z ∧ t=z+4 := ⟨t-4,by omega,by ring⟩
  dsimp [Checks,heads,newHeads,delta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

-- Normalization expands all sixteen seam and peak polynomials.
set_option maxHeartbeats 2400000 in
private theorem corner_two_checks (t : ℤ) (ht : 4 ≤ t) :
    let y := 2*t
    let x := 4*t
    let A := heads x y t 0
    let B := heads x y t 1
    let L := heads x y t 2
    let M := heads x y t 3
    let Bn := newHeads x y t 1
    let Ln := newHeads x y t 2
    let Mn := newHeads x y t 3
    let N := x*y*t*t-1
    let Q := 2*N+1
    Checks (N-1) 0
      [((t-2)*A+2*M, B-N), ((t-2)*B+4*M, L-N), ((4*t-8)*M, A-N), ((2*t-2)*L, M-N)] ∧
    Checks (2*N) 0
      [((t-2)*(2*A)+2*Mn, Bn-Q), ((t-2)*Bn+4*Mn, Ln-Q), ((4*t-8)*Mn+2*A, A-Q), ((2*t-2)*Ln, Mn-Q)] := by
  obtain ⟨t0, ht0, rfl⟩ : ∃ z : ℤ, 0 ≤ z ∧ t=z+4 := ⟨t-4,by omega,by ring⟩
  dsimp [Checks,heads,newHeads,delta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

-- Normalization expands all sixteen seam and peak polynomials.
set_option maxHeartbeats 2400000 in
private theorem corner_three_checks (t : ℤ) (ht : 4 ≤ t) :
    let y := 2*t
    let x := 8*t
    let A := heads x y t 0
    let B := heads x y t 1
    let L := heads x y t 2
    let M := heads x y t 3
    let Bn := newHeads x y t 1
    let Ln := newHeads x y t 2
    let Mn := newHeads x y t 3
    let N := x*y*t*t-1
    let Q := 2*N+1
    Checks (N-1) 0
      [((8*t-14)*M, A-N), ((t-2)*B+8*M, L-N), ((t-2)*A+4*M, B-N), ((2*t-2)*L, M-N)] ∧
    Checks (2*N) 0
      [((8*t-14)*Mn+2*A, A-Q), ((t-2)*Bn+8*Mn, Ln-Q), ((t-2)*(2*A)+4*Mn, Bn-Q), ((2*t-2)*Ln, Mn-Q)] := by
  obtain ⟨t0, ht0, rfl⟩ : ∃ z : ℤ, 0 ≤ z ∧ t=z+4 := ⟨t-4,by omega,by ring⟩
  dsimp [Checks,heads,newHeads,delta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
