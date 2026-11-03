/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Arithmetic
   mirror-E: none(waiver:consumed-uniform-margins)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Uniform doubled seam and peak inequalities on the entire upper cone. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Source
/-! Doubled endpoint checks for strict and equal parameters. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
open private heads newHeads delta from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Source

-- Each pair contains a doubled positive mass and its doubled terminal.
private def Checks (cap h : ℤ) : List (ℤ × ℤ) → Prop
  | [] => True
  | (p, n)::bs => 0 ≤ h + p + n ∧ h + p ≤ cap ∧ Checks cap (h + p + n) bs

set_option maxHeartbeats 2000000 in
private theorem strict_checks (h q : ℤ) (hh : 2 ≤ h) (hq : 4 ≤ q) :
    let A := heads (h * q) q 0
    let B := heads (h * q) q 1
    let L := heads (h * q) q 2
    let M := heads (h * q) q 3
    let Bn := newHeads (h * q) q 1
    let Ln := newHeads (h * q) q 2
    let Mn := newHeads (h * q) q 3
    let N := h * q ^ 4 - 1
    let Q := 2 * N + 1
    Checks (N - 1) 0
      [(h * (q - 1) * M, A - N), ((q - 2) * A, B - N), ((q - 2) * B, L - N), 
       ((q - 2) * L + (h - 2) * M, M - N)] ∧
    Checks (2 * N) 0
      [(h * (q - 1) * Mn, A - Q), ((q - 2) * (2 * A), Bn - Q), ((q - 2) * Bn + 2 * A, Ln - Q), 
       ((q - 2) * Ln + (h - 2) * Mn, Mn - Q)] := by
  obtain ⟨u, hu, rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ h = u + 2 := ⟨h - 2, by omega, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℤ, 0 ≤ v ∧ q = v + 4 := ⟨q - 4, by omega, by ring⟩
  dsimp [Checks, heads, newHeads, delta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

set_option maxHeartbeats 2000000 in
private theorem equal_checks (q : ℤ) (hq : 4 ≤ q) :
    let A := heads q q 0
    let B := heads q q 1
    let L := heads q q 2
    let M := heads q q 3
    let Bn := newHeads q q 1
    let Ln := newHeads q q 2
    let Mn := newHeads q q 3
    let N := q ^ 4 - 1
    let Q := 2 * N + 1
    Checks (N - 1) 0
      [((q - 2) * A, B - N), ((q - 2) * B, L - N), ((q - 2) * L, M - N), ((q - 2) * M, A - N)] ∧
    Checks (2 * N) 0
      [((q - 2) * (2 * A) + 2 * A, Bn - Q), ((q - 2) * Bn, Ln - Q), ((q - 2) * Ln, Mn - Q), 
       ((q - 2) * Mn, A - Q)] := by
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℤ, 0 ≤ v ∧ q = v + 4 := ⟨q - 4, by omega, by ring⟩
  dsimp [Checks, heads, newHeads, delta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity
end D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
