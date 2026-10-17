/- GID: D5/S3/Arith/Robin/OriginalResidualFiniteTransfer/DyadicPrimitive
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalResidualFiniteTransfer/DyadicPrimitive
   mirror-E: none(waiver:finite-analytic-inequality)
   anchors: []
   utility: none
   digest: The original two periodic primitives have an all-real-coefficient folded range and a joint signed finite variation bound with both jumps. -/

import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive

open D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

/-- The real folded-interval radius; its last branch has no vertex denominator. -/
def radius (d : ℕ) (A B : ℝ) : ℝ :=
  if B ≤ 0 then (d : ℝ)*(A-B)^2/(8*(2*A-B))
  else if B < A then (d : ℝ)*A^2/(8*(2*A-B))
  else (d : ℝ)*B/8

/-- The midpoint of the enclosing interval of the actual primitive combination. -/
def midpoint (d : ℕ) (A B : ℝ) : ℝ :=
  if B ≤ 0 then -(d : ℝ)*(A-B)^2/(8*(2*A-B))
  else if B < A then (d : ℝ)*B/8-(d : ℝ)*(A-B)^2/(8*(2*A-B))
  else (d : ℝ)*B/8

private def foldedResidue (d m : ℕ) : ℕ := min (m % (2*d)) (2*d-m % (2*d))

/-- Both halves use the original remainder primitive, including their common seam. -/
theorem folded_identity {d : ℕ} (hd : 0 < d) (A B : ℝ) (m : ℕ) :
    A*periodicPrimitive d m-B*periodicPrimitive (2*d) m =
      (2*A-B)*(foldedResidue d m : ℝ)^2/(4*d)-
        (A-B)*(foldedResidue d m : ℝ)/2 := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hr : m % (2*d) < 2*d := Nat.mod_lt _ (by omega)
  have hm : m % d = (m % (2*d)) % d :=
    (Nat.mod_mod_of_dvd m (dvd_mul_left d 2)).symm
  by_cases h : m % (2*d) < d
  · have hf : foldedResidue d m = m % (2*d) := by
      unfold foldedResidue
      exact min_eq_left (by omega)
    rw [hf]
    simp only [periodicPrimitive, hm, Nat.mod_eq_of_lt h, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring
  · have hsub : m % (2*d)-d < d := by omega
    have hm' : m % d = m % (2*d)-d := by
      rw [hm, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub]
    have hf : foldedResidue d m = 2*d-m % (2*d) := by
      unfold foldedResidue
      exact min_eq_right (by omega)
    have hc : ((m % (2*d)-d : ℕ) : ℝ) = (m % (2*d) : ℕ)-(d : ℝ) :=
      Nat.cast_sub (by omega)
    have hc' : ((2*d-m % (2*d) : ℕ) : ℝ) = 2*(d : ℝ)-(m % (2*d) : ℕ) := by
      rw [Nat.cast_sub (by omega : m % (2*d) ≤ 2*d)]
      push_cast
      ring
    simp only [periodicPrimitive, hm', hf, hc, hc', Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring

private theorem quadratic_range {d A B s : ℝ} (hd : 0 < d) (hA : 0 < A)
    (hs : 0 ≤ s) (hsd : s ≤ d) :
    let Q := (2*A-B)*s^2/(4*d)-(A-B)*s/2
    if B ≤ 0 then
      -d*(A-B)^2/(4*(2*A-B)) ≤ Q ∧ Q ≤ 0
    else if B < A then
      -d*(A-B)^2/(4*(2*A-B)) ≤ Q ∧ Q ≤ d*B/4
    else 0 ≤ Q ∧ Q ≤ d*B/4 := by
  dsimp only
  by_cases hB : B ≤ 0
  · rw [if_pos hB]
    have hD : 0 < 2*A-B := by linarith
    have hlo : 0 ≤ (2*A-B)*s^2/(4*d)-(A-B)*s/2+
        d*(A-B)^2/(4*(2*A-B)) := by
      have he : (2*A-B)*s^2/(4*d)-(A-B)*s/2+d*(A-B)^2/(4*(2*A-B)) =
          ((2*A-B)*s-d*(A-B))^2/(4*d*(2*A-B)) := by field_simp; ring
      rw [he]
      positivity
    have hchord : (2*A-B)*s^2/(4*d)-(A-B)*s/2-B*s/4 ≤ 0 := by
      have he : (2*A-B)*s^2/(4*d)-(A-B)*s/2-B*s/4 =
          (2*A-B)*s*(s-d)/(4*d) := by field_simp; ring
      rw [he]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (by positivity)
    constructor
    · linarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hB hs]
  · rw [if_neg hB]
    by_cases hBA : B < A
    · rw [if_pos hBA]
      have hD : 0 < 2*A-B := by linarith
      have hlo : 0 ≤ (2*A-B)*s^2/(4*d)-(A-B)*s/2+
          d*(A-B)^2/(4*(2*A-B)) := by
        have he : (2*A-B)*s^2/(4*d)-(A-B)*s/2+d*(A-B)^2/(4*(2*A-B)) =
            ((2*A-B)*s-d*(A-B))^2/(4*d*(2*A-B)) := by field_simp; ring
        rw [he]
        positivity
      have hchord : (2*A-B)*s^2/(4*d)-(A-B)*s/2-B*s/4 ≤ 0 := by
        have he : (2*A-B)*s^2/(4*d)-(A-B)*s/2-B*s/4 =
            (2*A-B)*s*(s-d)/(4*d) := by field_simp; ring
        rw [he]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (by positivity)
      constructor
      · linarith
      · nlinarith [mul_le_mul_of_nonneg_left hsd (by linarith : 0 ≤ B)]
    · rw [if_neg hBA]
      have hB0 : 0 ≤ B := by linarith
      have hBA0 : 0 ≤ B-A := by linarith
      constructor
      · have he : (2*A-B)*s^2/(4*d)-(A-B)*s/2 =
            s*(A*s+(B-A)*(2*d-s))/(4*d) := by field_simp; ring
        rw [he]
        exact div_nonneg (mul_nonneg hs (add_nonneg (mul_nonneg hA.le hs)
          (mul_nonneg hBA0 (by linarith)))) (by positivity)
      · have he : d*B/4-((2*A-B)*s^2/(4*d)-(A-B)*s/2) =
            (d-s)*(2*A*s+B*(d-s))/(4*d) := by field_simp; ring
        have hp : 0 ≤ (d-s)*(2*A*s+B*(d-s))/(4*d) :=
          div_nonneg (mul_nonneg (by linarith) (add_nonneg (by positivity)
            (mul_nonneg hB0 (by linarith)))) (by positivity)
        rw [← he] at hp
        linarith

private theorem interval_midpoint_bound {x lo hi : ℝ} (hl : lo ≤ x) (hu : x ≤ hi) :
    |x-(lo+hi)/2| ≤ (hi-lo)/2 :=
  abs_le.mpr ⟨by linarith, by linarith⟩

/-- An enclosing range of the original primitive for every signed second weight. -/
theorem primitive_range {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    (B : ℝ) (m : ℕ) :
    |A*periodicPrimitive d m-B*periodicPrimitive (2*d) m-midpoint d A B| ≤
      radius d A B := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 ≤ (foldedResidue d m : ℝ) := Nat.cast_nonneg _
  have hsd : (foldedResidue d m : ℝ) ≤ d := by
    exact_mod_cast (show foldedResidue d m ≤ d by
      unfold foldedResidue
      have := Nat.mod_lt m (by omega : 0 < 2*d)
      omega)
  have hb := quadratic_range hd' hA hs hsd
  dsimp only at hb
  rw [← folded_identity hd A B m] at hb
  by_cases hB : B ≤ 0
  · rw [if_pos hB] at hb
    have hm : midpoint d A B = (-(d : ℝ)*(A-B)^2/(4*(2*A-B))+0)/2 := by
      simp only [midpoint, if_pos hB]
      ring
    have hr : radius d A B = (0-(-(d : ℝ)*(A-B)^2/(4*(2*A-B))))/2 := by
      simp only [radius, if_pos hB]
      ring
    rw [hm, hr]
    exact interval_midpoint_bound hb.1 hb.2
  · rw [if_neg hB] at hb
    by_cases hBA : B < A
    · rw [if_pos hBA] at hb
      have hD : 0 < 2*A-B := by linarith
      have hm : midpoint d A B =
          (-(d : ℝ)*(A-B)^2/(4*(2*A-B))+(d : ℝ)*B/4)/2 := by
        simp only [midpoint, if_neg hB, if_pos hBA]
        ring
      have hr : radius d A B =
          ((d : ℝ)*B/4-(-(d : ℝ)*(A-B)^2/(4*(2*A-B))))/2 := by
        simp only [radius, if_neg hB, if_pos hBA]
        field_simp
        <;> ring
      rw [hm, hr]
      exact interval_midpoint_bound hb.1 hb.2
    · rw [if_neg hBA] at hb
      have hm : midpoint d A B = (0+(d : ℝ)*B/4)/2 := by
        simp only [midpoint, if_neg hB, if_neg hBA]
        ring
      have hr : radius d A B = ((d : ℝ)*B/4-0)/2 := by
        simp only [radius, if_neg hB, if_neg hBA]
        ring
      rw [hm, hr]
      exact interval_midpoint_bound hb.1 hb.2

/-- The shared signed telescope cancels the midpoint before taking absolute values. -/
theorem centered_pair_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (b : ℕ → ℝ) {A : ℝ} (hA : 0 < A) (B : ℝ) :
    |∑ m ∈ Ico N (2*N), b m*(A*centered d m-B*centered (2*d) m)| ≤
      radius d A B*variation N b := by
  apply centered_pair_of_primitive_range hN b
    (fun m => A*centered d m-B*centered (2*d) m)
    (fun m => A*periodicPrimitive d m-B*periodicPrimitive (2*d) m)
    (fun m => by
      rw [show A*periodicPrimitive d (m+1)-B*periodicPrimitive (2*d) (m+1)-
          (A*periodicPrimitive d m-B*periodicPrimitive (2*d) m) =
          A*(periodicPrimitive d (m+1)-periodicPrimitive d m)-
            B*(periodicPrimitive (2*d) (m+1)-periodicPrimitive (2*d) m) by ring,
        primitive_step hd, primitive_step (by omega)])
    (-midpoint d A B) (radius d A B)
  intro m
  simpa only [sub_eq_add_neg] using primitive_range hd hA B m

#print axioms folded_identity
#print axioms primitive_range
#print axioms centered_pair_bound

end D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
