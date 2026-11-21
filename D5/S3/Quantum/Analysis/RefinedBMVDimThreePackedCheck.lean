/- GID: D5/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate.criterion_nonneg_ordered; instance=D5/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck.mask_check_five
   digest: Exact integer coefficient checks for the three-dimensional refined BMV bounds. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeInteger

/-! # Packed coefficient signs for the dimension-three refined BMV bounds -/

namespace RefinedBMV.DimThree.PackedCheck

def packDigits (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + base * packDigits base ds

def packSigned (base : Int) : List Int → Int
  | [] => 0
  | d :: ds => d + base * packSigned base ds

private theorem midpoint_lt_base (w : Nat) : 2 ^ w < 2 ^ (w + 1) := by
  rw [Nat.pow_succ]
  have := Nat.pow_pos (by decide : 0 < 2) (n := w)
  omega

theorem digit_signs_of_mask (w : Nat) (coefficients : List Int)
    (hbound : ∀ c ∈ coefficients, -((2 ^ w : Nat) : Int) ≤ c ∧ c < ((2 ^ w : Nat) : Int))
    (hcheck :
      packDigits (2 ^ (w + 1)) (coefficients.map (fun c => (c + ↑(2 ^ w : Nat)).toNat)) &&&
        packDigits (2 ^ (w + 1)) (List.replicate coefficients.length (2 ^ w)) =
          packDigits (2 ^ (w + 1)) (List.replicate coefficients.length (2 ^ w))) :
    ∀ c ∈ coefficients, 0 ≤ c := by
  induction coefficients with
  | nil => simp
  | cons c cs ih =>
    have hc := hbound c (by simp)
    have hnonneg : 0 ≤ c + ↑(2 ^ w : Nat) := by omega
    have hcast := Int.toNat_of_nonneg hnonneg
    have hlt : (c + ↑(2 ^ w : Nat)).toNat < 2 ^ (w + 1) := by
      rw [Nat.pow_succ]
      omega
    have hm := midpoint_lt_base w
    have hbase := Nat.pow_pos (by decide : 0 < 2) (n := w + 1)
    have hhead := congrArg (fun k : Nat => k % 2 ^ (w + 1)) hcheck
    simp only [List.map_cons, List.length_cons, List.replicate_succ, packDigits,
      Nat.and_mod_two_pow, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt hm] at hhead
    have hge : 2 ^ w ≤ (c + ↑(2 ^ w : Nat)).toNat := by
      calc
        2 ^ w = (c + ↑(2 ^ w : Nat)).toNat &&& 2 ^ w := hhead.symm
        _ ≤ _ := Nat.and_le_left
    have htail := congrArg (fun k : Nat => k / 2 ^ (w + 1)) hcheck
    simp only [List.map_cons, List.length_cons, List.replicate_succ, packDigits,
      Nat.and_div_two_pow, Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt hlt,
      Nat.div_eq_of_lt hm, Nat.zero_add] at htail
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · omega
    · exact ih (fun x hx => hbound x (by simp [hx])) htail v hv

theorem packDigits_shift (base mid : Nat) (cs : List Int)
    (hbound : ∀ c ∈ cs, -↑mid ≤ c) :
    (↑(packDigits base (cs.map (fun c => (c + ↑mid).toNat))) : Int) =
      packSigned base cs + ↑(packDigits base (List.replicate cs.length mid)) := by
  induction cs with
  | nil => simp [packDigits, packSigned]
  | cons c cs ih =>
    have hc := hbound c (by simp)
    have hnonneg : 0 ≤ c + ↑mid := by omega
    simp only [List.map_cons, List.length_cons, List.replicate_succ, packDigits,
      packSigned, Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg hnonneg]
    rw [ih (fun x hx => hbound x (by simp [hx])), Int.mul_add]
    omega

def centeredMask (w d : Nat) : Nat :=
  2 ^ w * ((2 ^ (w + 1)) ^ (d * (d + 1) + 1) - 1) / (2 ^ (w + 1) - 1)

def centeredCriterion (p w : Nat) : Int :=
  let d := 12 * p
  let b : Nat := 2 ^ (w + 1)
  criterion p (1 : Int) (1 + ↑b) (1 + ↑b + ↑(b ^ (d + 1))) + ↑(centeredMask w d)

def maskCheck (p w : Nat) : Bool :=
  let m := centeredMask w (12 * p)
  ((centeredCriterion p w).toNat &&& m) == m

set_option maxHeartbeats 0 in
theorem mask_check_five : maskCheck 5 128 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem mask_check_six : maskCheck 6 160 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem mask_check_seven : maskCheck 7 168 = true := by
  decide +kernel

#print axioms mask_check_five
#print axioms mask_check_six
#print axioms mask_check_seven

end RefinedBMV.DimThree.PackedCheck
