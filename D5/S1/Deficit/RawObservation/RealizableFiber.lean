/- GID: D5/S1/Deficit/RawObservation/RealizableFiber
   generality: G
   mirror-B: none(waiver:new-formal-source)
   mirror-E: none(waiver:universal-algebraic-proof)
   anchors: []
   utility: none
   digest: The actual golden image of nonnegative raw Fibonacci digits is an exact
     integral cone, with a constructive classification of every displayed-value fiber. -/

import D5.S1.Deficit.DoubleFaceLength

set_option autoImplicit false

namespace D5.S1.Deficit.RawObservation

open D5.S0.Carrier D5.S1.Digit D5.S1.Deficit.DoubleFaceLength

/- Existing beta-add/single helpers in DeficitInteger are private. These two local
calculations expose no new mathematical claim; the image theorem below needs them. -/
private theorem eval_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i c d => ?_)
  · simp
  · push_cast
    ring

private theorem eval_single (i c : Nat) :
    betaDigits (Finsupp.single i c) = (c : GoldenInt) * phi ^ (i + 2) := by
  classical
  rw [betaDigits, Finsupp.sum_single_index (by simp)]

private theorem power_cone (i : Nat) :
    0 ≤ (phi ^ (i + 2)).a ∧
      (phi ^ (i + 2)).a ≤ (phi ^ (i + 2)).b ∧
      (phi ^ (i + 2)).b ≤ 2 * (phi ^ (i + 2)).a := by
  induction i with
  | zero => norm_num [phi, pow_succ]
  | succ i ih =>
      rw [show i + 1 + 2 = (i + 2) + 1 by omega, pow_succ]
      simp only [a_mul, b_mul, phi_a, phi_b, mul_zero, mul_one, zero_add, add_zero]
      omega

/-- Positivity and the two sharp walls of the actual raw-digit image. -/
theorem beta_raw_cone (r : RawDigits) :
    0 ≤ (betaDigits r).a ∧ (betaDigits r).a ≤ (betaDigits r).b ∧
      (betaDigits r).b ≤ 2 * (betaDigits r).a := by
  classical
  induction r using Finsupp.induction with
  | zero => simp [betaDigits]
  | single_add i c r _ _ ih =>
      rw [eval_add, eval_single]
      simp only [a_add, b_add, a_mul, b_mul, a_natCast, b_natCast, zero_mul, zero_add]
      have hc : (0 : Int) ≤ c := by omega
      rcases power_cone i with ⟨hp0, hp1, hp2⟩
      have h0 := mul_nonneg hc hp0
      have h1 := mul_le_mul_of_nonneg_left hp1 hc
      have h2 := mul_le_mul_of_nonneg_left hp2 hc
      constructor
      · omega
      constructor <;> nlinarith [ih.2.1, ih.2.2]

/-- A constructive representative using the first two existing raw-digit slots. -/
def bottom (u v : Nat) : RawDigits := Finsupp.single 0 u + Finsupp.single 1 v

/-- This is an equality with the actual betaDigits evaluator, not an assigned label. -/
theorem beta_bottom (u v : Nat) :
    betaDigits (bottom u v) =
      (⟨(u : Int) + v, (u : Int) + 2 * v⟩ : GoldenInt) := by
  rw [bottom, eval_add, eval_single, eval_single]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ] <;> ring

/-- Complete image classification, with both directions and no free hidden coordinate. -/
theorem raw_image_iff (z : GoldenInt) :
    (∃ r : RawDigits, betaDigits r = z) ↔
      0 ≤ z.a ∧ z.a ≤ z.b ∧ z.b ≤ 2 * z.a := by
  constructor
  · rintro ⟨r, rfl⟩
    exact beta_raw_cone r
  · rintro ⟨_, hab, hba⟩
    have hu : 0 ≤ 2 * z.a - z.b := by omega
    have hv : 0 ≤ z.b - z.a := by omega
    refine ⟨bottom (2 * z.a - z.b).toNat (z.b - z.a).toNat, ?_⟩
    rw [beta_bottom, Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hv]
    apply GoldenInt.ext <;> simp only <;> ring

/-- For a displayed natural n, the possible first coordinates are exactly
ceil(n/2) through n, expressed without rounding or division conventions. -/
theorem display_fiber_iff (n : Nat) (a : Int) :
    (∃ r : RawDigits, rawValue r = n ∧ (betaDigits r).a = a) ↔
      a ≤ (n : Int) ∧ (n : Int) ≤ 2 * a := by
  constructor
  · rintro ⟨r, hn, ha⟩
    have hc := beta_raw_cone r
    rw [betaDigits_b, hn, ha] at hc
    exact hc.2
  · intro h
    have ha0 : 0 ≤ a := by omega
    obtain ⟨r, hr⟩ := (raw_image_iff (⟨a, (n : Int)⟩ : GoldenInt)).mpr
      ⟨ha0, h.1, h.2⟩
    refine ⟨r, ?_, congrArg GoldenInt.a hr⟩
    have hb := congrArg GoldenInt.b hr
    rw [betaDigits_b] at hb
    exact_mod_cast hb

/-- Every raw state has an explicit two-slot representative with the same golden
semantics. This is not asserted to preserve the entire raw state or carry choices. -/
theorem two_slot_representation (r : RawDigits) :
    betaDigits
      (bottom (2 * (betaDigits r).a - (betaDigits r).b).toNat
        ((betaDigits r).b - (betaDigits r).a).toNat) = betaDigits r := by
  have h := beta_raw_cone r
  have hu : 0 ≤ 2 * (betaDigits r).a - (betaDigits r).b := by omega
  have hv : 0 ≤ (betaDigits r).b - (betaDigits r).a := by omega
  rw [beta_bottom, Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hv]
  apply GoldenInt.ext <;> simp only <;> ring

/-- The first two slot multiplicities are unique at the golden-semantic level. -/
theorem bottom_semantics_injective :
    Function.Injective (fun uv : Nat × Nat => betaDigits (bottom uv.1 uv.2)) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have ha := congrArg GoldenInt.a h
  have hb := congrArg GoldenInt.b h
  simp only [beta_bottom] at ha hb
  have hu : u = u' := by omega
  have hv : v = v' := by omega
  exact Prod.ext hu hv

#print axioms raw_image_iff
#print axioms display_fiber_iff
#print axioms two_slot_representation

end D5.S1.Deficit.RawObservation
