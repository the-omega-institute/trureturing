/- GID: D5/S3/ArithUnits/Thue
   generality: G
   mirror-B: D5/B/S3/ArithUnits/Thue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Thue's lemma gives nonzero representatives bounded by the prime square root. -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace D5.S3.ArithUnits.Thue

/-- Thue's small-representative lemma: every integer not divisible by a
prime is congruent to a ratio of two nonzero integers whose absolute values
are at most the integer square root of the prime. -/
theorem thue_small_representatives
    (p : Nat) (hp : p.Prime) (x : Int) (hpx : ¬ (p : Int) ∣ x) :
    ∃ a b : Int,
      a ≠ 0 ∧
      b ≠ 0 ∧
      a.natAbs ≤ Nat.sqrt p ∧
      b.natAbs ≤ Nat.sqrt p ∧
      Int.ModEq (p : Int) a (x * b) := by
  letI : Fact p.Prime := ⟨hp⟩
  let t := Nat.sqrt p
  let f : Fin (t + 1) × Fin (t + 1) → ZMod p := fun uv =>
    (uv.1.val : ZMod p) - (x : ZMod p) * (uv.2.val : ZMod p)
  have hcard : Fintype.card (ZMod p) <
      Fintype.card (Fin (t + 1) × Fin (t + 1)) := by
    simpa [t, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt p
  obtain ⟨u, v, huv, hcollision⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f hcard
  let a : Int := (u.1.val : Int) - (v.1.val : Int)
  let b : Int := (u.2.val : Int) - (v.2.val : Int)
  have ht_lt_p : t < p := by
    simpa [t] using Nat.sqrt_lt_self hp.one_lt
  have hu1_le : u.1.val ≤ t := by omega
  have hv1_le : v.1.val ≤ t := by omega
  have hu2_le : u.2.val ≤ t := by omega
  have hv2_le : v.2.val ≤ t := by omega
  have hu1_lt_p : u.1.val < p := hu1_le.trans_lt ht_lt_p
  have hv1_lt_p : v.1.val < p := hv1_le.trans_lt ht_lt_p
  have hu2_lt_p : u.2.val < p := hu2_le.trans_lt ht_lt_p
  have hv2_lt_p : v.2.val < p := hv2_le.trans_lt ht_lt_p
  have hx_ne : (x : ZMod p) ≠ 0 := by
    intro hx
    exact hpx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx)
  have ha_ne : a ≠ 0 := by
    intro ha
    have hu1v1 : u.1.val = v.1.val := by
      have : (u.1.val : Int) = (v.1.val : Int) := by
        exact sub_eq_zero.mp (by simpa [a] using ha)
      exact Int.ofNat_inj.mp this
    have hu1 : u.1 = v.1 := Fin.ext hu1v1
    have hmul : (x : ZMod p) * (u.2.val : ZMod p) =
        (x : ZMod p) * (v.2.val : ZMod p) := by
      simpa [f, hu1] using hcollision
    have hu2cast : (u.2.val : ZMod p) = (v.2.val : ZMod p) :=
      mul_left_cancel₀ hx_ne hmul
    have hu2v2 : u.2.val = v.2.val := by
      have := congrArg ZMod.val hu2cast
      simpa [ZMod.val_natCast_of_lt hu2_lt_p,
        ZMod.val_natCast_of_lt hv2_lt_p] using this
    apply huv
    exact Prod.ext hu1 (Fin.ext hu2v2)
  have hb_ne : b ≠ 0 := by
    intro hb
    have hu2v2 : u.2.val = v.2.val := by
      have : (u.2.val : Int) = (v.2.val : Int) := by
        exact sub_eq_zero.mp (by simpa [b] using hb)
      exact Int.ofNat_inj.mp this
    have hu2 : u.2 = v.2 := Fin.ext hu2v2
    have hu1cast : (u.1.val : ZMod p) = (v.1.val : ZMod p) := by
      simpa [f, hu2] using hcollision
    have hu1v1 : u.1.val = v.1.val := by
      have := congrArg ZMod.val hu1cast
      simpa [ZMod.val_natCast_of_lt hu1_lt_p,
        ZMod.val_natCast_of_lt hv1_lt_p] using this
    apply huv
    exact Prod.ext (Fin.ext hu1v1) hu2
  have ha_bound : a.natAbs ≤ t :=
    Int.natAbs_coe_sub_coe_le_of_le hu1_le hv1_le
  have hb_bound : b.natAbs ≤ t :=
    Int.natAbs_coe_sub_coe_le_of_le hu2_le hv2_le
  have hcast : (a : ZMod p) = ((x * b : Int) : ZMod p) := by
    dsimp [f] at hcollision
    simp only [a, b, Int.cast_sub, Int.cast_natCast, Int.cast_mul]
    linear_combination hcollision
  refine ⟨a, b, ha_ne, hb_ne, ?_, ?_, ?_⟩
  · simpa [t] using ha_bound
  · simpa [t] using hb_bound
  · exact (ZMod.intCast_eq_intCast_iff a (x * b) p).mp hcast

end D5.S3.ArithUnits.Thue
