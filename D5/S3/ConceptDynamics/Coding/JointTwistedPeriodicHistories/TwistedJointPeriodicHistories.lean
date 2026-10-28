/- GID: D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/TwistedJointPeriodicHistories
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Two twisted returns on one actual expanded history reduce exactly to a signed gcd return, with the noncommutative compatibility obstruction retained. -/

import D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories
import Mathlib.Data.Int.GCD

/-! Joint twisted returns reduce to one signed gcd return on actual histories. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.TwistedJointPeriodicHistories

open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat)
open D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

universe u
variable {H : Type u} [Group H] [Fintype H] {n : ℕ}

local instance : DecidableEq H := Classical.decEq H

/-- Actual histories carrying two twisted return equations at the prescribed
parametrized times `d*a` and `d*b`. -/
def JointTwistedPeriod
    (C : GroupMat H n n) (h g : H) (d a b : ℕ) :=
  {x : History (expandedGraph C) //
    (shift (expandedGraph C))^[d * a] x = groupHistory C h x ∧
    (shift (expandedGraph C))^[d * b] x = groupHistory C g x}

private theorem bezout_one (a b : ℕ) (hab : Nat.Coprime a b) :
    (a : ℤ) * a.gcdA b + (b : ℤ) * a.gcdB b = 1 := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one] at h
  simpa using h.symm

private theorem gcd_time (d a b : ℕ) (hab : Nat.Coprime a b) :
    (a.gcdA b : ℤ) * (d * a : ℤ) +
        (a.gcdB b : ℤ) * (d * b : ℤ) = (d : ℤ) := by
  have h := bezout_one a b hab
  calc
    a.gcdA b * (↑d * ↑a) + a.gcdB b * (↑d * ↑b) =
        ↑d * (↑a * a.gcdA b + ↑b * a.gcdB b) := by ring
    _ = ↑d := by rw [h, mul_one]

private theorem zpow_mul_of_commute (h g : H) (hc : Commute h g)
    (u v q : ℤ) :
    (h ^ u * g ^ v) ^ q = h ^ (u * q) * g ^ (v * q) := by
  rw [(hc.zpow_zpow u v).mul_zpow, zpow_mul, zpow_mul]

/-- A nonempty joint carrier forces both the commutation and power
compatibility required by the gcd reduction. -/
theorem joint_compatibility
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (x : JointTwistedPeriod C h g d a b) :
    Commute h g ∧ h ^ b = g ^ a := by
  let xh : TwistedPeriod C h (d * a) := ⟨x.val, x.property.1⟩
  let xg : TwistedPeriod C g (d * b) := ⟨x.val, x.property.2⟩
  have hh := signed_recovery C h xh (1 : ℤ) 0
  have hg := signed_recovery C g xg (1 : ℤ) 0
  have hga := signed_recovery C g xg (1 : ℤ) (d * a : ℤ)
  have hgb := signed_recovery C h xh (1 : ℤ) (d * b : ℤ)
  have hh' : (x.val.val (d * a : ℤ)).2 = h * (x.val.val 0).2 := by
    simpa [xh, Int.natCast_mul, add_assoc] using congrArg Prod.snd hh
  have hg' : (x.val.val (d * b : ℤ)).2 = g * (x.val.val 0).2 := by
    simpa [xg, Int.natCast_mul, add_assoc] using congrArg Prod.snd hg
  have hga' : (x.val.val ((d : ℤ) * (a : ℤ) + (d : ℤ) * (b : ℤ))).2 =
      g * (x.val.val (d * a : ℤ)).2 := by
    simpa [xg, Int.natCast_mul, add_assoc] using congrArg Prod.snd hga
  have hgb' : (x.val.val ((d : ℤ) * (b : ℤ) + (d : ℤ) * (a : ℤ))).2 =
      h * (x.val.val (d * b : ℤ)).2 := by
    simpa [xh, Int.natCast_mul, add_assoc] using congrArg Prod.snd hgb
  have hcomm_coord : g * (h * (x.val.val 0).2) = h * (g * (x.val.val 0).2) := by
    calc
      g * (h * (x.val.val 0).2) = g * (x.val.val (d * a : ℤ)).2 := by rw [hh']
      _ = (x.val.val ((d : ℤ) * (a : ℤ) + (d : ℤ) * (b : ℤ))).2 := hga'.symm
      _ = (x.val.val ((d : ℤ) * (b : ℤ) + (d : ℤ) * (a : ℤ))).2 := by
        exact congrArg (fun t : ℤ => (x.val.val t).2) (by ring)
      _ = h * (x.val.val (d * b : ℤ)).2 := hgb'
      _ = h * (g * (x.val.val 0).2) := by rw [hg']
  have hcomm : Commute h g := by
    change h * g = g * h
    exact (mul_right_cancel (by simpa [mul_assoc] using hcomm_coord)).symm
  refine ⟨hcomm, ?_⟩
  have hpowb := signed_recovery C h xh (b : ℤ) 0
  have hgpow := signed_recovery C g xg (a : ℤ) 0
  have hpowb' : (x.val.val ((b : ℤ) * ((d : ℤ) * (a : ℤ)))).2 =
      h ^ b * (x.val.val 0).2 := by
    simpa [xh, Int.natCast_mul, add_assoc] using congrArg Prod.snd hpowb
  have hgpow' : (x.val.val ((a : ℤ) * ((d : ℤ) * (b : ℤ)))).2 =
      g ^ a * (x.val.val 0).2 := by
    simpa [xg, Int.natCast_mul, add_assoc] using congrArg Prod.snd hgpow
  have hpow_coord : h ^ b * (x.val.val 0).2 = g ^ a * (x.val.val 0).2 := by
    calc
      h ^ b * (x.val.val 0).2 =
          (x.val.val ((b : ℤ) * ((d : ℤ) * (a : ℤ)))).2 := hpowb'.symm
      _ = (x.val.val ((a : ℤ) * ((d : ℤ) * (b : ℤ)))).2 := by
        exact congrArg (fun t : ℤ => (x.val.val t).2) (by ring)
      _ = g ^ a * (x.val.val 0).2 := hgpow'
  exact mul_right_cancel hpow_coord

/-- A joint return forces commutation of the two deck twists. -/
theorem joint_commute
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (x : JointTwistedPeriod C h g d a b) : Commute h g :=
  (joint_compatibility C h g d a b x).1

/-- A joint return forces the power compatibility relation. -/
theorem joint_power_compat
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (x : JointTwistedPeriod C h g d a b) : h ^ b = g ^ a :=
  (joint_compatibility C h g d a b x).2

private theorem joint_to_gcd_history
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (hab : Nat.Coprime a b) (x : JointTwistedPeriod C h g d a b) :
    let u := a.gcdA b
    let v := a.gcdB b
    let c := h ^ u * g ^ v
    (shift (expandedGraph C))^[d] x.val = groupHistory C c x.val := by
  dsimp
  let xh : TwistedPeriod C h (d * a) := ⟨x.val, x.property.1⟩
  let xg : TwistedPeriod C g (d * b) := ⟨x.val, x.property.2⟩
  let u : ℤ := a.gcdA b
  let v : ℤ := a.gcdB b
  let c : H := h ^ u * g ^ v
  have htime : u * (d * a : ℤ) + v * (d * b : ℤ) = (d : ℤ) := by
    exact gcd_time d a b hab
  have hrec : ∀ t : ℤ,
      x.val.val (t + (d : ℤ)) =
        ((x.val.val t).1, c * (x.val.val t).2) := by
    intro t
    have hshift := signed_recovery C h xh u (t + v * (d * b : ℤ))
    have gshift := signed_recovery C g xg v t
    have gshift' : x.val.val (t + v * (d * b : ℤ)) =
        ((x.val.val t).1, g ^ v * (x.val.val t).2) := by
      simpa [add_assoc] using gshift
    have hshift' :
        (x.val.val (t + v * (d * b : ℤ) + u * (d * a : ℤ))).2 =
          h ^ u * (x.val.val (t + v * (d * b : ℤ))).2 := by
      simpa [xh, Int.natCast_mul] using congrArg Prod.snd hshift
    have hshift'' : (x.val.val (t + v * (d * b : ℤ) + u * (d * a : ℤ))).2 =
        h ^ u * (g ^ v * (x.val.val t).2) := by
      rw [hshift']
      rw [gshift']
    have hadd : t + v * (d * b : ℤ) + u * (d * a : ℤ) = t + (d : ℤ) := by
      calc
        t + v * (d * b : ℤ) + u * (d * a : ℤ) =
            t + (u * (d * a : ℤ) + v * (d * b : ℤ)) := by ring
        _ = t + (d : ℤ) := by rw [htime]
    rw [hadd] at hshift''
    apply Prod.ext
    · have hv := congrArg Prod.fst hshift
      calc
        (x.val.val (t + (d : ℤ))).1 =
            (x.val.val (t + v * (d * b : ℤ))).1 := by simpa [xh, hadd, Int.natCast_mul] using hv
        _ = (x.val.val t).1 := by simpa using congrArg Prod.fst gshift'
    · simpa [c, hshift'', mul_assoc]
  rw [shift_iterate_translate]
  apply Subtype.ext
  funext t
  change x.val.val (t + (d : ℤ)) = ((x.val.val t).1, c * (x.val.val t).2)
  simpa [c] using hrec t

private theorem compatible_powers
    (h g : H) (a b : ℕ) (hc : Commute h g) (hpow : h ^ b = g ^ a)
    (hab : Nat.Coprime a b) :
    let u := a.gcdA b
    let v := a.gcdB b
    let c := h ^ u * g ^ v
    c ^ (a : ℤ) = h ∧ c ^ (b : ℤ) = g := by
  dsimp
  let u : ℤ := a.gcdA b
  let v : ℤ := a.gcdB b
  let c : H := h ^ u * g ^ v
  have habz := bezout_one a b hab
  have hpowz : h ^ (b : ℤ) = g ^ (a : ℤ) := by
    simpa using hpow
  have hca : c ^ (a : ℤ) = h := by
    calc
      c ^ (a : ℤ) = h ^ (u * (a : ℤ)) * g ^ (v * (a : ℤ)) :=
        zpow_mul_of_commute h g hc u v (a : ℤ)
      _ = h ^ (u * (a : ℤ)) * h ^ (v * (b : ℤ)) := by
        have hh := congrArg (fun z : H => z ^ v) hpowz
        have hcross : g ^ (v * (a : ℤ)) = h ^ (v * (b : ℤ)) := by
          calc
            g ^ (v * (a : ℤ)) = g ^ ((a : ℤ) * v) := by rw [mul_comm]
            _ = (g ^ (a : ℤ)) ^ v := zpow_mul g (a : ℤ) v
            _ = (h ^ (b : ℤ)) ^ v := hh.symm
            _ = h ^ ((b : ℤ) * v) := (zpow_mul h (b : ℤ) v).symm
            _ = h ^ (v * (b : ℤ)) := by rw [mul_comm]
        rw [hcross]
      _ = h ^ (u * (a : ℤ) + v * (b : ℤ)) := by rw [zpow_add]
      _ = h := by
        have huv : u * (a : ℤ) + v * (b : ℤ) = 1 := by
          rw [mul_comm u, mul_comm v]
          exact habz
        rw [huv, zpow_one]
  have hcb : c ^ (b : ℤ) = g := by
    calc
      c ^ (b : ℤ) = h ^ (u * (b : ℤ)) * g ^ (v * (b : ℤ)) :=
        zpow_mul_of_commute h g hc u v (b : ℤ)
      _ = g ^ (u * (a : ℤ)) * g ^ (v * (b : ℤ)) := by
        have hh := congrArg (fun z : H => z ^ u) hpowz
        have hcross : h ^ (u * (b : ℤ)) = g ^ (u * (a : ℤ)) := by
          calc
            h ^ (u * (b : ℤ)) = h ^ ((b : ℤ) * u) := by rw [mul_comm]
            _ = (h ^ (b : ℤ)) ^ u := zpow_mul h (b : ℤ) u
            _ = (g ^ (a : ℤ)) ^ u := hh
            _ = g ^ ((a : ℤ) * u) := (zpow_mul g (a : ℤ) u).symm
            _ = g ^ (u * (a : ℤ)) := by rw [mul_comm]
        rw [hcross]
      _ = g ^ (u * (a : ℤ) + v * (b : ℤ)) := by rw [zpow_add]
      _ = g := by
        have huv : u * (a : ℤ) + v * (b : ℤ) = 1 := by
          rw [mul_comm u, mul_comm v]
          exact habz
        rw [huv, zpow_one]
  exact ⟨hca, hcb⟩

/-- Two twisted returns on one actual history force the signed gcd return. -/
theorem joint_to_gcd
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (hab : Nat.Coprime a b) (x : JointTwistedPeriod C h g d a b) :
    (shift (expandedGraph C))^[d] x.val =
      groupHistory C (h ^ (a.gcdA b) * g ^ (a.gcdB b)) x.val := by
  exact joint_to_gcd_history C h g d a b hab x

/-- The two original returns are recovered from a compatible gcd return. -/
def gcd_to_joint
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (hab : Nat.Coprime a b) (hc : Commute h g)
    (hpow : h ^ b = g ^ a) (x : TwistedPeriod C (h ^ (a.gcdA b) * g ^ (a.gcdB b)) d) :
    JointTwistedPeriod C h g d a b := by
  let u : ℤ := a.gcdA b
  let v : ℤ := a.gcdB b
  let c : H := h ^ u * g ^ v
  have hca : c ^ (a : ℤ) = h := by
    simpa [c] using (compatible_powers h g a b hc hpow hab).1
  have hcb : c ^ (b : ℤ) = g := by
    simpa [c] using (compatible_powers h g a b hc hpow hab).2
  refine ⟨x.val, ?_⟩
  constructor
  · rw [shift_iterate_translate]
    apply Subtype.ext
    funext t
    change x.val.val (t + (d * a : ℤ)) = ((x.val.val t).1, h * (x.val.val t).2)
    have hr := signed_recovery C c x (a : ℤ) t
    convert hr using 1 <;> simp [c, hca, Int.natCast_mul] <;> ring
  · rw [shift_iterate_translate]
    apply Subtype.ext
    funext t
    change x.val.val (t + (d * b : ℤ)) = ((x.val.val t).1, g * (x.val.val t).2)
    have hr := signed_recovery C c x (b : ℤ) t
    convert hr using 1 <;> simp [c, hcb, Int.natCast_mul] <;> ring

/-- Under the noncommutative compatibility conditions, the two-return carrier
is exactly the gcd-return carrier, without changing the underlying history. -/
def jointGcdEquiv
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (hab : Nat.Coprime a b) (hc : Commute h g)
    (hpow : h ^ b = g ^ a) :
    JointTwistedPeriod C h g d a b ≃
      TwistedPeriod C (h ^ (a.gcdA b) * g ^ (a.gcdB b)) d where
  toFun x := ⟨x.val, joint_to_gcd C h g d a b hab x⟩
  invFun x := gcd_to_joint C h g d a b hab hc hpow x
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

@[instance_reducible] def jointTwistedPeriodFintype
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (hd : 0 < d)
    (hab : Nat.Coprime a b) (hc : Commute h g)
    (hpow : h ^ b = g ^ a) : Fintype (JointTwistedPeriod C h g d a b) :=
  letI := twistedPeriodFintype C (h ^ (a.gcdA b) * g ^ (a.gcdB b)) hd
  Fintype.ofEquiv _ (jointGcdEquiv C h g d a b hab hc hpow).symm

theorem jointTwistedPeriod_card
    (C : GroupMat H n n) (h g : H) (d a b : ℕ)
    (hd : 0 < d)
    (hab : Nat.Coprime a b) (hc : Commute h g)
    (hpow : h ^ b = g ^ a) :
    @Fintype.card (JointTwistedPeriod C h g d a b)
      (jointTwistedPeriodFintype C h g d a b hd hab hc hpow) =
      ∑ i : Fin n, ∑ z : H,
        ((C^d) i i).coeff
          (z⁻¹ * (h ^ (a.gcdA b) * g ^ (a.gcdB b)) * z) := by
  letI := twistedPeriodFintype C (h ^ (a.gcdA b) * g ^ (a.gcdB b)) hd
  letI := jointTwistedPeriodFintype C h g d a b hd hab hc hpow
  rw [Fintype.card_congr (jointGcdEquiv C h g d a b hab hc hpow)]
  exact twistedPeriod_card C
    (h ^ (a.gcdA b) * g ^ (a.gcdB b)) hd

end D5.S3.ConceptDynamics.Coding.TwistedJointPeriodicHistories
