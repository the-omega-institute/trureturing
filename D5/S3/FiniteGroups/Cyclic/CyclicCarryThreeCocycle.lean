/- GID: D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree]
   utility: none
   digest: Summation on the cyclic generator detects the parameter of normalized carry three-cocycles modulo coboundaries. -/

import D5.S1.Deficit.Cocycles.AdditiveCarryCocycle
import Mathlib.Data.ZMod.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import OmegaBuild.Commands

/-! The cyclic carry three-cocycle for trivial additive coefficients. -/

compile_only_with_mathlib

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.FiniteGroups.Cyclic.CyclicCarryThreeCocycle

open D5.S1.Deficit.Cocycles.AdditiveCarryCocycle (sectionCarry section_carry_cocycle)

variable {n : ℕ}

/-- The carry of the two least nonnegative representatives. -/
def carry (a b : ZMod n) : ℕ :=
  (a.val + b.val) / n

private def representative (a : ZMod n) : ℤ :=
  a.val

private theorem sectionCarry_eq_mul [NeZero n] (a b : ZMod n) :
    sectionCarry representative a b = (n : ℤ) * (carry a b : ℤ) := by
  have h : n * carry a b + (a + b).val = a.val + b.val := by
    rw [ZMod.val_add]
    exact Nat.div_add_mod _ _
  unfold sectionCarry representative
  apply sub_eq_iff_eq_add.mpr
  simpa only [Nat.cast_add, Nat.cast_mul] using
    congrArg (fun k : ℕ => (k : ℤ)) h.symm

/-- The sum of the two carries is independent of the order of association. -/
theorem carry_cocycle [NeZero n] (a b c : ZMod n) :
    carry a b + carry (a + b) c = carry b c + carry a (b + c) := by
  let q := Int.castAddHom (ZMod n)
  have hsection : Function.RightInverse representative q := by
    intro x
    change ((x.val : ℤ) : ZMod n) = x
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h := congrArg (fun x : q.ker => (x : ℤ))
    (section_carry_cocycle q representative hsection a b c)
  change sectionCarry representative a b + sectionCarry representative (a + b) c =
    sectionCarry representative b c + sectionCarry representative a (b + c) at h
  simp only [sectionCarry_eq_mul, ← mul_add] at h
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  exact_mod_cast (mul_left_cancel₀ hn h)

/-- The explicit cyclic carry representative with parameter `t`. -/
def w (t a b c : ZMod n) : ZMod n :=
  t * a * (carry b c : ZMod n)

/-- The representative vanishes when any of its arguments is the group identity. -/
theorem w_normalized [NeZero n] (t a b : ZMod n) :
    w t 0 a b = 0 ∧ w t a 0 b = 0 ∧ w t a b 0 = 0 := by
  simp [w, carry, Nat.div_eq_of_lt (ZMod.val_lt b)]

/-- The inhomogeneous three-cocycle equation for the trivial action. -/
theorem w_cocycle [NeZero n] (t a b c d : ZMod n) :
    w t b c d - w t (a + b) c d + w t a (b + c) d -
      w t a b (c + d) + w t a b c = 0 := by
  have h : (carry b c : ZMod n) + (carry (b + c) d : ZMod n) =
      (carry c d : ZMod n) + (carry b (c + d) : ZMod n) := by
    simpa only [Nat.cast_add] using
      congrArg (fun k : ℕ => (k : ZMod n)) (carry_cocycle b c d)
  calc
    _ = t * a * ((carry b c : ZMod n) + (carry (b + c) d : ZMod n) -
        ((carry c d : ZMod n) + (carry b (c + d) : ZMod n))) := by
      unfold w
      ring
    _ = 0 := by rw [h, sub_self, mul_zero]

/-- Adding one produces a carry exactly at the last residue. -/
theorem carry_one_right [NeZero n] (hn : 1 < n) (b : ZMod n) :
    carry b 1 = if b.val = n - 1 then 1 else 0 := by
  have hb := ZMod.val_lt b
  rw [carry, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn]
  split
  · rw [show b.val + 1 = n by omega, Nat.div_self (NeZero.pos n)]
  · exact Nat.div_eq_of_lt (by omega)

/-- Summing over the middle argument at the chosen generator recovers `t`. -/
theorem sum_w [NeZero n] (hn : 1 < n) (t : ZMod n) :
    (∑ b : ZMod n, w t 1 b 1) = t := by
  let last : ZMod n := ((n - 1 : ℕ) : ZMod n)
  have hlast : last.val = n - 1 := ZMod.val_natCast_of_lt (by omega)
  calc
    (∑ b : ZMod n, w t 1 b 1) = w t 1 last 1 := by
      refine Finset.sum_eq_single_of_mem last (Finset.mem_univ _) ?_
      intro b _ hb
      have hv : b.val ≠ n - 1 := fun he =>
        hb (ZMod.val_injective n (he.trans hlast.symm))
      simp [w, carry_one_right hn, hv]
    _ = t := by rw [w, carry_one_right hn, ite_eq_left hlast, Nat.cast_one, mul_one, mul_one]

/-- Mathlib's degree-two differential, in additive cyclic coordinates. -/
noncomputable def coboundary {M : Type*} [AddCommGroup M]
    (β : ZMod n → ZMod n → M) (a b c : ZMod n) : M :=
  groupCohomology.d₂₃ (Rep.trivial ℤ (Multiplicative (ZMod n)) M)
    (fun p => β p.1.toAdd p.2.toAdd)
    (Multiplicative.ofAdd a, Multiplicative.ofAdd b, Multiplicative.ofAdd c)

theorem coboundary_apply {M : Type*} [AddCommGroup M]
    (β : ZMod n → ZMod n → M) (a b c : ZMod n) :
    coboundary β a b c = β b c - β (a + b) c + β a (b + c) - β a b := rfl

/-- Translation by the generator makes every coboundary sum vanish. -/
theorem sum_coboundary [NeZero n] {M : Type*} [AddCommGroup M]
    (β : ZMod n → ZMod n → M) :
    (∑ b : ZMod n, coboundary β 1 b 1) = 0 := by
  have shifted (f : ZMod n → M) :
      (∑ b : ZMod n, f (b + 1)) = ∑ b : ZMod n, f b :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) f
  calc
    _ = (∑ b : ZMod n, (β b 1 - β (b + 1) 1)) +
        (∑ b : ZMod n, (β 1 (b + 1) - β 1 b)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [coboundary_apply, add_comm (1 : ZMod n) b]
      abel
    _ = 0 := by
      simp only [Finset.sum_sub_distrib]
      rw [shifted (fun x => β x 1), shifted (fun x => β 1 x)]
      simp only [sub_self, add_zero]

/-- Two cyclic carry representatives differ by a coboundary exactly when their
parameters agree. The two-cochain may be arbitrary. -/
theorem difference_is_coboundary_iff [NeZero n] (hn : 1 < n) (t u : ZMod n) :
    (∃ β : ZMod n → ZMod n → ZMod n,
      ∀ a b c, w t a b c - w u a b c = coboundary β a b c) ↔ t = u := by
  constructor
  · rintro ⟨β, hβ⟩
    have hsum : (∑ b : ZMod n, (w t 1 b 1 - w u 1 b 1)) =
        ∑ b : ZMod n, coboundary β 1 b 1 :=
      Finset.sum_congr rfl (fun b _ => hβ 1 b 1)
    rw [Finset.sum_sub_distrib, sum_w hn t, sum_w hn u, sum_coboundary] at hsum
    exact sub_eq_zero.mp hsum
  · rintro rfl
    exact ⟨fun _ _ => 0, fun a b c => by simp [coboundary_apply]⟩

#print axioms w_normalized
#print axioms w_cocycle

/--
info:
'D5.S3.FiniteGroups.Cyclic.CyclicCarryThreeCocycle.difference_is_coboundary_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms difference_is_coboundary_iff

end D5.S3.FiniteGroups.Cyclic.CyclicCarryThreeCocycle
