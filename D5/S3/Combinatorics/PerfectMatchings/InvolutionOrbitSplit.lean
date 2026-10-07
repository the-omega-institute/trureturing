/- GID: D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic]
   utility: none
   digest: Perfect matching components split into two product orbits. -/

import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Algebra.Group.Action.End
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

open Equiv

variable {X : Type*} (s t : Perm X)

/-- Connectivity in the graph with the two matching edges at each vertex. -/
def Connected (x y : X) : Prop :=
  Relation.ReflTransGen (fun u v => s u = v ∨ t u = v) x y

/-- The full integer-power orbit, including singleton orbits. -/
def RotationOrbit (r : Perm X) (x : X) : Set X := {y | r.SameCycle x y}

private theorem square_eq_one (h : Function.Involutive s) : s * s = 1 := by
  ext x
  exact h x

private theorem inv_eq_self (h : Function.Involutive s) : s⁻¹ = s :=
  Function.Involutive.symm_eq_self_of_involutive s h

private theorem conjugate_rotation (hs : Function.Involutive s)
    (ht : Function.Involutive t) : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
  rw [mul_inv_rev, inv_eq_self s hs, inv_eq_self t ht]
  simp only [← mul_assoc, square_eq_one s hs, one_mul]

private theorem invert_rotation (hs : Function.Involutive s)
    (ht : Function.Involutive t) (k : ℤ) :
    s * (s * t) ^ k = (s * t) ^ (-k) * s := by
  have h : s * (s * t) ^ k * s⁻¹ = (s * t) ^ (-k) := by
    rw [← conj_zpow, conjugate_rotation s t hs ht, inv_zpow']
  calc
    s * (s * t) ^ k = (s * (s * t) ^ k * s⁻¹) * s := by group
    _ = (s * t) ^ (-k) * s := by rw [h]

private theorem right_as_reflection (hs : Function.Involutive s)
    (ht : Function.Involutive t) : t = (s * t) ^ (-1 : ℤ) * s := by
  simp only [zpow_neg_one, mul_inv_rev, inv_eq_self s hs, inv_eq_self t ht,
    mul_assoc, square_eq_one s hs, mul_one]

private theorem reflection_even (hs : Function.Involutive s)
    (ht : Function.Involutive t) (j : ℤ) :
    (s * t) ^ (2 * j) * s = (s * t) ^ j * s * ((s * t) ^ j)⁻¹ := by
  rw [← zpow_neg, mul_assoc, invert_rotation s t hs ht, neg_neg,
    ← mul_assoc, ← zpow_add]
  congr 2
  omega

private theorem reflection_odd (hs : Function.Involutive s)
    (ht : Function.Involutive t) (j : ℤ) :
    (s * t) ^ (2 * j + 1) * s =
      (s * t) ^ (j + 1) * t * ((s * t) ^ (j + 1))⁻¹ := by
  let r := s * t
  change r ^ (2 * j + 1) * s = r ^ (j + 1) * t * (r ^ (j + 1))⁻¹
  have htr : t = r ^ (-1 : ℤ) * s := right_as_reflection s t hs ht
  rw [htr, ← zpow_neg, ← mul_assoc, ← zpow_add]
  rw [mul_assoc, invert_rotation s t hs ht, neg_neg, ← mul_assoc, ← zpow_add]
  congr 2
  omega

private theorem conjugate_no_fixed (f g : Perm X) (hf : ∀ x, f x ≠ x) :
    ∀ x, (g * f * g⁻¹) x ≠ x := by
  have hfe : MulAction.fixedBy X f = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr hf
  have hge : MulAction.fixedBy X (g * f * g⁻¹) = ∅ := by
    rw [← MulAction.smul_fixedBy X f g, hfe]
    simp
  intro x hx
  have hm : x ∈ MulAction.fixedBy X (g * f * g⁻¹) := hx
  rw [hge] at hm
  exact hm

/-- The generators have no fixed points exactly when every reflection has none. -/
theorem fixedPointFree_iff_reflection_exclusion (hs : Function.Involutive s)
    (ht : Function.Involutive t) :
    ((∀ x, s x ≠ x) ∧ (∀ x, t x ≠ x)) ↔
      ∀ (k : ℤ) (x : X), ((s * t) ^ k * s) x ≠ x := by
  constructor
  · rintro ⟨hsl, htr⟩ k
    by_cases he : k % 2 = 0
    · have hk : k = 2 * (k / 2) := by omega
      rw [hk, reflection_even s t hs ht]
      exact conjugate_no_fixed s ((s * t) ^ (k / 2)) hsl
    · have hk : k = 2 * (k / 2) + 1 := by omega
      rw [hk, reflection_odd s t hs ht]
      exact conjugate_no_fixed t ((s * t) ^ (k / 2 + 1)) htr
  · intro h
    constructor
    · simpa only [zpow_zero, one_mul] using h 0
    · rw [right_as_reflection s t hs ht]
      exact h (-1)

/-- No matching edge can return to the same product orbit, and this property
characterizes fixed-point-freeness of both involutions. -/
theorem fixedPointFree_iff_rotation_separation (hs : Function.Involutive s)
    (ht : Function.Involutive t) :
    ((∀ x, s x ≠ x) ∧ (∀ x, t x ≠ x)) ↔
      ∀ x, ¬ (s * t).SameCycle x (s x) := by
  constructor
  · intro h x ⟨k, hk⟩
    have hn := (fixedPointFree_iff_reflection_exclusion s t hs ht).mp h (-k) x
    apply hn
    rw [Perm.mul_apply, ← hk, ← Perm.mul_apply, ← zpow_add]
    simp
  · intro h
    constructor
    · intro x hx
      exact h x ⟨0, by simpa only [zpow_zero, Perm.one_apply] using hx.symm⟩
    · intro x hx
      exact h x ⟨1, by simp only [zpow_one, Perm.mul_apply, hx]⟩

private theorem left_swaps_orbits (hs : Function.Involutive s)
    (ht : Function.Involutive t) {x y : X}
    (h : (s * t).SameCycle x y ∨ (s * t).SameCycle (s x) y) :
    (s * t).SameCycle x (s y) ∨ (s * t).SameCycle (s x) (s y) := by
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩
  · right
    refine ⟨-k, ?_⟩
    rw [← hk]
    exact (congrArg (fun p : Perm X => p x) (invert_rotation s t hs ht k)).symm
  · left
    refine ⟨-k, ?_⟩
    rw [← hk]
    have h := congrArg (fun p : Perm X => p (s x)) (invert_rotation s t hs ht k)
    simp only [Perm.mul_apply] at h
    rw [hs x] at h
    exact h.symm

private theorem connected_zpow (hs : Function.Involutive s)
    (ht : Function.Involutive t) (x : X) (k : ℤ) :
    Connected s t x (((s * t) ^ k) x) := by
  have hf (y : X) : Connected s t y ((s * t) y) :=
    (show Connected s t y (t y) from .single (Or.inr rfl)).trans
      (show Connected s t (t y) (s (t y)) from .single (Or.inl rfl))
  have hb (y : X) : Connected s t y ((s * t)⁻¹ y) := by
    rw [mul_inv_rev, inv_eq_self s hs, inv_eq_self t ht]
    exact (show Connected s t y (s y) from .single (Or.inl rfl)).trans
      (show Connected s t (s y) (t (s y)) from .single (Or.inr rfl))
  have hp (p : Perm X) (hh : ∀ y, Connected s t y (p y)) (n : ℕ) :
      Connected s t x ((p ^ n) x) := by
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hh _)
  cases k with
  | ofNat n =>
    change Connected s t x (((s * t) ^ (n : ℤ)) x)
    rw [zpow_natCast]
    exact hp (s * t) hf n
  | negSucc n =>
    simpa only [zpow_negSucc, inv_pow] using hp (s * t)⁻¹ hb (n + 1)

/-- Every alternating path ends in exactly one of the two candidate product
orbits; the candidates may coincide when fixed points are allowed. -/
theorem connected_iff_rotation_orbits (hs : Function.Involutive s)
    (ht : Function.Involutive t) (x y : X) :
    Connected s t x y ↔
      (s * t).SameCycle x y ∨ (s * t).SameCycle (s x) y := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (Perm.SameCycle.refl _ _)
    | @tail u v h huv ih =>
      rcases huv with hsu | htu
      · subst v
        exact left_swaps_orbits s t hs ht ih
      · subst v
        have hh := left_swaps_orbits s t hs ht ih
        have he : t u = (s * t)⁻¹ (s u) := by
          simpa only [zpow_neg_one, Perm.mul_apply] using
            congrArg (fun p : Perm X => p u) (right_as_reflection s t hs ht)
        rw [he]
        exact hh.imp (fun h => h.symm_apply_right) (fun h => h.symm_apply_right)
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact connected_zpow s t hs ht x k
    · exact (show Connected s t x (s x) from .single (Or.inl rfl)).trans
        (connected_zpow s t hs ht (s x) k)

private theorem left_image_orbit (hs : Function.Involutive s)
    (ht : Function.Involutive t) (x : X) :
    s '' RotationOrbit (s * t) x = RotationOrbit (s * t) (s x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨k, hk⟩, rfl⟩
    refine ⟨-k, ?_⟩
    rw [← hk]
    exact (congrArg (fun p : Perm X => p x) (invert_rotation s t hs ht k)).symm
  · rintro ⟨k, hk⟩
    refine ⟨s y, ⟨-k, ?_⟩, hs y⟩
    rw [← hk]
    have h := congrArg (fun p : Perm X => p (s x)) (invert_rotation s t hs ht k)
    simp only [Perm.mul_apply] at h
    rw [hs x] at h
    exact h.symm

/-- Each matching component is the disjoint union of two nonempty product
orbits. Each matching swaps the two pieces, including when the matchings agree. -/
theorem component_split (hs : Function.Involutive s) (ht : Function.Involutive t)
    (hsl : ∀ x, s x ≠ x) (htr : ∀ x, t x ≠ x) (x : X) :
    Disjoint (RotationOrbit (s * t) x) (RotationOrbit (s * t) (s x)) ∧
    (RotationOrbit (s * t) x).Nonempty ∧
    (RotationOrbit (s * t) (s x)).Nonempty ∧
    {y | Connected s t x y} =
      RotationOrbit (s * t) x ∪ RotationOrbit (s * t) (s x) ∧
    s '' RotationOrbit (s * t) x = RotationOrbit (s * t) (s x) ∧
    t '' RotationOrbit (s * t) x = RotationOrbit (s * t) (s x) := by
  have hsep := (fixedPointFree_iff_rotation_separation s t hs ht).mp ⟨hsl, htr⟩
  refine ⟨Set.disjoint_left.mpr ?_, ⟨x, Perm.SameCycle.refl _ _⟩,
    ⟨s x, Perm.SameCycle.refl _ _⟩, ?_, left_image_orbit s t hs ht x, ?_⟩
  · intro y hxy hsy
    exact hsep x (hxy.trans hsy.symm)
  · ext y
    exact connected_iff_rotation_orbits s t hs ht x y
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hsz : s z ∈ RotationOrbit (s * t) (s x) := by
        rw [← left_image_orbit s t hs ht x]
        exact Set.mem_image_of_mem s hz
      have he : t z = (s * t)⁻¹ (s z) := by
        simpa only [zpow_neg_one, Perm.mul_apply] using
          congrArg (fun p : Perm X => p z) (right_as_reflection s t hs ht)
      rw [he]
      exact hsz.symm_apply_right
    · intro hy
      have hry : (s * t).SameCycle (s x) ((s * t) y) := hy.apply_right
      change (s * t) y ∈ RotationOrbit (s * t) (s x) at hry
      rw [← left_image_orbit s t hs ht x] at hry
      rcases hry with ⟨z, hz, hzy⟩
      refine ⟨z, hz, ?_⟩
      have he : t z = (s * t)⁻¹ (s z) := by
        simpa only [zpow_neg_one, Perm.mul_apply] using
          congrArg (fun p : Perm X => p z) (right_as_reflection s t hs ht)
      rw [he, hzy]
      exact (s * t).symm_apply_apply y

/-- The product orbit classes occurring in one matching component are
precisely the two distinct classes represented by x and its s-partner. -/
theorem component_orbit_classes (hs : Function.Involutive s) (ht : Function.Involutive t)
    (hsl : ∀ x, s x ≠ x) (htr : ∀ x, t x ≠ x) (x : X) :
    Set.range (fun y : {y // Connected s t x y} => RotationOrbit (s * t) y.val) =
      {RotationOrbit (s * t) x, RotationOrbit (s * t) (s x)} ∧
    RotationOrbit (s * t) x ≠ RotationOrbit (s * t) (s x) := by
  have horbit {a b : X} (h : (s * t).SameCycle a b) :
      RotationOrbit (s * t) a = RotationOrbit (s * t) b := by
    ext z
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  constructor
  · ext O
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      rcases (connected_iff_rotation_orbits s t hs ht x y).mp hy with hx | hsx
      · exact Or.inl (horbit hx).symm
      · exact Or.inr (horbit hsx).symm
    · rintro (rfl | rfl)
      · exact ⟨⟨x, Relation.ReflTransGen.refl⟩, rfl⟩
      · exact ⟨⟨s x, Relation.ReflTransGen.single (Or.inl rfl)⟩, rfl⟩
  · intro heq
    have h := (component_split s t hs ht hsl htr x).1
    apply Set.disjoint_left.mp h (Perm.SameCycle.refl (s * t) x)
    rw [← heq]
    exact Perm.SameCycle.refl _ _

#print axioms fixedPointFree_iff_reflection_exclusion
#print axioms fixedPointFree_iff_rotation_separation
#print axioms connected_iff_rotation_orbits
#print axioms component_split
#print axioms component_orbit_classes

end D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
