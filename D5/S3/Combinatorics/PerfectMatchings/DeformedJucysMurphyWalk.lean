/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyWalk
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic]
   utility: none
   digest: The native matching walk covers its component within the vertex bound. -/

import D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

set_option autoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk

open Equiv
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

attribute [local instance] Classical.propDecidable

/-- The native partner map as a permutation, without changing labels. -/
def matchingPerm {k : ℕ} (p : P k) : Perm (Fin (2 * k)) :=
  p.property.1.toPerm

/-- The same two-coloured matching component as in Definition 4.1.
The order of the two generators makes the rotation match two native steps. -/
def Component {k : ℕ} (p : P k) (x y : Fin (2 * k)) : Prop :=
  Connected (matchingPerm p) (matchingPerm (e k)) x y

private theorem walk_step {k : ℕ} (p : P k) (x : Fin (2 * k)) (n : ℕ) :
    walk p x (n + 1) = if n % 2 = 0 then (e k).val (walk p x n)
      else p.val (walk p x n) := rfl

private theorem walk_even_odd {k : ℕ} (p : P k) (x : Fin (2 * k)) (n : ℕ) :
    walk p x (2 * n) = ((matchingPerm p * matchingPerm (e k)) ^ n) x ∧
    walk p x (2 * n + 1) = (e k).val
      (((matchingPerm p * matchingPerm (e k)) ^ n) x) := by
  induction n with
  | zero => simp [walk, matchingPerm, e]
  | succ n ih =>
    have he : walk p x (2 * (n + 1)) =
        p.val ((e k).val (((matchingPerm p * matchingPerm (e k)) ^ n) x)) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, walk_step, if_neg (by omega)]
      rw [ih.2]
    constructor
    · simpa only [pow_succ', Perm.mul_apply, matchingPerm, Function.Involutive.coe_toPerm]
        using he
    · rw [walk_step, if_pos (by omega)]
      rw [he]
      simp only [pow_succ', Perm.mul_apply, matchingPerm, Function.Involutive.coe_toPerm]

private theorem orbit_data {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    Disjoint (RotationOrbit (matchingPerm p * matchingPerm (e k)) x)
      (RotationOrbit (matchingPerm p * matchingPerm (e k)) (p.val x)) ∧
    (matchingPerm (e k)) '' RotationOrbit (matchingPerm p * matchingPerm (e k)) x =
      RotationOrbit (matchingPerm p * matchingPerm (e k)) (p.val x) := by
  have h := component_split (matchingPerm p) (matchingPerm (e k))
    p.property.1 (e k).property.1 p.property.2 (e k).property.2 x
  exact ⟨h.1, h.2.2.2.2.2⟩

private theorem walk_orbit {k : ℕ} (p : P k) (x : Fin (2 * k)) (n : ℕ) :
    if n % 2 = 0 then
      walk p x n ∈ RotationOrbit (matchingPerm p * matchingPerm (e k)) x
    else walk p x n ∈
      RotationOrbit (matchingPerm p * matchingPerm (e k)) (p.val x) := by
  have he := (walk_even_odd p x (n / 2)).1
  have ho := (walk_even_odd p x (n / 2)).2
  have hm : ((matchingPerm p * matchingPerm (e k)) ^ (n / 2)) x ∈
      RotationOrbit (matchingPerm p * matchingPerm (e k)) x :=
    (Perm.SameCycle.refl _ _).pow_right
  split
  · next h => rwa [show n = 2 * (n / 2) by omega, he]
  · next h =>
    rw [show n = 2 * (n / 2) + 1 by omega, ho]
    change matchingPerm (e k) _ ∈ _
    rw [← (orbit_data p x).2]
    exact Set.mem_image_of_mem _ hm

/-- Native step parity is exactly the full product-orbit colour. -/
theorem walk_colour {k : ℕ} (p : P k) (x : Fin (2 * k)) (n : ℕ) :
    decide ((matchingPerm p * matchingPerm (e k)).SameCycle x (walk p x n)) =
      (n % 2 == 0) := by
  classical
  have hm := walk_orbit p x n
  by_cases he : n % 2 = 0
  · simp only [he, if_true] at hm
    have hs : (matchingPerm p * matchingPerm (e k)).SameCycle x (walk p x n) := hm
    simp [hs, he]
  · simp only [he, if_false] at hm
    have hn : ¬ (matchingPerm p * matchingPerm (e k)).SameCycle x (walk p x n) := by
      intro hx
      exact Set.disjoint_left.mp (orbit_data p x).1 hx hm
    simp [hn, he]

private theorem walk_same_parity {k : ℕ} (p : P k) (x : Fin (2 * k))
    {i j : ℕ} (h : walk p x i = walk p x j) : i % 2 = j % 2 := by
  have hi := walk_orbit p x i
  have hj := walk_orbit p x j
  by_contra hn
  by_cases hi0 : i % 2 = 0
  · have hj0 : ¬ j % 2 = 0 := by omega
    simp only [hi0, hj0, if_true, if_false] at hi hj
    exact Set.disjoint_left.mp (orbit_data p x).1 hi (h ▸ hj)
  · have hj0 : j % 2 = 0 := by omega
    simp only [hi0, hj0, if_true, if_false] at hi hj
    exact Set.disjoint_left.mp (orbit_data p x).1 hj (h ▸ hi)

private theorem walk_equal_tails {k : ℕ} (p : P k) (x : Fin (2 * k))
    {i j : ℕ} (h : walk p x i = walk p x j) (d : ℕ) :
    walk p x (i + d) = walk p x (j + d) := by
  have hp := walk_same_parity p x h
  induction d with
  | zero => simpa using h
  | succ d ih =>
    rw [Nat.add_succ, Nat.add_succ, walk_step, walk_step, ih]
    rw [show (i + d) % 2 = (j + d) % 2 by omega]

private theorem component_has_walk {k : ℕ} (p : P k) (x y : Fin (2 * k))
    (h : Component p x y) : ∃ n, walk p x n = y := by
  rcases (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
    p.property.1 (e k).property.1 x y).mp h with h | h
  · obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨2 * n, (walk_even_odd p x n).1.trans hn⟩
  · change y ∈ RotationOrbit (matchingPerm p * matchingPerm (e k)) (p.val x) at h
    rw [← (orbit_data p x).2] at h
    obtain ⟨z, hz, hzy⟩ := h
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    exact ⟨2 * n + 1, (walk_even_odd p x n).2.trans (congrArg (e k).val hn |>.trans hzy)⟩

/-- The original finite walk visits every vertex of its entire component.
In particular, doubled matching/identity edges remain two-vertex components. -/
theorem walk_covers_component {k : ℕ} (p : P k) (x y : Fin (2 * k)) :
    Component p x y ↔ ∃ n < 2 * k, walk p x n = y := by
  classical
  constructor
  · intro h
    have hex := component_has_walk p x y h
    let m := Nat.find hex
    have hm : walk p x m = y := Nat.find_spec hex
    have hmin : ∀ i < m, walk p x i ≠ y := fun i hi => Nat.find_min hex hi
    have hinj : Function.Injective (fun i : Fin (m + 1) => walk p x i.val) := by
      intro i j hij
      apply Fin.ext
      by_contra hne
      have shorten (a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) (hab : a < b)
          (heq : walk p x a = walk p x b) : False := by
        have ht := walk_equal_tails p x heq (m - b)
        rw [show b + (m - b) = m by omega, hm] at ht
        exact hmin (a + (m - b)) (by omega) ht
      rcases lt_or_gt_of_ne hne with hij' | hji'
      · exact shorten i.val j.val (by omega) (by omega) hij' hij
      · exact shorten j.val i.val (by omega) (by omega) hji' hij.symm
    have hc := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hc
    exact ⟨m, by omega, hm⟩
  · rintro ⟨n, _, rfl⟩
    have hc : ∀ m, Component p x (walk p x m) := by
      intro m
      induction m with
      | zero => exact Relation.ReflTransGen.refl
      | succ m ih =>
        rw [walk_step]
        split
        · exact ih.tail (Or.inr rfl)
        · exact ih.tail (Or.inl rfl)
    exact hc n

#print axioms walk_colour
#print axioms walk_covers_component

end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk
