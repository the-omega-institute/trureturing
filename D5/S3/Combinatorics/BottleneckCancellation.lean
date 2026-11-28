/- GID: D5/S3/Combinatorics/BottleneckCancellation
   generality: G
   mirror-B: none(waiver:covered-by-bottleneck-cancellation-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative cancellation of finitely many prescribed occurrence pairs in a pseudometric matching. -/

module

public import OmegaBuild.Commands
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Linarith

/-!
Omega original.

Quantitative cancellation of finitely many prescribed occurrence pairs in a
pseudometric matching. Occurrences, rather than their labels, are removed.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.BottleneckCancellation

open Finset

private theorem indicator_budget {I : Type*} {X : Type*} [Fintype I] [DecidableEq X]
    (p : I → X) (hp : Function.Injective p) (x z : X)
    (hx : x ∉ Set.range p) (C : ℝ) (hC : 0 ≤ C) :
    (if x = z then C else 0) + (∑ i, if p i = z then C else 0) ≤ C := by
  classical
  by_cases hz : z ∈ Set.range p
  · obtain ⟨i, rfl⟩ := hz
    have hxi : x ≠ p i := fun h => hx ⟨i, h.symm⟩
    rw [ite_eq_right hxi, zero_add]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [ite_eq_right (fun h => hji (hp h))]
    · simp
  · have hxi : ∀ i, p i ≠ z := fun i h => hz ⟨i, h⟩
    simp only [hxi, ↓reduceIte, Finset.sum_const_zero, add_zero]
    split_ifs <;> linarith

private theorem weighted_cancel (n : ℕ) :
    ∀ {X : Type*} {Y : Type*} {I : Type*} [Fintype I], Fintype.card I = n →
    ∀ {M : Type*} [PseudoMetricSpace M] (a : X → M) (b : Y → M)
      (e : X ≃ Y) (p : I → X) (q : I → Y)
      (_hp : Function.Injective p) (_hq : Function.Injective q)
      (c : X → ℝ) (w : I → ℝ),
      (∀ x, 0 ≤ c x) → (∀ i, 0 ≤ w i) →
      (∀ x, dist (a x) (b (e x)) ≤ c x) →
      (∀ i, dist (a (p i)) (b (q i)) ≤ w i) →
      ∃ f : {x // x ∉ Set.range p} ≃ {y // y ∉ Set.range q},
        ∀ x : {x // x ∉ Set.range p}, dist (a x) (b (f x)) ≤ c x + ∑ i, (c (p i) + w i) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X Y I _ hn M _ a b e p q hp hq c w hc hw he hd
    by_cases hI : Nonempty I
    · let i : I := Classical.choice hI
      let J := {j : I // j ≠ i}
      let X' := {x : X // x ≠ p i}
      let Y' := {y : Y // y ≠ q i}
      let p' : J → X' := fun j => ⟨p j, fun h => j.2 (hp h)⟩
      let q' : J → Y' := fun j => ⟨q j, fun h => j.2 (hq h)⟩
      have hp' : Function.Injective p' := fun j k h => Subtype.ext (hp (congrArg Subtype.val h))
      have hq' : Function.Injective q' := fun j k h => Subtype.ext (hq (congrArg Subtype.val h))
      let z := e.symm (q i)
      let E := (Equiv.swap (p i) z).trans e
      have Ei : E (p i) = q i := by simp [E, z]
      let e' : X' ≃ Y' := E.subtypeEquiv fun x => by
        change x ≠ p i ↔ E x ≠ q i
        rw [← Ei, E.injective.ne_iff]
      let C := c (p i) + w i
      have hC : 0 ≤ C := add_nonneg (hc _) (hw _)
      let c' : X' → ℝ := fun x => c x + if (x : X) = z then C else 0
      have hc' : ∀ x, 0 ≤ c' x := by
        intro x
        exact add_nonneg (hc _) (by split_ifs <;> positivity)
      have he' : ∀ x : X', dist (a x) (b (e' x)) ≤ c' x := by
        intro x
        change dist (a x) (b (E x)) ≤ c x + if (x : X) = z then C else 0
        by_cases hxz : (x : X) = z
        · have E_z : E z = e (p i) := by simp [E]
          rw [hxz, E_z, ite_eq_left rfl]
          have hz : e z = q i := e.apply_symm_apply _
          have h1 := he z
          have h2 := hd i
          have h3 := he (p i)
          have ht := dist_triangle (a z) (b (q i)) (a (p i))
          have ht' := dist_triangle (a z) (a (p i)) (b (e (p i)))
          rw [dist_comm (b (q i)) (a (p i))] at ht
          rw [hz] at h1
          dsimp [C]
          linarith
        · have Ex : E x = e x := by
            simp [E, Equiv.swap_apply_of_ne_of_ne x.2 hxz]
          rw [Ex, ite_eq_right hxz, add_zero]
          exact he x
      have hJ : Fintype.card J < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := i) (by simp)
      obtain ⟨f, hf⟩ := ih (Fintype.card J) hJ rfl
        (fun x : X' => a x) (fun y : Y' => b y) e' p' q' hp' hq'
        c' (fun j => w j) hc' (fun j => hw j) he' (fun j => hd j)
      let L : {x // x ∉ Set.range p} ≃ {x : X' // x ∉ Set.range p'} := {
        toFun := fun x => ⟨⟨x, fun h => x.2 ⟨i, h.symm⟩⟩, by
          rintro ⟨j, h⟩
          exact x.2 ⟨j, congrArg Subtype.val h⟩⟩
        invFun := fun x => ⟨x.1, by
          rintro ⟨j, h⟩
          by_cases hj : j = i
          · exact x.1.2 (by simpa [hj] using h.symm)
          · exact x.2 ⟨⟨j, hj⟩, Subtype.ext h⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      let R : {y // y ∉ Set.range q} ≃ {y : Y' // y ∉ Set.range q'} := {
        toFun := fun y => ⟨⟨y, fun h => y.2 ⟨i, h.symm⟩⟩, by
          rintro ⟨j, h⟩
          exact y.2 ⟨j, congrArg Subtype.val h⟩⟩
        invFun := fun y => ⟨y.1, by
          rintro ⟨j, h⟩
          by_cases hj : j = i
          · exact y.1.2 (by simpa [hj] using h.symm)
          · exact y.2 ⟨⟨j, hj⟩, Subtype.ext h⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      refine ⟨L.trans (f.trans R.symm), fun x => ?_⟩
      have hb := hf (L x)
      have hbudget : (if (x : X) = z then C else 0) +
          (∑ j : J, if p j = z then C else 0) ≤ C := by
        exact indicator_budget (fun j : J => p j)
          (fun j k h => Subtype.ext (hp h)) x z (by
            rintro ⟨j, h⟩
            exact x.2 ⟨j, h⟩) C hC
      have hsum : (∑ j : J, (c (p j) + w j)) + C =
          ∑ j : I, (c (p j) + w j) := by
        simpa [C, add_comm] using
          (Fintype.sum_eq_add_sum_subtype_ne (fun j : I => c (p j) + w j) i).symm
      change dist (a x) (b ((f (L x)).1 : Y)) ≤ _
      change dist (a x) (b ((f (L x)).1 : Y)) ≤
        c x + (if (x : X) = z then C else 0) +
          ∑ j : J, (c (p j) + (if p j = z then C else 0) + w j) at hb
      have hsplit : (∑ j : J, (c (p j) + (if p j = z then C else 0) + w j)) =
          (∑ j : J, (c (p j) + w j)) + (∑ j : J, if p j = z then C else 0) := by
        simp_rw [add_right_comm (c _) _ (w _)]
        exact Finset.sum_add_distrib
      rw [hsplit] at hb
      linarith
    · have : IsEmpty I := not_nonempty_iff.mp hI
      let f := e.subtypeEquiv (p := fun x => x ∉ Set.range p)
        (q := fun y => y ∉ Set.range q) (by simp)
      refine ⟨f, fun x => ?_⟩
      simpa [f] using he x

/-- A single total complement matching obeys the uniform cancellation bound.
The ambient index types may even be infinite; only the deletion sets are finite. -/
theorem complement_bound {X : Type*} {Y : Type*} {M : Type*} [PseudoMetricSpace M]
    (a : X → M) (b : Y → M) (e : X ≃ Y) (U : Finset X) (V : Finset Y)
    (d : U ≃ V) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (he : ∀ x, dist (a x) (b (e x)) ≤ ε)
    (hd : ∀ u : U, dist (a u) (b (d u)) ≤ η) :
    ∃ f : {x // x ∉ U} ≃ {y // y ∉ V},
      ∀ x : {x // x ∉ U}, dist (a x) (b (f x)) ≤ (U.card + 1 : ℝ) * ε + U.card * η := by
  classical
  obtain ⟨f, hf⟩ := weighted_cancel (Fintype.card U) rfl a b e
    (fun u : U => (u : X)) (fun u : U => (d u : Y))
    Subtype.val_injective (Subtype.val_injective.comp d.injective)
    (fun _ => ε) (fun _ => η) (fun _ => hε) (fun _ => hη) he hd
  have hrX : Set.range (fun u : U => (u : X)) = (U : Set X) := by ext; simp
  have hrY : Set.range (fun u : U => (d u : Y)) = (V : Set Y) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩; exact (d u).2
    · intro hy; exact ⟨d.symm ⟨y, hy⟩, by simp⟩
  let L := Equiv.subtypeEquivRight (fun x => show x ∉ U ↔
    x ∉ Set.range (fun u : U => (u : X)) by rw [hrX]; rfl)
  let R := Equiv.subtypeEquivRight (fun y => show y ∉ V ↔
    y ∉ Set.range (fun u : U => (d u : Y)) by rw [hrY]; rfl)
  refine ⟨L.trans (f.trans R.symm), fun x => ?_⟩
  have h := hf (L x)
  change dist (a x) (b (f (L x))) ≤ _
  change dist (a x) (b (f (L x))) ≤ ε + ∑ _i : U, (ε + η) at h
  simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using h

end Omega.BottleneckCancellation
