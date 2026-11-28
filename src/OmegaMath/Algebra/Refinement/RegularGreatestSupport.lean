module

public import OmegaMath.Algebra.Refinement.RegularComponents
public import OmegaMath.Algebra.Refinement.FiniteTransport
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Finset.Order

/-!
Omega original.

Greatest supports in joint additive-observation fibers over conical regular
commutative monoids. The coefficient operations and equalities are the original
ones. Component identities preserve the observations while joining supports;
finite coordinates then suffice even for an infinite family of observations.
-/

@[expose] public section

namespace Omega.Refinement.Regular

universe u v w z

variable {K : Type u} [AddCommMonoid K]

/-- Two vectors with the same additive observations admit a vector with those
observations and exactly the union of their supports. No finite carrier is needed. -/
theorem joint_fiber_support_union (hc : Conical K) (hr : AddRegular K)
    {I : Type v} {J : Type w} {M : J → Type z} [∀ j, AddMonoid (M j)]
    (F : ∀ j, (I → K) →+ M j) (p q : I → K)
    (hpq : ∀ j, F j p = F j q) :
    ∃ r : I → K, (∀ j, F j r = F j p) ∧
      Function.support r = Function.support p ∪ Function.support q := by
  classical
  choose e he hqe using fun i => regular_component_idempotent hr (q i)
  have hqe_add : q + e = q := by
    funext i
    exact (add_comm _ _).trans (component_identity (he i) (hqe i))
  have he_zero (i : I) : e i = 0 ↔ q i = 0 := by
    constructor
    · intro h
      obtain ⟨t, ht⟩ := (hqe i).2
      exact (hc _ _ (ht.trans h)).1
    · intro h
      obtain ⟨t, ht⟩ := (hqe i).1
      exact (hc _ _ (ht.trans h)).1
  refine ⟨p + e, ?_, ?_⟩
  · intro j
    calc
      F j (p + e) = F j p + F j e := (F j).map_add _ _
      _ = F j q + F j e := by rw [hpq j]
      _ = F j (q + e) := ((F j).map_add _ _).symm
      _ = F j p := by rw [hqe_add, hpq j]
  · ext i
    change p i + e i ≠ 0 ↔ p i ≠ 0 ∨ q i ≠ 0
    constructor
    · intro h
      by_contra hn
      push Not at hn
      exact h (by rw [hn.1, (he_zero i).mpr hn.2, zero_add])
    · rintro (h | h) hz
      · exact h (hc _ _ hz).1
      · exact h ((he_zero i).mp (hc _ _ hz).2)

/-- Every joint additive-observation fiber over finitely many coordinates has
a witness containing every feasible support. Targets need only be additive
monoids; the dependent observation family can be infinite or empty. -/
theorem exists_greatest_joint_fiber_support (hc : Conical K) (hr : AddRegular K)
    {I : Type v} [Finite I] {J : Type w} {M : J → Type z}
    [∀ j, AddMonoid (M j)] (F : ∀ j, (I → K) →+ M j) (p : I → K) :
    ∃ r : I → K, (∀ j, F j r = F j p) ∧
      ∀ q : I → K, (∀ j, F j q = F j p) →
        ∀ i : I, q i ≠ 0 → r i ≠ 0 := by
  classical
  let T := {q : I → K // ∀ j, F j q = F j p}
  let base : T := ⟨p, fun _ => rfl⟩
  letI : Nonempty T := ⟨base⟩
  let s : T → Set I := fun q => Function.support q.val
  have hd : Directed (· ⊆ ·) s := by
    intro a b
    obtain ⟨r, hrF, hrs⟩ := joint_fiber_support_union hc hr F a.val b.val
      (fun j => (a.property j).trans (b.property j).symm)
    refine ⟨⟨r, fun j => (hrF j).trans (a.property j)⟩, ?_, ?_⟩
    · intro i hi
      change i ∈ Function.support r
      rw [hrs]
      exact Or.inl hi
    · intro i hi
      change i ∈ Function.support r
      rw [hrs]
      exact Or.inr hi
  let c : I → T := fun i =>
    if h : ∃ q : T, q.val i ≠ 0 then Classical.choose h else base
  letI := Fintype.ofFinite I
  obtain ⟨r, hr⟩ := hd.finset_le (Finset.univ.image c)
  refine ⟨r.val, r.property, ?_⟩
  intro q hq i hi
  have hex : ∃ q : T, q.val i ≠ 0 := ⟨⟨q, hq⟩, hi⟩
  have hci : (c i).val i ≠ 0 := by
    dsimp [c]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact hr (c i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hci

end Omega.Refinement.Regular
