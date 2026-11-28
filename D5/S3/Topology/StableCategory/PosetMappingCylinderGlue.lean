import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.UpperLower.Basic

/-!
# Poset mapping cylinders glued along a lower subposet

For `u : R →o A` and an order embedding `e : R ↪o V` with lower range,
the only cross-summand inequalities go from `e r` to an `a` above `u r`.
Taking `e` to be the identity gives the non-Hausdorff mapping cylinder.
-/

set_option autoImplicit false

namespace D5.S3.Topology.PosetMappingCylinderGlue

variable {R A V : Type*} [PartialOrder R] [PartialOrder A] [PartialOrder V]

/-- The carrier `A ⊕ V` with the order determined by the gluing data. -/
def Glue (u : R →o A) (e : R ↪o V) (_ : IsLowerSet (Set.range (e : R → V))) : Type _ :=
  A ⊕ V

private def glueLE (u : R →o A) (e : R ↪o V) : A ⊕ V → A ⊕ V → Prop
  | .inl a, .inl b => a ≤ b
  | .inr v, .inr w => v ≤ w
  | .inr v, .inl a => ∃ r : R, v = e r ∧ u r ≤ a
  | .inl _, .inr _ => False

variable (u : R →o A) (e : R ↪o V) (hLower : IsLowerSet (Set.range (e : R → V)))

private def sumOrder : PartialOrder (A ⊕ V) where
  le := glueLE u e
  le_refl x := by
    cases x with
    | inl a => exact le_refl a
    | inr v => exact le_refl v
  le_trans x y z hxy hyz := by
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        cases z with
        | inl c => exact le_trans (α := A) hxy hyz
        | inr w => exact False.elim hyz
      | inr v => exact False.elim hxy
    | inr v =>
      cases y with
      | inl a =>
        cases z with
        | inl b =>
          change (∃ r : R, v = e r ∧ u r ≤ a) at hxy
          obtain ⟨r, hr, hra⟩ := hxy
          change ∃ r : R, v = e r ∧ u r ≤ b
          exact ⟨r, hr, le_trans (α := A) hra hyz⟩
        | inr w => exact False.elim hyz
      | inr w =>
        cases z with
        | inl a =>
          change (∃ r : R, w = e r ∧ u r ≤ a) at hyz
          obtain ⟨r, hw, hra⟩ := hyz
          have hv : v ∈ Set.range (e : R → V) :=
            hLower (show v ≤ w from hxy) ⟨r, hw.symm⟩
          obtain ⟨s, hs⟩ := hv
          have hsr : e s ≤ e r := by
            rw [hs, ← hw]
            exact hxy
          change ∃ s : R, v = e s ∧ u s ≤ a
          exact ⟨s, hs.symm, (u.monotone (e.le_iff_le.mp hsr)).trans hra⟩
        | inr t => exact le_trans (α := V) hxy hyz
  le_antisymm x y hxy hyx := by
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (le_antisymm (α := A) hxy hyx)
      | inr w => exact False.elim hxy
    | inr v =>
      cases y with
      | inl b => exact False.elim hyx
      | inr w => exact congrArg Sum.inr (le_antisymm (α := V) hxy hyx)

instance : PartialOrder (Glue u e hLower) := sumOrder u e hLower

instance [Fintype A] [Fintype V] : Fintype (Glue u e hLower) :=
  inferInstanceAs (Fintype (A ⊕ V))

/-- Inclusion of the target of the cylinder map. -/
def inA : A ↪o Glue u e hLower :=
  OrderEmbedding.ofMapLEIff (β := Glue u e hLower) (fun a : A => (Sum.inl a : A ⊕ V))
    (fun _ _ => Iff.rfl)

/-- Inclusion of the poset containing the lower copy of `R`. -/
def inV : V ↪o Glue u e hLower :=
  OrderEmbedding.ofMapLEIff (β := Glue u e hLower) (fun v : V => (Sum.inr v : A ⊕ V))
    (fun _ _ => Iff.rfl)

@[simp] theorem inV_le_inA_iff (v : V) (a : A) :
    inV u e hLower v ≤ inA u e hLower a ↔ ∃ r : R, v = e r ∧ u r ≤ a := Iff.rfl

@[simp] theorem not_inA_le_inV (a : A) (v : V) :
    ¬ inA u e hLower a ≤ inV u e hLower v := fun h => h

private theorem idRangeLower (R : Type*) [PartialOrder R] :
    IsLowerSet (Set.range (OrderEmbedding.id R : R → R)) := by
  rw [OrderEmbedding.coe_id, Set.range_id]
  exact isLowerSet_univ

/-- The non-Hausdorff mapping cylinder on `A ⊕ R`. -/
abbrev Cylinder := Glue u (OrderEmbedding.id R) (idRangeLower R)

abbrev cylinderA : A ↪o Cylinder u := inA u (OrderEmbedding.id R) (idRangeLower R)

abbrev cylinderR : R ↪o Cylinder u := inV u (OrderEmbedding.id R) (idRangeLower R)

@[simp] theorem cylinderR_le_cylinderA_iff (r : R) (a : A) :
    cylinderR u r ≤ cylinderA u a ↔ u r ≤ a := by
  change (∃ s : R, r = s ∧ u s ≤ a) ↔ u r ≤ a
  constructor
  · rintro ⟨s, rfl, h⟩
    exact h
  · exact fun h => ⟨r, rfl, h⟩

/-- The cylinder embeds into the glued poset via the identity on `A` and `e` on `R`. -/
def inCylinder : Cylinder u ↪o Glue u e hLower :=
  OrderEmbedding.ofMapLEIff (α := Cylinder u) (β := Glue u e hLower)
    (fun x => (Sum.map id (e : R → V) x : A ⊕ V)) (by
      intro x y
      change A ⊕ R at x y
      cases x with
      | inl a => cases y <;> exact Iff.rfl
      | inr r =>
        cases y with
        | inl a =>
          change (∃ s : R, e r = e s ∧ u s ≤ a) ↔ (∃ s : R, r = s ∧ u s ≤ a)
          constructor
          · rintro ⟨s, hs, hsa⟩
            exact ⟨s, e.injective hs, hsa⟩
          · rintro ⟨s, hs, hsa⟩
            exact ⟨s, congrArg (fun t : R => e t) hs, hsa⟩
        | inr s => exact e.le_iff_le)

@[simp] theorem inCylinder_cylinderA (a : A) :
    inCylinder u e hLower (cylinderA u a) = inA u e hLower a := rfl

@[simp] theorem inCylinder_cylinderR (r : R) :
    inCylinder u e hLower (cylinderR u r) = inV u e hLower (e r) := rfl

section Evaluation

variable {P : Type*} [Preorder P] (f : A →o P) (g : V →o P)
  (agree : g.comp e.toOrderHom = f.comp u)

/-- Evaluate on either summand using two maps that agree along `R`. -/
def evaluate : Glue u e hLower →o P where
  toFun x := Sum.elim (f : A → P) (g : V → P) x
  monotone' := by
    intro x y hxy
    change A ⊕ V at x y
    cases x with
    | inl a =>
      cases y with
      | inl b => exact f.monotone (show a ≤ b from hxy)
      | inr w => exact False.elim hxy
    | inr v =>
      cases y with
      | inl a =>
        change (∃ r : R, v = e r ∧ u r ≤ a) at hxy
        obtain ⟨r, hr, hra⟩ := hxy
        have hAgree : g (e r) = f (u r) := congrArg (fun k : R →o P => k r) agree
        change g v ≤ f a
        rw [hr, hAgree]
        exact f.monotone hra
      | inr w => exact g.monotone (show v ≤ w from hxy)

@[simp] theorem evaluate_comp_inA :
    (evaluate u e hLower f g agree).comp (inA u e hLower).toOrderHom = f := rfl

@[simp] theorem evaluate_comp_inV :
    (evaluate u e hLower f g agree).comp (inV u e hLower).toOrderHom = g := rfl

/-- The cylinder projection is the identity on `A` and `u` on `R`. -/
def retract : Cylinder u →o A :=
  evaluate u (OrderEmbedding.id R) (idRangeLower R) OrderHom.id u rfl

@[simp] theorem evaluate_comp_inCylinder :
    (evaluate u e hLower f g agree).comp (inCylinder u e hLower).toOrderHom =
      f.comp (retract u) := by
  apply OrderHom.ext
  funext x
  change A ⊕ R at x
  cases x with
  | inl a => rfl
  | inr r => exact congrArg (fun k : R →o P => k r) agree

end Evaluation

/-- Every chain is contained in the image of `V` or the image of the cylinder. -/
theorem chain_subset_range {s : Set (Glue u e hLower)} (hs : IsChain (· ≤ ·) s) :
    s ⊆ Set.range (inV u e hLower : V → Glue u e hLower) ∨
    s ⊆ Set.range (inCylinder u e hLower : Cylinder u → Glue u e hLower) := by
  classical
  by_cases hA : ∃ a : A, inA u e hLower a ∈ s
  · right
    obtain ⟨a, ha⟩ := hA
    intro x hx
    change A ⊕ V at x
    cases x with
    | inl b => exact ⟨cylinderA u b, rfl⟩
    | inr v =>
      have hv : inV u e hLower v ∈ s := hx
      rcases hs.total hv ha with h | h
      · obtain ⟨r, hr, _⟩ := (inV_le_inA_iff u e hLower v a).mp h
        exact ⟨cylinderR u r, congrArg (fun w : V => inV u e hLower w) hr.symm⟩
      · exact (not_inA_le_inV u e hLower a v h).elim
  · left
    intro x hx
    change A ⊕ V at x
    cases x with
    | inl a => exact (hA ⟨a, hx⟩).elim
    | inr v => exact ⟨v, rfl⟩

/-- The two images meet exactly in the common copy of `R`. -/
theorem range_inV_inter_range_inCylinder :
    Set.range (inV u e hLower : V → Glue u e hLower) ∩
      Set.range (inCylinder u e hLower : Cylinder u → Glue u e hLower) =
    Set.range (e.comp (inV u e hLower) : R → Glue u e hLower) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    change (∃ v : V, inV u e hLower v = x) ∧
      (∃ m : Cylinder u, inCylinder u e hLower m = x) at hx
    obtain ⟨⟨v, rfl⟩, m, hm⟩ := hx
    change A ⊕ R at m
    cases m with
    | inl a =>
      have ha : (Sum.inl a : A ⊕ V) = Sum.inr v := hm
      exact (Sum.inl_ne_inr ha).elim
    | inr r => exact ⟨r, hm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨⟨e r, rfl⟩, ⟨cylinderR u r, rfl⟩⟩

end D5.S3.Topology.PosetMappingCylinderGlue
