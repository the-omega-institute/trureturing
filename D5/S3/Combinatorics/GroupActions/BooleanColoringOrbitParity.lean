/- GID: D5/S3/Combinatorics/GroupActions/BooleanColoringOrbitParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GroupActions/BooleanColoringOrbitParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd Boolean coloring orbits are at most as numerous as even ones. -/

module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.Data.Finset.Dedup
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
For each group element, XOR with an odd fixed coloring exchanges the two parities among
its fixed colorings. When there is no odd fixed coloring, the odd fixed-point count is zero.
Burnside's lemma turns these pointwise comparisons into the orbit inequality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace D5.S3.Combinatorics.GroupActions.BooleanColoringOrbitParity

public section

open scoped BigOperators

universe u v

variable {G : Type u} {α : Type v}

/-- Boolean colorings equipped with the action by inverse relabeling. -/
@[expose] def Coloring (α : Type v) := α → Bool

/-- XOR over the sites. With a complete duplicate-free list, `true` means odd. -/
@[expose] def parity (sites : List α) (c : Coloring α) : Bool :=
  sites.foldr (fun x acc => c x ^^ acc) false

private def Fixed (σ : α → α) (c : Coloring α) : Prop :=
  ∀ x, c (σ x) = c x

private def toggle (u c : Coloring α) : Coloring α :=
  fun x => c x ^^ u x

private theorem xor_interchange (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem parity_toggle (sites : List α) (u c : Coloring α) :
    parity sites (toggle u c) = (parity sites c ^^ parity sites u) := by
  induction sites with
  | nil => rfl
  | cons x sites ih =>
    change
      ((c x ^^ u x) ^^ parity sites (toggle u c)) =
        ((c x ^^ parity sites c) ^^ (u x ^^ parity sites u))
    rw [ih]
    exact xor_interchange _ _ _ _

private theorem toggle_twice (u c : Coloring α) : toggle u (toggle u c) = c := by
  funext x
  exact Bool.bne_self_right (c x) (u x)

private theorem fixed_toggle_iff {σ : α → α} {u : Coloring α} (hu : Fixed σ u)
    (c : Coloring α) : Fixed σ (toggle u c) ↔ Fixed σ c := by
  constructor
  · intro hc x
    have hx := hc x
    change (c (σ x) ^^ u (σ x)) = (c x ^^ u x) at hx
    rw [hu x] at hx
    exact Bool.xor_left_inj.mp hx
  · intro hc x
    change (c (σ x) ^^ u (σ x)) = (c x ^^ u x)
    rw [hc x, hu x]

private theorem parity_toggle_odd {sites : List α} {u : Coloring α}
    (hu : parity sites u = true) (c : Coloring α) :
    parity sites (toggle u c) = !(parity sites c) := by
  rw [parity_toggle, hu, Bool.xor_true]

/-- Bijective relabeling preserves parity on a complete duplicate-free list. -/
private theorem parity_relabel (sites : List α) (sitesNodup : sites.Nodup)
    (sitesComplete : ∀ x, x ∈ sites) (σ : α → α)
    (σInjective : Function.Injective σ) (σSurjective : Function.Surjective σ)
    (c : Coloring α) : parity sites (fun x => c (σ x)) = parity sites c := by
  have hperm : (sites.map σ).Perm sites := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_map_iff σInjective).mpr sitesNodup) sitesNodup).mpr
    intro x
    constructor
    · intro _
      exact sitesComplete x
    · intro _
      obtain ⟨y, hy⟩ := σSurjective x
      exact List.mem_map.mpr ⟨y, sitesComplete y, hy⟩
  unfold parity
  rw [← List.foldr_map (f := σ) (g := fun x acc => c x ^^ acc)]
  exact hperm.foldr_eq' (fun x _ y _ acc => Bool.xor_left_comm (c y) (c x) acc) false

instance [Group G] [MulAction G α] : MulAction G (Coloring α) :=
  MulAction.compHom (α → Bool)
    (show G →* DomMulAct G from (MulEquiv.inv' G).toMonoidHom)

/-- The list of all sites used to compute parity. -/
@[expose] noncomputable def sites (α : Type v) [Fintype α] : List α :=
  (Finset.univ : Finset α).toList

private theorem parity_smul [Group G] [MulAction G α] [Fintype α] (g : G) (c : Coloring α) :
    parity (sites α) (g • c) = parity (sites α) c := by
  change parity (sites α) (fun x => c (g⁻¹ • x)) = parity (sites α) c
  exact parity_relabel (sites α) (Finset.nodup_toList _) (fun x => by simp [sites])
    (fun x => g⁻¹ • x) (MulAction.injective g⁻¹) (MulAction.surjective g⁻¹) c

/-- Colorings of parity `p`, with `true` denoting odd parity. -/
abbrev ParityColoring (α : Type v) [Fintype α] (p : Bool) :=
  { c : Coloring α // parity (sites α) c = p }

instance [Group G] [MulAction G α] [Fintype α] (p : Bool) :
    MulAction G (ParityColoring α p) where
  smul g c := ⟨g • c.val, by exact (parity_smul g c.val).trans c.property⟩
  one_smul c := Subtype.ext (one_smul G c.val)
  mul_smul g h c := Subtype.ext (mul_smul g h c.val)

private noncomputable local instance [Fintype α] : Fintype (Coloring α) := by
  classical
  exact inferInstanceAs (Fintype (α → Bool))

private noncomputable local instance [Fintype α] (p : Bool) : Fintype (ParityColoring α p) :=
  Fintype.ofFinite _

@[no_expose] noncomputable instance [Group G] [MulAction G α] [Fintype α] (p : Bool) :
    Fintype (MulAction.orbitRel.Quotient G (ParityColoring α p)) := by
  exact Fintype.ofFinite _

section
variable [Group G] [MulAction G α] [Fintype α]

variable (α) in
private abbrev FixedParityColoring (g : G) (p : Bool) :=
  ↥(MulAction.fixedBy (ParityColoring α p) g)

private noncomputable local instance (g : G) (p : Bool) : Fintype (FixedParityColoring α g p) :=
  Fintype.ofFinite _

private theorem fixed_of_fixedBy {g : G} {p : Bool} (c : FixedParityColoring α g p) :
    Fixed (fun x => g⁻¹ • x) c.val.val :=
  fun x => congrArg (fun d : ParityColoring α p => d.val x)
    (MulAction.mem_fixedBy.mp c.property)

private def toggleFixed {g : G} (odd : FixedParityColoring α g true) {p : Bool}
    (c : FixedParityColoring α g p) : FixedParityColoring α g (!p) := by
  refine ⟨⟨toggle odd.val.val c.val.val, ?_⟩, ?_⟩
  · rw [parity_toggle_odd odd.val.property, c.val.property]
  · apply MulAction.mem_fixedBy.mpr
    apply Subtype.ext
    exact funext ((fixed_toggle_iff (fixed_of_fixedBy odd) c.val.val).mpr (fixed_of_fixedBy c))

/-- An odd fixed coloring gives a parity-reversing involution on fixed colorings. -/
private def fixedByParityEquiv (g : G) (odd : ↥(MulAction.fixedBy (ParityColoring α true) g)) :
    ↥(MulAction.fixedBy (ParityColoring α true) g) ≃
      ↥(MulAction.fixedBy (ParityColoring α false) g) where
  toFun := toggleFixed odd
  invFun := toggleFixed odd
  left_inv c := Subtype.ext (Subtype.ext (toggle_twice odd.val.val c.val.val))
  right_inv c := Subtype.ext (Subtype.ext (toggle_twice odd.val.val c.val.val))

private theorem card_fixedBy_odd_le_even (g : G) :
    Fintype.card (FixedParityColoring α g true) ≤ Fintype.card (FixedParityColoring α g false) := by
  classical
  by_cases h : Nonempty (FixedParityColoring α g true)
  · obtain ⟨odd⟩ := h
    exact (Fintype.card_congr (fixedByParityEquiv g odd)).le
  · let _ : IsEmpty (FixedParityColoring α g true) := ⟨fun c => h ⟨c⟩⟩
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _

/-- The even Boolean colorings of a finite group action have at least as many orbits
as the odd Boolean colorings. -/
theorem card_odd_orbits_le_even [Finite G] :
    Fintype.card (MulAction.orbitRel.Quotient G (ParityColoring α true)) ≤
      Fintype.card (MulAction.orbitRel.Quotient G (ParityColoring α false)) := by
  let _ := Fintype.ofFinite G
  have h : (∑ g : G, Fintype.card (FixedParityColoring α g true)) ≤
      ∑ g : G, Fintype.card (FixedParityColoring α g false) :=
    Finset.sum_le_sum (fun g _ => card_fixedBy_odd_le_even (α := α) g)
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (ParityColoring α true),
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (ParityColoring α false)] at h
  exact Nat.le_of_mul_le_mul_right h (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩)

end

#print axioms card_odd_orbits_le_even

end

end D5.S3.Combinatorics.GroupActions.BooleanColoringOrbitParity
