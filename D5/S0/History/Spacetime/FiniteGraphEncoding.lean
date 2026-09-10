/- GID: D5/S0/History/Spacetime/FiniteGraphEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/FiniteGraphEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent total single-valued HF graphs reconstruct functions on exactly their finite domain. -/

import D5.S0.History.Spacetime.HFEncoding
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

namespace D5.S0.History.Spacetime.FiniteGraphEncoding

open HFEncoding
noncomputable section

/-- No junk pairs, exactly the prescribed domain, and a unique legal value at each input. -/
def IsFunctionGraph (E : Finset HF) (P : HF → Prop) (g : HF) : Prop :=
  (∀ p, mem p g → ∃ x ∈ E, ∃ y, P y ∧ p = pair x y) ∧
  (∀ x : E, ∃! y : {c // P c}, mem (pair x.val y.val) g)

def graphCode {α : Type} {P : HF → Prop} (E : Finset HF)
    (e : α ≃ {c // P c}) (f : E → α) : HF := by
  classical
  exact setCode (Finset.univ.image (fun x : E => pair x.val (e (f x)).val))

theorem mem_graphCode {α : Type} {P : HF → Prop} (E : Finset HF)
    (e : α ≃ {c // P c}) (f : E → α) (p : HF) :
    mem p (graphCode E e f) ↔ ∃ x : E, p = pair x.val (e (f x)).val := by
  classical
  simp [graphCode, eq_comm]

theorem pair_mem_graphCode {α : Type} {P : HF → Prop} (E : Finset HF)
    (e : α ≃ {c // P c}) (f : E → α) (x : E) (y : HF) :
    mem (pair x.val y) (graphCode E e f) ↔ y = (e (f x)).val := by
  rw [mem_graphCode]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hx, hy⟩ := pair_inj.mp hz
    have : x = z := Subtype.ext hx
    simpa [← this] using hy
  · intro h; exact ⟨x, congrArg (pair x.val) h⟩

theorem graphCode_valid {α : Type} {P : HF → Prop} (E : Finset HF)
    (e : α ≃ {c // P c}) (f : E → α) : IsFunctionGraph E P (graphCode E e f) := by
  constructor
  · intro p hp
    obtain ⟨x, rfl⟩ := (mem_graphCode E e f p).mp hp
    exact ⟨x.val, x.property, _, (e (f x)).property, rfl⟩
  · intro x
    refine ⟨e (f x), (pair_mem_graphCode E e f x _).mpr rfl, ?_⟩
    intro y hy
    exact Subtype.ext ((pair_mem_graphCode E e f x _).mp hy)

/-- The decoder uses totality only at archived inputs, never an off-domain default. -/
def lookupCode {E : Finset HF} {P : HF → Prop} {g : HF}
    (h : IsFunctionGraph E P g) (x : E) : {c // P c} :=
  Classical.choose (h.2 x).exists

theorem lookupCode_mem {E : Finset HF} {P : HF → Prop} {g : HF}
    (h : IsFunctionGraph E P g) (x : E) : mem (pair x.val (lookupCode h x).val) g :=
  Classical.choose_spec (h.2 x).exists

theorem lookupCode_unique {E : Finset HF} {P : HF → Prop} {g : HF}
    (h : IsFunctionGraph E P g) (x : E) (y : {c // P c})
    (hy : mem (pair x.val y.val) g) : lookupCode h x = y :=
  (h.2 x).unique (lookupCode_mem h x) hy

/-- Every raw member is recovered by the unique lookup; this excludes hidden graph entries. -/
theorem mem_iff_lookup {E : Finset HF} {P : HF → Prop} {g : HF}
    (h : IsFunctionGraph E P g) (p : HF) :
    mem p g ↔ ∃ x : E, p = pair x.val (lookupCode h x).val := by
  constructor
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := h.1 p hp
    have hu := lookupCode_unique h ⟨x, hx⟩ ⟨y, hy⟩ hp
    exact ⟨⟨x, hx⟩, congrArg (pair x) (congrArg Subtype.val hu).symm⟩
  · rintro ⟨x, rfl⟩; exact lookupCode_mem h x

def decodeGraph {α : Type} {P : HF → Prop} {E : Finset HF}
    (e : α ≃ {c // P c}) (g : HF) (h : IsFunctionGraph E P g) : E → α :=
  fun x => e.symm (lookupCode h x)

@[simp] theorem decodeGraph_encode {α : Type} {P : HF → Prop} (E : Finset HF)
    (e : α ≃ {c // P c}) (f : E → α) :
    decodeGraph e (graphCode E e f) (graphCode_valid E e f) = f := by
  funext x
  have h := lookupCode_unique (graphCode_valid E e f) x (e (f x))
    ((pair_mem_graphCode E e f x _).mpr rfl)
  simp [decodeGraph, h]

@[simp] theorem encode_decodeGraph {α : Type} {P : HF → Prop} (E : Finset HF)
    (e : α ≃ {c // P c}) (g : HF) (h : IsFunctionGraph E P g) :
    graphCode E e (decodeGraph e g h) = g := by
  apply hf_ext
  intro p
  rw [mem_graphCode, mem_iff_lookup h]
  simp [decodeGraph]

def graph_code_equiv {α : Type} {P : HF → Prop} (E : Finset HF)
    (e : α ≃ {c // P c}) : (E → α) ≃ {g // IsFunctionGraph E P g} where
  toFun f := ⟨graphCode E e f, graphCode_valid E e f⟩
  invFun g := decodeGraph e g.val g.property
  left_inv := decodeGraph_encode E e
  right_inv g := Subtype.ext (encode_decodeGraph E e g.val g.property)

/-- A relation code contains only pairs of archived endpoints. -/
def IsRelationCode (E : Finset HF) (r : HF) : Prop :=
  ∀ p, mem p r → ∃ x ∈ E, ∃ y ∈ E, p = pair x y

def relationCode (E : Finset HF) (r : E → E → Prop) : HF := by
  classical
  exact setCode ((Finset.univ.filter (fun p : E × E => r p.1 p.2)).image
    (fun p => pair p.1.val p.2.val))

theorem mem_relationCode (E : Finset HF) (r : E → E → Prop) (p : HF) :
    mem p (relationCode E r) ↔ ∃ x y : E, r x y ∧ p = pair x.val y.val := by
  classical
  simp [relationCode, eq_comm]

@[simp] theorem pair_mem_relationCode (E : Finset HF) (r : E → E → Prop) (x y : E) :
    mem (pair x.val y.val) (relationCode E r) ↔ r x y := by
  rw [mem_relationCode]
  constructor
  · rintro ⟨u, v, huv, h⟩
    obtain ⟨hx, hy⟩ := pair_inj.mp h
    have : x = u := Subtype.ext hx
    have : y = v := Subtype.ext hy
    simpa [*] using huv
  · intro h; exact ⟨x, y, h, rfl⟩

theorem relationCode_valid (E : Finset HF) (r : E → E → Prop) :
    IsRelationCode E (relationCode E r) := by
  intro p hp
  obtain ⟨x, y, _, rfl⟩ := (mem_relationCode E r p).mp hp
  exact ⟨x.val, x.property, y.val, y.property, rfl⟩

def decodeRelation (E : Finset HF) (r : HF) : E → E → Prop :=
  fun x y => mem (pair x.val y.val) r

@[simp] theorem decodeRelation_encode (E : Finset HF) (r : E → E → Prop) :
    decodeRelation E (relationCode E r) = r := by
  funext x y; exact propext (pair_mem_relationCode E r x y)

@[simp] theorem encode_decodeRelation (E : Finset HF) (r : HF) (h : IsRelationCode E r) :
    relationCode E (decodeRelation E r) = r := by
  apply hf_ext
  intro p
  rw [mem_relationCode]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩; exact hxy
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := h p hp
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hp, rfl⟩

def relation_code_equiv (E : Finset HF) : (E → E → Prop) ≃ {r // IsRelationCode E r} where
  toFun r := ⟨relationCode E r, relationCode_valid E r⟩
  invFun r := decodeRelation E r.val
  left_inv := decodeRelation_encode E
  right_inv r := Subtype.ext (encode_decodeRelation E r.val r.property)

/-- A subset code contains only event names from E. -/
def IsSubsetCode (E : Finset HF) (s : HF) : Prop := ∀ x, mem x s → x ∈ E

def subsetCode (E : Finset HF) (s : Finset E) : HF := by
  classical
  exact setCode (s.image Subtype.val)

theorem mem_subsetCode (E : Finset HF) (s : Finset E) (p : HF) :
    mem p (subsetCode E s) ↔ ∃ x ∈ s, x.val = p := by
  classical
  simp [subsetCode]

@[simp] theorem event_mem_subsetCode (E : Finset HF) (s : Finset E) (x : E) :
    mem x.val (subsetCode E s) ↔ x ∈ s := by
  rw [mem_subsetCode]
  constructor
  · rintro ⟨y, hy, h⟩; exact (Subtype.ext h : y = x) ▸ hy
  · intro h; exact ⟨x, h, rfl⟩

theorem subsetCode_valid (E : Finset HF) (s : Finset E) :
    IsSubsetCode E (subsetCode E s) := by
  intro p hp
  obtain ⟨x, _, rfl⟩ := (mem_subsetCode E s p).mp hp
  exact x.property

def decodeSubset (E : Finset HF) (s : HF) : Finset E := by
  classical
  exact Finset.univ.filter (fun x => mem x.val s)

@[simp] theorem mem_decodeSubset (E : Finset HF) (s : HF) (x : E) :
    x ∈ decodeSubset E s ↔ mem x.val s := by
  classical
  simp [decodeSubset]

@[simp] theorem decodeSubset_encode (E : Finset HF) (s : Finset E) :
    decodeSubset E (subsetCode E s) = s := by
  ext x; simp

@[simp] theorem encode_decodeSubset (E : Finset HF) (s : HF) (h : IsSubsetCode E s) :
    subsetCode E (decodeSubset E s) = s := by
  apply hf_ext
  intro p
  rw [mem_subsetCode]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (mem_decodeSubset E s x).mp hx
  · intro hp
    exact ⟨⟨p, h p hp⟩, (mem_decodeSubset E s _).mpr hp, rfl⟩

def subset_code_equiv (E : Finset HF) : Finset E ≃ {s // IsSubsetCode E s} where
  toFun s := ⟨subsetCode E s, subsetCode_valid E s⟩
  invFun s := decodeSubset E s.val
  left_inv := decodeSubset_encode E
  right_inv s := Subtype.ext (encode_decodeSubset E s.val s.property)

end
end D5.S0.History.Spacetime.FiniteGraphEncoding
