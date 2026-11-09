/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogue
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supplied exact six-bit orthogonality catalogue and complete proof transfer. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/- Binary vectors are the six low bits of an integer. Addition is XOR;
   zero-containing XOR-closed sets are exactly the subspaces over F_2. -/
namespace BinaryOrthogonality

abbrev Vector := Fin 64

def add (x y : Vector) : Vector := ⟨(x.val ^^^ y.val) % 64, Nat.mod_lt _ (by decide)⟩

def dot (x y : Vector) : Nat :=
  ((List.range 6).map (fun i => (x.val / 2^i % 2) * (y.val / 2^i % 2))).sum % 2

theorem add_cancel (x y : Vector) : add (add x y) y = x := by
  revert x y
  decide +kernel

theorem dot_symm (x y : Vector) : dot x y = dot y x := by
  simp only [dot, Nat.mul_comm]

def IsSpace (U : Finset Vector) : Prop :=
  0 ∈ U ∧ (∀ x ∈ U, ∀ y ∈ U, add x y ∈ U)

abbrev Vertex := {U : Finset Vector // IsSpace U ∧ U ≠ {0}}

def graph : SimpleGraph Vertex where
  Adj U W := U ≠ W ∧ ∀ u ∈ U.val, ∀ w ∈ W.val, dot u w = 0
  symm := ⟨by
    intro U W h
    exact ⟨h.1.symm, fun w hw u hu => (dot_symm w u).trans (h.2 u hu w hw)⟩⟩
  loopless := ⟨fun U h => h.1 rfl⟩

def carrier (mask : Nat) : Finset Vector := Finset.univ.filter fun x => mask.testBit x.val

@[simp] theorem mem_carrier (m : Nat) (v : Vector) :
    v ∈ carrier m ↔ m.testBit v.val = true := by simp [carrier]

theorem zero_carrier : carrier 1 = {0} := by decide +kernel

theorem mask_subset {a b : Nat} (ha : a < 2^64) (h : carrier a ⊆ carrier b) :
    a &&& b = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 64
  · have hh := h (x := (⟨i, hi⟩ : Vector))
    simp only [mem_carrier] at hh
    cases hai : a.testBit i <;> simp_all
  · have hz : a.testBit i = false := Nat.testBit_lt_two_pow (by
      exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hz]

structure Catalogue where
  count : Nat
  positive : 0 < count
  masks : Array Nat
  perps : Array Nat
  colors : Array Nat
  extensions : Array Nat

def Catalogue.mask (D : Catalogue) (i : Fin D.count) := D.masks[i.val]!
def Catalogue.perp (D : Catalogue) (i : Fin D.count) := D.perps[i.val]!
def Catalogue.color (D : Catalogue) (i : Fin D.count) := D.colors[i.val]!
def Catalogue.space (D : Catalogue) (i : Fin D.count) := carrier (D.mask i)
def Catalogue.step (D : Catalogue) (i : Fin D.count) (v : Vector) : Fin D.count :=
  ⟨D.extensions[i.val * 64 + v.val]! % D.count, Nat.mod_lt _ D.positive⟩
def Catalogue.zero (D : Catalogue) : Fin D.count := ⟨0, D.positive⟩

def Catalogue.Covers (D : Catalogue) : Prop :=
  D.space D.zero = {0} ∧
  ∀ (i : Fin D.count) (v : Vector),
    D.space i ⊆ D.space (D.step i v) ∧ v ∈ D.space (D.step i v) ∧
    ∀ x ∈ D.space (D.step i v), x ∈ D.space i ∨ add x v ∈ D.space i

instance (D : Catalogue) : Decidable D.Covers := inferInstanceAs (Decidable (_ ∧ _))

theorem Catalogue.complete (D : Catalogue) (hc : D.Covers)
    (U : Finset Vector) (hU : IsSpace U) : ∃ i, D.space i = U := by
  have cover (S : Finset Vector) (hs : S ⊆ U) : ∃ i, S ⊆ D.space i ∧ D.space i ⊆ U := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨D.zero, Finset.empty_subset _, ?_⟩
      rw [hc.1]
      exact Finset.singleton_subset_iff.mpr hU.1
    | @insert v S hv ih =>
      obtain ⟨i, hsi, hiu⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hs)
      refine ⟨D.step i v, Finset.insert_subset (hc.2 i v).2.1
        (hsi.trans (hc.2 i v).1), ?_⟩
      intro x hx
      rcases (hc.2 i v).2.2 x hx with h | h
      · exact hiu h
      · have hh := hU.2 (add x v) (hiu h) v (hs (Finset.mem_insert_self _ _))
        simpa only [add_cancel] using hh
  obtain ⟨i, h1, h2⟩ := cover U (Finset.Subset.refl U)
  exact ⟨i, Finset.Subset.antisymm h2 h1⟩

def Catalogue.Proper (D : Catalogue) : Prop :=
  (∀ i, D.mask i < 2^64 ∧ D.color i < 15) ∧
  (∀ (i : Fin D.count) (v : Vector),
    v ∈ carrier (D.perp i) ↔ ∀ u ∈ D.space i, dot u v = 0) ∧
  (∀ i j, i ≠ D.zero → j ≠ D.zero → D.mask i ≠ D.mask j →
    D.mask j &&& D.perp i = D.mask j → D.color i ≠ D.color j)

instance (D : Catalogue) : Decidable D.Proper := inferInstanceAs (Decidable (_ ∧ _))

noncomputable def Catalogue.index (D : Catalogue) (hc : D.Covers) (U : Vertex) : Fin D.count :=
  (D.complete hc U.val U.property.1).choose

theorem Catalogue.index_spec (D : Catalogue) (hc : D.Covers) (U : Vertex) :
    D.space (D.index hc U) = U.val := (D.complete hc U.val U.property.1).choose_spec

theorem Catalogue.colorable (D : Catalogue) (hc : D.Covers) (hp : D.Proper) :
    graph.Colorable 15 := by
  classical
  let idx := D.index hc
  refine ⟨{ toFun := fun U => ⟨D.color (idx U), (hp.1 _).2⟩, map_rel' := ?_ }⟩
  intro U W hUW
  change (⟨D.color (idx U), (hp.1 _).2⟩ : Fin 15) ≠ ⟨D.color (idx W), (hp.1 _).2⟩
  intro h
  have nezero (V : Vertex) : idx V ≠ D.zero := by
    intro h
    apply V.property.2
    rw [← D.index_spec hc V]
    change D.space (idx V) = {0}
    rw [h, hc.1]
  have distinct : D.mask (idx U) ≠ D.mask (idx W) := by
    intro heq
    apply hUW.1
    apply Subtype.ext
    rw [← D.index_spec hc U, ← D.index_spec hc W]
    exact congrArg carrier heq
  have sub : D.space (idx W) ⊆ carrier (D.perp (idx U)) := by
    intro w hw
    apply (hp.2.1 _ w).mpr
    intro u hu
    rw [D.index_spec hc W] at hw
    rw [D.index_spec hc U] at hu
    exact hUW.2 u hu w hw
  exact hp.2.2 _ _ (nezero U) (nezero W) distinct
    (mask_subset (hp.1 _).1 sub) (congrArg Fin.val h)

end BinaryOrthogonality
