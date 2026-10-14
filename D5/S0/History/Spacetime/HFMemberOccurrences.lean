/- GID: D5/S0/History/Spacetime/HFMemberOccurrences
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/HFMemberOccurrences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual descending member paths count recursive HF mass in complete archive codes. -/

import D5.S0.History.Spacetime.ArchiveEncoding
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace D5.S0.History.Spacetime.HFMemberOccurrences

open HFEncoding ArchiveCarrier CoordinateEncoding SourceTreeEncoding
open ArchiveRecordEncoding ArchiveEncoding FiniteGraphEncoding
open scoped BigOperators
noncomputable section

private theorem memberWF : WellFounded mem := InvImage.wf toZF ZFSet.mem_wf

/-- The root and the finite sum over the original set's distinct members. -/
def mass : HF → Nat := memberWF.fix fun x rec =>
  1 + ∑ y : ↥(members x), rec y.val (mem_members.mp y.property)

theorem mass_eq (x : HF) : mass x = 1 + ∑ y : ↥(members x), mass y.val := by
  exact WellFounded.fix_eq memberWF _ x

/-- An empty list is the root; each listed set is an actual member of its predecessor. -/
def Descends : HF → List HF → Prop
  | _, [] => True
  | x, y :: p => mem y x ∧ Descends y p

def Occurrence (x : HF) := {p : List HF // Descends x p}

private def splitOccurrence (x : HF) :
    Occurrence x ≃ Unit ⊕ (Σ y : ↥(members x), Occurrence y.val) where
  toFun p := match p with
    | ⟨[], _⟩ => Sum.inl ()
    | ⟨y :: p, h⟩ => Sum.inr ⟨⟨y, mem_members.mpr h.1⟩, ⟨p, h.2⟩⟩
  invFun p := match p with
    | Sum.inl _ => ⟨[], trivial⟩
    | Sum.inr ⟨y, p⟩ => ⟨y.val :: p.val, mem_members.mp y.property, p.property⟩
  left_inv p := by rcases p with ⟨_ | ⟨y, p⟩, h⟩ <;> rfl
  right_inv p := by rcases p with ⟨⟨⟩⟩ | ⟨y, p⟩ <;> rfl

instance occurrenceFinite (x : HF) : Finite (Occurrence x) := by
  induction x using memberWF.induction with
  | h x ih =>
    let (y : ↥(members x)) : Finite (Occurrence y.val) :=
      ih y.val (mem_members.mp y.property)
    let (y : ↥(members x)) : Fintype (Occurrence y.val) := Fintype.ofFinite _
    exact Finite.of_equiv _ (splitOccurrence x).symm

theorem occurrence_card (x : HF) : Nat.card (Occurrence x) = mass x := by
  induction x using memberWF.induction with
  | h x ih =>
    let (y : ↥(members x)) : Fintype (Occurrence y.val) := Fintype.ofFinite _
    rw [Nat.card_congr (splitOccurrence x), Nat.card_sum, Nat.card_sigma, mass_eq]
    simp only [Nat.card_unique]
    congr 1
    exact Finset.sum_congr rfl fun y _ => ih y.val (mem_members.mp y.property)

private theorem mass_mem_le {x y : HF} (h : mem y x) : mass y ≤ mass x := by
  rw [mass_eq x]
  have hs : mass y ≤ ∑ z : ↥(members x), mass z.val :=
    Finset.single_le_sum (f := fun z : ↥(members x) => mass z.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ
      (⟨y, mem_members.mpr h⟩ : ↥(members x)))
  omega

open Classical in
private theorem members_insert (a b : HF) :
    members (insert a b) = Insert.insert a (members b) := by
  classical
  ext y
  simp

private theorem members_empty : members empty = ∅ := by
  ext y
  simp

private theorem mass_insert_of_not_mem (a b : HF) (h : ¬ mem a b) :
    mass (insert a b) = mass a + mass b := by
  classical
  rw [mass_eq, mass_eq b]
  simp only [Finset.sum_coe_sort, members_insert]
  rw [Finset.sum_insert (by simpa using h)]
  omega

private theorem natCode_zero : natCode 0 = empty := by
  apply toZF_injective
  simp

private theorem natCode_succ (n : Nat) : natCode (n + 1) = insert (natCode n) (natCode n) := by
  apply toZF_injective
  simp [Nat.cast_add, Ordinal.toZFSet_add_one]

private theorem natCode_not_mem_self (n : Nat) : ¬ mem (natCode n) (natCode n) := by
  simp [mem, Ordinal.toZFSet_mem_toZFSet_iff]

theorem mass_natCode (n : Nat) : mass (natCode n) = 2 ^ n := by
  induction n with
  | zero =>
    rw [natCode_zero, mass_eq, members_empty]
    simp
  | succ n ih =>
    rw [natCode_succ, mass_insert_of_not_mem _ _ (natCode_not_mem_self n), ih,
      pow_succ]
    omega

private theorem mass_pair_left (a b : HF) : mass a ≤ mass (pair a b) := by
  exact (mass_mem_le (by simp : mem a (insert a empty))).trans
    (mass_mem_le (by simp [pair] : mem (insert a empty) (pair a b)))

private theorem mass_pair_right (a b : HF) : mass b ≤ mass (pair a b) := by
  exact (mass_mem_le (by simp : mem b (insert a (insert b empty)))).trans
    (mass_mem_le (by simp [pair] : mem (insert a (insert b empty)) (pair a b)))

/-- Every archived leaf survives all fields of the original rich code, irrespective of masks. -/
theorem richCode_leaf_bound (x : Rich 3) (e : x.1.archive.Event) (n : Nat)
    (h : (x.1.archive.attributes e).source = FreeMagma.of n) :
    2 ^ n ≤ mass (richCode x) ∧
      2 ^ n ≤ Nat.card (Occurrence (richCode x)) := by
  have hs : mass (natCode n) ≤ mass (sourceCode (x.1.archive.attributes e).source) := by
    rw [h]
    exact mass_pair_right _ _
  have ha : mass (sourceCode (x.1.archive.attributes e).source) ≤
      mass (attributesCode (x.1.archive.attributes e)) := by
    change mass (sourceCode _) ≤ mass (pair _ (pair _ (pair _ (sourceCode _))))
    exact (mass_pair_right _ _).trans
      ((mass_pair_right _ _).trans (mass_pair_right _ _))
  have hg : mass (attributesCode (x.1.archive.attributes e)) ≤
      mass (archiveRecord x.1.archive).attributes := by
    exact (mass_pair_right _ _).trans (mass_mem_le
      ((mem_graphCode _ _ _ _).mpr ⟨e, rfl⟩))
  have ho : mass (archiveRecord x.1.archive).attributes ≤ mass (richCode x) := by
    change mass _ ≤ mass (pair (pair (pair _ (pair _ _)) _) _)
    exact (mass_pair_left _ _).trans ((mass_pair_right _ _).trans
      ((mass_pair_left _ _).trans (mass_pair_left _ _)))
  have hm : 2 ^ n ≤ mass (richCode x) := by
    rw [← mass_natCode]
    exact hs.trans (ha.trans (hg.trans ho))
  exact ⟨hm, (occurrence_card _).symm ▸ hm⟩

end
end D5.S0.History.Spacetime.HFMemberOccurrences
