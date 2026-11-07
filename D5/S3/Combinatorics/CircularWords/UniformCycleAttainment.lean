/- GID: D5/S3/Combinatorics/CircularWords/UniformCycleAttainment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/UniformCycleAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual rooted deletion fibres determine the full-carrier ambiguity count and a correct attaining history decoder. -/

import D5.S3.Combinatorics.CircularWords.CircularOrderCount
import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
import D5.S3.Combinatorics.CircularWords.PairedDeletionFiber
import D5.S3.Combinatorics.CircularWords.SingleDeletionFiberCount
import D5.S3.Combinatorics.CircularWords.ThreeSpecifiedDeletions
import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.UniformCycleAttainment

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
open D5.S3.Combinatorics.CircularWords.PairedDeletionFiber
open D5.S3.Combinatorics.CircularWords.SingleDeletionFiberCount
open D5.S3.Combinatorics.CircularWords.ThreeSpecifiedDeletions
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

universe u
variable {α : Type u} [DecidableEq α]

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Carrier (A : Finset α) := Finset (Cycle α)
def carrier (A : Finset α) : Carrier A := circles A

theorem mem_carrier_legal {A : Finset α} {C : Cycle α} (hC : C ∈ carrier A) :
    C.Nodup ∧ C.toFinset = A := by
  rcases Finset.mem_image.mp hC with ⟨w, hw, rfl⟩
  have hp : w.Perm A.toList := mem_orders.mp hw
  have hn : w.Nodup := hp.nodup_iff.mpr A.nodup_toList
  refine ⟨Cycle.nodup_coe_iff.mpr hn, ?_⟩
  change w.toFinset = A
  ext a
  simp only [List.mem_toFinset, hp.mem_iff, Finset.mem_toList]

theorem legal_mem_carrier {A : Finset α} {C : Cycle α}
    (hC : C.Nodup) (sC : C.toFinset = A) : C ∈ carrier A := by
  induction C using Quotient.inductionOn with
  | _ w =>
    have hn : w.Nodup := Cycle.nodup_coe_iff.mp hC
    have hs : w.toFinset = A := sC
    have hp : w.Perm A.toList := by
      apply (List.perm_ext_iff_of_nodup hn A.nodup_toList).mpr
      intro a
      have ha : a ∈ w.toFinset ↔ a ∈ A := by rw [hs]
      simpa only [List.mem_toFinset, Finset.mem_toList] using ha
    exact Finset.mem_image.mpr ⟨w, mem_orders.mpr hp, rfl⟩

theorem carrier_card (A : Finset α) (hA : A.Nonempty) :
    (carrier A).card = (A.card - 1).factorial := circles_card A hA

theorem carrier_nonempty {A : Finset α} (hA : A.Nonempty) :
    (carrier A).Nonempty := by
  apply Finset.card_pos.mp
  rw [carrier_card A hA]
  exact Nat.factorial_pos _

private theorem support_mem (C : Cycle α) (a : α) :
    a ∈ C.toFinset ↔ a ∈ C := by
  induction C using Quotient.inductionOn with
  | _ w => exact List.mem_toFinset

private theorem filter_absent {L : List α} {z : α} (hz : z ∉ L) :
    L.filter (fun a => decide (a ≠ z)) = L := by
  apply List.filter_eq_self.mpr
  intro a ha
  simp only [decide_eq_true_eq]
  exact fun e => hz (e ▸ ha)

/- This is an equality of lists, before taking the Cycle quotient. -/
theorem filter_rotate_root {z : α} {L : List α} (hz : z ∉ L)
    (j : Fin (z :: L).length) :
    ((z :: L).rotate j.val).filter (fun a => decide (a ≠ z)) =
      L.rotate (j.val - 1) := by
  rcases j with ⟨v, hv⟩
  cases v with
  | zero =>
    simpa only [List.rotate_zero, List.filter_cons, ne_eq, not_true_eq_false,
      decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_sub] using filter_absent hz
  | succ r =>
    have hr : r < L.length := by simp only [List.length_cons] at hv; omega
    have hzdrop : z ∉ L.drop r := by
      intro h
      apply hz
      have h' : z ∈ L.take r ++ L.drop r := List.mem_append.mpr (Or.inr h)
      simpa only [List.take_append_drop] using h'
    have hztake : z ∉ L.take r := by
      intro h
      apply hz
      have h' : z ∈ L.take r ++ L.drop r := List.mem_append.mpr (Or.inl h)
      simpa only [List.take_append_drop] using h'
    have hbound : r + 1 ≤ (z :: L).length := by simp only [List.length_cons]; omega
    rw [List.rotate_eq_drop_append_take hbound]
    simp only [List.drop_succ_cons, List.take_succ_cons, List.filter_append,
      List.filter_cons, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, filter_absent hzdrop,
      filter_absent hztake, Nat.add_sub_cancel]
    exact (List.rotate_eq_drop_append_take (Nat.le_of_lt hr)).symm

def secondGap (B : List α) (x z : α) (j : Fin B.length) : Cycle α :=
  delete z (gapCircle B x j)

def GapSecondLaw (B : List α) (x z : α) : Prop :=
  ∀ j k : Fin B.length,
    secondGap B x z j = secondGap B x z k ↔
      j.val = k.val ∨ (j.val = 0 ∧ k.val = 1) ∨ (j.val = 1 ∧ k.val = 0)

theorem secondGap_root_formula {x z : α} {L : List α}
    (hxz : x ≠ z) (hz : z ∉ L) (j : Fin (z :: L).length) :
    secondGap (z :: L) x z j = (x :: L.rotate (j.val - 1) : Cycle α) := by
  change (((x :: (z :: L).rotate j.val).filter
    (fun a => decide (a ≠ z))) : Cycle α) = _
  simp only [List.filter_cons, decide_eq_true hxz, ↓reduceIte,
    filter_rotate_root hz j]

theorem rooted_gap_second_law {x z : α} {L : List α}
    (hn : (z :: L).Nodup) (hL0 : L ≠ []) (hx : x ∉ z :: L) :
    GapSecondLaw (z :: L) x z := by
  have hxz : x ≠ z := fun e => hx (by simp [e])
  have hz : z ∉ L := (List.nodup_cons.mp hn).1
  have hLn : L.Nodup := hn.tail
  have hxL : x ∉ L := fun h => hx (List.mem_cons_of_mem z h)
  intro j k
  rw [secondGap_root_formula hxz hz j, secondGap_root_formula hxz hz k]
  have hj : j.val - 1 < L.length := by
    have h := j.isLt
    have hpos := List.length_pos_iff.mpr hL0
    simp only [List.length_cons] at h
    omega
  have hk : k.val - 1 < L.length := by
    have h := k.isLt
    have hpos := List.length_pos_iff.mpr hL0
    simp only [List.length_cons] at h
    omega
  have heq :
      (x :: L.rotate (j.val - 1) : Cycle α) = (x :: L.rotate (k.val - 1) : Cycle α) ↔
        j.val - 1 = k.val - 1 := by
    constructor
    · intro h
      have hanchor : (x :: L.rotate (j.val - 1)).Nodup :=
        List.nodup_cons.mpr ⟨by simpa only [List.mem_rotate] using hxL,
          List.nodup_rotate.mpr hLn⟩
      have hr := anchored_coe_injective hanchor h
      have hm := hLn.rotate_congr hL0 (j.val - 1) (k.val - 1) hr
      simpa only [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] using hm
    · intro h
      rw [h]
  rw [heq]
  omega

/- Root a legal residual at the surviving second label. -/
theorem legal_residual_root {A : Finset α} (hA : 4 ≤ A.card) (x z : A)
    (hxz : x.1 ≠ z.1) {B : Cycle α} (hB : B.Nodup)
    (sB : B.toFinset = A.erase x.1) :
    ∃ L : List α, B = (z.1 :: L : Cycle α) ∧ (z.1 :: L).Nodup ∧
      L ≠ [] ∧ x.1 ∉ z.1 :: L ∧ (z.1 :: L).toFinset = A.erase x.1 := by
  have hz : z.1 ∈ B := (support_mem B z.1).mp (by
    rw [sB]
    exact Finset.mem_erase.mpr ⟨Ne.symm hxz, z.property⟩)
  obtain ⟨L, hroot⟩ := rooted hz
  have hn : (z.1 :: L).Nodup := Cycle.nodup_coe_iff.mp (hroot ▸ hB)
  have hs : (z.1 :: L).toFinset = A.erase x.1 := by
    change (z.1 :: L : Cycle α).toFinset = _
    rw [← hroot, sB]
  have hlen : (z.1 :: L).length = A.card - 1 := by
    rw [← List.toFinset_card_of_nodup hn, hs, Finset.card_erase_of_mem x.property]
  have hL0 : L ≠ [] := by intro e; simp only [e, List.length_cons, List.length_nil] at hlen; omega
  have hx : x.1 ∉ z.1 :: L := by
    intro h
    have hm : x.1 ∈ A.erase x.1 := hs ▸ List.mem_toFinset.mpr h
    exact (Finset.mem_erase.mp hm).1 rfl
  exact ⟨L, hroot, hn, hL0, hx, hs⟩

/- Finite index fibres. No certificate is assumed by the final cycle theorem. -/
theorem slot_fiber_zero_card {B : List α} {x z : α} (hlen : 2 ≤ B.length)
    (law : GapSecondLaw B x z) :
    Nat.card {j : Fin B.length //
      secondGap B x z j = secondGap B x z ⟨0, by omega⟩} = 2 := by
  let j0 : Fin B.length := ⟨0, by omega⟩
  let j1 : Fin B.length := ⟨1, by omega⟩
  have h10 : secondGap B x z j1 = secondGap B x z j0 :=
    (law j1 j0).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  let a : {j : Fin B.length // secondGap B x z j = secondGap B x z j0} := ⟨j0, rfl⟩
  let b : {j : Fin B.length // secondGap B x z j = secondGap B x z j0} := ⟨j1, h10⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨a, b, ?_, ?_⟩
  · intro h
    have he := congrArg (fun t => t.val.val) h
    change 0 = 1 at he
    omega
  · ext j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have h := (law j.val j0).mp j.property
    rcases h with h | h | h
    · left; apply Subtype.ext; apply Fin.ext; exact h
    · left; apply Subtype.ext; apply Fin.ext; exact h.1
    · right; apply Subtype.ext; apply Fin.ext; exact h.1

theorem slot_fiber_other_card {B : List α} {x z : α} (hlen : 2 ≤ B.length)
    (law : GapSecondLaw B x z) (D : Cycle α)
    (hD : D ≠ secondGap B x z ⟨0, by omega⟩)
    (hreal : Nonempty {j : Fin B.length // secondGap B x z j = D}) :
    Nat.card {j : Fin B.length // secondGap B x z j = D} = 1 := by
  let j0 : Fin B.length := ⟨0, by omega⟩
  obtain ⟨j, hj⟩ := hreal
  have hjlarge : 1 < j.val := by
    by_contra h
    have he : secondGap B x z j = secondGap B x z j0 := by
      apply (law j j0).mpr
      have hj01 : j.val = 0 ∨ j.val = 1 := by omega
      rcases hj01 with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Or.inr ⟨h1, rfl⟩)
    exact hD (hj.symm.trans he)
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨j, hj⟩, ?_⟩
  intro k
  apply Subtype.ext
  apply Fin.ext
  have h := (law k.val j).mp (k.property.trans hj.symm)
  rcases h with h | h | h
  · exact h
  · omega
  · omega

abbrev FirstLift (A : Finset α) (x : A) (B : Cycle α) :=
  {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x.1 C = B}

theorem firstLift_card {A : Finset α} (hA : 3 ≤ A.card) (x : A)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x.1) :
    Nat.card (FirstLift A x B) = A.card - 1 :=
  deletion_fiber_card hA x.property hB sB

abbrev PairLift (A : Finset α) (x z : A) (B D : Cycle α) :=
  {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧
    delete x.1 C = B ∧ delete z.1 C = D}

/- Restrict the actual insertionEquiv, not a proxy set of gap objects. -/
def pairInsertionEquiv {A : Finset α} (x z : A) {W : List α}
    (hn : W.Nodup) (hW0 : W ≠ []) (hs : W.toFinset = A.erase x.1)
    (D : Cycle α) :
    {j : Fin W.length // secondGap W x.1 z.1 j = D} ≃
      PairLift A x z (W : Cycle α) D := by
  let e := insertionEquiv x.property hn hW0 hs
  let first (C : PairLift A x z (W : Cycle α) D) : FirstLift A x (W : Cycle α) :=
    ⟨C.val, C.property.1, C.property.2.1, C.property.2.2.1⟩
  refine
    { toFun := fun j => ⟨(e j.val).val, (e j.val).property.1,
        (e j.val).property.2.1, (e j.val).property.2.2, j.property⟩
      invFun := fun C => ⟨e.symm (first C), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change delete z.1 (e (e.symm (first C))).val = D
    rw [e.apply_symm_apply]
    exact C.property.2.2.2
  · intro j
    apply Subtype.ext
    exact e.symm_apply_apply j.val
  · intro C
    apply Subtype.ext
    change (e (e.symm (first C))).val = C.val
    exact congrArg (fun t : FirstLift A x (W : Cycle α) => t.val) (e.apply_symm_apply (first C))

instance pairLift_finite (A : Finset α) (x z : A) (B D : Cycle α) :
    Finite (PairLift A x z B D) := by
  let f : PairLift A x z B D → {C : Cycle α // C ∈ carrier A} :=
    fun C => ⟨C.val, legal_mem_carrier C.property.1 C.property.2.1⟩
  exact Finite.of_injective f (fun C E h => Subtype.ext
    (congrArg (fun t : {C : Cycle α // C ∈ carrier A} => t.val) h))

/- Actual finite-subtype upper bound from authenticated R1. It is valid even
for unrealized B,D, and does not assume that B is a legal residual. -/
theorem pairLift_atMostTwo {A : Finset α} (hA : 3 ≤ A.card) (x z : A)
    (hxz : x.1 ≠ z.1) (B D : Cycle α) : Nat.card (PairLift A x z B D) ≤ 2 := by
  by_cases hne : Nonempty (PairLift A x z B D)
  · let a := Classical.choice hne
    let f : PairLift A x z B D → Fin 2 := fun C => if C = a then 0 else 1
    have hf : Function.Injective f := by
      intro C E he
      by_cases hC : C = a
      · have hE : E = a := by
          by_contra hE
          simp [f, hC, hE] at he
        exact hC.trans hE.symm
      · have hE : E ≠ a := by
          intro hE
          simp [f, hC, hE] at he
        apply Subtype.ext
        apply pair_fiber_at_most_two hA x.property z.property hxz
          a.property.1 C.property.1 E.property.1
          a.property.2.1 C.property.2.1 E.property.2.1
          ⟨a.property.2.2.1.trans C.property.2.2.1.symm,
            a.property.2.2.2.trans C.property.2.2.2.symm⟩
          ⟨a.property.2.2.1.trans E.property.2.2.1.symm,
            a.property.2.2.2.trans E.property.2.2.2.symm⟩
        · intro h; exact hC (Subtype.ext h)
        · intro h; exact hE (Subtype.ext h)
    calc
      Nat.card (PairLift A x z B D) ≤ Nat.card (Fin 2) :=
        Nat.card_le_card_of_injective f hf
      _ = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  · haveI : IsEmpty (PairLift A x z B D) := ⟨fun C => hne ⟨C⟩⟩
    simp only [Nat.card_of_isEmpty, Nat.zero_le]

def PairBranchExact {A : Finset α} (hA : 4 ≤ A.card)
    (x z : A) (hxz : x.1 ≠ z.1) {B : Cycle α}
    (hB : B.Nodup) (sB : B.toFinset = A.erase x.1) : Prop :=
  ∃ D : Cycle α, Nat.card (PairLift A x z B D) = 2 ∧
    ∀ E : Cycle α, E ≠ D → Nonempty (PairLift A x z B E) →
      Nat.card (PairLift A x z B E) = 1

theorem pair_branch_exact {A : Finset α} (hA : 4 ≤ A.card) (x z : A)
    (hxz : x.1 ≠ z.1) {B : Cycle α} (hB : B.Nodup)
    (sB : B.toFinset = A.erase x.1) : PairBranchExact hA x z hxz hB sB := by
  obtain ⟨L, rfl, hn, hL0, hx, hs⟩ := legal_residual_root hA x z hxz hB sB
  have hlen : 2 ≤ (z.1 :: L).length := by
    have hpos := List.length_pos_iff.mpr hL0
    simp only [List.length_cons]
    omega
  have law := rooted_gap_second_law hn hL0 hx
  let j0 : Fin (z.1 :: L).length := ⟨0, by omega⟩
  let D := secondGap (z.1 :: L) x.1 z.1 j0
  refine ⟨D, ?_, ?_⟩
  · exact (Nat.card_congr (pairInsertionEquiv x z hn (by simp) hs D)).symm.trans
      (slot_fiber_zero_card hlen law)
  · intro E hE hreal
    have hidx : Nonempty {j : Fin (z.1 :: L).length //
        secondGap (z.1 :: L) x.1 z.1 j = E} := by
      obtain ⟨C⟩ := hreal
      exact ⟨(pairInsertionEquiv x z hn (by simp) hs E).symm C⟩
    exact (Nat.card_congr (pairInsertionEquiv x z hn (by simp) hs E)).symm.trans
      (slot_fiber_other_card hlen law E hE hidx)

/- Reused history-only construction, with the consumed draft's type/projection
errors repaired. Response is a family; History must be Hist (Response A). -/
abbrev Query (A : Finset α) := A
abbrev Response (A : Finset α) (_ : Query A) := Cycle α
abbrev History (A : Finset α) := Hist (Response A)

def read (A : Finset α) (x : Query A) (C : Cycle α) : Response A x := delete x.1 C
def consistent (A : Finset α) (h : History A) (C : Cycle α) : Prop :=
  ∀ a ∈ h, read A a.1 C = a.2
def candidateSet (A : Finset α) (h : History A) : Finset (Cycle α) :=
  (carrier A).filter (consistent A h)
def defaultCircle (A : Finset α) (hA : A.Nonempty) : Cycle α :=
  Classical.choose (carrier_nonempty hA)
def decode (A : Finset α) (hA : A.Nonempty) (h : History A) : Cycle α :=
  if hh : (candidateSet A h).Nonempty then Classical.choose hh else defaultCircle A hA
def pairHistory (A : Finset α) (x z : Query A) (bx bz : Cycle α) : History A :=
  [⟨x, bx⟩, ⟨z, bz⟩]
def attainingProtocol (A : Finset α) (x z y : Query A) :
    PassiveProtocol (Query A) (Response A) :=
  .query x (fun bx => .query z (fun bz =>
    if (candidateSet A (pairHistory A x z bx bz)).card = 1 then .stop
    else .query y (fun _ => .stop)))

theorem candidate_mem_of_carrier {A : Finset α} {h : History A} {C : Cycle α}
    (hC : C ∈ carrier A) (hh : ∀ a ∈ h, read A a.1 C = a.2) :
    C ∈ candidateSet A h := Finset.mem_filter.mpr ⟨hC, hh⟩

theorem mem_pair_candidates {A : Finset α} (x z : Query A)
    (B D C : Cycle α) : C ∈ candidateSet A (pairHistory A x z B D) ↔
      C ∈ carrier A ∧ delete x.1 C = B ∧ delete z.1 C = D := by
  rw [candidateSet, Finset.mem_filter]
  simp [consistent, pairHistory, read]

def pairLiftCandidateEquiv (A : Finset α) (x z : Query A) (B D : Cycle α) :
    PairLift A x z B D ≃ {C : Cycle α // C ∈ candidateSet A (pairHistory A x z B D)} :=
  { toFun := fun C => ⟨C.val, (mem_pair_candidates x z B D C.val).mpr
      ⟨legal_mem_carrier C.property.1 C.property.2.1, C.property.2.2⟩⟩
    invFun := fun C =>
      let h := (mem_pair_candidates x z B D C.val).mp C.property
      let hlegal := mem_carrier_legal h.1
      ⟨C.val, hlegal.1, hlegal.2, h.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem pair_candidates_card (A : Finset α) (x z : Query A) (B D : Cycle α) :
    (candidateSet A (pairHistory A x z B D)).card = Nat.card (PairLift A x z B D) := by
  exact ((Nat.card_congr (pairLiftCandidateEquiv A x z B D)).trans
    (Nat.card_eq_finsetCard _)).symm

theorem decoder_eq_of_candidate_singleton {A : Finset α} (hA : A.Nonempty)
    {h : History A} {C : Cycle α} (hs : candidateSet A h = {C})
    (hC : C ∈ candidateSet A h) : decode A hA h = C := by
  have hnon : (candidateSet A h).Nonempty := ⟨C, hC⟩
  simp only [decode, dif_pos hnon]
  have hc := Classical.choose_spec hnon
  have hc' : Classical.choose hnon ∈ ({C} : Finset (Cycle α)) := by
    simpa only [hs] using hc
  exact Finset.mem_singleton.mp hc'

theorem candidateSet_singleton_of_three {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.1 ≠ z.1) (hxy : x.1 ≠ y.1) (hzy : z.1 ≠ y.1)
    {C : Cycle α} (hC : C ∈ carrier A) (bx bz byy : Cycle α)
    (hc : read A x C = bx) (hz : read A z C = bz) (hy : read A y C = byy) :
    candidateSet A [⟨x,bx⟩,⟨z,bz⟩,⟨y,byy⟩] = {C} := by
  have hCL := mem_carrier_legal hC
  ext D
  constructor
  · intro hD
    have hDL := mem_carrier_legal (Finset.mem_filter.mp hD).1
    have hxD := (Finset.mem_filter.mp hD).2 ⟨x,bx⟩ (by simp)
    have hzD := (Finset.mem_filter.mp hD).2 ⟨z,bz⟩ (by simp)
    have hyD := (Finset.mem_filter.mp hD).2 ⟨y,byy⟩ (by simp)
    apply Finset.mem_singleton.mpr
    exact (reconstruct_three hA x.property z.property y.property hxz hxy hzy
      hCL.1 hDL.1 hCL.2 hDL.2
      (by simpa only [read] using hc.trans hxD.symm)
      (by simpa only [read] using hz.trans hzD.symm)
      (by simpa only [read] using hy.trans hyD.symm)).symm
  · intro hD
    have he : D = C := Finset.mem_singleton.mp hD
    subst D
    exact candidate_mem_of_carrier hC (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hc
      · exact hz
      · exact hy)

theorem pair_or_three_decode {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.1 ≠ z.1) (hxy : x.1 ≠ y.1) (hzy : z.1 ≠ y.1)
    {C : Cycle α} (hC : C ∈ carrier A) (bx bz byy : Cycle α)
    (hc : read A x C = bx) (hz : read A z C = bz) (hy : read A y C = byy) :
    ((candidateSet A (pairHistory A x z bx bz)).card = 1 →
      decode A (Finset.card_pos.mp (by omega)) (pairHistory A x z bx bz) = C) ∧
    decode A (Finset.card_pos.mp (by omega)) [⟨x,bx⟩,⟨z,bz⟩,⟨y,byy⟩] = C := by
  have hA0 : A.Nonempty := Finset.card_pos.mp (by omega)
  have hmem2 : C ∈ candidateSet A (pairHistory A x z bx bz) :=
    (mem_pair_candidates x z bx bz C).mpr ⟨hC, hc, hz⟩
  constructor
  · intro hpair
    obtain ⟨E, hE⟩ := Finset.card_eq_one.mp hpair
    have he : C = E := Finset.mem_singleton.mp (hE ▸ hmem2)
    have hs : candidateSet A (pairHistory A x z bx bz) = {C} := by simpa only [he] using hE
    exact decoder_eq_of_candidate_singleton hA0 hs hmem2
  · have hs := candidateSet_singleton_of_three hA x z y hxz hxy hzy hC bx bz byy hc hz hy
    exact decoder_eq_of_candidate_singleton hA0 hs (by rw [hs]; exact Finset.mem_singleton_self C)

theorem attainingProtocol_run_length {A : Finset α} (x z y : Query A) (C : Cycle α) :
    (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length =
      if (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 1
        then 2 else 3 := by
  by_cases h : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 1
  · simp [attainingProtocol, runPassiveProtocol, h]
  · simp [attainingProtocol, runPassiveProtocol, h]

theorem attainingProtocol_correct {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.1 ≠ z.1) (hxy : x.1 ≠ y.1) (hzy : z.1 ≠ y.1)
    {C : Cycle α} (hC : C ∈ carrier A) :
    decode A (Finset.card_pos.mp (by omega))
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C) = C := by
  have hd := pair_or_three_decode hA x z y hxz hxy hzy hC
    (read A x C) (read A z C) (read A y C) rfl rfl rfl
  by_cases hp : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 1
  · simp only [attainingProtocol, runPassiveProtocol, if_pos hp]
    exact hd.1 hp
  · simpa only [attainingProtocol, runPassiveProtocol, if_neg hp] using hd.2

/- Full carrier partition. Every legal residual is realized by insertion. -/
theorem delete_legal {A : Finset α} {C : Cycle α}
    (hC : C.Nodup) (sC : C.toFinset = A) (x : α) :
    (delete x C).Nodup ∧ (delete x C).toFinset = A.erase x := by
  induction C using Quotient.inductionOn with
  | _ W =>
    have hn : W.Nodup := Cycle.nodup_coe_iff.mp hC
    have hs : W.toFinset = A := sC
    constructor
    · exact Cycle.nodup_coe_iff.mpr (hn.filter (fun a => decide (a ≠ x)))
    · change (W.filter (fun a => decide (a ≠ x))).toFinset = A.erase x
      rw [← hs]
      ext a
      simp [and_comm]

theorem every_first_residual_realized {A : Finset α} (hA : 3 ≤ A.card) (x : A)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x.1) :
    ∃ C ∈ carrier A, delete x.1 C = B := by
  induction B using Quotient.inductionOn with
  | _ W =>
    have hn : W.Nodup := Cycle.nodup_coe_iff.mp hB
    have hs : W.toFinset = A.erase x.1 := sB
    have hlen : W.length = A.card - 1 := by
      rw [← List.toFinset_card_of_nodup hn, hs, Finset.card_erase_of_mem x.property]
    have hW0 : W ≠ [] := by intro e; simp only [e, List.length_nil] at hlen; omega
    let j : Fin W.length := ⟨0, by omega⟩
    let C := insertionEquiv x.property hn hW0 hs j
    exact ⟨C.val, legal_mem_carrier C.property.1 C.property.2.1, C.property.2.2⟩

theorem first_residual_image {A : Finset α} (hA : 3 ≤ A.card) (x : A) :
    (carrier A).image (delete x.1) = carrier (A.erase x.1) := by
  ext B
  constructor
  · rintro h
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp h
    have hL := mem_carrier_legal hC
    have hd := delete_legal hL.1 hL.2 x.1
    exact legal_mem_carrier hd.1 hd.2
  · intro hB
    have hL := mem_carrier_legal hB
    obtain ⟨C, hC, hd⟩ := every_first_residual_realized hA x hL.1 hL.2
    exact Finset.mem_image.mpr ⟨C, hC, hd⟩

def ambiguous (A : Finset α) (x z : Query A) : Finset (Cycle α) :=
  (carrier A).filter (fun C =>
    (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 2)

theorem ambiguous_subset (A : Finset α) (x z : Query A) :
    ambiguous A x z ⊆ carrier A := Finset.filter_subset _ _

theorem ambiguous_first_fiber_card {A : Finset α} (hA : 4 ≤ A.card) (x z : Query A)
    (hxz : x.1 ≠ z.1) {B : Cycle α} (hB : B.Nodup)
    (sB : B.toFinset = A.erase x.1) :
    ((ambiguous A x z).filter (fun C => delete x.1 C = B)).card = 2 := by
  obtain ⟨D, hD, hother⟩ := pair_branch_exact hA x z hxz hB sB
  have hset : (ambiguous A x z).filter (fun C => delete x.1 C = B) =
      candidateSet A (pairHistory A x z B D) := by
    ext C
    constructor
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hu, hxC⟩
      rcases Finset.mem_filter.mp hu with ⟨hC, htwo⟩
      have hL := mem_carrier_legal hC
      have hzC : delete z.1 C = D := by
        by_contra hzC
        have hone := hother (delete z.1 C) hzC
          ⟨⟨C, hL.1, hL.2, hxC, rfl⟩⟩
        have hc : (candidateSet A (pairHistory A x z
            (read A x C) (read A z C))).card = 1 := by
          change (candidateSet A (pairHistory A x z (delete x.1 C) (delete z.1 C))).card = 1
          rw [hxC, pair_candidates_card, hone]
        omega
      exact (mem_pair_candidates x z B D C).mpr ⟨hC, hxC, hzC⟩
    · intro h
      rcases (mem_pair_candidates x z B D C).mp h with ⟨hC, hxC, hzC⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hC, ?_⟩, hxC⟩
      change (candidateSet A (pairHistory A x z (delete x.1 C) (delete z.1 C))).card = 2
      rw [hxC, hzC, pair_candidates_card, hD]
  rw [hset, pair_candidates_card, hD]

theorem residual_carrier_card {A : Finset α} (hA : 3 ≤ A.card) (x : A) :
    (carrier (A.erase x.1)).card = (A.card - 2).factorial := by
  have hc : (A.erase x.1).card = A.card - 1 := Finset.card_erase_of_mem x.property
  have hnon : (A.erase x.1).Nonempty := Finset.card_pos.mp (by omega)
  rw [carrier_card _ hnon, hc]
  congr 1

theorem ambiguous_card {A : Finset α} (hA : 4 ≤ A.card) (x z : Query A)
    (hxz : x.1 ≠ z.1) : (ambiguous A x z).card = 2 * (A.card - 2).factorial := by
  have hmaps : ((ambiguous A x z : Finset (Cycle α)) : Set (Cycle α)).MapsTo
      (delete x.1) (carrier (A.erase x.1)) := by
    intro C hC
    have hL := mem_carrier_legal (ambiguous_subset A x z hC)
    have hd := delete_legal hL.1 hL.2 x.1
    exact legal_mem_carrier hd.1 hd.2
  calc
    (ambiguous A x z).card = ∑ B ∈ carrier (A.erase x.1),
        ((ambiguous A x z).filter (fun C => delete x.1 C = B)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ _B ∈ carrier (A.erase x.1), 2 := by
      apply Finset.sum_congr rfl
      intro B hB
      have hL := mem_carrier_legal hB
      exact ambiguous_first_fiber_card hA x z hxz hL.1 hL.2
    _ = 2 * (A.card - 2).factorial := by
      simp [residual_carrier_card (by omega : 3 ≤ A.card) x, Nat.mul_comm]

def BranchCountCertificate (A : Finset α) (x z : Query A) : Prop :=
  ∃ n : Nat, n = A.card ∧ (carrier A).card = (n - 1).factorial ∧
    ∃ U : Finset (Cycle α), U ⊆ carrier A ∧ U.card = 2 * (n - 2).factorial ∧
      (∀ C ∈ carrier A,
        (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card ≤ 2) ∧
      (∀ C ∈ carrier A,
        ((candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 2 ↔ C ∈ U))

theorem branch_count_certificate {A : Finset α} (hA : 4 ≤ A.card) (x z : Query A)
    (hxz : x.1 ≠ z.1) : BranchCountCertificate A x z := by
  refine ⟨A.card, rfl, carrier_card A (Finset.card_pos.mp (by omega)),
    ambiguous A x z, ambiguous_subset A x z, ambiguous_card hA x z hxz, ?_, ?_⟩
  · intro C _
    rw [pair_candidates_card]
    exact pairLift_atMostTwo (A := A) (by omega) x z hxz (read A x C) (read A z C)
  · intro C hC
    simp only [ambiguous, Finset.mem_filter, hC, true_and]

theorem third_query_iff_ambiguous {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.1 ≠ z.1) {C : Cycle α} (hC : C ∈ carrier A) :
    (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length = 3 ↔
      C ∈ ambiguous A x z := by
  have hle : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card ≤ 2 := by
    rw [pair_candidates_card]
    exact pairLift_atMostTwo (A := A) (by omega) x z hxz _ _
  have hmem : C ∈ candidateSet A (pairHistory A x z (read A x C) (read A z C)) :=
    (mem_pair_candidates x z _ _ C).mpr ⟨hC, rfl, rfl⟩
  have hpos := Finset.card_pos.mpr ⟨C, hmem⟩
  rw [attainingProtocol_run_length]
  simp only [ambiguous, Finset.mem_filter, hC, true_and]
  split_ifs <;> omega

theorem third_query_count {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.1 ≠ z.1) :
    ((carrier A).filter (fun C =>
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length = 3)).card =
        2 * (A.card - 2).factorial := by
  have hs : (carrier A).filter (fun C =>
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length = 3) =
        ambiguous A x z := by
    ext C
    constructor
    · intro h
      have hc := Finset.mem_filter.mp h
      exact (third_query_iff_ambiguous hA x z y hxz hc.1).mp hc.2
    · intro h
      have hc := ambiguous_subset A x z h
      exact Finset.mem_filter.mpr ⟨hc, (third_query_iff_ambiguous hA x z y hxz hc).mpr h⟩
  rw [hs]
  exact ambiguous_card hA x z hxz

/- An explicit recurrence and positive factors are needed before field algebra. -/
theorem factorial_ratio_mean (n : Nat) (hn : 4 ≤ n) :
    ((2 * (n - 1).factorial + 2 * (n - 2).factorial : Nat) : ℚ) /
      ((n - 1).factorial : ℚ) = 2 + 2 / (n - 1 : ℚ) := by
  have hpred : n - 1 = (n - 2) + 1 := by omega
  have hf : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
    calc
      (n - 1).factorial = ((n - 2) + 1).factorial := congrArg Nat.factorial hpred
      _ = ((n - 2) + 1) * (n - 2).factorial := Nat.factorial_succ _
      _ = (n - 1) * (n - 2).factorial := by rw [← hpred]
  have hnp : 0 < n - 1 := by omega
  have hfp : 0 < (n - 2).factorial := Nat.factorial_pos _
  have hnq : ((n - 1 : Nat) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnp)
  have hfq : ((n - 2).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hfp)
  have hfr : ((n - 1).factorial : ℚ) =
      ((n - 1 : Nat) : ℚ) * ((n - 2).factorial : ℚ) := by exact_mod_cast hf
  have hcast : ((n - 1 : Nat) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [← hcast]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hfr]
  field_simp [hnq, hfq] <;> ring

theorem exact_mean_from_branch_certificate {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hcost : BranchCountCertificate A x z) :
    ((∑ C ∈ carrier A,
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length : Nat) : ℚ) /
      ((carrier A).card : ℚ) = 2 + 2 / (A.card - 1 : ℚ) := by
  rcases hcost with ⟨n, rfl, hcard, U, hUsub, hUcard, hAtMost, hU⟩
  have hlen (C : Cycle α) (hC : C ∈ carrier A) :
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length =
        2 + if C ∈ U then 1 else 0 := by
    rw [attainingProtocol_run_length]
    by_cases hu : C ∈ U
    · have hc2 := (hU C hC).mpr hu
      simp [hc2, hu]
    · have hc2 : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card ≠ 2 :=
        fun h => hu ((hU C hC).mp h)
      have hmem : C ∈ candidateSet A (pairHistory A x z (read A x C) (read A z C)) :=
        (mem_pair_candidates x z _ _ C).mpr ⟨hC, rfl, rfl⟩
      have hpos := Finset.card_pos.mpr ⟨C, hmem⟩
      have hle := hAtMost C hC
      have hc1 : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 1 := by omega
      simp [hc1, hu]
  have hfilter : (carrier A).filter (fun C => C ∈ U) = U := by
    ext C
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hUsub h, h⟩⟩
  have hind : (∑ C ∈ carrier A, if C ∈ U then 1 else 0 : Nat) = U.card := by
    rw [← Finset.sum_filter]
    rw [hfilter]
    simp
  have hsum : (∑ C ∈ carrier A,
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length : Nat) =
        2 * (carrier A).card + U.card := by
    calc
      _ = ∑ C ∈ carrier A, (2 + if C ∈ U then 1 else 0) :=
        Finset.sum_congr rfl (fun C hC => hlen C hC)
      _ = _ := by rw [Finset.sum_add_distrib, hind]; simp [Nat.mul_comm]
  simp only [hsum, hcard, hUcard]
  exact factorial_ratio_mean A.card hA

/- Unconditional upper/attainment result on the full actual carrier. The lower-bound theorem is proved in the separate actual-model transport module. -/
theorem actual_cycle_attaining_mean {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.1 ≠ z.1) :
    ((∑ C ∈ carrier A,
      (runPassiveProtocol (read A) (attainingProtocol A x z y) C).length : Nat) : ℚ) /
      ((carrier A).card : ℚ) = 2 + 2 / (A.card - 1 : ℚ) :=
  exact_mean_from_branch_certificate hA x z y (branch_count_certificate hA x z hxz)



/-- An explicit full-history policy implementing the finite attaining tree.
Its terminal label is the entire observed history, which the decoder consumes. -/
def attainingPolicy (A : Finset α) (x z y : Query A) (h : History A) :
    Sum (Query A) (History A) :=
  if h.length = 0 then .inl x
  else if h.length = 1 then .inl z
  else if h.length = 2 ∧ (candidateSet A h).card ≠ 1 then .inl y
  else .inr h

/-- Four units of fuel suffice for the actual three-query-or-earlier run,
including its terminal action. No hidden state enters the policy. -/
theorem attainingPolicy_execute (A : Finset α) (x z y : Query A) (C : Cycle α) :
    execute (read A) (attainingPolicy A x z y) 4 [] C =
      some (runPassiveProtocol (read A) (attainingProtocol A x z y) C,
        runPassiveProtocol (read A) (attainingProtocol A x z y) C) := by
  by_cases hp : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 1
  · simp only [attainingProtocol,runPassiveProtocol,if_pos hp]
    simpa [execute,attainingPolicy,pairHistory] using (show
      execute (read A) (attainingPolicy A x z y) 4 [] C =
      some ([⟨x,read A x C⟩,⟨z,read A z C⟩], [⟨x,read A x C⟩,⟨z,read A z C⟩]) from by
        simp [execute,attainingPolicy,show (candidateSet A
          [⟨x,read A x C⟩,⟨z,read A z C⟩]).card = 1 from hp])
  · simp only [attainingProtocol,runPassiveProtocol,if_neg hp]
    simpa [execute,attainingPolicy,pairHistory] using (show
      execute (read A) (attainingPolicy A x z y) 4 [] C =
      some ([⟨x,read A x C⟩,⟨z,read A z C⟩,⟨y,read A y C⟩],
        [⟨x,read A x C⟩,⟨z,read A z C⟩,⟨y,read A y C⟩]) from by
        simp [execute,attainingPolicy,show (candidateSet A
          [⟨x,read A x C⟩,⟨z,read A z C⟩]).card ≠ 1 from hp])

end
end D5.S3.Combinatorics.CircularWords.UniformCycleAttainment
