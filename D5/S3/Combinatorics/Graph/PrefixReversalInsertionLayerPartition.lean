/- GID: D5/S3/Combinatorics/Graph/PrefixReversalInsertionLayerPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversalInsertionLayerPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle, mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Complete native insertion layers over a directed base distinct from its reverse partition uniquely into independently specified child domains. -/
import D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversalInsertionLayerPartition

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement

universe u
variable {α : Type u} [DecidableEq α]

/-- Erase a set of selected labels from a genuine rotation-quotient circle. -/
def erase (S : Finset α) : Cycle α → Cycle α :=
  restrict (fun x => decide (x ∉ S))

theorem erase_coe (S : Finset α) (l : List α) :
    erase S (l : Cycle α) = (l.filter (fun x => decide (x ∉ S)) : Cycle α) := rfl

theorem erase_reverse (S : Finset α) (C : Cycle α) :
    erase S C.reverse = (erase S C).reverse :=
  restrict_reverse (fun x => decide (x ∉ S)) C

/-- Iterated restrictions depend only on the selected set, not on an insertion order. -/
theorem erase_union (S T : Finset α) (C : Cycle α) :
    erase S (erase T C) = erase (S ∪ T) C := by
  change restrict (fun x => decide (x ∉ S)) (restrict (fun x => decide (x ∉ T)) C) = _
  rw [restrict_restrict]
  have he : (fun x => decide (x ∉ S) && decide (x ∉ T)) =
      (fun x => decide (x ∉ S ∪ T)) := by
    funext x
    by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [hs, ht]
  rw [he]
  rfl

@[simp] theorem erase_idempotent (S : Finset α) (C : Cycle α) :
    erase S (erase S C) = erase S C := by
  rw [erase_union, Finset.union_self]

/-- The actual recursion step is deletion of the new label after the old restriction. -/
theorem erase_insert (S : Finset α) (x : α) (C : Cycle α) :
    erase (insert x S) C = delete x (erase S C) := by
  change restrict (fun y => decide (y ∉ insert x S)) C =
    restrict (fun y => decide (y ≠ x)) (restrict (fun y => decide (y ∉ S)) C)
  rw [restrict_restrict]
  have he : (fun y => decide (y ≠ x) && decide (y ∉ S)) =
      (fun y => decide (y ∉ insert x S)) := by
    funext y
    by_cases hx : y = x <;> by_cases hs : y ∈ S <;> simp [hx, hs]
  rw [he]

theorem delete_reverse (x : α) (C : Cycle α) :
    delete x C.reverse = (delete x C).reverse :=
  restrict_reverse (fun y => decide (y ≠ x)) C

theorem mem_erase (S : Finset α) (C : Cycle α) (x : α) :
    x ∈ erase S C ↔ x ∈ C ∧ x ∉ S := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change x ∈ ((l.filter (fun y => decide (y ∉ S))) : Cycle α) ↔
      x ∈ (l : Cycle α) ∧ x ∉ S
    simp only [Cycle.mem_coe_iff, List.mem_filter, decide_eq_true_eq]

theorem erase_nodup (S : Finset α) {C : Cycle α} (hC : C.Nodup) :
    (erase S C).Nodup := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change ((l.filter (fun y => decide (y ∉ S))) : Cycle α).Nodup
    exact Cycle.nodup_coe_iff.mpr ((Cycle.nodup_coe_iff.mp hC).filter _)

/-- The native layer is specified entirely by actual deletion, before a walk is chosen. -/
def Layer {m : ℕ} (S : Finset (Fin (m + 1))) (P : Cycle (Fin (m + 1)))
    (v : Configuration m) : Prop :=
  erase S (configurationCycle v) = P ∨
    erase S (configurationCycle v) = P.reverse

theorem configurationCircle_nodup {m : ℕ} (v : Configuration m) :
    (configurationCycle v).Nodup := by
  apply Cycle.nodup_coe_iff.mpr
  exact List.nodup_ofFn.mpr v.injective

theorem mem_configurationCircle {m : ℕ} (v : Configuration m)
    (x : Fin (m + 1)) : x ∈ configurationCycle v := by
  apply Cycle.mem_coe_iff.mpr
  exact List.mem_ofFn.mpr ⟨v.symm x, v.apply_symm_apply x⟩

theorem mem_nativeResidual {m : ℕ} (S : Finset (Fin (m + 1)))
    (v : Configuration m) (x : Fin (m + 1)) :
    x ∈ erase S (configurationCycle v) ↔ x ∉ S := by
  rw [mem_erase]
  exact ⟨fun h => h.2, fun h => ⟨mem_configurationCircle v x, h⟩⟩

/-- Every full nodup native-label circle is represented by an actual permutation. -/
theorem fullCircle_native {m : ℕ} {C : Cycle (Fin (m + 1))}
    (hn : C.Nodup) (hm : ∀ x, x ∈ C) :
    ∃ v : Configuration m, configurationCycle v = C := by
  induction C using Quotient.inductionOn with
  | _ l =>
    have hnl : l.Nodup := Cycle.nodup_coe_iff.mp hn
    have hml : ∀ x, x ∈ l := fun x => Cycle.mem_coe_iff.mp (hm x)
    have hset : l.toFinset = Finset.univ := by
      ext x
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact hml x
    have hlen : l.length = m + 1 := by
      have he := List.toFinset_card_of_nodup hnl
      rw [hset, Finset.card_univ, Fintype.card_fin] at he
      exact he.symm
    let v : Configuration m := (finCongr hlen.symm).trans
      (List.Nodup.getEquivOfForallMemList l hnl hml)
    refine ⟨v, ?_⟩
    have hv : List.ofFn v = l := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, hlen]
      · intro i hi hj
        simp only [List.getElem_ofFn]
        rfl
    exact congrArg (fun t : List (Fin (m + 1)) => (t : Cycle (Fin (m + 1)))) hv

/-- Every independent full residual circle has an actual native supplier.
    Append all erased labels once, then turn the resulting full list into a
    permutation. This establishes nonempty children without a candidate scan. -/
theorem nativeResidual_surjective {m : ℕ} (S : Finset (Fin (m + 1)))
    {D : Cycle (Fin (m + 1))} (hn : D.Nodup)
    (hm : ∀ y, y ∈ D ↔ y ∉ S) :
    ∃ v : Configuration m, erase S (configurationCycle v) = D := by
  classical
  induction D using Quotient.inductionOn with
  | _ l =>
    have hnl : l.Nodup := Cycle.nodup_coe_iff.mp hn
    have hml : ∀ y, y ∈ l ↔ y ∉ S := by
      intro y
      exact (Cycle.mem_coe_iff).symm.trans (hm y)
    have hdis : List.Disjoint S.toList l := by
      apply List.disjoint_left.mpr
      intro y hy hl
      exact (hml y).mp hl (Finset.mem_toList.mp hy)
    have hfull : ((S.toList ++ l : List (Fin (m + 1))) : Cycle (Fin (m + 1))).Nodup :=
      Cycle.nodup_coe_iff.mpr (S.nodup_toList.append hnl hdis)
    have hall : ∀ y : Fin (m + 1),
        y ∈ ((S.toList ++ l : List (Fin (m + 1))) : Cycle (Fin (m + 1))) := by
      intro y
      apply Cycle.mem_coe_iff.mpr
      by_cases hy : y ∈ S
      · exact List.mem_append.mpr (Or.inl (Finset.mem_toList.mpr hy))
      · exact List.mem_append.mpr (Or.inr ((hml y).mpr hy))
    obtain ⟨v, hv⟩ := fullCircle_native hfull hall
    refine ⟨v, ?_⟩
    rw [hv, erase_coe, List.filter_append]
    have hz : S.toList.filter (fun y => decide (y ∉ S)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      simp [Finset.mem_toList.mp hy]
    have hl : l.filter (fun y => decide (y ∉ S)) = l := by
      apply List.filter_eq_self.mpr
      intro y hy
      simp [(hml y).mp hy]
    rw [hz, hl, List.nil_append]
    rfl

/-- All admissible directed child circles, independently of any supplier scan.
    They contain exactly the labels outside S, with no repeats, and deleting the
    newly inserted label gives the specified positive base orientation. -/
def ChildCircle {m : ℕ} (S : Finset (Fin (m + 1))) (x : Fin (m + 1))
    (P : Cycle (Fin (m + 1))) :=
  {D : Cycle (Fin (m + 1)) //
    D.Nodup ∧ (∀ y, y ∈ D ↔ y ∉ S) ∧ erase S D = D ∧ delete x D = P}

/-- A child supplier domain is another independent deletion layer. -/
def ChildDomain {m : ℕ} {S : Finset (Fin (m + 1))} {x : Fin (m + 1)}
    {P : Cycle (Fin (m + 1))} (D : ChildCircle S x P)
    (v : Configuration m) : Prop := Layer S D.val v

theorem childCircle_not_reverse {m : ℕ} {S : Finset (Fin (m + 1))}
    {x : Fin (m + 1)} {P : Cycle (Fin (m + 1))} (hP : P ≠ P.reverse)
    (D E : ChildCircle S x P) : D.val ≠ E.val.reverse := by
  intro he
  have hd := D.property.2.2.2
  have he' := E.property.2.2.2
  apply hP
  calc
    P = delete x D.val := hd.symm
    _ = delete x E.val.reverse := congrArg (delete x) he
    _ = (delete x E.val).reverse := delete_reverse x E.val
    _ = P.reverse := congrArg Cycle.reverse he'

/-- Every child is wholly contained in the next parent layer. -/
theorem childDomain_parent {m : ℕ} {S : Finset (Fin (m + 1))}
    {x : Fin (m + 1)} {P : Cycle (Fin (m + 1))}
    (D : ChildCircle S x P) {v : Configuration m} (hv : ChildDomain D v) :
    Layer (insert x S) P v := by
  rcases hv with hv | hv
  · left
    rw [erase_insert, hv]
    exact D.property.2.2.2
  · right
    rw [erase_insert, hv, delete_reverse, D.property.2.2.2]

/-- The actual erased native circle, oriented by its deletion to P, is a child.
    The negative case reverses the *actual whole child circle*, not its gaps. -/
theorem childDomain_exists {m : ℕ} {S : Finset (Fin (m + 1))}
    {x : Fin (m + 1)} {P : Cycle (Fin (m + 1))}
    {v : Configuration m} (hv : Layer (insert x S) P v) :
    ∃ D : ChildCircle S x P, ChildDomain D v := by
  let C := erase S (configurationCycle v)
  have hn : C.Nodup := erase_nodup S (configurationCircle_nodup v)
  have hm : ∀ y, y ∈ C ↔ y ∉ S := mem_nativeResidual S v
  have hs : erase S C = C := erase_idempotent S (configurationCycle v)
  rcases hv with hp | hp
  · have hp' : delete x C = P := by
      simpa only [erase_insert] using hp
    exact ⟨⟨C, hn, hm, hs, hp'⟩, Or.inl rfl⟩
  · have hp' : delete x C = P.reverse := by
      simpa only [erase_insert] using hp
    have hn' : C.reverse.Nodup := Cycle.nodup_reverse_iff.mpr hn
    have hm' : ∀ y, y ∈ C.reverse ↔ y ∉ S := by
      intro y
      rw [Cycle.mem_reverse_iff, hm]
    have hs' : erase S C.reverse = C.reverse := by rw [erase_reverse, hs]
    have hd' : delete x C.reverse = P := by
      rw [delete_reverse, hp', Cycle.reverse_reverse]
    refine ⟨⟨C.reverse, hn', hm', hs', hd'⟩, Or.inr ?_⟩
    exact (Cycle.reverse_reverse C).symm

/-- Supplier domains for distinct positive child circles cannot share a vertex. -/
theorem childDomain_unique {m : ℕ} {S : Finset (Fin (m + 1))}
    {x : Fin (m + 1)} {P : Cycle (Fin (m + 1))} (hP : P ≠ P.reverse)
    (D E : ChildCircle S x P) {v : Configuration m}
    (hD : ChildDomain D v) (hE : ChildDomain E v) : D = E := by
  apply Subtype.ext
  rcases hD with hd | hd <;> rcases hE with he | he
  · exact hd.symm.trans he
  · exact (childCircle_not_reverse hP D E (hd.symm.trans he)).elim
  · exact (childCircle_not_reverse hP E D (he.symm.trans hd)).elim
  · simpa only [Cycle.reverse_reverse] using
      congrArg Cycle.reverse (hd.symm.trans he)

/-- Complete partition: existence and uniqueness concern *every* actual native vertex. -/
theorem insertionLayer_partition {m : ℕ} {S : Finset (Fin (m + 1))}
    {x : Fin (m + 1)} {P : Cycle (Fin (m + 1))} (hP : P ≠ P.reverse)
    (v : Configuration m) :
    Layer (insert x S) P v ↔ ∃! D : ChildCircle S x P, ChildDomain D v := by
  constructor
  · intro hv
    obtain ⟨D, hD⟩ := childDomain_exists hv
    exact ⟨D, hD, fun E hE => childDomain_unique hP E D hE hD⟩
  · rintro ⟨D, hD, _⟩
    exact childDomain_parent D hD

/-- The partition equivalence transports actual vertices and preserves their value.
    It does not assume anything about graphs, path states, or a recursive constructor. -/
noncomputable def insertionLayerEquiv {m : ℕ} {S : Finset (Fin (m + 1))}
    {x : Fin (m + 1)} {P : Cycle (Fin (m + 1))} (hP : P ≠ P.reverse) :
    {v : Configuration m // Layer (insert x S) P v} ≃
      (Σ D : ChildCircle S x P, {v : Configuration m // ChildDomain D v}) := by
  classical
  let pick (v : {v : Configuration m // Layer (insert x S) P v}) :=
    Classical.choose (((insertionLayer_partition hP v.val).mp v.property).exists)
  have pick_mem (v : {v : Configuration m // Layer (insert x S) P v}) :
      ChildDomain (pick v) v.val := Classical.choose_spec (((insertionLayer_partition hP v.val).mp v.property).exists)
  refine {
    toFun := fun v => ⟨pick v, ⟨v.val, pick_mem v⟩⟩
    invFun := fun dv => ⟨dv.2.val, childDomain_parent dv.1 dv.2.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro v
    exact Subtype.ext rfl
  · rintro ⟨D, v⟩
    have he : pick ⟨v.val, childDomain_parent D v.property⟩ = D :=
      childDomain_unique hP _ D (pick_mem _) v.property
    apply Sigma.ext he
    apply (Subtype.heq_iff_coe_eq (fun w => by
      change ChildDomain (pick ⟨v.val, childDomain_parent D v.property⟩) w ↔
        ChildDomain D w
      rw [he])).mpr
    rfl

#print axioms insertionLayer_partition
#print axioms insertionLayerEquiv

end D5.S3.Combinatorics.Graph.PrefixReversalInsertionLayerPartition
