/- GID: D5/S3/Combinatorics/PriorityLattice/IdealCompression
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/IdealCompression
   mirror-E: none(waiver:general-priority-lattice-counting)
   anchors: []
   utility: none
   digest: Priority-forest interval structure and counting. -/

/-
admission_basis: escape-witness
escape_witness: IntervalForest.idealCodeOrderIso
The compression constructs the closed-support correspondence using no_skipped_root to certify the interval closure of restricted and reconstructed supports.
Direct frozen dependencies: none; direct D5 dependencies are supplied by this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14955
Proof shapes expand all same-delivery declarations and apply the upstream-only bypass test.
IntervalForest.ClosedSupport: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
IntervalForest.restrictSupport: proof_shape: content
IntervalForest.restrictSupport_parent: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.restrictSupport_support
IntervalForest.restrictSupport_le: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.idealSupportOrderIso
IntervalForest.restrictSupport_support: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.idealSupportOrderIso
IntervalForest.support_closed: proof_shape: content
IntervalForest.support_le_iff_below: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.idealSupportOrderIso
IntervalForest.idealSupportOrderIso: proof_shape: content
coeIicOrderIso: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.idealCodeOrderIso
CodeClosed: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
codeClosedDecidable: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card1
IntervalForest.supportParent: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.compressCode_relation
IntervalForest.supportParent_spec: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.firstNeeded
IntervalForest.firstNeeded: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.compressCode_relation
IntervalForest.firstNeeded_le: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.firstIndex_le
IntervalForest.firstNeeded_mem: proof_shape: content
IntervalForest.firstIndex: proof_shape: content
IntervalForest.firstIndex_le: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.compressCode
IntervalForest.compressCode: proof_shape: content
IntervalForest.compressCode_relation: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.indices_support_closed
IntervalForest.supportToIndices: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
IntervalForest.mem_supportToIndices: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
IntervalForest.indicesToSupport: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
IntervalForest.mem_indicesToSupport: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
IntervalForest.support_indices_closed: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
IntervalForest.indices_support_closed: proof_shape: content
IntervalForest.support_indices_inverse: proof_shape: bind-only; consumer: IdealCompression.IntervalForest.closedSupportCodeOrderIso
IntervalForest.closedSupportCodeOrderIso: proof_shape: content
IntervalForest.idealCodeOrderIso: proof_shape: content
SmallCases.p1: proof_shape: bind-only; consumer: IdealCompression.SmallCases.card_one
SmallCases.a2: proof_shape: content
SmallCases.b2: proof_shape: content
SmallCases.s2: proof_shape: content
SmallCases.c2: proof_shape: content
SmallCases.parent_one_cases: proof_shape: bind-only; consumer: IdealCompression.SmallCases.forests_one
SmallCases.forests_one: proof_shape: bind-only; consumer: IdealCompression.SmallCases.forestOneFintype
SmallCases.forests_two: proof_shape: content
SmallCases.forestOneFintype: proof_shape: bind-only; consumer: IdealCompression.SmallCases.card_one
SmallCases.forestTwoFintype: proof_shape: content
SmallCases.card_one: proof_shape: bind-only; consumer: IdealCompression.pi_one_card
SmallCases.card_two: proof_shape: content
pi_zero_card: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi0Equiv
pi_one_card: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi1Equiv
pi_two_card: proof_shape: content
SmallIdealCodes.t1: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card1
SmallIdealCodes.t20: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card20
SmallIdealCodes.t21: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card21
SmallIdealCodes.t3: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card3
SmallIdealCodes.code_one: proof_shape: bind-only; consumer: PrincipalIdeals.ideal_zero_code
SmallIdealCodes.code_two: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card_two_iff
SmallIdealCodes.code_three: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card_three_iff
SmallIdealCodes.card1: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.code1Equiv
SmallIdealCodes.card20: proof_shape: content
SmallIdealCodes.card21: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.card_two_iff
SmallIdealCodes.card3: proof_shape: content
SmallIdealCodes.card_two_iff: proof_shape: content
SmallIdealCodes.card_three_iff: proof_shape: content
codeClosed_image: proof_shape: bind-only; consumer: IdealCompression.codePermutationOrderIso
codePermutationOrderIso: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.twoTripleModelsIso
SmallIdealCodes.cycle3: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.twoTripleModelsIso
SmallIdealCodes.twoTripleModelsIso: proof_shape: bind-only; consumer: PrincipalIdeals.ideal_two_code_iff
SmallIdealCodes.code1Enum: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.code1Enum_injective
SmallIdealCodes.code2Enum: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.code2Enum_injective
SmallIdealCodes.code3Enum: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.code3Enum_injective
SmallIdealCodes.code1Enum_injective: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.code1Equiv
SmallIdealCodes.code2Enum_injective: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.code2Equiv
SmallIdealCodes.code3Enum_injective: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.code3Equiv
SmallIdealCodes.code1Equiv: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi0CodeOrderIso
SmallIdealCodes.code2Equiv: proof_shape: content
SmallIdealCodes.code3Equiv: proof_shape: content
SmallIdealCodes.pi0Enum: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi0CodeOrderIso
SmallIdealCodes.pi1Enum: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi1CodeOrderIso
SmallIdealCodes.pi2Enum: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi2CodeOrderIso
SmallIdealCodes.pi0Enum_injective: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi0Equiv
SmallIdealCodes.pi1Enum_injective: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi1Equiv
SmallIdealCodes.pi2Enum_injective: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi2Equiv
SmallIdealCodes.pi0Equiv: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi0CodeOrderIso
SmallIdealCodes.pi1Equiv: proof_shape: bind-only; consumer: IdealCompression.SmallIdealCodes.pi1CodeOrderIso
SmallIdealCodes.pi2Equiv: proof_shape: content
SmallIdealCodes.pi0CodeOrderIso: proof_shape: bind-only; consumer: PrincipalIdeals.ideal_zero_code
SmallIdealCodes.pi1CodeOrderIso: proof_shape: content
SmallIdealCodes.pi2CodeOrderIso: proof_shape: content
IntervalForest.compressCode_self_iff: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.code_one_step_implies_one_long
IntervalForest.support_adjacent_of_needed: proof_shape: content
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import D5.S3.Combinatorics.PriorityLattice.ForestCovers
import Mathlib.Data.Finset.Sort

open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.ForestCovers
open D5.S3.Combinatorics.PriorityLattice.ForestCovers.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression.IntervalForest
end D5.S3.Combinatorics.PriorityLattice.IdealCompression.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.IdealCompression.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression
namespace IntervalForest

variable {n : Nat}

private def ClosedSupport (P : IntervalForest n) (s : Finset (Fin (n+1))) : Prop :=
  s ⊆ (support P) ∧ forall v, v ∈ s -> forall p, P.parent v = some p ->
    forall w, p < w -> w <= v -> w ∈ s

private noncomputable def restrictSupport (P : IntervalForest n) (s : Finset (Fin (n+1)))
    (hs : (ClosedSupport P) s) : IntervalForest n := by
  classical
  exact forestOfLocal (fun v => if v ∈ s then P.parent v else none)
    (by
      intro v p hp
      by_cases hv : v ∈ s
      · simp only [hv,ite_true] at hp
        exact P.increasing v p hp
      · simp only [hv,ite_false] at hp
        cases hp)
    (by
      intro v p w hp hpw hwv
      by_cases hv : v ∈ s
      · simp only [hv,ite_true] at hp
        have hw := hs.2 v hv p hp w hpw hwv
        simp only [hw,ite_true]
        exact (mem_support P w).mp (hs.1 hw)
      · simp only [hv,ite_false] at hp
        cases hp)

@[simp] private theorem restrictSupport_parent (P : IntervalForest n) (s : Finset (Fin (n+1)))
    (hs : (ClosedSupport P) s) (v : Fin (n+1)) :
    ((restrictSupport P) s hs).parent v = if v ∈ s then P.parent v else none := rfl

private theorem restrictSupport_le (P : IntervalForest n) (s : Finset (Fin (n+1)))
    (hs : (ClosedSupport P) s) : (restrictSupport P) s hs <= P := by
  classical
  rw [le_iff_parent]
  intro v p hp
  by_cases hv : v ∈ s
  · simpa only [restrictSupport_parent,hv,ite_true] using hp
  · simp only [restrictSupport_parent,hv,ite_false] at hp
    cases hp

@[simp] private theorem restrictSupport_support (P : IntervalForest n) (s : Finset (Fin (n+1)))
    (hs : (ClosedSupport P) s) : (support ((restrictSupport P) s hs)) = s := by
  classical
  ext v
  rw [mem_support,restrictSupport_parent]
  by_cases hv : v ∈ s
  · simpa only [hv,ite_true,iff_true] using (mem_support P v).mp (hs.1 hv)
  · simp only [hv,ite_false,ne_eq,not_true_eq_false]

private theorem support_closed {P Q : IntervalForest n} (hQP : Q <= P) : (ClosedSupport P) (support Q) := by
  refine ⟨support_mono hQP,?_⟩
  intro v hv p hp w hpw hwv
  obtain ⟨q,hq⟩ := Option.ne_none_iff_exists'.mp ((mem_support Q v).mp hv)
  have hqp := (le_iff_parent Q P).mp hQP v q hq
  have he : q = p := Option.some.inj (hqp.symm.trans hp)
  subst q
  exact (mem_support Q w).mpr (Q.no_skipped_root hq hpw hwv)

private theorem support_le_iff_below {P Q R : IntervalForest n} (hQP : Q <= P) (hRP : R <= P) :
    (support Q) ⊆ (support R) ↔ Q <= R := by
  constructor
  · intro hs
    rw [le_iff_parent]
    intro v p hp
    have hv := hs ((mem_support Q v).mpr (by simp [hp]))
    obtain ⟨q,hq⟩ := Option.ne_none_iff_exists'.mp ((mem_support R v).mp hv)
    have hPp := (le_iff_parent Q P).mp hQP v p hp
    have hPq := (le_iff_parent R P).mp hRP v q hq
    have he : q = p := Option.some.inj (hPq.symm.trans hPp)
    simpa only [he] using hq
  · exact support_mono

private noncomputable def idealSupportOrderIso (P : IntervalForest n) :
    Set.Iic P ≃o {s : Finset (Fin (n+1)) // (ClosedSupport P) s} where
  toFun Q := ⟨(support Q.val),support_closed Q.property⟩
  invFun s := ⟨(restrictSupport P) s.val s.property,(restrictSupport_le P) s.val s.property⟩
  left_inv Q := by
    apply Subtype.ext
    exact eq_of_same_support_below
      ((restrictSupport_le P) (support Q.val) (support_closed Q.property)) Q.property
      (restrictSupport_support P (support Q.val) (support_closed Q.property))
  right_inv s := by apply Subtype.ext; exact restrictSupport_support P s.val s.property
  map_rel_iff' := by intro Q R; exact support_le_iff_below Q.property R.property

end IntervalForest

private noncomputable def coeIicOrderIso {A : Type*} [PartialOrder A] (a : A) :
    Set.Iic a ≃o Set.Iic (a : WithTop A) := by
  let e : Set.Iic a ≃ Set.Iic (a : WithTop A) := Equiv.ofBijective
    (fun x => ⟨(x.val : WithTop A),WithTop.coe_le_coe.mpr x.property⟩) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact WithTop.coe_inj.mp (congrArg Subtype.val h)
    · intro x
      have hne : x.val ≠ ⊤ := by
        intro h
        have hx := x.property
        rw [h] at hx
        exact WithTop.not_top_le_coe a hx
      obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp hne
      have hba : b <= a := by apply WithTop.coe_le_coe.mp; rw [hb]; exact x.property
      exact ⟨⟨b,hba⟩,Subtype.ext hb⟩)
  exact { e with map_rel_iff' := by intro x y; exact WithTop.coe_le_coe }

end D5.S3.Combinatorics.PriorityLattice.IdealCompression

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression

variable {k : Nat}

def CodeClosed (t : ((v : Fin k) -> Fin (v.val + 1))) (s : Finset (Fin k)) : Prop :=
  ∀ v ∈ s, ∀ w : Fin k, (t v).val <= w.val -> w <= v -> w ∈ s

private instance codeClosedDecidable (t : ((v : Fin k) -> Fin (v.val + 1))) (s : Finset (Fin k)) : Decidable (CodeClosed t s) :=
  inferInstanceAs (Decidable (∀ v ∈ s, ∀ w : Fin k, (t v).val <= w.val -> w <= v -> w ∈ s))



namespace IntervalForest

variable {n : Nat}

noncomputable def supportParent (P : IntervalForest n) (v : (support P)) : Fin (n+1) :=
  (Option.ne_none_iff_exists'.mp ((mem_support P v.val).mp v.property)).choose

theorem supportParent_spec (P : IntervalForest n) (v : (support P)) :
    P.parent v.val = some ((supportParent P) v) :=
  (Option.ne_none_iff_exists'.mp ((mem_support P v.val).mp v.property)).choose_spec

noncomputable def firstNeeded (P : IntervalForest n) (v : (support P)) : Fin (n+1) :=
  ⟨((supportParent P) v).val+1,by
    have h := P.increasing _ _ ((supportParent_spec P) v)
    have := v.val.isLt
    change ((supportParent P) v).val < v.val.val at h
    omega⟩

private theorem firstNeeded_le (P : IntervalForest n) (v : (support P)) : (firstNeeded P) v <= v.val := by
  have h := P.increasing _ _ ((supportParent_spec P) v)
  change ((supportParent P) v).val < v.val.val at h
  change ((supportParent P) v).val+1 <= v.val.val
  omega

private theorem firstNeeded_mem (P : IntervalForest n) (v : (support P)) :
    (firstNeeded P) v ∈ (support P) := by
  rw [mem_support]
  exact P.no_skipped_root ((supportParent_spec P) v)
    (by change ((supportParent P) v).val < ((supportParent P) v).val+1; omega)
    ((firstNeeded_le P) v)

noncomputable def firstIndex (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (i : Fin k) : Fin k :=
  ((support P).orderIsoOfFin h).symm ⟨(firstNeeded P) ((support P).orderIsoOfFin h i),(firstNeeded_mem P) _⟩

private theorem firstIndex_le (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k) (i : Fin k) :
    (firstIndex P) h i <= i := by
  apply ((support P).orderIsoOfFin h).le_iff_le.mp
  change ((support P).orderIsoOfFin h ((firstIndex P) h i)).val <= ((support P).orderIsoOfFin h i).val
  simp only [firstIndex,OrderIso.apply_symm_apply]
  exact (firstNeeded_le P) _

noncomputable def compressCode (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k) : ((v : Fin k) -> Fin (v.val + 1)) :=
  fun i => ⟨((firstIndex P) h i).val,Nat.lt_succ_of_le ((firstIndex_le P) h i)⟩

private theorem compressCode_relation (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (i j : Fin k) : ((compressCode P) h i).val <= j.val ↔
      (supportParent P) ((support P).orderIsoOfFin h i) < ((support P).orderIsoOfFin h j).val := by
  change (firstIndex P) h i <= j ↔ _
  rw [← ((support P).orderIsoOfFin h).le_iff_le]
  change ((support P).orderIsoOfFin h ((firstIndex P) h i)).val <= ((support P).orderIsoOfFin h j).val ↔ _
  simp only [firstIndex,OrderIso.apply_symm_apply]
  change ((supportParent P) ((support P).orderIsoOfFin h i)).val+1 <= ((support P).orderIsoOfFin h j).val.val ↔
    ((supportParent P) ((support P).orderIsoOfFin h i)).val < ((support P).orderIsoOfFin h j).val.val
  omega

private noncomputable def supportToIndices (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (s : Finset (Fin (n+1))) : Finset (Fin k) := by
  classical exact Finset.univ.filter (fun i => ((support P).orderIsoOfFin h i).val ∈ s)

@[simp] private theorem mem_supportToIndices (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (s : Finset (Fin (n+1))) (i : Fin k) :
    i ∈ (supportToIndices P) h s ↔ ((support P).orderIsoOfFin h i).val ∈ s := by
  classical simp [supportToIndices]

private noncomputable def indicesToSupport (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (s : Finset (Fin k)) : Finset (Fin (n+1)) := by
  classical exact s.image (fun i => ((support P).orderIsoOfFin h i).val)

@[simp] private theorem mem_indicesToSupport (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (s : Finset (Fin k)) (i : Fin k) :
    ((support P).orderIsoOfFin h i).val ∈ (indicesToSupport P) h s ↔ i ∈ s := by
  classical
  simp only [indicesToSupport,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,hji⟩
    have he : j = i := ((support P).orderIsoOfFin h).injective (Subtype.ext hji)
    simpa only [he] using hj
  · intro hi; exact ⟨i,hi,rfl⟩

private theorem support_indices_closed (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (s : Finset (Fin (n+1))) (hs : (ClosedSupport P) s) :
    CodeClosed ((compressCode P) h) ((supportToIndices P) h s) := by
  intro i hi j ht hji
  rw [mem_supportToIndices] at hi ⊢
  have hpj := ((compressCode_relation P) h i j).mp ht
  have hji' : ((support P).orderIsoOfFin h j).val <= ((support P).orderIsoOfFin h i).val :=
    ((support P).orderIsoOfFin h).monotone hji
  exact hs.2 _ hi _ ((supportParent_spec P) _) _ hpj hji'

private theorem indices_support_closed (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (s : Finset (Fin k)) (hs : CodeClosed ((compressCode P) h) s) :
    (ClosedSupport P) ((indicesToSupport P) h s) := by
  classical
  constructor
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact ((support P).orderIsoOfFin h i).property
  · intro v hv p hp w hpw hwv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hwP := (mem_support P w).mpr (P.no_skipped_root hp hpw hwv)
    let j := ((support P).orderIsoOfFin h).symm ⟨w,hwP⟩
    have hj : ((support P).orderIsoOfFin h j).val = w := by simp [j]
    have hji : j <= i := by
      apply ((support P).orderIsoOfFin h).le_iff_le.mp
      change ((support P).orderIsoOfFin h j).val <= ((support P).orderIsoOfFin h i).val
      rwa [hj]
    have hparent : (supportParent P) ((support P).orderIsoOfFin h i) = p :=
      Option.some.inj (((supportParent_spec P) _).symm.trans hp)
    have ht : ((compressCode P) h i).val <= j.val := by
      rw [(compressCode_relation P),hparent,hj]
      exact hpw
    rw [← hj,mem_indicesToSupport]
    exact hs i hi j ht hji

private theorem support_indices_inverse (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k)
    (s : Finset (Fin (n+1))) (hs : s ⊆ (support P)) :
    (indicesToSupport P) h ((supportToIndices P) h s) = s := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact ((mem_supportToIndices P) h s i).mp hi
  · intro hv
    let i := ((support P).orderIsoOfFin h).symm ⟨v,hs hv⟩
    have hi : ((support P).orderIsoOfFin h i).val = v := by simp [i]
    exact Finset.mem_image.mpr ⟨i,((mem_supportToIndices P) h s i).mpr (hi ▸ hv),hi⟩

private noncomputable def closedSupportCodeOrderIso (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k) :
    {s : Finset (Fin (n+1)) // (ClosedSupport P) s} ≃o {s : Finset (Fin _) // CodeClosed ((compressCode P) h) s} where
  toFun s := ⟨(supportToIndices P) h s.val,(support_indices_closed P) h s.val s.property⟩
  invFun s := ⟨(indicesToSupport P) h s.val,(indices_support_closed P) h s.val s.property⟩
  left_inv s := Subtype.ext ((support_indices_inverse P) h s.val s.property.1)
  right_inv s := by
    apply Subtype.ext
    ext i
    exact ((mem_supportToIndices P) h _ i).trans ((mem_indicesToSupport P) h s.val i)
  map_rel_iff' := by
    intro s t
    change (supportToIndices P) h s.val ⊆ (supportToIndices P) h t.val ↔ s.val ⊆ t.val
    constructor
    · intro hst v hv
      let i := ((support P).orderIsoOfFin h).symm ⟨v,s.property.1 hv⟩
      have hi : ((support P).orderIsoOfFin h i).val = v := by simp [i]
      rw [← hi] at hv ⊢
      rw [← mem_supportToIndices] at hv ⊢
      exact hst hv
    · intro hst i hi
      rw [mem_supportToIndices] at hi ⊢
      exact hst hi

noncomputable def idealCodeOrderIso (P : IntervalForest n) {k : Nat} (h : (edgeCount P) = k) :
    Set.Iic (P : (WithTop (IntervalForest n))) ≃o {s : Finset (Fin _) // CodeClosed ((compressCode P) h) s} :=
  (coeIicOrderIso P).symm.trans ((idealSupportOrderIso P).trans ((closedSupportCodeOrderIso P) h))

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.IdealCompression

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression

namespace SmallCases

attribute [local instance] Classical.decEq

private def p1 : IntervalForest 1 := forestOfLocal ![none, some 0]
  (by decide) (by decide)

private def a2 : IntervalForest 2 := forestOfLocal ![none, some 0, none]
  (by decide) (by decide)

private def b2 : IntervalForest 2 := forestOfLocal ![none, none, some 1]
  (by decide) (by decide)

private def s2 : IntervalForest 2 := forestOfLocal ![none, some 0, some 0]
  (by decide) (by decide)

private def c2 : IntervalForest 2 := forestOfLocal ![none, some 0, some 1]
  (by decide) (by decide)

private theorem parent_one_cases {n : Nat} (hn : 1 < n+1) (P : IntervalForest n) :
    P.parent ⟨1,hn⟩ = none ∨ P.parent ⟨1,hn⟩ = some 0 := by
  cases h : P.parent ⟨1,hn⟩ with
  | none => exact Or.inl rfl
  | some p =>
    have hp := P.increasing _ _ h
    have hpv : p.val < 1 := hp
    have hzero : p = 0 := by
      apply Fin.ext
      simpa only [Fin.val_zero] using (show p.val = 0 from by omega)
    subst p
    exact Or.inr rfl

private theorem forests_one (P : IntervalForest 1) : P = IntervalForest.empty 1 ∨ P = p1 := by
  rcases parent_one_cases (by omega) P with h | h
  · left
    apply IntervalForest.ext
    funext v
    fin_cases v
    · exact P.parent_zero
    · exact h
  · right
    apply IntervalForest.ext
    funext v
    fin_cases v
    · exact P.parent_zero
    · exact h

private theorem forests_two (P : IntervalForest 2) :
    P = IntervalForest.empty 2 ∨ P = a2 ∨ P = b2 ∨ P = s2 ∨ P = c2 := by
  have h0 := P.parent_zero
  have h1 := parent_one_cases (by omega) P
  have h2 : P.parent 2 = none ∨ P.parent 2 = some 0 ∨ P.parent 2 = some 1 := by
    cases h : P.parent 2 with
    | none => exact Or.inl rfl
    | some p =>
      have hp := P.increasing _ _ h
      have hpv : p.val < 2 := hp
      have hval : p.val = 0 ∨ p.val = 1 := by omega
      have hpc : p = 0 ∨ p = 1 := hval.imp Fin.ext Fin.ext
      rcases hpc with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hbad : ¬ (P.parent 1 = none ∧ P.parent 2 = some 0) := by
    rintro ⟨hn, hp⟩
    exact P.no_skipped_root hp (by decide : (0 : Fin 3) < 1) (by decide) hn
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
  · left; apply IntervalForest.ext; funext v; fin_cases v <;> assumption
  · exact (hbad ⟨h1,h2⟩).elim
  · right; right; left; apply IntervalForest.ext; funext v; fin_cases v <;> assumption
  · right; left; apply IntervalForest.ext; funext v; fin_cases v <;> assumption
  · right; right; right; left; apply IntervalForest.ext; funext v; fin_cases v <;> assumption
  · right; right; right; right; apply IntervalForest.ext; funext v; fin_cases v <;> assumption

private noncomputable instance forestOneFintype : Fintype (IntervalForest 1) where
  elems := {IntervalForest.empty 1, p1}
  complete P := by simpa using forests_one P

private noncomputable instance forestTwoFintype : Fintype (IntervalForest 2) where
  elems := {IntervalForest.empty 2,a2,b2,s2,c2}
  complete P := by simpa using forests_two P

private theorem card_one : Nat.card (IntervalForest 1) = 2 := by
  rw [Nat.card_eq_fintype_card]
  change ({IntervalForest.empty 1, p1} : Finset (IntervalForest 1)).card = 2
  have hne : IntervalForest.empty 1 ≠ p1 := by
    intro h
    have hp := congrArg (fun P : IntervalForest 1 => P.parent 1) h
    change (none : Option (Fin 2)) = some 0 at hp
    cases hp
  simp [hne]

private theorem card_two : Nat.card (IntervalForest 2) = 5 := by
  rw [Nat.card_eq_fintype_card]
  change ({IntervalForest.empty 2,a2,b2,s2,c2} : Finset (IntervalForest 2)).card = 5
  have hab : a2 ≠ b2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have has : a2 ≠ s2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have hac : a2 ≠ c2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have hbs : b2 ≠ s2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have hbc : b2 ≠ c2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have hsc : s2 ≠ c2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have hea : IntervalForest.empty 2 ≠ a2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have heb : IntervalForest.empty 2 ≠ b2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have hes : IntervalForest.empty 2 ≠ s2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  have hec : IntervalForest.empty 2 ≠ c2 := by intro h; have := congrArg (fun P => (P.parent 1,P.parent 2)) h; contradiction
  simp [hab,has,hac,hbs,hbc,hsc,hea,heb,hes,hec]

end SmallCases

private theorem pi_zero_card : Nat.card ((WithTop (IntervalForest 0))) = 2 := by
  change Nat.card (Option (IntervalForest 0)) = 2
  rw [Finite.card_option, IntervalForest.card_zero]

theorem pi_one_card : Nat.card ((WithTop (IntervalForest 1))) = 3 := by
  change Nat.card (Option (IntervalForest 1)) = 3
  rw [Finite.card_option, SmallCases.card_one]

theorem pi_two_card : Nat.card ((WithTop (IntervalForest 2))) = 6 := by
  change Nat.card (Option (IntervalForest 2)) = 6
  rw [Finite.card_option, SmallCases.card_two]

end D5.S3.Combinatorics.PriorityLattice.IdealCompression

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression
namespace SmallIdealCodes

def t1 : ((v : Fin 1) -> Fin (v.val + 1)) := fun _ => 0

def t20 : ((v : Fin 2) -> Fin (v.val + 1)) := fun _ => 0

def t21 : ((v : Fin 2) -> Fin (v.val + 1)) := fun i => ⟨i.val,by omega⟩

def t3 (a : Fin 2) (b : Fin 3) : ((v : Fin 3) -> Fin (v.val + 1)) := fun i =>
  if h0 : i.val = 0 then 0 else
    if h1 : i.val = 1 then ⟨a.val,by have := a.isLt; omega⟩ else
      ⟨b.val,by have := b.isLt; have := i.isLt; omega⟩

theorem code_one (t : ((v : Fin 1) -> Fin (v.val + 1))) : t = t1 := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply Fin.ext; have hh := (t 0).isLt; change (t 0).val < 1 at hh; dsimp [t1,t20,t21,t3]; omega

theorem code_two (t : ((v : Fin 2) -> Fin (v.val + 1))) : t = t20 ∨ t = t21 := by
  have h : (t 1).val = 0 ∨ (t 1).val = 1 := by have := (t 1).isLt; omega
  rcases h with h | h
  · left; funext i; fin_cases i
    · apply Fin.ext; have hh := (t 0).isLt; change (t 0).val < 1 at hh; dsimp [t1,t20,t21,t3]; omega
    · exact Fin.ext h
  · right; funext i; fin_cases i
    · apply Fin.ext; have hh := (t 0).isLt; change (t 0).val < 1 at hh; dsimp [t1,t20,t21,t3]; omega
    · exact Fin.ext h

theorem code_three (t : ((v : Fin 3) -> Fin (v.val + 1))) : ∃ a : Fin 2, ∃ b : Fin 3, t = t3 a b := by
  refine ⟨t 1,t 2,?_⟩
  funext i
  fin_cases i
  · apply Fin.ext; have hh := (t 0).isLt; change (t 0).val < 1 at hh; dsimp [t1,t20,t21,t3]; omega
  · rfl
  · rfl

private theorem card1 : Nat.card ({s : Finset (Fin _) // CodeClosed t1 s}) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card20 : Nat.card ({s : Finset (Fin _) // CodeClosed t20 s}) = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card21 : Nat.card ({s : Finset (Fin _) // CodeClosed t21 s}) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card3 (a : Fin 2) (b : Fin 3) : Nat.card ({s : Finset (Fin _) // CodeClosed (t3 a b) s}) =
    if a = 0 then (if b = 0 then 4 else if b = 1 then 4 else 6)
    else (if b = 0 then 5 else if b = 1 then 6 else 8) := by
  rw [Nat.card_eq_fintype_card]
  fin_cases a <;> fin_cases b <;> decide

theorem card_two_iff (t : ((v : Fin 2) -> Fin (v.val + 1))) : Nat.card ({s : Finset (Fin _) // CodeClosed t s}) = 3 ↔ t = t20 := by
  rcases code_two t with rfl | rfl
  · rw [card20]; simp only [eq_self_iff_true]
  · have hne : t21 ≠ t20 := by
      intro h
      have hc := congrArg (fun t => (t 1).val) h
      contradiction
    rw [card21]; simp only [hne]; norm_num

theorem card_three_iff (t : ((v : Fin 3) -> Fin (v.val + 1))) : Nat.card ({s : Finset (Fin _) // CodeClosed t s}) = 6 ↔
    t = t3 0 2 ∨ t = t3 1 1 := by
  obtain ⟨a,b,rfl⟩ := code_three t
  rw [card3]
  have inj : Function.Injective (fun p : Fin 2 × Fin 3 => t3 p.1 p.2) := by
    intro p q h
    apply Prod.ext
    · exact Fin.ext (congrArg (fun t => (t 1).val) h)
    · exact Fin.ext (congrArg (fun t => (t 2).val) h)
  have heq (a b c d) : t3 a b = t3 c d ↔ a = c ∧ b = d := by
    constructor
    · intro h; have := @inj (a,b) (c,d) h; exact Prod.mk.inj this
    · rintro ⟨rfl,rfl⟩; rfl
  simp_rw [heq]
  fin_cases a <;> fin_cases b <;> decide

end SmallIdealCodes
end D5.S3.Combinatorics.PriorityLattice.IdealCompression

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression

variable {k l : Nat}

private theorem codeClosed_image (t : ((v : Fin k) -> Fin (v.val + 1))) (u : ((v : Fin l) -> Fin (v.val + 1))) (e : Fin k ≃ Fin l)
    (he : ∀ i j, ((t i).val <= j.val ∧ j <= i) ↔
      ((u (e i)).val <= (e j).val ∧ e j <= e i))
    (s : Finset (Fin k)) (hs : CodeClosed t s) : CodeClosed u (s.image e) := by
  intro v hv w htw hwv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  let j := e.symm w
  have hj : e j = w := e.apply_symm_apply w
  have hr := (he i j).mpr (by rw [hj]; exact ⟨htw,hwv⟩)
  exact Finset.mem_image.mpr ⟨j,hs i hi j hr.1 hr.2,hj⟩

private noncomputable def codePermutationOrderIso (t : ((v : Fin k) -> Fin (v.val + 1))) (u : ((v : Fin l) -> Fin (v.val + 1))) (e : Fin k ≃ Fin l)
    (he : ∀ i j, ((t i).val <= j.val ∧ j <= i) ↔
      ((u (e i)).val <= (e j).val ∧ e j <= e i)) : {s : Finset (Fin _) // CodeClosed t s} ≃o {s : Finset (Fin _) // CodeClosed u s} where
  toFun s := ⟨s.val.image e,codeClosed_image t u e he s.val s.property⟩
  invFun s := ⟨s.val.image e.symm,codeClosed_image u t e.symm (by
    intro i j
    have hu : (u (e (e.symm i))).val = (u i).val :=
      congrArg (fun v => (u v).val) (e.apply_symm_apply i)
    simpa only [hu,Equiv.apply_symm_apply] using (he (e.symm i) (e.symm j)).symm) s.val s.property⟩
  left_inv s := by apply Subtype.ext; simp only [Finset.image_image]; simp
  right_inv s := by apply Subtype.ext; simp only [Finset.image_image]; simp
  map_rel_iff' := by
    intro s t
    exact Finset.image_subset_image_iff e.injective

namespace SmallIdealCodes

private def cycle3 : Fin 3 ≃ Fin 3 where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

noncomputable def twoTripleModelsIso : {s : Finset (Fin _) // CodeClosed (t3 0 2) s} ≃o {s : Finset (Fin _) // CodeClosed (t3 1 1) s} :=
  codePermutationOrderIso _ _ cycle3 (by intro i j; fin_cases i <;> fin_cases j <;> decide)

end SmallIdealCodes
end D5.S3.Combinatorics.PriorityLattice.IdealCompression

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression
namespace SmallIdealCodes

open SmallCases

private def code1Enum : Fin 2 -> {s : Finset (Fin _) // CodeClosed t1 s} := fun i =>
  if i = 0 then ⟨{},by decide⟩ else ⟨{0},by decide⟩

private def code2Enum : Fin 3 -> {s : Finset (Fin _) // CodeClosed t20 s} := fun i =>
  if i = 0 then ⟨{},by decide⟩ else if i = 1 then ⟨{0},by decide⟩
  else ⟨{0,1},by decide⟩

private def code3Enum : Fin 6 -> {s : Finset (Fin _) // CodeClosed (t3 0 2) s} := fun i =>
  if i = 0 then ⟨{},by decide⟩ else if i = 1 then ⟨{0},by decide⟩
  else if i = 2 then ⟨{2},by decide⟩ else if i = 3 then ⟨{0,1},by decide⟩
  else if i = 4 then ⟨{0,2},by decide⟩ else ⟨{0,1,2},by decide⟩

private theorem code1Enum_injective : Function.Injective code1Enum := by
  unfold Function.Injective
  decide

private theorem code2Enum_injective : Function.Injective code2Enum := by
  unfold Function.Injective
  decide

private theorem code3Enum_injective : Function.Injective code3Enum := by
  unfold Function.Injective
  decide

private noncomputable def code1Equiv : Fin 2 ≃ {s : Finset (Fin _) // CodeClosed t1 s} :=
  Equiv.ofBijective code1Enum (code1Enum_injective.bijective_of_nat_card_le (by rw [Nat.card_fin,card1]))

private noncomputable def code2Equiv : Fin 3 ≃ {s : Finset (Fin _) // CodeClosed t20 s} :=
  Equiv.ofBijective code2Enum (code2Enum_injective.bijective_of_nat_card_le (by rw [Nat.card_fin,card20]))

private noncomputable def code3Equiv : Fin 6 ≃ {s : Finset (Fin _) // CodeClosed (t3 0 2) s} :=
  Equiv.ofBijective code3Enum (code3Enum_injective.bijective_of_nat_card_le (by rw [Nat.card_fin,card3]; decide))

private noncomputable def pi0Enum : Fin 2 -> WithTop (IntervalForest 0) := fun i =>
  if i = 0 then (IntervalForest.empty 0 : WithTop (IntervalForest 0)) else ⊤
private noncomputable def pi1Enum : Fin 3 -> WithTop (IntervalForest 1) := fun i =>
  if i = 0 then (IntervalForest.empty 1 : WithTop (IntervalForest 1)) else if i = 1 then (p1 : WithTop (IntervalForest 1)) else ⊤
private noncomputable def pi2Enum : Fin 6 -> WithTop (IntervalForest 2) := fun i =>
  if i = 0 then (IntervalForest.empty 2 : WithTop (IntervalForest 2)) else if i = 1 then (a2 : WithTop (IntervalForest 2))
  else if i = 2 then (b2 : WithTop (IntervalForest 2)) else if i = 3 then (s2 : WithTop (IntervalForest 2))
  else if i = 4 then (c2 : WithTop (IntervalForest 2)) else ⊤

private theorem pi0Enum_injective : Function.Injective pi0Enum := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl |
    (have hc := congrArg (fun x : (WithTop (IntervalForest 0)) => (x : Option (IntervalForest 0)).isNone) h; contradiction)

private theorem pi1Enum_injective : Function.Injective pi1Enum := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [pi1Enum] at h ⊢ <;>
    first | rfl | (simp only [WithTop.coe_ne_top,WithTop.top_ne_coe] at h) |
    (have hc := congrArg (fun x : (WithTop (IntervalForest 1)) => (x : WithTop (IntervalForest 1)).map (fun P => P.parent 1)) h; contradiction)

private theorem pi2Enum_injective : Function.Injective pi2Enum := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [pi2Enum] at h ⊢ <;>
    first | rfl | (simp only [WithTop.coe_ne_top,WithTop.top_ne_coe] at h) |
    (have hc := congrArg (fun x : (WithTop (IntervalForest 2)) => (x : WithTop (IntervalForest 2)).map (fun P => (P.parent 1,P.parent 2))) h; contradiction)

private noncomputable def pi0Equiv : Fin 2 ≃ (WithTop (IntervalForest 0)) :=
  Equiv.ofBijective pi0Enum (pi0Enum_injective.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact pi_zero_card.le))
private noncomputable def pi1Equiv : Fin 3 ≃ (WithTop (IntervalForest 1)) :=
  Equiv.ofBijective pi1Enum (pi1Enum_injective.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact pi_one_card.le))
private noncomputable def pi2Equiv : Fin 6 ≃ (WithTop (IntervalForest 2)) :=
  Equiv.ofBijective pi2Enum (pi2Enum_injective.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact pi_two_card.le))

noncomputable def pi0CodeOrderIso : (WithTop (IntervalForest 0)) ≃o {s : Finset (Fin _) // CodeClosed t1 s} :=
  { pi0Equiv.symm.trans code1Equiv with
    map_rel_iff' := by
      intro x y
      obtain ⟨i,rfl⟩ := pi0Equiv.surjective x
      obtain ⟨j,rfl⟩ := pi0Equiv.surjective y
      simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
      change code1Enum i <= code1Enum j ↔ pi0Enum i <= pi0Enum j
      change (code1Enum i).val ⊆ (code1Enum j).val ↔
        (pi0Enum i : WithTop (IntervalForest 0)) <= pi0Enum j
      fin_cases i <;> fin_cases j <;>
        simp [code1Enum,pi0Enum,IntervalForest.le_iff_parent] <;> decide }

noncomputable def pi1CodeOrderIso : (WithTop (IntervalForest 1)) ≃o {s : Finset (Fin _) // CodeClosed t20 s} :=
  { pi1Equiv.symm.trans code2Equiv with
    map_rel_iff' := by
      intro x y
      obtain ⟨i,rfl⟩ := pi1Equiv.surjective x
      obtain ⟨j,rfl⟩ := pi1Equiv.surjective y
      simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
      change code2Enum i <= code2Enum j ↔ pi1Enum i <= pi1Enum j
      change (code2Enum i).val ⊆ (code2Enum j).val ↔
        (pi1Enum i : WithTop (IntervalForest 1)) <= pi1Enum j
      fin_cases i <;> fin_cases j <;>
        simp [code2Enum,pi1Enum,IntervalForest.le_iff_parent] <;> decide }

noncomputable def pi2CodeOrderIso : (WithTop (IntervalForest 2)) ≃o {s : Finset (Fin _) // CodeClosed (t3 0 2) s} :=
  { pi2Equiv.symm.trans code3Equiv with
    map_rel_iff' := by
      intro x y
      obtain ⟨i,rfl⟩ := pi2Equiv.surjective x
      obtain ⟨j,rfl⟩ := pi2Equiv.surjective y
      simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
      change code3Enum i <= code3Enum j ↔ pi2Enum i <= pi2Enum j
      change (code3Enum i).val ⊆ (code3Enum j).val ↔
        (pi2Enum i : WithTop (IntervalForest 2)) <= pi2Enum j
      fin_cases i <;> fin_cases j <;>
        simp [code3Enum,pi2Enum,IntervalForest.le_iff_parent] <;> decide }

end SmallIdealCodes
end D5.S3.Combinatorics.PriorityLattice.IdealCompression

namespace D5.S3.Combinatorics.PriorityLattice.IdealCompression
namespace IntervalForest

variable {n k : Nat}

theorem compressCode_self_iff (P : IntervalForest n) (h : (edgeCount P) = k) (i : Fin k) :
    ((compressCode P) h i).val = i.val ↔
      ((supportParent P) ((support P).orderIsoOfFin h i)).val+1 = ((support P).orderIsoOfFin h i).val.val := by
  change ((firstIndex P) h i).val = i.val ↔ _
  constructor
  · intro hi
    have hfin : (firstIndex P) h i = i := Fin.ext hi
    have hc := congrArg (fun j => ((support P).orderIsoOfFin h j).val) hfin
    simp only [firstIndex,OrderIso.apply_symm_apply] at hc
    exact congrArg Fin.val hc
  · intro hi
    have hc : (firstNeeded P) ((support P).orderIsoOfFin h i) = ((support P).orderIsoOfFin h i).val := Fin.ext hi
    have hh : (⟨(firstNeeded P) ((support P).orderIsoOfFin h i),(firstNeeded_mem P) _⟩ : (support P)) =
        (support P).orderIsoOfFin h i := Subtype.ext hc
    unfold firstIndex
    rw [hh,OrderIso.symm_apply_apply]

theorem support_adjacent_of_needed (P : IntervalForest n) (h : (edgeCount P) = k)
    (i j : Fin k) (hij : i.val+1 = j.val) (ht : ((compressCode P) h j).val <= i.val) :
    ((support P).orderIsoOfFin h i).val.val+1 = ((support P).orderIsoOfFin h j).val.val := by
  have hijlt : i < j := by change i.val < j.val; omega
  have hvlt := ((support P).orderIsoOfFin h).strictMono hijlt
  change ((support P).orderIsoOfFin h i).val.val < ((support P).orderIsoOfFin h j).val.val at hvlt
  let w : Fin (n+1) := ⟨((support P).orderIsoOfFin h i).val.val+1,by
    have := ((support P).orderIsoOfFin h j).val.isLt
    omega⟩
  have hp := ((compressCode_relation P) h j i).mp ht
  have hpw : (supportParent P) ((support P).orderIsoOfFin h j) < w := by
    change ((supportParent P) ((support P).orderIsoOfFin h j)).val < ((support P).orderIsoOfFin h i).val.val at hp
    change ((supportParent P) ((support P).orderIsoOfFin h j)).val < ((support P).orderIsoOfFin h i).val.val+1
    omega
  have hwj : w <= ((support P).orderIsoOfFin h j).val := by
    change ((support P).orderIsoOfFin h i).val.val+1 <= ((support P).orderIsoOfFin h j).val.val
    omega
  have hwm := (mem_support P w).mpr
    (P.no_skipped_root ((supportParent_spec P) _) hpw hwj)
  let z := ((support P).orderIsoOfFin h).symm ⟨w,hwm⟩
  have hz : ((support P).orderIsoOfFin h z).val = w := by simp [z]
  have hiz : i < z := by
    apply ((support P).orderIsoOfFin h).lt_iff_lt.mp
    change ((support P).orderIsoOfFin h i).val < ((support P).orderIsoOfFin h z).val
    rw [hz]
    change ((support P).orderIsoOfFin h i).val.val < ((support P).orderIsoOfFin h i).val.val+1
    omega
  have hzj : z <= j := by
    apply ((support P).orderIsoOfFin h).le_iff_le.mp
    change ((support P).orderIsoOfFin h z).val <= ((support P).orderIsoOfFin h j).val
    rwa [hz]
  have he : z = j := by apply Fin.ext; have hi : i.val < z.val := hiz; have hj : z.val <= j.val := hzj; omega
  rw [he] at hz
  exact (congrArg Fin.val hz).symm

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.IdealCompression
