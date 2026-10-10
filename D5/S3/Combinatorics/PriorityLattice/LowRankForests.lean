/- GID: D5/S3/Combinatorics/PriorityLattice/LowRankForests
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/LowRankForests
   mirror-E: none(waiver:general-priority-lattice-counting)
   anchors: []
   utility: none
   digest: Priority-forest interval structure and counting. -/

/-
admission_basis: escape-witness
escape_witness: long_three_card
The count uses a bijection with actual one-long forests whose surjectivity recovers the required predecessor from the interval-root invariant.
Direct frozen dependencies: none; direct D5 dependencies are supplied by this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14955
Proof shapes expand all same-delivery declarations and apply the upstream-only bypass test.
OneLongAt: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.code_one_step_implies_one_long
OneLong: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.code_one_step_implies_one_long
CodeOneStep: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.code_one_step_implies_one_long
IntervalForest.code_one_step_implies_one_long: proof_shape: content
IntervalForest.one_long_implies_code_one_step: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.one_long_iff_code_one_step
IntervalForest.one_long_iff_code_one_step: proof_shape: content
IntervalForest.oneLongAt_unique: proof_shape: bind-only; consumer: LowRankForests.longDataToForest_injective
codeOneStepDecidable: proof_shape: bind-only; consumer: LowRankForests.SmallIdealCodes.oneStep_three_iff
SmallIdealCodes.oneStep_two_iff: proof_shape: bind-only; consumer: PrincipalIdeals.ideal_one_iff_oneLong
SmallIdealCodes.oneStep_three_iff: proof_shape: bind-only; consumer: PrincipalIdeals.ideal_two_iff_oneLong
PositiveSupport: proof_shape: bind-only; consumer: LowRankForests.LongData
shortParent: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.edgeCount_one_exists_single
shortForest: proof_shape: content
shortForest_support: proof_shape: bind-only; consumer: LowRankForests.singleEdge_support
longParent: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.eq_oneLongForest
oneLongForest: proof_shape: content
oneLongForest_parent: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.eq_oneLongForest
oneLongForest_support: proof_shape: bind-only; consumer: LowRankForests.longDataToForest
LongData: proof_shape: bind-only; consumer: LowRankForests.longDataEquiv
IntervalForest.positive_support: proof_shape: bind-only; consumer: LowRankForests.IntervalForest.eq_oneLongForest
oneLongForest_oneLongAt: proof_shape: bind-only; consumer: LowRankForests.longDataToForest
longDataToForest: proof_shape: content
longDataToForest_injective: proof_shape: bind-only; consumer: LowRankForests.longDataEquiv
IntervalForest.eq_oneLongForest: proof_shape: bind-only; consumer: LowRankForests.longDataToForest_surjective
longDataToForest_surjective: proof_shape: content
longDataEquiv: proof_shape: content
longVertex: proof_shape: bind-only; consumer: LowRankForests.allowedExtra_not_pair
priorVertex: proof_shape: bind-only; consumer: LowRankForests.allowedExtra_not_pair
longPair: proof_shape: bind-only; consumer: LowRankForests.allowedExtra_not_pair
prior_ne_long: proof_shape: bind-only; consumer: LowRankForests.longPair_card
longPair_card: proof_shape: bind-only; consumer: LowRankForests.longPairData
longPair_positive: proof_shape: bind-only; consumer: LowRankForests.longPairData
longPairData: proof_shape: bind-only; consumer: LowRankForests.longPairData_right_inv
longDataIndex: proof_shape: bind-only; consumer: LowRankForests.longPairData_right_inv
longVertex_dataIndex: proof_shape: bind-only; consumer: LowRankForests.longPairData_right_inv
longPair_subset_data: proof_shape: bind-only; consumer: LowRankForests.longPairData_right_inv
longPairData_right_inv: proof_shape: bind-only; consumer: LowRankForests.longPairEquiv
longPairEquiv: proof_shape: bind-only; consumer: LowRankForests.long_two_card
long_two_card: proof_shape: content
AllowedExtra: proof_shape: bind-only; consumer: LowRankForests.TripleParams
TripleParams: proof_shape: bind-only; consumer: LowRankForests.long_three_card
allowedExtra_not_pair: proof_shape: bind-only; consumer: LowRankForests.tripleData
tripleData: proof_shape: bind-only; consumer: LowRankForests.tripleDataEquiv
tripleData_injective: proof_shape: bind-only; consumer: LowRankForests.tripleDataEquiv
tripleData_surjective: proof_shape: bind-only; consumer: LowRankForests.tripleDataEquiv
tripleDataEquiv: proof_shape: bind-only; consumer: LowRankForests.long_three_card
allowedExtra_card: proof_shape: bind-only; consumer: LowRankForests.long_three_card
long_three_card: proof_shape: content
singleEdge: proof_shape: content
singleEdge_support: proof_shape: bind-only; consumer: LowRankForests.singleEdgeEquiv
singleEdge_count: proof_shape: bind-only; consumer: LowRankForests.singleEdgeEquiv
IntervalForest.edgeCount_one_short: proof_shape: content
IntervalForest.edgeCount_one_exists_single: proof_shape: content
singleEdgeEquiv: proof_shape: content
single_edges_card: proof_shape: content
-/

import D5.S3.Combinatorics.PriorityLattice.IdealCompression

open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.ForestCovers
open D5.S3.Combinatorics.PriorityLattice.ForestCovers.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.IdealCompression
open D5.S3.Combinatorics.PriorityLattice.IdealCompression.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.IdealCompression.SmallIdealCodes
open D5.S3.Combinatorics.PriorityLattice.IdealCompression.SmallCases

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests.IntervalForest
end D5.S3.Combinatorics.PriorityLattice.LowRankForests.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.LowRankForests.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests

variable {n k : Nat}

def OneLongAt (P : IntervalForest n) (v : Fin (n+1)) : Prop :=
  (∃ p, P.parent v = some p ∧ p.val+2 = v.val) ∧
  ∀ w p, w ≠ v -> P.parent w = some p -> p.val+1 = w.val

def OneLong (P : IntervalForest n) : Prop := ∃ v, OneLongAt P v

def CodeOneStep (t : ((v : Fin k) -> Fin (v.val + 1))) : Prop := ∃ i j : Fin k,
  i.val+1 = j.val ∧ (t j).val = i.val ∧ ∀ z, z ≠ j -> (t z).val = z.val

namespace IntervalForest

private theorem code_one_step_implies_one_long (P : IntervalForest n) (h : (edgeCount P) = k)
    (ht : CodeOneStep ((compressCode P) h)) : OneLong P := by
  obtain ⟨i,j,hij,htj,hrest⟩ := ht
  refine ⟨((support P).orderIsoOfFin h j).val,?_,?_⟩
  · refine ⟨(supportParent P) ((support P).orderIsoOfFin h j),(supportParent_spec P) _,?_⟩
    have hidx : (firstIndex P) h j = i := Fin.ext htj
    have hfirst := congrArg (fun z => ((support P).orderIsoOfFin h z).val.val) hidx
    simp only [firstIndex,OrderIso.apply_symm_apply] at hfirst
    change ((supportParent P) ((support P).orderIsoOfFin h j)).val+1 = ((support P).orderIsoOfFin h i).val.val at hfirst
    have hadj := (support_adjacent_of_needed P) h i j hij htj.le
    omega
  · intro w p hw hp
    have hwm := (IntervalForest.mem_support P w).mpr (by simp [hp])
    let z := ((support P).orderIsoOfFin h).symm ⟨w,hwm⟩
    have hz : ((support P).orderIsoOfFin h z).val = w := by simp [z]
    have hzj : z ≠ j := by intro hh; rw [hh] at hz; exact hw hz.symm
    have hshort := ((compressCode_self_iff P) h z).mp (hrest z hzj)
    have hpar : (supportParent P) ((support P).orderIsoOfFin h z) = p := by
      apply Option.some.inj
      have hh := (supportParent_spec P) ((support P).orderIsoOfFin h z)
      rw [hz] at hh
      exact hh.symm.trans hp
    rwa [hpar,hz] at hshort

private theorem one_long_implies_code_one_step (P : IntervalForest n) (h : (edgeCount P) = k)
    (hP : OneLong P) : CodeOneStep ((compressCode P) h) := by
  obtain ⟨v,⟨p,hp,hpv⟩,hrest⟩ := hP
  have hvm := (mem_support P v).mpr (by simp [hp])
  let j := ((support P).orderIsoOfFin h).symm ⟨v,hvm⟩
  let i := (firstIndex P) h j
  have hj : ((support P).orderIsoOfFin h j).val = v := by simp [j]
  have hpar : (supportParent P) ((support P).orderIsoOfFin h j) = p := by
    apply Option.some.inj
    have hh := (supportParent_spec P) ((support P).orderIsoOfFin h j)
    rw [hj] at hh
    exact hh.symm.trans hp
  have hi : ((support P).orderIsoOfFin h i).val.val = p.val+1 := by
    dsimp only [i]
    simp only [firstIndex,OrderIso.apply_symm_apply]
    change ((supportParent P) ((support P).orderIsoOfFin h j)).val+1 = p.val+1
    rw [hpar]
  have hijlt : i < j := by
    apply ((support P).orderIsoOfFin h).lt_iff_lt.mp
    change ((support P).orderIsoOfFin h i).val.val < ((support P).orderIsoOfFin h j).val.val
    rw [hi,hj]
    omega
  have hij : i.val+1 = j.val := by
    by_contra hh
    have hilt : i.val < j.val := hijlt
    have hgap : i.val+1 < j.val := by omega
    let z : Fin k := ⟨i.val+1,by have := j.isLt; omega⟩
    have hiz : i < z := by change i.val < i.val+1; omega
    have hzj : z < j := hgap
    have hviz := ((support P).orderIsoOfFin h).strictMono hiz
    have hvzj := ((support P).orderIsoOfFin h).strictMono hzj
    change ((support P).orderIsoOfFin h i).val.val < ((support P).orderIsoOfFin h z).val.val at hviz
    change ((support P).orderIsoOfFin h z).val.val < ((support P).orderIsoOfFin h j).val.val at hvzj
    rw [hi] at hviz
    rw [hj] at hvzj
    omega
  refine ⟨i,j,hij,rfl,?_⟩
  intro z hzj
  apply ((compressCode_self_iff P) h z).mpr
  have hwne : ((support P).orderIsoOfFin h z).val ≠ v := by
    intro hh
    have he : (support P).orderIsoOfFin h z = (support P).orderIsoOfFin h j := Subtype.ext (hh.trans hj.symm)
    exact hzj (((support P).orderIsoOfFin h).injective he)
  exact hrest _ _ hwne ((supportParent_spec P) _)

theorem one_long_iff_code_one_step (P : IntervalForest n) (h : (edgeCount P) = k) :
    OneLong P ↔ CodeOneStep ((compressCode P) h) :=
  ⟨(one_long_implies_code_one_step P) h,(code_one_step_implies_one_long P) h⟩

private theorem oneLongAt_unique (P : IntervalForest n) {v w : Fin (n+1)}
    (hv : OneLongAt P v) (hw : OneLongAt P w) : v = w := by
  by_contra hne
  obtain ⟨p,hp,hpv⟩ := hv.1
  have hshort := hw.2 v p hne hp
  omega

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.LowRankForests

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests

private instance codeOneStepDecidable {k : Nat} (t : ((v : Fin k) -> Fin (v.val + 1))) : Decidable (CodeOneStep t) :=
  inferInstanceAs (Decidable (∃ i j : Fin k,
    i.val+1 = j.val ∧ (t j).val = i.val ∧ ∀ z, z ≠ j -> (t z).val = z.val))

namespace SmallIdealCodes

theorem oneStep_two_iff (t : ((v : Fin 2) -> Fin (v.val + 1))) : CodeOneStep t ↔ t = t20 := by
  rcases code_two t with rfl | rfl <;> decide

theorem oneStep_three_iff (t : ((v : Fin 3) -> Fin (v.val + 1))) : CodeOneStep t ↔
    t = t3 0 2 ∨ t = t3 1 1 := by
  obtain ⟨a,b,rfl⟩ := code_three t
  fin_cases a <;> fin_cases b <;> decide

end SmallIdealCodes
end D5.S3.Combinatorics.PriorityLattice.LowRankForests

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests

variable {n : Nat}

private def PositiveSupport (s : Finset (Fin (n+1))) : Prop := ∀ v ∈ s, 0 < v.val

private noncomputable def shortParent (s : Finset (Fin (n+1))) (v : Fin (n+1)) : Option (Fin (n+1)) := by
  classical exact if v ∈ s then some ⟨v.val-1,by have := v.isLt; omega⟩ else none

private noncomputable def shortForest (s : Finset (Fin (n+1))) (hs : PositiveSupport s) : IntervalForest n := by
  classical
  exact forestOfLocal (shortParent s)
    (by
      intro v p hp
      by_cases hv : v ∈ s
      · simp only [shortParent,hv,ite_true,Option.some.injEq] at hp
        have hpos := hs v hv
        rw [← hp]
        change v.val-1 < v.val
        omega
      · simp [shortParent,hv] at hp)
    (by
      intro v p w hp hpw hwv
      by_cases hv : v ∈ s
      · simp only [shortParent,hv,ite_true,Option.some.injEq] at hp
        have hpos := hs v hv
        have hpval := congrArg Fin.val hp
        dsimp only at hpval
        have hwval : w.val = v.val := by change p.val < w.val at hpw; change w.val <= v.val at hwv; omega
        have hw : w = v := Fin.ext hwval
        subst w
        simp [shortParent,hv]
      · simp [shortParent,hv] at hp)

@[simp] private theorem shortForest_support (s : Finset (Fin (n+1))) (hs : PositiveSupport s) :
    (support (shortForest s hs)) = s := by
  classical
  ext v
  simp [IntervalForest.mem_support,shortForest,forestOfLocal,shortParent]

private noncomputable def longParent (s : Finset (Fin (n+1))) (v : Fin (n+1)) (w : Fin (n+1)) :
    Option (Fin (n+1)) := by
  classical exact if w = v then some ⟨v.val-2,by have := v.isLt; omega⟩ else shortParent s w

private noncomputable def oneLongForest (s : Finset (Fin (n+1))) (hs : PositiveSupport s)
    (v : Fin (n+1)) (hv : v ∈ s) (hv2 : 2 <= v.val)
    (hp : (⟨v.val-1,by have := v.isLt; omega⟩ : Fin (n+1)) ∈ s) : IntervalForest n := by
  classical
  exact forestOfLocal (longParent s v)
    (by
      intro w p hw
      by_cases hwv : w = v
      · simp only [longParent,hwv,ite_true,Option.some.injEq] at hw
        subst w
        rw [← hw]
        change v.val-2 < v.val
        omega
      · simp only [longParent,hwv,ite_false] at hw
        exact (shortForest s hs).increasing w p hw)
    (by
      intro w p z hw hpz hzw
      by_cases hwv : w = v
      · subst w
        simp only [longParent,ite_true,Option.some.injEq] at hw
        have hpval := congrArg Fin.val hw
        dsimp only at hpval
        change p.val < z.val at hpz
        change z.val <= v.val at hzw
        have hz : z.val = v.val ∨ z.val = v.val-1 := by omega
        rcases hz with hz | hz
        · have he : z = v := Fin.ext hz
          subst z
          simp [longParent]
        · have he : z = (⟨v.val-1,by have := v.isLt; omega⟩ : Fin (n+1)) := Fin.ext hz
          have hzmem : z ∈ s := he ▸ hp
          have hzne : z ≠ v := by intro h; have := congrArg Fin.val h; omega
          simp [longParent,hzne,shortParent,hzmem]
      · simp only [longParent,hwv,ite_false] at hw
        have hz := (shortForest s hs).no_skipped_root hw hpz hzw
        change shortParent s z ≠ none at hz
        by_cases hzv : z = v
        · simp [longParent,hzv]
        · simpa only [longParent,hzv,ite_false] using hz)

@[simp] private theorem oneLongForest_parent (s : Finset (Fin (n+1))) (hs : PositiveSupport s)
    (v : Fin (n+1)) (hv : v ∈ s) (hv2 : 2 <= v.val)
    (hp : (⟨v.val-1,by have := v.isLt; omega⟩ : Fin (n+1)) ∈ s) (w : Fin (n+1)) :
    (oneLongForest s hs v hv hv2 hp).parent w = longParent s v w := rfl

@[simp] private theorem oneLongForest_support (s : Finset (Fin (n+1))) (hs : PositiveSupport s)
    (v : Fin (n+1)) (hv : v ∈ s) (hv2 : 2 <= v.val)
    (hp : (⟨v.val-1,by have := v.isLt; omega⟩ : Fin (n+1)) ∈ s) :
    (support (oneLongForest s hs v hv hv2 hp)) = s := by
  classical
  ext w
  by_cases hw : w = v
  · subst w
    simp [IntervalForest.mem_support,longParent,hv]
  · simp [IntervalForest.mem_support,longParent,hw,shortParent]

end D5.S3.Combinatorics.PriorityLattice.LowRankForests

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests

variable {n k : Nat}

private def LongData (n k : Nat) := {d : Fin (n+1) × Finset (Fin (n+1)) //
  PositiveSupport d.2 ∧ d.2.card = k ∧ d.1 ∈ d.2 ∧ 2 <= d.1.val ∧
  (⟨d.1.val-1,by have := d.1.isLt; omega⟩ : Fin (n+1)) ∈ d.2}

namespace IntervalForest

private theorem positive_support (P : IntervalForest n) : PositiveSupport (support P) := by
  intro v hv
  have hn := (mem_support P v).mp hv
  by_contra h
  have hz : v = 0 := by apply Fin.ext; change v.val = 0; omega
  exact hn (hz ▸ P.parent_zero)

end IntervalForest

private theorem oneLongForest_oneLongAt (d : LongData n k) :
    OneLongAt (oneLongForest d.val.2 d.property.1 d.val.1 d.property.2.2.1
      d.property.2.2.2.1 d.property.2.2.2.2) d.val.1 := by
  classical
  constructor
  · refine ⟨⟨d.val.1.val-2,by have := d.val.1.isLt; omega⟩,?_,?_⟩
    · simp [longParent]
    · have := d.property.2.2.2.1; dsimp; omega
  · intro w p hw hp
    simp only [oneLongForest_parent,longParent,hw,ite_false] at hp
    by_cases hws : w ∈ d.val.2
    · simp only [shortParent,hws,ite_true,Option.some.injEq] at hp
      have hpos := d.property.1 w hws
      have hv := congrArg Fin.val hp
      dsimp at hv
      omega
    · simp [shortParent,hws] at hp

private noncomputable def longDataToForest (d : LongData n k) :
    {P : IntervalForest n // (edgeCount P) = k ∧ OneLong P} :=
  ⟨oneLongForest d.val.2 d.property.1 d.val.1 d.property.2.2.1
    d.property.2.2.2.1 d.property.2.2.2.2,
    by constructor
       · change (support (oneLongForest _ _ _ _ _ _)).card = k
         rw [oneLongForest_support]
         exact d.property.2.1
       · exact ⟨d.val.1,oneLongForest_oneLongAt d⟩⟩

private theorem longDataToForest_injective : Function.Injective (@longDataToForest n k) := by
  intro d e h
  have hP := congrArg Subtype.val h
  dsimp only [longDataToForest] at hP
  have hs := congrArg IntervalForest.support hP
  simp only [oneLongForest_support] at hs
  have hd := oneLongForest_oneLongAt d
  have he := oneLongForest_oneLongAt e
  rw [← hP] at he
  have hv := IntervalForest.oneLongAt_unique _ hd he
  exact Subtype.ext (Prod.ext hv hs)

namespace IntervalForest

private theorem eq_oneLongForest (P : IntervalForest n) (v : Fin (n+1)) (hv : OneLongAt P v)
    (hv2 : 2 <= v.val) (hvm : v ∈ (support P))
    (hpred : (⟨v.val-1,by have := v.isLt; omega⟩ : Fin (n+1)) ∈ (support P)) :
    P = oneLongForest (support P) (positive_support P) v hvm hv2 hpred := by
  classical
  apply ext
  funext w
  rw [oneLongForest_parent]
  by_cases hw : w = v
  · subst w
    obtain ⟨p,hp,hpv⟩ := hv.1
    rw [hp]
    simp only [longParent,ite_true,Option.some.injEq]
    apply Fin.ext
    dsimp
    omega
  · simp only [longParent,hw,ite_false]
    by_cases hm : w ∈ (support P)
    · obtain ⟨p,hp⟩ := Option.ne_none_iff_exists'.mp ((mem_support P w).mp hm)
      rw [hp]
      simp only [shortParent,hm,ite_true,Option.some.injEq]
      have hlen := hv.2 w p hw hp
      apply Fin.ext
      dsimp
      omega
    · have hn : P.parent w = none := by simpa only [mem_support,not_not] using hm
      simp only [shortParent,hm,ite_false,hn]

end IntervalForest

private theorem longDataToForest_surjective : Function.Surjective (@longDataToForest n k) := by
  intro T
  obtain ⟨v,hv⟩ := T.property.2
  obtain ⟨p,hp,hpv⟩ := hv.1
  have hv2 : 2 <= v.val := by omega
  have hvm := (IntervalForest.mem_support T.val v).mpr (by simp [hp])
  let w : Fin (n+1) := ⟨v.val-1,by have := v.isLt; omega⟩
  have hpw : p < w := by change p.val < v.val-1; omega
  have hwv : w <= v := by change v.val-1 <= v.val; omega
  have hwm := (IntervalForest.mem_support T.val w).mpr (T.val.no_skipped_root hp hpw hwv)
  let d : LongData n k := ⟨(v,(support T.val)),(positive_support T.val),T.property.1,hvm,hv2,hwm⟩
  refine ⟨d,?_⟩
  apply Subtype.ext
  exact ((eq_oneLongForest T.val) v hv hv2 hvm hwm).symm

private noncomputable def longDataEquiv (n k : Nat) :
    LongData n k ≃ {P : IntervalForest n // (edgeCount P) = k ∧ OneLong P} :=
  Equiv.ofBijective longDataToForest ⟨longDataToForest_injective,longDataToForest_surjective⟩

end D5.S3.Combinatorics.PriorityLattice.LowRankForests

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests

variable {n : Nat}

private def longVertex (a : Fin (n-1)) : Fin (n+1) := ⟨a.val+2,by have := a.isLt; omega⟩
private def priorVertex (a : Fin (n-1)) : Fin (n+1) := ⟨a.val+1,by have := a.isLt; omega⟩
private def longPair (a : Fin (n-1)) : Finset (Fin (n+1)) := {priorVertex a,longVertex a}

private theorem prior_ne_long (a : Fin (n-1)) : priorVertex a ≠ longVertex a := by
  intro h
  have := congrArg Fin.val h
  dsimp [priorVertex,longVertex] at this
  omega

@[simp] private theorem longPair_card (a : Fin (n-1)) : (longPair a).card = 2 := by
  simp [longPair,prior_ne_long a]

private theorem longPair_positive (a : Fin (n-1)) : PositiveSupport (longPair a) := by
  intro v hv
  simp only [longPair,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> dsimp [priorVertex,longVertex] <;> omega

private def longPairData (a : Fin (n-1)) : LongData n 2 :=
  ⟨(longVertex a,longPair a),longPair_positive a,longPair_card a,
    by simp [longPair],by dsimp [longVertex]; omega,by
      have hh : (⟨(longVertex a).val-1,by have := (longVertex a).isLt; omega⟩ : Fin (n+1)) =
          priorVertex a := by apply Fin.ext; dsimp [longVertex,priorVertex] <;> omega
      rw [hh]; simp [longPair]⟩

private def longDataIndex {k : Nat} (d : LongData n k) : Fin (n-1) :=
  ⟨d.val.1.val-2,by have := d.val.1.isLt; have := d.property.2.2.2.1; omega⟩

@[simp] private theorem longVertex_dataIndex {k : Nat} (d : LongData n k) :
    longVertex (longDataIndex d) = d.val.1 := by
  apply Fin.ext
  have := d.property.2.2.2.1
  dsimp [longVertex,longDataIndex]
  omega

private theorem longPair_subset_data {k : Nat} (d : LongData n k) :
    longPair (longDataIndex d) ⊆ d.val.2 := by
  intro v hv
  simp only [longPair,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · have hh : priorVertex (longDataIndex d) =
        (⟨d.val.1.val-1,by have := d.val.1.isLt; omega⟩ : Fin (n+1)) := by
      apply Fin.ext
      have := d.property.2.2.2.1
      dsimp [priorVertex,longDataIndex]
      omega
    rw [hh]
    exact d.property.2.2.2.2
  · rw [longVertex_dataIndex]
    exact d.property.2.2.1

private theorem longPairData_right_inv (d : LongData n 2) : longPairData (longDataIndex d) = d := by
  apply Subtype.ext
  apply Prod.ext
  · exact longVertex_dataIndex d
  · change longPair (longDataIndex d) = d.val.2
    apply Finset.eq_of_subset_of_card_le (longPair_subset_data d)
    rw [longPair_card,d.property.2.1]

private def longPairEquiv (n : Nat) : Fin (n-1) ≃ LongData n 2 where
  toFun := longPairData
  invFun := longDataIndex
  left_inv a := by apply Fin.ext; dsimp [longDataIndex,longPairData,longVertex]; omega
  right_inv := longPairData_right_inv

theorem long_two_card (n : Nat) :
    Nat.card {P : IntervalForest n // (edgeCount P) = 2 ∧ OneLong P} = n-1 := by
  rw [← Nat.card_congr (longDataEquiv n 2),← Nat.card_congr (longPairEquiv n),Nat.card_fin]

end D5.S3.Combinatorics.PriorityLattice.LowRankForests

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests

variable {n : Nat}

private def AllowedExtra (a : Fin (n-1)) := {j : Fin n // j.val ≠ a.val ∧ j.val ≠ a.val+1}
private def TripleParams (n : Nat) := Σ a : Fin (n-1), AllowedExtra a

private theorem allowedExtra_not_pair (a : Fin (n-1)) (j : AllowedExtra a) :
    j.val.succ ∉ longPair a := by
  simp only [longPair,Finset.mem_insert,Finset.mem_singleton,not_or]
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change j.val.val+1 = a.val+1 at hv
    exact j.property.1 (by omega)
  · intro h
    have hv := congrArg Fin.val h
    change j.val.val+1 = a.val+2 at hv
    exact j.property.2 (by omega)

private def tripleData (T : TripleParams n) : LongData n 3 := by
  refine ⟨(longVertex T.1,insert T.2.val.succ (longPair T.1)),?_,?_,?_,?_,?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · exact longPair_positive T.1 v hv
  · rw [Finset.card_insert_of_notMem (allowedExtra_not_pair T.1 T.2),longPair_card]
  · exact Finset.mem_insert_of_mem (by simp [longPair])
  · dsimp [longVertex]; omega
  · have hh : (⟨(longVertex T.1).val-1,by have := (longVertex T.1).isLt; omega⟩ : Fin (n+1)) =
        priorVertex T.1 := by apply Fin.ext; dsimp [longVertex,priorVertex] <;> omega
    rw [hh]
    exact Finset.mem_insert_of_mem (by simp [longPair])

private theorem tripleData_injective : Function.Injective (@tripleData n) := by
  rintro ⟨a,j⟩ ⟨b,l⟩ h
  have hv := congrArg (fun d : LongData n 3 => d.val.1.val) h
  change a.val+2 = b.val+2 at hv
  have hab : a = b := Fin.ext (by omega)
  subst b
  have hs := congrArg (fun d : LongData n 3 => d.val.2) h
  change insert j.val.succ (longPair a) = insert l.val.succ (longPair a) at hs
  have hj : j.val.succ ∈ insert l.val.succ (longPair a) := hs ▸ Finset.mem_insert_self _ _
  have heq : j.val.succ = l.val.succ := (Finset.mem_insert.mp hj).resolve_right (allowedExtra_not_pair a j)
  have hsub : j = l := Subtype.ext (Fin.ext (by have := congrArg Fin.val heq; dsimp at this; omega))
  rw [hsub]

private theorem tripleData_surjective : Function.Surjective (@tripleData n) := by
  intro d
  classical
  let a := longDataIndex d
  have hsub := longPair_subset_data d
  have hcard : (d.val.2 \ longPair a).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub,d.property.2.1,longPair_card]
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hcard
  have hwm : w ∈ d.val.2 \ longPair a := by rw [hw]; simp
  have hws := (Finset.mem_sdiff.mp hwm).1
  have hwn := (Finset.mem_sdiff.mp hwm).2
  have hwpos := d.property.1 w hws
  let j : Fin n := ⟨w.val-1,by have := w.isLt; omega⟩
  have hjw : j.succ = w := by apply Fin.ext; dsimp [j]; omega
  have hj : j.val ≠ a.val ∧ j.val ≠ a.val+1 := by
    constructor
    · intro he
      apply hwn
      have hew : w = priorVertex a := by apply Fin.ext; have := congrArg Fin.val hjw; dsimp [priorVertex] at *; omega
      rw [hew]; simp [longPair]
    · intro he
      apply hwn
      have hew : w = longVertex a := by apply Fin.ext; have := congrArg Fin.val hjw; dsimp [longVertex] at *; omega
      rw [hew]; simp [longPair]
  refine ⟨⟨a,⟨j,hj⟩⟩,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact longVertex_dataIndex d
  · change insert j.succ (longPair a) = d.val.2
    rw [hjw]
    ext v
    constructor
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hws
      · exact hsub hv
    · intro hv
      by_cases hm : v ∈ longPair a
      · exact Finset.mem_insert_of_mem hm
      · have hd : v ∈ d.val.2 \ longPair a := Finset.mem_sdiff.mpr ⟨hv,hm⟩
        rw [hw,Finset.mem_singleton] at hd
        exact Finset.mem_insert.mpr (Or.inl hd)

private noncomputable def tripleDataEquiv (n : Nat) : TripleParams n ≃ LongData n 3 :=
  Equiv.ofBijective tripleData ⟨tripleData_injective,tripleData_surjective⟩

private theorem allowedExtra_card (a : Fin (n-1)) : Nat.card (AllowedExtra a) = n-2 := by
  let b : Fin n := ⟨a.val,by have := a.isLt; omega⟩
  let c : Fin n := ⟨a.val+1,by have := a.isLt; omega⟩
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
  let s : Finset (Fin n) := Finset.univ \ {b,c}
  have he : AllowedExtra a ≃ s := Equiv.subtypeEquivRight (by
    intro j
    change (j.val ≠ a.val ∧ j.val ≠ a.val+1) ↔ j ∈ s
    simp [s,b,c,Fin.ext_iff])
  rw [Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_coe]
  dsimp only [s]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [hbc]

theorem long_three_card (n : Nat) :
    Nat.card {P : IntervalForest n // (edgeCount P) = 3 ∧ OneLong P} = (n-1)*(n-2) := by
  rw [← Nat.card_congr (longDataEquiv n 3),← Nat.card_congr (tripleDataEquiv n)]
  change Nat.card (Σ a : Fin (n-1), AllowedExtra a) = _
  haveI : ∀ a : Fin (n-1), Finite (AllowedExtra a) := fun a => by
    unfold AllowedExtra
    infer_instance
  rw [Nat.card_sigma]
  simp_rw [allowedExtra_card]
  simp

end D5.S3.Combinatorics.PriorityLattice.LowRankForests

namespace D5.S3.Combinatorics.PriorityLattice.LowRankForests

variable {n : Nat}

private noncomputable def singleEdge (i : Fin n) : IntervalForest n :=
  shortForest {i.succ} (by intro v hv; have hv' := Finset.mem_singleton.mp hv; subst v; simp)

@[simp] private theorem singleEdge_support (i : Fin n) : (support (singleEdge i)) = {i.succ} :=
  shortForest_support _ _

@[simp] private theorem singleEdge_count (i : Fin n) : (edgeCount (singleEdge i)) = 1 := by
  change (support (singleEdge i)).card = 1
  rw [singleEdge_support,Finset.card_singleton]

namespace IntervalForest

private theorem edgeCount_one_short (P : IntervalForest n) (h : (edgeCount P) = 1)
    (v p : Fin (n+1)) (hp : P.parent v = some p) : p.val+1 = v.val := by
  classical
  have hs : (support P).card = 1 := h
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hs
  have hv : v ∈ (support P) := (mem_support P v).mpr (by simp [hp])
  have hvw : v = w := by simpa only [hw,Finset.mem_singleton] using hv
  have hinc := P.increasing v p hp
  let z : Fin (n+1) := ⟨p.val+1,by have := v.isLt; change p.val < v.val at hinc; omega⟩
  have hpz : p < z := by change p.val < p.val+1; omega
  have hzv : z <= v := by change p.val+1 <= v.val; exact Nat.succ_le_of_lt hinc
  have hz : z ∈ (support P) := (mem_support P z).mpr (P.no_skipped_root hp hpz hzv)
  have hzw : z = w := by simpa only [hw,Finset.mem_singleton] using hz
  exact congrArg Fin.val (hzw.trans hvw.symm)

private theorem edgeCount_one_exists_single (P : IntervalForest n) (h : (edgeCount P) = 1) :
    ∃ i : Fin n, P = singleEdge i := by
  classical
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show (support P).card = 1 from h)
  have hvm : v ∈ (support P) := hv ▸ Finset.mem_singleton_self _
  obtain ⟨p,hp⟩ := Option.ne_none_iff_exists'.mp ((mem_support P v).mp hvm)
  have hlen := (edgeCount_one_short P) h v p hp
  let i : Fin n := ⟨p.val,by have := v.isLt; omega⟩
  have hiv : i.succ = v := Fin.ext hlen
  refine ⟨i,?_⟩
  apply ext
  funext w
  by_cases hw : w = v
  · subst w
    rw [hp]
    change some p = shortParent {i.succ} v
    have hmem : v ∈ ({i.succ} : Finset (Fin (n+1))) := by rw [hiv]; simp
    simp only [shortParent,hmem,ite_true,Option.some.injEq]
    apply Fin.ext
    dsimp
    omega
  · have hwn : P.parent w = none := by
      have hnot : w ∉ (support P) := by rw [hv]; simpa using hw
      simpa only [mem_support,not_not] using hnot
    rw [hwn]
    change none = shortParent {i.succ} w
    have hmem : w ∉ ({i.succ} : Finset (Fin (n+1))) := by rw [hiv]; simpa using hw
    simp [shortParent,hmem]

end IntervalForest

private noncomputable def singleEdgeEquiv (n : Nat) : Fin n ≃ {P : IntervalForest n // (edgeCount P) = 1} := by
  refine Equiv.ofBijective (fun i => ⟨singleEdge i,singleEdge_count i⟩) ?_
  constructor
  · intro i j h
    have hs := congrArg (fun P => (support P.val)) h
    simp only [singleEdge_support,Finset.singleton_inj] at hs
    exact Fin.ext (by have := congrArg Fin.val hs; dsimp at this; omega)
  · intro P
    obtain ⟨i,hi⟩ := (edgeCount_one_exists_single P.val) P.property
    exact ⟨i,Subtype.ext hi.symm⟩

theorem single_edges_card (n : Nat) : Nat.card {P : IntervalForest n // (edgeCount P) = 1} = n := by
  rw [← Nat.card_congr (singleEdgeEquiv n),Nat.card_fin]

end D5.S3.Combinatorics.PriorityLattice.LowRankForests
