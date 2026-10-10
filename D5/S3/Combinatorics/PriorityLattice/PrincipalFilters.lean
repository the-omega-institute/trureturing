/- GID: D5/S3/Combinatorics/PriorityLattice/PrincipalFilters
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/PrincipalFilters
   mirror-E: none(waiver:general-priority-lattice-counting)
   anchors: []
   utility: none
   digest: Priority-forest interval structure and counting. -/

/-
admission_basis: open-problem-resolution (#14857; Proved)
escape_witness: none
Direct frozen dependencies: none; direct D5 dependencies are supplied by this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14955
Proof shapes expand all same-delivery declarations and apply the upstream-only bypass test.
IntervalForest.GraftData: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graft
IntervalForest.graft: proof_shape: content
IntervalForest.graft_bounds: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graft_cover
IntervalForest.graft_count: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graft_cover
IntervalForest.graft_cover: proof_shape: content
IntervalForest.graft_injective: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graftCoverEquiv
IntervalForest.graftCoverEquiv: proof_shape: content
IntervalForest.roots: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graftParentEquiv
IntervalForest.mem_roots: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graftParentEquiv
IntervalForest.roots_nonempty: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.lastRoot
IntervalForest.lastRoot: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.empty_not_tree
IntervalForest.parent_lastRoot: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graftParentEquiv
IntervalForest.root_le_lastRoot: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graftParentEquiv
IntervalForest.roots_card: proof_shape: bind-only; consumer: PrincipalFilters.filter_iso_singleton_prefix
IntervalForest.graftParentEquiv: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graft_card
IntervalForest.prefixFinEquiv: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.graft_card
IntervalForest.graft_card: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.upper_forest_covers_card
IntervalForest.upper_forest_covers_card: proof_shape: content
withTopIciForward: proof_shape: bind-only; consumer: PrincipalFilters.withTopIciOrderIso
withTopIciBackward: proof_shape: bind-only; consumer: PrincipalFilters.withTopIciOrderIso
withTopIciOrderIso: proof_shape: bind-only; consumer: PrincipalFilters.principalFilterContraction
SingletonPrefix: proof_shape: bind-only; consumer: PrincipalFilters.contract_expand
prefixEmbed: proof_shape: bind-only; consumer: PrincipalFilters.contractForest
prefixEmbed_injective: proof_shape: bind-only; consumer: PrincipalFilters.option_prefixEmbed_injective
contractForest: proof_shape: content
expandForest: proof_shape: content
expand_parent_prefix: proof_shape: bind-only; consumer: PrincipalFilters.contract_expand
expand_parent_suffix: proof_shape: bind-only; consumer: PrincipalFilters.expand_above
contract_parent_map: proof_shape: bind-only; consumer: PrincipalFilters.contract_expand
option_prefixEmbed_injective: proof_shape: bind-only; consumer: PrincipalFilters.contract_expand
contract_expand: proof_shape: bind-only; consumer: PrincipalFilters.contractionOrderIso
expand_above: proof_shape: bind-only; consumer: PrincipalFilters.contractionOrderIso
expand_contract: proof_shape: bind-only; consumer: PrincipalFilters.contractionOrderIso
expand_le_iff: proof_shape: bind-only; consumer: PrincipalFilters.contractionOrderIso
contractionOrderIso: proof_shape: content
principalFilterContraction: proof_shape: content
qualifies_filter_of_singleton_prefix: proof_shape: content
filterAtomEquiv: proof_shape: content
filter_atoms_card: proof_shape: content
IntervalForest.lastRoot_empty: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.empty_not_tree
IntervalForest.tree_iff_lastRoot_zero: proof_shape: bind-only; consumer: PrincipalFilters.IntervalForest.empty_not_tree
IntervalForest.empty_not_tree: proof_shape: bind-only; consumer: PrincipalFilters.pi_atoms_card
pi_atoms_card: proof_shape: content
IntervalForest.singletonPrefix_of_roots_card: proof_shape: bind-only; consumer: PrincipalFilters.filter_iso_singleton_prefix
IntervalForest.singletonPrefix_of_tree: proof_shape: bind-only; consumer: PrincipalFilters.filter_iso_singleton_prefix
filter_iso_singleton_prefix: proof_shape: content
forest_filter_qualifies_iff: proof_shape: content
suffixVertex: proof_shape: bind-only; consumer: PrincipalFilters.suffixToCode
suffix_parent_exists: proof_shape: content
suffixToCode: proof_shape: content
suffixToCode_parent: proof_shape: content
suffixCodeParent: proof_shape: bind-only; consumer: PrincipalFilters.suffixCodeForest
suffixCodeParent_none: proof_shape: bind-only; consumer: PrincipalFilters.suffixCodeForest
suffixCodeForest: proof_shape: content
suffixCodeForest_prefix: proof_shape: bind-only; consumer: PrincipalFilters.suffixForestEquivCode
suffix_code_left_inv: proof_shape: bind-only; consumer: PrincipalFilters.suffixForestEquivCode
suffix_code_right_inv: proof_shape: bind-only; consumer: PrincipalFilters.suffixForestEquivCode
suffixForestEquivCode: proof_shape: content
singleton_prefix_card: proof_shape: content
singletonPrefix_lastRoot: proof_shape: bind-only; consumer: PrincipalFilters.qualifyingFilterEquiv
qualifyingFilterEquiv: proof_shape: content
theta_sum: proof_shape: content
filterCountResult: proof_shape: content
PriorityForest: proof_shape: bind-only; consumer: PrincipalFilters.Pi
PriorityForest.ext: proof_shape: bind-only; consumer: PrincipalFilters.PriorityForest.edges_injective
PriorityForest.toCore: proof_shape: bind-only; consumer: PrincipalFilters.PriorityForest.edges_injective
PriorityForest.ofCore: proof_shape: bind-only; consumer: PrincipalFilters.PriorityForest.forestToCoreOrderIso
PriorityForest.edges: proof_shape: bind-only; consumer: PrincipalFilters.PriorityForest.edges_injective
PriorityForest.edges_injective: proof_shape: bind-only; consumer: PrincipalFilters.PriorityForest.forestPartialOrder
PriorityForest.forestPartialOrder: proof_shape: bind-only; consumer: PrincipalFilters.PriorityForest.forestToCoreOrderIso
PriorityForest.forestFinite: proof_shape: bind-only; consumer: PrincipalFilters.theta_transfer
PriorityForest.forestToCoreOrderIso: proof_shape: bind-only; consumer: PrincipalFilters.coreOrderIso
Pi: proof_shape: bind-only; consumer: PrincipalFilters.filter_qualification_transfer
theta: proof_shape: bind-only; consumer: PrincipalFilters.claimTheta
claimTheta: proof_shape: bind-only; consumer: PrincipalFilters.result (statement type)
coreOrderIso: proof_shape: bind-only; consumer: PrincipalFilters.filter_qualification_transfer
iciCongr: proof_shape: bind-only; consumer: PrincipalFilters.filter_qualification_transfer
filter_qualification_transfer: proof_shape: bind-only; consumer: PrincipalFilters.theta_transfer
theta_transfer: proof_shape: bind-only; consumer: PrincipalFilters.result
result: proof_shape: content
-/

import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Algebra.BigOperators.Intervals
import D5.S3.Combinatorics.PriorityLattice.ForestCovers

open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.ForestCovers
open D5.S3.Combinatorics.PriorityLattice.ForestCovers.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.IntervalForest
end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
namespace IntervalForest

variable {n : Nat}

private def GraftData (P : IntervalForest n) :=
  {e : Fin (n+1) × Fin (n+1) // P.parent e.2 = none ∧ e.1 < e.2 ∧
    forall w, e.1 < w -> w < e.2 -> P.parent w ≠ none}

private def graft (P : IntervalForest n) (e : GraftData P) : IntervalForest n :=
  forestOfLocal (Function.update P.parent e.val.2 (some e.val.1))
    (by
      intro w q hw
      by_cases hwe : w = e.val.2
      · subst w; simp only [Function.update_self,Option.some.injEq] at hw
        subst q; exact e.property.2.1
      · rw [Function.update_of_ne hwe] at hw
        exact P.increasing w q hw)
    (by
      intro w q z hw hqz hzw
      by_cases hze : z = e.val.2
      · subst z; simp
      · rw [Function.update_of_ne hze]
        by_cases hwe : w = e.val.2
        · subst w
          simp only [Function.update_self,Option.some.injEq] at hw
          subst q
          exact e.property.2.2 z hqz (lt_of_le_of_ne hzw hze)
        · rw [Function.update_of_ne hwe] at hw
          exact P.no_skipped_root hw hqz hzw)

private theorem graft_bounds (P : IntervalForest n) (e : GraftData P) : P < (graft P) e := by
  apply lt_of_le_of_ne
  · rw [le_iff_parent]
    intro v p hp
    have hve : v ≠ e.val.2 := by intro he; subst v; rw [e.property.1] at hp; cases hp
    change Function.update P.parent e.val.2 (some e.val.1) v = some p
    rwa [Function.update_of_ne hve]
  · intro heq
    have hp := congrArg (fun Q : IntervalForest n => Q.parent e.val.2) heq
    change P.parent e.val.2 = Function.update P.parent e.val.2 (some e.val.1) e.val.2 at hp
    simp [e.property.1] at hp

private theorem graft_count (P : IntervalForest n) (e : GraftData P) :
    (edgeCount ((graft P) e)) = (edgeCount P)+1 := by
  classical
  have hs : (support ((graft P) e)) = insert e.val.2 (support P) := by
    ext v
    simp only [mem_support,Finset.mem_insert]
    change Function.update P.parent e.val.2 (some e.val.1) v ≠ none <-> v = e.val.2 ∨ P.parent v ≠ none
    by_cases hv : v = e.val.2
    · subst v; simp
    · simp [hv]
  unfold edgeCount
  rw [hs,Finset.card_insert_of_notMem]
  simpa [e.property.1]

private theorem graft_cover (P : IntervalForest n) (e : GraftData P) : P ⋖ (graft P) e :=
  covBy_iff_edgeCount.mpr ⟨(graft_bounds P) e,(graft_count P) e⟩

private theorem graft_injective (P : IntervalForest n) : Function.Injective ((graft P)) := by
  intro e f h
  apply Subtype.ext
  have hechild : e.val.2 = f.val.2 := by
    by_contra hne
    have hp := congrArg (fun Q : IntervalForest n => Q.parent e.val.2) h
    change Function.update P.parent e.val.2 (some e.val.1) e.val.2 =
      Function.update P.parent f.val.2 (some f.val.1) e.val.2 at hp
    simp [Function.update_of_ne hne,e.property.1] at hp
  have hpp := congrArg (fun Q : IntervalForest n => Q.parent e.val.2) h
  change Function.update P.parent e.val.2 (some e.val.1) e.val.2 =
    Function.update P.parent f.val.2 (some f.val.1) e.val.2 at hpp
  rw [hechild] at hpp
  simp only [Function.update_self,Option.some.injEq] at hpp
  exact Prod.ext hpp hechild

private noncomputable def graftCoverEquiv (P : IntervalForest n) : GraftData P ≃ {Q // P ⋖ Q} := by
  refine Equiv.ofBijective (fun e => ⟨(graft P) e,(graft_cover P) e⟩) ?_
  constructor
  · intro e f h
    exact (graft_injective P) (congrArg Subtype.val h)
  · intro Q
    obtain ⟨v,p,hPv,hQv,hpv,hmid,hsame⟩ := cover_adjacent_roots Q.property
    refine ⟨⟨(p,v),hPv,hpv,hmid⟩,?_⟩
    apply Subtype.ext
    apply ext
    funext w
    by_cases hw : w = v
    · subst w
      change Function.update P.parent v (some p) v = Q.val.parent v
      rw [Function.update_self,hQv]
    · change Function.update P.parent v (some p) w = Q.val.parent w
      rw [Function.update_of_ne hw,hsame w hw]

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
namespace IntervalForest

variable {n : Nat}

noncomputable def roots (P : IntervalForest n) : Finset (Fin (n+1)) :=
  by classical exact Finset.univ.filter (fun v => P.parent v = none)

@[simp] private theorem mem_roots (P : IntervalForest n) (v : Fin (n+1)) :
    v ∈ (roots P) <-> P.parent v = none := by classical simp [roots]

theorem roots_nonempty (P : IntervalForest n) : (roots P).Nonempty :=
  ⟨0,(mem_roots P 0).mpr P.parent_zero⟩

noncomputable def lastRoot (P : IntervalForest n) : Fin (n+1) := (roots P).max' (roots_nonempty P)

private theorem parent_lastRoot (P : IntervalForest n) : P.parent (lastRoot P) = none := by
  exact (mem_roots P _).mp (Finset.max'_mem _ _)

private theorem root_le_lastRoot (P : IntervalForest n) {v : Fin (n+1)} (hv : P.parent v = none) :
    v <= (lastRoot P) := by
  exact Finset.le_max' _ _ ((mem_roots P v).mpr hv)

private theorem roots_card (P : IntervalForest n) : (roots P).card = n+1-(edgeCount P) := by
  classical
  have hs : (roots P) = Finset.univ \ (support P) := by ext v; simp
  rw [hs,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ,Fintype.card_fin]
  rfl

private noncomputable def graftParentEquiv (P : IntervalForest n) :
    GraftData P ≃ {p : Fin (n+1) // p < (lastRoot P)} := by
  refine Equiv.ofBijective (fun e => ⟨e.val.1,?_⟩) ?_
  · exact e.property.2.1.trans_le ((root_le_lastRoot P) e.property.1)
  · constructor
    · intro e f h
      apply Subtype.ext
      have hp := congrArg Subtype.val h
      change e.val.1 = f.val.1 at hp
      apply Prod.ext hp
      rcases lt_trichotomy e.val.2 f.val.2 with hef | hef | hfe
      · exact (f.property.2.2 e.val.2 (hp ▸ e.property.2.1) hef e.property.1).elim
      · exact hef
      · exact (e.property.2.2 f.val.2 (hp.symm ▸ f.property.2.1) hfe f.property.1).elim
    · intro p
      classical
      let R := (roots P).filter (fun v => p.val < v)
      have hR : R.Nonempty := by
        refine ⟨(lastRoot P),Finset.mem_filter.mpr ⟨?_,p.property⟩⟩
        exact (mem_roots P _).mpr (parent_lastRoot P)
      let v := R.min' hR
      have hv := Finset.mem_filter.mp (Finset.min'_mem R hR)
      have hroot := (mem_roots P v).mp hv.1
      have hmid : forall w, p.val < w -> w < v -> P.parent w ≠ none := by
        intro w hpw hwv hw
        have hwm : w ∈ R := Finset.mem_filter.mpr ⟨(mem_roots P w).mpr hw,hpw⟩
        have hmin : v <= w := Finset.min'_le _ _ hwm
        exact (not_lt_of_ge hmin) hwv
      exact ⟨⟨(p.val,v),hroot,hv.2,hmid⟩,rfl⟩

private def prefixFinEquiv (a : Fin (n+1)) : {p : Fin (n+1) // p < a} ≃ Fin a.val where
  toFun p := ⟨p.val.val,p.property⟩
  invFun p := ⟨⟨p.val,by have := p.isLt; omega⟩,p.isLt⟩
  left_inv p := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv p := by apply Fin.ext; rfl

private theorem graft_card (P : IntervalForest n) : Nat.card (GraftData P) = (lastRoot P).val := by
  rw [Nat.card_congr ((graftParentEquiv P).trans (prefixFinEquiv (lastRoot P))),Nat.card_fin]

private theorem upper_forest_covers_card (P : IntervalForest n) :
    Nat.card {Q : IntervalForest n // P ⋖ Q} = (lastRoot P).val := by
  rw [← Nat.card_congr (graftCoverEquiv P)]
  exact (graft_card P)

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

private def withTopIciForward {A : Type*} [PartialOrder A] (a : A) :
    WithTop (Set.Ici a) -> Set.Ici (a : WithTop A)
  | none => ⟨⊤,by change (a : WithTop A) <= ⊤; exact le_top⟩
  | some b => ⟨(b.val : WithTop A),WithTop.coe_le_coe.mpr b.property⟩

private def withTopIciBackward {A : Type*} [PartialOrder A] (a : A)
    (y : Set.Ici (a : WithTop A)) : WithTop (Set.Ici a) :=
  match h : y.val with
  | none => none
  | some b => some ⟨b,WithTop.coe_le_coe.mp (by
      have hh : (a : WithTop A) <= y.val := y.property
      rw [h] at hh
      exact hh)⟩

private def withTopIciOrderIso {A : Type*} [PartialOrder A] (a : A) :
    WithTop (Set.Ici a) ≃o Set.Ici (a : WithTop A) where
  toFun := withTopIciForward a
  invFun := withTopIciBackward a
  left_inv y := by cases y <;> rfl
  right_inv y := by rcases y with ⟨y,h⟩; cases y <;> rfl
  map_rel_iff' := by
    intro x y
    cases x with
    | top =>
      cases y with
      | top => exact iff_of_true le_rfl le_rfl
      | coe y =>
        change (⊤ : WithTop A) <= (y.val : WithTop A) <-> (⊤ : WithTop (Set.Ici a)) <= y
        simp
    | coe x =>
      cases y with
      | top =>
        change (x.val : WithTop A) <= ⊤ <-> (x : WithTop (Set.Ici a)) <= ⊤
        simp
      | coe y =>
        change (x.val : WithTop A) <= (y.val : WithTop A) <-> (x : WithTop (Set.Ici a)) <= y
        simp only [WithTop.coe_le_coe]
        rfl

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

variable {n : Nat}

def SingletonPrefix (P : IntervalForest n) (a : Fin (n+1)) : Prop :=
  (forall v, v <= a -> P.parent v = none) ∧
  (forall v, a < v -> P.parent v ≠ none)

private def prefixEmbed (a : Fin (n+1)) : Fin (a.val+1) -> Fin (n+1) :=
  fun v => ⟨v.val, by omega⟩

private theorem prefixEmbed_injective (a : Fin (n+1)) : Function.Injective (prefixEmbed a) := by
  intro u v h
  exact Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h)

private def contractForest (a : Fin (n+1)) (Q : IntervalForest n) : IntervalForest a.val :=
  forestOfLocal
    (fun v => (Q.parent (prefixEmbed a v)).map (fun p =>
      if hp : p.val < a.val+1 then (⟨p.val,hp⟩ : Fin (a.val+1)) else 0))
    (by
      intro v p h
      cases hv : Q.parent (prefixEmbed a v) with
      | none => simp [hv] at h
      | some q =>
        have hq := Q.increasing _ _ hv
        have hql : q.val < a.val+1 := by have hvb := v.isLt; change q.val < v.val at hq; omega
        simp only [hv, Option.map_some, dif_pos hql, Option.some.injEq] at h
        subst p
        exact hq)
    (by
      intro v p w hp hpw hwv hw
      cases hv : Q.parent (prefixEmbed a v) with
      | none => simp [hv] at hp
      | some q =>
        have hq := Q.increasing _ _ hv
        have hql : q.val < a.val+1 := by have hvb := v.isLt; change q.val < v.val at hq; omega
        simp only [hv, Option.map_some, dif_pos hql, Option.some.injEq] at hp
        subst p
        have hqw : q < prefixEmbed a w := hpw
        have hwv' : prefixEmbed a w <= prefixEmbed a v := hwv
        have hnon := Q.no_skipped_root hv hqw hwv'
        cases hh : Q.parent (prefixEmbed a w) with
        | none => exact hnon hh
        | some t => simp [hh] at hw)

private def expandForest (P : IntervalForest n) (a : Fin (n+1)) (hP : SingletonPrefix P a)
    (S : IntervalForest a.val) : IntervalForest n :=
  forestOfLocal
    (fun v => if hv : v.val <= a.val then
      (S.parent ⟨v.val,by omega⟩).map (prefixEmbed a) else P.parent v)
    (by
      intro v p hp
      by_cases hv : v.val <= a.val
      · simp only [hv,dite_true] at hp
        cases hs : S.parent ⟨v.val,by omega⟩ with
        | none => simp [hs] at hp
        | some q =>
          simp only [hs,Option.map_some,Option.some.injEq] at hp
          have hq := S.increasing _ _ hs
          rw [← hp]
          exact hq
      · simp only [hv,dite_false] at hp
        exact P.increasing v p hp)
    (by
      intro v p w hp hpw hwv hw
      by_cases hv : v.val <= a.val
      · simp only [hv,dite_true] at hp
        cases hs : S.parent ⟨v.val,by omega⟩ with
        | none => simp [hs] at hp
        | some q =>
          simp only [hs,Option.map_some,Option.some.injEq] at hp
          have hwbound : w.val <= a.val := by exact le_trans hwv hv
          have hqw : q < (⟨w.val,by omega⟩ : Fin (a.val+1)) := by rw [← hp] at hpw; exact hpw
          have hwv' : (⟨w.val,by omega⟩ : Fin (a.val+1)) <= ⟨v.val,by omega⟩ := hwv
          have hn := S.no_skipped_root hs hqw hwv'
          simp only [hwbound,dite_true] at hw
          cases hsw : S.parent ⟨w.val,by omega⟩ with
          | none => exact hn hsw
          | some t => simp [hsw] at hw
      · simp only [hv,dite_false] at hp
        have hpa : a <= p := by
          by_contra hpa
          have hparoot := hP.1 a le_rfl
          have hav : a <= v := by change a.val <= v.val; omega
          exact P.no_skipped_root hp (lt_of_not_ge hpa) hav hparoot
        have hwa : a < w := hpa.trans_lt hpw
        have hw' : ¬ w.val <= a.val := not_le.mpr hwa
        simp only [hw',dite_false] at hw
        exact hP.2 w hwa hw)

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

variable {n : Nat}

private theorem expand_parent_prefix (P : IntervalForest n) (a : Fin (n+1)) (hP : SingletonPrefix P a)
    (S : IntervalForest a.val) (v : Fin (a.val+1)) :
    (expandForest P a hP S).parent (prefixEmbed a v) = (S.parent v).map (prefixEmbed a) := by
  have hv : (prefixEmbed a v).val <= a.val := Nat.le_of_lt_succ v.isLt
  change (if hv' : (prefixEmbed a v).val <= a.val then
    (S.parent ⟨(prefixEmbed a v).val,by omega⟩).map (prefixEmbed a) else _) = _
  rw [dif_pos hv]
  rfl

private theorem expand_parent_suffix (P : IntervalForest n) (a : Fin (n+1)) (hP : SingletonPrefix P a)
    (S : IntervalForest a.val) (v : Fin (n+1)) (hv : a < v) :
    (expandForest P a hP S).parent v = P.parent v := by
  change (if hv' : v.val <= a.val then _ else _) = _
  have hv' : ¬ v.val <= a.val := not_le.mpr hv
  rw [dif_neg hv']

private theorem contract_parent_map (a : Fin (n+1)) (Q : IntervalForest n) (v : Fin (a.val+1)) :
    ((contractForest a Q).parent v).map (prefixEmbed a) = Q.parent (prefixEmbed a v) := by
  change ((Q.parent (prefixEmbed a v)).map (fun p =>
      if hp : p.val < a.val+1 then (⟨p.val,hp⟩ : Fin (a.val+1)) else 0)).map (prefixEmbed a) = _
  cases hp : Q.parent (prefixEmbed a v) with
  | none => rfl
  | some p =>
    have hlt := Q.increasing _ _ hp
    have hpbound : p.val < a.val+1 := by
      change p.val < v.val at hlt
      have := v.isLt
      omega
    simp only [Option.map_some,dif_pos hpbound]
    rfl

private theorem option_prefixEmbed_injective (a : Fin (n+1)) :
    Function.Injective (Option.map (prefixEmbed a)) := by
  exact Option.map_injective (prefixEmbed_injective a)

private theorem contract_expand (P : IntervalForest n) (a : Fin (n+1)) (hP : SingletonPrefix P a)
    (S : IntervalForest a.val) : contractForest a (expandForest P a hP S) = S := by
  apply IntervalForest.ext
  funext v
  apply option_prefixEmbed_injective a
  rw [contract_parent_map,expand_parent_prefix]

private theorem expand_above (P : IntervalForest n) (a : Fin (n+1)) (hP : SingletonPrefix P a)
    (S : IntervalForest a.val) : P <= expandForest P a hP S := by
  rw [IntervalForest.le_iff_parent]
  intro v p hp
  by_cases hv : v <= a
  · rw [hP.1 v hv] at hp
    cases hp
  · rw [expand_parent_suffix P a hP S v (lt_of_not_ge hv)]
    exact hp

private theorem expand_contract (P : IntervalForest n) (a : Fin (n+1)) (hP : SingletonPrefix P a)
    (Q : IntervalForest n) (hPQ : P <= Q) : expandForest P a hP (contractForest a Q) = Q := by
  apply IntervalForest.ext
  funext v
  by_cases hv : v <= a
  · let w : Fin (a.val+1) := ⟨v.val,Nat.lt_succ_of_le hv⟩
    have hw : prefixEmbed a w = v := rfl
    rw [← hw,expand_parent_prefix,contract_parent_map]
  · rw [expand_parent_suffix P a hP (contractForest a Q) v (lt_of_not_ge hv)]
    have hpv := hP.2 v (lt_of_not_ge hv)
    obtain ⟨p,hp⟩ := Option.ne_none_iff_exists'.mp hpv
    rw [hp,(IntervalForest.le_iff_parent P Q).mp hPQ v p hp]

private theorem expand_le_iff (P : IntervalForest n) (a : Fin (n+1)) (hP : SingletonPrefix P a)
    (S T : IntervalForest a.val) : expandForest P a hP S <= expandForest P a hP T <-> S <= T := by
  rw [IntervalForest.le_iff_parent,IntervalForest.le_iff_parent]
  constructor
  · intro h v p hp
    have he : (expandForest P a hP S).parent (prefixEmbed a v) = some (prefixEmbed a p) := by
      rw [expand_parent_prefix,hp]
      rfl
    have ht := h (prefixEmbed a v) (prefixEmbed a p) he
    rw [expand_parent_prefix] at ht
    apply option_prefixEmbed_injective a
    exact ht
  · intro h v p hp
    by_cases hv : v <= a
    · let w : Fin (a.val+1) := ⟨v.val,Nat.lt_succ_of_le hv⟩
      have hw : prefixEmbed a w = v := rfl
      rw [← hw,expand_parent_prefix] at hp ⊢
      cases hs : S.parent w with
      | none => simp [hs] at hp
      | some q =>
        simp only [hs,Option.map_some,Option.some.injEq] at hp
        rw [h w q hs]
        exact congrArg some hp
    · rw [expand_parent_suffix P a hP S v (lt_of_not_ge hv)] at hp
      rw [expand_parent_suffix P a hP T v (lt_of_not_ge hv)]
      exact hp

private noncomputable def contractionOrderIso (P : IntervalForest n) (a : Fin (n+1))
    (hP : SingletonPrefix P a) : Set.Ici P ≃o IntervalForest a.val where
  toFun := fun Q => contractForest a Q.val
  invFun := fun S => ⟨expandForest P a hP S,expand_above P a hP S⟩
  left_inv Q := Subtype.ext (expand_contract P a hP Q.val Q.property)
  right_inv := contract_expand P a hP
  map_rel_iff' := by
    intro Q R
    have hQ := expand_contract P a hP Q.val Q.property
    have hR := expand_contract P a hP R.val R.property
    change contractForest a Q.val <= contractForest a R.val <-> Q.val <= R.val
    rw [← expand_le_iff P a hP, hQ,hR]

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

noncomputable def principalFilterContraction {n : Nat} (P : IntervalForest n)
    (a : Fin (n+1)) (hP : SingletonPrefix P a) : Set.Ici (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest a.val)) := by
  change Set.Ici (P : WithTop (IntervalForest n)) ≃o WithTop (IntervalForest a.val)
  exact (withTopIciOrderIso P).symm.trans (contractionOrderIso P a hP).withTopCongr

private theorem qualifies_filter_of_singleton_prefix {n : Nat} (P : IntervalForest n)
    (a : Fin (n+1)) (hP : SingletonPrefix P a) :
    ∃ m ≤ n, Nonempty (Set.Ici (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m))) := by
  exact ⟨a.val,Nat.le_of_lt_succ a.isLt,⟨principalFilterContraction P a hP⟩⟩

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

private noncomputable def filterAtomEquiv {n : Nat} (P : IntervalForest n) (hP : ¬ IsTree P) :
    {Q : IntervalForest n // P ⋖ Q} ≃ {x : Set.Ici (P : (WithTop (IntervalForest n))) // IsAtom x} := by
  refine Equiv.ofBijective (fun Q => ⟨⟨(Q.val : (WithTop (IntervalForest n))), by
    change (P : WithTop (IntervalForest n)) <= Q.val
    exact WithTop.coe_le_coe.mpr Q.property.le⟩,?_⟩) ?_
  · rw [Set.Ici.isAtom_iff]
    change (P : WithTop (IntervalForest n)) ⋖ Q.val
    exact WithTop.coe_covBy_coe.mpr Q.property
  · constructor
    · intro Q R h
      apply Subtype.ext
      have hc := congrArg (fun x => x.val.val) h
      exact WithTop.coe_inj.mp hc
    · intro x
      have hx : (P : (WithTop (IntervalForest n))) ⋖ x.val.val := Set.Ici.isAtom_iff.mp x.property
      have hxne : x.val.val ≠ ⊤ := by
        intro heq
        rw [heq] at hx
        exact hP ((coatom_iff_tree P).mp (covBy_top_iff.mp hx))
      change (x.val.val : WithTop (IntervalForest n)) ≠ ⊤ at hxne
      obtain ⟨Q,hQ⟩ := WithTop.ne_top_iff_exists.mp hxne
      have hcov : P ⋖ Q := by
        apply WithTop.coe_covBy_coe.mp
        simpa only [hQ] using hx
      refine ⟨⟨Q,hcov⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hQ

private theorem filter_atoms_card {n : Nat} (P : IntervalForest n) (hP : ¬ IsTree P) :
    Nat.card {x : Set.Ici (P : (WithTop (IntervalForest n))) // IsAtom x} = (lastRoot P).val := by
  rw [← Nat.card_congr (filterAtomEquiv P hP)]
  exact (upper_forest_covers_card P)

namespace IntervalForest

@[simp] private theorem lastRoot_empty (n : Nat) : (lastRoot (empty n)) = Fin.last n := by
  apply le_antisymm
  · exact Fin.le_last _
  · exact (root_le_lastRoot (empty n)) rfl

private theorem tree_iff_lastRoot_zero {n : Nat} (P : IntervalForest n) :
    IsTree P <-> (lastRoot P) = 0 := by
  constructor
  · intro h; exact h _ (parent_lastRoot P)
  · intro h v hv
    have hle := (root_le_lastRoot P) hv
    rw [h] at hle
    exact le_antisymm hle (Fin.zero_le _)

private theorem empty_not_tree {n : Nat} (hn : 1 <= n) : ¬ IsTree (empty n) := by
  rw [tree_iff_lastRoot_zero,lastRoot_empty]
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_zero] at hv
  omega

end IntervalForest

private theorem pi_atoms_card {n : Nat} (hn : 1 <= n) : Nat.card {x : (WithTop (IntervalForest n)) // IsAtom x} = n := by
  have h := filter_atoms_card (IntervalForest.empty n) (IntervalForest.empty_not_tree hn)
  have hc := atom_card_orderIso (OrderIso.IciBot : Set.Ici (⊥ : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest n)))
  change Nat.card {x : Set.Ici ((IntervalForest.empty n : IntervalForest n) : (WithTop (IntervalForest n))) // IsAtom x} =
    Nat.card {x : (WithTop (IntervalForest n)) // IsAtom x} at hc
  rw [hc,IntervalForest.lastRoot_empty] at h
  exact h

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace IntervalForest

variable {n : Nat}

private theorem singletonPrefix_of_roots_card (P : IntervalForest n)
    (hcard : (roots P).card = (lastRoot P).val+1) : SingletonPrefix P (lastRoot P) := by
  classical
  have hsub : (roots P) ⊆ Finset.Iic (lastRoot P) := by
    intro v hv
    exact Finset.mem_Iic.mpr ((root_le_lastRoot P) ((mem_roots P v).mp hv))
  have heq : (roots P) = Finset.Iic (lastRoot P) := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa using hcard.ge
  constructor
  · intro v hv
    exact (mem_roots P v).mp (heq ▸ Finset.mem_Iic.mpr hv)
  · intro v hv h
    exact (not_le_of_gt hv) ((root_le_lastRoot P) h)

private theorem singletonPrefix_of_tree (P : IntervalForest n) (hP : IsTree P) :
    SingletonPrefix P 0 := by
  constructor
  · intro v hv
    have : v = 0 := le_antisymm hv (Fin.zero_le _)
    simpa [this] using P.parent_zero
  · intro v hv h
    exact (ne_of_gt hv) (hP v h)

end IntervalForest

theorem filter_iso_singleton_prefix {n m : Nat} (P : IntervalForest n)
    (e : Set.Ici (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m))) : SingletonPrefix P (lastRoot P) ∧ m = (lastRoot P).val := by
  by_cases hP : IsTree P
  · have hz : (lastRoot P) = 0 := ((tree_iff_lastRoot_zero P)).mp hP
    have hr := filter_iso_rank e
    have hc := ((edgeCount_eq_iff_tree P)).mpr hP
    change m+1 = n+1-(edgeCount P) at hr
    constructor
    · rw [hz]; exact (singletonPrefix_of_tree P) hP
    · simp only [hz,Fin.val_zero]; omega
  · have hr := filter_iso_rank e
    change m+1 = n+1-(edgeCount P) at hr
    have hm : 1 <= m := by
      have hc := (edgeCount_le P)
      by_contra h
      have he : (edgeCount P) = n := by omega
      exact hP (((edgeCount_eq_iff_tree P)).mp he)
    have ha := atom_card_orderIso e
    rw [filter_atoms_card P hP,pi_atoms_card hm] at ha
    constructor
    · apply (singletonPrefix_of_roots_card P)
      rw [(roots_card P)]
      omega
    · exact ha.symm

private theorem forest_filter_qualifies_iff {n : Nat} (P : IntervalForest n) :
    (∃ m ≤ n, Nonempty (Set.Ici (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m)))) ↔
      SingletonPrefix P (lastRoot P) := by
  constructor
  · rintro ⟨m,_,⟨e⟩⟩
    exact (filter_iso_singleton_prefix P e).1
  · exact qualifies_filter_of_singleton_prefix P (lastRoot P)

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

variable {n : Nat}

private def suffixVertex (a : Fin (n+1)) (v : Fin (n-a.val)) : Fin (n+1) :=
  ⟨a.val+v.val+1,by have := v.isLt; omega⟩

private theorem suffix_parent_exists (a : Fin (n+1))
    (T : {P : IntervalForest n // SingletonPrefix P a}) (v : Fin (n-a.val)) :
    ∃ p, T.val.parent (suffixVertex a v) = some p ∧ a.val <= p.val := by
  have hn := T.property.2 (suffixVertex a v) (by change a.val < a.val+v.val+1; omega)
  cases hp : T.val.parent (suffixVertex a v) with
  | none => exact (hn hp).elim
  | some p =>
    refine ⟨p,rfl,?_⟩
    by_contra h
    have hpa : p < a := by change p.val < a.val; omega
    have hav : a <= suffixVertex a v := by change a.val <= a.val+v.val+1; omega
    exact T.val.no_skipped_root hp hpa hav (T.property.1 a le_rfl)

private noncomputable def suffixToCode (a : Fin (n+1))
    (T : {P : IntervalForest n // SingletonPrefix P a}) : ((v : Fin (n-a.val)) -> Fin (v.val + 1)) := fun v =>
  ⟨(suffix_parent_exists a T v).choose.val-a.val,by
    have hp := T.val.increasing _ _ (suffix_parent_exists a T v).choose_spec.1
    have ha := (suffix_parent_exists a T v).choose_spec.2
    change (suffix_parent_exists a T v).choose.val < a.val+v.val+1 at hp
    omega⟩

private theorem suffixToCode_parent (a : Fin (n+1))
    (T : {P : IntervalForest n // SingletonPrefix P a}) (v : Fin (n-a.val)) :
    T.val.parent (suffixVertex a v) = some
      (⟨a.val+(suffixToCode a T v).val,by have := (suffixToCode a T v).isLt; have := v.isLt; omega⟩ : Fin (n+1)) := by
  have h := (suffix_parent_exists a T v).choose_spec
  have he : (⟨a.val+(suffixToCode a T v).val,by have := (suffixToCode a T v).isLt; have := v.isLt; omega⟩ : Fin (n+1)) =
      (suffix_parent_exists a T v).choose := by
    apply Fin.ext
    dsimp [suffixToCode]
    omega
  rw [he]
  exact h.1

private def suffixCodeParent (a : Fin (n+1)) (t : ((v : Fin (n-a.val)) -> Fin (v.val + 1)))
    (v : Fin (n+1)) : Option (Fin (n+1)) :=
  if hv : v.val <= a.val then none else
    some ⟨a.val+(t ⟨v.val-a.val-1,by have := v.isLt; omega⟩).val,by
      have := (t ⟨v.val-a.val-1,by have := v.isLt; omega⟩).isLt
      have := v.isLt
      omega⟩

private theorem suffixCodeParent_none (a : Fin (n+1)) (t : ((v : Fin (n-a.val)) -> Fin (v.val + 1)))
    (v : Fin (n+1)) : suffixCodeParent a t v = none ↔ v <= a := by
  change suffixCodeParent a t v = none ↔ v.val <= a.val
  by_cases hv : v.val <= a.val
  · simp only [suffixCodeParent,hv,dite_true]
  · simp only [suffixCodeParent,hv,dite_false,Option.some_ne_none]

private def suffixCodeForest (a : Fin (n+1)) (t : ((v : Fin (n-a.val)) -> Fin (v.val + 1))) : IntervalForest n :=
  forestOfLocal (suffixCodeParent a t)
    (by
      intro v p hp
      by_cases hv : v.val <= a.val
      · simp [suffixCodeParent,hv] at hp
      · simp only [suffixCodeParent,hv,dite_false,Option.some.injEq] at hp
        have h := (t ⟨v.val-a.val-1,by have := v.isLt; omega⟩).isLt
        dsimp only at h
        have hpv := congrArg Fin.val hp
        dsimp at hpv
        change p.val < v.val
        omega)
    (by
      intro v p w hp hpw _ hw
      have hwa := (suffixCodeParent_none a t w).mp hw
      by_cases hv : v.val <= a.val
      · simp [suffixCodeParent,hv] at hp
      · simp only [suffixCodeParent,hv,dite_false,Option.some.injEq] at hp
        have hpv := congrArg Fin.val hp
        dsimp at hpv
        change p.val < w.val at hpw
        change w.val <= a.val at hwa
        omega)

private theorem suffixCodeForest_prefix (a : Fin (n+1)) (t : ((v : Fin (n-a.val)) -> Fin (v.val + 1))) :
    SingletonPrefix (suffixCodeForest a t) a := by
  constructor
  · intro v hv
    exact (suffixCodeParent_none a t v).mpr hv
  · intro v hv h
    exact (not_le_of_gt hv) ((suffixCodeParent_none a t v).mp h)

private theorem suffix_code_left_inv (a : Fin (n+1)) (t : ((v : Fin (n-a.val)) -> Fin (v.val + 1))) :
    suffixToCode a ⟨suffixCodeForest a t,suffixCodeForest_prefix a t⟩ = t := by
  funext v
  have hp := suffixToCode_parent a ⟨suffixCodeForest a t,suffixCodeForest_prefix a t⟩ v
  change suffixCodeParent a t (suffixVertex a v) = _ at hp
  have hv : ¬ (suffixVertex a v).val <= a.val := by dsimp [suffixVertex]; omega
  simp only [suffixCodeParent,hv,dite_false,Option.some.injEq] at hp
  have harg : (⟨(suffixVertex a v).val-a.val-1,by dsimp [suffixVertex]; have := v.isLt; omega⟩ : Fin (n-a.val)) = v := by
    apply Fin.ext
    dsimp [suffixVertex]
    omega
  have hval := congrArg Fin.val hp
  dsimp only [Fin.val_mk] at hval
  have ht := congrArg (fun i => (t i).val) harg
  rw [ht] at hval
  apply Fin.ext
  omega

private theorem suffix_code_right_inv (a : Fin (n+1))
    (T : {P : IntervalForest n // SingletonPrefix P a}) :
    (⟨suffixCodeForest a (suffixToCode a T),suffixCodeForest_prefix a (suffixToCode a T)⟩ :
      {P : IntervalForest n // SingletonPrefix P a}) = T := by
  apply Subtype.ext
  apply IntervalForest.ext
  funext v
  by_cases hv : v.val <= a.val
  · change suffixCodeParent a (suffixToCode a T) v = T.val.parent v
    rw [(suffixCodeParent_none a (suffixToCode a T) v).mpr hv,T.property.1 v hv]
  · let w : Fin (n-a.val) := ⟨v.val-a.val-1,by have := v.isLt; omega⟩
    have hw : suffixVertex a w = v := by apply Fin.ext; dsimp [suffixVertex,w]; omega
    have hp := suffixToCode_parent a T w
    rw [hw] at hp
    change suffixCodeParent a (suffixToCode a T) v = T.val.parent v
    simp only [suffixCodeParent,hv,dite_false]
    exact hp.symm

private noncomputable def suffixForestEquivCode (a : Fin (n+1)) :
    {P : IntervalForest n // SingletonPrefix P a} ≃ ((v : Fin (n-a.val)) -> Fin (v.val + 1)) where
  toFun := suffixToCode a
  invFun t := ⟨suffixCodeForest a t,suffixCodeForest_prefix a t⟩
  left_inv := suffix_code_right_inv a
  right_inv := suffix_code_left_inv a

private theorem singleton_prefix_card (a : Fin (n+1)) :
    Nat.card {P : IntervalForest n // SingletonPrefix P a} = (n-a.val).factorial := by
  rw [Nat.card_congr (suffixForestEquivCode a)]
  rw [← Nat.card_congr (treeEquivCode (n-a.val))]
  exact increasing_tree_card (n-a.val)

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

variable {n : Nat}

private theorem singletonPrefix_lastRoot (P : IntervalForest n) (a : Fin (n+1))
    (h : SingletonPrefix P a) : (lastRoot P) = a := by
  apply le_antisymm
  · by_contra hh
    exact h.2 (lastRoot P) (lt_of_not_ge hh) (parent_lastRoot P)
  · exact (root_le_lastRoot P) (h.1 a le_rfl)

private noncomputable def qualifyingFilterEquiv (n : Nat) :
    (Σ a : Fin (n+1), {P : IntervalForest n // SingletonPrefix P a}) ≃
      {x : (WithTop (IntervalForest n)) // ∃ m ≤ n, Nonempty (Set.Ici x ≃o (WithTop (IntervalForest m)))} := by
  refine Equiv.ofBijective (fun T => ⟨(T.2.val : (WithTop (IntervalForest n))),
    qualifies_filter_of_singleton_prefix T.2.val T.1 T.2.property⟩) ?_
  constructor
  · rintro ⟨a,P⟩ ⟨b,Q⟩ h
    have hPQ : P.val = Q.val := WithTop.coe_inj.mp (congrArg Subtype.val h)
    have ha := singletonPrefix_lastRoot P.val a P.property
    have hb := singletonPrefix_lastRoot Q.val b Q.property
    rw [hPQ] at ha
    have hab : a = b := ha.symm.trans hb
    subst b
    have hsub : P = Q := Subtype.ext hPQ
    rw [hsub]
  · intro x
    have hne : x.val ≠ ⊤ := by
      intro h
      obtain ⟨m,_,hm⟩ := x.property
      rw [h] at hm
      exact top_filter_not_iso n m hm
    change (x.val : WithTop (IntervalForest n)) ≠ ⊤ at hne
    obtain ⟨P,hP⟩ := WithTop.ne_top_iff_exists.mp hne
    have hqual : ∃ m ≤ n, Nonempty (Set.Ici (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m))) := by
      change ∃ m ≤ n, Nonempty (Set.Ici (P : WithTop (IntervalForest n)) ≃o (WithTop (IntervalForest m)))
      rw [hP]
      exact x.property
    refine ⟨⟨(lastRoot P),⟨P,forest_filter_qualifies_iff P |>.mp hqual⟩⟩,?_⟩
    exact Subtype.ext hP

private theorem theta_sum (n : Nat) : filterCount n = ∑ k ∈ Finset.range (n+1), k.factorial := by
  unfold filterCount
  rw [← Nat.card_congr (qualifyingFilterEquiv n),Nat.card_sigma]
  simp_rw [singleton_prefix_card]
  rw [Fin.sum_univ_eq_sum_range (fun a => (n-a).factorial) (n+1)]
  exact Finset.sum_range_reflect (fun k => k.factorial) (n+1)

private theorem filterCountResult : forall n, 1 <= n ->
    filterCount n = ∑ k ∈ Finset.range (n+1), k.factorial := by
  intro n _
  exact theta_sum n

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalFilters

structure PriorityForest (n : Nat) where
  parent : Fin (n + 1) -> Option (Fin (n + 1))
  increasing : forall v p, parent v = some p -> p < v
  intervals : forall u v w : Fin (n + 1), u <= v -> v <= w ->
    Relation.EqvGen (fun a b => parent b = some a) u w ->
    Relation.EqvGen (fun a b => parent b = some a) u v

namespace PriorityForest

@[ext] private theorem ext {n : Nat} {P Q : PriorityForest n} (h : P.parent = Q.parent) : P = Q := by
  cases P; cases Q; cases h; rfl

private def toCore {n : Nat} (P : PriorityForest n) : D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest n :=
  ⟨P.parent,P.increasing,P.intervals⟩
private def ofCore {n : Nat} (P : D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest n) : PriorityForest n :=
  ⟨P.parent,P.increasing,P.intervals⟩

def edges {n : Nat} (P : PriorityForest n) : Set (Fin (n+1) × Fin (n+1)) :=
  {e | P.parent e.2 = some e.1}

private theorem edges_injective {n : Nat} : Function.Injective (@edges n) := by
  intro P Q h
  have hc : P.toCore.edges = Q.toCore.edges := h
  have he := D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest.edges_injective hc
  exact ext (congrArg D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest.parent he)

instance forestPartialOrder (n : Nat) : PartialOrder (PriorityForest n) := PartialOrder.lift edges edges_injective
private instance forestFinite (n : Nat) : Finite (PriorityForest n) := Finite.of_injective toCore
  (by intro P Q h; exact ext (congrArg D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest.parent h))

private def forestToCoreOrderIso (n : Nat) : PriorityForest n ≃o D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest n where
  toFun := toCore
  invFun := ofCore
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl
  map_rel_iff' := by intro P Q; rfl

end PriorityForest

@[reducible] def Pi (n : Nat) := WithTop (PriorityForest n)

noncomputable def theta (n : Nat) : Nat :=
  Nat.card {x : Pi n // ∃ m ≤ n, Nonempty (Set.Ici x ≃o Pi m)}

def claimTheta : Prop := forall n, 1 <= n ->
  theta n = ∑ k ∈ Finset.range (n+1), k.factorial

def coreOrderIso (n : Nat) : Pi n ≃o (WithTop (IntervalForest n)) :=
  (PriorityForest.forestToCoreOrderIso n).withTopCongr

private def iciCongr {A B : Type*} [PartialOrder A] [PartialOrder B] (e : A ≃o B) (x : A) :
    Set.Ici x ≃o Set.Ici (e x) :=
  { toEquiv := Equiv.subtypeEquiv (p := fun y => x <= y)
      (q := fun y => e x <= y) e.toEquiv (fun y => e.le_iff_le.symm)
    map_rel_iff' := by intro y z; exact e.le_iff_le }

private theorem filter_qualification_transfer (n : Nat) (x : Pi n) :
    (∃ m ≤ n, Nonempty (Set.Ici x ≃o Pi m)) ↔
      ∃ m ≤ n, Nonempty (Set.Ici (coreOrderIso n x) ≃o (WithTop (IntervalForest m))) := by
  constructor
  · rintro ⟨m,hm,⟨e⟩⟩
    exact ⟨m,hm,⟨((iciCongr (coreOrderIso n) x).symm.trans e).trans (coreOrderIso m)⟩⟩
  · rintro ⟨m,hm,⟨e⟩⟩
    exact ⟨m,hm,⟨((iciCongr (coreOrderIso n) x).trans e).trans (coreOrderIso m).symm⟩⟩

private theorem theta_transfer (n : Nat) : theta n = D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.filterCount n := by
  classical
  letI : Fintype {x : Pi n // ∃ m ≤ n, Nonempty (Set.Ici x ≃o Pi m)} := Fintype.ofFinite _
  letI : Fintype {x : (WithTop (IntervalForest n)) // ∃ m ≤ n,
      Nonempty (Set.Ici x ≃o (WithTop (IntervalForest m)))} := Fintype.ofFinite _
  unfold theta D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.filterCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquiv (coreOrderIso n).toEquiv (filter_qualification_transfer n))

theorem result : claimTheta := by
  intro n hn
  rw [theta_transfer]
  exact D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.filterCountResult n hn

end D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
