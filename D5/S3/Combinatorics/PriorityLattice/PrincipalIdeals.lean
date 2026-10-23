/- GID: D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/PrincipalIdeals
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
ideal_zero_code: proof_shape: content
ideal_one_code_iff: proof_shape: content
ideal_two_code_iff: proof_shape: content
ideal_zero_iff_count: proof_shape: content
ideal_one_iff_oneLong: proof_shape: content
ideal_two_iff_oneLong: proof_shape: content
forest_ideal_shape_iff: proof_shape: content
forest_ideal_pos_shape_iff: proof_shape: content
card_disjoint_or: proof_shape: bind-only; consumer: PrincipalIdeals.forest_ideal_count
optionPredicateEquiv: proof_shape: bind-only; consumer: PrincipalIdeals.card_option_predicate
card_option_predicate: proof_shape: bind-only; consumer: PrincipalIdeals.card_withTop_predicate
card_withTop_predicate: proof_shape: bind-only; consumer: PrincipalIdeals.gammaPos_expansion
claimIdealCount: proof_shape: bind-only; consumer: PrincipalIdeals.IdealCount.idealCountResult (statement type)
long_classes_card: proof_shape: content
forest_ideal_count: proof_shape: content
gamma_expansion: proof_shape: content
gammaPos_expansion: proof_shape: content
gamma_formula: proof_shape: content
gammaPos_formula: proof_shape: content
IdealCount.idealCountResult: proof_shape: content
gamma: proof_shape: bind-only; consumer: PrincipalIdeals.claimGamma
gammaPos: proof_shape: bind-only; consumer: PrincipalIdeals.claimGamma
iicCongr: proof_shape: bind-only; consumer: PrincipalIdeals.ideal_pos_qualification_transfer
ideal_qualification_transfer: proof_shape: bind-only; consumer: PrincipalIdeals.gamma_transfer
ideal_pos_qualification_transfer: proof_shape: bind-only; consumer: PrincipalIdeals.gammaPos_transfer
gamma_transfer: proof_shape: bind-only; consumer: PrincipalIdeals.result
gammaPos_transfer: proof_shape: bind-only; consumer: PrincipalIdeals.result
claimGamma: proof_shape: bind-only; consumer: PrincipalIdeals.result (statement type)
result: proof_shape: content
-/

import D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
import D5.S3.Combinatorics.PriorityLattice.LowRankForests

open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.ForestCovers
open D5.S3.Combinatorics.PriorityLattice.ForestCovers.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.IdealCompression
open D5.S3.Combinatorics.PriorityLattice.IdealCompression.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.LowRankForests
open D5.S3.Combinatorics.PriorityLattice.LowRankForests.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
open D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.IdealCompression.SmallIdealCodes
open D5.S3.Combinatorics.PriorityLattice.IdealCompression.SmallCases
open D5.S3.Combinatorics.PriorityLattice.PrincipalFilters.PriorityForest

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.IntervalForest
end D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

open SmallIdealCodes

variable {n : Nat}

private theorem ideal_zero_code (P : IntervalForest n) (h : (edgeCount P) = 1) :
    Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest 0))) := by
  have ht : (compressCode P) h = t1 := code_one _
  have e := (idealCodeOrderIso P) h
  rw [ht] at e
  exact ⟨e.trans pi0CodeOrderIso.symm⟩

private theorem ideal_one_code_iff (P : IntervalForest n) (h : (edgeCount P) = 2) :
    Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest 1))) ↔ (compressCode P) h = t20 := by
  constructor
  · rintro ⟨e⟩
    have hc : Nat.card ({s : Finset (Fin _) // CodeClosed ((compressCode P) h) s}) = 3 := by
      rw [← Nat.card_congr ((idealCodeOrderIso P) h).toEquiv,Nat.card_congr e.toEquiv]
      exact pi_one_card
    exact (card_two_iff _).mp hc
  · intro ht
    have e := (idealCodeOrderIso P) h
    rw [ht] at e
    exact ⟨e.trans pi1CodeOrderIso.symm⟩

private theorem ideal_two_code_iff (P : IntervalForest n) (h : (edgeCount P) = 3) :
    Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest 2))) ↔
      (compressCode P) h = t3 0 2 ∨ (compressCode P) h = t3 1 1 := by
  constructor
  · rintro ⟨e⟩
    have hc : Nat.card ({s : Finset (Fin _) // CodeClosed ((compressCode P) h) s}) = 6 := by
      rw [← Nat.card_congr ((idealCodeOrderIso P) h).toEquiv,Nat.card_congr e.toEquiv]
      exact pi_two_card
    exact (card_three_iff _).mp hc
  · intro ht
    have e := (idealCodeOrderIso P) h
    rcases ht with ht | ht
    · rw [ht] at e
      exact ⟨e.trans pi2CodeOrderIso.symm⟩
    · rw [ht] at e
      exact ⟨e.trans (twoTripleModelsIso.symm.trans pi2CodeOrderIso.symm)⟩

end D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

variable {n : Nat}

open SmallIdealCodes

private theorem ideal_zero_iff_count (P : IntervalForest n) :
    Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest 0))) ↔ (edgeCount P) = 1 := by
  constructor
  · rintro ⟨e⟩; exact ideal_iso_rank e
  · exact ideal_zero_code P

private theorem ideal_one_iff_oneLong (P : IntervalForest n) :
    Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest 1))) ↔ (edgeCount P) = 2 ∧ OneLong P := by
  constructor
  · rintro ⟨e⟩
    have hk : (edgeCount P) = 2 := ideal_iso_rank e
    refine ⟨hk,?_⟩
    apply ((one_long_iff_code_one_step P) hk).mpr
    apply (oneStep_two_iff _).mpr
    exact (ideal_one_code_iff P hk).mp ⟨e⟩
  · rintro ⟨hk,hP⟩
    apply (ideal_one_code_iff P hk).mpr
    exact (oneStep_two_iff _).mp (((one_long_iff_code_one_step P) hk).mp hP)

private theorem ideal_two_iff_oneLong (P : IntervalForest n) :
    Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest 2))) ↔ (edgeCount P) = 3 ∧ OneLong P := by
  constructor
  · rintro ⟨e⟩
    have hk : (edgeCount P) = 3 := ideal_iso_rank e
    refine ⟨hk,?_⟩
    apply ((one_long_iff_code_one_step P) hk).mpr
    apply (oneStep_three_iff _).mpr
    exact (ideal_two_code_iff P hk).mp ⟨e⟩
  · rintro ⟨hk,hP⟩
    apply (ideal_two_code_iff P hk).mpr
    exact (oneStep_three_iff _).mp (((one_long_iff_code_one_step P) hk).mp hP)

theorem forest_ideal_shape_iff (P : IntervalForest n) :
    (∃ m ≤ n, Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m)))) ↔
      (edgeCount P) = 1 ∨ ((edgeCount P) = 2 ∧ OneLong P) ∨ ((edgeCount P) = 3 ∧ OneLong P) := by
  constructor
  · rintro ⟨m,_,⟨e⟩⟩
    have hm := forest_ideal_index_le_two P e
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl ((ideal_zero_iff_count P).mp ⟨e⟩)
    · exact Or.inr (Or.inl ((ideal_one_iff_oneLong P).mp ⟨e⟩))
    · exact Or.inr (Or.inr ((ideal_two_iff_oneLong P).mp ⟨e⟩))
  · rintro (hk | hk | hk)
    · exact ⟨0,Nat.zero_le _,(ideal_zero_iff_count P).mpr hk⟩
    · refine ⟨1,?_,(ideal_one_iff_oneLong P).mpr hk⟩
      have := (edgeCount_le P); omega
    · refine ⟨2,?_,(ideal_two_iff_oneLong P).mpr hk⟩
      have := (edgeCount_le P); omega

private theorem forest_ideal_pos_shape_iff (P : IntervalForest n) :
    (∃ m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m)))) ↔
      ((edgeCount P) = 2 ∧ OneLong P) ∨ ((edgeCount P) = 3 ∧ OneLong P) := by
  constructor
  · rintro ⟨m,hm,_,⟨e⟩⟩
    have hm2 := forest_ideal_index_le_two P e
    have hcases : m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl
    · exact Or.inl ((ideal_one_iff_oneLong P).mp ⟨e⟩)
    · exact Or.inr ((ideal_two_iff_oneLong P).mp ⟨e⟩)
  · rintro (hk | hk)
    · refine ⟨1,by omega,?_,(ideal_one_iff_oneLong P).mpr hk⟩
      have := (edgeCount_le P); omega
    · refine ⟨2,by omega,?_,(ideal_two_iff_oneLong P).mpr hk⟩
      have := (edgeCount_le P); omega

end D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

private theorem card_disjoint_or {A : Type*} [Finite A] (p q : A -> Prop)
    (h : ∀ x, p x -> q x -> False) :
    Nat.card {x : A // p x ∨ q x} = Nat.card {x : A // p x}+Nat.card {x : A // q x} := by
  classical
  rw [Nat.card_congr (subtypeOrEquiv p q (by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    exact h x hx.1 hx.2)),Nat.card_sum]

private noncomputable def optionPredicateEquiv {A : Type*} (p : Option A -> Prop) (q : A -> Prop)
    (hn : p none) (hs : ∀ a, p (some a) ↔ q a) :
    Option {a : A // q a} ≃ {x : Option A // p x} := by
  let f : Option {a : A // q a} -> {x : Option A // p x} :=
    fun x => match x with
      | none => ⟨none,hn⟩
      | some a => ⟨some a.val,(hs a.val).mpr a.property⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro x y h
    cases x with
    | none => cases y with
      | none => rfl
      | some b => have hh := congrArg Subtype.val h; cases hh
    | some a => cases y with
      | none => have hh := congrArg Subtype.val h; cases hh
      | some b =>
        have hh : a.val = b.val := Option.some.inj (congrArg Subtype.val h)
        exact congrArg some (Subtype.ext hh)
  · rintro ⟨x,hx⟩
    cases x with
    | none => exact ⟨none,rfl⟩
    | some a => exact ⟨some ⟨a,(hs a).mp hx⟩,rfl⟩

private theorem card_option_predicate {A : Type*} [Finite A] (p : Option A -> Prop) (q : A -> Prop)
    (hn : p none) (hs : ∀ a, p (some a) ↔ q a) :
    Nat.card {x : Option A // p x} = Nat.card {a : A // q a}+1 := by
  rw [← Nat.card_congr (optionPredicateEquiv p q hn hs),Finite.card_option]

private theorem card_withTop_predicate {A : Type*} [Finite A] (p : WithTop A -> Prop) (q : A -> Prop)
    (hn : p ⊤) (hs : ∀ a : A, p (a : WithTop A) ↔ q a) :
    Nat.card {x : WithTop A // p x} = Nat.card {a : A // q a}+1 :=
  card_option_predicate p q hn hs

end D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

private def claimIdealCount : Prop := forall n, 1 <= n ->
  idealCount n = n ^ 2 - n + 2 ∧ positiveIdealCount n = n ^ 2 + 2 - 2 * n

end D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

variable {n : Nat}

private theorem long_classes_card (n : Nat) : Nat.card {P : IntervalForest n //
    ((edgeCount P) = 2 ∧ OneLong P) ∨ ((edgeCount P) = 3 ∧ OneLong P)} =
    (n-1)+(n-1)*(n-2) := by
  rw [card_disjoint_or]
  · rw [long_two_card,long_three_card]
  · intro P h2 h3
    omega

private theorem forest_ideal_count (n : Nat) : Nat.card {P : IntervalForest n //
    (edgeCount P) = 1 ∨ ((edgeCount P) = 2 ∧ OneLong P) ∨ ((edgeCount P) = 3 ∧ OneLong P)} =
    n+(n-1)+(n-1)*(n-2) := by
  rw [card_disjoint_or]
  · rw [single_edges_card,long_classes_card]
    omega
  · intro P h1 hrest
    rcases hrest with h2 | h3 <;> omega

private theorem gamma_expansion (n : Nat) : idealCount n = n+(n-1)+(n-1)*(n-2)+1 := by
  unfold idealCount
  have hc := card_withTop_predicate
    (fun x : (WithTop (IntervalForest n)) => ∃ m ≤ n, Nonempty (Set.Iic (x : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m))))
    (fun P : IntervalForest n => (edgeCount P) = 1 ∨
      ((edgeCount P) = 2 ∧ OneLong P) ∨ ((edgeCount P) = 3 ∧ OneLong P))
    (by exact ⟨n,le_rfl,⟨OrderIso.IicTop⟩⟩)
    (fun P => forest_ideal_shape_iff P)
  exact hc.trans (congrArg (fun k => k+1) (forest_ideal_count n))

private theorem gammaPos_expansion (n : Nat) (hn : 1 <= n) :
    positiveIdealCount n = (n-1)+(n-1)*(n-2)+1 := by
  unfold positiveIdealCount
  have hc := card_withTop_predicate
    (fun x : (WithTop (IntervalForest n)) => ∃ m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic (x : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m))))
    (fun P : IntervalForest n => ((edgeCount P) = 2 ∧ OneLong P) ∨ ((edgeCount P) = 3 ∧ OneLong P))
    (by exact ⟨n,hn,le_rfl,⟨OrderIso.IicTop⟩⟩)
    (fun P => forest_ideal_pos_shape_iff P)
  exact hc.trans (congrArg (fun k => k+1) (long_classes_card n))

theorem gamma_formula (n : Nat) (hn : 1 <= n) : idealCount n = n^2-n+2 := by
  rw [gamma_expansion]
  by_cases h1 : n = 1
  · subst n; norm_num
  · have h2 : 2 <= n := by omega
    have hn1 : n-1+1 = n := Nat.sub_add_cancel hn
    have hn2 : n-2+2 = n := Nat.sub_add_cancel h2
    have hsq : n <= n^2 := by nlinarith
    have hsub : n^2-n+n = n^2 := Nat.sub_add_cancel hsq
    nlinarith

theorem gammaPos_formula (n : Nat) (hn : 1 <= n) : positiveIdealCount n = n^2+2-2*n := by
  rw [gammaPos_expansion n hn]
  by_cases h1 : n = 1
  · subst n; norm_num
  · have h2 : 2 <= n := by omega
    have hn1 : n-1+1 = n := Nat.sub_add_cancel hn
    have hn2 : n-2+2 = n := Nat.sub_add_cancel h2
    have hsq : 2*n <= n^2+2 := by nlinarith
    have hsub : n^2+2-2*n+2*n = n^2+2 := Nat.sub_add_cancel hsq
    nlinarith

namespace IdealCount

private theorem idealCountResult : claimIdealCount := by
  intro n hn
  exact ⟨gamma_formula n hn,gammaPos_formula n hn⟩

end IdealCount

end D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

namespace D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals

noncomputable def gamma (n : Nat) : Nat :=
  Nat.card {x : Pi n // ∃ m ≤ n, Nonempty (Set.Iic x ≃o Pi m)}
noncomputable def gammaPos (n : Nat) : Nat :=
  Nat.card {x : Pi n // ∃ m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic x ≃o Pi m)}

private def iicCongr {A B : Type*} [PartialOrder A] [PartialOrder B] (e : A ≃o B) (x : A) :
    Set.Iic x ≃o Set.Iic (e x) :=
  { toEquiv := Equiv.subtypeEquiv (p := fun y => y <= x)
      (q := fun y => y <= e x) e.toEquiv (fun y => e.le_iff_le.symm)
    map_rel_iff' := by intro y z; exact e.le_iff_le }

private theorem ideal_qualification_transfer (n : Nat) (x : Pi n) :
    (∃ m ≤ n, Nonempty (Set.Iic x ≃o Pi m)) ↔
      ∃ m ≤ n, Nonempty (Set.Iic (coreOrderIso n x) ≃o (WithTop (IntervalForest m))) := by
  constructor
  · rintro ⟨m,hm,⟨e⟩⟩
    exact ⟨m,hm,⟨((iicCongr (coreOrderIso n) x).symm.trans e).trans (coreOrderIso m)⟩⟩
  · rintro ⟨m,hm,⟨e⟩⟩
    exact ⟨m,hm,⟨((iicCongr (coreOrderIso n) x).trans e).trans (coreOrderIso m).symm⟩⟩

private theorem ideal_pos_qualification_transfer (n : Nat) (x : Pi n) :
    (∃ m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic x ≃o Pi m)) ↔
      ∃ m, 1 <= m ∧ m <= n ∧ Nonempty
        (Set.Iic (coreOrderIso n x) ≃o (WithTop (IntervalForest m))) := by
  constructor
  · rintro ⟨m,hm1,hm,⟨e⟩⟩
    exact ⟨m,hm1,hm,⟨((iicCongr (coreOrderIso n) x).symm.trans e).trans (coreOrderIso m)⟩⟩
  · rintro ⟨m,hm1,hm,⟨e⟩⟩
    exact ⟨m,hm1,hm,⟨((iicCongr (coreOrderIso n) x).trans e).trans (coreOrderIso m).symm⟩⟩

private theorem gamma_transfer (n : Nat) : gamma n = D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.idealCount n :=
  Nat.card_congr (Equiv.subtypeEquiv (coreOrderIso n).toEquiv (ideal_qualification_transfer n))
private theorem gammaPos_transfer (n : Nat) : gammaPos n = D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.positiveIdealCount n :=
  Nat.card_congr (Equiv.subtypeEquiv (coreOrderIso n).toEquiv (ideal_pos_qualification_transfer n))

def claimGamma : Prop := forall n, 1 <= n ->
  gamma n = n^2-n+2 ∧ gammaPos n = n^2+2-2*n

theorem result : claimGamma := by
  intro n hn
  rw [gamma_transfer,gammaPos_transfer]
  exact D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals.IdealCount.idealCountResult n hn

end D5.S3.Combinatorics.PriorityLattice.PrincipalIdeals
