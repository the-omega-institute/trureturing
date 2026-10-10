/- GID: D5/S3/Combinatorics/PriorityLattice/ForestCovers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/ForestCovers
   mirror-E: none(waiver:general-priority-lattice-counting)
   anchors: []
   utility: none
   digest: Priority-forest interval structure and counting. -/

/-
admission_basis: escape-witness
escape_witness: covBy_rank; IntervalForest.lower_covers_card_le
The cover characterization constructs a valid one-edge extension from the first missing support vertex and uses it to control the lower-cover injection.
Direct frozen dependencies: none; direct D5 dependencies are supplied by this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14955
Proof shapes expand all same-delivery declarations and apply the upstream-only bypass test.
IntervalForest.support: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.addBelow_count
IntervalForest.mem_support: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.addBelow_count
IntervalForest.le_iff_parent: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.addBelow_bounds
IntervalForest.support_mono: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.cover_support_diff_singleton
IntervalForest.eq_of_support_eq: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.edgeCount_strictMono
IntervalForest.edgeCount: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.addBelow_count
IntervalForest.edgeCount_strictMono: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.covBy_iff_edgeCount
IntervalForest.addBelow: proof_shape: content
IntervalForest.addBelow_bounds: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.exists_one_edge_extension
IntervalForest.addBelow_count: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.exists_one_edge_extension
IntervalForest.exists_one_edge_extension: proof_shape: content
IntervalForest.covBy_iff_edgeCount: proof_shape: content
IntervalForest.fillParent: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.fillForest
IntervalForest.fillParent_roots: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.fillForest
IntervalForest.fillForest: proof_shape: content
IntervalForest.fillForest_tree: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.isMax_iff_tree
IntervalForest.le_fillForest: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.isMax_iff_tree
IntervalForest.isMax_iff_tree: proof_shape: content
IntervalForest.support_subset_erase_zero: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.edgeCount_eq_iff_tree
IntervalForest.edgeCount_le: proof_shape: bind-only; consumer: ForestCovers.rank_strictMono
IntervalForest.edgeCount_eq_iff_tree: proof_shape: bind-only; consumer: ForestCovers.covBy_rank
IntervalForest.forestGradeOrder: proof_shape: content
rank: proof_shape: bind-only; consumer: ForestCovers.completionGradeOrder
coatom_iff_tree: proof_shape: content
rank_strictMono: proof_shape: bind-only; consumer: ForestCovers.completionGradeOrder
covBy_rank: proof_shape: content
completionGradeOrder: proof_shape: content
finite_exists_lower_cover: proof_shape: bind-only; consumer: ForestCovers.rank_map_orderIso
rank_map_orderIso: proof_shape: content
atom_card_orderIso: proof_shape: bind-only; consumer: PrincipalFilters.filter_iso_singleton_prefix
coatom_card_orderIso: proof_shape: bind-only; consumer: ForestCovers.forest_ideal_index_le_two
IntervalForest.eq_of_same_support_below: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.lowerCoverEdge_injective
IntervalForest.cover_support_diff_singleton: proof_shape: content
IntervalForest.lowerCoverEdge: proof_shape: content
IntervalForest.lowerCoverEdge_injective: proof_shape: content
IntervalForest.lower_covers_card_le: proof_shape: content
forestCoatomEquiv: proof_shape: content
pi_coatom_card: proof_shape: content
idealCoatomEquiv: proof_shape: bind-only; consumer: ForestCovers.ideal_coatoms_le
ideal_coatoms_le: proof_shape: content
rank_bot: proof_shape: bind-only; consumer: ForestCovers.filter_iso_rank
iic_covBy_iff: proof_shape: bind-only; consumer: ForestCovers.ideal_iso_rank
ici_covBy_iff: proof_shape: bind-only; consumer: ForestCovers.filter_iso_rank
ideal_iso_rank: proof_shape: content
filter_iso_rank: proof_shape: content
top_filter_not_iso: proof_shape: bind-only; consumer: PrincipalFilters.qualifyingFilterEquiv
factorial_gt_succ: proof_shape: bind-only; consumer: ForestCovers.forest_ideal_index_le_two
forest_ideal_index_le_two: proof_shape: content
IntervalForest.cover_parent_update: proof_shape: content
IntervalForest.cover_adjacent_roots: proof_shape: content
-/

import Mathlib.Data.Fintype.WithTopBot
import Mathlib.Tactic.Linarith
import D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
import Mathlib.Order.Atoms
import Mathlib.Order.Grade

open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers.IntervalForest
end D5.S3.Combinatorics.PriorityLattice.ForestCovers.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.ForestCovers.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers
namespace IntervalForest

variable {n : Nat}

noncomputable def support (P : IntervalForest n) : Finset (Fin (n+1)) :=
  by classical exact Finset.univ.filter (fun v => P.parent v ≠ none)

@[simp] theorem mem_support (P : IntervalForest n) (v : Fin (n+1)) :
    v ∈ (support P) <-> P.parent v ≠ none := by classical simp [support]

theorem le_iff_parent (P Q : IntervalForest n) :
    P <= Q <-> forall v p, P.parent v = some p -> Q.parent v = some p := by
  constructor
  · intro h v p hp; exact @h (p,v) hp
  · intro h e he; exact h e.2 e.1 he

theorem support_mono {P Q : IntervalForest n} (h : P <= Q) : (support P) ⊆ (support Q) := by
  intro v hv
  rw [mem_support] at hv ⊢
  cases hp : P.parent v with
  | none => exact (hv hp).elim
  | some p => rw [(le_iff_parent P Q).mp h v p hp]; simp

private theorem eq_of_support_eq {P Q : IntervalForest n} (h : P <= Q)
    (hs : (support P) = (support Q)) : P = Q := by
  apply ext
  funext v
  cases hp : P.parent v with
  | some p => exact ((le_iff_parent P Q).mp h v p hp).symm
  | none =>
    have hv : v ∉ (support P) := by simpa
    rw [hs, mem_support, not_not] at hv
    exact hv.symm

noncomputable def edgeCount (P : IntervalForest n) : Nat := (support P).card

private theorem edgeCount_strictMono : StrictMono (@edgeCount n) := by
  intro P Q h
  apply Finset.card_lt_card
  exact (support_mono h.le).ssubset_of_ne (fun heq => h.ne (eq_of_support_eq h.le heq))

private noncomputable def addBelow (P Q : IntervalForest n) (hPQ : P <= Q)
    (v p : Fin (n+1)) (hPv : P.parent v = none) (hQv : Q.parent v = some p)
    (hfirst : forall w, w < v -> Q.parent w ≠ none -> P.parent w ≠ none) : IntervalForest n :=
  forestOfLocal (Function.update P.parent v (some p))
    (by
      intro w q hw
      by_cases hwv : w = v
      · subst w; simp only [Function.update_self, Option.some.injEq] at hw
        subst q; exact Q.increasing v p hQv
      · rw [Function.update_of_ne hwv] at hw
        exact P.increasing w q hw)
    (by
      intro w q z hw hqz hzw
      by_cases hzv : z = v
      · subst z; simp
      · rw [Function.update_of_ne hzv]
        by_cases hwv : w = v
        · subst w
          simp only [Function.update_self, Option.some.injEq] at hw
          subst q
          have hzn := Q.no_skipped_root hQv hqz hzw
          exact hfirst z (lt_of_le_of_ne hzw hzv) hzn
        · rw [Function.update_of_ne hwv] at hw
          exact P.no_skipped_root hw hqz hzw)

private theorem addBelow_bounds (P Q : IntervalForest n) (hPQ : P <= Q)
    (v p : Fin (n+1)) (hPv : P.parent v = none) (hQv : Q.parent v = some p)
    (hfirst : forall w, w < v -> Q.parent w ≠ none -> P.parent w ≠ none) :
    P < addBelow P Q hPQ v p hPv hQv hfirst ∧ addBelow P Q hPQ v p hPv hQv hfirst <= Q := by
  let R := addBelow P Q hPQ v p hPv hQv hfirst
  have hPR : P <= R := by
    rw [le_iff_parent]
    intro w q hw
    change Function.update P.parent v (some p) w = some q
    have hwv : w ≠ v := by intro hh; subst w; rw [hPv] at hw; cases hw
    rwa [Function.update_of_ne hwv]
  have hne : P ≠ R := by
    intro hh
    have hp := congrArg (fun T : IntervalForest n => T.parent v) hh
    change P.parent v = Function.update P.parent v (some p) v at hp
    simp [hPv] at hp
  refine ⟨lt_of_le_of_ne hPR hne, ?_⟩
  rw [le_iff_parent]
  intro w q hw
  change Function.update P.parent v (some p) w = some q at hw
  by_cases hwv : w = v
  · subst w; simp only [Function.update_self, Option.some.injEq] at hw; subst q; exact hQv
  · rw [Function.update_of_ne hwv] at hw
    exact (le_iff_parent P Q).mp hPQ w q hw

private theorem addBelow_count (P Q : IntervalForest n) (hPQ : P <= Q)
    (v p : Fin (n+1)) (hPv : P.parent v = none) (hQv : Q.parent v = some p)
    (hfirst : forall w, w < v -> Q.parent w ≠ none -> P.parent w ≠ none) :
    edgeCount (addBelow P Q hPQ v p hPv hQv hfirst) = (edgeCount P) + 1 := by
  classical
  have hs : (support (addBelow P Q hPQ v p hPv hQv hfirst)) = insert v (support P) := by
    ext w
    simp only [mem_support, Finset.mem_insert]
    change Function.update P.parent v (some p) w ≠ none <-> w = v ∨ P.parent w ≠ none
    by_cases hw : w = v
    · subst w; simp
    · simp [Function.update_of_ne hw, hw]
  unfold edgeCount
  rw [hs, Finset.card_insert_of_notMem]
  simpa

private theorem exists_one_edge_extension {P Q : IntervalForest n} (hPQ : P < Q) :
    ∃ R, P < R ∧ R <= Q ∧ (edgeCount R) = (edgeCount P)+1 := by
  classical
  have hss : (support P) ⊂ (support Q) :=
    (support_mono hPQ.le).ssubset_of_ne (fun heq => hPQ.ne (eq_of_support_eq hPQ.le heq))
  have hne : ((support Q) \ (support P)).Nonempty := by
    obtain ⟨v,hvQ,hvP⟩ := Finset.exists_of_ssubset hss
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvQ,hvP⟩⟩
  let v := ((support Q) \ (support P)).min' hne
  have hv : v ∈ (support Q) \ (support P) := Finset.min'_mem _ _
  have hPv : P.parent v = none := by
    have hh := (Finset.mem_sdiff.mp hv).2
    simpa only [mem_support, not_not] using hh
  have hQv : Q.parent v ≠ none := (mem_support Q v).mp (Finset.mem_sdiff.mp hv).1
  obtain ⟨p,hp⟩ := Option.ne_none_iff_exists'.mp hQv
  have hfirst : forall w, w < v -> Q.parent w ≠ none -> P.parent w ≠ none := by
    intro w hw hQw hPw
    have hwmem : w ∈ (support Q) \ (support P) := by simp [hQw,hPw]
    have hmin : v <= w := Finset.min'_le _ _ hwmem
    exact (not_lt_of_ge hmin) hw
  refine ⟨addBelow P Q hPQ.le v p hPv hp hfirst, ?_, ?_, ?_⟩
  · exact (addBelow_bounds P Q hPQ.le v p hPv hp hfirst).1
  · exact (addBelow_bounds P Q hPQ.le v p hPv hp hfirst).2
  · exact addBelow_count P Q hPQ.le v p hPv hp hfirst

theorem covBy_iff_edgeCount {P Q : IntervalForest n} :
    P ⋖ Q <-> P < Q ∧ (edgeCount Q) = (edgeCount P)+1 := by
  constructor
  · intro h
    obtain ⟨R,hPR,hRQ,hcount⟩ := exists_one_edge_extension h.lt
    have heq : R = Q := by
      rcases h.eq_or_eq hPR.le hRQ with hRP | hRQ
      · exact (hPR.ne hRP.symm).elim
      · exact hRQ
    subst R
    exact ⟨h.lt,hcount⟩
  · rintro ⟨hPQ,hcount⟩
    refine ⟨hPQ, ?_⟩
    intro R hPR hRQ
    have h1 := edgeCount_strictMono hPR
    have h2 := edgeCount_strictMono hRQ
    omega

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.ForestCovers

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers
namespace IntervalForest

variable {n : Nat}

private def fillParent (P : IntervalForest n) (v : Fin (n+1)) : Option (Fin (n+1)) :=
  if v = 0 then none else (P.parent v).or (some 0)

private theorem fillParent_roots (P : IntervalForest n) (v : Fin (n+1)) :
    fillParent P v = none <-> v = 0 := by
  by_cases hv : v = 0
  · simp [fillParent,hv]
  · cases hp : P.parent v <;> simp [fillParent,hv,hp]

private def fillForest (P : IntervalForest n) : IntervalForest n :=
  forestOfLocal (fillParent P)
    (by
      intro v p h
      by_cases hv : v = 0
      · simp [fillParent,hv] at h
      · cases hp : P.parent v with
        | none =>
          simp [fillParent,hv,hp] at h
          subst p
          exact Fin.pos_iff_ne_zero.mpr hv
        | some q =>
          have heq : q = p := by simpa [fillParent,hv,hp] using h
          subst p
          exact P.increasing v q hp)
    (by
      intro v p w _ hpw _ hw
      have hwz := (fillParent_roots P w).mp hw
      subst w
      exact (not_lt_of_ge (Fin.zero_le p)) hpw)

private theorem fillForest_tree (P : IntervalForest n) : IsTree (fillForest P) := by
  intro v hv
  exact (fillParent_roots P v).mp hv

private theorem le_fillForest (P : IntervalForest n) : P <= (fillForest P) := by
  rw [le_iff_parent]
  intro v p hp
  have hv : v ≠ 0 := by intro hv; subst v; rw [parent_zero] at hp; cases hp
  change fillParent P v = some p
  simp [fillParent,hv,hp]

private theorem isMax_iff_tree (P : IntervalForest n) : IsMax P <-> IsTree P := by
  constructor
  · intro h
    have heq : P = (fillForest P) := le_antisymm (le_fillForest P) (h (le_fillForest P))
    rw [heq]
    exact fillForest_tree P
  · intro h Q hPQ
    apply le_of_eq
    symm
    apply ext
    funext v
    cases hp : P.parent v with
    | none => have hv := h v hp; subst v; simp only [parent_zero]
    | some p => exact ((le_iff_parent P Q).mp hPQ v p hp).symm

private theorem support_subset_erase_zero (P : IntervalForest n) :
    (support P) ⊆ Finset.univ.erase 0 := by
  classical
  intro v hv
  have hvn : v ≠ 0 := by
    intro hv0
    subst v
    simpa [parent_zero] using hv
  simp [hvn]

theorem edgeCount_le (P : IntervalForest n) : (edgeCount P) <= n := by
  classical
  have h := Finset.card_le_card (support_subset_erase_zero P)
  simpa [edgeCount] using h

theorem edgeCount_eq_iff_tree (P : IntervalForest n) : (edgeCount P) = n <-> IsTree P := by
  classical
  constructor
  · intro h v hv
    by_contra hv0
    have hcard : (Finset.univ.erase (0 : Fin (n+1))).card <= (support P).card := by
      simpa [edgeCount] using h.ge
    have hs := Finset.eq_of_subset_of_card_le (support_subset_erase_zero P) hcard
    have hvS : v ∈ (support P) := by rw [hs]; simp [hv0]
    exact (mem_support P v).mp hvS hv
  · intro h
    have hs : (support P) = Finset.univ.erase 0 := by
      ext v
      simp only [mem_support,Finset.mem_erase,Finset.mem_univ,and_true]
      constructor
      · intro hv hv0; subst v; exact hv P.parent_zero
      · intro hv hp; exact hv (h v hp)
    simp [edgeCount,hs]

private noncomputable instance forestGradeOrder (n : Nat) : GradeOrder Nat (IntervalForest n) where
  grade := edgeCount
  grade_strictMono := edgeCount_strictMono
  covBy_grade := by
    intro a b h
    have hc := (covBy_iff_edgeCount.mp h).2
    exact Nat.covBy_iff_add_one_eq.mpr hc.symm

end IntervalForest


noncomputable def rank {n : Nat} (x : (WithTop (IntervalForest n))) : Nat :=
  (x : Option (IntervalForest n)).elim (n+1) IntervalForest.edgeCount

theorem coatom_iff_tree {n : Nat} (P : IntervalForest n) :
    IsCoatom (P : (WithTop (IntervalForest n))) <-> IsTree P := by
  rw [← covBy_top_iff]
  change (P : WithTop (IntervalForest n)) ⋖ ⊤ <-> IsTree P
  rw [WithTop.coe_covBy_top, IntervalForest.isMax_iff_tree]

private theorem rank_strictMono (n : Nat) : StrictMono (@rank n) := by
  intro x y h
  change (x : WithTop (IntervalForest n)) < y at h
  induction x using WithTop.recTopCoe with
  | top => exact (not_lt_of_ge le_top h).elim
  | coe P =>
    induction y using WithTop.recTopCoe with
    | top => exact Nat.lt_succ_of_le (edgeCount_le P)
    | coe Q => exact grade_strictMono (𝕆 := Nat) (WithTop.coe_lt_coe.mp h)

theorem covBy_rank {n : Nat} {x y : (WithTop (IntervalForest n))} (h : x ⋖ y) : rank y = rank x+1 := by
  change (x : WithTop (IntervalForest n)) ⋖ y at h
  induction x using WithTop.recTopCoe with
  | top => exact (not_lt_of_ge le_top h.lt).elim
  | coe P =>
    induction y using WithTop.recTopCoe with
    | top =>
      have ht : IsTree P := (IntervalForest.isMax_iff_tree P).mp (WithTop.coe_covBy_top.mp h)
      have hc := (IntervalForest.edgeCount_eq_iff_tree P).mpr ht
      change n+1 = (edgeCount P)+1
      omega
    | coe Q => exact (IntervalForest.covBy_iff_edgeCount.mp (WithTop.coe_covBy_coe.mp h)).2

private noncomputable instance completionGradeOrder (n : Nat) : GradeOrder Nat ((WithTop (IntervalForest n))) where
  grade := rank
  grade_strictMono := rank_strictMono n
  covBy_grade := by
    intro a b h
    exact Nat.covBy_iff_add_one_eq.mpr (covBy_rank h).symm

end D5.S3.Combinatorics.PriorityLattice.ForestCovers

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers

private theorem finite_exists_lower_cover {A : Type*} [PartialOrder A] [OrderBot A] [Finite A]
    {x : A} (hx : x ≠ ⊥) : ∃ y, y ⋖ x := by
  have hne : (Set.Iio x).Nonempty := ⟨⊥, bot_lt_iff_ne_bot.mpr hx⟩
  obtain ⟨y,hy,hmax⟩ := (Set.toFinite (Set.Iio x)).exists_maximal hne
  refine ⟨y,hy,?_⟩
  intro z hyz hzx
  have hzy : z <= y := hmax hzx hyz.le
  exact (not_lt_of_ge hzy) hyz

private theorem rank_map_orderIso
    {A B : Type*} [PartialOrder A] [PartialOrder B] [OrderBot A] [OrderBot B] [Finite A]
    (f : A -> Nat) (g : B -> Nat) (hf : StrictMono f)
    (hf0 : f ⊥ = 0) (hg0 : g ⊥ = 0)
    (hfstep : forall {x y}, x ⋖ y -> f y = f x+1)
    (hgstep : forall {x y}, x ⋖ y -> g y = g x+1)
    (e : A ≃o B) (x : A) : g (e x) = f x := by
  have hall : forall k, forall x, f x = k -> g (e x) = f x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hk
      by_cases hx : x = ⊥
      · subst x; rw [map_bot,hg0,hf0]
      · obtain ⟨y,hy⟩ := finite_exists_lower_cover hx
        have hfy := hfstep hy
        have hgy := hgstep ((apply_covBy_apply_iff e).mpr hy)
        have hprev := ih (f y) (by have := hf hy.lt; omega) y rfl
        omega
  exact hall (f x) x rfl

theorem atom_card_orderIso {A B : Type*} [PartialOrder A] [PartialOrder B]
    [OrderBot A] [OrderBot B] (e : A ≃o B) :
    Nat.card {a : A // IsAtom a} = Nat.card {b : B // IsAtom b} := by
  exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun a => (e.isAtom_iff a).symm))

private theorem coatom_card_orderIso {A B : Type*} [PartialOrder A] [PartialOrder B]
    [OrderTop A] [OrderTop B] (e : A ≃o B) :
    Nat.card {a : A // IsCoatom a} = Nat.card {b : B // IsCoatom b} := by
  exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun a => (e.isCoatom_iff a).symm))

end D5.S3.Combinatorics.PriorityLattice.ForestCovers

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers
namespace IntervalForest

variable {n : Nat}

theorem eq_of_same_support_below {P Q R : IntervalForest n}
    (hQP : Q <= P) (hRP : R <= P) (hs : (support Q) = (support R)) : Q = R := by
  apply ext
  funext v
  have hmem : Q.parent v ≠ none <-> R.parent v ≠ none := by
    rw [← mem_support,← mem_support,hs]
  cases hq : Q.parent v with
  | none =>
    have hr : R.parent v = none := by simpa [hq] using not_congr hmem
    exact hr.symm
  | some p =>
    have hrn : R.parent v ≠ none := hmem.mp (by simp [hq])
    obtain ⟨q,hr⟩ := Option.ne_none_iff_exists'.mp hrn
    have hpP := (le_iff_parent Q P).mp hQP v p hq
    have hqP := (le_iff_parent R P).mp hRP v q hr
    have hpq : p = q := Option.some.inj (hpP.symm.trans hqP)
    rw [hr,hpq]

private theorem cover_support_diff_singleton {Q P : IntervalForest n} (h : Q ⋖ P) :
    ∃ v, (support P) \ (support Q) = {v} := by
  classical
  apply Finset.card_eq_one.mp
  rw [Finset.card_sdiff_of_subset (support_mono h.le)]
  have hc := (covBy_iff_edgeCount.mp h).2
  change (support P).card = (support Q).card+1 at hc
  omega

private noncomputable def lowerCoverEdge (P : IntervalForest n) (Q : {Q : IntervalForest n // Q ⋖ P}) :
    {v : Fin (n+1) // v ∈ (support P)} := by
  classical
  let v := (cover_support_diff_singleton Q.property).choose
  have hv : v ∈ (support P) \ (support Q.val) := by
    rw [(cover_support_diff_singleton Q.property).choose_spec]
    exact Finset.mem_singleton_self v
  exact ⟨v,(Finset.mem_sdiff.mp hv).1⟩

private theorem lowerCoverEdge_injective (P : IntervalForest n) : Function.Injective (lowerCoverEdge P) := by
  classical
  intro Q R h
  apply Subtype.ext
  apply eq_of_same_support_below Q.property.le R.property.le
  have hval := congrArg Subtype.val h
  change (cover_support_diff_singleton Q.property).choose =
    (cover_support_diff_singleton R.property).choose at hval
  have hdiff : (support P) \ (support Q.val) = (support P) \ (support R.val) := by
    rw [(cover_support_diff_singleton Q.property).choose_spec,
      (cover_support_diff_singleton R.property).choose_spec,hval]
  have hQP := support_mono Q.property.le
  have hRP := support_mono R.property.le
  ext v
  have hmem := Finset.ext_iff.mp hdiff v
  simp only [Finset.mem_sdiff] at hmem
  constructor
  · intro hvQ
    by_contra hvR
    have hvP := hQP hvQ
    exact (hmem.mpr ⟨hvP,hvR⟩).2 hvQ
  · intro hvR
    by_contra hvQ
    have hvP := hRP hvR
    exact (hmem.mp ⟨hvP,hvQ⟩).2 hvR

theorem lower_covers_card_le (P : IntervalForest n) :
    Nat.card {Q : IntervalForest n // Q ⋖ P} <= (edgeCount P) := by
  have h := Nat.card_le_card_of_injective (lowerCoverEdge P) (lowerCoverEdge_injective P)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, edgeCount] using h

end IntervalForest

private noncomputable def forestCoatomEquiv (n : Nat) :
    {P : IntervalForest n // IsTree P} ≃ {x : (WithTop (IntervalForest n)) // IsCoatom x} := by
  refine Equiv.ofBijective (fun P => ⟨(P.val : (WithTop (IntervalForest n))), (coatom_iff_tree P.val).mpr P.property⟩) ?_
  constructor
  · intro P Q h
    apply Subtype.ext
    have hcoe := congrArg Subtype.val h
    exact WithTop.coe_inj.mp hcoe
  · intro x
    have hxne : x.val ≠ ⊤ := x.property.ne_top
    change (x.val : WithTop (IntervalForest n)) ≠ ⊤ at hxne
    obtain ⟨P,hP⟩ := WithTop.ne_top_iff_exists.mp hxne
    have hP' : (P : (WithTop (IntervalForest n))) = x.val := hP
    have hx : IsCoatom (P : (WithTop (IntervalForest n))) := hP'.symm ▸ x.property
    refine ⟨⟨P,(coatom_iff_tree P).mp hx⟩,?_⟩
    apply Subtype.ext
    exact hP

private theorem pi_coatom_card (n : Nat) : Nat.card {x : (WithTop (IntervalForest n)) // IsCoatom x} = n.factorial := by
  rw [← Nat.card_congr (forestCoatomEquiv n)]
  exact increasing_tree_card n

private noncomputable def idealCoatomEquiv {n : Nat} (P : IntervalForest n) :
    {Q : IntervalForest n // Q ⋖ P} ≃ {x : Set.Iic (P : (WithTop (IntervalForest n))) // IsCoatom x} := by
  refine Equiv.ofBijective (fun Q => ⟨⟨(Q.val : (WithTop (IntervalForest n))), by
    change (Q.val : WithTop (IntervalForest n)) <= P
    exact WithTop.coe_le_coe.mpr Q.property.le⟩,?_⟩) ?_
  · rw [Set.Iic.isCoatom_iff]
    change (Q.val : WithTop (IntervalForest n)) ⋖ P
    exact WithTop.coe_covBy_coe.mpr Q.property
  · constructor
    · intro Q R h
      apply Subtype.ext
      have hc := congrArg (fun x => x.val.val) h
      exact WithTop.coe_inj.mp hc
    · intro x
      have hx : x.val.val ⋖ (P : (WithTop (IntervalForest n))) := Set.Iic.isCoatom_iff.mp x.property
      have hxne : x.val.val ≠ ⊤ := by
        intro he
        have hlt := hx.lt
        rw [he] at hlt
        exact (not_lt_of_ge le_top) hlt
      change (x.val.val : WithTop (IntervalForest n)) ≠ ⊤ at hxne
      obtain ⟨Q,hQ⟩ := WithTop.ne_top_iff_exists.mp hxne
      have hcov : Q ⋖ P := by
        apply WithTop.coe_covBy_coe.mp
        simpa only [hQ] using hx
      refine ⟨⟨Q,hcov⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hQ

private theorem ideal_coatoms_le {n : Nat} (P : IntervalForest n) :
    Nat.card {x : Set.Iic (P : (WithTop (IntervalForest n))) // IsCoatom x} <= (edgeCount P) := by
  rw [← Nat.card_congr (idealCoatomEquiv P)]
  exact (lower_covers_card_le P)

end D5.S3.Combinatorics.PriorityLattice.ForestCovers

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers


@[simp] private theorem rank_bot (n : Nat) : rank (⊥ : (WithTop (IntervalForest n))) = 0 := by
  change (edgeCount (IntervalForest.empty n)) = 0
  simp [IntervalForest.edgeCount,IntervalForest.support,IntervalForest.empty]

private theorem iic_covBy_iff {A : Type*} [PartialOrder A] {x : A} {y z : Set.Iic x} :
    y ⋖ z <-> y.val ⋖ z.val := by
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => c <= x) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Iic

private theorem ici_covBy_iff {A : Type*} [PartialOrder A] {x : A} {y z : Set.Ici x} :
    y ⋖ z <-> y.val ⋖ z.val := by
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => x <= c) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Ici

theorem ideal_iso_rank {n m : Nat} {x : (WithTop (IntervalForest n))} (e : Set.Iic x ≃o (WithTop (IntervalForest m))) :
    rank x = m+1 := by
  have hf : StrictMono (fun y : Set.Iic x => rank y.val) := by
    intro y z hyz
    exact grade_strictMono (𝕆 := Nat) (show (y.val : (WithTop (IntervalForest n))) < z.val from hyz)
  have hf0 : (fun y : Set.Iic x => rank y.val) ⊥ = 0 := rank_bot n
  have hfstep : forall {y z : Set.Iic x}, y ⋖ z -> rank z.val = rank y.val+1 := by
    intro y z hyz
    exact covBy_rank (iic_covBy_iff.mp hyz)
  have h := rank_map_orderIso (fun y : Set.Iic x => rank y.val) (@rank m) hf hf0 (rank_bot m)
    hfstep (fun h => covBy_rank h) e ⊤
  have het : e ⊤ = ⊤ := map_top e
  rw [het] at h
  change m+1 = rank x at h
  exact h.symm

theorem filter_iso_rank {n m : Nat} {x : (WithTop (IntervalForest n))} (e : Set.Ici x ≃o (WithTop (IntervalForest m))) :
    m+1 = n+1-rank x := by
  let f : Set.Ici x -> Nat := fun y => rank y.val-rank x
  have hf : StrictMono f := by
    intro y z hyz
    have hlt := rank_strictMono n hyz
    have hy := (rank_strictMono n).monotone y.property
    dsimp [f]
    omega
  have hf0 : f ⊥ = 0 := by dsimp [f]; omega
  have hfstep : forall {y z : Set.Ici x}, y ⋖ z -> f z = f y+1 := by
    intro y z hyz
    have hstep := covBy_rank (ici_covBy_iff.mp hyz)
    have hy := (rank_strictMono n).monotone y.property
    dsimp [f]
    omega
  have h := rank_map_orderIso f (@rank m) hf hf0 (rank_bot m)
    hfstep (fun h => covBy_rank h) e ⊤
  have het : e ⊤ = ⊤ := map_top e
  rw [het] at h
  change m+1 = n+1-rank x at h
  exact h

theorem top_filter_not_iso (n m : Nat) : ¬ Nonempty (Set.Ici (⊤ : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m))) := by
  rintro ⟨e⟩
  have h := filter_iso_rank e
  change m+1 = n+1-(n+1) at h
  omega

private theorem factorial_gt_succ (m : Nat) (hm : 3 <= m) : m+1 < m.factorial := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    nlinarith

end D5.S3.Combinatorics.PriorityLattice.ForestCovers

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers

theorem forest_ideal_index_le_two {n m : Nat} (P : IntervalForest n)
    (e : Set.Iic (P : (WithTop (IntervalForest n))) ≃o (WithTop (IntervalForest m))) : m <= 2 := by
  have hk : (edgeCount P) = m+1 := ideal_iso_rank e
  have hc := coatom_card_orderIso e
  rw [pi_coatom_card] at hc
  have hbound := ideal_coatoms_le P
  rw [hc,hk] at hbound
  by_contra hm
  have h3 : 3 <= m := by omega
  exact (not_lt_of_ge hbound) (factorial_gt_succ m h3)

end D5.S3.Combinatorics.PriorityLattice.ForestCovers

namespace D5.S3.Combinatorics.PriorityLattice.ForestCovers
namespace IntervalForest

variable {n : Nat}

private theorem cover_parent_update {P Q : IntervalForest n} (h : P ⋖ Q) :
    ∃ v p, P.parent v = none ∧ Q.parent v = some p ∧
      (forall w, w ≠ v -> Q.parent w = P.parent w) := by
  classical
  obtain ⟨v,hv⟩ := cover_support_diff_singleton h
  have hvdiff : v ∈ (support Q) \ (support P) := by rw [hv]; simp
  have hPv : P.parent v = none := by
    have hh := (Finset.mem_sdiff.mp hvdiff).2
    simpa only [mem_support,not_not] using hh
  have hQv : Q.parent v ≠ none := (mem_support Q v).mp (Finset.mem_sdiff.mp hvdiff).1
  obtain ⟨p,hp⟩ := Option.ne_none_iff_exists'.mp hQv
  refine ⟨v,p,hPv,hp,?_⟩
  intro w hw
  cases hPw : P.parent w with
  | some q => exact (le_iff_parent P Q).mp h.le w q hPw
  | none =>
    by_contra hQw
    have hwm : w ∈ (support Q) \ (support P) := by simp [hQw,hPw]
    rw [hv,Finset.mem_singleton] at hwm
    exact hw hwm

theorem cover_adjacent_roots {P Q : IntervalForest n} (h : P ⋖ Q) :
    ∃ v p, P.parent v = none ∧ Q.parent v = some p ∧ p < v ∧
      (forall w, p < w -> w < v -> P.parent w ≠ none) ∧
      (forall w, w ≠ v -> Q.parent w = P.parent w) := by
  obtain ⟨v,p,hPv,hQv,hsame⟩ := cover_parent_update h
  refine ⟨v,p,hPv,hQv,Q.increasing _ _ hQv,?_,hsame⟩
  intro w hpw hwv
  have hnon := Q.no_skipped_root hQv hpw hwv.le
  rwa [hsame w hwv.ne] at hnon

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.ForestCovers
