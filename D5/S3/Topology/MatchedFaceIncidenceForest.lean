/- GID: D5/S3/Topology/MatchedFaceIncidenceForest
   generality: G
   mirror-B: D5/B/S3/Topology/MatchedFaceIncidenceForest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: The removed-face incidence graph of an elementary collapse sequence is a forest under a coface bound. -/

import OmegaBuild.Commands
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Max

/-!
# Matched face incidence forest

The incidence graph on faces removed during a fixed-dimensional elementary
collapse sequence is a forest if each removed lower face has at most one other
original coface of the same cardinality as its assigned upper face.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.Topology.MatchedFaceIncidenceForest

variable {V : Type*} {n : ℕ}

/-- The selected lower faces of cardinality `n`. -/
abbrev MatchedLower (n : ℕ) (K : PreAbstractSimplicialComplex V) (matched : Set (Finset V)) :=
  {e : Finset V // e ∈ K ∧ e.card = n ∧ e ∈ matched}

/-- The original faces of cardinality `n + 1`. -/
abbrev UpperFace (n : ℕ) (K : PreAbstractSimplicialComplex V) :=
  {t : Finset V // t ∈ K ∧ t.card = n + 1}

/-- Incidence by face inclusion, with one side for each face size. -/
def incidenceGraph (n : ℕ) (K : PreAbstractSimplicialComplex V) (matched : Set (Finset V)) :
    SimpleGraph (MatchedLower n K matched ⊕ UpperFace n K) where
  Adj
    | .inl e, .inr t => e.val ⊆ t.val
    | .inr t, .inl e => e.val ⊆ t.val
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> exact h⟩
  loopless := ⟨by
    intro x h
    cases x <;> exact h⟩

private theorem acyclic_of_rank {G : SimpleGraph V} (rank : V → ℕ)
    (hne : ∀ ⦃u v⦄, G.Adj u v → rank u ≠ rank v)
    (hunique : ∀ ⦃v x y⦄, G.Adj x v → G.Adj y v →
      rank x < rank v → rank y < rank v → x = y) :
    G.IsAcyclic := by
  classical
  intro v cycle hc
  obtain ⟨w, hw, hmax⟩ := cycle.support.toFinset.exists_max_image rank
    ⟨v, List.mem_toFinset.mpr cycle.start_mem_support⟩
  have hw' := List.mem_toFinset.mp hw
  let rotated := cycle.rotate w hw'
  have hr : rotated.IsCycle := hc.rotate hw'
  have rank_le {x : V} (hx : x ∈ rotated.support) : rank x ≤ rank w :=
    hmax x (List.mem_toFinset.mpr ((cycle.mem_support_rotate_iff w hw').mp hx))
  have hs := (rotated.adj_snd hr.not_nil).symm
  have hp := rotated.adj_penultimate hr.not_nil
  exact hr.snd_ne_penultimate (hunique hs hp
    ((rank_le (rotated.getVert_mem_support 1)).lt_of_ne (hne hs))
    ((rank_le (rotated.getVert_mem_support (rotated.length - 1))).lt_of_ne (hne hp)))

/-- A collapse matching with at most one additional coface per matched lower face
gives a forest if each additional coface precedes the assigned upper face. -/
theorem incidenceGraph_isAcyclic
    {K : PreAbstractSimplicialComplex V} {matched : Set (Finset V)}
    (assigned : MatchedLower n K matched ↪ UpperFace n K) (time : UpperFace n K → ℕ)
    (hassigned : ∀ e, e.val ⊆ (assigned e).val)
    (hadditional : ∀ e : MatchedLower n K matched,
      {t : UpperFace n K | e.val ⊆ t.val ∧ t ≠ assigned e}.Subsingleton)
    (hearlier : ∀ ⦃e : MatchedLower n K matched⦄ ⦃t : UpperFace n K⦄,
      e.val ⊆ t.val → t ≠ assigned e → time t < time (assigned e)) :
    (incidenceGraph n K matched).IsAcyclic := by
  let rank : MatchedLower n K matched ⊕ UpperFace n K → ℕ :=
    Sum.elim (fun e => 2 * time (assigned e)) (fun t => 2 * time t + 1)
  have matched_lt (e : MatchedLower n K matched) :
      (incidenceGraph n K matched).Adj (.inl e) (.inr (assigned e)) ∧
        rank (.inl e) < rank (.inr (assigned e)) := by
    refine ⟨hassigned e, ?_⟩
    change 2 * time (assigned e) < 2 * time (assigned e) + 1
    omega
  have assigned_of_lt {e : MatchedLower n K matched} {t : UpperFace n K}
      (h : e.val ⊆ t.val) (hlt : rank (.inl e) < rank (.inr t)) : t = assigned e := by
    by_contra hne
    have ht := hearlier h hne
    change 2 * time (assigned e) < 2 * time t + 1 at hlt
    omega
  apply acyclic_of_rank rank
  · intro u v huv
    cases u <;> cases v <;> simp_all [incidenceGraph, rank] <;> omega
  · intro v x y hx hy hxr hyr
    cases v with
    | inl e =>
      rcases x with f | s
      · exact False.elim hx
      rcases y with f | t
      · exact False.elim hy
      have hs : s ≠ assigned e := by
        rintro rfl
        exact (matched_lt e).2.not_gt hxr
      have ht : t ≠ assigned e := by
        rintro rfl
        exact (matched_lt e).2.not_gt hyr
      exact congrArg Sum.inr (hadditional e ⟨hx, hs⟩ ⟨hy, ht⟩)
    | inr t =>
      rcases x with e | s
      · rcases y with f | s
        · exact congrArg Sum.inl (assigned.injective
            ((assigned_of_lt hx hxr).symm.trans (assigned_of_lt hy hyr)))
        · exact False.elim hy
      · exact False.elim hx

#print axioms incidenceGraph_isAcyclic


section CollapseSequence

open D5.S3.Geometry.FiniteElementaryCollapse (CollapsePair)
open D5.S3.Geometry.FiniteRelativeSimplicialCollapse (Sequence)

variable [Fintype V] [DecidableEq V]
variable {K L : PreAbstractSimplicialComplex V}

private theorem pair_ambient_le (S : Sequence K L) :
    ∀ P ∈ S.pairs, P.ambient ≤ K := by
  induction S with
  | refl K => simp [Sequence.pairs]
  | step P T ih =>
    intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact le_rfl
    · exact (ih Q hQ).trans P.retained_le

private theorem pairwise_after_retained (S : Sequence K L) :
    S.pairs.Pairwise (fun P Q => Q.ambient ≤ P.retained) := by
  induction S with
  | refl K => exact .nil
  | step P T ih => exact .cons (pair_ambient_le T) ih

private theorem face_retained_or_removed (S : Sequence K L) {f : Finset V} (hf : f ∈ K) :
    f ∈ L ∨ ∃ P ∈ S.pairs, f = P.lower ∨ f = P.upper := by
  induction S with
  | refl K => exact Or.inl hf
  | step P T ih =>
    by_cases h : f = P.lower ∨ f = P.upper
    · exact Or.inr ⟨P, List.mem_cons_self, h⟩
    have hf' := (P.mem_retained_iff f).mpr
      ⟨hf, fun hl => h (Or.inl hl), fun hu => h (Or.inr hu)⟩
    rcases ih hf' with hL | ⟨Q, hQ, he⟩
    · exact Or.inl hL
    · exact Or.inr ⟨Q, List.mem_cons_of_mem _ hQ, he⟩

/-- The lower faces removed in the given collapse sequence. -/
def removedLowerFaces (S : Sequence K L) : Set (Finset V) :=
  {e | ∃ P ∈ S.pairs, P.lower = e}

/-- For a collapse sequence deleting every face of cardinality `n + 1` by pairing
it with a free face of cardinality `n`, the incidence graph is a forest if
each free lower face has at most one other original coface of size `n + 1`. -/
theorem incidenceGraph_isAcyclic_of_sequence (S : Sequence K L)
    (hsize : ∀ P ∈ S.pairs, P.lower.card = n)
    (hfinal : ∀ f ∈ L, f.card ≠ n + 1)
    (hcofaces : ∀ P ∈ S.pairs,
      {t : UpperFace n K | P.lower ⊆ t.val ∧ t.val ≠ P.upper}.Subsingleton) :
    (incidenceGraph n K (removedLowerFaces S)).IsAcyclic := by
  classical
  let I := Fin S.pairs.length
  let P (n : I) := S.pairs.get n
  have hmem (n : I) : P n ∈ S.pairs := List.get_mem _ _
  have hafter {a b : I} (h : a < b) : (P b).ambient ≤ (P a).retained :=
    List.pairwise_iff_get.mp (pairwise_after_retained S) a b h
  have hupper (i : I) : (P i).upper.card = n + 1 := by
    rw [CollapsePair.upper, Finset.card_insert_of_notMem (P i).apex_notMem, hsize _ (hmem i)]
  let lower (i : I) : MatchedLower n K (removedLowerFaces S) :=
    ⟨(P i).lower, pair_ambient_le S _ (hmem i) (P i).lower_mem,
      hsize _ (hmem i), ⟨P i, hmem i, rfl⟩⟩
  let upper (i : I) : UpperFace n K :=
    ⟨(P i).upper, pair_ambient_le S _ (hmem i) (P i).upper_mem, hupper i⟩
  have later_faces_distinct {a b : I} (h : a < b) :
      lower a ≠ lower b ∧ upper a ≠ upper b := by
    constructor
    · intro he
      have hh := ((P a).mem_retained_iff (P b).lower).mp
        (hafter h (P b).lower_mem)
      exact hh.2.1 (congrArg Subtype.val he).symm
    · intro he
      have hh := ((P a).mem_retained_iff (P b).upper).mp
        (hafter h (P b).upper_mem)
      exact hh.2.2 (congrArg Subtype.val he).symm
  have hlower : Function.Bijective lower := by
    constructor
    · intro a b hab
      rcases lt_trichotomy a b with hl | he | hr
      · exact ((later_faces_distinct hl).1 hab).elim
      · exact he
      · exact ((later_faces_distinct hr).1 hab.symm).elim
    · intro e
      obtain ⟨Q, hQ, he⟩ := e.property.2.2
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hQ
      refine ⟨i, Subtype.ext ?_⟩
      change (S.pairs.get i).lower = e.val
      rw [hi, he]
  have hUp : Function.Bijective upper := by
    constructor
    · intro a b hab
      rcases lt_trichotomy a b with hl | he | hr
      · exact ((later_faces_distinct hl).2 hab).elim
      · exact he
      · exact ((later_faces_distinct hr).2 hab.symm).elim
    · intro t
      rcases face_retained_or_removed S t.property.1 with hL | ⟨Q, hQ, h⟩
      · exact (hfinal _ hL t.property.2).elim
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hQ
      rcases h with he | he
      · exact (by have hc := hsize Q hQ; rw [← he, t.property.2] at hc; omega)
      · refine ⟨i, Subtype.ext ?_⟩
        change (S.pairs.get i).upper = t.val
        rw [hi, ← he]
  let lowerEquiv := Equiv.ofBijective lower hlower
  let upperEquiv := Equiv.ofBijective upper hUp
  let assigned := (lowerEquiv.symm.trans upperEquiv).toEmbedding
  let time (t : UpperFace n K) : ℕ := (upperEquiv.symm t).val
  have hassign (i : I) : assigned (lower i) = upper i := by
    change upperEquiv (lowerEquiv.symm (lowerEquiv i)) = upperEquiv i
    rw [Equiv.symm_apply_apply]
  have htime (i : I) : time (upper i) = i.val :=
    congrArg Fin.val (upperEquiv.symm_apply_apply i)
  apply incidenceGraph_isAcyclic assigned time
  · intro e
    obtain ⟨i, rfl⟩ := hlower.surjective e
    rw [hassign i]
    exact Finset.subset_insert _ _
  · intro e
    obtain ⟨i, rfl⟩ := hlower.surjective e
    rw [hassign i]
    intro t ht t' ht'
    exact hcofaces (P i) (hmem i) ⟨ht.1, fun he => ht.2 (Subtype.ext he)⟩
      ⟨ht'.1, fun he => ht'.2 (Subtype.ext he)⟩
  · intro e t hInc hOther
    obtain ⟨i, rfl⟩ := hlower.surjective e
    obtain ⟨j, rfl⟩ := hUp.surjective t
    rw [hassign i] at hOther
    rw [hassign i, htime i, htime j]
    have hne : j ≠ i := fun he => hOther (congrArg upper he)
    by_contra hj
    have hji : ¬ j < i := hj
    have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) hne.symm
    have hjmem := (P i).retained_le (hafter hij (P j).upper_mem)
    have hproper : (P i).lower ⊂ (P j).upper :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hInc, fun hEq => by
        have hc := congrArg Finset.card hEq
        rw [hsize _ (hmem i), hupper j] at hc
        omega⟩
    exact hOther (Subtype.ext ((P i).free _ hjmem hproper))

#print axioms incidenceGraph_isAcyclic_of_sequence

end CollapseSequence

end D5.S3.Topology.MatchedFaceIncidenceForest
