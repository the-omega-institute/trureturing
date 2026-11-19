/- GID: D5/S3/Combinatorics/Graph/StarForming/LongCoreWord
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/LongCoreWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.word_dissociates; instance=D5/S3/Combinatorics/Graph/StarForming/LongCoreWord.inside_dissociates
   digest: Actual separated words of twenty-vertex core patterns induce dissociation. -/

import D5.S3.Combinatorics.Graph.StarForming.FiniteCover
import D5.S3.Combinatorics.Graph.StarForming.FiniteMasks


/-! Original proof bodies and exact pattern tables from subquorum-colorings,
revision 48728b42d39ab3de5de251c61da5a404ec418a69,
formal/StarForming/LongCoreWord.lean. Apache-2.0, The Omega Institute contributors.
Numerical parameter suffixes are not inferred without their graph hypotheses. -/

namespace D5.S3.Combinatorics.Graph.StarForming.LongCoreWord

open D5.S3.Combinatorics.Graph.StarForming.DissociationCover
open scoped BigOperators

def insideRows : List (List Nat) := [
  [1, 6],
  [0, 2, 7],
  [1, 3, 8],
  [2, 4, 9],
  [3, 5, 10],
  [4, 11],
  [0, 12, 18],
  [1, 13, 19],
  [2, 14, 18],
  [3, 15, 19],
  [4, 16, 18],
  [5, 17, 19],
  [6],
  [7, 14],
  [8, 13],
  [9, 16],
  [10, 15],
  [11],
  [6, 8, 10],
  [7, 9, 11]]

def insideAdj (first second : Fin 20) : Prop :=
  (insideRows.getD first.val []).contains second.val = true

instance : DecidableRel insideAdj :=
  fun first second => inferInstanceAs (Decidable
    ((insideRows.getD first.val []).contains second.val = true))

def pattern (kind : Bool) : List Nat :=
  if kind then [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 18, 19]
  else [1, 4, 6, 7, 8, 9, 10, 11, 14, 15]

def selected (kind : Bool) (vertex : Fin 20) : Prop :=
  (pattern kind).contains vertex.val = true

instance (kind : Bool) : DecidablePred (selected kind) :=
  fun vertex => inferInstanceAs (Decidable ((pattern kind).contains vertex.val = true))

def forward (first second : Fin 20) : Prop :=
  (first.val = 5 ∧ second.val = 0) ∨ (first.val = 17 ∧ second.val = 12)

instance : DecidableRel forward :=
  fun first second => inferInstanceAs (Decidable
    ((first.val = 5 ∧ second.val = 0) ∨ (first.val = 17 ∧ second.val = 12)))

def wordAdj {Block : Type} (successor : Block → Block)
    (first second : Block × Fin 20) : Prop :=
  (first.1 = second.1 ∧ insideAdj first.2 second.2) ∨
  (successor first.1 = second.1 ∧ forward first.2 second.2) ∨
  (successor second.1 = first.1 ∧ forward second.2 first.2)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem inside_dissociates (kind : Bool) : Dissociates insideAdj (selected kind) := by
  cases kind <;> unfold Dissociates <;> decide

theorem pattern_counts : ∀ kind : Bool,
    ((List.finRange 20).filter (fun vertex => decide (selected kind vertex))).length =
      (if kind then 12 else 10) ∧
    (([(12, 13), (14, 15), (16, 17)] : List (Nat × Nat)).filter
      (fun pair => !(pattern kind).contains pair.1 && !(pattern kind).contains pair.2)).length =
      (if kind then 1 else 2) := by
  decide

theorem forward_selected_forces_A :
    ∀ firstKind secondKind : Bool, ∀ first second : Fin 20,
      selected firstKind first → selected secondKind second → forward first second →
        firstKind = true ∧ secondKind = true := by
  decide

theorem selected_edge_internal {Block : Type} (successor : Block → Block)
    (word : Block → Bool)
    (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true))
    (first second : Block × Fin 20)
    (hfirst : selected (word first.1) first.2)
    (hsecond : selected (word second.1) second.2)
    (hedge : wordAdj successor first second) :
    first.1 = second.1 ∧ insideAdj first.2 second.2 := by
  rcases hedge with hinternal | hforward | hbackward
  · exact hinternal
  · obtain ⟨hnext, hboundary⟩ := hforward
    have hkind := forward_selected_forces_A _ _ _ _ hfirst hsecond hboundary
    have hnextKind : word (successor first.1) = true := by
      rw [hnext]
      exact hkind.2
    exact (hseparation first.1 ⟨hkind.1, hnextKind⟩).elim
  · obtain ⟨hnext, hboundary⟩ := hbackward
    have hkind := forward_selected_forces_A _ _ _ _ hsecond hfirst hboundary
    have hnextKind : word (successor second.1) = true := by
      rw [hnext]
      exact hkind.2
    exact (hseparation second.1 ⟨hkind.1, hnextKind⟩).elim

theorem word_dissociates {Block : Type} (successor : Block → Block)
    (word : Block → Bool)
    (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) :
    Dissociates (wordAdj successor)
      (fun vertex => selected (word vertex.1) vertex.2) := by
  intro center first second hcenter hfirst hsecond hfirstEdge hsecondEdge
  have hfirstInside := selected_edge_internal successor word hseparation
    center first hcenter hfirst hfirstEdge
  have hsecondInside := selected_edge_internal successor word hseparation
    center second hcenter hsecond hsecondEdge
  have hfirstSelected : selected (word center.1) first.2 := by
    rw [hfirstInside.1]
    exact hfirst
  have hsecondSelected : selected (word center.1) second.2 := by
    rw [hsecondInside.1]
    exact hsecond
  have hlocal := inside_dissociates (word center.1) center.2 first.2 second.2
    hcenter hfirstSelected hsecondSelected hfirstInside.2 hsecondInside.2
  exact Prod.ext (hfirstInside.1.symm.trans hsecondInside.1) hlocal

open StarFormingDissociationRefutation

/-- The original inside graph is simple; no boundary edges have been added. -/
theorem inside_simple :
    (∀ v : Fin 20, ¬ insideAdj v v) ∧
    (∀ v w : Fin 20, insideAdj v w ↔ insideAdj w v) := by
  unfold insideAdj insideRows
  decide +kernel

/-- A word interface gives a finite simple graph even for arbitrary successor
maps. The selection theorem retains its explicit no-adjacent-A hypothesis. -/
def graph {Block : Type} (successor : Block → Block) : SimpleGraph (Block × Fin 20) where
  Adj := wordAdj successor
  symm := ⟨by
    intro a b h
    rcases h with ⟨hab,he⟩ | hf | hb
    · exact Or.inl ⟨hab.symm,(inside_simple.2 _ _).mp he⟩
    · exact Or.inr (Or.inr hf)
    · exact Or.inr (Or.inl hb)⟩
  loopless := ⟨by
    intro a h
    rcases h with hi | hf | hb
    · exact inside_simple.1 _ hi.2
    · rcases hf.2 with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> omega
    · rcases hb.2 with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> omega⟩

instance {Block : Type} [DecidableEq Block] (successor : Block → Block) :
    DecidableRel (graph successor).Adj := fun a b =>
  inferInstanceAs (Decidable (
    (a.1 = b.1 ∧ insideAdj a.2 b.2) ∨
    (successor a.1 = b.1 ∧ forward a.2 b.2) ∨
    (successor b.1 = a.1 ∧ forward b.2 a.2)))

variable {Block : Type} [Fintype Block] [DecidableEq Block]

def selectedSet (word : Block → Bool) : Finset (Block × Fin 20) :=
  Finset.univ.filter (fun v => selected (word v.1) v.2)

/-- The actual word selection has the sum of its original pattern sizes. -/
theorem selectedSet_card (word : Block → Bool) :
    (selectedSet word).card = ∑ i : Block, (if word i then 12 else 10) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (by intro v hv; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i hi
  have he : ((selectedSet word).filter (fun v => v.1 = i)) =
      (Finset.univ.filter (selected (word i))).image (fun v : Fin 20 => (i,v)) := by
    ext v
    simp only [selectedSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨hs,heq⟩
      exact ⟨v.2,heq ▸ hs,Prod.ext heq.symm rfl⟩
    · rintro ⟨w,hw,he⟩
      subst v
      exact ⟨hw,rfl⟩
  rw [he,Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
  have hh := (pattern_counts (word i)).1
  rw [FiniteMasks.list_count] at hh
  simpa using hh

/-- A separated word gives a genuine canonical dissociation lower bound. -/
theorem beta_word_lower (successor : Block → Block) (word : Block → Bool)
    (hseparation : ∀ block, ¬ (word block = true ∧ word (successor block) = true)) :
    (∑ i : Block, (if word i then 12 else 10)) ≤ beta (graph successor) 2 := by
  classical
  rw [← selectedSet_card word]
  have hi : IsKIndependent (graph successor) 2 (selectedSet word) := by
    apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    intro center hc first hf second hs ha hb
    exact word_dissociates successor word hseparation center first second
      (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hf).2
      (Finset.mem_filter.mp hs).2 ha hb
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

end D5.S3.Combinatorics.Graph.StarForming.LongCoreWord
