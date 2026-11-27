/- GID: D5/S3/Combinatorics/UnorderedTrees/ForkDecoration
   generality: I
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/ForkDecoration
   mirror-E: none(waiver:unordered-tree-fork-decoration)
   anchors: []
   utility: none
   digest: Normalized leaf decorations classify the actual qualifying unordered rooted trees. -/

import D5.S3.Combinatorics.UnorderedTrees.LeafDecoration
import Mathlib.SetTheory.Cardinal.Finite

/-! Size-preserving classification of rooted trees with equal vertex-height and internal count. -/

namespace D5.S3.Combinatorics.UnorderedTrees.ForkDecoration

open ParentTree LeafPruning OneFork LeafDecoration
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The terminal counts have an implicit mandatory leaf each. Equal-arm counts are sorted. -/
@[ext] structure Counts (b c : ℕ) where
  spine : Fin (b + c + 1) → ℕ
  short : ℕ
  long : ℕ
  sorted : c = 0 → short ≤ long

abbrev Data := Σ b : ℕ, Σ c : ℕ, Counts b c

/-- Total vertices after attaching the leaf fibres. -/
def weight : Data → ℕ
  | ⟨b, c, r⟩ => b + c + 5 + ∑ i, r.spine i + r.short + r.long

abbrev Weighted (n : ℕ) := {d : Data // weight d = n}
abbrev Qualifying (n : ℕ) := {T : TreeClass n // classHeight T = classInternalCount T}

def Counts.leaves {b c : ℕ} (r : Counts b c) : Fork b c → ℕ
  | .inl i => r.spine i
  | .inr false => r.short + 1
  | .inr true => r.long + 1

private theorem terminal_positive {b c : ℕ} (r : Counts b c) (p : Fork b c)
    (hp : ¬ Internal (fork b c) p) : 0 < r.leaves p := by
  rcases p with i | j
  · exact (hp (fork_internal_spine b c i)).elim
  · cases j <;> simp [Counts.leaves]

private def model {b c : ℕ} (r : Counts b c) := inflate (fork b c) r.leaves

private theorem model_root {b c : ℕ} (r : Counts b c) : Internal (model r) (model r).root :=
  internal_inflate _ _ (terminal_positive r) _

private def modelCore {b c : ℕ} (r : Counts b c) :
    Iso (fork b c) (prune (model r) (model_root r)) :=
  pruneInflateIso _ _ (terminal_positive r)

private theorem model_fibre {b c : ℕ} (r : Counts b c) (p : Fork b c) :
    Fintype.card (LeafFibre (model r) ((modelCore r).equiv p)) = r.leaves p := by
  unfold model modelCore
  simpa only [Fintype.card_fin] using
    (Fintype.card_congr (inflateLeafIso (fork b c) r.leaves (terminal_positive r) p)).symm

private theorem card_model {b c : ℕ} (r : Counts b c) :
    Fintype.card (Inflated r.leaves) = weight ⟨b, c, r⟩ := by
  rw [card_inflate, card_fork, Fintype.sum_sum_type]
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  rw [Finset.sum_insert (show false ∉ ({true} : Finset Bool) by simp), Finset.sum_singleton]
  simp only [Counts.leaves, weight]
  omega

private theorem model_qualifies {b c : ℕ} (r : Counts b c) :
    height (model r) = internalCount (model r) := by
  apply (pruning_reduction _ (model_root r)).2.mpr
  rw [← Fintype.card_congr (modelCore r).equiv, ← iso_height (modelCore r), card_fork,
    height_fork]

private theorem counts_eq_of_iso {b c : ℕ} {r s : Counts b c}
    (e : Iso (fork b c) (fork b c)) (h : ∀ p, r.leaves p = s.leaves (e.equiv p)) :
    r = s := by
  have hspine : r.spine = s.spine := by
    funext i
    simpa only [fork_iso_spine e i, Counts.leaves] using h (.inl i)
  apply Counts.ext hspine
  · have hfalse := h (.inr false)
    have htrue := h (.inr true)
    rcases fork_iso_tips e with ⟨hf, ht⟩ | ⟨hc, hf, ht⟩
    · simpa [hf, Counts.leaves] using hfalse
    · simp only [hf, Counts.leaves] at hfalse
      simp only [ht, Counts.leaves] at htrue
      have hr := r.sorted hc
      have hs := s.sorted hc
      omega
  · have hfalse := h (.inr false)
    have htrue := h (.inr true)
    rcases fork_iso_tips e with ⟨hf, ht⟩ | ⟨hc, hf, ht⟩
    · simpa [ht, Counts.leaves] using htrue
    · simp only [hf, Counts.leaves] at hfalse
      simp only [ht, Counts.leaves] at htrue
      have hr := r.sorted hc
      have hs := s.sorted hc
      omega

private theorem model_injective {b c b' c' : ℕ} (r : Counts b c) (s : Counts b' c')
    (e : Iso (model r) (model s)) : (⟨b, c, r⟩ : Data) = ⟨b', c', s⟩ := by
  obtain ⟨f, hf⟩ := (iso_iff_fibres (model_root r) (model_root s)).mp ⟨e⟩
  obtain ⟨hb, hc⟩ := fork_iso_parameters ((modelCore r).trans (f.trans (modelCore s).symm))
  subst b'
  subst c'
  let g := (modelCore r).trans (f.trans (modelCore s).symm)
  have hmatch (p : Fork b c) : r.leaves p = s.leaves (g.equiv p) := by
    rw [← model_fibre r p, hf, ← model_fibre s (g.equiv p)]
    simp [g, Iso.trans, Iso.symm]
  rw [counts_eq_of_iso g hmatch]

private theorem model_surjective {V : Type u} [Fintype V] (T : Tree V)
    (ht : height T = internalCount T) : ∃ (d : Data),
      weight d = Fintype.card V ∧ Nonempty (Iso (model d.2.2) T) := by
  let hr := qualifying_root T ht
  obtain ⟨b, c, ⟨g⟩⟩ := exists_fork_iso (prune T hr) ((pruning_reduction T hr).2.mp ht)
  let mass (p : Core T) := Fintype.card (LeafFibre T p)
  have horient : ∃ e : Iso (fork b c) (prune T hr),
      c = 0 → mass (e.equiv (.inr false)) ≤ mass (e.equiv (.inr true)) := by
    by_cases h : c = 0
    · subst c
      by_cases hle : mass (g.equiv (.inr false)) ≤ mass (g.equiv (.inr true))
      · exact ⟨g, fun _ => hle⟩
      · exact ⟨(swapTips b).trans g, fun _ => (Nat.le_of_lt (Nat.lt_of_not_ge hle))⟩
    · exact ⟨g, fun hc => (h hc).elim⟩
  obtain ⟨e, hsort⟩ := horient
  have hpos (p : Bool) : 0 < mass (e.equiv (.inr p)) :=
    leaf_pos_of_terminal T hr _ ((iso_internal e _).not.mp (fork_terminal b c p))
  let r : Counts b c :=
    ⟨fun i => mass (e.equiv (.inl i)), mass (e.equiv (.inr false)) - 1,
      mass (e.equiv (.inr true)) - 1, fun hc => Nat.sub_le_sub_right (hsort hc) 1⟩
  have hread (p : Fork b c) : r.leaves p = mass (e.equiv p) := by
    rcases p with i | j
    · rfl
    · cases j
      · change mass (e.equiv (.inr false)) - 1 + 1 = _
        have hp := hpos false
        omega
      · change mass (e.equiv (.inr true)) - 1 + 1 = _
        have hp := hpos true
        omega
  let f := (modelCore r).symm.trans e
  have hmatch (p : Core (model r)) :
      Fintype.card (LeafFibre (model r) p) = mass (f.equiv p) := by
    obtain ⟨q, rfl⟩ := (modelCore r).equiv.surjective p
    rw [model_fibre, hread]
    simp [f, Iso.trans, Iso.symm]
  obtain ⟨j, _⟩ := extendIso f hmatch
  exact ⟨⟨b, c, r⟩, (card_model r).symm.trans (Fintype.card_congr j.equiv), ⟨j⟩⟩

private def modelLabel {n : ℕ} (d : Weighted n) : Inflated d.val.2.2.leaves ≃ Fin n :=
  Fintype.equivFinOfCardEq ((card_model d.val.2.2).trans d.property)

private def labelled {n : ℕ} (d : Weighted n) : Tree (Fin n) :=
  relabel (model d.val.2.2) (modelLabel d)

private def compileData {n : ℕ} (d : Weighted n) : Qualifying n := by
  let e : Iso (model d.val.2.2) (labelled d) :=
    relabelIso (model d.val.2.2) (modelLabel d)
  refine ⟨Quotient.mk _ (labelled d), ?_⟩
  change height (labelled d) = internalCount (labelled d)
  unfold internalCount
  rw [← iso_height e, ← Fintype.card_congr (internalEquiv e)]
  exact model_qualifies d.val.2.2

/-- Actual qualifying isomorphism classes are in bijection with weight-matched decorations. -/
def classification (n : ℕ) : Weighted n ≃ Qualifying n :=
  Equiv.ofBijective compileData (by
    constructor
    · intro d d' h
      have hq : Quotient.mk (treeSetoid n) (labelled d) = Quotient.mk _ (labelled d') :=
        congrArg Subtype.val h
      obtain ⟨e⟩ := (code_eq_iff_iso (labelled d) (labelled d')).mp (Quotient.exact hq)
      apply Subtype.ext
      exact model_injective _ _ ((relabelIso _ (modelLabel d)).trans
        (e.trans (relabelIso _ (modelLabel d')).symm))
    · rintro ⟨q, hq⟩
      obtain ⟨T, rfl⟩ := Quotient.exists_rep q
      obtain ⟨d, hd, ⟨e⟩⟩ := model_surjective T hq
      let w : Weighted n := ⟨d, hd.trans (Fintype.card_fin n)⟩
      refine ⟨w, Subtype.ext (Quotient.sound ?_)⟩
      exact (code_eq_iff_iso (labelled w) T).mpr
        ⟨(relabelIso _ (modelLabel w)).symm.trans e⟩)

/-- The normalized decorations retain the original count at every size. -/
theorem card_weighted (n : ℕ) : Nat.card (Weighted n) = a n := by
  rw [Nat.card_congr (classification n), Nat.card_eq_fintype_card]
  rfl

#print axioms classification
#print axioms card_weighted

end

end D5.S3.Combinatorics.UnorderedTrees.ForkDecoration
