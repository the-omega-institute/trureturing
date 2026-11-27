/- GID: D5/S3/Topology/RankedFiberLabelObstruction
   generality: G
   mirror-B: D5/B/S3/Topology/RankedFiberLabelObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Rank bounds obstruct lifting required flags through comparison maps. -/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import OmegaBuild.Commands

/-! Bound the number of forced distinct labels supported by a single chain
inside a ranked fiber. This is the cardinality step in the ordinary
triangle-cone obstruction for Mosquera-Lois and Tanaka Question 6.3. -/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.Topology.RankedFiberLabelObstruction

variable {P A : Type*} [Preorder P] [DecidableEq A]

/-- If the labels in `required` must come from vertices with ranks in
`[lower, upper]`, one source chain can only supply as many distinct
required labels as there are ranks in that interval. -/
theorem card_required_le_of_rank (rank : P → ℕ) (hrank : StrictMono rank)
    (label : P → A) (source : Finset P) (hchain : IsChain (· < ·) (source : Set P))
    (required : Finset A) (hrequired : required ⊆ source.image label)
    (lower upper : ℕ)
    (hrange : ∀ p ∈ source, label p ∈ required → lower ≤ rank p ∧ rank p ≤ upper) :
    required.card ≤ upper + 1 - lower := by
  let used := source.filter fun p => label p ∈ required
  have hsub : required ⊆ used.image label := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (hrequired ha)
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, ha⟩, rfl⟩
  have hinj : Set.InjOn rank (used : Set P) := by
    intro x hx y hy he
    by_contra hne
    have hxs := (Finset.mem_filter.mp (show x ∈ used from hx)).1
    have hys := (Finset.mem_filter.mp (show y ∈ used from hy)).1
    rcases hchain hxs hys hne with h | h
    · exact (ne_of_lt (hrank h)) he
    · exact (ne_of_lt (hrank h)) he.symm
  have hranks : used.image rank ⊆ Finset.Icc lower upper := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hs, ha⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr (hrange p hs ha)
  calc
    required.card ≤ (used.image label).card := Finset.card_le_card hsub
    _ ≤ used.card := Finset.card_image_le
    _ = (used.image rank).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc lower upper).card := Finset.card_le_card hranks
    _ = upper + 1 - lower := Nat.card_Icc _ _

/-- If all required cofaces need a prescribed old support and just one
vertex of their containing face has that support, their witnesses lie in
its fiber. This rules out any required flag longer than the rank interval
of that fiber. -/
theorem flag_omitted_of_unique_support
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (rank : P → ℕ) (hrank : StrictMono rank)
    (project : P → V) (sourceSupport : P → Finset C) (targetSupport : V → Finset C)
    (hsupport : ∀ p, sourceSupport p = targetSupport (project p))
    (label : P → Finset V) (hcontains : ∀ p, project p ∈ label p)
    (hcarried : ∀ p v, v ∈ label p → targetSupport v ⊆ sourceSupport p)
    (support : Finset C) (face : Finset V) (selected : V)
    (hunique : ∀ v ∈ face, support ⊆ targetSupport v → v = selected)
    (required : Finset (Finset V))
    (hrequired : ∀ a ∈ required, a ⊆ face ∧ ∃ v ∈ a, support ⊆ targetSupport v)
    (lower upper : ℕ) (hsmall : upper + 1 - lower < required.card)
    (hfiber : ∀ p, project p = selected → lower ≤ rank p ∧ rank p ≤ upper)
    (source : Finset P) (hchain : IsChain (· < ·) (source : Set P)) :
    ¬ required ⊆ source.image label := by
  intro himage
  refine (not_le_of_gt hsmall) (card_required_le_of_rank rank hrank label source hchain
    required himage lower upper ?_)
  intro p _ hp
  obtain ⟨hsub, v, hv, hsup⟩ := hrequired (label p) hp
  apply hfiber
  apply hunique (project p) (hsub (hcontains p))
  exact hsup.trans (hsupport p ▸ hcarried p v hv)

/-- Pulling back a strictly increasing chain of target flags through a
monotone assignment needs one new source vertex at every step. If the
first flag is a singleton recording the entire retracted face, its rank
is a lower bound on the starting size. -/
theorem card_add_le_of_lifted_flag_chain {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (faces : Finset (Finset X)) (r : X → Y) (H : Finset X → Finset (Finset Y))
    (hmono : MonotoneOn H (faces : Set (Finset X)))
    (hrecord : ∀ s ∈ faces, ∀ t, H s = {t} → s.image r = t)
    {n : ℕ} (s : ℕ → Finset X) (hs : ∀ i ≤ n, s i ∈ faces)
    (hchain : ∀ i < n, s i ⊆ s (i + 1) ∨ s (i + 1) ⊆ s i)
    (htarget : ∀ i < n, H (s i) ⊂ H (s (i + 1)))
    (t : Finset Y) (hfirst : H (s 0) = {t}) :
    t.card + n ≤ (s n).card := by
  have hstart : t.card ≤ (s 0).card := by
    rw [← hrecord _ (hs 0 (Nat.zero_le _)) t hfirst]
    exact Finset.card_image_le
  have step (i : ℕ) (hi : i < n) : (s i).card < (s (i + 1)).card := by
    have hincr := htarget i hi
    have hreverse : ¬ s (i + 1) ⊆ s i := by
      intro h
      have hle := hmono (hs _ hi) (hs _ (Nat.le_of_lt hi)) h
      exact (not_le_of_gt hincr) hle
    exact Finset.card_lt_card
      (lt_of_le_not_ge ((hchain i hi).resolve_right hreverse) hreverse)
  have bridge (i : ℕ) (hi : i ≤ n) : t.card + i ≤ (s i).card := by
    induction i with
    | zero => simpa using hstart
    | succ i ih =>
      have hlt : i < n := Nat.lt_of_succ_le hi
      exact Nat.succ_le_of_lt ((ih hlt.le).trans_lt (step i hlt))
  exact bridge n le_rfl

end D5.S3.Topology.RankedFiberLabelObstruction
