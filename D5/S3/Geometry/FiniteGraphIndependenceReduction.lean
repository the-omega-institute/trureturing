/- GID: D5/S3/Geometry/FiniteGraphIndependenceReduction
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphIndependenceReduction
   mirror-E: none(waiver:native-independence-domination)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Simultaneous open-neighborhood domination gives a native strong deformation retraction. -/
import D5.S3.Geometry.FiniteCoordinateTruncation

/-!
# Simultaneous domination folds

If the open neighborhood of a retained vertex is contained in the open
neighborhood of each deleted vertex, transfer all deleted mass to that vertex.
The straight segment stays in the actual independence realization and fixes
the retained induced realization pointwise. No forest hypothesis is used.

This is the classical domination fold for independence complexes. The forest
classification to which it applies is Ehrenborg--Hetyei, *The topology of the
independence complex* (2006), Corollary 6.1, DOI 10.1016/j.ejc.2005.04.010.
-/

noncomputable section
open Set Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteGraphIndependenceReduction

open FiniteCoordinateTruncation FiniteGraphVertexSubstitution
open FiniteConeCollapse FiniteConeUnionWedge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Keep the original labels, with the deleted finite set removed. -/
abbrev Retained (D : Finset V) := {b : V // b ∉ D}

private def embedding (D : Finset V) : Retained D ↪ V := Function.Embedding.subtype _

/-- Linear mass transfer, defined on all ambient coordinate vectors. -/
def transfer (a : V) (D : Finset V) (x : V → ℝ) (b : V) : ℝ :=
  x b + (if b = a then ∑ d ∈ D, x d else 0) - (if b ∈ D then x b else 0)

private theorem transfer_deleted (a : V) (D : Finset V) (ha : a ∉ D)
    (x : V → ℝ) {d : V} (hd : d ∈ D) : transfer a D x d = 0 := by
  simp [transfer, hd, show d ≠ a from fun h => ha (h ▸ hd)]

private theorem transfer_fixed (a : V) (D : Finset V) (x : V → ℝ)
    (hx : ∀ d ∈ D, x d = 0) : transfer a D x = x := by
  have hs : ∑ d ∈ D, x d = 0 := Finset.sum_eq_zero hx
  funext b
  by_cases hb : b ∈ D <;> simp [transfer, hs, hb, *]

private theorem probability_transfer (a : V) (D : Finset V) (ha : a ∉ D)
    {x : V → ℝ} (hx : Probability x) : Probability (transfer a D x) := by
  refine ⟨?_, ?_⟩
  · intro b
    by_cases hb : b ∈ D
    · rw [transfer_deleted a D ha x hb]
    · by_cases hba : b = a
      · subst b
        simpa [transfer, ha] using add_nonneg (hx.1 a)
          (Finset.sum_nonneg fun d _ => hx.1 d)
      · simpa [transfer, hb, hba] using hx.1 b
  · simp [transfer, Finset.sum_add_distrib, Finset.sum_sub_distrib, hx.2]

/-- For each edge one endpoint vanishes both before and after transfer.
Domination is used even when the survivor initially has zero mass. -/
theorem transfer_common_zero (G : SimpleGraph V) (a : V) (D : Finset V)
    (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d)
    {x : V → ℝ} (hx : Avoid G x) :
    ∀ p q, G.Adj p q →
      (x p = 0 ∧ transfer a D x p = 0) ∨
      (x q = 0 ∧ transfer a D x q = 0) := by
  have hsurvivor : ∀ q, G.Adj a q → x q ≠ 0 → transfer a D x a = 0 := by
    intro q haq hq
    have ha : x a = 0 := (hx a q haq).resolve_right hq
    have hd : ∀ d ∈ D, x d = 0 := by
      intro d hd
      exact (hx d q (hdom d hd haq)).resolve_right hq
    simp [transfer, ha, Finset.sum_eq_zero hd]
  have hother : ∀ b, b ≠ a → x b = 0 → transfer a D x b = 0 := by
    intro b hb hx
    simp [transfer, hb, hx]
  intro p q hpq
  by_cases hp : p = a
  · subst p
    by_cases hq : x q = 0
    · exact Or.inr ⟨hq, hother q (G.ne_of_adj hpq).symm hq⟩
    · exact Or.inl ⟨(hx a q hpq).resolve_right hq, hsurvivor q hpq hq⟩
  · by_cases hq : q = a
    · subst q
      by_cases hpz : x p = 0
      · exact Or.inl ⟨hpz, hother p hp hpz⟩
      · exact Or.inr ⟨(hx a p hpq.symm).resolve_right hpz,
          hsurvivor p hpq.symm hpz⟩
    · exact (hx p q hpq).imp (fun h => ⟨h, hother p hp h⟩)
        (fun h => ⟨h, hother q hq h⟩)

private theorem continuous_transfer (a : V) (D : Finset V) :
    Continuous (transfer a D) := by
  apply continuous_pi
  intro b
  unfold transfer
  apply Continuous.sub
  · apply Continuous.add (continuous_apply b)
    split_ifs
    · exact continuous_finsetSum _ fun d _ => continuous_apply d
    · exact continuous_const
  · split_ifs
    · exact continuous_apply b
    · exact continuous_const

private theorem induced_faces_le (G : SimpleGraph V) (D : Finset V) :
    ((independenceComplex (G.induce {b | b ∉ D})).toPreAbstractSimplicialComplex.map
      (embedding D)) ≤ (independenceComplex G).toPreAbstractSimplicialComplex := by
  rw [← unrestricted, restricted_map _ G _ (fun _ _ => Iff.rfl)]
  intro s hs
  exact ⟨hs.1, hs.2.1⟩

/-- Native zero-extension inclusion of the retained induced graph. -/
def inclusion (G : SimpleGraph V) (D : Finset V) :
    C(Ispace (G.induce {b | b ∉ D}), Ispace G) :=
  (realizationInclusion (induced_faces_le G D)).comp
    (mapHomeomorph (independenceComplex (G.induce {b | b ∉ D})).toPreAbstractSimplicialComplex
      (embedding D) : C(_, _))

private theorem inclusion_at (G : SimpleGraph V) (D : Finset V)
    (y : Ispace (G.induce {b | b ∉ D})) (b : Retained D) :
    (inclusion G D y).val b = y.val b := push_at (embedding D) y.val b

private theorem inclusion_off (G : SimpleGraph V) (D : Finset V)
    (y : Ispace (G.induce {b | b ∉ D})) {d : V} (hd : d ∈ D) :
    (inclusion G D y).val d = 0 :=
  push_off (embedding D) y.val d (by rintro ⟨b, rfl⟩; exact b.property hd)

private theorem restrict_transfer (G : SimpleGraph V) (a : V) (D : Finset V)
    (ha : a ∉ D) (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d)
    (x : Ispace G) :
    (fun b : Retained D => transfer a D x.val b) ∈
      realization (independenceComplex (G.induce {b | b ∉ D})).toPreAbstractSimplicialComplex := by
  have hp := probability_transfer a D ha (probability G x)
  have he : push (embedding D) (fun b => transfer a D x.val b) = transfer a D x.val := by
    funext b
    by_cases hb : b ∈ D
    · rw [transfer_deleted a D ha x.val hb, push_off]
      rintro ⟨c, rfl⟩
      exact c.property hb
    · exact push_at (embedding D) _ ⟨b, hb⟩
  apply (realization_iff _ _).mpr
  refine ⟨⟨fun b => hp.1 b, ?_⟩, ?_⟩
  · calc
      _ = ∑ b, push (embedding D) (fun b => transfer a D x.val b) b :=
        (sum_push (embedding D) (fun b => transfer a D x.val b)).symm
      _ = 1 := by rw [he]; exact hp.2
  · intro p q hpq
    exact (transfer_common_zero G a D hdom (avoid G x) p q hpq).elim
      (fun h => Or.inl h.2) (fun h => Or.inr h.2)

/-- Delete the zero coordinates after transferring their mass to the survivor. -/
def retraction (G : SimpleGraph V) (a : V) (D : Finset V) (ha : a ∉ D)
    (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d) :
    C(Ispace G, Ispace (G.induce {b | b ∉ D})) where
  toFun x := ⟨fun b => transfer a D x.val b, restrict_transfer G a D ha hdom x⟩
  continuous_toFun := (continuous_pi fun b : Retained D =>
    ((continuous_apply b.val).comp (continuous_transfer a D)).comp
      continuous_subtype_val).subtype_mk _

private theorem inclusion_retraction (G : SimpleGraph V) (a : V) (D : Finset V)
    (ha : a ∉ D) (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d)
    (x : Ispace G) :
    (inclusion G D (retraction G a D ha hdom x)).val = transfer a D x.val := by
  funext b
  by_cases hb : b ∈ D
  · rw [inclusion_off G D _ hb, transfer_deleted a D ha x.val hb]
  · exact inclusion_at G D _ ⟨b, hb⟩

/-- The retained induced space is fixed by the retraction. -/
theorem retraction_inclusion (G : SimpleGraph V) (a : V) (D : Finset V)
    (ha : a ∉ D) (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d)
    (y : Ispace (G.induce {b | b ∉ D})) :
    retraction G a D ha hdom (inclusion G D y) = y := by
  apply Subtype.ext
  funext b
  change transfer a D (inclusion G D y).val b.val = y.val b
  rw [transfer_fixed a D _ (fun d hd => inclusion_off G D y hd)]
  exact inclusion_at G D y b

/-- The actual straight homotopy, relative to the entire retained coordinate
subspace, from the identity to inclusion after retraction. -/
def foldHomotopy (G : SimpleGraph V) (a : V) (D : Finset V) (ha : a ∉ D)
    (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d) :
    (ContinuousMap.id (Ispace G)).HomotopyRel
      ((inclusion G D).comp (retraction G a D ha hdom))
      {x | ∀ d ∈ D, x.val d = 0} where
  toHomotopy := straight _ _ (by
    intro t x
    rw [ContinuousMap.comp_apply, inclusion_retraction]
    exact (realization_iff G _).mpr
      ⟨probability_mix (probability G x) (probability_transfer a D ha (probability G x)) t,
        avoid_mix (transfer_common_zero G a D hdom (avoid G x)) t⟩)
  prop' t x hx := by
    apply Subtype.ext
    change mix t x.val (inclusion G D (retraction G a D ha hdom x)).val = x.val
    rw [inclusion_retraction, transfer_fixed a D x.val hx]
    funext b
    simp only [mix]
    ring

/-- The induced retained realization and the original realization have the
same homotopy type, with the displayed native maps as inverses. -/
def foldEquiv (G : SimpleGraph V) (a : V) (D : Finset V) (ha : a ∉ D)
    (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d) :
    Ispace G ≃ₕ Ispace (G.induce {b | b ∉ D}) where
  toFun := retraction G a D ha hdom
  invFun := inclusion G D
  left_inv := ⟨(foldHomotopy G a D ha hdom).toHomotopy.symm⟩
  right_inv := by
    have he : (retraction G a D ha hdom).comp (inclusion G D) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro y
      exact retraction_inclusion G a D ha hdom y
    rw [he]

end D5.S3.Geometry.FiniteGraphIndependenceReduction
