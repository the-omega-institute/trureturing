/- GID: D5/S3/Combinatorics/UnorderedTrees/LeafDecoration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/LeafDecoration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Internal trees and leaf fibre cardinalities reconstruct actual unordered rooted trees. -/

/-
admission_basis: escape-witness
extendIso: proof_shape: content; escape_witness: assemble.
The partition of original vertices by internality and leaf parent gives an explicit bijection. Its conjugation with the fibrewise equivalences extends the core map while preserving every parent edge.
Live consumers: iso_iff_fibres and ForkDecoration.model_surjective.
-/

import D5.S3.Combinatorics.UnorderedTrees.OneFork
import Mathlib.Data.Fintype.BigOperators

/-! Reversible leaf decoration of rooted parent trees. -/

namespace D5.S3.Combinatorics.UnorderedTrees.LeafDecoration

open ParentTree LeafPruning
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev Core {V : Type u} (T : Tree V) := {x // Internal T x}

def LeafFibre {V : Type u} (T : Tree V) (p : Core T) :=
  {x : V // ¬ Internal T x ∧ Child T x p.val}

instance {V : Type u} [Fintype V] (T : Tree V) (p : Core T) :
    Fintype (LeafFibre T p) := by
  unfold LeafFibre
  infer_instance

private def assembleVertex {V : Type u} (T : Tree V) :
    Core T ⊕ (Σ p : Core T, LeafFibre T p) → V
  | .inl p => p.val
  | .inr ⟨_, z⟩ => z.val

/-- The vertex partition into internal vertices and original leaves grouped by their parents. -/
private def assemble {V : Type u} (T : Tree V) (hr : Internal T T.root) :
    Core T ⊕ (Σ p : Core T, LeafFibre T p) ≃ V :=
  Equiv.ofBijective (assembleVertex T) (by
    constructor
    · intro x y h
      rcases x with p | ⟨p, z⟩ <;> rcases y with q | ⟨q, w⟩
      · exact congrArg Sum.inl (Subtype.ext h)
      · change p.val = w.val at h
        exact (w.property.1 (h ▸ p.property)).elim
      · change z.val = q.val at h
        exact (z.property.1 (h.symm ▸ q.property)).elim
      · change z.val = w.val at h
        have hp : p = q := Subtype.ext
          (z.property.2.2.symm.trans ((congrArg T.parent h).trans w.property.2.2))
        subst q
        exact congrArg Sum.inr (congrArg (Sigma.mk p) (Subtype.ext h))
    · intro x
      by_cases hx : Internal T x
      · exact ⟨.inl ⟨x, hx⟩, rfl⟩
      · have hxr : x ≠ T.root := fun h => hx (h.symm ▸ hr)
        exact ⟨.inr ⟨⟨T.parent x, ⟨x, hxr, rfl⟩⟩, ⟨x, hx, hxr, rfl⟩⟩, rfl⟩)

/-- An isomorphism of original trees restricts to their internal subtrees. -/
private def restrictIso {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    {hr : Internal T T.root} {hs : Internal S S.root} (e : Iso T S) :
    Iso (prune T hr) (prune S hs) where
  equiv := internalEquiv e
  root_eq := Subtype.ext e.root_eq
  parent_eq p := Subtype.ext (e.parent_eq p.val)

/-- Each original leaf fibre is carried bijectively onto the image vertex's fibre. -/
private def leafIso {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) (p : Core T) : LeafFibre T p ≃ LeafFibre S (internalEquiv e p) :=
  e.equiv.subtypeEquiv (by
    intro x
    change (¬ Internal T x ∧ Child T x p.val) ↔
      (¬ Internal S (e.equiv x) ∧ Child S (e.equiv x) (e.equiv p.val))
    rw [iso_internal e, iso_child e])

/-- Matching the cardinalities of leaf fibres extends the specified internal isomorphism. -/
theorem extendIso {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {T : Tree V} {S : Tree W} {hr : Internal T T.root} {hs : Internal S S.root}
    (e : Iso (prune T hr) (prune S hs))
    (h : ∀ p, Fintype.card (LeafFibre T p) = Fintype.card (LeafFibre S (e.equiv p))) :
    ∃ f : Iso T S, ∀ p : Core T, f.equiv p.val = (e.equiv p).val := by
  let fibres (p : Core T) := Fintype.equivOfCardEq (h p)
  let g := Equiv.sumCongr e.equiv (Equiv.sigmaCongr e.equiv fibres)
  let f := (assemble T hr).symm.trans (g.trans (assemble S hs))
  have hleft (p : Core T) : f p.val = (e.equiv p).val := by
    change f (assemble T hr (.inl p)) = _
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hright (p : Core T) (z : LeafFibre T p) :
      f z.val = (fibres p z).val := by
    change f (assemble T hr (.inr ⟨p, z⟩)) = _
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  refine ⟨⟨f, ?_, ?_⟩, hleft⟩
  · exact (hleft (prune T hr).root).trans (congrArg Subtype.val e.root_eq)
  · intro x
    obtain ⟨y, rfl⟩ := (assemble T hr).surjective x
    rcases y with p | ⟨p, z⟩
    · change f ((prune T hr).parent p).val = S.parent (f p.val)
      rw [hleft, hleft]
      exact congrArg Subtype.val (e.parent_eq p)
    · change f (T.parent z.val) = S.parent (f z.val)
      rw [z.property.2.2, hleft, hright]
      exact (fibres p z).property.2.2.symm

/-- Original isomorphism is equivalent to matching leaf counts along a pruned isomorphism. -/
theorem iso_iff_fibres {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {T : Tree V} {S : Tree W} (hr : Internal T T.root) (hs : Internal S S.root) :
    Nonempty (Iso T S) ↔ ∃ e : Iso (prune T hr) (prune S hs),
      ∀ p, Fintype.card (LeafFibre T p) = Fintype.card (LeafFibre S (e.equiv p)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨restrictIso e, fun p => Fintype.card_congr (leafIso e p)⟩
  · rintro ⟨e, h⟩
    obtain ⟨f, _⟩ := extendIso e h
    exact ⟨f⟩

/-- The carrier obtained by attaching a finite fibre of fresh leaves at each vertex. -/
abbrev Inflated {V : Type u} (k : V → ℕ) := V ⊕ (Σ p : V, Fin (k p))

/-- Attach exactly `k p` fresh leaves at each skeleton vertex `p`. -/
def inflate {V : Type u} (T : Tree V) (k : V → ℕ) : Tree (Inflated k) where
  parent
    | .inl p => .inl (T.parent p)
    | .inr ⟨p, _⟩ => .inl p
  root := .inl T.root
  fixed_root := congrArg Sum.inl T.fixed_root
  reaches := by
    let parent : Inflated k → Inflated k := fun x =>
      match x with
      | .inl p => .inl (T.parent p)
      | .inr ⟨p, _⟩ => .inl p
    have hc : Function.Semiconj (Sum.inl : V → Inflated k) T.parent parent := fun _ => rfl
    have h (p : V) : ∃ j, (parent^[j]) (.inl p) = Sum.inl T.root := by
      obtain ⟨j, hj⟩ := T.reaches p
      exact ⟨j, by simpa only [hj] using (hc.iterate_right j p).symm⟩
    intro x
    rcases x with p | ⟨p, i⟩
    · exact h p
    · obtain ⟨j, hj⟩ := h p
      exact ⟨j + 1, by simpa only [Function.iterate_succ_apply] using hj⟩

theorem internal_inflate {V : Type u} (T : Tree V) (k : V → ℕ)
    (hk : ∀ p, ¬ Internal T p → 0 < k p) (p : V) :
    Internal (inflate T k) (.inl p) := by
  by_cases hp : Internal T p
  · obtain ⟨q, hq⟩ := hp
    exact ⟨.inl q, fun h => hq.1 (Sum.inl.inj h), congrArg Sum.inl hq.2⟩
  · exact ⟨.inr ⟨p, ⟨0, hk p hp⟩⟩, by simp [inflate], rfl⟩

private theorem terminal_inflate {V : Type u} (T : Tree V) (k : V → ℕ) (z : Σ p : V, Fin (k p)) :
    ¬ Internal (inflate T k) (.inr z) := by
  rintro ⟨x, _, h⟩
  cases x <;> cases h

/-- With positive terminal decorations, pruning recovers the entire original skeleton. -/
def pruneInflateIso {V : Type u} (T : Tree V) (k : V → ℕ)
    (hk : ∀ p, ¬ Internal T p → 0 < k p) :
    Iso T (prune (inflate T k) (internal_inflate T k hk T.root)) where
  equiv := Equiv.ofBijective (fun p => ⟨.inl p, internal_inflate T k hk p⟩)
    ⟨fun _ _ h => Sum.inl.inj (congrArg Subtype.val h), by
      rintro ⟨p | z, hp⟩
      · exact ⟨p, rfl⟩
      · exact (terminal_inflate T k z hp).elim⟩
  root_eq := rfl
  parent_eq _ := rfl

/-- The fibre above an inflated vertex has exactly the prescribed number of leaves. -/
def inflateLeafIso {V : Type u} (T : Tree V) (k : V → ℕ)
    (hk : ∀ p, ¬ Internal T p → 0 < k p) (p : V) :
    Fin (k p) ≃ LeafFibre (inflate T k) ((pruneInflateIso T k hk).equiv p) :=
  Equiv.ofBijective
    (fun i => ⟨.inr ⟨p, i⟩, terminal_inflate T k _, by simp [inflate], rfl⟩) (by
      constructor
      · intro i j h
        exact Sigma.mk.inj_iff.mp (Sum.inr.inj (congrArg Subtype.val h)) |>.2 |> eq_of_heq
      · rintro ⟨x | ⟨q, i⟩, hx⟩
        · exact (hx.1 (internal_inflate T k hk x)).elim
        · have he : q = p := Sum.inl.inj hx.2.2
          subst q
          exact ⟨i, rfl⟩)

theorem card_inflate {V : Type u} [Fintype V] (k : V → ℕ) :
    Fintype.card (Inflated k) = Fintype.card V + ∑ p, k p := by
  simp [Inflated, Fintype.card_sum, Fintype.card_sigma]

/-- A terminal in the internal tree must have an original leaf child. -/
theorem leaf_pos_of_terminal {V : Type u} [Fintype V] (T : Tree V)
    (hr : Internal T T.root) (p : Core T) (hp : ¬ Internal (prune T hr) p) :
    0 < Fintype.card (LeafFibre T p) := by
  obtain ⟨z, hz⟩ := p.property
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨z, ?_, hz⟩⟩
  intro hzi
  apply hp
  exact ⟨⟨z, hzi⟩, fun h => hz.1 (congrArg Subtype.val h), Subtype.ext hz.2⟩

#print axioms iso_iff_fibres
#print axioms extendIso
#print axioms pruneInflateIso
#print axioms inflateLeafIso

end

end D5.S3.Combinatorics.UnorderedTrees.LeafDecoration
