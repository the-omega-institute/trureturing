/- GID: D5/S3/Combinatorics/Graph/Homomorphisms/RootedTwinHomCount
   generality: G
   mirror-B: none(waiver:covered-by-rooted-twin-hom-count-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two copies of a rooted digraph are joined through a new centre. -/

module

public import OmegaBuild.Commands
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Embedding.Set
public import Mathlib.Order.RelIso.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic


/-!
Omega original.

Two copies of a rooted digraph are joined through a new centre. Restricting a
homomorphism with prescribed centre image gives two independent homomorphisms
whose root images are respectively an in-neighbour and an out-neighbour of that
image. Asymmetry makes these two classes disjoint. This is the rooted counting
step in Proposition 5.2 of He, Mani, Nie, Tung and Wei, arXiv:2512.11222.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.RootedTwinHomCount

universe u v

variable {A : Type u} {B : Type v}

/-- Two copies of `H`, with precisely the arcs from the left root to the new
centre and from the centre to the right root. -/
def rootedTwin (H : Digraph A) (w : A) : Digraph (Option (Bool × A)) where
  Adj
    | some (i, a), some (j, b) => i = j ∧ H.Adj a b
    | some (i, a), none => i = false ∧ a = w
    | none, some (j, b) => j = true ∧ b = w
    | none, none => False

/-- Restriction to either copy is an adjacency-preserving map. -/
def restrict (H : Digraph A) (w : A) {R : B → B → Prop}
    (f : RelHom (rootedTwin H w).Adj R) (i : Bool) : RelHom H.Adj R where
  toFun a := f (some (i, a))
  map_rel' h := f.map_rel' ⟨rfl, h⟩

/-- Assemble two compatible homomorphisms and the prescribed centre image. -/
def assemble (H : Digraph A) (w : A) {R : B → B → Prop} (t : B)
    (g : {g : RelHom H.Adj R // R (g w) t})
    (h : {h : RelHom H.Adj R // R t (h w)}) : RelHom (rootedTwin H w).Adj R where
  toFun
    | none => t
    | some (false, a) => g.val a
    | some (true, a) => h.val a
  map_rel' := by
    intro x y edge
    cases x with
    | none =>
      cases y with
      | none => exact False.elim edge
      | some y =>
        rcases y with ⟨j, b⟩
        rcases edge with ⟨rfl, rfl⟩
        exact h.property
    | some x =>
      rcases x with ⟨i, a⟩
      cases y with
      | none =>
        rcases edge with ⟨rfl, rfl⟩
        exact g.property
      | some y =>
        rcases y with ⟨j, b⟩
        rcases edge with ⟨rfl, edge⟩
        cases i
        · exact g.val.map_rel' edge
        · exact h.val.map_rel' edge

/-- The centre fibre is exactly the product of the two root-constrained classes.
No finiteness or asymmetry is required for this correspondence. -/
def rootFiberEquiv (H : Digraph A) (w : A) (R : B → B → Prop) (t : B) :
    {f : RelHom (rootedTwin H w).Adj R // f none = t} ≃
      ({g : RelHom H.Adj R // R (g w) t} × {g : RelHom H.Adj R // R t (g w)}) where
  toFun f :=
    (⟨restrict H w f.val false, by
       have h := f.val.map_rel' (show (rootedTwin H w).Adj (some (false, w)) none from ⟨rfl, rfl⟩)
       have e : f.val.toFun none = t := f.property
       rw [e] at h
       exact h⟩,
     ⟨restrict H w f.val true, by
       have h := f.val.map_rel' (show (rootedTwin H w).Adj none (some (true, w)) from ⟨rfl, rfl⟩)
       have e : f.val.toFun none = t := f.property
       rw [e] at h
       exact h⟩)
  invFun p := ⟨assemble H w t p.1 p.2, rfl⟩
  left_inv f := by
    apply Subtype.ext
    apply RelHom.ext
    intro x
    cases x with
    | none => exact f.property.symm
    | some x => rcases x with ⟨i, a⟩; cases i <;> rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply RelHom.ext
      intro a
      rfl
    · apply Subtype.ext
      apply RelHom.ext
      intro a
      rfl

/-- In an asymmetric host the two root classes inject into all homomorphisms. -/
def rootClassInjection (H : Digraph A) (w : A) {R : B → B → Prop}
    (hR : ∀ x y, R x y → ¬ R y x) (t : B) :
    ({g : RelHom H.Adj R // R (g w) t} ⊕ {g : RelHom H.Adj R // R t (g w)}) ↪
      RelHom H.Adj R :=
  Function.Embedding.sumSet
    (s := {g : RelHom H.Adj R | R (g w) t})
    (t := {g : RelHom H.Adj R | R t (g w)})
    (Set.disjoint_left.mpr fun g hg hh => hR (g w) t hg hh)

/-- The general quarter bound counts all homomorphisms, allowing image collisions. -/
theorem quarter_bound [Finite A] [Finite B] (H : Digraph A) (w : A)
    (R : B → B → Prop) (hR : ∀ x y, R x y → ¬ R y x) (t : B) :
    4 * Nat.card {f : RelHom (rootedTwin H w).Adj R // f none = t} ≤
      (Nat.card (RelHom H.Adj R)) ^ 2 := by
  classical
  have : Finite (RelHom H.Adj R) := Finite.of_injective
    (fun f : RelHom H.Adj R => (f : A → B)) (fun _ _ h => RelHom.ext (congrFun h))
  have hs : Nat.card {g : RelHom H.Adj R // R (g w) t} +
      Nat.card {g : RelHom H.Adj R // R t (g w)} ≤ Nat.card (RelHom H.Adj R) := by
    rw [← Nat.card_sum]
    exact Nat.card_le_card_of_injective _ (rootClassInjection H w hR t).injective
  rw [Nat.card_congr (rootFiberEquiv H w R t), Nat.card_prod]
  simpa only [mul_assoc] using (four_mul_le_sq_add _ _).trans (Nat.pow_le_pow_left hs 2)

end Omega.RootedTwinHomCount
