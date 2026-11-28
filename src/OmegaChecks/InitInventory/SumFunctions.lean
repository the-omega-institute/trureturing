module
public import Init.Data.Sum.Lemmas
public import Lean

/-!
The missing sum identities compare whole functions. The eliminator η rule
determines a function by its restrictions to the two constructors. Composition
with the eliminator and the constructor identity recover this η rule together.
-/

public section
open Lean Function
namespace OmegaChecks.InitBoundaries.SumFunctions
universe u v w x y z

/-- Equality of the two restrictions as functions determines the entire function. -/
def BranchExt : Prop := ∀ {α : Type u} {β : Type v} {γ : Sort w} (f g : α ⊕ β → γ),
  f ∘ Sum.inl = g ∘ Sum.inl → f ∘ Sum.inr = g ∘ Sum.inr → f = g

theorem branchesOfEta (eta : type_of% @Sum.elim_comp_inl_inr.{u,v,w}) : BranchExt.{u,v,w} := by
  intro α β γ f g l r
  calc
    f = Sum.elim (f ∘ Sum.inl) (f ∘ Sum.inr) := (eta f).symm
    _ = Sum.elim (g ∘ Sum.inl) (g ∘ Sum.inr) := by rw [l, r]
    _ = g := eta g

theorem etaIffBranches : (type_of% @Sum.elim_comp_inl_inr.{u,v,w}) ↔ BranchExt.{u,v,w} :=
  ⟨branchesOfEta, fun ext _ _ _ f => ext _ f rfl rfl⟩

/-- Pointwise equality on the two-element domain implies equality of the functions. -/
def TwoPointExt : Prop := ∀ {γ : Sort w} (f g : Unit ⊕ Unit → γ), (∀ s, f s = g s) → f = g

theorem twoPointOfEta (eta : type_of% @Sum.elim_comp_inl_inr.{0,0,w}) : TwoPointExt.{w} := by
  intro γ f g eq
  exact branchesOfEta eta f g (congrArg (fun y (_ : Unit) => y) (eq (.inl ())))
    (congrArg (fun y (_ : Unit) => y) (eq (.inr ())))

/-- Applying composition to the two constructor functions leaves the sum identity as the other premise. -/
theorem etaOfComposition (compose : type_of% @Sum.comp_elim.{max (u+1) (v+1),w,u,v})
    (identity : type_of% @Sum.elim_inl_inr.{u,v}) : type_of% @Sum.elim_comp_inl_inr.{u,v,w} := by
  intro α β γ f
  exact (compose f Sum.inl Sum.inr).symm.trans (congrArg (fun op => f ∘ op) identity)

theorem compositionOfEta (eta : type_of% @Sum.elim_comp_inl_inr.{u,v,w}) :
    type_of% @Sum.comp_elim.{x,w,u,v} := fun {_ _ _ _} f g h => (eta (f ∘ Sum.elim g h)).symm

theorem identityOfEta (eta : type_of% @Sum.elim_comp_inl_inr.{u,v,max (u+1) (v+1)}) :
    type_of% @Sum.elim_inl_inr.{u,v} := fun {_ _} => eta id

theorem constantsOfComposition (compose : type_of% @Sum.comp_elim.{1,w,u,v}) :
    type_of% @Sum.elim_const_const.{w,u,v} := by
  intro γ α β c
  exact (compose (fun _ : Unit => c) (fun _ => ()) (fun _ => ())).symm

theorem constantsIff : (type_of% @Sum.elim_const_const.{w,u,v}) ↔
    (type_of% @Sum.elim_lam_const_lam_const.{w,u,v}) := Iff.rfl

theorem mapIdentityIff : (type_of% @Sum.map_id_id.{u,v}) ↔ (type_of% @Sum.elim_inl_inr.{u,v}) := Iff.rfl

theorem elimMapOfComposition (compose : type_of% @Sum.comp_elim.{max (v+1) (y+1),w,u,x}) :
    type_of% @Sum.elim_comp_map.{u,v,w,x,y} := by
  intro α β ε γ δ f₁ f₂ g₁ g₂
  exact compose (Sum.elim f₂ g₂) (Sum.inl ∘ f₁) (Sum.inr ∘ g₁)

theorem mapCompositionOfElimMap (elimMap : type_of% @Sum.elim_comp_map.{y,u,max (v+1) (x+1),z,w}) :
    type_of% @Sum.map_comp_map.{u,v,w,x,y,z} := by
  intro α' α'' β' β'' α β f' g' f g
  exact @elimMap _ _ _ _ _ f (Sum.inl ∘ f') g (Sum.inr ∘ g')

/-- Composition computes the double swap as the eliminator with the two original constructors. -/
theorem swapIffIdentity (compose : type_of% @Sum.comp_elim.{max (u+1) (v+1),max (u+1) (v+1),u,v}) :
    (type_of% @Sum.swap_swap_eq.{u,v}) ↔ (type_of% @Sum.elim_inl_inr.{u,v}) := by
  have rearrange {α : Type u} {β : Type v} : (@Sum.swap β α ∘ @Sum.swap α β) = Sum.elim Sum.inl Sum.inr :=
    compose Sum.swap Sum.inr Sum.inl
  exact ⟨fun law {_ _} => rearrange.symm.trans law, fun law {_ _} => rearrange.trans law⟩

/-- Applying the sum map with identity functions twice gives the same complete function. -/
def ConstructorIdempotent : Prop := ∀ {α : Type u} {β : Type v},
  let embed := @Sum.elim α β (α ⊕ β) Sum.inl Sum.inr
  embed ∘ embed = embed

theorem idempotentOfMapComposition (rule : type_of% @Sum.map_comp_map.{u,u,v,v,u,v}) :
    ConstructorIdempotent.{u,v} := fun {_ _} => rule id id id id

/-- Precomposition with the swap cancels in an equality of complete functions. -/
def CancelSwap : Prop := ∀ {α : Type u} {β : Type v} {γ : Sort w} (f g : α ⊕ β → γ),
  f ∘ Sum.swap = g ∘ Sum.swap → f = g

theorem cancelOfSwap (law : type_of% @Sum.swap_swap_eq.{u,v}) : CancelSwap.{u,v,w} := by
  intro α β γ f g eq
  calc
    f = f ∘ (Sum.swap ∘ Sum.swap) := (congrArg (f ∘ ·) law).symm
    _ = g ∘ (Sum.swap ∘ Sum.swap) := congrArg (· ∘ Sum.swap) eq
    _ = g := congrArg (g ∘ ·) law

theorem mapIdentityOfIdentity (rule : type_of% @Sum.elim_inl_inr.{u,v}) : type_of% @Sum.map_id_id.{u,v} :=
  mapIdentityIff.mpr rule

theorem identityOfMapIdentity (rule : type_of% @Sum.map_id_id.{u,v}) : type_of% @Sum.elim_inl_inr.{u,v} :=
  mapIdentityIff.mp rule

theorem lambdaOfConstants (rule : type_of% @Sum.elim_const_const.{w,u,v}) :
    type_of% @Sum.elim_lam_const_lam_const.{w,u,v} := constantsIff.mp rule

theorem constantsOfLambda (rule : type_of% @Sum.elim_lam_const_lam_const.{w,u,v}) :
    type_of% @Sum.elim_const_const.{w,u,v} := constantsIff.mpr rule

def consequences : List (Name × Name × Name) := [
  (``Sum.elim_comp_inl_inr, ``TwoPointExt, ``twoPointOfEta),
  (``Sum.comp_elim, ``Sum.elim_comp_map, ``elimMapOfComposition),
  (``Sum.elim_comp_map, ``Sum.map_comp_map, ``mapCompositionOfElimMap),
  (``Sum.map_comp_map, ``ConstructorIdempotent, ``idempotentOfMapComposition),
  (``Sum.swap_swap_eq, ``CancelSwap, ``cancelOfSwap),
  (``Sum.elim_inl_inr, ``Sum.map_id_id, ``mapIdentityOfIdentity),
  (``Sum.map_id_id, ``Sum.elim_inl_inr, ``identityOfMapIdentity),
  (``Sum.elim_const_const, ``Sum.elim_lam_const_lam_const, ``lambdaOfConstants),
  (``Sum.elim_lam_const_lam_const, ``Sum.elim_const_const, ``constantsOfLambda)]

end OmegaChecks.InitBoundaries.SumFunctions
