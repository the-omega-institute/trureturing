/- GID: D5/S3/FiniteGroups/UniformPartitionAutomorphisms
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/UniformPartitionAutomorphisms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform partition symmetries have unique semidirect coordinates. -/

import D5.S3.FiniteGroups.SuccessorQuotient
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Perm

/-! The candidate content is the explicit extraction of a block permutation and
bijective fiber maps from preservation and reflection of first-coordinate equality.
The intended witness is the inverse construction in `coordinates`: it recovers
every automorphism, rather than only embedding a known product action. The live
consequences are the semidirect multiplication and factorial order. No cyclic
order on a block is assumed. Empty block-index types and singleton fibers remain
in scope; nonempty fibers are necessary for uniqueness of the block permutation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.UniformPartitionAutomorphisms

open Equiv

variable {K L : Type*}

/-- The existing relation-automorphism subgroup for the uniform partition. -/
abbrev Aut (K L : Type*) :=
  SuccessorQuotient.relationAut (fun x y : K × L => x.1 = y.1)

/-- Relabel the destinations of a family of fiber permutations. -/
def reindex (K L : Type*) : Perm K →* MulAut (K → Perm L) where
  toFun α := MulEquiv.arrowCongr α (MulEquiv.refl _)
  map_one' := by ext σ w t; rfl
  map_mul' α β := by ext σ w t; rfl

/-- Standard semidirect coordinates, with fiber permutations indexed by destination. -/
abbrev Coordinates (K L : Type*) :=
  SemidirectProduct (K → Perm L) (Perm K) (reindex K L)

/-- Assemble a block permutation and destination-indexed fiber permutations. -/
def assemble (σ : K → Perm L) (α : Perm K) : Aut K L :=
  ⟨(Equiv.prodCongr α (Equiv.refl L)).trans (Equiv.prodCongrRight σ), by
    intro x y
    change α x.1 = α y.1 ↔ x.1 = y.1
    exact α.injective.eq_iff⟩

section Extraction

variable [Nonempty L]

private noncomputable def blockMap (p : Aut K L) (v : K) : K :=
  (p.val (v, Classical.choice ‹Nonempty L›)).1

private theorem blockMap_fst (p : Aut K L) (x : K × L) :
    blockMap p x.1 = (p.val x).1 :=
  (p.property (x.1, Classical.choice ‹Nonempty L›) x).mpr rfl

private theorem blockMap_bijective (p : Aut K L) : Function.Bijective (blockMap p) := by
  constructor
  · intro v w h
    exact (p.property (v, Classical.choice ‹Nonempty L›)
      (w, Classical.choice ‹Nonempty L›)).mp h
  · intro w
    obtain ⟨x, hx⟩ := p.val.surjective (w, Classical.choice ‹Nonempty L›)
    exact ⟨x.1, (blockMap_fst p x).trans (congrArg Prod.fst hx)⟩

private noncomputable def blockPerm (p : Aut K L) : Perm K :=
  Equiv.ofBijective (blockMap p) (blockMap_bijective p)

private theorem blockPerm_fst (p : Aut K L) (x : K × L) :
    blockPerm p x.1 = (p.val x).1 := blockMap_fst p x

private theorem fiber_bijective (p : Aut K L) (w : K) :
    Function.Bijective (fun t : L => (p.val ((blockPerm p).symm w, t)).2) := by
  constructor
  · intro t u h
    have he : p.val ((blockPerm p).symm w, t) =
        p.val ((blockPerm p).symm w, u) := by
      apply Prod.ext
      · exact (blockPerm_fst p ((blockPerm p).symm w, t)).symm.trans
          (blockPerm_fst p ((blockPerm p).symm w, u))
      · exact h
    exact congrArg Prod.snd (p.val.injective he)
  · intro u
    obtain ⟨x, hx⟩ := p.val.surjective (w, u)
    have hv : x.1 = (blockPerm p).symm w := by
      apply (blockPerm p).injective
      rw [Equiv.apply_symm_apply]
      exact (blockPerm_fst p x).trans (congrArg Prod.fst hx)
    refine ⟨x.2, ?_⟩
    have he : ((blockPerm p).symm w, x.2) = x := Prod.ext hv.symm rfl
    exact congrArg Prod.snd ((congrArg p.val he).trans hx)

private noncomputable def fiberPerm (p : Aut K L) (w : K) : Perm L :=
  Equiv.ofBijective (fun t => (p.val ((blockPerm p).symm w, t)).2)
    (fiber_bijective p w)

private theorem blockPerm_assemble (σ : K → Perm L) (α : Perm K) :
    blockPerm (assemble σ α) = α := by
  ext v
  rfl

/-- Every partition automorphism has unique explicit block and fiber coordinates. -/
noncomputable def coordinates : Aut K L ≃ Coordinates K L where
  toFun p := ⟨fiberPerm p, blockPerm p⟩
  invFun c := assemble c.left c.right
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Prod.ext
    · exact blockPerm_fst p x
    · change (p.val ((blockPerm p).symm (blockPerm p x.1), x.2)).2 = (p.val x).2
      rw [Equiv.symm_apply_apply]
  right_inv c := by
    apply SemidirectProduct.ext
    · funext w
      apply Equiv.ext
      intro t
      change (c.left (c.right ((blockPerm (assemble c.left c.right)).symm w))) t = c.left w t
      rw [blockPerm_assemble, Equiv.apply_symm_apply]
    · exact blockPerm_assemble c.left c.right

end Extraction

private def assemblyHom : Coordinates K L →* Aut K L where
  toFun c := assemble c.left c.right
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl
  map_mul' c d := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Prod.ext
    · rfl
    · change c.left (c.right (d.right x.1))
        (d.left (c.right.symm (c.right (d.right x.1))) x.2) =
        c.left (c.right (d.right x.1)) (d.left (d.right x.1) x.2)
      rw [Equiv.symm_apply_apply]

/-- The full uniform-partition symmetry group, with its standard semidirect law. -/
noncomputable def automorphismEquiv [Nonempty L] : Aut K L ≃* Coordinates K L :=
  { coordinates with
    map_mul' p q := by
      apply coordinates.symm.injective
      calc
        coordinates.symm (coordinates (p * q)) = p * q :=
          coordinates.symm_apply_apply _
        _ = assemblyHom (coordinates p) * assemblyHom (coordinates q) := by
          change p * q = coordinates.symm (coordinates p) * coordinates.symm (coordinates q)
          rw [coordinates.symm_apply_apply, coordinates.symm_apply_apply]
        _ = assemblyHom (coordinates p * coordinates q) :=
          (assemblyHom.map_mul _ _).symm }

/-- The factorial order is a consequence of the actual coordinate classification. -/
theorem card_aut [Finite K] [Finite L] [Nonempty L] :
    Nat.card (Aut K L) = (Nat.card L).factorial ^ Nat.card K * (Nat.card K).factorial := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite L
  rw [Nat.card_congr automorphismEquiv.toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_perm]

end D5.S3.FiniteGroups.UniformPartitionAutomorphisms
