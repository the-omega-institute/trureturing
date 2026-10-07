/- GID: D5/S3/HomologicalAlgebra/Solid/SequentialPresentation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/SequentialPresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Filtered.Connected

/-! Countable telescope presentations in an AB5 abelian category.
New proofs, released under the Apache 2.0 license. -/

noncomputable section
open CategoryTheory Limits
open CoproductsFromFiniteFiltered

namespace CWSolid

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] IsFiltered.isConnected

variable {C : Type*} [Category* C] [Abelian C]
  [HasCoproducts.{0} C] [HasProducts.{0} C]
  [HasColimitsOfShape (Finset (Discrete ℕ)) C]
  [HasExactColimitsOfShape (Finset (Discrete ℕ)) C]

/-- The coordinate projection from a countable coproduct. -/
def sequenceProjection (A : ℕ → C) (n : ℕ) : (∐ A) ⟶ A n :=
  Limits.Sigma.desc (fun m => if h : m = n then eqToHom (congrArg A h) else 0)

@[simp, reassoc]
theorem sequenceProjection_leg (A : ℕ → C) (m n : ℕ) :
    Sigma.ι A m ≫ sequenceProjection A n =
      if h : m = n then eqToHom (congrArg A h) else 0 := by
  simp [sequenceProjection]

set_option backward.isDefEq.respectTransparency false in
/-- AB5 makes the canonical map from the sum into the product monic.
This is proved by taking the filtered union of its finite split submaps. -/
theorem sequenceProjection_jointly_monic (A : ℕ → C) {X : C}
    (g : X ⟶ ∐ A) (hg : ∀ n, g ≫ sequenceProjection A n = 0) : g = 0 := by
  classical
  let p : (∐ A) ⟶ ∏ᶜ A := Pi.lift (sequenceProjection A)
  let F := liftToFinsetObj (Discrete.functor A)
  let φ : F ⟶ (Functor.const (Finset (Discrete ℕ))).obj (∏ᶜ A) :=
    { app s := (finiteSubcoproductsCocone A).ι.app s ≫ p
      naturality s t f := by
        dsimp
        rw [Category.comp_id]
        exact (finiteSubcoproductsCocone A).w_assoc f p }
  haveI (s : Finset (Discrete ℕ)) : Mono (φ.app s) := by
    let B : s → C := fun x => A x.1.as
    let r : (∏ᶜ A) ⟶ F.obj s :=
      biproduct.lift (fun x : s => Pi.π A x.1.as) ≫ (biproduct.isoCoproduct B).hom
    have hr : φ.app s ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro ⟨x, hx⟩
      dsimp only [φ]
      simp only [Category.assoc]
      change Sigma.ι B ⟨x, hx⟩ ≫
        (finiteSubcoproductsCocone A).ι.app s ≫ p ≫ r = Sigma.ι B ⟨x, hx⟩ ≫ 𝟙 _
      rw [Category.comp_id]
      simp only [finiteSubcoproductsCocone_ι_app, Sigma.ι_desc_assoc]
      rw [← cancel_mono (biproduct.isoCoproduct B).inv]
      dsimp only [r]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply biproduct.hom_ext
      intro y
      simp only [Category.assoc, p, biproduct.isoCoproduct_inv, Sigma.ι_desc]
      dsimp only [B, finiteSubcoproductsCocone_pt]
      rw [biproduct.lift_π, Pi.lift_comp_π, sequenceProjection_leg]
      by_cases h : (⟨x, hx⟩ : s) = y
      · subst y
        simp
      · have hn : x.as ≠ y.1.as := fun e => h (Subtype.ext (Discrete.ext e))
        simp [biproduct.ι_π, h, hn]
    exact mono_of_mono_fac hr
  haveI : Mono φ := NatTrans.mono_of_mono_app _
  haveI : Mono p := colim.map_mono' φ (isColimitFiniteSubproductsCocone A)
    (isColimitConstCocone (Finset (Discrete ℕ)) (∏ᶜ A)) p (by intro s; simp [φ])
  apply (cancel_mono p).1
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, p, Pi.lift_comp_π, zero_comp]
  exact hg n

set_option backward.isDefEq.respectTransparency false in
/-- One minus the forward transition is monic for every countable sequence;
no monicity of the transitions is required. -/
theorem oneMinusSequence_mono (A : ℕ → C) (a : ∀ n, A n ⟶ A (n + 1)) :
    Mono (𝟙 (∐ A) - Limits.Sigma.desc (fun n => a n ≫ Sigma.ι A (n + 1))) := by
  let d := 𝟙 (∐ A) - Limits.Sigma.desc (fun n => a n ≫ Sigma.ι A (n + 1))
  have hd₀ : d ≫ sequenceProjection A 0 = sequenceProjection A 0 := by
    apply Sigma.hom_ext
    intro n
    simp [d, Preadditive.comp_sub, Preadditive.sub_comp]
  have hd (n : ℕ) : d ≫ sequenceProjection A (n + 1) =
      sequenceProjection A (n + 1) - sequenceProjection A n ≫ a n := by
    apply Sigma.hom_ext
    intro m
    by_cases h : m = n
    · subst m
      simp [d, Preadditive.comp_sub, Preadditive.sub_comp, sequenceProjection_leg_assoc]
    · simp [d, Preadditive.comp_sub, Preadditive.sub_comp, h, sequenceProjection_leg_assoc]
  apply Preadditive.mono_of_cancel_zero
  intro X g hgd
  apply sequenceProjection_jointly_monic A g
  intro n
  induction n with
  | zero => rw [← hd₀, ← Category.assoc, hgd, zero_comp]
  | succ n ih =>
      have h := congrArg (· ≫ sequenceProjection A (n + 1)) hgd
      rw [Category.assoc, hd, Preadditive.comp_sub, ← Category.assoc,
        ih, zero_comp, sub_zero, zero_comp] at h
      exact h

end CWSolid
