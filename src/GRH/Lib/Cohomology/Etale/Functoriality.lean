import GRH.Lib.Cohomology.Etale.Defs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Functoriality of Ext of abelian presheaves in both variables and along exact functors. -/

noncomputable section


open CategoryTheory Limits Abelian.Ext Functor Function H ShortComplex ShortExact
variable {D C C' C''} [Category D] [Category C] [Category C'] [Category C''] {F G N M K :
  AbFunctor C} {F' G' N' M' : AbFunctor C'} {F'' N'' : AbFunctor C''} {n} (c :
  Comparison F F') (c' : Comparison F' F'') (a' : M' ⟶ N') (a : N' ⟶ c.φ ⋙ N) (α' : K ⟶ M) (α :
  M ⟶ N) (β : F ⟶ G) (β' : G ⟶ K) (Ξ : (D ⥤ Ab) ⥤ AbFunctor C') {R} [Ring R]

/-- exact functors -/
class abbrev IsExactFunctor := Additive Ξ, PreservesFiniteLimits Ξ, PreservesFiniteColimits Ξ

lemma H.smul_eq_push [CoeffAction R F] (r : R) x : r • x = push N
  (CoeffAction.act r : End F).asHom n x :=
  rfl

variable (R) {Φ Ψ} [@IsExactFunctor C C' _ _ Φ] [IsExactFunctor Ψ] {Θ}
  [@IsExactFunctor C' C'' _ _ Θ] (η : Φ ⟶ Ψ) (x : H N F n)

instance : IsGrothendieckAbelian.{1} (AbFunctor C) :=
  {ab5OfSize.1 _ := inferInstance, hasSeparator := .of_equivalence (opOpEquivalence C).congrLeft}

/-- Induction on Ext classes out of N: a property holds for every class if it holds for
morphisms N → F and, for each short exact 0 → S₁ → S₂ → S₃ → 0, passes from x in Ext^n(N,S₃)
to its image in Ext^{n+1}(N,S₁). -/
@[induction_eliminator] lemma H.dimension_shift_induction {P : ∀ {F n}, H N F n → Prop} (h₀ : ∀ F f,
  @P F 0 (mk₀ f)) (h : ∀ S (hS : ShortExact S) n x, @P _ n x → P (x.comp hS.extClass rfl)) : P x :=
  n.rec ((mk₀_bijective ..).2.forall.2 <| h₀ ·) (fun _ _ F x ↦ (x.covariant_sequence_exact₁ _
  ⟨exact_cokernel (Injective.ι F)⟩ (eq_zero_of_injective _) rfl).elim (by bound)) F x

attribute [simp] mapExactFunctor_comp mapExactFunctor_mk₀ mapExactFunctor_extClass mapExtAddHom

attribute [local simp] H.map H.push Comparison.pull mk₀_add
set_option backward.isDefEq.respectTransparency false

lemma mapExactFunctor_mapExactFunctor : (x.mapExactFunctor Φ).mapExactFunctor Θ =
  x.mapExactFunctor (Φ ⋙ Θ) := by induction x <;> simp_all

lemma mapExactFunctor_naturality : push _ (η F) n (x.mapExactFunctor Φ) =
  map _ (η N) n (x.mapExactFunctor Ψ) := by
  have := (extClass_naturality (f := mapNatTrans · η))
  induction x <;> simp_all [map_of_exact, ← comp_assoc_of_second_deg_zero, comp_assoc (h₂₃ := rfl)]

namespace H

@[simp] lemma map_id : map F (𝟙 N) n x = x := by simp

lemma map_comp : map F (α' ≫ α) n x = map F α' n (map F α n x) := by simp

lemma push_comp : push N (β ≫ β') n x = push N β' n (push N β n x) := by simp

/-- The additive map sending a morphism α: M → N to the pull-back Ext^n(N,F) → Ext^n(M,F). -/
def mapHom F M N n := AddMonoidHom.mk' (@map C _ N M F · n) (by simp)

lemma map_push : map G α n (push N β n x) = push M β n (map F α n x) := by simp

/-- For a ring R acting on F and α: M → N, the pull-back Ext^n(N,F) → Ext^n(M,F) as an R-linear
map. -/
def mapₗ F [CoeffAction R F] (α : M ⟶ N) n : H N F n →ₗ[R] H M F n :=
  { map .. with map_smul' _ := map_push α (End.asHom _) }

lemma mapExactFunctor_restrictAlong_id : x.mapExactFunctor (restrictAlong (𝟭 _)) =
  x := by induction x <;> aesop

end H

lemma IsCohomEquiv.of_isIso [IsIso α] : IsCohomEquiv F α :=
  (bijective_iff_has_inverse.2 ⟨map F (inv α) ·, by cat_disch⟩)

lemma Comparison.pull_push (β : _ ⋙ G ⟶ G') γ γ' (h : whiskerLeft _ γ ≫ β = c.coeffHom ≫ γ') α x :
    pull ⟨_, β⟩ α n (push N γ n x) = push N' γ' n (c.pull α n x) := by aesop

@[simp] lemma Comparison.id_pull : (id F).pull α =
  map F α := by ext n x; simp [mapExactFunctor_restrictAlong_id, x.comp_mk₀_id]

/-- The composite of comparisons (φ,β) from F to F' and (φ',β') from F' to F'': the functor φ∘φ'
with the map Fφφ' → F'φ' → F''. -/
abbrev Comparison.trans : Comparison F F'' := ⟨_ ⋙ _, c'.φ.whiskerLeft c.coeffHom ≫ c'.coeffHom⟩

variable {c c' a a' α' α}

lemma IsCohomEquiv.comp_iff (h' : IsCohomEquiv F α') : IsCohomEquiv F (α' ≫ α) ↔
  IsCohomEquiv F α := by simp [IsCohomEquiv, ← (h' _).of_comp_iff', comp_def]; rfl

namespace Comparison

lemma pull_id_eq_push : pull ⟨𝟭 C, β⟩ (𝟙 N) n =
  push N β n := by ext; simp [mapExactFunctor_restrictAlong_id]

lemma pull_whiskerRight {φ ψ} η (β : _ ⟶ F') (α : N' ⟶ _) :
  pull ⟨φ, whiskerRight η F ≫ β⟩ α n = pull ⟨ψ, β⟩ (α ≫ whiskerRight η N) n := by ext; simpa using!
  congr((push _ β n $(mapExactFunctor_naturality ((whiskeringLeft ..).map η) _)).map _ α n)

lemma map_pull_eq_pull_map {b} (w : a' ≫ a = b ≫ whiskerLeft _ α := by exact freeAb.hom_ext) n x :
    map _ a' n (c.pull a n x) = c.pull b n (map F α n x) := by aesop

lemma pull_trans {α' : N'' ⟶ _} x : c'.pull α' n (c.pull a n x) =
    (c.trans c').pull (α' ≫ whiskerLeft _ a) n x := by simp [mapExactFunctor_mapExactFunctor]; rfl
