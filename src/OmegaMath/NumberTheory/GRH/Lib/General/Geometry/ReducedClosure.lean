import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.Base
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Line bundles as cocycles of functions on ring-valued points; sections, frames. Dense
complex points, reduced closure, lifting maps into closed subschemes. -/

open AlgebraicGeometry CategoryTheory IsLocalRing RingHom Spec Scheme.IdealSheafData

variable {X Y Z : Scheme.{0}} {ι κ : Type} {t : Y ⟶ X} {U' : X.Opens} (ξ : κ → (Spec ⟨ℂ⟩ ⟶ X))

/-- For a ring homomorphism φ from ι to κ, the induced morphism of schemes from Spec κ to Spec ι. -/
noncomputable abbrev specMap [CommRing ι] [CommRing κ] (φ : ι →+* κ) :=
  Spec.map (CommRingCat.ofHom φ)

/-- The morphism t: Y → X lands in the open U, that is, t⁻¹U is all of Y. -/
def LandsIn (t : Y ⟶ X) (U : X.Opens) := ⊤ ≤ t ⁻¹ᵁ U

/-- Functions on ring-valued points of X: rules attaching an element of A to every point Spec A
→ X, for every ring A, with no compatibility required. -/
abbrev PointFn X := ∀ A, (Spec.{0} A ⟶ X) → A

@[simp] lemma landsIn_inf {V} : LandsIn t (U' ⊓ V) ↔ LandsIn t U' ∧ LandsIn t V := forall₂_and

@[simp] lemma landsIn_top : LandsIn t ⊤ := le_rfl

@[simp] lemma landsIn_preimage {s} : @LandsIn _ Z s (t ⁻¹ᵁ U') ↔ LandsIn (s ≫ t) U' := .rfl

lemma LandsIn.comp {U : X.Opens} : LandsIn t U → ∀ a, @LandsIn _ Z (a ≫ t) U := by tauto

/-- The function f is regular on U: for points t: Spec A → X landing in U, its value commutes
with all ring maps φ: A → B. -/
def PointFn.IsRegularOn (f : PointFn X) U := ∀ ⦃A B⦄ φ t, LandsIn t U → f B (Spec.map φ ≫ t) =
  φ (f A t)

/-- For a point t: Spec A → X landing in U, the ring map Γ(X, U) → A evaluating sections at t. -/
noncomputable def PointFn.evalSection {A} t (h : LandsIn t U') :=
  t.appLE U' ⊤ h ≫ (Scheme.ΓSpecIso A).1

/-- The function on points given by a section s over U: its value at t is t*s if t lands in U,
and 0 otherwise. -/
noncomputable def PointFn.ofSection {U : X.Opens} :
    Γ(X, U) →ₙ+* PointFn X := by use! fun s _ t ↦ if h : _ then evalSection t h s else 0 <;> aesop

/-- A line bundle on X as an open cover U_i with transition functions g_ij regular on U_i ∩ U_j,
satisfying g_ii = 1 and g_ij g_jk = g_ik. -/
@[ext] structure LineBundle (X : Scheme.{0}) (ι : Type) where
  opens : ι → X.Opens
  transition : ι → ι → PointFn X
  cover : ⨆ i, opens i = ⊤ := by simp [← iSup_inf_iSup, ← iInf_iSup_eq_of_finite, LineBundle.cover]
  regular i j : (transition i j).IsRegularOn (opens i ⊓ opens
    j) := by simp_all [PointFn.IsRegularOn, LineBundle.regular _ _ _ _]
  transition_self i A t : LandsIn t (opens i) →
    transition i i A t = 1 := by simp +contextual [LineBundle.transition_self]
  transition_trans i j k A t : LandsIn t (opens i) → LandsIn t (opens j) → LandsIn t (opens k) →
    transition i j A t * transition j k A t = transition i k A t :=
    by (try simp +contextual [LineBundle.transition_trans,
    ← Finset.prod_mul_distrib]) <;> grind [LineBundle.transition_trans]

variable (L : LineBundle X ι) (M : LineBundle X κ) (R) [CommRing R] [X.Over (Spec ⟨R⟩)] (p :
  Y ⟶ X) (s : ι → PointFn X)

/-- For p: Y → X and a function f on ring-valued points of X, the function t ↦ f(p∘t) on
ring-valued points of Y. -/
@[simp] noncomputable def PointFn.pull (f : PointFn X) : PointFn Y := (f · <| · ≫ p)

noncomputable instance :
    Algebra R (PointFn X) := toAlgebra (.pi fun _ ↦ .pi (· ≫ X ↘ Spec ⟨R⟩ |> preimage |>.hom))

/-- The pull-back of the line bundle (U_i, g_ij) along p: Y → X, with cover p⁻¹U_i and
transition functions p*g_ij. -/
@[simps] noncomputable def LineBundle.pull :=
  mk _ (L.transition · · |>.pull p) (p.iSup_preimage_eq_top L.3)

/-- The trivial line bundle on X: the single open set X and the transition function 1. -/
@[simps] def LineBundle.one : LineBundle X Unit where opens _ := ⊤; transition _ _ := 1

/-- The dual line bundle: the same cover, with (i, j) transition function g_ji. -/
@[simps] def LineBundle.inv := mk L.opens fun i ↦ (L.transition · i)

/-- The tensor product L ⊗ M: the cover by the intersections U_i ∩ V_a, with products of
transition functions; for linear systems, the Segre product. -/
@[simps] def LineBundle.mul := mk (fun i : ι × κ ↦ L.opens i.1 ⊓ M.opens i.2) fun i j ↦
  L.transition i.1 j.1 * M.transition i.2 j.2

/-- The family (s_i) is a global section of L: each s_i is regular on U_i, and s_i = g_ij s_j at
points landing in U_i and U_j. -/
def LineBundle.IsSection := (∀ i, (s i).IsRegularOn (L.opens i)) ∧ ∀ i j A t,
  LandsIn t (L.opens i) → LandsIn t (L.opens j) → s i A t = L.transition i j A t * s j A t

/-- The family s is a nowhere vanishing global section of L: a section with s_i a unit at every
point landing in U_i. -/
def LineBundle.IsFrame := L.IsSection s ∧ ∀ i A t, LandsIn t (L.opens i) → IsUnit (s i A t)

/-- The line bundles L and M are isomorphic: L ⊗ M⁻¹ has a nowhere vanishing global section. -/
def LineBundle.IsIsomorphic := ∃ u, (L.mul M.inv).IsFrame u

/-- The R-module of global sections of L, for a scheme X over R. -/
def LineBundle.H0 : Submodule R (ι →
  PointFn X) := by use! {s | L.IsSection s ∧ ∀ i A t, ¬LandsIn t (L.opens i) → s i A t =
  0} <;> simp [IsSection, PointFn.IsRegularOn, HSMul.hSMul, SMul.smul] <;> grind

/-- Let i: Y → Z be a closed immersion and f: X → Z with X reduced. If the preimage under f of
the image of i is dense in X, then f factors through i. -/
lemma exists_lift_of_dense_preimage {X Y Z} [IsReduced X] i [@IsClosedImmersion Y Z i] (f : X ⟶ Z)
    (h : Dense (f ⁻¹' .range i)) : ∃ g, g ≫ i = f :=
    ⟨_, IsClosedImmersion.lift_fac i _ (map_bot f ▸ (map_gc f).le_u (support_eq_top_iff.1 (by
    ext; simp [i.support_ker, f.continuous.closure_preimage_subset _ (h _)])).le)⟩

/-- The images of the complex points ξ_z : Spec ℂ → X form a dense subset of X. -/
abbrev IsDenseFamily {Z : Type} {X} (ξ : Z → (Spec ⟨ℂ⟩ ⟶ X)) := DenseRange (ξ · (closedPoint ℂ))

/-- The family ξ_z : Spec ℂ → X is separating: X is reduced and the images of the ξ_z have dense
union. -/
def IsSeparatingFamily {Z : Type} {X} (ξ : Z → (Spec ⟨ℂ⟩ ⟶ X)) := IsReduced X ∧ IsDenseFamily ξ

/-- Reduced closure: complex points ξ_z : Spec ℂ → X factor as ξ_z = i ∘ e_z through a closed
immersion i : Y → X, with Y reduced and the points e_z dense in Y. -/
lemma exists_reduced_closure : ∃ Y i e, IsClosedImmersion i ∧ (∀ z, e z ≫ i = ξ z) ∧
  @IsSeparatingFamily κ Y
  e := let h z := (exists_lift_of_dense_preimage (vanishingIdeal (.closure (.range (ξ · (closedPoint
  ℂ))))).subschemeι (ξ z) (dense_indiscrete ⟨_, ⟨_, subset_closure ⟨z, rfl⟩⟩, rfl⟩)).choose_spec
  ⟨_, _, _, inferInstance, h, @.of_openCover _ (subschemeCover _).cover fun _ ↦
  (affine_isReduced_iff _).2 ((Ideal.isRadical_iff_quotient_reduced _).1
  (PrimeSpectrum.isRadical_vanishingIdeal _)), (subschemeι _).isEmbedding.dense_iff.2
  (closure_mono (by grind [Scheme.Hom.comp_apply]) ·.2)⟩
