/- GID: D5/S3/Zeros/GRH/Lib/General/Geometry/ConstantFunctions
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Geometry/ConstantFunctions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Geometry.ConstantFunctions. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Geometry/ConstantFunctions.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Algebra.TangentNakayama
import D5.S3.Zeros.GRH.Lib.Shimura.AbelianScheme.KernelRing
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: Locus where a point lies in a closed subscheme is an ideal. fpqc descent: a functional
relation total on a cover is a morphism. Global functions on a base-changed abelian variety are
constant on fibres. -/

open CategoryTheory AlgebraicGeometry Ideal.Quotient Limits.pullback CommRingCat Spec RingHom

lemma le_ker_iff_factors {S B} [CommRing S] [CommRing B] {I} {γ : S →+* B} : I ≤ ker γ ↔ ∃ l,
    l ≫ specMap (mk I) = specMap γ := ⟨(⟨specMap <| lift _ _ ·, (map_comp ..).symm⟩),
  fun ⟨l, h⟩ x m ↦ by simpa [eq_zero_iff_mem.2 m] using congr(preimage $h x).symm⟩

/-- For a closed immersion i: Z → X and a: Spec S → X, there is an ideal I of S, finitely
generated if i is of finite presentation, such that a∘Spec γ factors through Z exactly when
γ: S → B kills I. -/
lemma exists_ideal_le_ker_iff_factors {S} [CommRing S] {X Z} i [@IsClosedImmersion.{0} Z X i] a :
  ∃ I, (LocallyOfFinitePresentation i → I.FG) ∧ ∀ ⦃B⦄ [CommRing B] (γ : S →+* B), I ≤ ker γ ↔ ∃ l,
  l ≫ i = map (ofHom γ) ≫ a := (IsClosedImmersion.Spec_iff (f := snd i a).1 inferInstance).imp
  fun I ⟨e, he⟩ ↦ ⟨fun _ ↦ I.mk_ker ▸ by apply_rules +allowSynthFailures [mk_surjective,
  Algebra.FinitePresentation.ker_fG_of_surjective (mkₐ S I), (e.inv_comp_eq.2 he).subst,
  (LocallyOfFinitePresentation.SpecMap_iff (ofHom _)).1], fun _ _ _ ↦
  le_ker_iff_factors.trans ⟨.imp'
  (· ≫ e.2 ≫ fst ..) (by grind [condition]), (⟨lift _ _ ·.choose_spec ≫ e.1, by grind [lift_snd]⟩)⟩⟩

open GrothendieckTopology Sheaf Precoverage CartesianMonoidalCategory AddGrpObj

/-- Descent: let R relate T-points x of W to y of A, be stable under pull-back and subtraction,
and total on an fpqc cover of A. A homomorphism f : W → B killing points related to 0 gives
a homomorphism F with F(y) = f(x) whenever R(x,y). -/
lemma exists_hom_of_rel {S} {A B W : Over S} [AddObj A] [AddObj B] [AddObj W] (f : W ⟶ B)
  [IsAdditive f] (R : ∀ {T}, (T ⟶ W) → (T ⟶ A) → _) (nat : ∀ {T' T x y} a, @R T x y →
  @R T' (a ≫ x) (a ≫
  y)) (sub : ∀ {T x y x' y'}, @R T x y → R x' y' → R (x - x') (y - y')) (ker : ∀ {T} x, @R T x 0 → x
  ≫ f = 0) P (hP : P ∈ AlgebraicGeometry.Scheme.fpqcPrecoverage A.left) (h : ∀ Z g, @P Z g → ∃ x,
  R x ((Over.mk (g ≫ _)).homMk g)) : ∃ F, IsAdditive F ∧ ∀ T x y, @R T x y → y ≫ F = x ≫ f := by
  have hP := le_canonical _ _ ((mem_over_iff _ ⟨(∃ x, @R · x ·), by tauto⟩).2 (
  mem_toGrothendieck_iff_of_isStableUnderComposition.2 ⟨_, hP, (⟨_, _, 𝟙 _, h · · ·, rfl⟩)⟩))
  have {T} x y z a b := ker _ (by simpa using @sub T x y z y a b)
  refine (isSheaf_yoneda_obj B _ hP (fun _ _ ↦ (·.choose ≫ f)) fun _ ↦ ?_).exists.imp fun F (_ :
    ∀ _, _) ↦ ⟨isAdditive_of_universal (((isSheaf_yoneda_obj _).isSeparated _ (intersection_covering
    _ (pullback_stable _ (SemiCartesianMonoidalCategory.fst .. + SemiCartesianMonoidalCategory.snd
    ..) hP) (pullback_stable _ (SemiCartesianMonoidalCategory.snd ..) hP))).ext fun _ _ ⟨⟨_, a⟩,
    _, b⟩ ↦ have := sub a b; ?_), ?_⟩ <;> clear sub <;> simp_all <;> grind [comp_add, sub_comp]

open PointFn Scheme.Hom AddMonObj

/-- For s : X → S, every function regular on all of X takes equal values at two ring-valued
points of X with the same image under s. -/
def HasConstFunctions {X S : Scheme} (s : X ⟶ S) := ∀ c B x y, x ≫ s = y ≫ s →
  @ofSection X ⊤ c B x = ofSection c B y

/-- Let A be an abelian variety over a field k and X = A ×_k Spec C. A function regular on all
of X takes equal values at any two ring-valued points with the same image in Spec C. -/
lemma hasConstFunctions_of_isPullback {k} [Field k] {A} [@IsAbelianScheme (Spec ⟨k⟩) A]
  [IsIntegral A.1] {X C p s q} (H : IsPullback p s A.hom (Y := Spec C) q) :
  @HasConstFunctions X _ s := fun _ _ x y ↦ by
  let := (isField_of_universallyClosed _ A.hom).toField
  grind [(((isIso_pushoutSection_iff H landsIn_top le_rfl (by simp)).1 (by apply_rules
    [isAffineOpen_top, isIso_pushoutSection_of_isQuasiSeparated_of_flat_right, isCompact_preimage,
    isCompact_univ, isQuasiSeparated_preimage, isQuasiSeparated_univ])).epi_inr_of_epi (appLE_eq_app
    _ ▸ ConcreteCategory.epi_of_surjective _ fun _ ↦ ⟨_, (@appTop (Spec _) ..).1.injective
    congr(appTop $(ζ[A].w) _)⟩)).1 (evalSection x landsIn_top) (evalSection y _),
    ofSection_eq landsIn_top, evalSection, appLE_comp_appLE]
