/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateMap
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.HodgeTate.HodgeTateMap. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/HodgeTate/HodgeTateMap.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate.HodgeTatePairs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology (known result; see
Lib.PadicComparison.HodgeTate.HodgeTateVectors).

This file: Hodge–Tate map in weight h: definition, naturality, scaling, multiplicativity. -/

open AddCommGrpCat CategoryTheory HodgeTatePair Finset TotalH TensorProduct

attribute [local simp] Functor.curryObj contractionPow H.smul_eq_push H.map H.push comp_assoc
  cup_comp_homClass_left

variable {p k} [Field k] [EmbeddedInQpBar p k] {N N' : AbFunctor (CommAlg k)} {q h} (α :
  N' ⟶ N) (x : HodgeH N q) {n}

/-- For a functor N from k-algebras to abelian groups, the total cohomology of (S,M) ↦
N(B_{S,M}) with coefficients F on the category of pairs; the target of λ_h. -/
abbrev PairH N := TotalH (pairAlg ⋙ N) scalarCoeff

/-- The Hodge–Tate map λ_h: restrict a Hodge class along B_{S,M} → T ⊕ M, apply the h-th power
of the contraction class, and project ⋀M to degree zero. -/
noncomputable def hodgeTateMap (h : ℕ) : HodgeH N q →ₗ[k] PairH N :=
  ⟨⟨((Comparison.restrict toHodgeTest _).pull (Functor.whiskerRight
  toSqZero N) q · |>.toTotalH.comp (contractionPow h)), by simp⟩, by simp [← comp_smul,
  ← act_comp_contractionPow, comp_assoc_of_eq, of_comp_homClass, Comparison.pull]⟩

/-- For α: N' → N, the k-linear pull-back from total Ext(N∘B,F) to total Ext(N'∘B,F), where B is
(S,M) ↦ B_{S,M}. -/
noncomputable def PairH.map : PairH N →ₗ[k] PairH N' :=
  ⟨(pullbackAlong (pairAlg.whiskerLeft α)).toAddHom, comp_smul⟩

/-- The k-linear map from the degree-n cohomology of N(T) on p-adic tests to total Ext(N∘B,F):
restrict along B_{S,M} → T and include as the degree-n summand. -/
noncomputable def restrictToPairs : H (genericOver ⋙ N) genericCoeff n →ₗ[k] PairH N :=
  ⟨⟨Abelian.Ext.toTotalH ∘ (Comparison.restrict toTest _).pull (Functor.whiskerRight toGeneric N)
  n, by simp⟩, by simp [smul_eq_comp, of_comp_homClass, Comparison.pull]; bound⟩

lemma restrictToPairs_map x : restrictToPairs (.map _ (genericOver.whiskerLeft α) n x) = .map α
  (restrictToPairs x) := by simpa using! (Comparison.pull_comp_restrictAlong (.mk₀ α) ..).symm

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- The Hodge–Tate map λ_h is natural: for α: N' → N and a Hodge class x on N, λ_h(α^* x) = α^*
λ_h(x). -/
lemma hodgeTateMap_map : hodgeTateMap h (.map α x) = .map α (hodgeTateMap h x) := by
  simpa using! (comp_assoc_of_eq (Comparison.pull_comp_restrictAlong (.mk₀ α) ..) _).symm

/-- For t in k and a Hodge class x of any degree, the Hodge–Tate map in weight h satisfies
λ_h(s_t x) = t^h λ_h(x), where s_t is the scaling induced by (a, m) ↦ (a, tm). -/
lemma hodgeTateMap_scale t (x : HodgeH N q) : hodgeTateMap h (.scale t x) =
  t ^ h • hodgeTateMap h x := by
  erw [← comp_smul, ← scaleModule_comp_contractionPow, ← (x.mapExactFunctor_restrictAlong_id ▸
    mapExactFunctor_naturality ((Functor.whiskeringLeft ..).map _) x :)]
  simp [hodgeTateMap, comp_assoc_of_eq, of_comp_homClass, Comparison.pull]; rfl

variable {a b} [HasFlatValues N] {M L : AbFunctor HodgeTatePair} [HasFlatValues M] (x :
  HodgeH N a) (y : HodgeH N' b) (e : b + a = n)

/-- For y in total Ext(L,F), the k-linear map x ↦ x × y from total Ext(M,F) to total Ext(M ⊗
L,F): external product followed by multiplication in F. -/
noncomputable def HodgeTatePair.cross (y : TotalH L scalarCoeff) :
  TotalH M scalarCoeff →ₗ[k] TotalH (abTensor M L) scalarCoeff := ⟨⟨(·.cup y |>.comp (.homClass
  (toTest.whiskerLeft (PadicTest.genericAlg ⋙ forget₂ ..).mulPairing))), by simp [TotalH.cup]⟩,
  by simp [smul_eq_comp]; intros; repeat erw [← homClass_comp]
     congr 2; exact abTensor_hom_ext fun _ _ _ ↦ congrArg _ (smul_mul_assoc ..)⟩

set_option backward.isDefEq.respectTransparency false

/-- Binomial rule: for x in Ext^a(M,Λ) and y in total Ext(L,Λ), the wedge product x × y followed
by u_l = `contractionPow` l equals ∑_{h ≤ l} C(l,h)(−1)^{(a+h)(l−h)} (x·u_h) × (y·u_{l−h}). -/
lemma HodgeTatePair.contractionPow_cup l (x : H M _ a) (y : TotalH L _) :
  comp (.cup x.toTotalH y) (pullbackAlong wedgePairing (contractionPow l)) = ∑ h ∈ range (l +
  1), l.choose h • (-1 : k) ^ ((a + h) * (l - h)) • cross (comp y (contractionPow (l - h)))
  (comp x.toTotalH (contractionPow h)) := by
  induction l generalizing a y
  simp [cross, cup_comp_homClass_right, ← homClass_comp]
  congr 2; exact abTensor_hom_ext fun X _ _ ↦
    congrArg _ ((@ExteriorAlgebra.algebraMapInv X.GenericRing ..).map_mul ..)
  let E : Cocycle (abTensor formCoeff formCoeff) (piAbFunctor fun _ ↦ abTensor formCoeff
    formCoeff) := ⟨fun f ↦ ofHom (.pi (cond · (abTensorMap (contractionCocycle.component f)
    (formCoeff.map f)) (abTensorMap (formCoeff.map f) (contractionCocycle.component f)) |>.hom)),
    fun _ _ ↦ addCommGrp_tensor_hom_ext (by simp [funext_iff, contractionCocycle.cocycle_comp,
    add_tmul, tmul_add, piAbFunctor, abTensor])⟩
  have h b : (comp (.cup x.toTotalH y) E.cohomClass).comp (.homClass (piAbFunctor.π _ b)) =
    cond b (.cup (x.toTotalH.comp contractionCocycle.cohomClass) y)
    ((-1) ^ a • .cup x.toTotalH (y.comp contractionCocycle.cohomClass)) := by
    simp_rw [TotalH.cup, TotalH.map_comp, comp_assoc]
    erw [← map_zsmul, map_extClass contractionCocycle.shortExact_extension,
      map_extClass contractionCocycle.shortExact_extension,
      ← extClass_sign_comm (abTensor_shortExact contractionCocycle.shortExact_extension)]
    cases b <;> refine congrArg (_ ∘ _) (.trans (E.cohomClass_comp_eq_extClass (S := ⟨_, _, _⟩) _ _
      _ (fun _ ↦ by apply abTensorMap <;> first | apply 𝟙 | exact ofHom (.inr _ (formCoeff _))) ?_
      ?_) id_comp) <;> intros <;> apply addCommGrp_tensor_hom_ext <;> simp [Cocycle.extension,
      abTensor, piAbFunctor, E, piAbFunctor.π, ← add_tmul, ← tmul_add]
  rw [sum_choose_succ_nsmul fun _ _ ↦ _, contractionPow, ← TotalH.comp_assoc_of_sq
    (E.cohomClass_naturality _ _ ((piAbFunctor.π _ false ≫ abTensor.map (toHodgeTest.whiskerLeft
    (HodgeTest.scaleModule ..)) _ + piAbFunctor.π _ true) ≫ wedgePairing) fun _ _ _ ↦
    addCommGrp_tensor_hom_ext (congrArg _ <| contraction_mul _ (neg_one_smul k) ·.1 ·.1))]
  simp [TotalH.homClass, Abelian.Ext.mk₀_add, homClass_comp, ← comp_assoc, h,
    ← cup_comp_homClass_left]
  simp [comp_of, *, smul_sum]
  congr! 2 <;> simp_all [← comp_of, scaleModule_comp_contractionPow, comp_smul,
    Nat.succ_sub] <;> module

/-- Product formula: for Hodge classes x of degree a and y, λ_l(x × y) = ∑_{h ≤ l}
C(l,h)(−1)^{(a+h)(l−h)} λ_h(x) × λ_{l−h}(y).

Known result: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. -/
lemma hodgeTateMap_cup l : hodgeTateMap l (N := abTensor N N') (_root_.cup exteriorAlg.mulPairing x
  y e) = ∑ h ∈ range (l + 1), (l.choose h • (-1 : k) ^ ((a + h) * (l - h)) • cross
  (hodgeTateMap (l - h) y)) (hodgeTateMap h x) := (comp_assoc_of_eq ((cup_of ..).trans
  (congrArg _ (Comparison.pull_cup (by simp) ..).symm)) _).symm.trans (contractionPow_cup ..)
