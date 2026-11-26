import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Etale.EllAdicCohomology
import OmegaMath.NumberTheory.GRH.Lib.PadicComparison.Primitive.TiltedTheory
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Primitive comparison theorem and period isomorphism (known result; see
Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology).

This file: Primitive comparison modulo p lifts to period-ring coefficients. -/


open CategoryTheory TensorProduct Functor PadicTest AlgebraTensorModule WittVector PadicInt ZMod
  Comparison
variable {p} [ThePrime p] {S} [CommRing S] [Algebra Ainf S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p]
  Ainf S] (b) [CommRing b] [Algebra (ZMod p) b] (K) [CommRing K] [Algebra S K] [Module.Flat S K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] S K] {Ψ} (θ :
  asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ)

noncomputable local instance : Algebra ℤ_[p] b := .compHom _ (constantCoeff.comp (fromPadicInt p))

local instance : IsScalarTower ℤ_[p] (ZMod p) b := .of_compHom ..

/-- Primitive comparison: let (S, K) satisfy `IsPeriodRingPair`, K flat over S, Ψ ≅ K ⊗ (S ⊗
W(c^♭))^ on p-adic tests c. The natural map K ⊗ W(LC(Spec c[1/p], 𝔽_p)) → Ψ is bijective on
cohomology along α: N' → N if N, N' have flat base change, all Hⁿ(N, ℤ_p) are finitely
generated, and `primitiveMap` ⊗ (S/p) ⊗ 𝔪 is. -/
lemma exists_primitive_period_comparison (hS : IsPeriodRingPair p S K) : ∃ γ :
  genericTest ⋙ asModules ((testIncl ⋙ locConstAlg) ⋙ wittFunctor ℤ_[p]) ⋙ tensorWith K K ⟶
  Ψ, (∀ A a x, γ A (a ⊗ₜ x) = θ.1 A (a ⊗ₜ .of _ _ (1 ⊗ₜ .map (locConstToTilt A).1.1 x))) ∧
  ∀ {N N'} {α : N' ⟶ _ ⋙ N}, FP N → FP N' → (∀ n, Module.Finite ℤ_[p] (H N ellAdicCoeff n)) →
  CoeffCompBij primitiveMap α (almostCoeff (OFlat ⊗[Ainf] S)) →
  (ofModuleHom _ γ).IsBijective α := let Θ := (testIncl ⋙ locConstAlg) ⋙ wittFunctor _
  let c := NatIso.ofComponents (fun _ ↦ (cancelBaseChange ..).symm.toModuleIso) fun _ ↦ by
    exact ModuleCat.hom_ext tmul_ext
  let j : Θ ⋙ _ ⟶ (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S) ⋙ 𝟭
    _ := open Algebra.TensorProduct in (baseChangeTranspose ..).2
    (.mk fun _ ↦ ConcreteCategory.ofHom ⟨includeRight.1.comp (map includeRight.1), fun z ↦ .trans
    (congrArg (tmul _ 1) (ext fun _ ↦ (includeRight.2 _).trans (congrArg _ (cast_id ..))))
    ((includeRight.2 _).trans congr($(IsScalarTower.algebraMap_eq ..) z ⊗ₜ 1).symm)⟩)
  let o := whiskerRight (j ≫ whiskerLeft _ (algCompletion.of ..)) _
  ⟨whiskerLeft _ (c.1 ≫ whiskerRight o _) ≫ whiskerRight primitiveMap (asModules (periodAlg ..) ⋙
    tensorWith ..) ≫ θ.1,
    fun _ _ _ ↦ congrArg (θ.1 _ <| _ ⊗ₜ ·) ((adicMap_algebraMap ..).trans (congrArg _ (congrArg₂
    (tmul _) (mul_one 1) (ext fun _ ↦ one_smul OFlat _)))), fun hN hN' hf P ↦ by
  have h₀ A : IsPerfectTorsionFree (oFlatLocConst A) := ⟨perfectRing_tensor (by simp) ⟨.of _ OFlat,
    inferInstance⟩ ⟨_, perfectRing_locConstAlg _⟩, .of_ne_zero (M := _ ⊗ _) pFlat_ne_zero⟩
  obtain ⟨v, w⟩ := witt_reduction_spec (ZMod p), witt_reduction_spec OFlat, (h₀ · |>.1),
    isTorsionFree_of_dvd_pow (S := ℤ_[p]) hS.isSMulRegular_natCast (unitCoeff_spec · ▸ by aesop)
  refine (isBijective_iff_of_coeff_iso (whiskerRight c.1 (moduleCoeff (𝟭 _))) _ ((isoWhiskerRight θ
    (moduleCoeff (𝟭 _))).eq_comp_inv.2 rfl)).2 (((hN.isBijective_of_isReductionMod ⟨.of_ne_zero
    NeZero.out, maximalIdeal_eq_span_p.rec {}⟩
    hS.isCompleteTorsionFree (locConstAlg.1 ·.1 |> v |>.2.1) irreducible_p (Θ := Θ) o (by simp
    [Module.rank_lt_aleph0]) (isCompleteTorsionFree_completion <| isSMulRegular_tensor_witt
    hS.regular <| h₀ ·) fun A _ _ q h ↦ ?_).baseChangeMap_bijective_iff hN).1 (by tauto) |>.trans
    (P.periodAlg_of_almostCoeff hN hS (by tauto) h₀ isPerfectTorsionFree_tilt) rfl)
  let B := locConstAlg.1 A.1
  let g := (⟨constantCoeff, fun _ ↦ congr(algebraMap _ _ $(cast_id p _))⟩ :
    Θ A →ₐ[ℤ_[p]] B).toLinearMap
  obtain ⟨_ : IsScalarTower ℤ_[p] Ainf OFlat, ⟨t, u⟩, ⟨s, k⟩, ⟨-, e⟩⟩ := .of_compHom ..,
    h.comp_algebraMap, (v _).1.lTensor g (L := S), (w _).1.lTensor (wittConstCoeff (oFlatLocConst
    A)) (L := S), CompatibleSMul.of_algebraMap_surjective OFlat B (@ringHom_surjective p ℤ_[p] _ _)
  let E := (cancelBaseChange ..).symm ≪≫ₗ congr (.refl S S) (.ofBijective (rTensor _ B _)
    ((w _).1.bijective_rTensor ((Algebra.linearMap Ainf OFlat).restrictScalars ℤ_[p])
    (ZModModule.char_nsmul_eq_zero p)) ≪≫ₗ equivOfCompatibleSMul (ZMod p) ..)
  have i : (wittConstCoeff ..).baseChange S ∘ₗ (j A).1.toLinearMap = E.1 ∘ₗ g.baseChange S :=
    ext fun a x ↦ congr($(by simp) ⊗ₜ ($(by simp) ⊗ₜ _))
  use t.forall.2 fun _ ↦ (E.surjective.comp s _).imp ((q.comp _).sub_mem_ker_iff.1 ∘
    (u _).2 ∘ (e _).1 ∘ LinearMap.sub_mem_ker_iff.2 ∘ congr($i ·).trans), fun x ↦ by
    erw [u, ← e, congr($i x), E.map_eq_zero_iff, k]; rfl⟩
