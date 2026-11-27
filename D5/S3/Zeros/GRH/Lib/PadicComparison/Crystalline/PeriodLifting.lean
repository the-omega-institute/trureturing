/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/PeriodLifting
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/PeriodLifting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Crystalline.PeriodLifting. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Crystalline/PeriodLifting.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline.TestGenericFibre
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Crystalline comparison: p-adic étale cohomology with good reduction is crystalline
(known result; see Lib.PadicComparison.Crystalline.CrystallineClasses).

Part of: Primitive comparison theorem and period isomorphism (known result; see
Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology).

This file: Basis of the envelope; gamma-1 is onto with constant invariants (crystalline Poincare
lemma). Almost comparison modulo p lifts to completed Witt coefficients after inverting tau. -/

section

open Module Submodule Nat Polynomial Function Set Algebra LinearMap TensorProduct algebraMap
variable {p} [ThePrime p] {A} [CommRing A] (B : CrysTest A) {T I} [CommRing T] [Algebra B T]

/-- Let B be a p-torsion-free, p-adically complete A-algebra, T a B-algebra with B-basis u_a
v^n, and z = t − v with t in B. Then the divided power algebra `preEnvelope` of {z} has
a B-basis u_a y_n with z^n = n! y_n. -/
lemma exists_preEnvelope_basis z (b : Basis _ B T) (u : I → T) {v} {t : B} (hb : ∀ a n, b (a, n) =
  u a * v ^ n) (q : t - v = z) : ∃ (y : ℕ → preEnvelope {z}) (b : Basis _ B _), (∀ a n, b (a, n) =
  u a * y n) ∧ ∀ n, z ^ n = n ! * y n := let F := b.constr B fun j ↦ u j.1 * z ^ j.2
  let c := b.map (.ofInvolutive F (congr($((b.ext fun (a, n) ↦ by
    have h w := by simpa using congr(mulLeft B (u a) $(((C t - X) ^ n :).aeval_eq_sum_range w))
    simp [F, h, ← hb, ← h, ← q] : F * F = 1)) ·)))
  let y n : preEnvelope {z} := ⟨_, subset_adjoin ⟨z, rfl, n, rfl⟩⟩
  have e j : c j = _ := b.constr_basis B ..
  have H n := by ext; simp [y, natCast_def']
  ⟨y, _, Prod.forall'.1 (Basis.mk_apply (linearIndependent_iff'.2 fun s g h i hi ↦
    includeLeft_injective (S := ℤ) Int.cast_injective (by
    simpa [y, ← e, Finsupp.single_apply, hi, ite_tmul, smul_tmul', natCast_def', -map_smul] using
      congr(AlgebraTensorModule.rTensor ℤ ℚ (c.coord i) ($h) * i.2 !))) (by
  erw [← restrictScalars_top _ T, ← top_toSubmodule, ← adjoin_adjoin_coe_preimage, adjoin_eq_span,
    ← span_smul_of_span_eq_top c.span_eq, span_le, smul_subset_iff, forall_mem_range]
  intro j x hx; simpa [*, smul_def'] using Submonoid.closure_induction_left (by
    simp [← nsmul_eq_mul, nsmul_mem, mem_span_of_mem]) (fun x ⟨_, rfl, m, h⟩ w _ i n c ↦ by
    convert i (n + m) (c * (n + m).choose n) using 1; ext
    simp [← h, y, ← mul_assoc, pow_add, cast_add_choose, natCast_def']; field_simp) hx j.2 j.2 !)),
    H⟩

/-- Let B → E be p-torsion-free p-complete A-algebras, E with topological B-basis u_a (t−v)^n/n!,
t ∈ B, v a unit, u_{a₀} = 1. If the B-endomorphism γ has γv = (1+q)v, p³ ∣ q, q invertible in K, and
γu_a = (1+η_a)u_a with pη_a ∣ q for a ≠ a₀, then 0 → K⊗_A B → K⊗_A E → K⊗_A E → 0, by γ − 1, is
exact. -/
lemma koszulExact_pd_line {K} [CommRing K] [Algebra A K] (E : CrysTest A) [Algebra B E]
  [IsScalarTower A B E] [Zero I] {b : Basis _ B T} {j : T →ₗ[B] E} (J : IsBijOnCompletion p j) {u :
  I → E} {y : ℕ → E} {v t q} (hb : ∀ a n, j (b (a, n)) = u a * y n) (hy : ∀ n,
  (algebraMap B E t - v) ^ n = n ! * y n) (hr : IsUnit v) (ha : u 0 = 1) (hδ : p.cast ^ 3 ∣ q) (hq :
  IsUnit (algebraMap A K q)) (γ : E →ₐ[B] E) (hv : γ v = (q + 1) • v) (hu : ∀ a ≠ 0, ∃ η : A,
  γ (u a) = (η + 1) • u a ∧ p * η ∣ q) : KoszulExact (ULift.map.{0, _, 1, 1} (((Algebra.linearMap B
  E).restrictScalars A).baseChange K)) (.map ((γ.toLinearMap.restrictScalars A).baseChange K)) := by
  choose! η hu c hη using hu
  obtain ⟨⟨d, a⟩, _, _, e⟩ := hδ, isAdicComplete_over_base (S := B) E.2.2,
    B.2.2, by simpa using (hy 0).symm
  let s := -p ^ 2 * d • v
  choose w hw using fun n ↦ show ∃ w, γ (y n.succ) = y n.succ - q • v * (y n + p • w) from
    ((pdIdeal _).add_mem (pdIdeal_le_comap C (⟨_,
    hy ·⟩)) (smul_mem _ X (pdIdeal_le_comap C E.2.p_mem_pdIdeal)) n.succ).elim fun P h ↦
    (P.binomExpansion 0 s).rec fun k e ↦ ⟨-d • v * k, nsmul_right_injective n.succ.factorial_ne_zero
    (by linear_combination (norm := (simp [*, s, ↓map_pow, derivative_pow, factorial]; algebra))
         n.succ ! * e + congr(eval s $h - eval 0 $h - s * (derivative $h).eval 0 - γ $(hy n.succ)))⟩
  choose F f using (J.linearMap_comp_bijective (Y := E).2 <| b.constr ℕ ·); choose κ k using
    J.linearMap_comp_bijective.2 (b.coord (0, 0))
  simp [DFunLike.ext_iff] at f k; let m := Algebra.linearMap B E
  let S := F fun i@(a, n) ↦ ite (a = 0) (-y n.succ) (p * c a • v * j (b i))
  let L W : End B E := v • (1 - (p : B) • W)
  let W := -F fun (a, n) ↦ ite (a = 0) (w n) (c a • γ (u a) * (y n - γ v * n.casesOn 0 (y + p • w)))
  have ⟨⟨h₃, h₄⟩, h₁, h₂⟩ : (γ.toLinearMap ∘ₗ m = m ∧ κ ∘ₗ m = .id) ∧ γ.toLinearMap ∘ₗ S + -S = q •
    L W ∧ q • (m ∘ₗ (t • κ) + -L 0) = S ∘ₗ F fun i@(a, n) ↦ ite (a = 0) (-q • j ((n + 1 : B) • b i
    - n.casesOn 0 (t • b ⟨a, ·⟩))) (-η a • j (b i)) := ⟨by simpa [*, m, LinearMap.ext_ring_iff]
    using (k (b (0, 0))), by constructor <;> exact J.linearMap_comp_bijective.1 (b.ext fun (a, n) ↦
    nsmul_right_injective n.factorial_ne_zero (by
    have := (by simpa [factorial] using hy n.succ); cases n <;> simp +zetaDelta [f, k,
    apply_ite (F _)] <;> split <;> simp [*, hη a, smul_def'] <;> grind))⟩
  have H W := hq.smul_bijective.comp (f := ((L W).restrictScalars A).baseChange K)
    (TensorProduct.map_bijective (f := 1) bijective_id (hr.smul_bijective.comp ⟨fun x z e ↦ congrFun
    (@E.2.isDerivedComplete.1 (W^[·] x) (W^[·] z) (funext (by simpa [shiftDiff, ← End.pow_apply,
    pow_add] using (congr(W^[·] $e))))) 0,
    E.2.isDerivedComplete.exists_eq_of_approx E.2.isDerivedComplete _ _ fun x ↦ ⟨x, W x, by simp⟩⟩))
  apply_fun (·.restrictScalars A |>.baseChange K) at h₁ h₂ h₃ h₄
  simp [KoszulExact, subset_def, IsFixedPt, Surjective, baseChange_comp, LinearMap.ext_iff,
    ← ULift.down_inj] at *
  use LeftInverse.injective h₄, (H 0).2.forall.2 fun x e ↦ ⟨q • _, by
    simpa [add_neg_eq_zero] using (h₂ x).trans (congrArg _ (@(H W).1 _ 0 (by
    simp [← h₁, ← h₂, h₃, by simpa using e])))⟩, (H W).2.forall.2 (⟨_, h₁ ·⟩)

end

open CategoryTheory TensorProduct Function Functor Module LinearMap AlgebraTensorModule Lift
  WittVector AdicCompletion Submodule ModuleCat Comparison AddCommGrpCat

/-- Let `IsPeriodRingPair` hold for S, K with K flat over S; N has flat base change, N' for K
⊗_S G(ψ'); ψ, ψ' take values b in `IsPerfectTorsionFree`. A comparison bijective for b ⊗ (O^♭
⊗_{A_inf} S) ⊗ 𝔪 is bijective for K ⊗_S (S ⊗ W(b))^, p-adic completion. -/
lemma CoeffCompBij.periodAlg_of_almostCoeff {C C'} [Category C] [Category C'] {p} [ThePrime p] {N :
  AbFunctor C} {N' : AbFunctor C'}
  {φ} {α : N' ⟶ φ ⋙ N} (hN : FP N) {S K} [CommRing S] [Algebra Ainf S] [CommRing K] [Algebra S
  K] [Flat S K] (hK : IsPeriodRingPair p S K) {ψ ψ'} {β : φ ⋙ ψ ⟶ ψ'} (hN' : ∀ G : _ ⥤ ModuleCat S,
  AllBijective (baseChangeMap K K N' (ψ' ⋙ G) ·)) (h : ∀ A, IsPerfectTorsionFree (ψ A)) (h' : ∀ A,
  IsPerfectTorsionFree (ψ' A)) (H : CoeffCompBij β α (almostCoeff (OFlat ⊗[Ainf] S))) :
  CoeffCompBij β α (asModules (periodAlg S) ⋙ tensorWith K K) := by
  have ⟨w, z, _⟩ := witt_reduction_spec OFlat OFlat
  let c : wittMaxIdeal →ₗ[Ainf] MaxIdealFlat := (Algebra.linearMap ..).restrict (q :=
    (IsLocalRing.maximalIdeal _).restrictScalars _) fun _ ↦ (mem_wittMaxIdeal.1 · 0)
  have hc : IsReductionMod p c := ⟨(⟨⟨_, teichmuller_mem_wittMaxIdeal ·.2⟩, rfl⟩), fun _ ↦ by
    erw [Subtype.ext_iff, w.2]; simp [Subtype.ext_iff]; aesop (add simp [wittMaxIdeal, p_nonzero])⟩
  let P := asModules (wittFunctor (k := OFlat)) ⋙ tensorWith S (S ⊗[Ainf] wittMaxIdeal); let Q :=
    moduleCompletion S p
  have := CompatibleSMul.of_algebraMap_surjective (OFlat ⊗[Ainf] S) MaxIdealFlat w.1
  let E (b : CommAlg OFlat) :=
    .ofBijective _ ((hc.lTensor _).bijective_rTensor _ (by simp [p_eq_zero_of_algebra_oFlat])) ≪≫ₗ
    TensorProduct.comm .. ≪≫ₗ ((cancelBaseChange _ _ OFlat ..).symm ≪≫ₗ .lTensor b
    ((assoc _ _ _ _ S _).symm ≪≫ₗ equivOfCompatibleSMul OFlat ..)).restrictScalars _
  let e b : P b →+ _ := ((E b).1 ∘ₗ (wittConstCoeff b).lTensor _).toAddMonoidHom
  let q : P ⋙ Q ⋙ forget₂ .. ⟶ almostCoeff _ ⋙ forget₂ .. := ⟨fun b ↦ ofHom (.comp
    (QuotientAddGroup.lift _ (e b) (by simp [p_eq_zero_of_algebra_oFlat, ↓IsConcreteLE.le_iff,
    ↓mem_toAddSubgroup, ↓nsmulRange.mem_span_pow_smul_top_iff, ← Nat.cast_smul_eq_nsmul OFlat]))
    (AdicCompletion.eval _ _ 1).toAddMonoidHom), fun _ _ f ↦ ConcreteCategory.coe_ext (map_ext
    _ (DFunLike.congr_fun (tmul_ext : (e _).comp (P.2 f).1.toAddMonoidHom = .comp _ (e _)) <| · 1))⟩
  have m {D} [Category D] {ψ : D ⥤ _} (h : ∀ A, IsPerfectTorsionFree (ψ A)) :=
    modShortExact_of_isReductionMod (Φ := ψ ⋙ P ⋙ Q) (q :=
    ψ.whiskerLeft q) fun A ↦ have := (h A).1; ((witt_reduction_spec OFlat _).1.lTensor _).elim
    fun k l ↦ ⟨isSMulRegular_completion (isSMulRegular_tensor_witt (isSMulRegular_tensor_of_flat_mod
      c w hc (z.1.submodule (wittMaxIdeal.restrictScalars _) _) hK.regular) (h A)), .of_comp (g :=
      of _ _) ((E _).surjective.comp k), fun y : AdicCompletion .. ↦
    (mkQ_surjective _ (y.1 1)).elim fun x a ↦ congr(Quot.lift _ _ $a.symm = 0).to_iff.trans
    ((E _).map_eq_zero_iff.trans ((l x).trans (by simpa [↓nsmulRange.mem_span_pow_smul_top_iff,
      ← a] using! (congr(y ∈ $(pow_smul_top_eq_ker_eval (n := 1) (fg_span_singleton _)))).symm)))⟩
  let v b : _ ⟶ P b := ↟(rTensor _ _ (toSpanSingleton _ _ (1 ⊗ₜ ⟨_, toWittResidue_tau⟩)))
  have t {X Y} f (g : Y ⟶ X) (h : g ≫ f = algebraMap _ S tau • 𝟙 Y) :
      Bijective ((Q ⋙ tensorWith K K).2 g ≫ (Q ⋙ _).2 f) := by
    rw [← Functor.map_comp, h, Q.comp_map, (rfl : Q.2 _ = (_ : S) • 𝟙 _)]
    simpa [tensorWith] using! hK.isUnit_tau.smul_bijective (β := K ⊗[S] Q Y)
  let γ := isoWhiskerRight (isoOfAppBijective (whiskerRight (⟨fun _ ↦ ↟(rTensor _ _ (liftBaseChange
    S (wittMaxIdeal.subtype.smulRight 1))), fun _ _ _ ↦ hom_ext tmul_ext⟩ : P ⟶ asModules
    (wittFunctor ⋙ algBaseChange S)) (Q ⋙ tensorWith ..)) (fun b ↦ ⟨.of_comp (t (v b) _ (by
    dsimp [P, tensorWith]; ext ⟨⟩; exact congr($(by simp [← tmul_smul, mul_comm]; rfl) ⊗ₜ _))).1,
    .of_comp (t _ (v b) (by ext; exact congr($(by simp [Algebra.smul_def]) ⊗ₜ _))).2⟩) ≪≫
    (_ ⋙ algBaseChange S).isoWhiskerLeft (isoWhiskerRight (moduleCompletionIso ..) _)) (moduleCoeff
    (𝟭 _))
  refine (isBijective_iff_of_coeff_iso (c := ⟨φ,
    _⟩) (ψ.whiskerLeft γ.1) _ (whiskerLeft_comp_whiskerRight β γ.1)).1 (((.of_mod (m h) (m h')
    (by ext; exact congr(⟨$(q.2 _) _⟩)) (fun _ _ ↦ ?_) ?_ H : CoeffCompBij β α
    (P ⋙ Q)).baseChangeMap_bijective_iff hN).1 (hN' _)) <;> apply IsDerivedComplete.cohomology
    fun _ ↦ .of_isAdicComplete (AdicCompletion.isAdicComplete (fg_span_singleton _))
