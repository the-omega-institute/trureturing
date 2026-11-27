/- GID: D5/S3/Zeros/GRH/Lib/General/Algebra/TensorCohomology
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Algebra/TensorCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Algebra.TensorCohomology. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Algebra/TensorCohomology.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.BijectiveComparisons
import D5.S3.Zeros.GRH.Lib.PadicComparison.Descent.ReductionModP
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Flat change of coefficients in Ext cohomology is a map of delta-functors. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor


open CategoryTheory TensorProduct Function Module Flat Abelian.Ext H Comparison LongExactSeq Functor
variable {C C'} [Category C] [Category C'] {S T M} [CommRing S] [CommRing T] [Algebra S T]
  [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M] {Φ : C ⥤ ModuleCat S} {Φ' φ}
  {N K : AbFunctor C} {N' : AbFunctor C'} {n} (β : φ ⋙ Φ ⟶ Φ') (α : N' ⟶ φ ⋙ N)

@[simp] lemma baseChangeMap_tmul m x : baseChangeMap T M N Φ n (m ⊗ₜ x) =
  push N (tensorWith.mk T m Φ) n x := (rfl)

/-- For β: Φ∘φ → Φ' of functors to S-modules and α: N' → N∘φ, the comparison map H^n(N, Φ) →
H^n(N', Φ') as an S-linear map. -/
noncomputable def Comparison.pullₗ n : H N (moduleCoeff Φ) n →ₗ[S] H N' (moduleCoeff Φ') n :=
  {(ofModuleHom _ β).pull α n
  with map_smul' _ := by apply pull_push ⟨φ, _⟩; ext; apply_rules [ULift.ext, LinearMap.map_smul]}

lemma baseChangeMap_pull x : baseChangeMap T M _ _ n ((pullₗ β α n).lTensor M x) = pullₗ
    (by exact whiskerRight β (tensorWith T M)) α n (baseChangeMap T M N Φ n x) := by
  induction x <;> simp_all; symm; apply pull_push ⟨φ, _⟩; rfl

lemma push_homReprEquiv_symm β A x : push _ β 0 (mk₀ ((homReprEquiv A K).symm x)) =
  mk₀ ((homReprEquiv A N).symm (β A x)) := (mk₀_comp_mk₀ ..).trans
  (congrArg _ ((Equiv.eq_symm_apply _).2 (congrArg _ ((homReprEquiv ..).1.4 x))))

lemma Ten.freeAb_reprBy A : AllBijective (baseChangeMap T M (freeAb (reprBy A)) Φ ·) := Nat.rec
  ((bijective_iff_of_comm_sq (by induction · <;> simp_all [mk₀_add]; apply push_homReprEquiv_symm)
  (((addEquiv₀.trans ((homReprEquiv ..).trans .ulift)).symm.toLinearEquiv (M :=
  Φ A) (by solve_by_elim [push_homReprEquiv_symm, symm])).lTensor M).bijective (mk₀_bijective ..)).1
  ((homReprEquiv ..).trans .ulift).symm.bijective) (by simp [Bijective, Surjective, nontriviality])

lemma hasFlatBaseChange_reprFunctor (A : C) :
  FP (freeAb (reprBy A)) := by simp [FP, Ten.freeAb_reprBy]

/-- For M flat over S, the maps M ⊗_S Ext^n(N, Φ) → Ext^n(N, M ⊗ Φ) admit dévissage in N
(`Devissage`): the four and five lemmas apply to them along short exact sequences. -/
lemma Ten.devissage [Flat S M] : Devissage (baseChangeMap T M · Φ ·) :=
  let t {N} n := (baseChangeMap T M N Φ n).toAddMonoidHom
  let l {N N' a n n'} (e : H N' N a) h := (AddCommGrpCat.ofHom (LinearMap.lTensor M
    ⟨(e.precomp _ h).toAddHom, by simp [smul_eq_push, push]⟩).toAddMonoidHom).hom
  have k {N N' a n n'} e h x : t n' (@l N N' a n n' e h x) = e.comp (t n x) h := by
    apply x.induction_on .. <;> simp_all [l, t, push]
  have L _ e := let L := contravariant e _; (by constructor <;> tauto : Hom
    ⟨(l _ ·.zero_add), (l _ ·.zero_add), (l _ ·.one_add), lTensor_preserves_injective_linearMap _
    L.injective_f, (lTensor_exact M <| L.exact_f_g ·), (lTensor_exact M <| L.exact_g_delta ·),
      (lTensor_exact M <| L.exact_delta_f ·)⟩ (contravariant e _) t t
      t); ⟨⟨by exact (L _ · |>.four_lemma)⟩, fun _ ↦ (have := subsingleton_of_id_eq_zero ·; by
      simp [nontriviality, AllBijective, Bijective, Surjective]), (L · · |>.five_lemma)⟩

/-- Restriction along φ from H^n(h_B, F) to the cohomology of Hom(B, φ –) with coefficients F∘φ
is bijective for all n; so the latter is F(B), in degree 0. -/
abbrev IsAcyclicAt (φ : C' ⥤ C) F B := IsBijective (.restrict φ F) (freeAbMap (𝟙 (φ ⋙ reprBy B)))

variable {β α D} [Category D] {Ψ : C ⥤ D}

/-- For β: Ψ∘φ → Ψ', α: N' → N∘φ and a functor F to S-modules, the statement that H^n(N, F∘Ψ) →
H^n(N', F∘Ψ') is bijective for all n. -/
abbrev CoeffCompBij {Ψ'} (β : φ ⋙ Ψ ⟶ Ψ') (α : N' ⟶ φ ⋙ N) F :=
  (ofModuleHom (S := S) φ (Φ := Ψ ⋙ F) (whiskerRight β F)).IsBijective α

lemma Comparison.IsBijective.baseChangeMap_bijective_iff (H : (ofModuleHom φ β).IsBijective α) [Flat
  S M] (h : FP N) : AllBijective (baseChangeMap T M N' Φ' ·) ↔ CoeffCompBij β α (_root_.tensorWith T
  M) := forall_congr' fun n ↦ (bijective_iff_of_comm_sq (by apply baseChangeMap_pull)
  (map_bijective bijective_id (H n)) bijective_id).symm.trans ((h ..).of_comp_iff _)
