/- GID: D5/S3/FiniteGroups/OriginalDFrobenius
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/OriginalDFrobenius
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Frobenius divisibility over the original Schur division ring. -/

import D5.S3.FiniteGroups.OriginalDClifford
import D5.S3.FiniteGroups.NormalizerImageAction
import D5.S3.FiniteGroups.OriginalDRegularAction
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Sylow
import Mathlib.RepresentationTheory.Invariants

/-!
The Hall coprimality argument below is the consumed portion of
Yawara Ishida, yawara/odd-order, revision
ba8ec35982ceecbd31ca987cbe0cee30477f4883,
OddOrder/Isaacs/Ch06_FrobeniusActions/KernelComplement.lean, lines 53–103.
Copyright (c) 2026 Yawara Ishida. Released under Apache-2.0.
Schur–Zassenhaus is reused directly from pinned Mathlib.
-/

noncomputable section
namespace D5.S3.FiniteGroups.OriginalDFrobenius

set_option backward.isDefEq.respectTransparency false
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped MonoidAlgebra
open OriginalDCliffordCandidate
open D5.S3.FiniteGroups.CliffordDecomposition.Representation
open D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation

universe uk uG uV
variable {G : Type uG} [Group G]

private theorem exists_complement [Finite G] (N : Subgroup G) [N.Normal]
    (hfix : ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1) :
    ∃ C : Subgroup G, N.IsComplement' C := by
  classical
  have h4 : ∀ n ∈ N, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ N := by
    intro n hn hn1 g hg
    by_contra hgN
    have hcomm : g * n = n * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hfixed : MulAut.conjNormal g (⟨n, hn⟩ : N) = (⟨n, hn⟩ : N) := by
      apply Subtype.ext
      change g * n * g⁻¹ = n
      rw [hcomm, mul_inv_cancel_right]
    exact hn1 (congrArg (fun z : N => (z : G)) (hfix g hgN ⟨n, hn⟩ hfixed))
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    by_contra hncop
    obtain ⟨p, hp, hpN, hpI⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
    have : Fact p.Prime := ⟨hp⟩
    -- Cauchy: an element `x ∈ N` of order `p`.
    obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpN
    set x : G := (x₀ : G) with hx_def
    have hx_ord : orderOf x = p := by rw [hx_def, Subgroup.orderOf_coe]; exact hx₀
    have hx_ne : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx_ord
      exact hp.one_lt.ne' hx_ord.symm
    have hxN : x ∈ N := x₀.2
    -- extend `⟨x⟩` to a Sylow `p`-subgroup `S` of `G`
    have hzp : IsPGroup p (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx_ord, pow_one]
    obtain ⟨S, hzS⟩ := hzp.exists_le_sylow
    have hxS : x ∈ (S : Subgroup G) := hzS (Subgroup.mem_zpowers x)
    have hS_nontrivial : Nontrivial ↥(S : Subgroup G) :=
      ⟨⟨⟨x, hxS⟩, 1, fun h => hx_ne (congrArg Subtype.val h)⟩⟩
    -- the center of `S` is a nontrivial subgroup of `C_G(x) ≤ N`
    have : Nontrivial (Subgroup.center ↥(S : Subgroup G)) :=
      S.isPGroup'.center_nontrivial
    obtain ⟨z₀, hz₀_ne⟩ := exists_ne (1 : Subgroup.center ↥(S : Subgroup G))
    set z : G := ((z₀ : ↥(S : Subgroup G)) : G) with hz_def
    have hz_ne : z ≠ 1 := by
      intro h1
      exact hz₀_ne (Subtype.ext (Subtype.ext h1))
    have hz_comm : ∀ s : ↥(S : Subgroup G), (s : G) * z = z * (s : G) := by
      intro s
      have := (Subgroup.mem_center_iff.mp z₀.2 s)
      exact congrArg Subtype.val this
    have hzN : z ∈ N := by
      refine h4 x hxN hx_ne ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hz_comm ⟨x, hxS⟩).symm
    -- so `S ≤ C_G(z) ≤ N`
    have hS_le_N : (S : Subgroup G) ≤ N := by
      refine le_trans ?_ (h4 z hzN hz_ne)
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hz_comm ⟨s, hs⟩
    -- contradiction: the full `p`-part of `|G|` divides `|N|`, yet `p ∣ [G:N]`
    have hcardS : Nat.card ↥(S : Subgroup G) = p ^ (Nat.card G).factorization p :=
      S.card_eq_multiplicity
    have hdvd_pow : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G := by
      rw [pow_succ, ← hcardS, ← Subgroup.card_mul_index (H := N)]
      exact mul_dvd_mul (hcardS ▸ Subgroup.card_dvd_of_le hS_le_N) hpI
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hdvd_pow
    omega
  -- Step 2: Schur-Zassenhaus complement.
  obtain ⟨A, hA⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  exact ⟨A, hA⟩

private theorem restrict_complement (N C H : Subgroup G) (hNH : N ≤ H)
    (hC : N.IsComplement' C) :
    (N.subgroupOf H).IsComplement' (C.subgroupOf H) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro h hn hc
    exact Subtype.ext (Subgroup.disjoint_def.mp hC.disjoint hn hc)
  · apply Set.eq_univ_of_forall
    intro h
    obtain ⟨⟨n, c⟩, he, _⟩ := hC.existsUnique (h : G)
    have hcH : (c : G) ∈ H := by
      have hc : (c : G) = (n : G)⁻¹ * (h : G) := by rw [← he]; group
      rw [hc]
      exact H.mul_mem (H.inv_mem (hNH n.property)) h.property
    exact Set.mem_mul.mpr
      ⟨⟨n.val, hNH n.property⟩, n.property, ⟨c.val, hcH⟩, c.property, Subtype.ext he⟩

section ActualCenter
open NormalizerImageAction
variable {k : Type uk} [Field k] {M : Type uV} [AddCommGroup M] [Module k M]
  (r : G →* (M ≃ₗ[k] M)) (L : Subgroup G) [L.Normal]
  {D : Type*} [DivisionRing D] [Module D M] [SMulCommClass k D M]
  (t : G →* Module.End D M) (ht : ∀ g x, t g x = r g x)

include ht in
private theorem image_D_linear (a : Image r L) (d : D) (x : M) :
    (a : Module.End k M) (d • x) = d • (a : Module.End k M) x := by
  rcases a with ⟨_, b, rfl⟩
  change q r L b (d • x) = d • q r L b x
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, LinearMap.add_apply, smul_add, hb, hc]
  | single n c =>
    have he : q r L (MonoidAlgebra.single n c) = c • (r (n : G)).toLinearMap := by
      change Representation.asAlgebraHom ((representation r).comp L.subtype) _ = _
      rw [Representation.asAlgebraHom_single]
      rfl
    rw [he]
    change c • r (n : G) (d • x) = d • (c • r (n : G) x)
    rw [← ht, (t (n : G)).map_smul, smul_comm, ht]

private def centerDAction : Center r L →+* Module.End D M where
  toFun z := {
    toFun := (z.val : Module.End k M)
    map_add' := (z.val : Module.End k M).map_add
    map_smul' d x := image_D_linear r L t ht z.val d x }
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl
  map_zero' := by ext x; rfl
  map_add' _ _ := by ext x; rfl

private theorem center_covariance (g : G) (z : Center r L) :
    t g * centerDAction r L t ht z =
      centerDAction r L t ht (centerAction r L g z) * t g := by
  ext x
  change t g ((z.val : Module.End k M) x) =
    (((centerAction r L g z).val : Image r L) : Module.End k M) (t g x)
  rw [ht, centerAction_coe, alpha_coe, ambient_apply, ht]
  change r g ((z.val : Module.End k M) x) =
    r g ((z.val : Module.End k M) (r g⁻¹ (r g x)))
  have hinv : r g⁻¹ (r g x) = x := by
    rw [map_inv]
    exact (r g).symm_apply_apply x
  rw [hinv]

include ht in
private theorem actual_complement_rank [Finite L] [Module.Finite k M] [Nontrivial M]
    [Module.Finite D M]
    (hsemi : letI := actualModule r L; IsSemisimpleModule k[L] M)
    (hiso : letI := actualModule r L; IsIsotypic k[L] M)
    (hfix : ∀ g : G, g ∉ L → ∀ n : L, MulAut.conjNormal g n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial ((representation r).comp L.subtype))
    (J : Subgroup G) [Finite J] (hJ : L.IsComplement' J) :
    Nat.card J ∣ Module.finrank D M := by
  classical
  letI := actualModule r L
  letI : IsScalarTower k k[L] M := by
    apply IsScalarTower.of_algebraMap_smul
    intro c x
    change q r L (algebraMap k k[L] c) x = c • x
    exact congrArg (fun f : Module.End k M => f x) ((q r L).commutes c)
  letI : IsSemisimpleModule k[L] M := hsemi
  have hlsmul : Algebra.lsmul k k M (A := k[L]) = q r L := by
    ext b x
    rfl
  letI : IsSimpleRing (Image r L) := by
    change IsSimpleRing (q r L).range
    rw [← hlsmul]
    exact FiniteIsotypicImage.isSimpleRing_actionRange hiso
  let F : Type _ := Center r L
  letI : Field F := centerField r L
  let c : J →* (F ≃ₐ[k] F) := (centerAction r L).comp J.subtype
  have hc : c.ker = ⊥ := complement_center_kernel_eq_bot r L hsemi hiso hfix hnt J hJ
  let action : MulSemiringAction J F := MulSemiringAction.compHom F c
  letI : MulSemiringAction J F := action
  letI : MulAction J F := action.toDistribMulAction.toMulAction
  letI : SMul J F := action.toDistribMulAction.toMulAction.toSMul
  letI : FaithfulSMul J F := by
    constructor
    intro g h he
    apply (MonoidHom.ker_eq_bot_iff.mp hc)
    apply AlgEquiv.ext
    change ∀ x : F, c g x = c h x at he
    exact he
  let K : Type _ := FixedPoints.subfield J F
  letI : IsGaloisGroup J K F := inferInstance
  letI : FiniteDimensional K F := IsGaloisGroup.finiteDimensional J K F
  letI : IsGalois K F := IsGaloisGroup.isGalois J K F
  let e : J ≃* Gal(F/K) := FixedPoints.toAlgAutMulEquiv J F
  let tau : Gal(F/K) →* Module.End D M := (t.comp J.subtype).comp e.symm.toMonoidHom
  let a : F →+* Module.End D M := centerDAction r L t ht
  have cov (g : Gal(F/K)) (z : F) : tau g * a z = a (g z) * tau g := by
    obtain ⟨j, rfl⟩ := e.surjective g
    change t (j : G) * a z = a ((e j) z) * t (j : G)
    exact center_covariance r L t ht (j : G) z
  let E := FrobeniusOriginalD.RegularAction.regularEquiv a tau cov
  rw [Nat.card_congr e.toEquiv]
  exact ⟨Module.finrank D (FrobeniusOriginalD.RegularAction.fixed tau), by
    rw [E.finrank_eq, Module.finrank_pi_fintype]
    simp [Nat.card_eq_fintype_card]⟩

end ActualCenter

private theorem isotypic_of_semilinear
    {R S : Type*} [Ring R] [Ring S]
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module S Y]
    (alpha : R ≃+* S) (e : X ≃ₛₗ[alpha.toRingHom] Y) (h : IsIsotypic S Y) :
    IsIsotypic R X := by
  letI := RingHomInvPair.of_ringEquiv alpha
  letI := RingHomInvPair.of_ringEquiv_symm alpha
  intro A hA B hB
  let eA := e.submoduleMap A
  let eB := e.submoduleMap B
  letI : IsSimpleModule S (A.map e.toLinearMap) :=
    (eA.toLinearMap.isSimpleModule_iff_of_bijective eA.bijective).mp hA
  letI : IsSimpleModule S (B.map e.toLinearMap) :=
    (eB.toLinearMap.isSimpleModule_iff_of_bijective eB.bijective).mp hB
  obtain ⟨i⟩ := h (A.map e.toLinearMap) (B.map e.toLinearMap)
  exact ⟨(eB.trans i).trans eA.symm⟩

section Component
variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
  [FiniteDimensional k V] [ρ.IsIrreducible]
  (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ)

private abbrev P := isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
  σ.asSubmodule

private abbrev U := originalDBaseComponent ρ σ hσ
private abbrev H := originalDActualInertia ρ σ hσ

private instance componentKModule : Module k (U ρ σ hσ) :=
  inferInstanceAs (Module k (P ρ σ))

private instance componentKFinite : Module.Finite k (U ρ σ hσ) :=
  Module.Finite.of_injective ((P ρ σ).subtype.restrictScalars k) Subtype.val_injective


private theorem le_inertia : N ≤ H ρ σ hσ := by
  intro n hn
  change (U ρ σ hσ).map (originalDTranslate ρ n).toLinearMap = U ρ σ hσ
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hm := (P ρ σ).smul_mem (MonoidAlgebra.of k N ⟨n, hn⟩) hx
    simpa only [MonoidAlgebra.of_apply, Representation.single_smul, one_smul,
      MonoidHom.comp_apply, Representation.asModuleEquiv, LinearEquiv.refl_apply] using hm
  · intro x hx
    refine ⟨ρ n⁻¹ x, ?_, ?_⟩
    · have hm := (P ρ σ).smul_mem (MonoidAlgebra.of k N ⟨n⁻¹, N.inv_mem hn⟩) hx
      simpa only [MonoidAlgebra.of_apply, Representation.single_smul, one_smul,
        MonoidHom.comp_apply, Representation.asModuleEquiv, LinearEquiv.refl_apply] using hm
    · exact Representation.self_inv_apply ρ n x

private theorem action_mem (h : H ρ σ hσ) (u : U ρ σ hσ) :
    ρ (h : G) (u : Representation.asModule (ρ.comp N.subtype)) ∈ U ρ σ hσ := by
  have hh := h.property
  change (U ρ σ hσ).map (originalDTranslate ρ (h : G)).toLinearMap = U ρ σ hσ at hh
  change originalDTranslate ρ (h : G) (u : Representation.asModule (ρ.comp N.subtype)) ∈ _
  have hm := Submodule.mem_map_of_mem (f := (originalDTranslate ρ (h : G)).toLinearMap) u.property
  exact (congrArg (fun Q : Submodule (Module.End k[G] ρ.asModule)
      (Representation.asModule (ρ.comp N.subtype)) =>
        originalDTranslate ρ (h : G) u.val ∈ Q) hh).mp hm

private def componentAction : H ρ σ hσ →* (U ρ σ hσ ≃ₗ[k] U ρ σ hσ) where
  toFun h := {
    toFun u := ⟨ρ (h : G) u.val, action_mem ρ σ hσ h u⟩
    invFun u := ⟨ρ ((h⁻¹ : H ρ σ hσ) : G) u.val, action_mem ρ σ hσ h⁻¹ u⟩
    left_inv u := Subtype.ext (Representation.inv_self_apply ρ (h : G) u.val)
    right_inv u := Subtype.ext (Representation.self_inv_apply ρ (h : G) u.val)
    map_add' u v := Subtype.ext ((ρ (h : G)).map_add u.val v.val)
    map_smul' c u := Subtype.ext ((ρ (h : G)).map_smul c u.val) }
  map_one' := by
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    change ρ 1 u.val = u.val
    simp
  map_mul' h g := by
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    change ρ ((h : G) * (g : G)) u.val = ρ (h : G) (ρ (g : G) u.val)
    rw [map_mul]
    rfl

private def componentDAction : H ρ σ hσ →* Module.End (Module.End k[G] ρ.asModule) (U ρ σ hσ) where
  toFun h := {
    toFun := componentAction ρ σ hσ h
    map_add' := (componentAction ρ σ hσ h).map_add
    map_smul' d u := Subtype.ext ((originalDTranslate ρ (h : G)).map_smul d (u : Representation.asModule (ρ.comp N.subtype))) }
  map_one' := by
    apply LinearMap.ext
    intro u
    exact LinearEquiv.congr_fun (map_one (componentAction ρ σ hσ)) u
  map_mul' h g := by
    apply LinearMap.ext
    intro u
    exact LinearEquiv.congr_fun (map_mul (componentAction ρ σ hσ) h g) u

private def componentRestrictionEquiv :
    letI := NormalizerImageAction.actualModule (componentAction ρ σ hσ)
      (N.subgroupOf (H ρ σ hσ))
    (U ρ σ hσ) ≃ₛₗ[(MonoidAlgebra.domCongr k k
      (Subgroup.subgroupOfEquivOfLe (le_inertia ρ σ hσ))).toRingEquiv.toRingHom] (P ρ σ) := by
  letI := NormalizerImageAction.actualModule (componentAction ρ σ hσ)
    (N.subgroupOf (H ρ σ hσ))
  refine { toFun := fun u => u
           invFun := fun u => u
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro b u
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp only [zero_smul, map_zero]; rfl
  | add b c hb hc => simpa only [map_add, add_smul] using congrArg₂ (· + ·) hb hc
  | single n c =>
    apply Subtype.ext
    change ((NormalizerImageAction.q (componentAction ρ σ hσ)
      (N.subgroupOf (H ρ σ hσ)) (MonoidAlgebra.single n c)) u).val =
      (MonoidAlgebra.domCongr k k
        (Subgroup.subgroupOfEquivOfLe (le_inertia ρ σ hσ))
          (MonoidAlgebra.single n c)) • (u : Representation.asModule (ρ.comp N.subtype))
    rw [NormalizerImageAction.q, Representation.asAlgebraHom_single,
      MonoidAlgebra.domCongr_single, Representation.single_smul]
    rfl

private theorem component_semisimple :
    letI := NormalizerImageAction.actualModule (componentAction ρ σ hσ)
      (N.subgroupOf (H ρ σ hσ))
    IsSemisimpleModule k[N.subgroupOf (H ρ σ hσ)] (U ρ σ hσ) := by
  letI := NormalizerImageAction.actualModule (componentAction ρ σ hσ)
    (N.subgroupOf (H ρ σ hσ))
  letI : IsSimpleModule k[N] σ.asSubmodule :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hσ
  exact ((componentRestrictionEquiv ρ σ hσ).toLinearMap.isSemisimpleModule_iff_of_bijective
    (componentRestrictionEquiv ρ σ hσ).bijective).mpr inferInstance

private theorem component_isotypic :
    letI := NormalizerImageAction.actualModule (componentAction ρ σ hσ)
      (N.subgroupOf (H ρ σ hσ))
    IsIsotypic k[N.subgroupOf (H ρ σ hσ)] (U ρ σ hσ) := by
  letI := NormalizerImageAction.actualModule (componentAction ρ σ hσ)
    (N.subgroupOf (H ρ σ hσ))
  letI : IsSimpleModule k[N] σ.asSubmodule :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hσ
  exact isotypic_of_semilinear
    (MonoidAlgebra.domCongr k k (Subgroup.subgroupOfEquivOfLe (le_inertia ρ σ hσ))).toRingEquiv
    (componentRestrictionEquiv ρ σ hσ)
    (IsIsotypicOfType.isotypicComponent k[N]
      (Representation.asModule (ρ.comp N.subtype)) σ.asSubmodule).isIsotypic

private instance component_nontrivial : Nontrivial (U ρ σ hσ) := by
  letI : IsSimpleModule k[N] σ.asSubmodule :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hσ
  exact Submodule.nontrivial_iff_ne_bot.mpr
    (bot_lt_isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype)) σ.asSubmodule).ne'

private instance componentDFinite : Module.Finite (Module.End k[G] ρ.asModule) (U ρ σ hσ) := by
  let D := Module.End k[G] ρ.asModule
  letI : Module.Finite D ρ.asModule := Module.Finite.of_restrictScalars_finite k D ρ.asModule
  letI : Module.Finite D (Representation.asModule (ρ.comp N.subtype)) := by
    change Module.Finite D ρ.asModule
    infer_instance
  exact Module.Finite.of_injective (U ρ σ hσ).subtype Subtype.val_injective

private instance component_comm : SMulCommClass k (Module.End k[G] ρ.asModule) (U ρ σ hσ) where
  smul_comm c d u := by
    apply Subtype.ext
    change c • d u.val = d (c • u.val)
    have hd := d.map_smul (MonoidAlgebra.single (1 : G) c) u.val
    simpa only [Representation.single_smul, map_one, Module.End.one_apply] using hd.symm

private theorem invariants_bot
    (hnt : ¬ Representation.IsTrivial (ρ.comp N.subtype)) :
    (ρ.comp N.subtype).invariants = ⊥ := by
  let S : Subrepresentation ρ := ⟨(ρ.comp N.subtype).invariants,
    fun g _ hx => Representation.le_comap_invariants ρ N g hx⟩
  have hS : S ≠ ⊤ := by
    intro htop
    apply hnt
    constructor
    intro n
    ext x
    have hx : x ∈ S := by rw [htop]; trivial
    exact hx n
  have hb : S = ⊥ := (eq_bot_or_eq_top S).resolve_right hS
  exact congrArg Subrepresentation.toSubmodule hb

private theorem component_nontrivial_on_N
    (hnt : ¬ Representation.IsTrivial (ρ.comp N.subtype)) :
    ¬ Representation.IsTrivial
      ((NormalizerImageAction.representation (componentAction ρ σ hσ)).comp
        (N.subgroupOf (H ρ σ hσ)).subtype) := by
  intro htriv
  letI := htriv
  have hz (u : U ρ σ hσ) : u = 0 := by
    have hu : (u.val : V) ∈ (ρ.comp N.subtype).invariants := by
      intro n
      let n' : N.subgroupOf (H ρ σ hσ) := ⟨⟨n.val, le_inertia ρ σ hσ n.property⟩, n.property⟩
      have hn := Representation.IsTrivial.out (ρ :=
        (NormalizerImageAction.representation (componentAction ρ σ hσ)).comp
          (N.subgroupOf (H ρ σ hσ)).subtype) n'
      exact congrArg (fun v : U ρ σ hσ => (v.val : V)) (LinearMap.congr_fun hn u)
    rw [invariants_bot ρ hnt] at hu
    exact Subtype.ext hu
  obtain ⟨u, hu⟩ := exists_ne (0 : U ρ σ hσ)
  exact hu (hz u)

end Component


/-- Frobenius divisibility with the original Schur division ring acting by evaluation.
The coefficient field, group and carrier have independent universes. -/
theorem index_dvd_originalD_finrank
    [Finite G] {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
    (N : Subgroup G) [N.Normal] (ρ : Representation k G V)
    [FiniteDimensional k V] [ρ.IsIrreducible]
    (hfix : ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial (ρ.comp N.subtype)) :
    N.index ∣ Module.finrank (Module.End k[G] ρ.asModule) ρ.asModule := by
  classical
  letI : Nontrivial V :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial inferInstance
  obtain ⟨σ, hσ⟩ := exists_isAtom (ρ.comp N.subtype)
  let H := originalDActualInertia ρ σ hσ
  let L := N.subgroupOf H
  have hNH : N ≤ H := le_inertia ρ σ hσ
  obtain ⟨C, hC⟩ := exists_complement N hfix
  let J := C.subgroupOf H
  have hJ : L.IsComplement' J := restrict_complement N C H hNH hC
  have hfixH : ∀ h : H, h ∉ L → ∀ n : L, MulAut.conjNormal h n = n → n = 1 := by
    intro h hh n hn
    let n₀ : N := ⟨((n : H) : G), n.property⟩
    have hn₀ : MulAut.conjNormal (h : G) n₀ = n₀ := by
      apply Subtype.ext
      exact congrArg (fun z : L => ((z : H) : G)) hn
    have hone := hfix (h : G) hh n₀ hn₀
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val hone))
  have hrank : L.index ∣ Module.finrank (Module.End k[G] ρ.asModule)
      (originalDBaseComponent ρ σ hσ) := by
    rw [hJ.symm.index_eq_card]
    exact actual_complement_rank (componentAction ρ σ hσ) L
      (componentDAction ρ σ hσ) (fun _ _ => rfl)
      (component_semisimple ρ σ hσ) (component_isotypic ρ σ hσ) hfixH
      (component_nontrivial_on_N ρ σ hσ hnt) J hJ
  rw [originalD_finrank_independent_universes ρ σ hσ,
    ← N.relIndex_mul_index hNH, Nat.mul_comm (N.relIndex H) H.index]
  exact Nat.mul_dvd_mul_left H.index hrank

set_option pp.universes true in
#check @index_dvd_originalD_finrank
#print axioms index_dvd_originalD_finrank

end D5.S3.FiniteGroups.OriginalDFrobenius
