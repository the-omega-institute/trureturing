/- GID: D5/S3/FiniteGroups/Frobenius/OriginalDFrobenius
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/OriginalDFrobenius
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Frobenius divisibility over the original Schur division ring. -/

import D5.S3.FiniteGroups.Frobenius.OriginalDClifford
import D5.S3.FiniteGroups.Frobenius.NormalizerImageAction
import D5.S3.FiniteGroups.Frobenius.OriginalDRegularAction
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
Retirement: when the Mathlib revision pinned in this repository's lake-manifest.json
provides an equivalent of this namespace's `exists_complement`, replace the
transplanted Hall-coprimality fragment with direct Mathlib reuse and remove unused
transplants. Required scope: any finite group G and normal subgroup N such that
∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1; the conclusion is
∃ C : Subgroup G, N.IsComplement' C, with no properness or nontriviality assumption.
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
private theorem actual_complement_regular [Finite L] [Module.Finite k M] [Nontrivial M]
    [Module.Finite D M]
    (hsemi : letI := actualModule r L; IsSemisimpleModule k[L] M)
    (hiso : letI := actualModule r L; IsIsotypic k[L] M)
    (hfix : ∀ g : G, g ∉ L → ∀ n : L, MulAut.conjNormal g n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial ((representation r).comp L.subtype))
    (J : Subgroup G) [Finite J] (hJ : L.IsComplement' J) :
    ∃ (S : Submodule D M) (E : M ≃ₗ[D] (J → S)),
      ∀ (j : J) (u : M) (g : J), E (t j u) g = E u (j⁻¹ * g) := by
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
    apply (c.ker_eq_bot_iff.mp hc)
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
    simp only [tau, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
    change t (j : G) * a z = a ((e j) z) * t (j : G)
    exact center_covariance r L t ht (j : G) z
  let EG := FrobeniusOriginalD.RegularAction.regularEquiv a tau cov
  let EJ : M ≃ₗ[D] (J → FrobeniusOriginalD.RegularAction.fixed tau) :=
    EG ≪≫ₗ LinearEquiv.piCongrLeft' D
      (fun _ : Gal(F/K) => FrobeniusOriginalD.RegularAction.fixed tau) e.symm.toEquiv
  refine ⟨FrobeniusOriginalD.RegularAction.fixed tau, EJ, ?_⟩
  intro j u g
  change EG (t (j : G) u) (e g) = EG u (e (j⁻¹ * g))
  have htau : tau (e j) = t (j : G) := by simp [tau]
  rw [← htau, FrobeniusOriginalD.RegularAction.regularEquiv_apply_action]
  rw [map_mul, map_inv]

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
  obtain ⟨S, E, _⟩ := actual_complement_regular r L t ht hsemi hiso hfix hnt J hJ
  letI : Fintype J := Fintype.ofFinite J
  exact ⟨Module.finrank D S, by
    rw [E.finrank_eq, Module.finrank_pi_fintype]
    simp [Nat.card_eq_fintype_card]⟩

end ActualCenter

private theorem isotypic_of_semilinear
    {R S : Type*} [Ring R] [Ring S]
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module S Y]
    (alpha : R ≃+* S) (e : X ≃ₛₗ[(alpha : R →+* S)] Y) (h : IsIsotypic S Y) :
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
    simp only [MonoidAlgebra.of_apply, Representation.single_smul, one_smul] at hm
    dsimp [Representation.asModuleEquiv, LinearEquiv.refl] at hm
    exact hm
  · intro x hx
    refine ⟨ρ n⁻¹ x, ?_, ?_⟩
    · have hm := (P ρ σ).smul_mem (MonoidAlgebra.of k N ⟨n⁻¹, N.inv_mem hn⟩) hx
      simp only [MonoidAlgebra.of_apply, Representation.single_smul, one_smul] at hm
      dsimp [Representation.asModuleEquiv, LinearEquiv.refl] at hm
      exact hm
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
    (U ρ σ hσ) ≃ₛₗ[((MonoidAlgebra.domCongr k k
      (Subgroup.subgroupOfEquivOfLe (le_inertia ρ σ hσ))).toRingEquiv :
        k[N.subgroupOf (H ρ σ hσ)] →+* k[N])] (P ρ σ) := by
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
  | zero => simp only [zero_smul, map_zero]
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
  have hp : Nontrivial (P ρ σ) := Submodule.nontrivial_iff_ne_bot.mpr
    (bot_lt_isotypicComponent σ.asSubmodule).ne'
  exact hp

private instance componentDFinite : Module.Finite (Module.End k[G] ρ.asModule) (U ρ σ hσ) := by
  classical
  let D := Module.End k[G] ρ.asModule
  letI : DivisionRing D := inferInstance
  have hfin : Module.Finite D ρ.asModule := Module.Finite.of_restrictScalars_finite k D ρ.asModule
  letI : Module.Finite D (Representation.asModule (ρ.comp N.subtype)) := hfin
  exact Module.Finite.of_injective (U ρ σ hσ).subtype Subtype.val_injective

private instance component_comm : SMulCommClass k (Module.End k[G] ρ.asModule) (U ρ σ hσ) where
  smul_comm c d u := by
    apply Subtype.ext
    change c • d u.val = d (c • u.val)
    have hd := d.map_smul (MonoidAlgebra.single (1 : G) c) u.val
    simp only [Representation.single_smul, map_one, Module.End.one_apply] at hd
    dsimp [Representation.asModuleEquiv, LinearEquiv.refl] at hd
    exact hd.symm

private def globalDAction : G →* Module.End (Module.End k[G] ρ.asModule) ρ.asModule where
  toFun g := (originalDTranslate ρ g).toLinearMap
  map_one' := by
    ext x
    change ρ 1 x = x
    simp
  map_mul' g h := by
    ext x
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul]
    rfl

private theorem component_to_full_regular [Finite G]
    (C : Subgroup G) (hC : N.IsComplement' C)
    (S : Submodule (Module.End k[G] ρ.asModule) (U ρ σ hσ))
    (E : U ρ σ hσ ≃ₗ[Module.End k[G] ρ.asModule]
      (C.subgroupOf (H ρ σ hσ) → S))
    (hE : ∀ (j : C.subgroupOf (H ρ σ hσ)) (u : U ρ σ hσ)
      (g : C.subgroupOf (H ρ σ hσ)),
      E (componentDAction ρ σ hσ j u) g = E u (j⁻¹ * g)) :
    ∃ T : ρ.asModule ≃ₗ[Module.End k[G] ρ.asModule] (C → S),
      ∀ (c : C) (v : ρ.asModule) (x : C),
        T (globalDAction ρ c v) x = T v (c⁻¹ * x) := by
  classical
  let D := Module.End k[G] ρ.asModule
  letI : DivisionRing D := inferInstance
  letI : Module.Finite D ρ.asModule := Module.Finite.of_restrictScalars_finite k D ρ.asModule
  letI : Fintype C := Fintype.ofFinite C
  let J := C.subgroupOf (H ρ σ hσ)
  letI : Fintype J := Fintype.ofFinite J
  let incl : U ρ σ hσ →ₗ[D] ρ.asModule := (U ρ σ hσ).subtype
  let b : S →ₗ[D] U ρ σ hσ := E.symm.toLinearMap.comp (LinearMap.single D (fun _ : J => S) 1)
  let A := globalDAction ρ
  let T : (C → S) →ₗ[D] ρ.asModule := {
    toFun := fun f => ∑ c : C, A (c : G) (incl (b (f c)))
    map_add' := by intro f g; simp [map_add, Finset.sum_add_distrib]
    map_smul' := by intro d f; simp [map_smul, Finset.smul_sum] }
  have hsingle (c : C) (s : S) :
      T (Pi.single c s) = A (c : G) (incl (b s)) := by
    change (∑ x : C, A (x : G) (incl (b ((Pi.single c s : C → S) x)))) = _
    rw [Finset.sum_eq_single c]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne hx]
    · simp
  have hbase (j : J) (s : S) :
      componentDAction ρ σ hσ j (b s) = E.symm (Pi.single j s) := by
    apply E.injective
    rw [E.apply_symm_apply]
    funext x
    rw [hE]
    have hb : E (b s) = (Pi.single (1 : J) s : J → S) := E.apply_symm_apply _
    rw [hb]
    change (Pi.single (1 : J) s : J → S) (j⁻¹ * x) = (Pi.single j s : J → S) x
    by_cases hx : x = j
    · subst x; simp
    · simp [Pi.single_apply, hx, Ne.symm hx, inv_mul_eq_one]
  have hu (u : U ρ σ hσ) :
      u = ∑ j : J, componentDAction ρ σ hσ j (b (E u j)) := by
    simp_rw [hbase]
    have hs : (∑ j : J, Pi.single j (E u j)) = E u := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc
      u = E.symm.toLinearMap (∑ j : J, Pi.single j (E u j)) := by
        rw [hs]; exact (E.symm_apply_apply u).symm
      _ = _ := map_sum E.symm.toLinearMap _ _
  let R := LinearMap.range T
  have hCU (c : C) (u : U ρ σ hσ) : A (c : G) (incl u) ∈ R := by
    rw [hu u, map_sum, map_sum]
    apply R.sum_mem
    intro j _
    let cj : C := c * ⟨((j : H ρ σ hσ) : G), j.property⟩
    have he : A (c : G) (incl (componentDAction ρ σ hσ j (b (E u j)))) =
        T (Pi.single cj (E u j)) := by
      rw [hsingle]
      change A (c : G) (A (((j : H ρ σ hσ) : G)) (incl (b (E u j)))) =
        A ((c : G) * ((j : H ρ σ hσ) : G)) (incl (b (E u j)))
      rw [map_mul]
      rfl
    rw [he]
    exact LinearMap.mem_range_self T _
  have hGU (g : G) (u : U ρ σ hσ) : A g (incl u) ∈ R := by
    obtain ⟨⟨c, n⟩, he, _⟩ := hC.symm.existsUnique g
    rw [← he, map_mul, Module.End.mul_apply]
    let nh : H ρ σ hσ := ⟨n.val, le_inertia ρ σ hσ n.property⟩
    exact hCU c (componentDAction ρ σ hσ nh u)
  have hstable (g : G) (v : ρ.asModule) (hv : v ∈ R) : A g v ∈ R := by
    obtain ⟨f, rfl⟩ := hv
    change A g (∑ c : C, A (c : G) (incl (b (f c)))) ∈ R
    rw [map_sum]
    apply R.sum_mem
    intro c _
    rw [← Module.End.mul_apply, ← map_mul]
    exact hGU (g * (c : G)) (b (f c))
  let Rg : Submodule k[G] ρ.asModule := {
    carrier := R
    zero_mem' := R.zero_mem
    add_mem' := R.add_mem
    smul_mem' := by
      intro a v hv
      change a • v ∈ R
      induction a using MonoidAlgebra.induction_linear with
      | zero => simpa using R.zero_mem
      | add a b ha hb => simpa only [add_smul] using R.add_mem ha hb
      | single g c =>
        have hm := (R.restrictScalars k).smul_mem c (hstable g v hv)
        simp only [Representation.single_smul]
        dsimp [Representation.asModuleEquiv, LinearEquiv.refl]
        exact hm }
  have hRg : Rg ≠ ⊥ := by
    intro hbot
    obtain ⟨u, hu0⟩ := exists_ne (0 : U ρ σ hσ)
    have huR := hGU 1 u
    rw [map_one, Module.End.one_apply] at huR
    have huRg : incl u ∈ Rg := huR
    rw [hbot] at huRg
    exact hu0 (Subtype.ext huRg)
  have htop : Rg = ⊤ := (eq_bot_or_eq_top Rg).resolve_left hRg
  have hsurj : Function.Surjective T := by
    apply LinearMap.range_eq_top.mp
    ext v
    change v ∈ Rg ↔ v ∈ (⊤ : Submodule D ρ.asModule)
    rw [htop]
    simp
  have hdim : Module.finrank D (C → S) = Module.finrank D ρ.asModule := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [originalD_finrank_independent_universes ρ σ hσ, E.finrank_eq,
      Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : Fintype.card C = (H ρ σ hσ).index * Fintype.card J := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        ← hC.symm.index_eq_card,
        ← (restrict_complement N C (H ρ σ hσ) (le_inertia ρ σ hσ) hC).symm.index_eq_card]
      exact (N.relIndex_mul_index (le_inertia ρ σ hσ)).symm.trans (Nat.mul_comm _ _)
    rw [hc]
    simpa only [Nat.cast_id] using (Nat.mul_assoc (H ρ σ hσ).index (Fintype.card J)
      (Module.finrank D S))
  let T' := LinearEquiv.ofBijective T
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  refine ⟨T'.symm, ?_⟩
  intro c v x
  have heq : T (fun x => T'.symm v (c⁻¹ * x)) = A (c : G) (T (T'.symm v)) := by
    change (∑ x : C, A (x : G) (incl (b (T'.symm v (c⁻¹ * x))))) =
      A (c : G) (∑ x : C, A (x : G) (incl (b (T'.symm v x))))
    rw [map_sum]
    simp_rw [← Module.End.mul_apply, ← map_mul]
    symm
    exact Fintype.sum_equiv (Equiv.mulLeft c) _ _ (fun _ => by simp)
  have heq' : T'.symm (A (c : G) v) = fun x => T'.symm v (c⁻¹ * x) := by
    apply T'.injective
    change T (T'.symm (A (c : G) v)) = T (fun x => T'.symm v (c⁻¹ * x))
    rw [heq]
    change T' (T'.symm (A (c : G) v)) = A (c : G) (T' (T'.symm v))
    rw [T'.apply_symm_apply, T'.apply_symm_apply]
  exact congrFun heq' x

private theorem invariants_bot
    (hnt : ¬ Representation.IsTrivial (ρ.comp N.subtype)) :
    (_root_.Representation.invariants (ρ.comp N.subtype)) = ⊥ := by
  let S : Subrepresentation ρ := ⟨(_root_.Representation.invariants (ρ.comp N.subtype)),
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
    have hu : (u.val : V) ∈ (_root_.Representation.invariants (ρ.comp N.subtype)) := by
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
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial (ρ := ρ) inferInstance
  obtain ⟨σ, hσ⟩ :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.exists_isAtom (ρ.comp N.subtype)
  letI : DivisionRing (Module.End k[G] ρ.asModule) := inferInstance
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
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : G)) hone
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

/-- The actual complement acts as a direct sum of its left regular representation,
over the original, possibly noncommutative Schur division ring. -/
theorem exists_complement_originalD_regular
    [Finite G] {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
    (N : Subgroup G) [N.Normal] (ρ : Representation k G V)
    [FiniteDimensional k V] [ρ.IsIrreducible]
    (hfix : ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial (ρ.comp N.subtype)) :
    ∃ C : Subgroup G, N.IsComplement' C ∧
      ∃ (S : Submodule (Module.End k[G] ρ.asModule) ρ.asModule)
        (E : ρ.asModule ≃ₗ[Module.End k[G] ρ.asModule] (C → S)),
        ∀ (c : C) (v : ρ.asModule) (x : C),
          E (originalDTranslate ρ c v) x = E v (c⁻¹ * x) := by
  classical
  letI : Nontrivial V :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial (ρ := ρ) inferInstance
  obtain ⟨σ, hσ⟩ :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.exists_isAtom (ρ.comp N.subtype)
  let D := Module.End k[G] ρ.asModule
  letI : DivisionRing D := inferInstance
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
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : G)) hone
  obtain ⟨S, E, hE⟩ := actual_complement_regular (componentAction ρ σ hσ) L
    (componentDAction ρ σ hσ) (fun _ _ => rfl)
    (component_semisimple ρ σ hσ) (component_isotypic ρ σ hσ) hfixH
    (component_nontrivial_on_N ρ σ hσ hnt) J hJ
  obtain ⟨T, hT⟩ := component_to_full_regular ρ σ hσ C hC S E hE
  let incl : U ρ σ hσ →ₗ[D] ρ.asModule := (U ρ σ hσ).subtype
  let S' := S.map incl
  let eS : S ≃ₗ[D] S' := S.equivMapOfInjective incl Subtype.val_injective
  let T' := T ≪≫ₗ LinearEquiv.piCongrRight (fun _ : C => eS)
  refine ⟨C, hC, S', T', ?_⟩
  intro c v x
  exact congrArg eS (hT c v x)



end D5.S3.FiniteGroups.OriginalDFrobenius
