/- GID: D5/S3/Factorization/Dedekind/TameDifferent
   generality: G
   mirror-B: D5/B/S3/Factorization/Dedekind/TameDifferent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-power quotient traces and Dedekind different divisibility detect tame ramification. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026tamedifferent.md.
Authors: The Tau Ceti contributors

-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open Module LinearMap Ideal
open scoped nonZeroDivisors

namespace D5.S3.Factorization.Dedekind.TameDifferent

section QuotientTrace
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain B]
variable {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal]
attribute [local instance] Ideal.Quotient.field

theorem prime_power_quotient_trace [Module.Finite A B] (hP : P ≠ ⊥) (n : ℕ)
    [instA : Algebra (A ⧸ p) (B ⧸ P ^ n)] [instT : IsScalarTower A (A ⧸ p) (B ⧸ P ^ n)]
    [Algebra (A ⧸ p) (B ⧸ P)] [IsScalarTower A (A ⧸ p) (B ⧸ P)] (z : B) :
    Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ z) =
      n • Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ z) := by
  induction n generalizing instA instT with
  | zero =>
      have hz : z ∈ P ^ 0 := by simp
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
  | succ n ih =>
      have : Nontrivial (B ⧸ P ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.pow_le_self n.succ_ne_zero)
      have hcomap : p ≤ Ideal.comap (algebraMap A B) (P ^ n) :=
        (Ideal.comap_eq_of_scalar_tower_quotient (algebraMap (A ⧸ p) _).injective).ge.trans
          (Ideal.comap_mono (Ideal.pow_le_pow_right n.le_succ))
      let _ : Algebra (A ⧸ p) (B ⧸ P ^ n) := Ideal.Quotient.algebraQuotientOfLEComap hcomap
      have _ : IsScalarTower A (A ⧸ p) (B ⧸ P ^ n) := .of_algebraMap_eq fun x ↦ by
        rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.algebraMap_eq]
        exact Ideal.quotientMap_mk.symm
      have hstep :
          Algebra.trace (A ⧸ p) (B ⧸ P ^ (n + 1)) (Ideal.Quotient.mk _ z) =
            Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ z) +
              Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ z) := by
        have := Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ (n + 1))
        obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP Ideal.IsPrime.ne_top' n
        have hsurj : Function.Surjective (algebraMap A (A ⧸ p)) :=
          Ideal.Quotient.algebraMap_eq p ▸ Ideal.Quotient.mk_surjective
        have hcompat : P ≤ Submodule.comap (LinearMap.mulLeft B a) (P ^ (n + 1)) := by
          intro x hx
          rw [Submodule.mem_comap, LinearMap.mulLeft_apply, pow_succ]
          exact mul_mem_mul ha hx
        let g := Submodule.mapQ P (P ^ (n + 1)) (LinearMap.mulLeft B a) hcompat
        let π := Submodule.factor (Ideal.pow_le_pow_right (I := P) (n.le_add_right 1))
        let i := (g.restrictScalars A).extendScalarsOfSurjective hsurj
        let pi := (π.restrictScalars A).extendScalarsOfSurjective hsurj
        have hi : ⇑i = g := funext fun _ ↦ by
          rw [LinearMap.extendScalarsOfSurjective_apply, LinearMap.restrictScalars_apply]
        have hpi : ⇑pi = π := funext fun _ ↦ by
          rw [LinearMap.extendScalarsOfSurjective_apply, LinearMap.restrictScalars_apply]
        have hinj : Function.Injective i := by
          rw [hi]
          refine (injective_iff_map_eq_zero g).2 fun y hy ↦ ?_
          obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
          change Ideal.Quotient.mk (P ^ (n + 1)) (a * x) = 0 at hy
          rw [Ideal.Quotient.eq_zero_iff_mem] at hy
          exact (Submodule.Quotient.mk_eq_zero _).2
            ((Ideal.IsMaximal.mem_pow_mul P hy).resolve_left ha')
        have hpisurj : Function.Surjective pi := by
          rw [hpi]
          exact Submodule.factor_surjective _
        have hex : Function.Exact i pi := by
          rw [hi, hpi]
          intro y
          obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
          simp only [g, π, Submodule.mapQ_apply, LinearMap.id_apply,
            Submodule.Quotient.mk_eq_zero, Set.mem_range,
            (Submodule.Quotient.mk_surjective _).exists, LinearMap.mulLeft_apply,
            Submodule.Quotient.eq]
          constructor
          · intro hu
            obtain ⟨x, w, hw, rfl⟩ := Ideal.exists_mul_add_mem_pow_succ hP a u ha ha' hu
            exact ⟨x, by rwa [sub_add_cancel_left, neg_mem_iff]⟩
          · rintro ⟨x, hx⟩
            exact (Submodule.sub_mem_iff_right _ (mul_mem_right x _ ha)).1
              (pow_le_pow_right n.le_succ hx)
        let f := Algebra.lmul (A ⧸ p) (B ⧸ P ^ (n + 1)) (Ideal.Quotient.mk _ z)
        let fN := Algebra.lmul (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ z)
        let fQ := Algebra.lmul (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ z)
        have hN : f ∘ₗ i = i ∘ₗ fN := by
          simp only [f, fN, LinearMap.ext_iff, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul,
            LinearMap.mul_apply', hi, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def,
            map_smul, implies_true]
        have hQ : pi ∘ₗ f = fQ ∘ₗ pi := by
          simp only [f, fQ, LinearMap.ext_iff, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul,
            LinearMap.mul_apply', hpi, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def,
            map_smul, implies_true]
        have _ : FiniteDimensional (A ⧸ p) (B ⧸ P) := FiniteDimensional.of_injective i hinj
        have _ : FiniteDimensional (A ⧸ p) (B ⧸ P ^ n) := Module.Finite.of_surjective pi hpisurj
        letI : Module.Free (A ⧸ p) (B ⧸ P) := Module.Free.of_divisionRing _ _
        letI : Module.Free (A ⧸ p) (B ⧸ P ^ n) := Module.Free.of_divisionRing _ _
        obtain ⟨s, hs⟩ := pi.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hpisurj)
        obtain ⟨E, hiE, hπE⟩ := hex.splitSurjectiveEquiv hinj ⟨s, hs⟩
        have hi_apply (x : B ⧸ P) : E.symm (x, 0) = i x := by
          simpa using congr($hiE x).symm
        set F : ((B ⧸ P) × (B ⧸ P ^ n)) →ₗ[A ⧸ p] (B ⧸ P) × (B ⧸ P ^ n) :=
          E.conj f with hF
        have hFapply (x : (B ⧸ P) × (B ⧸ P ^ n)) : F x = E (f (E.symm x)) := by
          simp [hF, LinearEquiv.conj_apply]
        have hsnd (x : B ⧸ P ^ (n + 1)) : (E x).2 = pi x := by
          simpa using congr($hπE x).symm
        have hinl : F ∘ₗ (inl (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) =
            (inl (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) ∘ₗ fN := by
          refine LinearMap.ext fun x ↦ E.symm.injective ?_
          have hfi : f (i x) = i (fN x) := congr($hN x)
          simp only [comp_apply, inl_apply, hFapply, E.symm_apply_apply, hi_apply]
          exact hfi
        have hsnd' : (snd (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) ∘ₗ F =
            fQ ∘ₗ (snd (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) := by
          refine LinearMap.ext fun x ↦ ?_
          have h₃ : pi (f (E.symm x)) = fQ (pi (E.symm x)) := congr($hQ (E.symm x))
          simp only [comp_apply, snd_apply, hFapply, hsnd, h₃]
          rw [← hsnd (E.symm x), E.apply_symm_apply]
        let u := (fst (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) ∘ₗ F ∘ₗ
          (inr (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n))
        have hshape : F = prodMap fN fQ + (inl (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) ∘ₗ
            u ∘ₗ (snd (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) := by
          refine LinearMap.prod_ext ?_ ?_
          · rw [hinl]
            refine LinearMap.ext fun x ↦ ?_
            simp [Prod.mk_zero_zero]
          · refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
            · simp [u]
            · simpa using LinearMap.congr_fun hsnd' ((inr (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) x)
        have hoff : LinearMap.trace (A ⧸ p) ((B ⧸ P) × (B ⧸ P ^ n))
            ((inl (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) ∘ₗ
              u ∘ₗ (snd (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n))) = 0 := by
          rw [LinearMap.trace_comp_comm']
          have hz : (u ∘ₗ (snd (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n))) ∘ₗ
              (inl (A ⧸ p) (B ⧸ P) (B ⧸ P ^ n)) = 0 := by
            apply LinearMap.ext
            intro x
            simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply,
              map_zero, LinearMap.zero_apply]
          rw [hz, map_zero]
        change LinearMap.trace (A ⧸ p) (B ⧸ P ^ (n + 1)) f =
          LinearMap.trace (A ⧸ p) (B ⧸ P) fN + LinearMap.trace (A ⧸ p) (B ⧸ P ^ n) fQ
        rw [← LinearMap.trace_conj' f E, ← hF, hshape, map_add,
          LinearMap.trace_prodMap', hoff, add_zero]
      rw [hstep, ih, succ_nsmul']

end QuotientTrace

section Different
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance] Ideal.Quotient.field
variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

theorem prime_power_divides_different_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p] {e : ℕ}
    (hPQ : IsCoprime (P ^ e) Q) (hmul : P ^ e * Q = Ideal.map (algebraMap A B) p) :
    P ^ e ∣ differentIdeal A B ↔ ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) ∨ (e : A ⧸ p) = 0 := by
  have traceCriterion
      {p : Ideal A} (hp : p ≠ ⊥) (I Q : Ideal B) (hIQ : I * Q = Ideal.map (algebraMap A B) p) :
      I ∣ differentIdeal A B ↔ ∀ x ∈ Q, Algebra.intTrace A B x ∈ p := by
    refine ⟨fun hdvd x hx ↦ ?_, fun htr ↦ ?_⟩
    · by_contra hx'
      exact not_dvd_differentIdeal_of_intTrace_not_mem A I Q hIQ x hx hx' hdvd
    let K := FractionRing A
    let L := FractionRing B
    have hp' : Ideal.map (algebraMap A B) p ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
    have hQ : Q ≠ ⊥ := fun h ↦ hp' (by rw [← hIQ, h, Ideal.mul_bot])
    have hI : I ≠ ⊥ := fun h ↦ hp' (by rw [← hIQ, h, Ideal.bot_mul])
    -- `I⁻¹ = Q / p · B` as fractional ideals of `B`
    have hIinv : ((I : FractionalIdeal B⁰ L))⁻¹ = Q / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [← hIQ, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
      rw [div_self (by simpa), mul_one, inv_inv]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) hI, hIinv,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
      rw [← Algebra.algebraMap_intTrace (A := A)]
      exact ⟨Algebra.intTrace A B z, htr z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hQle : p ≤ Ideal.comap (algebraMap A B) Q := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]; exact Ideal.mul_le_right
  have hPle : p ≤ Ideal.comap (algebraMap A B) (P ^ e) := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]; exact Ideal.mul_le_left
  let instQ : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap hQle
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  let instPe : Algebra (A ⧸ p) (B ⧸ P ^ e) := Ideal.Quotient.algebraQuotientOfLEComap hPle
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ e) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) := .of_restrictScalars_finite A _ _
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ e) := .of_restrictScalars_finite A _ _
  have : Module.Finite (A ⧸ p) (B ⧸ P) := .of_restrictScalars_finite A _ _
  -- the Chinese remainder decomposition of `B ⧸ pB`
  let ee : (B ⧸ Ideal.map (algebraMap A B) p) ≃ₐ[A ⧸ p] ((B ⧸ P ^ e) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hmul.symm).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hPQ)
      commutes' := Quotient.ind fun _ ↦ rfl }
  -- modulo `p`, the integral trace of an element of `Q` is `e` times its residue trace
  have htr (x : B) (hx : x ∈ Q) : Ideal.Quotient.mk p (Algebra.intTrace A B x) =
      e • Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk P x) := by
    have hx₁ : (ee (Ideal.Quotient.mk _ x)).1 = Ideal.Quotient.mk (P ^ e) x := by simp [ee]
    have hx₂ : (ee (Ideal.Quotient.mk _ x)).2 = 0 := by
      simpa [ee, Ideal.Quotient.eq_zero_iff_mem] using hx
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv ee,
      Algebra.trace_prod_apply, hx₁, hx₂, map_zero, add_zero,
      prime_power_quotient_trace hPbot e x]
  rw [traceCriterion hp _ Q hmul]
  refine ⟨fun h ↦ ?_, fun h x hx ↦ ?_⟩
  · by_contra! hc
    obtain ⟨hsep, he⟩ := hc
    have he₀ : e ≠ 0 := by rintro rfl; simp at he
    -- a residue with nonzero trace, lifted to an element of `Q`
    obtain ⟨w, hw⟩ : ∃ w, Algebra.trace (A ⧸ p) (B ⧸ P) w ≠ 0 := by
      simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (ee.symm (Ideal.Quotient.mk _ z, 0))
    have hy' := congrArg ee hy
    rw [AlgEquiv.apply_symm_apply] at hy'
    have hyQ : y ∈ Q := by
      simpa [ee, Ideal.Quotient.eq_zero_iff_mem] using congrArg Prod.snd hy'
    have hyP : Ideal.Quotient.mk P y = Ideal.Quotient.mk P z := by
      have : Ideal.Quotient.mk (P ^ e) y = Ideal.Quotient.mk (P ^ e) z := by
        simpa [ee] using congrArg Prod.fst hy'
      exact Ideal.Quotient.eq.mpr (Ideal.pow_le_self he₀ (Ideal.Quotient.eq.mp this))
    have := htr y hyQ
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (h y hyQ), hyP, nsmul_eq_mul] at this
    exact mul_ne_zero he hw this.symm
  · rw [← Ideal.Quotient.eq_zero_iff_mem, htr x hx]
    rcases h with h | h
    · rw [Algebra.trace_eq_zero_of_not_isSeparable h, LinearMap.zero_apply, smul_zero]
    · rw [nsmul_eq_mul, h, zero_mul]

end Different

end D5.S3.Factorization.Dedekind.TameDifferent
