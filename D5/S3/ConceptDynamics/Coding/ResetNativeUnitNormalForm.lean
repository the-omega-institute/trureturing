/- GID: D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Unique signed time normal forms on the original native group and full history representation. -/
import D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
import D5.S3.ConceptDynamics.Coding.ResetHistoryKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open Polynomial ResetSignIntegerCyclic ResetIntegralGluing ResetIntegralUnits
open ResetNativeIntegerChart ResetNumberedHistories ResetNativeIntegralDefect
open ResetStandardBeamGeometry ResetFullStandardBeamRepresentation StandardBeamHomeomorphisms
open ResetHistoryKernel

local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _

/-- An integer-linear chart; the original dimension group acquires no ring structure. -/
def nativeGluing (q : ℕ) (hq : 0 < q) : Native q ≃ₗ[ℤ] Compatible q :=
  (nativeIntEquiv q hq).symm.trans (gluing q).toAddEquiv.toIntLinearEquiv

/-- Literal forward time, sign, scalar and inverse-transition stage orientation. -/
theorem native_gluing (q : ℕ) (hq : 0 < q) :
    (∀ z : QF q, nativeGluing q hq (nativeIntEquiv q hq z) = gluing q z) ∧
    (∀ v : Native q, nativeGluing q hq (resetTheta q v) =
      gluing q (fp q X) * nativeGluing q hq v) ∧
    (∀ v : Native q, nativeGluing q hq
      (InertGroupBlockConjugacy.groupAction (resetMatrix q) (Multiplicative.ofAdd true) v) =
      gluing q (fp q (W q)) * nativeGluing q hq v) ∧
    (∀ z : ℤ, ∀ v : Native q, nativeGluing q hq (z • v) = z • nativeGluing q hq v) ∧
    (∀ n : ℕ, ∀ v : InertGroupBlockConjugacy.VertexModule Sign q,
      nativeGluing q hq (ResetNativeIntegerChart.nativeStage q n v) =
        gluing q (ringEquiv q (pp q
          (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
            ((resetInverse q hq ^ n) v))))) := by
  obtain ⟨hone,hX,hPoly,hScalar,hPol,hStage,hAction,hLabel⟩ := native_presentation q hq
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro z
    change gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq z)) = _
    rw [LinearEquiv.symm_apply_apply]
  · intro v
    obtain ⟨b,rfl⟩ := (nativeIntEquiv q hq).surjective v
    rw [← hX]
    change gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq (fp q X * b))) =
      gluing q (fp q X) * gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq b))
    simp only [LinearEquiv.symm_apply_apply, map_mul]
  · intro v
    obtain ⟨b,rfl⟩ := (nativeIntEquiv q hq).surjective v
    rw [hLabel, ← hPoly]
    change gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq (fp q (W q) * b))) =
      gluing q (fp q (W q)) * gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq b))
    simp only [LinearEquiv.symm_apply_apply, map_mul]
  · exact fun z v => (nativeGluing q hq).map_smul z v
  · intro n v
    change gluing q ((nativeIntEquiv q hq).symm (ResetNativeIntegerChart.nativeStage q n v)) = _
    rw [hStage]

private theorem inverse_time (q : ℕ) (A : Native q ≃ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) :
    ∀ x, A.symm (resetTheta q x) = resetTheta q (A.symm x) := by
  intro x
  apply A.injective
  rw [LinearEquiv.apply_symm_apply, ht, LinearEquiv.apply_symm_apply]

/-- The scalar and its inverse are obtained from the actual automorphism and its inverse. -/
def scalarUnit (q : ℕ) (hq : 0 < q) (A : Native q ≃ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) : (QF q)ˣ := by
  let B := centralizingMap q hq A.toLinearMap ht
  let C := centralizingMap q hq A.symm.toLinearMap (inverse_time q A ht)
  have hc : C 1 * B 1 = 1 := by
    rw [← centralizingMap_scalar q hq A.toLinearMap ht (C 1)]
    change (nativeIntEquiv q hq).symm
      (A (nativeIntEquiv q hq ((nativeIntEquiv q hq).symm
        (A.symm (nativeIntEquiv q hq 1))))) = 1
    simp
  exact ⟨B 1, C 1, (mul_comm _ _).trans hc, hc⟩

/-- Units act by integer-linear conjugation through the original native chart. -/
def nativeAction (q : ℕ) (hq : 0 < q) : (QF q)ˣ →* (Native q ≃ₗ[ℤ] Native q) where
  toFun u := (nativeIntEquiv q hq).symm.trans
    ((u.mulLeftLinearEquiv ℤ (QF q)).trans (nativeIntEquiv q hq))
  map_one' := by ext v; simp
  map_mul' u w := by ext v; simp [mul_assoc]

private theorem nativeAction_apply (q : ℕ) (hq : 0 < q) (u : (QF q)ˣ) (v : Native q) :
    nativeAction q hq u v =
      nativeIntEquiv q hq ((u : QF q) * (nativeIntEquiv q hq).symm v) := rfl

private theorem nativeAction_injective (q : ℕ) (hq : 0 < q) :
    Function.Injective (nativeAction q hq) := by
  intro u v h
  apply Units.ext
  have he := congrArg (fun A : Native q ≃ₗ[ℤ] Native q =>
    (nativeIntEquiv q hq).symm (A (nativeIntEquiv q hq 1))) h
  simpa only [nativeAction_apply, LinearEquiv.symm_apply_apply, mul_one] using he

private theorem scalarUnit_action (q : ℕ) (hq : 0 < q) (A : Native q ≃ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) :
    nativeAction q hq (scalarUnit q hq A ht) = A := by
  ext v
  obtain ⟨b,rfl⟩ := (nativeIntEquiv q hq).surjective v
  apply (nativeIntEquiv q hq).symm.injective
  rw [nativeAction_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hs := centralizingMap_scalar q hq A.toLinearMap ht b
  exact (mul_comm _ _).trans hs.symm

abbrev N := Native 2
/-- The actual image of the original unit shift, including its inverse powers. -/
def T : N ≃ₗ[ℤ] N := rho 2 (by omega) (unitShift (ResetGraph 2))
/-- The actual original Sign action, kept as an integer-linear endomorphism. -/
def U : Module.End ℤ N :=
  InertGroupBlockConjugacy.groupAction (resetMatrix 2) (Multiplicative.ofAdd true)

private theorem nativeAction_x : nativeAction 2 (by omega) xUnit = T := by
  ext v
  apply (nativeGluing 2 (by omega)).injective
  rw [nativeAction_apply, (native_gluing 2 (by omega)).1]
  have ht : T v = resetTheta 2 v := LinearMap.congr_fun (rho_unitShift 2 (by omega)) v
  rw [ht, (native_gluing 2 (by omega)).2.1]
  simp only [map_mul]
  rfl

private theorem nativeAction_w (v : N) : nativeAction 2 (by omega) wUnit v = U v := by
  apply (nativeGluing 2 (by omega)).injective
  rw [nativeAction_apply, (native_gluing 2 (by omega)).1]
  change _ = nativeGluing 2 (by omega)
    (InertGroupBlockConjugacy.groupAction (resetMatrix 2) (Multiplicative.ofAdd true) v)
  rw [(native_gluing 2 (by omega)).2.2.1]
  simp only [map_mul]
  rfl

private theorem nativeAction_neg (v : N) : nativeAction 2 (by omega) (-1) v = -v := by
  rw [nativeAction_apply]
  simp

private theorem normal_action (n : ℤ) (a b : Fin 2) (v : N) :
    nativeAction 2 (by omega) (normal n a b) v =
      ((-1 : ℤ) ^ a.val) • ((U ^ b.val) ((T ^ n) v)) := by
  simp only [normal, map_mul, map_pow, map_zpow, nativeAction_x,
    LinearEquiv.mul_apply]
  fin_cases a <;> fin_cases b <;>
    simp [LinearEquiv.mul_apply, nativeAction_w, nativeAction_neg]

private theorem centralizer_form (A : N ≃ₗ[ℤ] N)
    (ht : ∀ v, A (resetTheta 2 v) = resetTheta 2 (A v)) :
    ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
      A v = ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v)) := by
  let u := scalarUnit 2 (by omega) A ht
  obtain ⟨p,hp,huniq⟩ := unit_normal_form u
  have hu : nativeAction 2 (by omega) u = A := scalarUnit_action 2 (by omega) A ht
  refine ⟨p,?_,?_⟩
  · intro v
    rw [← hu, hp, normal_action]
  · intro r hr
    apply huniq
    apply nativeAction_injective 2 (by omega)
    rw [hu]
    ext v
    rw [normal_action]
    exact hr v

/-- All native centralizing automorphisms and every value of the original full-history action. -/
theorem native_normal_forms :
    (∀ A : N ≃ₗ[ℤ] N, (∀ v, A (resetTheta 2 v) = resetTheta 2 (A v)) →
      ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
        A v = ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v))) ∧
    (∀ h : ResetFullAut 2, ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
      rho 2 (by omega) h v =
        ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v))) := by
  exact ⟨centralizer_form, fun h => centralizer_form (rho 2 (by omega) h)
    (rho_time 2 (by omega) h)⟩

end D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
