/- GID: D5/S3/ConceptDynamics/Coding/ResetHistoryKernel
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetHistoryKernel
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Faithful finite alternating actions in the original Reset representation kernel. -/

import D5.S3.ConceptDynamics.Coding.MarkerPermutationAction
import D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetHistoryKernel

open Polynomial
open ResetNumberedHistories ResetStandardBeamGeometry
open ResetFullStandardBeamRepresentation ResetNativeIntegerChart ResetSignIntegerCyclic
open StandardBeamHomeomorphisms

private local instance originalNativeIntModule (q : ℕ) : Module ℤ (Native q) :=
  AddCommGroup.toIntModule _

private theorem rho_time (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (x : Native q) :
    rho q hq h (resetTheta q x) = resetTheta q (rho q hq h x) := by
  have hc : h * unitShift (ResetGraph q) = unitShift (ResetGraph q) * h := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro y
    exact h.property y
  have he := congrArg (rho q hq) hc
  rw [map_mul, map_mul] at he
  have hx := congrArg (fun f : Native q ≃ₗ[ℤ] Native q => f x) he
  have ht (y : Native q) : rho q hq (unitShift (ResetGraph q)) y = resetTheta q y :=
    LinearMap.congr_fun (rho_unitShift q hq) y
  simpa only [LinearEquiv.mul_apply, ht] using hx

private def chartMap (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) :
    QF q →ₗ[ℤ[X]] QF q :=
  (LinearMap.ofAEval (resetTheta q)
    ((nativeIntEquiv q hq).symm.toLinearMap.comp (rho q hq h).toLinearMap) (by
      intro x
      change (nativeIntEquiv q hq).symm (rho q hq h (resetTheta q x)) =
        (X : ℤ[X]) • (nativeIntEquiv q hq).symm (rho q hq h x)
      rw [rho_time]
      apply (nativeIntEquiv q hq).injective
      rw [LinearEquiv.apply_symm_apply]
      change _ = nativeIntEquiv q hq (fp q X * _)
      rw [(native_presentation q hq).2.1, LinearEquiv.apply_symm_apply])).comp
    (nativePolynomialEquiv q hq).toLinearMap

private theorem chartMap_apply (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (b : QF q) :
    chartMap q hq h b = (nativeIntEquiv q hq).symm
      (rho q hq h (nativeIntEquiv q hq b)) := rfl

private theorem chartMap_scalar (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (b : QF q) :
    chartMap q hq h b = b * chartMap q hq h 1 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hs := (chartMap q hq h).map_smul p 1
  change chartMap q hq h (fp q p * 1) = fp q p * chartMap q hq h 1 at hs
  simpa only [fp, mul_one] using hs

private theorem rho_commute (q : ℕ) (hq : 0 < q) (h g : ResetFullAut q) :
    Commute (rho q hq h) (rho q hq g) := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨b, rfl⟩ := (nativeIntEquiv q hq).surjective x
  apply (nativeIntEquiv q hq).symm.injective
  change (nativeIntEquiv q hq).symm
      (rho q hq h (rho q hq g (nativeIntEquiv q hq b))) =
    (nativeIntEquiv q hq).symm
      (rho q hq g (rho q hq h (nativeIntEquiv q hq b)))
  have he (h g : ResetFullAut q) :
      (nativeIntEquiv q hq).symm
        (rho q hq h (rho q hq g (nativeIntEquiv q hq b))) =
        chartMap q hq h (chartMap q hq g b) := by
    simp only [chartMap_apply, LinearEquiv.apply_symm_apply]
  rw [he h g, he g h,
    chartMap_scalar q hq h (chartMap q hq g b),
    chartMap_scalar q hq g (chartMap q hq h b),
    chartMap_scalar q hq g b, chartMap_scalar q hq h b]
  ring

private theorem alternating_killed {I H : Type} [Fintype I] [DecidableEq I] [Group H]
    (f : Equiv.Perm I →* H) (hc : ∀ a b, Commute (f a) (f b)) :
    alternatingGroup I ≤ f.ker := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro g hg
  have hs : Equiv.Perm.IsThreeCycle (g ^ 2) := by
    simpa [pow_two] using hg.isThreeCycle_sq
  have hconj := Equiv.Perm.isConj_of_cycleType_eq (hg.cycleType.trans hs.cycleType.symm)
  obtain ⟨a, b, hab⟩ := mem_commutatorSet_iff.mp
    (mem_commutatorSet_of_isConj_sq (Equiv.Perm I) hconj)
  change f g = 1
  rw [← hab, map_commutatorElement]
  exact (hc a b).commutator_eq

private def dataIndex (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin k → Bool) = 2 ^ k)).symm

/-- Reindex the actual faithful Boolean-word action by the prescribed finite cardinal. -/
def symmetricAction (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    Equiv.Perm (Fin (2 ^ k)) →* ResetFullAut q :=
  (MarkerPermutationAction.resetAction (by omega : 1 < q) (by omega : 0 < k)).comp
    (dataIndex k).permCongrHom.toMonoidHom

private theorem symmetricAction_injective (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    Function.Injective (symmetricAction q k hq hk) :=
  (MarkerPermutationAction.resetAction_injective (by omega : 1 < q) (by omega : 0 < k)).comp
    (dataIndex k).permCongrHom.injective

/-- A4 is included: three-cycles are commutators in Sym, without assuming Alt perfect. -/
def alternatingKernelEmbedding (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) (hq0 : 0 < q) :
    alternatingGroup (Fin (2 ^ k)) →* (rho q hq0).ker := by
  let phi := symmetricAction q k hq hk
  let f := (rho q hq0).comp phi
  have ha : alternatingGroup (Fin (2 ^ k)) ≤ f.ker :=
    alternating_killed f (fun a b => rho_commute q hq0 (phi a) (phi b))
  exact (phi.comp (alternatingGroup (Fin (2 ^ k))).subtype).codRestrict
    (rho q hq0).ker (fun a => ha a.property)

/-- Uniform injectivity into the ORIGINAL representation kernel on the ORIGINAL histories. -/
theorem alternatingKernelEmbedding_injective (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hq0 : 0 < q) : Function.Injective (alternatingKernelEmbedding q k hq hk hq0) := by
  intro a b he
  apply Subtype.ext
  apply symmetricAction_injective q k hq hk
  exact congrArg Subtype.val he

end D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
