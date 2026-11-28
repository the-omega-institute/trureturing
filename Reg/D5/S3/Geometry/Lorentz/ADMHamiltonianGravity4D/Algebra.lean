import D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
import Reg.Support.UnitSixO

/-! Typed observations of the metric, the momentum map, and the Hubble rate. -/

open LeanInformationAudit Matrix
open scoped Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
open _root_.D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D (hubble)
open _root_.Reg.Support.UnitSixO (operandSignature)

namespace Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

macro "bindADM% " theoremId:ident groupId:ident ar:term:max fam:term:max
    headId:ident occurrence:num : term => do
  let owner := `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
  let unit := (owner ++ theoremId.getId ++ `__information_unit)
  let familyName :=
    (`Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Algebra ++ groupId.getId ++ `family)
  `({ unitName := $(Lean.quote unit)
      realizationName := $(Lean.quote familyName)
      realizationSource := none
      generated := false
      arena := .source ⟨$ar⟩
      objectArena := .source ⟨$ar⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $ar ⟨$fam⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some (unitObserve% $headId)
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D
        definition := none
        coordinates := #[]
        readouts := #[{
          path := unitPath% $theoremId $headId 0 $occurrence
          stateBinder := 0
          functionOperand := true
          stateOperand := none
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

private abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
private abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
private abbrev Shift := Fin 3 → ℝ
abbrev MetricSignature : Signature := operandSignature ℝ (Shift → Mat3 → Mat4)
def metricActual : Realization MetricSignature := unitObserve% admMetric

private theorem metric_one_det : (admMetric 1 0 1).det = -1 := by
  norm_num [(admMetric_det_and_volume 1 0 1).1]

private theorem metric_one_ne : admMetric 1 0 1 ≠ 0 := by
  intro h
  have hd := metric_one_det
  rw [h] at hd
  norm_num at hd

private theorem metric_dependence :
    ∃ p x y, metricActual.readout () p x ≠ metricActual.readout () p y := by
  refine ⟨(), 0, 1, fun h => ?_⟩
  have hh := congrArg Matrix.det (congrFun (congrFun h 0) 1)
  change (admMetric 0 0 1).det = (admMetric 1 0 1).det at hh
  rw [metric_one_det, (admMetric_det_and_volume 0 0 1).1] at hh
  norm_num at hh

namespace Congruence

abbrev arena : Arena where
  signature := MetricSignature
  Law R := ∀ (N : ℝ) (β : Shift) (γ : Mat3),
    R.readout () () N β γ =
      (admShiftMatrix β)ᵀ *
        (fromBlocks (!![-(N ^ 2)] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 γ).reindex
          finSumFinEquiv finSumFinEquiv * admShiftMatrix β

def family : Registration arena (type_of% (@admMetric_congruence_factorization)) :=
  unitFamily% arena (@admMetric_congruence_factorization) metricActual
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have hf := admMetric_congruence_factorization 1 0 1
      have ho := h 1 0 1
      rw [← hf] at ho
      exact metric_one_ne ho.symm)
    metric_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@admMetric_congruence_factorization) (Realization MetricSignature) Unit Unit :=
  bindADM% admMetric_congruence_factorization Congruence arena family admMetric 0

end Congruence

namespace Inverse

abbrev arena : Arena where
  signature := MetricSignature
  Law R := ∀ {N : ℝ}, N ≠ 0 → ∀ (β : Shift) {γ γInv : Mat3},
    γ * γInv = 1 → γInv * γ = 1 →
      R.readout () () N β γ * admInvMetric N β γInv = 1 ∧
        admInvMetric N β γInv * admMetric N β γ = 1

def family : Registration arena (type_of% (@admMetric_mul_inv)) :=
  unitFamily% arena (@admMetric_mul_inv) metricActual
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have ho := (h (N := 1) (by norm_num) 0 (γ := 1) (γInv := 1) (by simp) (by simp)).1
      simp [realize] at ho)
    metric_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@admMetric_mul_inv) (Realization MetricSignature) Unit Unit :=
  bindADM% admMetric_mul_inv Inverse arena family admMetric 0

end Inverse

namespace Volume

abbrev arena : Arena where
  signature := MetricSignature
  Law R := ∀ (N : ℝ) (β : Shift) (γ : Mat3),
    (R.readout () () N β γ).det = -(N ^ 2) * γ.det ∧
      (0 < N → 0 ≤ γ.det → Real.sqrt (-(admMetric N β γ).det) = N * Real.sqrt γ.det)

def family : Registration arena (type_of% (@admMetric_det_and_volume)) :=
  unitFamily% arena (@admMetric_det_and_volume) metricActual
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have ho := (h 1 0 1).1
      norm_num [realize] at ho)
    metric_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@admMetric_det_and_volume) (Realization MetricSignature) Unit Unit :=
  bindADM% admMetric_det_and_volume Volume arena family admMetric 0

end Volume

namespace Normal

abbrev arena : Arena where
  signature := MetricSignature
  Law R := ∀ {N : ℝ}, N ≠ 0 → ∀ (β : Shift) (γ : Mat3),
    nUp N β ⬝ᵥ (R.readout () () N β γ *ᵥ nUp N β) = -1 ∧
      (∀ i : Fin 3, nUp N β ⬝ᵥ (admMetric N β γ *ᵥ eSpatial i) = 0) ∧
      admMetric N β γ *ᵥ nUp N β = Fin.cons (-N) (fun _ => 0)

def family : Registration arena (type_of% (@adm_unit_timelike_normal)) :=
  unitFamily% arena (@adm_unit_timelike_normal) metricActual
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have ho := (h (N := 1) (by norm_num) 0 1).1
      norm_num [realize] at ho)
    metric_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adm_unit_timelike_normal) (Realization MetricSignature) Unit Unit :=
  bindADM% adm_unit_timelike_normal Normal arena family admMetric 0

end Normal

private theorem identity_positive (w : Shift) (hw : w ≠ 0) :
    0 < w ⬝ᵥ ((1 : Mat3) *ᵥ w) := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! h
    apply hw
    funext i
    exact h i
  rw [Matrix.one_mulVec, dotProduct]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (w j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

namespace Signature

abbrev arena : Arena where
  signature := MetricSignature
  Law R := ∀ {N : ℝ}, 0 < N → ∀ (β : Shift) (γ : Mat3), γᵀ = γ →
    (∀ w : Shift, w ≠ 0 → 0 < w ⬝ᵥ (γ *ᵥ w)) →
    (∀ v : Fin 4 → ℝ,
      let w := fun i : Fin 3 => v i.succ + v 0 * β i
      v ⬝ᵥ (admMetric N β γ *ᵥ v) = -(N * v 0) ^ 2 + w ⬝ᵥ (γ *ᵥ w)) ∧
      nUp N β ⬝ᵥ (R.readout () () N β γ *ᵥ nUp N β) < 0 ∧
      (∀ v : Fin 4 → ℝ, v 0 = 0 → v ≠ 0 → 0 < v ⬝ᵥ (admMetric N β γ *ᵥ v)) ∧
      (admMetric N β γ)ᵀ = admMetric N β γ

def family : Registration arena (type_of% (@adm_lorentzian_signature)) :=
  unitFamily% arena (@adm_lorentzian_signature) metricActual
    (unitObserve% (fun _ _ _ => 0))
    (by
      intro h
      have ho := (h (N := 1) (by norm_num) 0 1 (by simp) identity_positive).2.1
      norm_num [realize] at ho)
    metric_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adm_lorentzian_signature) (Realization MetricSignature) Unit Unit :=
  bindADM% adm_lorentzian_signature Signature arena family admMetric 1

end Signature

namespace Legendre

abbrev signature : Signature := operandSignature ℝ (Mat3 → Mat3)

def actual : Realization signature := unitObserve% admMomentum

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, s ≠ 0 → ∀ K P : Mat3,
    admExtrinsicFromMomentum s (R.readout () () s K) = K ∧
      admMomentum s (admExtrinsicFromMomentum s P) = P ∧
      (admMomentum s K).trace = -2 * s * K.trace ∧
      (K * K).trace - K.trace ^ 2 = (1 / s ^ 2) * dewittKinetic (admMomentum s K)

def family : Registration arena (type_of% (@adm_legendre_transform_involution)) :=
  unitFamily% arena (@adm_legendre_transform_involution) actual
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have ho := (h (s := 1) (by norm_num) 1 0).1
      simp [realize, admExtrinsicFromMomentum] at ho)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      have ho := congrArg Matrix.trace (congrFun h 1)
      change (admMomentum 0 1).trace = (admMomentum 1 1).trace at ho
      have hz := (adm_legendre_transform_involution (sdetγ := 1) one_ne_zero 1 0).2.2.1
      rw [hz] at ho
      norm_num [admMomentum, Matrix.trace_one] at ho)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adm_legendre_transform_involution) (Realization signature) Unit Unit :=
  bindADM% adm_legendre_transform_involution Legendre arena family admMomentum 0

end Legendre

namespace DeWitt

abbrev signature : Signature := operandSignature Mat3 ℝ
def actual : Realization signature := unitObserve% dewittKinetic

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ P : Mat3, Pᵀ = P →
      let Ptf := P - (P.trace / 3) • 1
      P = (P.trace / 3) • 1 + Ptf ∧ Ptf.trace = 0 ∧ Ptfᵀ = Ptf ∧
        dewittKinetic P = -(1 / 6) * P.trace ^ 2 + (Ptf * Ptf).trace) ∧
      (∀ μ : ℝ, μ ≠ 0 → R.readout () () (μ • (1 : Mat3)) = -(3 / 2) * μ ^ 2 ∧
        dewittKinetic (μ • (1 : Mat3)) < 0) ∧
      (∀ P : Mat3, Pᵀ = P → P.trace = 0 → P ≠ 0 →
        dewittKinetic P = (P * P).trace ∧ 0 < (P * P).trace) ∧
      (∀ P : Mat3, Pᵀ = P → P.trace = 0 → ∃! v : Fin 5 → ℝ,
        P = !![v 0, v 2, v 3; v 2, v 1, v 4; v 3, v 4, -v 0 - v 1])

def family : Registration arena (type_of% (@dewitt_supermetric_lorentzian_signature)) :=
  unitFamily% arena (@dewitt_supermetric_lorentzian_signature) actual
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have ho := (h.2.1 1 one_ne_zero).1
      norm_num [realize] at ho)
    (by
      refine ⟨(), 0, 1, fun h => ?_⟩
      change dewittKinetic 0 = dewittKinetic 1 at h
      have ho := (dewitt_supermetric_lorentzian_signature.2.1 1 one_ne_zero).1
      rw [one_smul] at ho
      rw [ho] at h
      norm_num [dewittKinetic] at h)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dewitt_supermetric_lorentzian_signature) (Realization signature) Unit Unit :=
  bindADM% dewitt_supermetric_lorentzian_signature DeWitt arena family dewittKinetic 1

end DeWitt

namespace Friedmann

abbrev signature : Signature := operandSignature (ℝ → ℝ) (ℝ → ℝ)
def actual : Realization signature := unitObserve% hubble

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ → ℝ} {t : ℝ}, 0 < a t → ∀ (k Λ G ρ : ℝ),
    let γInv : Mat3 := (1 / a t ^ 2) • 1
    let K : Mat3 := (a t * deriv a t) • 1
    let Kmixed := γInv * K
    let H := R.readout () () a t
    (Kmixed * Kmixed).trace - Kmixed.trace ^ 2 - 6 * k / a t ^ 2 + 2 * Λ +
        16 * Real.pi * G * ρ = 0 ↔
      3 * H ^ 2 = 8 * Real.pi * G * ρ + Λ - 3 * k / a t ^ 2

def family : Registration arena (type_of% (@adm_hamiltonian_constraint_reproduces_friedmann)) :=
  unitFamily% arena (@adm_hamiltonian_constraint_reproduces_friedmann) actual
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have hpos : (0 : ℝ) < id 1 := by norm_num
      have hzero := (h (a := id) (t := 1) hpos 0 0 0 0).2 (by norm_num [realize])
      have hc := (adm_hamiltonian_constraint_reproduces_friedmann hpos 0 0 0 0).1 hzero
      norm_num [hubble, deriv_id''] at hc)
    (by
      refine ⟨(), (fun _ => 1), id, fun h => ?_⟩
      have hh := congrFun h 1
      change hubble (fun _ => 1) 1 = hubble id 1 at hh
      norm_num [hubble, deriv_id''] at hh)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adm_hamiltonian_constraint_reproduces_friedmann) (Realization signature) Unit Unit :=
  bindADM% adm_hamiltonian_constraint_reproduces_friedmann Friedmann arena family hubble 0

end Friedmann

end

end Reg.D5.S3.Geometry.Lorentz.ADMHamiltonianGravity4D.Algebra
