import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy

/-! Source-bound registrations for the qubit rotor gate, the Gram identity of three unit
vectors and the return phase of the shortest gates around a Bloch triangle. Each record
selects one actual occurrence of its readout in the original statement and keeps every other
clause verbatim. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.GroupInvariantPsi.C129QubitBargmann
open _root_.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy
open Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy

private def e₃ : Fin 3 → ℝ := ![0, 0, 1]

private lemma e₃_unit : e₃ ⬝ᵥ e₃ = 1 := by
  simp [e₃, dotProduct, Fin.sum_univ_three]

private lemma e₃_ne_neg : e₃ ≠ -e₃ := by
  intro h
  have := congrFun h 2
  simp [e₃] at this
  norm_num at this

private lemma rotor_e₃_e₃_entry : rotor e₃ e₃ 0 0 ≠ 0 := by
  have hpos : 0 < Real.sqrt (2 * (1 + e₃ ⬝ᵥ e₃)) := by
    rw [e₃_unit]; positivity
  have hne : ((Real.sqrt (2 * (1 + e₃ ⬝ᵥ e₃)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hentry : rotor e₃ e₃ 0 0 = ((Real.sqrt (2 * (1 + e₃ ⬝ᵥ e₃)) : ℝ) : ℂ)⁻¹ * 2 := by
    simp [rotor, pauliCombination, e₃]
    norm_num
  rw [hentry]
  exact mul_ne_zero (inv_ne_zero hne) two_ne_zero

private lemma rotor_e₃_neg_e₃ : rotor e₃ (-e₃) = 0 := by
  have h : 1 + e₃ ⬝ᵥ (-e₃) = 0 := by
    rw [dotProduct_neg, e₃_unit]; ring
  simp only [rotor, h, mul_zero, Real.sqrt_zero, Complex.ofReal_zero, _root_.inv_zero, zero_smul]

private theorem rotor_ne : rotor e₃ e₃ ≠ rotor e₃ (-e₃) := by
  rw [rotor_e₃_neg_e₃]
  intro h
  exact rotor_e₃_e₃_entry (by rw [h]; rfl)

namespace Rotor

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 3 → ℝ) (fun _ => Fin 3 → ℝ)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ a b => rotor a b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : Fin 3 → ℝ) (_ : a ⬝ᵥ a = 1) (_ : b ⬝ᵥ b = 1) (_ : b ≠ -a),
    R.readout () a b * (rotor a b)ᴴ = 1 ∧
      rotor a b * pauliCombination a * (rotor a b)ᴴ = pauliCombination b ∧
      ∀ ψ : QubitState, star ψ ⬝ᵥ ψ = 1 → qubitProjector a *ᵥ ψ = ψ →
        rotor a b *ᵥ ψ = shortestGate b ψ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h e₃ e₃ e₃_unit e₃_unit e₃_ne_neg).1
  simp only [rejected, realize, Matrix.zero_mul] at hh
  have := congrFun (congrFun hh 0) 0
  simp only [Matrix.zero_apply, Matrix.one_apply_eq] at this
  exact zero_ne_one this

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨e₃, e₃, -e₃, rotor_ne⟩

def source : Registration arena (type_of% @rotor_shortest_gate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rotor_shortest_gate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rotor_shortest_gate) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy.Rotor.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy.Rotor.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => rotor a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Rotor

namespace Gram

abbrev Params := Σ _ : Fin 3 → ℝ, Fin 3 → ℝ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p c => triangleD p.1 p.2 c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c : Fin 3 → ℝ) (_ : a ⬝ᵥ a = 1) (_ : b ⬝ᵥ b = 1) (_ : c ⬝ᵥ c = 1),
    R.readout () ⟨a, b⟩ c ^ 2 =
        1 + 2 * (a ⬝ᵥ b) * (b ⬝ᵥ c) * (c ⬝ᵥ a) - (a ⬝ᵥ b) ^ 2 - (b ⬝ᵥ c) ^ 2 -
          (c ⬝ᵥ a) ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h e₃ e₃ e₃ e₃_unit e₃_unit e₃_unit
  simp only [rejected, realize, e₃_unit] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨![1, 0, 0], ![0, 1, 0]⟩, ![0, 0, 1], ![1, 0, 0], ?_⟩
  change triangleD ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] ≠ triangleD ![1, 0, 0] ![0, 1, 0] ![1, 0, 0]
  simp [triangleD, dotProduct, Fin.sum_univ_three, cross_apply]

def source : Registration arena (type_of% @triangle_gram) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@triangle_gram, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@triangle_gram) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy.Gram.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy.Gram.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c => triangleD p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Gram

namespace Holonomy

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 3 → ℝ) (fun _ => Fin 3 → ℝ)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ a b => rotor a b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c : Fin 3 → ℝ) (_ : a ⬝ᵥ a = 1) (_ : b ⬝ᵥ b = 1) (_ : c ⬝ᵥ c = 1)
    (_ : b ≠ -a) (_ : c ≠ -b) (_ : a ≠ -c),
    triangleS a b c ^ 2 + triangleD a b c ^ 2 =
        2 * (1 + a ⬝ᵥ b) * (1 + b ⬝ᵥ c) * (1 + c ⬝ᵥ a) ∧
      0 < triangleS a b c ^ 2 + triangleD a b c ^ 2 ∧
      rotor c a * rotor b c * R.readout () a b =
        (((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ))⁻¹ •
          (((triangleS a b c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
            (((triangleD a b c : ℝ) : ℂ) * Complex.I) • pauliCombination a) ∧
      ∀ ψ : QubitState, star ψ ⬝ᵥ ψ = 1 → qubitProjector a *ᵥ ψ = ψ →
        shortestGate a (shortestGate c (shortestGate b ψ)) =
          ((((triangleS a b c : ℝ) : ℂ) - ((triangleD a b c : ℝ) : ℂ) * Complex.I) /
              ((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ)) • ψ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h e₃ e₃ e₃ e₃_unit e₃_unit e₃_unit e₃_ne_neg e₃_ne_neg e₃_ne_neg).2.2.1
  simp only [rejected, realize, Matrix.mul_zero] at hh
  have hS : triangleS e₃ e₃ e₃ = 4 := by
    simp [triangleS, e₃, dotProduct, Fin.sum_univ_three]; norm_num
  have hD : triangleD e₃ e₃ e₃ = 0 := by
    simp [triangleD, e₃, dotProduct]
  rw [hS, hD] at hh
  have := congrFun (congrFun hh 0) 0
  have hsq : Real.sqrt ((4 : ℝ) ^ 2 + 0 ^ 2) = 4 := by
    rw [show (4 : ℝ) ^ 2 + 0 ^ 2 = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsq] at this
  simp [pauliCombination, e₃] at this

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨e₃, e₃, -e₃, rotor_ne⟩

def source : Registration arena (type_of% @shortest_gate_triangle_holonomy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shortest_gate_triangle_holonomy, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@shortest_gate_triangle_holonomy) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy.Holonomy.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy.Holonomy.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => rotor a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Holonomy

end Reg.D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy
