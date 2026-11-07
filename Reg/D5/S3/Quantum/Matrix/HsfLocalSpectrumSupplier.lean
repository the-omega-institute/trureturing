import D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-binding attempt for the full finite-spectrum local all-Z theorem.
The readout keeps the radius implication and both scalar conclusions. The
source-selection reconstruction and escape coordinate remain unresolved under
https://github.com/the-omega-institute/trureturing/issues/23103.
This attempt does not assert declared_validated. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := Prop × ℝ × ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 → 0 < s.2.1 ∧ s.2.2.1 ≤ s.2.2.2)
    (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {d : ℕ} (p : Fin d → ℝ), (∀ i, 0 < p i) →
    ∀ (hlevels : ∃ i j, p i ≠ p j) (H : Matrix (Fin d) (Fin d) ℂ), H.IsHermitian →
    (∀ i j, p i = p j → H i j = 0) →
    ∀ (Z : Matrix (Fin d) (Fin d) ℂ), Z.IsHermitian →
    let P : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (p i : ℂ))
    let S := (1 : Matrix (Fin d) (Fin d) ℂ) + H
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P ^ 3 + t • (CFC.rpow P (3 / 2 : ℝ) * S *
        CFC.rpow P (3 / 2 : ℝ))) (2 / 3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    W.readout () () (frob H ≤ 3 * crossGap p hlevels / 32,
      crossGap p hlevels, crossGap p hlevels * frob H ^ 2 / 6,
      (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z ^ 2 -
        (5 / 48 : ℝ) • (B 1) ^ 3).trace.re)

private theorem bridge :
    (type_of% (@finite_spectrum_local_supplier)) ↔ arena.Law actual := by
  dsimp only [arena, actual, realize]
  constructor
  · intro h d p hp hl H hH hs Z hZ hr
    exact h p hp hl H hH hs hr Z hZ
  · intro h d p hp hl H hH hs hr Z hZ
    exact h p hp hl H hH hs Z hZ hr

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Fin 2 → ℝ := fun i => (i.val : ℝ) + 1
  have hp : ∀ i, 0 < p i := by intro i; dsimp [p]; positivity
  have hl : ∃ i j, p i ≠ p j := ⟨0, 1, by norm_num [p]⟩
  exact h p hp hl 0 (by simp) (by simp) 0 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (True, 1, 0, 0), (True, 0, 0, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@finite_spectrum_local_supplier)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@finite_spectrum_local_supplier), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_spectrum_local_supplier) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ s => s.1 → 0 < s.2.1 ∧ s.2.2.1 ≤ s.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

namespace Uniform

private abbrev signature : Signature where
  Params := Unit
  State _ := Prop × ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 → s.2.1 ≤ s.2.2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law W := ∀ {d : ℕ} (p : Fin d → ℝ), (∀ i, 0 < p i) →
    ∀ (H : Matrix (Fin d) (Fin d) ℂ), H.IsHermitian →
    ∀ (Z : Matrix (Fin d) (Fin d) ℂ), Z.IsHermitian →
    let P : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (p i : ℂ))
    let S := (1 : Matrix (Fin d) (Fin d) ℂ)+H
    let F := fun t : ℝ => P⁻¹*
      CFC.rpow (P^3+t • (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    let A : Matrix (Fin d) (Fin d) ℂ := fun i j => (spectralTau (p i) (p j) : ℂ)*H i j
    W.readout () () (frob H ≤ 1/20, (frob H^2-frob A^2)/6,
      (B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re)

private theorem bridge :
    (type_of% (@finite_spectrum_uniform_local_supplier)) ↔ arena.Law actual := by
  dsimp only [arena, actual, realize]
  constructor
  · intro h d p hp H hH Z hZ hr
    exact h p hp H hH hr Z hZ
  · intro h d p hp H hH hr Z hZ
    exact h p hp H hH Z hZ hr

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (d := 0) (fun _ => 1) (by intro i; norm_num) 0 (by simp) 0 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (True, 0, 0), (True, 1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@finite_spectrum_uniform_local_supplier)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@finite_spectrum_uniform_local_supplier), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

/-- Exact original telescope and actual-jet readout. Source-selection and
escape evidence remain unresolved under issue 23103; no validated status is asserted. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_spectrum_uniform_local_supplier) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier.Uniform.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier.Uniform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 → s.2.1 ≤ s.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Uniform

end
end Reg.D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
