import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

/-! Dependence of the uniform finite-cycle approximation on the error allowance. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 2 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q n : ℕ), 0 < n → ∀ lam : ℝ,
    ∀ hq : 2 * latticeSupportRadius n (lam / (8 * Real.pi ^ 2)) < q,
    ((n : ℝ) ^ 2 - 1) / 5 ≤ lam / (8 * Real.pi ^ 2) →
    lam / (8 * Real.pi ^ 2) ≤ (n : ℝ) * (n + 2) / 5 →
    letI : NeZero q := ⟨by omega⟩
    let m := lam / (8 * Real.pi ^ 2)
    let a := 1 - lam / (q : ℝ) ^ 2
    let error := fun x : ℝ => R.readout () () x
    ∃ (t Z : ℝ) (w : ℤ → ℝ), Activation m n t Z w ∧
      (∀ (u : ZMod q → ℝ), (∀ i, 0 ≤ u i) → (∑ i, u i) = 1 →
        (∑ i : ZMod q, (u i - w i.valMinAbs) ^ 2) +
          (2 * t / Z) * (cosineMoment 1 u - a) +
          (((q : ℝ) / (2 * Real.pi)) ^ 2 / Z) * (cosineMoment 2 u - a) ≤
        energy u - (∑' k : ℤ, w k ^ 2) + (2 * t / Z) * (lam / (q : ℝ) ^ 2)) ∧
      ∃ v ∈ feasible q a, IsMinOn energy (feasible q a) v ∧
        0 ≤ (∑' k : ℤ, w k ^ 2) - energy v ∧
        (∑' k : ℤ, w k ^ 2) - energy v ≤ (2 * t / Z) * (lam / (q : ℝ) ^ 2) ∧
        (∑' k : ℤ, w k ^ 2) - energy v ≤ error (lam / (q : ℝ) ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨_, _, _, _, _, _, _, _, hnonneg, _, hbound⟩ :=
    law 3 1 (by decide) 0 (by norm_num [latticeSupportRadius]) (by norm_num) (by norm_num)
  have hbad := hnonneg.trans hbound
  change (0 : ℝ) ≤ -1 at hbad
  norm_num at hbad

def evidence : Registration arena (type_of% @cyclic_to_lattice_comparison) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_to_lattice_comparison, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_to_lattice_comparison) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Centering

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.cos x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] (r : ℕ) (v : ZMod q → ℝ),
    let readout := R.readout () ()
    cosineMoment r v = ∑ i : ZMod q, v i * readout ((r : ℝ) * centeredAngle i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (q := 1) 0 (fun _ => 1)
  simp [cosineMoment, D5.S3.Fourier.Concentration.AggregateCosineBalance.mode, rejected, realize] at h

def evidence : Registration arena (type_of% @cosineMoment_eq_centered) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cosineMoment_eq_centered, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, Real.pi, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cosineMoment_eq_centered) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison.Centering.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison.Centering.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Centering

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
