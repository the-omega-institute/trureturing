import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicActivationShift

/-! Activating the boundary pair is detected by strict positivity of the fitted weights. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicActivationShift

open Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityLimit
open _root_.D5.S3.Fourier.Asymptotics.CyclicActivationShift
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => max 0 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 2 ≤ n) (odd : Bool),
    let clip := R.readout () ()
    let d := parityOffset odd
    let m₀ := ((n : ℝ) ^ 2 - 1) / 5
    let q := parityModulus odd
    let h := fun k => mesh (q k)
    ∃ (ε : ℝ) (root : ℕ → ℝ), 0 < ε ∧
      Tendsto (fun k => (root k - m₀) / h k ^ 2) atTop
        (𝓝 (((n : ℝ) ^ 2 - 1) * (63 * d ^ 2 + 47 - 31 * (n : ℝ) ^ 2) / 420)) ∧
      ∀ᶠ k in atTop, root k ∈ Set.Ioo (m₀ - ε) (m₀ + ε) ∧
        ∀ m ∈ Set.Icc (m₀ - ε) (m₀ + ε),
          let θ := 1 - 2 * m * h k ^ 2
          ∃ v ∈ feasible (q k) θ, cosineMoment 1 v = θ ∧ cosineMoment 2 v = θ ∧
            (∀ w ∈ feasible (q k) θ, w ≠ v → energy v < energy w) ∧
            ∀ i : ZMod (q k), 0 < clip (v i) ↔ |(i.valMinAbs : ℝ)| < n ∨
              (root k < m ∧ |(i.valMinAbs : ℝ)| = n) ∨
              sample i = sample ((↑(q k / 2) : ℤ) : ZMod (q k))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  obtain ⟨ε, root, _, _, he⟩ := hlaw 2 (by decide) false
  obtain ⟨k, hk, hs⟩ := he.exists
  obtain ⟨v, _, _, _, _, hsupport⟩ := hs (root k) ⟨hk.1.le, hk.2.le⟩
  let i : ZMod (parityModulus false k) := ((↑(parityModulus false k / 2) : ℤ) : ZMod _)
  exact (lt_irrefl (0 : ℝ)) ((hsupport i).mpr (Or.inr (Or.inr rfl)))

def evidence : Registration arena (type_of% @cyclic_activation_shift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_activation_shift, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_activation_shift) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicActivationShift.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicActivationShift.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicActivationShift
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicActivationShift
