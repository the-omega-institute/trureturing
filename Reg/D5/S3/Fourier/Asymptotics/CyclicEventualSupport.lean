import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicEventualSupport

/-! The support readout records strict positivity of the indicated weights. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicEventualSupport

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.D5.S3.Fourier.Asymptotics.CyclicEventualSupport
open _root_.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => max 0 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lam : ℝ) (_hlam : 0 < lam),
    let clip := R.readout () ()
    let m := lam / (8 * Real.pi ^ 2)
    ∃ (n : ℕ) (t Z : ℝ) (w : ℤ → ℝ), 0 < n ∧
      ((n : ℝ) ^ 2 - 1) / 5 ≤ m ∧ m < (n : ℝ) * (n + 2) / 5 ∧
      Activation m n t Z w ∧
      ∃ Q : ℕ, ∀ q ≥ Q, ∀ [NeZero q],
        (∃ v ∈ feasible q (1 - lam / (q : ℝ) ^ 2),
          IsMinOn energy (feasible q (1 - lam / (q : ℝ) ^ 2)) v ∧
          cosineMoment 1 v = 1 - lam / (q : ℝ) ^ 2 ∧
          cosineMoment 2 v = 1 - lam / (q : ℝ) ^ 2 ∧
          (∀ u ∈ feasible q (1 - lam / (q : ℝ) ^ 2), u ≠ v → energy v < energy u) ∧
          (∀ u ∈ feasible q (1 - lam / (q : ℝ) ^ 2),
            energy v + (∑ i, (u i - v i) ^ 2) ≤ energy u)) ∧
        ∀ v ∈ feasible q (1 - lam / (q : ℝ) ^ 2),
          IsMinOn energy (feasible q (1 - lam / (q : ℝ) ^ 2)) v → ∀ i : ZMod q,
            0 < clip (v i) ↔ (i.valMinAbs : ℝ) ^ 2 ≤ t ∨ ∀ j : ZMod q, sample i ≤ sample j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, t, Z, w, _, _, _, act, Q, hQ⟩ := h 1 (by norm_num)
  let q := Q + 1
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨⟨v, hv, hm, _, _⟩, hs⟩ := hQ q (by omega)
  have ht : 0 ≤ t := (sq_nonneg _).trans act.radius_lower
  have hcenter : ((0 : ZMod q).valMinAbs : ℝ) ^ 2 ≤ t := by simpa using ht
  exact (lt_irrefl _) ((hs v hv hm 0).mpr (Or.inl hcenter))

def evidence : Registration arena (type_of% @cyclic_eventual_exact_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_eventual_exact_support, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_eventual_exact_support) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicEventualSupport.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicEventualSupport.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicEventualSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicEventualSupport
