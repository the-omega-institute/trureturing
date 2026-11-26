import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for the Apéry spectrum and its residue witnesses. -/

namespace Reg.D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum

open CKApery LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (sensitivity)

noncomputable section

private def small : Params := ⟨1, 2, 3, by decide, by decide, by decide, by decide⟩
private def large : Params := ⟨1, 3, 3, by decide, by decide, by decide, by decide⟩

namespace Spectrum

-- The selected occurrence takes the whole admissible family as its state.
-- Its index is the only independent coordinate in the readout.
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Params) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n P => P.spectrum n) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b k : ℕ) (ha : 0 < a) (hab : a < b)
      (hc : Nat.Coprime a b) (hk : 3 ≤ k),
    let P : Params := ⟨a, b, k, ha, hab, hc, hk⟩
    (∀ n, R.readout () n P = P.sourceSpectrum n) ∧
    P.spectrumList.SortedGE ∧
    (∀ n, 0 < P.spectrum n ↔ n < b + k - 3) ∧
    (∀ z, P.spectrumList.count z =
      (List.range (P.U - 1)).countP (fun i => P.evalBeta (i + 1) == z) +
      (List.range P.V).countP (fun j => P.evalGamma j == z)) ∧
    (∀ z, P.spectrumList.count z ≤ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : 0 = small.sourceSpectrum 0 :=
    (h 1 2 3 (by decide) (by decide) (by decide) (by decide)).1 0
  have source := family_spectrum 1 2 3 (by decide) (by decide) (by decide) (by decide)
  have hpositive : 0 < small.spectrum 0 := (source.2.2.1 0).2 (by decide)
  have heq : small.spectrum 0 = small.sourceSpectrum 0 := source.1 0
  rw [heq, ← hzero] at hpositive
  exact (Nat.lt_irrefl 0) hpositive

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨2, small, large, ?_⟩
  change small.spectrum 2 ≠ large.spectrum 2
  have hsmall := (family_spectrum 1 2 3 (by decide) (by decide)
    (by decide) (by decide)).2.2.1 2
  have hlarge := (family_spectrum 1 3 3 (by decide) (by decide)
    (by decide) (by decide)).2.2.1 2
  have hzero : small.spectrum 2 = 0 :=
    Nat.eq_zero_of_not_pos (fun h => (Nat.lt_irrefl 2) (hsmall.1 h))
  have hpos : 0 < large.spectrum 2 := hlarge.2 (by decide)
  intro h
  rw [← h, hzero] at hpos
  exact (Nat.lt_irrefl 0) hpos

def evidence : Registration arena (type_of% @family_spectrum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨family_spectrum, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@family_spectrum) (Realization signature) Unit Unit where
  unitName :=
    Lean.Name.str
      `Reg.D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum.Spectrum
      "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum.Spectrum.evidence
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
    owner := `D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum
    definition := none
    coordinates := #[8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Spectrum

namespace Residue

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params Params.Rect (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ P q => P.W q.1 q.2) (fun e => nomatch e)

private def shifted : Realization signature :=
  realize signature (fun _ P q => P.W q.1 q.2 + P.d) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : Params) (s : Fin P.d),
    ∃! q : P.Rect, P.rightRes q = s ∧
      IsLeast {t : ℕ | t ∈ AddSubmonoid.closure ({P.a, P.b, P.d} : Set ℕ) ∧
        t % P.d = P.negRes s} (P.L q.1 q.2) ∧
      IsLeast {t : ℕ | t ∈ AddSubmonoid.closure ({P.d - P.a, P.d - P.b, P.d} : Set ℕ) ∧
        t % P.d = s} (R.readout () P q)

private theorem shifted_law : ¬ arena.Law shifted := by
  intro h
  let s : Fin small.d := ⟨0, by decide⟩
  obtain ⟨q, ⟨_, _, hleast⟩, _⟩ := h small s
  have hzero : (0 : ℕ) ∈
      {t : ℕ | t ∈ AddSubmonoid.closure ({small.d - small.a, small.d - small.b, small.d} : Set ℕ) ∧
        t % small.d = s} := ⟨AddSubmonoid.zero_mem _, by simp [s]⟩
  have hle : small.W q.1 q.2 + small.d ≤ 0 := hleast.2 hzero
  have hd : small.d = 6 := rfl
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨small, (⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩), ?_⟩
  change small.W 0 0 ≠ small.W 1 0
  decide

def evidence : Registration arena (type_of% @Params.residue_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Params.residue_witness, shifted, shifted_law⟩
  sensitivity := sensitivity arena.Law actual shifted shifted_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Params.residue_witness) (Realization signature) Unit Unit where
  unitName :=
    Lean.Name.str
      `Reg.D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum.Residue
      "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum.Residue.evidence
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
    owner := `D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Residue

end
end Reg.D5.S3.Arith.NumericalSemigroups.ChaudharyKhandelwalAperySpectrum
