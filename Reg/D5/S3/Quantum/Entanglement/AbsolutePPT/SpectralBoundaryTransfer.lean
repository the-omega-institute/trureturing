import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN6PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction (K1 K2)
open LeanInformationAudit Matrix

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin (n + 10) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev statement : Prop := ∀ (n a : ℕ), 1 ≤ a → SpectralBound n →
  SpectralBound (n + 1 + a) → SpectralBound (n + 1)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n a : ℕ), 1 ≤ a → SpectralBound n → SpectralBound (n + 1 + a) →
    ∀ l : Fin (n + 10) → ℝ, Antitone l → (∀ i, 0 ≤ l i) →
      (∑ i, l i) = 1 → (K1 (boundaryValues (n + 1) l)).PosSemidef →
      (K2 (boundaryValues (n + 1) l)).PosSemidef →
      O.readout () n l ≤ purityBound (n + 10)

private theorem endpoint18 : SpectralBound 9 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 9 l = QutritSpectralReduction.boundaryValues 3 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN6PurityBound.certificate_bound l ho (hn 17) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem endpoint21 : SpectralBound 12 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 12 l = QutritSpectralReduction.boundaryValues 4 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN7PurityBound.certificate_bound l ho (hn 20) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem flat_psd (k : Bool) :
    ((if k then K1 else K2) (boundaryValues 10 (fun _ => (1 / 19 : ℝ)))).PosSemidef := by
  have heq : (if k then K1 else K2) (boundaryValues 10 (fun _ => (1 / 19 : ℝ))) =
      (2 / 19 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [K1, K2, boundaryValues, Matrix.smul_apply, Matrix.one_apply]
  rw [heq]
  exact Matrix.PosSemidef.one.smul (by norm_num)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hle := h 9 2 (by decide) endpoint18 endpoint21 (fun _ => (1 / 19 : ℝ))
    (fun _ _ _ => le_rfl) (fun _ => by norm_num) (by simp)
    (by simpa using flat_psd true) (by simpa using flat_psd false)
  norm_num [rejected, realize, purityBound] at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : Fin 10, (0 : ℝ)^2) ≠ ∑ _ : Fin 10, (1 : ℝ)^2
  norm_num

def familyRegistration : Registration arena statement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spectral_bound_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- The omitted source selector leaves the structural reconstruction obligation open. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.spectral_bound_transfer)
    (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.spectral_bound_transfer.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

namespace RankFour
open UniformRankFourNecessary (sumFirst sumLast)

private theorem endpoint24 : RankFourSpectralBound 8 := by
  intro l ho hn ht h1 h2 _
  have hb : boundaryValues 15 l = QutritSpectralReduction.boundaryValues 5 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN8PurityBound.certificate_bound l ho (hn 23) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem flat_psd (n : ℕ) (k : Bool) :
    ((if k then K1 else K2) (boundaryValues (n + 7)
      (fun _ : Fin (n + 16) => (1 : ℝ) / (n + 16)))).PosSemidef := by
  have heq : (if k then K1 else K2) (boundaryValues (n + 7)
      (fun _ : Fin (n + 16) => (1 : ℝ) / (n + 16))) =
      (2 / ((n : ℝ) + 16)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [K1, K2, boundaryValues, Matrix.smul_apply, Matrix.one_apply] <;> ring
  rw [heq]
  exact Matrix.PosSemidef.one.smul (by positivity)

namespace Transfer
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin (n + 16) → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ n _ => if n = 9 then (2 : ℝ) else 0) (fun e => nomatch e)
/-- All three dimensions use the same whole-family intervention. -/
private def observedBound (O : Realization signature) (n : ℕ) : Prop :=
  ∀ l : Fin (n + 16) → ℝ, Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
    (K1 (boundaryValues (n + 7) l)).PosSemidef →
    (K2 (boundaryValues (n + 7) l)).PosSemidef → sumFirst 6 l ≤ sumLast 10 l →
    O.readout () n l ≤ purityBound (n + 16)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ n a : ℕ, 8 ≤ n → 1 ≤ a → observedBound O n →
    observedBound O (n + 1 + a) → observedBound O (n + 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h24 : observedBound rejected 8 := by
    intro l _ _ _ _ _ _
    change (0 : ℝ) ≤ purityBound 24
    norm_num [purityBound]
  have h27 : observedBound rejected 11 := by
    intro l _ _ _ _ _ _
    change (0 : ℝ) ≤ purityBound 27
    norm_num [purityBound]
  have hh := h 8 2 (by norm_num) (by norm_num) h24 h27
    (fun _ => 1 / 25) (fun _ _ _ => le_rfl) (fun _ => by norm_num)
    (by norm_num) (by convert flat_psd 9 true using 1 <;> norm_num) (by convert flat_psd 9 false using 1 <;> norm_num)
    (by norm_num [sumFirst, sumLast, Fin.sum_univ_succ])
  change (2 : ℝ) ≤ purityBound 25 at hh
  norm_num [purityBound] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨9, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : Fin 25, (0 : ℝ)^2) ≠ ∑ _ : Fin 25, (1 : ℝ)^2
  norm_num
def family : Registration arena (type_of% @rank_four_spectral_bound_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_four_spectral_bound_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.rank_four_spectral_bound_transfer)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.RankFour.Transfer.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.RankFour.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- The endpoint observations lie inside a parameterized source predicate.
  -- A source reconstruction entering those predicates is not supplied here.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Transfer

namespace Interval
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin (n + 16) → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ M : ℕ, 8 ≤ M → RankFourSpectralBound M →
    ∀ n : ℕ, 8 ≤ n → n ≤ M →
    ∀ l : Fin (n + 16) → ℝ, Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
    (K1 (boundaryValues (n + 7) l)).PosSemidef →
    (K2 (boundaryValues (n + 7) l)).PosSemidef → sumFirst 6 l ≤ sumLast 10 l →
    O.readout () n l ≤ purityBound (n + 16)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 8 (by norm_num) endpoint24 8 (by norm_num) (by norm_num)
    (fun _ => 1 / 24) (fun _ _ _ => le_rfl) (fun _ => by norm_num)
    (by norm_num) (by convert flat_psd 8 true using 1 <;> norm_num) (by convert flat_psd 8 false using 1 <;> norm_num)
    (by norm_num [sumFirst, sumLast, Fin.sum_univ_succ])
  change (2 : ℝ) ≤ purityBound 24 at hh
  norm_num [purityBound] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨8, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : Fin 24, (0 : ℝ)^2) ≠ ∑ _ : Fin 24, (1 : ℝ)^2
  norm_num
def family : Registration arena (type_of% @rank_four_endpoint_interval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_four_endpoint_interval, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.rank_four_endpoint_interval)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.RankFour.Interval.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.RankFour.Interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Interval

end RankFour

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
