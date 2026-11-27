import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52

open scoped Quaternion
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52

namespace Reg.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ M : ℕ, Fin M → ℍ[ℤ])
    (fun p => Fin p.1) (fun _ => ℍ[ℤ])

def actual : Realization signature :=
  realize signature (fun _ p r => p.2 r) (fun e => nomatch e)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {M : ℕ} (hM : 2 ≤ M) (s : Fin M → ℍ[ℤ]),
    (∀ r, IsQ8 (O.readout () ⟨M, s⟩ r)) → ∀ (u : ℍ[ℤ]) (hu : Noncentral u),
    ∃ τ : ℤ, 0 < τ ∧ τ < (M : ℤ) ∧ ¬ ((M : ℤ) ∣ τ) ∧
      correlation (by omega) s u hu τ ≠ 0

private theorem constantOne_fails : ¬ arena.Law constantOne := by
  intro h
  let u : ℍ[ℤ] := ⟨0, 1, 0, 0⟩
  have hu : Noncentral u := Or.inl rfl
  obtain ⟨τ, _, _, _, hτ⟩ := h (M := 2) le_rfl (fun _ => 0) (fun _ => Or.inl rfl) u hu
  exact hτ (by simp [correlation])

private theorem actual_depends_on_index : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, fun r => if r = 0 then 1 else -1⟩, 0, 1, ?_⟩
  intro h
  have hr := congrArg QuaternionAlgebra.re h
  change (1 : ℤ) = -1 at hr
  omega

/-- A constant unit readout accepts the zero sequence, whose literal correlations all vanish. -/
def family : Registration arena (type_of% @blake_conjecture_5_2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@blake_conjecture_5_2, constantOne, constantOne_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual constantOne constantOne_fails
  dependence := actual_depends_on_index

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@blake_conjecture_5_2) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52.blake_conjecture_5_2.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p r => p.2 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

namespace OddTransverse

open _root_.Reg.Support.UniverseSingleReadout (sensitivity)
universe v

abbrev arraySignature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ T : Type v, Σ M : ℕ, Σ _r : Fin M, T)
    (fun p => Fin p.2.1 → p.1 → ℍ[ℤ]) (fun _ => ℍ[ℤ])

def arrayReadout : Realization arraySignature.{v} :=
  realize arraySignature (fun _ p A => A p.2.2.1 p.2.2.2) (fun e => nomatch e)

def constantUnit : Realization arraySignature.{v} :=
  realize arraySignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arrayArena : Arena where
  signature := arraySignature.{v}
  Law O := ∀ {T : Type v} [Fintype T] [AddCommGroup T] {M : ℕ}
    (hM : 2 ≤ M) (hT : Odd (Fintype.card T)) (A : Fin M → T → ℍ[ℤ]),
    (∀ r t, IsQ8 (O.readout () ⟨T, M, r, t⟩ A)) → ∀ (u : ℍ[ℤ]) (hu : Noncentral u),
    letI : NeZero M := ⟨by omega⟩
    ∃ τ : Fin M, ∃ s : T, (τ, s) ≠ (0, 0) ∧
      baseCorrelation (by omega) A u hu τ s ≠ 0 ∧
      fullPeriodCorrelation (by omega) A u hu τ s ≠ 0

private theorem constantUnit_fails : ¬ arrayArena.{v}.Law constantUnit := by
  intro h
  let u : ℍ[ℤ] := ⟨0, 1, 0, 0⟩
  have hu : Noncentral u := Or.inl rfl
  obtain ⟨τ, s, _, hbase, _⟩ := h (T := PUnit.{v+1}) (M := 2) le_rfl
    (by simp) (fun _ _ => 0) (fun _ _ => Or.inl rfl) u hu
  exact hbase (by simp [baseCorrelation])

private theorem arrayReadout_depends : ObservationalDependence arraySignature.{v} arrayReadout := by
  intro role
  refine ⟨⟨PUnit.{v+1}, 2, 0, PUnit.unit⟩, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have hr := congrArg QuaternionAlgebra.re h
  change (0 : ℤ) = 1 at hr
  omega

/-- A constant unit readout lets the zero array pass the alphabet test at every index. -/
def family : Registration arrayArena.{v} (type_of% @odd_transverse_nonvanishing.{v}) where
  actual := arrayReadout
  bridge := Iff.rfl
  variation := ⟨@odd_transverse_nonvanishing.{v}, constantUnit, constantUnit_fails⟩
  sensitivity := sensitivity arrayArena.Law arrayReadout constantUnit constantUnit_fails
  dependence := arrayReadout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@odd_transverse_nonvanishing.{v}) (Realization arraySignature.{v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52.odd_transverse_nonvanishing.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52.OddTransverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arrayArena.{v}⟩
  objectArena := .source ⟨arrayArena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arrayArena.{v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arraySignature (fun _ p A => A p.2.2.1 p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52
    definition := none
    coordinates := #[0, 3, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end OddTransverse

end Reg.D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52
