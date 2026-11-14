import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity
import Reg.Support.DependentFamily

/-! Source-bound matrix-input audits with whole-family interventions. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity

@[reducible] def signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  have h := congrFun (congrFun he 0) 0
  exact zero_ne_one h

private theorem sensitivity (Law : Realization signature → Prop)
    (hbad : ¬ Law rejected) : Sensitivity ⟨signature, Law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, hbad⟩
    intro j hji
    cases i; cases j
    exact (hji rfl).elim
  · intro e
    exact nomatch e

namespace Expansion

def arena : Arena where
  signature := signature
  Law R := ∀ {d g : ℕ} (K : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) (X : Matrix (Fin d) (Fin d) ℂ),
    (MatrixMap.of_kraus K K)^[m] (R.readout () d X) =
      ∑ w : Fin m → Fin g, word K m w * X * (word K m w)ᴴ

private theorem actual_law : arena.Law actual := by
  exact @iterate_eq_word_sum

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (fun _ : Fin 0 => (0 : Matrix (Fin 1) (Fin 1) ℂ)) 0 1
  have hh := congrFun (congrFun he 0) 0
  simp [rejected, realize, word] at hh

def family : Registration arena (type_of% (@iterate_eq_word_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@iterate_eq_word_sum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity.Expansion.unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity.Expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Expansion

namespace Strict

def arena : Arena where
  signature := signature
  Law R := ∀ {d g : ℕ} (K : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) (_hspan : wordSpan K m = ⊤)
    (X : Matrix (Fin d) (Fin d) ℂ) (_hX : X.PosSemidef) (_hne : X ≠ 0),
    ((MatrixMap.of_kraus K K)^[m] (R.readout () d X)).PosDef

private theorem actual_law : arena.Law actual := by
  exact @iterate_posDef_of_wordSpan_eq_top

private theorem scalar_span : wordSpan (fun _ : Fin 0 => (0 : Matrix (Fin 1) (Fin 1) ℂ)) 0 = ⊤ := by
  apply top_unique
  intro A _
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      wordSpan (fun _ : Fin 0 => (0 : Matrix (Fin 1) (Fin 1) ℂ)) 0 :=
    Submodule.subset_span ⟨Fin.elim0, rfl⟩
  have he : A = A 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    simp
  rw [he]
  exact Submodule.smul_mem _ _ h1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := h (fun _ : Fin 0 => (0 : Matrix (Fin 1) (Fin 1) ℂ)) 0 scalar_span
    1 Matrix.PosSemidef.one (by simp)
  have hq := hp.dotProduct_mulVec_pos (x := fun _ => 1) (by
    intro he
    have hh := congrFun he (0 : Fin 1)
    simpa using hh)
  simp [rejected, realize] at hq

def family : Registration arena (type_of% (@iterate_posDef_of_wordSpan_eq_top)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@iterate_posDef_of_wordSpan_eq_top) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity.Strict.unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity.Strict.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Strict

end Reg.D5.S3.Quantum.QuantumChannels.KrausWordStrictPositivity
