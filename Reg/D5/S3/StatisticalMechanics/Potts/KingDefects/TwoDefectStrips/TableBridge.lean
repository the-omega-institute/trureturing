import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Faithful readout laws for the literal transfer interfaces. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
structure Params where
  q : ℕ
  k : ℕ
  M : ℕ
  P : (Fin k → Fin q) → Prop
  dec : DecidablePred P
  c : (Fin k → Fin q) → Fin M
attribute [instance] Params.dec
def observation (p : Params) (s : Fin p.M) : ℕ :=
  (((List.ofFn (fun i : Fin (p.q^p.k) => finFunctionFinEquiv.symm i)).filterMap
    (fun r => if p.P r then some (p.c r) else none)).insertionSort (· ≤ ·)).count s
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun p => Fin p.M) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p s => observation p s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p s => observation p s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Params) (s : Fin p.M), R.readout () p s =
    ∑ r : Fin p.k → Fin p.q, if p.P r ∧ p.c r = s then 1 else 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ⟨1,0,1,(fun _ => True),(fun _ => isTrue trivial),(fun _ => 0)⟩ 0
  norm_num [rejected, realize, observation] at hb

def family : Registration arena (type_of% @count_successors) where
  actual := actual
  bridge := by
    constructor
    · intro h p s; exact h p.P p.c s
    · intro h q k M P dec c s; exact h ⟨q,k,M,P,dec,c⟩ s
  variation := ⟨fun p s => count_successors p.P p.c s, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro ⟨⟩
    refine ⟨⟨1,0,2,(fun _ => True),(fun _ => isTrue trivial),(fun _ => 0)⟩, 0, 1, ?_⟩
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@count_successors) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
                    stateBinder := 6
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
