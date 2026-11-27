import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Faithful readout laws for the literal transfer interfaces. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace Rows
structure Params where
  q : ℕ
  k : ℕ
  H : Finset (Fin k × Fin k)
  V : Finset (Fin k × Fin k)
  n : ℕ
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params
    (fun p => Fin (p.n+1) → Row p.q p.k) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p f => defects p.H p.V (List.ofFn f)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p f => defects p.H p.V (List.ofFn f) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Params) (f : Fin (p.n+1) → Row p.q p.k),
    R.readout () p f = (∑ i, bondDefects p.H (f i) (f i)) +
      ∑ i : Fin p.n, bondDefects p.V (f i.castSucc) (f i.succ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ⟨1, 1, ∅, ∅, 0⟩ (fun _ _ => 0)
  norm_num [rejected, realize, defects, tailDefects, bondDefects] at hb
def family : Registration arena (type_of% @defects_rows) where
  actual := actual
  bridge := by
    constructor
    · intro h p f; exact h p.H p.V p.n f
    · intro h q k H V n f; exact h ⟨q,k,H,V,n⟩ f
  variation := ⟨fun p f => defects_rows p.H p.V p.n f, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro ⟨⟩
    refine ⟨⟨2, 1, ∅, {(0,0)}, 1⟩, (fun _ _ => 0), (fun i _ => i), ?_⟩
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@defects_rows) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
                    stateBinder := 5
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Rows
namespace Literal
structure Params where
  k : ℕ
  H : Finset (Fin k × Fin k)
  V : Finset (Fin k × Fin k)
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p n => literalCount (q := 4) p.H p.V 2 (n+1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p n => literalCount (q := 4) p.H p.V 2 (n+1) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Params),
    (∀ r : Row 4 p.k, bondDefects p.H r r =
      ∑ j : Fin (p.k-1), if r (_root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.lo j) =
        r (_root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.hi j) then 1 else 0) →
    (∀ r t : Row 4 p.k, bondDefects p.V r t =
      (∑ j, if r j = t j then 1 else 0) +
      (∑ j : Fin (p.k-1), if r (_root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.lo j) =
        t (_root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.hi j) then 1 else 0) +
      ∑ j : Fin (p.k-1), if r (_root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.hi j) =
        t (_root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.lo j) then 1 else 0) →
    ∀ n : ℕ, R.readout () p n =
      _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid.L (n+1) p.k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ⟨0,∅,∅⟩ (by intro r; simp [bondDefects])
    (by intro r t; simp [bondDefects]) 0
  have ha := literal_bridge (k := 0) ∅ ∅ (by intro r; simp [bondDefects])
    (by intro r t; simp [bondDefects]) 0
  change literalCount (q := 4) (k := 0) ∅ ∅ 2 1 + 1 =
    _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid.L 1 0 at hb
  change literalCount (q := 4) (k := 0) ∅ ∅ 2 1 =
    _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid.L 1 0 at ha
  rw [← ha] at hb
  exact Nat.succ_ne_self _ hb
def family : Registration arena (type_of% @literal_bridge) where
  actual := actual
  bridge := by
    constructor
    · intro h p hH hV n; exact h p.H p.V hH hV n
    · intro h k H V hH hV n; exact h ⟨k,H,V⟩ hH hV n
  variation := ⟨fun p hH hV n => literal_bridge p.H p.V hH hV n,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro ⟨⟩
    refine ⟨⟨1,{(0,0)},∅⟩, 0, 1, ?_⟩
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@literal_bridge) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge.Literal.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
                    stateBinder := 5
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Literal
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
