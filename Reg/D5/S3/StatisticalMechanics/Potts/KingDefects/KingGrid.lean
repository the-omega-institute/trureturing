import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-equivalent readout laws for king-graph defect counts. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid

noncomputable section

namespace labelled_eq_twentyFour

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 24 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (24 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k),
    L n k = R.readout () () (T n k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 4 4 (by norm_num) (by norm_num)
  have ha := labelled_eq_twentyFour 4 4 (by norm_num) (by norm_num)
  omega

def family : Registration arena (type_of% @labelled_eq_twentyFour) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@labelled_eq_twentyFour, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (24 * (0 : ℕ)) ≠ (24 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@labelled_eq_twentyFour) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.labelled_eq_twentyFour.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.labelled_eq_twentyFour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 24 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end labelled_eq_twentyFour

namespace sum_edges

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Σ n : ℕ, Σ k : ℕ, Edge n k → ℕ)
    (fun p => Edge p.1 p.2.1) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p e => p.2.2 e) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p e => p.2.2 e + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k : ℕ} (F : Edge n k → ℕ),
    (∑ e, R.readout () ⟨n, k, F⟩ e) =
      (∑ i : Fin n, ∑ j : Fin (k - 1), F (.H i j)) +
      (∑ i : Fin (n - 1), ∑ j : Fin k, F (.V i j)) +
      (∑ i : Fin (n - 1), ∑ j : Fin (k - 1), F (.D i j)) +
      (∑ i : Fin (n - 1), ∑ j : Fin (k - 1), F (.A i j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h 2 2 (fun _ => 0)
  have hc : Fintype.card (Edge 2 2) = 6 := by decide +kernel
  norm_num [arena, rejected, realize, Finset.sum_const, hc] at hb

def family : Registration arena (type_of% @sum_edges) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_edges, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨2, 2, fun e => if e = .H 0 0 then 0 else 1⟩,
      (Edge.H 0 0 : Edge 2 2), (Edge.V 0 0 : Edge 2 2), ?_⟩
    change (if (Edge.H 0 0 : Edge 2 2) = .H 0 0 then 0 else 1) ≠
      (if (Edge.V 0 0 : Edge 2 2) = .H 0 0 then 0 else 1)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sum_edges) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.sum_edges.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.sum_edges.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => p.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "body"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end sum_edges


end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
