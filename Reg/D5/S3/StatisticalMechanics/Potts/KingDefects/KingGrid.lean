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

namespace oneDefect_iff

local instance {n k : ℕ} {C : Type} [DecidableEq C] (f : Cell n k → C) :
    Decidable (OneDefect f) := by
  unfold OneDefect
  infer_instance

abbrev signature : Signature.{1, 0, 0, 0, 0} where
  Params := Σ n : ℕ, Σ k : ℕ, Σ C : Type, DecidableEq C
  State p := Cell p.1 p.2.1 → p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p f =>
    letI := p.2.2.2
    decide (OneDefect f)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k : ℕ} {C : Type} [d : DecidableEq C] (f : Cell n k → C),
    (R.readout () ⟨n, k, C, d⟩ f = true) ↔ ∃! e, mono f e

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx : ∃! e : Edge 1 2, mono (fun _ : Cell 1 2 => false) e :=
    (oneDefect_iff _).mp (by decide +kernel)
  have hb := (@h 1 2 Bool inferInstance (fun _ => false)).mpr hx
  exact Bool.noConfusion hb

def family : Registration arena (type_of% @oneDefect_iff.{0}) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using (@oneDefect_iff.{0}),
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, 2, Bool, inferInstance⟩, (fun _ => false), (fun p => p.2 == 0), ?_⟩
    change decide (OneDefect (fun _ : Cell 1 2 => false)) ≠
      decide (OneDefect (fun p : Cell 1 2 => p.2 == 0))
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@oneDefect_iff.{0}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.oneDefect_iff.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid.oneDefect_iff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => letI := p.2.2.2; decide (OneDefect x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := true
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end oneDefect_iff

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
