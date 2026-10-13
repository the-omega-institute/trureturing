import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Hiai.SpectralNonconcavity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology

namespace Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
noncomputable section
open Classical

namespace root_algebra

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v ↦ decide (0 < v)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v w : ℝ) (hv : R.readout () () v = true),
    0 < radius u v w ∧
    lowerRoot u v w < upperRoot u v w ∧
    upperRoot u v w * lowerRoot u v w = u * w - v ^ (2 : ℕ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law 0 0 0 rfl).1
  norm_num [radius] at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.root_algebra)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.root_algebra), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.root_algebra)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.root_algebra.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.root_algebra.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end root_algebra

namespace scaled_upperRoot

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z ↦ decide (0 ≤ z)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (z u v w : ℝ) (hz : R.readout () () z = true),
    z * upperRoot u v w = upperRoot (z * u) (z * v) (z * w)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (-1) 0 0 2 rfl
  norm_num [upperRoot, radius] at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scaled_upperRoot)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scaled_upperRoot), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), -1, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scaled_upperRoot)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.scaled_upperRoot.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.scaled_upperRoot.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end scaled_upperRoot

namespace slope_factor

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M ↦ decide (0 < M)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M m z c α : ℝ) (hM : R.readout () () M = true) (hm : 0 < m)
    (hz : 0 < z) (hc : c = z * M) (hne : m ≠ M),
    (M ^ α - m ^ α) / (M - m) =
      c ^ (α - 1) * z ^ (1 - α) * (1 - (m / M) ^ α) / (1 - m / M)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law 0 1 1 0 2 rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.slope_factor)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.slope_factor), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.slope_factor)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.slope_factor.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.slope_factor.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end slope_factor

namespace interior_gap

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p ↦ decide (0 < p)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α p : ℝ) (hα : 0 < α) (hαh : α < 1 / 2) (hp : R.readout () () p = true),
    0 < interior α p ∧ interior α p ≤ 1 / 4 ∧
      (((1 - interior α p) ^ p + interior α p ^ p) / 2) ^ ((1 - α) / p) <
        (2 : ℝ) ^ (-α / p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law (1 / 4) 0 (by norm_num) (by norm_num) rfl).2.2
  norm_num at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.interior_gap)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.interior_gap), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.interior_gap)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.interior_gap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.interior_gap.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end interior_gap

namespace scale_square

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s ↦ scale p s) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p s : ℝ) (hs : 0 ≤ s), R.readout () p s ^ (2 : ℕ) = s ^ p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law 2 1 (by norm_num)
  norm_num [rejected, realize] at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_square)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_square, rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, scale]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_square)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_square.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.scale_square.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end scale_square

namespace scale_fourth

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s ↦ scale p s) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p s : ℝ) (hs : 0 ≤ s), R.readout () p s ^ (4 : ℕ) = (s ^ (2 : ℕ)) ^ p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law 2 1 (by norm_num)
  norm_num [rejected, realize] at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_fourth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_fourth, rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, scale]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_fourth)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.scale_fourth.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.scale_fourth.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end scale_fourth

namespace entry_facts

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s ↦ decide (0 < s)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p s : ℝ) (hp : 0 < p) (hs : R.readout () () s = true) (hs1 : s < 1 / 2),
    0 < scale p s ∧ 0 < entryX p s ∧ 0 < entryA p s ∧ 0 < entryB p s ∧
    0 < entryE p s ∧ 0 < entryC p s ∧
    entryE p s ^ (2 : ℕ) = entryX p s * (1 - s) ^ p ∧
    entryA p s ^ (2 : ℕ) - entryB p s ^ (2 : ℕ) = (1 - s) ^ p * scale p s ^ (2 : ℕ) ∧
    entryC p s ^ (2 : ℕ) = entryA p s * (entryX p s + scale p s ^ (4 : ℕ)) +
      2 * scale p s ^ (3 : ℕ) * entryE p s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law 2 0 (by norm_num) rfl (by norm_num)).1
  norm_num [scale] at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_facts)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_facts), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_facts)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_facts.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.entry_facts.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end entry_facts

namespace small_interval

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s ↦ decide (0 < s)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ false) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ᶠ s : ℝ in 𝓝[>] 0, R.readout () () s = true ∧ s < 1 / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law
  simp only [rejected, realize, Bool.false_eq_true, false_and] at h
  exact (Filter.Eventually.exists h).elim (fun _ hf ↦ hf)

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.small_interval)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.small_interval), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.small_interval)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.small_interval.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.small_interval.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end small_interval

namespace entry_limits

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p ↦ decide (0 < p)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℝ) (hp : R.readout () () p = true),
    Tendsto (scale p) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (entryX p) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (entryE p) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (entryC p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (entryU p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (entryV p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (scaledW p) (𝓝[>] 0) (𝓝 (1 / k))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law 0 rfl).1
  have h1 : Tendsto (scale 0) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    change Tendsto (fun s : ℝ ↦ s ^ (0 / 2 : ℝ)) (𝓝[>] 0) (𝓝 1)
    simpa only [zero_div, Real.rpow_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] 0) (𝓝 1))
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique h h1
  norm_num at he

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_limits)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_limits), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_limits)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.entry_limits.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.entry_limits.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end entry_limits

namespace finite_factor_limits

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ α ↦ decide (α < 1)) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ true) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α p : ℝ) (hα : 0 < α) (hα1 : R.readout () () α = true) (hp : 0 < p),
    Tendsto (largeScale p) (𝓝[>] 0) (𝓝 (1 / k)) ∧
    Tendsto (small p) (𝓝[>] 0) (𝓝 k) ∧
    Tendsto (ratio p) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (slope α p) (𝓝[>] 0) (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law 1 2 (by norm_num) rfl (by norm_num)).2.2.2
  have hq := (finite_factor_limits (1 / 2) 2 (by norm_num)
    (by norm_num) (by norm_num)).2.2.1
  have hne : ∀ᶠ s : ℝ in 𝓝[>] 0, ratio 2 s ≠ 1 :=
    hq.eventually (eventually_ne_nhds (by norm_num : (0 : ℝ) ≠ 1))
  have h1 : Tendsto (slope 1 2) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).congr'
    filter_upwards [hne] with s hs
    simp only [slope, sub_self, Real.rpow_zero, sub_self, zero_add,
      Real.rpow_one, one_mul]
    exact (div_self (sub_ne_zero.mpr (Ne.symm hs))).symm
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique h h1
  norm_num at he

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.finite_factor_limits)) where
  actual := actual
  bridge := by
    constructor <;> intro source <;>
      simpa only [arena, actual, realize, decide_eq_true_eq] using source
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.finite_factor_limits), rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize] <;> intro he <;> cases he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.finite_factor_limits)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.finite_factor_limits.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.finite_factor_limits.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end finite_factor_limits

namespace k_square_power

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ α ↦ k ^ α) (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α : ℝ), R.readout () () α * k ^ α = (2 : ℝ) ^ (-α)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law 0
  norm_num [rejected, realize] at h

def evidence : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.k_square_power)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.k_square_power, rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j hj ↦ (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i ↦ nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    have hk2 : k ^ (2 : ℕ) = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
    change k ^ (0 : ℝ) ≠ k ^ (2 : ℝ)
    rw [Real.rpow_zero, Real.rpow_two, hk2]
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SpectralNonconcavity.k_square_power)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.SpectralNonconcavity.k_square_power.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars.k_square_power.evidence
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
    owner := `D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end k_square_power

end
end Reg.D5.S3.Quantum.Hiai.SpectralNonconcavityScalars
