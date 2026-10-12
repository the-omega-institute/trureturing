import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.CyclicTriangleDisk
import Reg.Support.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Gluing.CyclicTriangleDisk
open LeanInformationAudit
open scoped Topology Fin.NatCast
namespace Reg.D5.S3.Geometry.Gluing.CyclicTriangleDisk
noncomputable section
abbrev Params := {n : ℕ // n ≠ 0}
instance (p : Params) : NeZero p.val := ⟨p.property⟩
def origin : Point 1 := apex 0
def boundary : Point 1 := (0, ⟨(0,1), by norm_num⟩)
private theorem normal_distinct : normal origin ≠ normal boundary := by
  simp [normal, origin, boundary, radius, apex]
private theorem unrelated : ¬ Related origin boundary := by
  rw [related_iff_normal_eq]
  exact normal_distinct
private theorem radial_distinct : radial origin ≠ radial boundary := by
  intro h
  exact unrelated ((radial_eq_iff_related origin boundary).mp h)
private def zeroDisk : Disk := ⟨0, by norm_num⟩
private theorem disk_nontrivial : (⟨1, by norm_num⟩ : Disk) ≠ zeroDisk := by
  intro h
  have := congrArg Subtype.val h
  norm_num [zeroDisk] at this

namespace normalAudit
abbrev signature : Signature where
  Params := Params
  State p := Point p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Point p.val)
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ p x => @normal p.val _ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (x y : Point n), Related x y ↔ R.readout () ⟨n, NeZero.ne n⟩ x = R.readout () ⟨n, NeZero.ne n⟩ y
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact unrelated ((h origin boundary).mpr rfl)
def registration : Registration arena (type_of% (@related_iff_normal_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@related_iff_normal_eq, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨⟨1, by decide⟩, origin, boundary, normal_distinct⟩
def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@related_iff_normal_eq)
    (type_of% (realize signature (fun _ p x => @normal p.val _ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.CyclicTriangleDisk.related_iff_normal_eq.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.CyclicTriangleDisk.normalAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => @normal p.val _ x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.CyclicTriangleDisk,
    definition := none,
    coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms registration
end normalAudit

namespace radialAudit
abbrev signature : Signature where
  Params := Params
  State p := Point p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ p x => @radial p.val _ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (x y : Point n), R.readout () ⟨n, NeZero.ne n⟩ x = R.readout () ⟨n, NeZero.ne n⟩ y ↔ Related x y
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact unrelated ((h origin boundary).mp rfl)
def registration : Registration arena (type_of% (@radial_eq_iff_related)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@radial_eq_iff_related, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨⟨1, by decide⟩, origin, boundary, radial_distinct⟩
def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radial_eq_iff_related)
    (type_of% (realize signature (fun _ p x => @radial p.val _ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.CyclicTriangleDisk.radial_eq_iff_related.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.CyclicTriangleDisk.radialAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => @radial p.val _ x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.CyclicTriangleDisk,
    definition := none,
    coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms registration
end radialAudit

namespace normAudit
abbrev signature : Signature where
  Params := Params
  State p := Point p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ p x => @radial p.val _ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (x : Point n), ‖R.readout () ⟨n, NeZero.ne n⟩ x‖ = radius x
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h boundary
  norm_num [rejected,realize,boundary,radius] at hh
def registration : Registration arena (type_of% (@radial_norm)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@radial_norm, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨⟨1, by decide⟩, origin, boundary, radial_distinct⟩
def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radial_norm)
    (type_of% (realize signature (fun _ p x => @radial p.val _ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.CyclicTriangleDisk.radial_norm.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.CyclicTriangleDisk.normAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => @radial p.val _ x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.CyclicTriangleDisk,
    definition := none,
    coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms registration
end normAudit

namespace homeomorphAudit
abbrev signature : Signature where
  Params := Params
  State p := Fan p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Disk
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ p x => @quotientRadial p.val _ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => zeroDisk) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n], IsHomeomorph (R.readout () ⟨n, NeZero.ne n⟩)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h (n := 1)).surjective
  obtain ⟨q, hq⟩ := hs ⟨1, by norm_num⟩
  exact disk_nontrivial hq.symm
def registration : Registration arena (type_of% (@quotientRadial_isHomeomorph)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotientRadial_isHomeomorph, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, by decide⟩, Quotient.mk (seamSetoid 1) origin,
      Quotient.mk (seamSetoid 1) boundary, ?_⟩
    intro h
    exact radial_distinct (congrArg Subtype.val h)
def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quotientRadial_isHomeomorph)
    (type_of% (realize signature (fun _ p x => @quotientRadial p.val _ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.CyclicTriangleDisk.quotientRadial_isHomeomorph.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.CyclicTriangleDisk.homeomorphAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => @quotientRadial p.val _ x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.CyclicTriangleDisk,
    definition := none,
    coordinates := #[0],
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms registration
end homeomorphAudit
end
end Reg.D5.S3.Geometry.Gluing.CyclicTriangleDisk
