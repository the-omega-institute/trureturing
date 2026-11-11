import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Completion.RawGroupZeroQuotient

namespace Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient
open _root_.D5.S3.Quantum.Completion.RawGroupZeroQuotient
open _root_.D5.S3.Quantum.Completion.RawUnanchoredReplication
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

/-- Observe the truth of the exact conclusion with every source binder retained in Law. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Unit → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ p _ => p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hbad : False := Eq.mp (congrFun he ()) trivial
  exact hbad
private theorem zero_raw {G : Type u} [Group G] :
    RawCost (id : G → G) (fun _ _ => (0 : ℝ)) := by
  constructor <;> intros <;> norm_num

def right_diff_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (a b : G),
    R.readout () () (c a b = c (a * b⁻¹) 1) ()
private theorem right_diff_rejected : ¬ right_diff_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw 1 1
def right_diff_source : Registration right_diff_arena.{u} (type_of% @right_diff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@right_diff.{u}, rejected, right_diff_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity right_diff_arena.Law actual rejected right_diff_rejected
  dependence := dependence

def right_diff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@right_diff.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.right_diff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.right_diff_source
  realizationSource := none
  generated := false
  arena := .source ⟨right_diff_arena⟩
  objectArena := .source ⟨right_diff_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source right_diff_arena ⟨right_diff_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def zero_coset_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a)
    (x z : G) (hz : z ∈ zeroSubgroup h hs),
    R.readout () () (c (x*z) 1 = c x 1) ()
private theorem zero_coset_rejected : ¬ zero_coset_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl) 1 1 rfl
def zero_coset_source : Registration zero_coset_arena.{u} (type_of% @zero_coset.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zero_coset.{u}, rejected, zero_coset_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity zero_coset_arena.Law actual rejected zero_coset_rejected
  dependence := dependence

def zero_coset_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@zero_coset.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.zero_coset.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.zero_coset_source
  realizationSource := none
  generated := false
  arena := .source ⟨zero_coset_arena⟩
  objectArena := .source ⟨zero_coset_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zero_coset_arena ⟨zero_coset_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def independent_representatives_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a)
    (a b z w : G) (hz : z ∈ zeroSubgroup h hs) (hw : w ∈ zeroSubgroup h hs),
    R.readout () () (c (a*z) (b*w) = c a b) ()
private theorem independent_representatives_rejected : ¬ independent_representatives_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl) 1 1 1 1 rfl rfl
def independent_representatives_source : Registration independent_representatives_arena.{u} (type_of% @independent_representatives.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@independent_representatives.{u}, rejected, independent_representatives_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity independent_representatives_arena.Law actual rejected independent_representatives_rejected
  dependence := dependence

def independent_representatives_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@independent_representatives.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.independent_representatives.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.independent_representatives_source
  realizationSource := none
  generated := false
  arena := .source ⟨independent_representatives_arena⟩
  objectArena := .source ⟨independent_representatives_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source independent_representatives_arena ⟨independent_representatives_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def zero_iff_class_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a b : G),
    R.readout () () (c a b = 0 ↔ (QuotientGroup.mk a : G ⧸ zeroSubgroup h hs) = QuotientGroup.mk b) ()
private theorem zero_iff_class_rejected : ¬ zero_iff_class_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl) 1 1
def zero_iff_class_source : Registration zero_iff_class_arena.{u} (type_of% @zero_iff_class.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zero_iff_class.{u}, rejected, zero_iff_class_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity zero_iff_class_arena.Law actual rejected zero_iff_class_rejected
  dependence := dependence

def zero_iff_class_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@zero_iff_class.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.zero_iff_class.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.zero_iff_class_source
  realizationSource := none
  generated := false
  arena := .source ⟨zero_iff_class_arena⟩
  objectArena := .source ⟨zero_iff_class_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zero_iff_class_arena ⟨zero_iff_class_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def marker_classes_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a b : G)
    (hab : (QuotientGroup.mk a : G ⧸ zeroSubgroup h hs) = QuotientGroup.mk b),
    R.readout () () ((QuotientGroup.mk (U a) : G ⧸ zeroSubgroup h hs) = QuotientGroup.mk (U b)) ()
private theorem marker_classes_rejected : ¬ marker_classes_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl) 1 1 rfl
def marker_classes_source : Registration marker_classes_arena.{u} (type_of% @marker_classes.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@marker_classes.{u}, rejected, marker_classes_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity marker_classes_arena.Law actual rejected marker_classes_rejected
  dependence := dependence

def marker_classes_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@marker_classes.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.marker_classes.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.marker_classes_source
  realizationSource := none
  generated := false
  arena := .source ⟨marker_classes_arena⟩
  objectArena := .source ⟨marker_classes_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source marker_classes_arena ⟨marker_classes_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def quotientMarker_mk_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a : G),
    R.readout () () (quotientMarker h hs (QuotientGroup.mk a) = QuotientGroup.mk (U a)) ()
private theorem quotientMarker_mk_rejected : ¬ quotientMarker_mk_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl) 1
def quotientMarker_mk_source : Registration quotientMarker_mk_arena.{u} (type_of% @quotientMarker_mk.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotientMarker_mk.{u}, rejected, quotientMarker_mk_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity quotientMarker_mk_arena.Law actual rejected quotientMarker_mk_rejected
  dependence := dependence

def quotientMarker_mk_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@quotientMarker_mk.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotientMarker_mk.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotientMarker_mk_source
  realizationSource := none
  generated := false
  arena := .source ⟨quotientMarker_mk_arena⟩
  objectArena := .source ⟨quotientMarker_mk_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotientMarker_mk_arena ⟨quotientMarker_mk_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def quotientCost_mk_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a b : G),
    R.readout () () (quotientCost h hs (QuotientGroup.mk a) (QuotientGroup.mk b) = c a b) ()
private theorem quotientCost_mk_rejected : ¬ quotientCost_mk_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl) 1 1
def quotientCost_mk_source : Registration quotientCost_mk_arena.{u} (type_of% @quotientCost_mk.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotientCost_mk.{u}, rejected, quotientCost_mk_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity quotientCost_mk_arena.Law actual rejected quotientCost_mk_rejected
  dependence := dependence

def quotientCost_mk_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@quotientCost_mk.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotientCost_mk.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotientCost_mk_source
  realizationSource := none
  generated := false
  arena := .source ⟨quotientCost_mk_arena⟩
  objectArena := .source ⟨quotientCost_mk_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotientCost_mk_arena ⟨quotientCost_mk_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def quotient_raw_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a),
    R.readout () () (RawCost (quotientMarker h hs) (quotientCost h hs)) ()
private theorem quotient_raw_rejected : ¬ quotient_raw_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl)
def quotient_raw_source : Registration quotient_raw_arena.{u} (type_of% @quotient_raw.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotient_raw.{u}, rejected, quotient_raw_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity quotient_raw_arena.Law actual rejected quotient_raw_rejected
  dependence := dependence

def quotient_raw_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@quotient_raw.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotient_raw.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotient_raw_source
  realizationSource := none
  generated := false
  arena := .source ⟨quotient_raw_arena⟩
  objectArena := .source ⟨quotient_raw_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotient_raw_arena ⟨quotient_raw_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def quotient_symmetric_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}, ∀ (h : RawCost U c) (hs : ∀ a b, c a b = c b a),
    R.readout () () (∀ a b, quotientCost h hs a b = quotientCost h hs b a) ()
private theorem quotient_symmetric_rejected : ¬ quotient_symmetric_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl)
def quotient_symmetric_source : Registration quotient_symmetric_arena.{u} (type_of% @quotient_symmetric.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotient_symmetric.{u}, rejected, quotient_symmetric_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity quotient_symmetric_arena.Law actual rejected quotient_symmetric_rejected
  dependence := dependence

def quotient_symmetric_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@quotient_symmetric.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotient_symmetric.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.quotient_symmetric_source
  realizationSource := none
  generated := false
  arena := .source ⟨quotient_symmetric_arena⟩
  objectArena := .source ⟨quotient_symmetric_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotient_symmetric_arena ⟨quotient_symmetric_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def group19_2_arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G], ∀ (U : G → G) (c : G → G → ℝ) (h : RawCost U c)
    (hs : ∀ a b, c a b = c b a),
    R.readout () () (∃ f : G → ℝ,
      (∀ g, 0 ≤ f g) ∧ (∀ g, f g = c g 1) ∧
      (∀ a b, c a b = f (a*b⁻¹)) ∧ f 1 = 0 ∧ (∀ g, f g⁻¹ = f g) ∧
      (∀ a b z, c (a*z) (b*z) = c a b) ∧
      ∃ Z : Subgroup G, (∀ z, z ∈ Z ↔ f z = 0) ∧
        ∃ hn : Z.Normal, letI : Z.Normal := hn
          (∀ a b z w, z ∈ Z → w ∈ Z → c (a*z) (b*w) = c a b) ∧
          (∀ a b, (QuotientGroup.mk a : G ⧸ Z) = QuotientGroup.mk b →
            (QuotientGroup.mk (U a) : G ⧸ Z) = QuotientGroup.mk (U b)) ∧
          ∃ (V : G ⧸ Z → G ⧸ Z) (d : G ⧸ Z → G ⧸ Z → ℝ),
            (∀ a b, d (QuotientGroup.mk a) (QuotientGroup.mk b) = c a b) ∧
            (∀ a, V (QuotientGroup.mk a) = QuotientGroup.mk (U a)) ∧
            RawCost V d ∧ (∀ a b, d a b = d b a) ∧
            (∀ a b, c a b = 0 ↔ (QuotientGroup.mk a : G ⧸ Z) = QuotientGroup.mk b)) ()
private theorem group19_2_rejected : ¬ group19_2_arena.{u}.Law rejected := by
  intro h
  exact h (G := ULift.{u} Unit) (U := id) (c := fun _ _ => 0) zero_raw (fun _ _ => rfl)
def group19_2_source : Registration group19_2_arena.{u} (type_of% @group19_2.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@group19_2.{u}, rejected, group19_2_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity group19_2_arena.Law actual rejected group19_2_rejected
  dependence := dependence

def group19_2_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@group19_2.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawGroupZeroQuotient.group19_2.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient.group19_2_source
  realizationSource := none
  generated := false
  arena := .source ⟨group19_2_arena⟩
  objectArena := .source ⟨group19_2_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source group19_2_arena ⟨group19_2_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p _ => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Completion.RawGroupZeroQuotient
