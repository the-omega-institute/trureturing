import Reg.Support.FibonacciOriginalSourceWitness.Source155
import Reg.Support.FibonacciFactorCompletion.TailSourceReadouts
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
noncomputable section

abbrev suffixSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : List Label, ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def suffixActual : Realization suffixSignature :=
  realize suffixSignature (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e)

def suffixRejected : Realization suffixSignature :=
  realize suffixSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev suffixArena : Arena.{0,0,0,0,0} where
  signature := suffixSignature
  Law r := ∀ (s e : Guard) (w : List Label) (hw : LegalWord s e w)
    (z : ℝ) (hz : InSupport e z) (p : ℕ), InSupport .G0 (r.readout () ⟨w, z⟩ p)

/-- The legal one-letter word and supported zero also admit states beyond its length. -/
theorem suffix_rejected_law : ¬ suffixArena.Law suffixRejected := by
  intro h
  have supported : InSupport .G0 0 := by
    constructor
    · norm_num
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans tail_arithmetic.2.2.2.2.2.le
  have hh := h .G0 .G0 [Label.L2] rfl 0 supported 2
  have hlo := hh.1
  norm_num [suffixRejected, realize] at hlo

def suffixRegistration : Registration suffixArena (type_of% @suffix_supported) where
  actual := suffixActual
  bridge := Iff.rfl
  variation := ⟨@suffix_supported, suffixRejected, suffix_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    suffixArena.Law suffixActual suffixRejected suffix_rejected_law
  dependence := by
    intro i
    refine ⟨⟨[Label.L2], 0⟩, 0, 1, ?_⟩
    norm_num [suffixActual, realize, compose, branch, shift]

def suffix_supported_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.suffix_supported)
      (type_of% (realize.{0,0,0,0,0} suffixSignature
        (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.suffix_supported_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.suffixRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨suffixArena⟩
  objectArena := .source ⟨suffixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source suffixArena ⟨suffixRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} suffixSignature
    (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms suffixRegistration
#print axioms suffix_supported_registration

/-- Inhabited boundary witnesses use the original real support and ownership. -/
private theorem boundary_supported : InSupport .G0 (-1) := by
  exact ⟨le_refl _, (cut_bounds (0 : Color)).1.trans
    ((cut_bounds (0 : Color)).2.1.le.trans (cut_bounds (0 : Color)).2.2)⟩

private theorem boundary_cell_zero : Cell (fun _ => false) 0 (-1) := by
  apply (cell_flag_interval _ _ _).mpr
  have h := (cut_bounds (0 : Color)).2.1
  norm_num only [Fin.val_zero, zero_add, cut] at h ⊢
  exact ⟨le_refl _, h.le, fun _ => trivial, fun _ => rfl⟩

private theorem boundary_cell_one : ¬ Cell (fun _ => false) 1 (-1) := by
  intro h
  have impossible : (0 : Color) = 1 := boundary_cell_zero.2.symm.trans h.2
  exact (by decide : (0 : Color) ≠ 1) impossible

private theorem boundary_owned_zero : OwnedColor (fun _ => false) 0 0 (-1) := by
  exact ⟨boundary_supported, -1, boundary_cell_zero, by norm_num⟩

private theorem boundary_owned_one : ¬ OwnedColor (fun _ => false) 0 1 (-1) := by
  rintro ⟨_, u, hu, he⟩
  have hz : (-1 : ℝ) - u = 0 := abs_nonpos_iff.mp he
  have hu' : u = -1 := by linarith
  exact boundary_cell_one (hu' ▸ hu)

private theorem boundary_expanded_zero : ClosedExpanded 0 0 (-1) := by
  refine ⟨boundary_supported, ?_, ?_⟩
  · norm_num [cut]
  · have h := (cut_bounds (0 : Color)).2.1.le
    simpa only [Fin.val_zero, zero_add, cut, add_zero] using h

private theorem boundary_expanded_one : ¬ ClosedExpanded 0 1 (-1) := by
  intro h
  have hc := (cut_bounds (0 : Color)).2.1
  have hlo := h.2.1
  norm_num only [Fin.val_zero, Fin.val_one, zero_add, cut, sub_zero] at hc hlo
  exact (not_le_of_gt hc) hlo

abbrev cellSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Ownership (fun _ => Color) (fun _ => ℝ → Prop)

def cellActual : Realization cellSignature :=
  realize cellSignature (fun _ o c => Cell o c) (fun e => nomatch e)

def cellRejected : Realization cellSignature :=
  realize cellSignature (fun _ o _ => Cell o 1) (fun e => nomatch e)

abbrev cellArena : Arena.{0,0,0,0,0} where
  signature := cellSignature
  Law r := ∀ (o : Ownership) (c : Color) (u : ℝ),
    r.readout () o c u ↔ FlagInterval (cut c.val) (cut (c.val + 1))
      (lowerOwned o c) (upperOwned o c) u

theorem cell_rejected_law : ¬ cellArena.Law cellRejected := by
  intro h
  exact boundary_cell_one ((h (fun _ => false) 0 (-1)).mpr
    ((cell_flag_interval _ _ _).mp boundary_cell_zero))

def cellRegistration : Registration cellArena (type_of% @cell_flag_interval) where
  actual := cellActual
  bridge := Iff.rfl
  variation := ⟨@cell_flag_interval, cellRejected, cell_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    cellArena.Law cellActual cellRejected cell_rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => false), 0, 1, ?_⟩
    intro heq
    exact boundary_cell_one ((congrFun heq (-1)).mp boundary_cell_zero)

abbrev ownedSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : Ownership, ℝ)
    (fun _ => Color) (fun _ => ℝ → Prop)

def ownedActual : Realization ownedSignature :=
  realize ownedSignature (fun _ p c => OwnedColor p.1 p.2 c) (fun e => nomatch e)

def ownedRejected : Realization ownedSignature :=
  realize ownedSignature (fun _ p _ => OwnedColor p.1 p.2 1) (fun e => nomatch e)

private theorem owned_dependence : ObservationalDependence ownedSignature ownedActual := by
  intro i
  refine ⟨⟨(fun _ => false), 0⟩, 0, 1, ?_⟩
  intro heq
  exact boundary_owned_one ((congrFun heq (-1)).mp boundary_owned_zero)

abbrev ownedIntervalArena : Arena.{0,0,0,0,0} where
  signature := ownedSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (c : Color) (z : ℝ),
    r.readout () ⟨o, θ⟩ c z ↔ InSupport .G0 z ∧
      FlagInterval (cut c.val - θ) (cut (c.val + 1) + θ)
        (lowerOwned o c) (upperOwned o c) z

theorem owned_interval_rejected_law : ¬ ownedIntervalArena.Law ownedRejected := by
  intro h
  exact boundary_owned_one ((h (fun _ => false) 0 (le_refl _) 0 (-1)).mpr
    ((owned_color_interval _ 0 (le_refl _) _ _).mp boundary_owned_zero))

def ownedIntervalRegistration :
    Registration ownedIntervalArena (type_of% @owned_color_interval) where
  actual := ownedActual
  bridge := Iff.rfl
  variation := ⟨@owned_color_interval, ownedRejected, owned_interval_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    ownedIntervalArena.Law ownedActual ownedRejected owned_interval_rejected_law
  dependence := owned_dependence

abbrev ownedErrorArena : Arena.{0,0,0,0,0} where
  signature := ownedSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (c : Color) (z : ℝ) (hz : InSupport .G0 z),
    r.readout () ⟨o, θ⟩ c z ↔ ∃ e : ℝ, |e| ≤ θ ∧ observe o z e = c

theorem owned_error_rejected_law : ¬ ownedErrorArena.Law ownedRejected := by
  intro h
  exact boundary_owned_one ((h (fun _ => false) 0 0 (-1) boundary_supported).mpr
    ((owned_color_error _ 0 _ _ boundary_supported).mp boundary_owned_zero))

def ownedErrorRegistration : Registration ownedErrorArena (type_of% @owned_color_error) where
  actual := ownedActual
  bridge := Iff.rfl
  variation := ⟨@owned_color_error, ownedRejected, owned_error_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    ownedErrorArena.Law ownedActual ownedRejected owned_error_rejected_law
  dependence := owned_dependence

abbrev expandedSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => Color) (fun _ => ℝ → Prop)

def expandedActual : Realization expandedSignature :=
  realize expandedSignature (fun _ θ c => ClosedExpanded θ c) (fun e => nomatch e)

def expandedRejected : Realization expandedSignature :=
  realize expandedSignature (fun _ θ _ => ClosedExpanded θ 1) (fun e => nomatch e)

abbrev expandedArena : Arena.{0,0,0,0,0} where
  signature := expandedSignature
  Law r := ∀ (θ : ℝ) (hθ : 0 ≤ θ) (c : Color) (z : ℝ),
    r.readout () θ c z ↔ InSupport .G0 z ∧
      max (cut c.val-z) (max 0 (z-cut (c.val+1))) ≤ θ

theorem expanded_rejected_law : ¬ expandedArena.Law expandedRejected := by
  intro h
  exact boundary_expanded_one ((h 0 (le_refl _) 0 (-1)).mpr
    ((expanded_distance_formula 0 (le_refl _) _ _).mp boundary_expanded_zero))

def expandedRegistration : Registration expandedArena (type_of% @expanded_distance_formula) where
  actual := expandedActual
  bridge := Iff.rfl
  variation := ⟨@expanded_distance_formula, expandedRejected, expanded_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    expandedArena.Law expandedActual expandedRejected expanded_rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    intro heq
    exact boundary_expanded_one ((congrFun heq (-1)).mp boundary_expanded_zero)

def cell_flag_interval_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cell_flag_interval)
      (type_of% (realize.{0,0,0,0,0} cellSignature
        (fun _ o c => Cell o c) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cell_flag_interval_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cellRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨cellArena⟩
  objectArena := .source ⟨cellArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cellArena ⟨cellRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} cellSignature
        (fun _ o c => Cell o c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cellRegistration
#print axioms cell_flag_interval_registration

def owned_color_interval_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.owned_color_interval)
      (type_of% (realize.{0,0,0,0,0} ownedSignature
        (fun _ p c => OwnedColor p.1 p.2 c) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.owned_color_interval_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedIntervalRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨ownedIntervalArena⟩
  objectArena := .source ⟨ownedIntervalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ownedIntervalArena ⟨ownedIntervalRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} ownedSignature
        (fun _ p c => OwnedColor p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms ownedIntervalRegistration
#print axioms owned_color_interval_registration

def owned_color_error_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.owned_color_error)
      (type_of% (realize.{0,0,0,0,0} ownedSignature
        (fun _ p c => OwnedColor p.1 p.2 c) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.owned_color_error_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedErrorRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨ownedErrorArena⟩
  objectArena := .source ⟨ownedErrorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ownedErrorArena ⟨ownedErrorRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} ownedSignature
        (fun _ p c => OwnedColor p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms ownedErrorRegistration
#print axioms owned_color_error_registration

def expanded_distance_formula_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.expanded_distance_formula)
      (type_of% (realize.{0,0,0,0,0} expandedSignature
        (fun _ θ c => ClosedExpanded θ c) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.expanded_distance_formula_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.expandedRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨expandedArena⟩
  objectArena := .source ⟨expandedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source expandedArena ⟨expandedRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} expandedSignature
        (fun _ θ c => ClosedExpanded θ c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms expandedRegistration
#print axioms expanded_distance_formula_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal156
noncomputable section


def tail_arithmetic_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.tail_arithmetic)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ x => x^2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal156.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal156.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ x => x^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms tail_arithmetic_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal156

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal161
noncomputable section

def cut_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cut_bounds)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ c => cut c.val) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal161.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal161.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ c => cut c.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms cut_bounds_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal161

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal158
noncomputable section

def finite_approximation_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_approximation)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ z x => z - x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal158.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal158.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ z x => z - x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms finite_approximation_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal158

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal170
noncomputable section

def compose_strict_inside_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.compose_strict_inside)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ w x => compose w x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal170.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal170.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ w x => compose w x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms compose_strict_inside_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal170



namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal157
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

def lawful_tail_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.lawful_tail)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal157.lawful_tail_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal157.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms lawful_tail_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal157

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal159
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

def finite_tail_interior_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_tail_interior)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal159.finite_tail_interior_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal159.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "body", "arg", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms finite_tail_interior_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal159

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal160
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

def prepend_legal_tail_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.prepend_legal_tail)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal160.prepend_legal_tail_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal160.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms prepend_legal_tail_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal160

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal168
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

def competingT_mem_actual_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingT_mem_actual)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ x => x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal168.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal168.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms competingT_mem_actual_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal168

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal171
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

def certificate_actual_slots_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.certificate_actual_slots)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ x => x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal171.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal171.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms certificate_actual_slots_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal171

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal172
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

def block_supply_append_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.block_supply_append)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ x => x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal172.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal172.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms block_supply_append_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal172

namespace Reg.Support.FibonacciOriginalSourceWitness.Source155
noncomputable section

def original_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competing_tail_orbit_criterion)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ q x => q.2+q.1*(x-q.2)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.Support.FibonacciOriginalSourceWitness.Source155.original_unit
  realizationName := `Reg.Support.FibonacciOriginalSourceWitness.Source155.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ q x => q.2+q.1*(x-q.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value", "body"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_registration
end
end Reg.Support.FibonacciOriginalSourceWitness.Source155

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
noncomputable section
def disconnectedSet : Set ℝ := {z | z = 0 ∨ z = 2}
theorem disconnected_set : ¬ disconnectedSet.OrdConnected := by
  intro h
  have impossible := h.out (show (0 : ℝ) ∈ disconnectedSet from Or.inl rfl)
    (show (2 : ℝ) ∈ disconnectedSet from Or.inr rfl) (show (1 : ℝ) ∈ Set.Icc 0 2 by norm_num)
  norm_num [disconnectedSet] at impossible
abbrev ownedConnectedArena : Arena.{0,0,0,0,0} where
  signature := ownedSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (c : Color),
    {z | r.readout () ⟨o,θ⟩ c z}.OrdConnected
def ownedConnectedRejected : Realization ownedSignature :=
  realize ownedSignature (fun _ _ _ => disconnectedSet) (fun e => nomatch e)
theorem owned_connected_rejected_law : ¬ ownedConnectedArena.Law ownedConnectedRejected :=
  fun law => disconnected_set (law (fun _ => false) 0 le_rfl 0)
def ownedConnectedEvidence : Registration ownedConnectedArena (type_of% @owned_color_ordConnected) where
  actual := ownedActual
  bridge := Iff.rfl
  variation := ⟨@owned_color_ordConnected, ownedConnectedRejected, owned_connected_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity ownedConnectedArena.Law ownedActual ownedConnectedRejected owned_connected_rejected_law
  dependence := owned_dependence
abbrev competingParams := Σ _ : Ownership, Σ _ : ℝ, Σ _ : Guard, Σ _ : List Label, Σ _ : List Label, List Color
abbrev competingSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature competingParams (fun _ => Bool → List Color) (fun _ => Set ℝ)
def competingActual : Realization competingSignature :=
  realize competingSignature (fun _ p W => CompetingT p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 W) (fun e => nomatch e)
abbrev competingConnectedArena : Arena.{0,0,0,0,0} where
  signature := competingSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color),
    (r.readout () ⟨o,θ,s,Q,V,h⟩ W).OrdConnected
def competingRejected : Realization competingSignature :=
  realize competingSignature (fun _ _ _ => disconnectedSet) (fun e => nomatch e)
theorem competing_rejected_law : ¬ competingConnectedArena.Law competingRejected :=
  fun law => disconnected_set (law (fun _ => false) 0 le_rfl .G0 [] [] [] (fun _ => []))
theorem competing_dependence : ObservationalDependence competingSignature competingActual := by
  intro i
  refine ⟨⟨(fun _ => false),0,.G0,[],[],[]⟩, (fun _ => []), (fun _ => [1]), ?_⟩
  have yes : (-1 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => []) := by
    refine ⟨boundary_supported, ?_, ?_⟩ <;> simp
  intro eq
  change CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => []) =
    CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => [1]) at eq
  have bad : (-1 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => [1]) := eq ▸ yes
  exact boundary_owned_one (by simpa [compose] using bad.2.2 false 0 (by decide))
def competingConnectedEvidence : Registration competingConnectedArena (type_of% @competingT_ordConnected) where
  actual := competingActual
  bridge := Iff.rfl
  variation := ⟨@competingT_ordConnected, competingRejected, competing_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity competingConnectedArena.Law competingActual competingRejected competing_rejected_law
  dependence := competing_dependence
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.OwnedConnected
noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.owned_color_ordConnected)
    (type_of% Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedActual) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.OwnedConnected.unit, realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedConnectedEvidence, realizationSource := none, generated := false,
  arena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedConnectedArena⟩, objectArena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedConnectedArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedConnectedArena ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedConnectedEvidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ownedSignature (fun _ p c => OwnedColor p.1 p.2 c) (fun e => nomatch e)), variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.OwnedConnected

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.CompetingConnected
noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingT_ordConnected)
    (type_of% Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingActual) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.CompetingConnected.unit, realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingConnectedEvidence, realizationSource := none, generated := false,
  arena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingConnectedArena⟩, objectArena := .source ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingConnectedArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingConnectedArena ⟨Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingConnectedEvidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competingSignature (fun _ p W => CompetingT p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 W) (fun e => nomatch e)), variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry, definition := none, coordinates := #[0, 1, 3, 4, 5, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.CompetingConnected
