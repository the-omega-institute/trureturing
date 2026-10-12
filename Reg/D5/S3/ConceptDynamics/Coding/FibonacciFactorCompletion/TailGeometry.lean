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


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ x => x^2) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := r.readout () () t = 1-t ∧ 0<t ∧ t<1 ∧ 0<g ∧ g<1 ∧ 1<phi

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq : (0 : ℝ) = 1-t := h.1
  have lt := h.2.2.1
  linarith

def evidence : Registration sourceArena (type_of% @tail_arithmetic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tail_arithmetic, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

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

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Color
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ c => cut c.val) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (c : Color),
      -1 ≤ r.readout () () c ∧
      cut c.val < cut (c.val + 1) ∧
      cut (c.val + 1) ≤ phi

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h (0 : Color)).1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cut_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.cut_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : Color), (1 : Color), ?_⟩
    exact ne_of_lt (cut_bounds (0 : Color)).2.1

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

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ z x => z - x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (z : ℝ) (hz : InSupport s z)
    (ε : ℝ) (hε : 0 < ε),
    ∃ (e : Guard) (w : List Label),
      LegalWord s e w ∧ |r.readout () z (coordinate w 0)| < ε

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have supported : InSupport .G0 0 := by
    constructor
    · norm_num
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans tail_arithmetic.2.2.2.2.2.le
  obtain ⟨e, w, _, impossible⟩ := h .G0 0 supported 1 (by norm_num)
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_approximation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_approximation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, realize]

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

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (List Label) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ w x => compose w x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (w : List Label) (lo hi x left right : ℝ)
    (hxlo : lo < x) (hxhi : x < hi)
    (hlo : left ≤ compose w lo ∧ compose w lo ≤ right)
    (hhi : left ≤ compose w hi ∧ compose w hi ≤ right),
    left < r.readout () w x ∧ compose w x < right

theorem source_bridge : (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.compose_strict_inside) ↔
    sourceArena.Law actual := Iff.rfl

theorem positive_law : sourceArena.Law actual := @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.compose_strict_inside

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h [] (-1) 1 0 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num [compose]) (by norm_num [compose])).1
  exact (lt_irrefl (-1 : ℝ)) impossible

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨[], 0, 1, ?_⟩
  norm_num [actual, realize, compose]

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.compose_strict_inside) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

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


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Label) (fun _ => ℝ → ℝ)

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ l => branch l) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => fun _ => (1 : ℝ)) (fun e => nomatch e)

/-- The actual branch functions distinguish two legal label states at zero. -/
theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), Label.L0, Label.L2, ?_⟩
  intro heq
  have h := congrFun heq (0 : ℝ)
  norm_num [actual, realize, branch, shift] at h

/-- Supported zero supplies an inhabited input, without restricting the Law. -/
theorem zero_supported : InSupport .G0 (0 : ℝ) := by
  exact ⟨by norm_num, (by norm_num : (0 : ℝ) ≤ 1).trans
    tail_arithmetic.2.2.2.2.2.le⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.ExactOriginal157
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.LiteralBranchReadout

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (z : ℝ) (hz : InSupport s z),
    ∃ (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧ x 0 = z ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = r.readout () () (a p) (x (p + 1)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨a, x, path, hpath0, hx0, hedges, hsupp, hrec⟩ :=
    h .G0 0 LiteralBranchReadout.zero_supported
  have h := hrec 0
  change x 0 = (1 : ℝ) at h
  rw [hx0] at h
  norm_num at h

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.lawful_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.lawful_tail, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

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

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (lo hi : ℝ) (hlt : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s z),
    ∃ (e : Guard) (w : List Label), LegalWord s e w ∧
      lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      OperationFiniteSource (address w) ∧
      ∃ path : ℕ → Guard, path 0 = s ∧
        (∀ p, nextGuard (path p) (address w p) = some (path (p + 1))) ∧
        (∀ p, InSupport (path p) (coordinate w p)) ∧
        (∀ p, coordinate w p = r.readout () () (address w p) (coordinate w (p + 1)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hsupport : ∀ z ∈ Set.Icc (-1 : ℝ) 0, InSupport .G0 z := by
    intro z hz
    exact ⟨hz.1, hz.2.trans LiteralBranchReadout.zero_supported.2⟩
  obtain ⟨e, w, hw, hlo, hhi, hfinite, path, hpath0, hedges, hsupp, hrec⟩ :=
    h .G0 (-1) 0 (by norm_num) hsupport
  have h := hrec 0
  change coordinate w 0 = (1 : ℝ) at h
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_tail_interior) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.finite_tail_interior, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

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

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀     (s e : Guard) (w : List Label) (hw : LegalWord s e w)
    (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hpath0 : path 0 = e)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1)))
    (hsupp : ∀ p, InSupport (path p) (x p))
    (hrec : ∀ p, x p = branch (a p) (x (p + 1))),
    ∃ (b : ℕ → Label) (y : ℕ → ℝ) (q : ℕ → Guard),
      q 0 = s ∧ y 0 = compose w (x 0) ∧
      (∀ p, nextGuard (q p) (b p) = some (q (p + 1))) ∧
      (∀ p, InSupport (q p) (y p)) ∧
      (∀ p, y p = r.readout () () (b p) (y (p + 1))) ∧
      (∀ p (hp : p < w.length), b p = w[p]) ∧
      (∀ p, b (w.length + p) = a p) ∧
      (∀ p, y (w.length + p) = x p)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, y, q, hq0, hy0, hedges, hsupp, hrec, hprefix, hbFuture, hyFuture⟩ :=
    h .G0 .G0 [] rfl (fun _ => Label.L0) (fun _ => 0) (fun _ => .G0) rfl
      (fun _ => rfl) (fun _ => LiteralBranchReadout.zero_supported)
      (by intro p; norm_num [branch, shift])
  have h := hrec 0
  change y 0 = (1 : ℝ) at h
  norm_num [compose] at hy0
  rw [hy0] at h
  norm_num at h

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.prepend_legal_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.prepend_legal_tail, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

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
