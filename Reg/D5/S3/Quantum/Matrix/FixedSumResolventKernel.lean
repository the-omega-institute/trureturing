import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.FixedSumResolventKernel
import Reg.Support.SingleDependentReadout

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel
open _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory

abbrev integrandSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℝ × ℕ) (fun _ => ℝ) (fun _ => ℝ)

def resolventActual : Realization integrandSignature := realize integrandSignature
  (fun _ p s => _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent p.1 p.2.1 s ^ p.2.2) (fun e => nomatch e)

def scalarActual : Realization integrandSignature := realize integrandSignature
  (fun _ p s => (p.1 * p.2.1 / ((s + p.1) * (s + p.2.1))) ^ p.2.2)
  (fun e => nomatch e)

def integrandRejected : Realization integrandSignature := realize integrandSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev resolventArena : Arena where
  signature := integrandSignature
  Law R := ∀ {S : ℝ}, 0 < S → ∀ (r : ℝ) {j : ℕ}, 1 ≤ j →
    IntegrableOn (R.readout () (S,r,j)) (Ioi 0)

abbrev scalarArena : Arena where
  signature := integrandSignature
  Law R := ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → ∀ {j : ℕ}, 1 ≤ j →
    IntegrableOn (R.readout () (u,v,j)) (Ioi 0)

private theorem not_integrable_one : ¬ IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) := by
  simp [integrableOn_const_iff]

private theorem resolvent_rejected : ¬ resolventArena.Law integrandRejected := by
  intro h
  exact not_integrable_one (h (S := 1) (by norm_num) 1 (j := 1) (by norm_num))

private theorem scalar_rejected : ¬ scalarArena.Law integrandRejected := by
  intro h
  exact not_integrable_one (h (u := 1) (v := 1) (by norm_num) (by norm_num)
    (j := 1) (by norm_num))

private theorem resolvent_dependence : ObservationalDependence integrandSignature resolventActual := by
  intro i
  refine ⟨(2,1,1), 0, 1, ?_⟩
  norm_num [resolventActual, realize, _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent]

private theorem scalar_dependence : ObservationalDependence integrandSignature scalarActual := by
  intro i
  refine ⟨(1,1,1), 0, 1, ?_⟩
  norm_num [scalarActual, realize]

def resolventFamily : Registration resolventArena (type_of% @integrable_resolvent) where
  actual := resolventActual
  bridge := Iff.rfl
  variation := ⟨@integrable_resolvent, integrandRejected, resolvent_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    resolventArena.Law resolventActual integrandRejected resolvent_rejected
  dependence := resolvent_dependence

def scalarFamily : Registration scalarArena (type_of% @integrable_scalar) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@integrable_scalar, integrandRejected, scalar_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    scalarArena.Law scalarActual integrandRejected scalar_rejected
  dependence := scalar_dependence

abbrev convexSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℕ) (fun _ => ℝ) (fun _ => ℝ)

def convexActual : Realization convexSignature := realize convexSignature
  (fun _ p r => kernel p.1 p.2 r) (fun e => nomatch e)

def convexRejected : Realization convexSignature := realize convexSignature
  (fun _ _ r => -r ^ 2) (fun e => nomatch e)

abbrev convexArena : Arena where
  signature := convexSignature
  Law R := ∀ {S : ℝ}, 0 < S → ∀ {j : ℕ}, 1 ≤ j →
    ConvexOn ℝ (Ici 0) (R.readout () (S,j))

private theorem convex_rejected : ¬ convexArena.Law convexRejected := by
  intro h
  have hc := h (S := 1) (by norm_num) (j := 1) (by norm_num)
  have hh := hc.2 (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (show (2 : ℝ) ∈ Ici 0 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  norm_num [convexRejected, realize] at hh

private theorem convex_dependence : ObservationalDependence convexSignature convexActual := by
  intro i
  refine ⟨(2,1), 0, 1, ?_⟩
  change kernel 2 1 0 ≠ kernel 2 1 1
  have hz : kernel 2 1 0 = 0 := by simp [kernel, _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent]
  have hi : IntegrableOn (fun s => _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent 2 1 s) (Ioi 0) := by
    simpa using integrable_resolvent (S := 2) (by norm_num) 1 (j := 1) (by norm_num)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent 2 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    dsimp [_root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent]
    positivity
  have hp : 0 < ∫ s in Ioi 0, _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent 2 1 s := by
    apply (integral_pos_iff_support_of_nonneg_ae hn hi).mpr
    calc
      0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) := by simp
      _ ≤ (volume.restrict (Ioi (0 : ℝ))) (Function.support (_root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent 2 1)) := by
        apply measure_mono
        intro s hs
        have hs0 : 0 < s := hs
        change _root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent 2 1 s ≠ 0
        dsimp [_root_.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolvent]
        exact ne_of_gt (by positivity)
  rw [hz]
  exact ne_of_lt (by simpa [kernel] using hp)

def convexFamily : Registration convexArena (type_of% @convex_kernel) where
  actual := convexActual
  bridge := Iff.rfl
  variation := ⟨@convex_kernel, convexRejected, convex_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    convexArena.Law convexActual convexRejected convex_rejected
  dependence := convex_dependence

abbrev orderSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def orderActual : Realization orderSignature := realize orderSignature
  (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def orderRejected : Realization orderSignature := realize orderSignature
  (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev orderArena : Arena where
  signature := orderSignature
  Law R := ∀ {ι : Type u} [Fintype ι] (a b : ι → ℝ),
    (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → 0 < ∑ i, a i → 0 < ∑ i, b i →
    ∀ {j : ℕ}, 1 ≤ j →
    R.readout () () (scalarMoment j (∑ i, a i) (∑ i, b i) *
      ((∑ i, Real.sqrt (a i * b i)) ^ 2 / ((∑ i, a i) * ∑ i, b i)) ^ j)
      (∑ i, scalarMoment j (a i) (b i))

private theorem order_rejected : ¬ orderArena.{u}.Law orderRejected := by
  intro h
  exact h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num) (by simp) (by simp)
    (j := 1) (by norm_num)

private theorem order_dependence : ObservationalDependence orderSignature orderActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [orderActual, realize] at he

def orderFamily : Registration orderArena.{u} (type_of% @scalar_fidelity_moment.{u}) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@scalar_fidelity_moment, orderRejected, order_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    orderArena.Law orderActual orderRejected order_rejected
  dependence := order_dependence

def resolventAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_resolvent) (Realization integrandSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolventAuditUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.resolventFamily
  realizationSource := none
  generated := false
  arena := .source ⟨resolventArena⟩
  objectArena := .source ⟨resolventArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resolventArena ⟨resolventFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integrandSignature resolventActual.readout resolventActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.FixedSumResolventKernel
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms resolventAudit

def scalarAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_scalar) (Realization integrandSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.scalarAuditUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.scalarFamily
  realizationSource := none
  generated := false
  arena := .source ⟨scalarArena⟩
  objectArena := .source ⟨scalarArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scalarArena ⟨scalarFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integrandSignature scalarActual.readout scalarActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.FixedSumResolventKernel
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scalarAudit

def convexAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@convex_kernel) (Realization convexSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.convexAuditUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.convexFamily
  realizationSource := none
  generated := false
  arena := .source ⟨convexArena⟩
  objectArena := .source ⟨convexArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source convexArena ⟨convexFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize convexSignature convexActual.readout convexActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.FixedSumResolventKernel
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms convexAudit

def orderAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@scalar_fidelity_moment.{u}) (Realization orderSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.orderAuditUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel.orderFamily
  realizationSource := none
  generated := false
  arena := .source ⟨orderArena⟩
  objectArena := .source ⟨orderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source orderArena ⟨orderFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orderSignature orderActual.readout orderActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.FixedSumResolventKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms orderAudit

end Reg.D5.S3.Quantum.Matrix.FixedSumResolventKernel
