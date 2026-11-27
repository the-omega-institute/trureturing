import D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source observations of the finite prime tail and the normalized clipped layer. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail

open Real Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

namespace Tail

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature := realize signature
  (fun _ m y => primePowerTail m y) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (_ : 2 ≤ m) {ι : Type u} {l : Filter ι} {y z : ι → ℝ},
    Tendsto y l atTop → Tendsto (fun i => z i / y i) l atTop →
    Tendsto (fun i => y i ^ (m - 1) * log (y i) * R.readout () m (y i) (z i))
      l (𝓝 (1 / ((m : ℝ) - 1)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let lift : ℝ → ULift.{u} ℝ := ULift.up
  let l : Filter (ULift.{u} ℝ) := map lift atTop
  have hy : Tendsto ULift.down l atTop :=
    tendsto_map' (show Tendsto (id : ℝ → ℝ) atTop atTop from tendsto_id)
  have hz : Tendsto (fun i : ULift.{u} ℝ => (i.down * i.down) / i.down) l atTop := by
    apply tendsto_map'
    refine (show Tendsto (id : ℝ → ℝ) atTop atTop from tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change x = (x * x) / x
    field_simp [hx.ne']
  have hbad := h 2 le_rfl hy hz
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 (1 / ((2 : ℝ) - 1))) := by
    simpa only [Function.comp_def, rejected, realize, mul_zero, Nat.cast_ofNat] using
      hbad.comp (tendsto_map : Tendsto lift atTop l)
  have hne : 1 / ((2 : ℝ) - 1) ≠ 0 := by norm_num
  exact hne (tendsto_nhds_unique hzero tendsto_const_nhds)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 1, 2, ?_⟩
  intro h
  have heq := congrFun h 2
  change primePowerTail 2 1 2 = primePowerTail 2 2 2 at heq
  have hdiag : primePowerTail 2 2 2 = 0 := by simp [primePowerTail, primeInterval]
  have hprime : 2 ∈ primeInterval (1 : ℝ) 2 := by
    norm_num [primeInterval, Nat.prime_two]
  have hpos : 0 < primePowerTail 2 1 2 := by
    unfold primePowerTail
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨2, hprime, by positivity⟩
  exact hpos.ne' (heq.trans hdiag)

def family : Registration arena.{u} (type_of% (@prime_power_tail_tendsto.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_power_tail_tendsto.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_power_tail_tendsto.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail.prime_power_tail_tendsto.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail.Tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m y => primePowerTail m y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Tail

namespace Activation

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ m P => prefixH P ^ (((m : ℝ) - 1) / (m : ℝ)) * prefixEll P * activationLayer m P)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m →
    Tendsto (fun P : ℕ => R.readout () m P) atTop
      (𝓝 (((m : ℝ) / ((m : ℝ) - 1)) * (m : ℝ) ^ (1 / (m : ℝ))))

private theorem limit_ne_zero : (2 / ((2 : ℝ) - 1)) * (2 : ℝ) ^ (1 / (2 : ℝ)) ≠ 0 := by
  have h : 0 < (2 / ((2 : ℝ) - 1)) * (2 : ℝ) ^ (1 / (2 : ℝ)) := by
    norm_num
    positivity
  exact h.ne'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact limit_ne_zero (tendsto_nhds_unique (h 2 le_rfl) tendsto_const_nhds)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨2, 0, ?_⟩
  by_contra! h
  have h0 : actual.readout () 2 0 = 0 := by
    simp [actual, realize, activationLayer, Nat.primesLE_zero]
  have hzero := (activation_layer_tendsto 2 le_rfl).congr'
    (Eventually.of_forall (fun P => (h P).symm.trans h0))
  exact limit_ne_zero (tendsto_nhds_unique hzero tendsto_const_nhds)

def family : Registration arena (type_of% (@activation_layer_tendsto)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨activation_layer_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@activation_layer_tendsto) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail.activation_layer_tendsto.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail.Activation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ m P => prefixH P ^ (((m : ℝ) - 1) / (m : ℝ)) * prefixEll P * activationLayer m P)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Activation

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail
