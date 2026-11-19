import D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound mirrors of the public diagonal identities. -/

open PowerSeries Filter
open scoped PowerSeries.WithPiTopology
open _root_.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.Expansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
noncomputable section

private local instance : UniformSpace ℚ := ⊥
private local instance : UniformSpace (Polynomial ℚ) := ⊥

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries (Polynomial ℚ)) (fun _ => PowerSeries ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ f => diagonal f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change diagonal 0 ≠ diagonal 1
  simpa only [map_zero, map_one] using (zero_ne_one : (0 : PowerSeries ℚ) ≠ 1)

abbrev applyArena : Arena where
  signature := signature
  Law r := ∀ f : PowerSeries (Polynomial ℚ),
      r.readout () () f =
        PowerSeries.eval₂ (Polynomial.eval₂RingHom PowerSeries.C (1 + X)) X f

private theorem applyRejected : ¬ applyArena.Law rejected := by
  intro h
  have he := h 1
  have hd := diagonal_apply 1
  rw [map_one] at hd
  have hz : (0 : PowerSeries ℚ) = 1 := by simpa [rejected, realize, ← hd] using he
  exact zero_ne_one hz

def applyFamily : Registration applyArena (type_of% @diagonal_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_apply, rejected, applyRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    applyArena.Law actual rejected applyRejected
  dependence := dependence

def applyAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@diagonal_apply) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.applyUnit
  realizationName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.applyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨applyArena⟩
  objectArena := .source ⟨applyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source applyArena ⟨applyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => diagonal f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev constantArena : Arena where
  signature := signature
  Law r := ∀ p : Polynomial ℚ,
      r.readout () () (C p) = (Polynomial.eval₂RingHom PowerSeries.C (1 + X)) p

private theorem constantRejected : ¬ constantArena.Law rejected := by
  intro h
  have he := h 1
  have hz : (0 : PowerSeries ℚ) = 1 := by simpa [rejected, realize] using he
  exact zero_ne_one hz

def constantFamily : Registration constantArena (type_of% @diagonal_C) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_C, rejected, constantRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    constantArena.Law actual rejected constantRejected
  dependence := dependence

def constantAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@diagonal_C) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.constantUnit
  realizationName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.constantFamily
  realizationSource := none
  generated := false
  arena := .source ⟨constantArena⟩
  objectArena := .source ⟨constantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source constantArena ⟨constantFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => diagonal f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev variableArena : Arena where
  signature := signature
  Law r := r.readout () () X = X

private theorem variableRejected : ¬ variableArena.Law rejected := by
  intro h
  have he : (0 : PowerSeries ℚ) = X := h
  have hz := congrArg (coeff 1) he
  simpa using hz

def variableFamily : Registration variableArena (type_of% @diagonal_X) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_X, rejected, variableRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    variableArena.Law actual rejected variableRejected
  dependence := dependence

def variableAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@diagonal_X) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.variableUnit
  realizationName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.variableFamily
  realizationSource := none
  generated := false
  arena := .source ⟨variableArena⟩
  objectArena := .source ⟨variableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source variableArena ⟨variableFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => diagonal f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev substitutionArena : Arena where
  signature := signature
  Law r := ∀ (f : PowerSeries ℚ) (b : PowerSeries (Polynomial ℚ)),
      constantCoeff b = 0 → constantCoeff (diagonal b) = 0 →
        r.readout () () (subst b f) = subst (diagonal b) f

private theorem substitutionRejected : ¬ substitutionArena.Law rejected := by
  intro h
  have he := h 1 0 (by simp) (by simp)
  change (0 : PowerSeries ℚ) = subst (diagonal 0) 1 at he
  rw [map_zero] at he
  have hs : subst (0 : PowerSeries ℚ) (1 : PowerSeries ℚ) = 1 := by
    convert subst_C (a := (0 : PowerSeries ℚ)) (1 : ℚ) using 1 <;> simp
  exact zero_ne_one (he.trans hs)

def substitutionFamily : Registration substitutionArena (type_of% @diagonal_subst) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_subst, rejected, substitutionRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    substitutionArena.Law actual rejected substitutionRejected
  dependence := dependence

def substitutionAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@diagonal_subst) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.substitutionUnit
  realizationName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.substitutionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨substitutionArena⟩
  objectArena := .source ⟨substitutionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source substitutionArena ⟨substitutionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => diagonal f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev liftArena : Arena where
  signature := signature
  Law r := ∀ f : PowerSeries ℚ,
      r.readout () () (f.map (algebraMap ℚ (Polynomial ℚ))) = f

private theorem liftRejected : ¬ liftArena.Law rejected := by
  intro h
  have he := h 1
  have hz : (0 : PowerSeries ℚ) = 1 := he
  exact zero_ne_one hz

def liftFamily : Registration liftArena (type_of% @diagonal_lift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_lift, rejected, liftRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    liftArena.Law actual rejected liftRejected
  dependence := dependence

def liftAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@diagonal_lift) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.liftUnit
  realizationName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.liftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena⟩
  objectArena := .source ⟨liftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena ⟨liftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => diagonal f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def discontinuous : Realization signature := by
  classical
  exact realize signature (fun _ _ f => if f = 0 then 0 else 1) (fun e => nomatch e)

abbrev continuousArena : Arena where
  signature := signature
  Law r := Continuous (fun f => r.readout () () f)

private theorem continuousRejected : ¬ continuousArena.Law discontinuous := by
  intro h
  have ht : Filter.Tendsto (fun n : ℕ => (X : PowerSeries (Polynomial ℚ)) ^ n)
      Filter.atTop (nhds 0) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro m
    exact tendsto_atTop_of_eventually_const fun n (hmn : m < n) => by
      simp [coeff_X_pow, hmn.ne]
  have hn (n : ℕ) : (X : PowerSeries (Polynomial ℚ)) ^ n ≠ 0 :=
    pow_ne_zero n X_ne_zero
  have hh := (h.tendsto 0).comp ht
  have he : Filter.Tendsto (fun _ : ℕ => (1 : PowerSeries ℚ)) Filter.atTop (nhds 0) := by
    simpa [discontinuous, realize, hn, Function.comp_def] using hh
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds he)

def continuousFamily : Registration continuousArena (type_of% @diagonal_continuous) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_continuous, discontinuous, continuousRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    continuousArena.Law actual discontinuous continuousRejected
  dependence := dependence

def continuousAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@diagonal_continuous) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.continuousUnit
  realizationName := `Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences.continuousFamily
  realizationSource := none
  generated := false
  arena := .source ⟨continuousArena⟩
  objectArena := .source ⟨continuousArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source continuousArena ⟨continuousFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => diagonal f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Congruence.TebniA350759PrimeCongruences
