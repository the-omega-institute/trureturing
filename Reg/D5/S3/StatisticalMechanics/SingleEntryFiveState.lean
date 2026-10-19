import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntryFiveState
import Reg.Support.SingleDependentReadout

/-! # The same forward trajectory supplies the association observation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState
open _root_.D5.S3.StatisticalMechanics.SingleEntryFiveState
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open Matrix Filter

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Rates, ℝ → Fin 5 → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actualReadout : ∀ role p, (signature).State p → (signature).Output role p :=
  fun _ p x => association p.2 x

def actualAnchor : ∀ (_ : (signature).Anchor) p, (signature).State p :=
  fun e => nomatch e

def actual : Realization signature :=
  realize signature actualReadout actualAnchor

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both the probability-law existence clause and the full arbitrary-solution
clause remain. Only its actual time-dependent association is observed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Rates,
    ((∃ p : ℝ → Fin 5 → ℝ, ForwardSolution k p ∧
      (∀ t, 0 ≤ t → (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
      ∀ t, 0 < t →
        pyramidLaw p t ∈ D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.openSimplex ∧
        D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.visible (pyramidLaw p t) ∈
          D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.openPyramid) ∧
      (∀ i, 0 < equilibriumLaw k i) ∧ (∑ i, equilibriumLaw k i) = 1 ∧
      generator k *ᵥ equilibriumLaw k = 0 ∧
      association (fun _ => equilibriumLaw k) 0 = 0 ∧
      0 < fiberWidth (fun _ => equilibriumLaw k) 0 ∧
      activeMass (fun _ => equilibriumLaw k) 0 =
        k.theta / (k.theta + k.eta *
          (k.b / (k.a + k.b) * (k.d / (k.c + k.d))))) ∧
    (∀ (p : ℝ → Fin 5 → ℝ), ForwardSolution k p → ∀ t, 0 < t →
      0 < activeMass p t ∧ 0 < fiberWidth p t ∧ 0 < R.readout () ⟨k, p⟩ t ∧
        p t 2 * p t 3 < p t 1 * p t 4 ∧
        0 < k.theta * p t 0 - k.eta * p t 1 ∧
        (∃ lam c : Fin 5 → ℝ,
          (∀ j, 0 ≤ lam j ∧ 0 ≤ c j) ∧ (∑ j, c j) = 1 ∧
          (∃ j, 0 < lam j * c j) ∧
          ∀ u, 0 ≤ u → p u 0 = ∑ j, c j * Real.exp (-lam j * u)) ∧
        (∀ i, Tendsto (fun u => p u i) atTop (nhds (equilibriumLaw k i))) ∧
        Tendsto (association p) atTop (nhds 0) ∧
        Tendsto (activeMass p) atTop (nhds
          (k.theta / (k.theta + k.eta * (k.b / (k.a + k.b) * (k.d / (k.c + k.d)))))) ∧
        ∀ f : Fin 5 → ℝ,
          taskError p f t = taskContrast f * association p t / activeMass p t ∧
          (taskContrast f ≠ 0 → 0 < taskContrast f * taskError p f t))

private def unitRates : Rates where
  a := 1
  b := 1
  c := 1
  d := 1
  eta := 1
  theta := 1
  a_pos := by norm_num
  b_pos := by norm_num
  c_pos := by norm_num
  d_pos := by norm_num
  eta_pos := by norm_num
  theta_pos := by norm_num

private theorem rejected_law : ¬ arena.Law rejected := by
  obtain ⟨p, hp, _⟩ := (five_state_strict_association unitRates).1.1
  intro h
  have hh := ((h unitRates).2 p hp 1 (by norm_num)).2.2.1
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  obtain ⟨p, hp, _⟩ := (five_state_strict_association unitRates).1.1
  have hpos := ((five_state_strict_association unitRates).2 p hp 1 (by norm_num)).2.2.1
  have hzero : association p 0 = 0 := by
    simp [association, activeMass, firstOccupancy, secondOccupancy, hp.1]
  intro role
  refine ⟨⟨unitRates, p⟩, 0, 1, ?_⟩
  change association p 0 ≠ association p 1
  rw [hzero]
  exact ne_of_lt hpos

def family : Registration arena (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨five_state_strict_association, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntryFiveState
  definition := none
  coordinates := #[0, 1]
  readouts := #[{
    path := #["body", "arg", "body", "body", "body", "body",
      "arg", "arg", "fn", "arg", "arg"]
    stateBinder := 3
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@five_state_strict_association) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- This is the full original occurrence, including its independent existence
clause. Its state is a real time selecting a law, not a single sample. -/
def analysisSource : Analysis.Source (@five_state_strict_association) :=
  Analysis.Source.ofRegistration _ family .exact selection

/-- Association is a law statistic on an infinite time-indexed family. No
finite microstate table or native continuation correspondence is supplied. -/
def analysis : AuricFib.Contract.Application (@five_state_strict_association) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Real time-indexed five-mode law: no finite presentation or native reader/continuation bridge" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

end Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState

namespace Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers
open _root_.D5.S3.StatisticalMechanics.SingleEntryFiveState
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actualReadout : ∀ role f, signature.State f → signature.Output role f := fun _ f t => f t

def actualAnchor : ∀ (_ : signature.Anchor) f, signature.State f := fun e => nomatch e

def actual : Realization signature := realize signature actualReadout actualAnchor

def rejected : Realization signature := realize signature (fun _ _ _ => 0) actualAnchor

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨id, 0, 1, by norm_num [actual, realize, actualReadout]⟩

namespace Constant
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f : ℝ → ℝ) (_hf : ∀ t, 0 ≤ t → HasDerivAt f 0 t)
    (t : ℝ) (_ht : 0 ≤ t), R.readout () f t = f 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ => 1) (fun t _ => hasDerivAt_const t (1 : ℝ)) 0 le_rfl
  norm_num [rejected, realize] at hb

def family : Registration arena (type_of% @constant_on_nonneg) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨constant_on_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntryFiveState
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "fn", "arg"]
    stateBinder := 2
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``constant_on_nonneg).type
  let mut binders := 0
  let some selected := selection.readouts[0]? | throwError "A readout selection is required"
  for step in selected.path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected original readout occurrence is absent"
  unless binders == 4 && e.getAppFn == .bvar 3 &&
      e.getAppArgs[0]? == some (.bvar 1) do
    throwError "The selected readout is not the original function at its state binder"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@constant_on_nonneg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers.Constant.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers.Constant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Constant

namespace Positive
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f g : ℝ → ℝ) (c : ℝ) (_hf0 : f 0 = 0)
    (_hf : ∀ t, 0 ≤ t → HasDerivAt f (-c * f t + g t) t)
    (_hg : ∀ t, 0 < t → 0 < g t) (t : ℝ) (_ht : 0 < t),
    0 < R.readout () f t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd (t : ℝ) (_ht : 0 ≤ t) :
      HasDerivAt (fun u : ℝ => u) (-0 * t + (1 : ℝ)) t := by
    simpa only [neg_zero, zero_mul, zero_add] using hasDerivAt_id' t
  have hb := h id (fun _ => 1) 0 rfl hd (fun _ _ => by norm_num) 1 (by norm_num)
  norm_num [rejected, realize] at hb

def family : Registration arena (type_of% @positive_forcing) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨positive_forcing, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntryFiveState
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
    stateBinder := 6
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``positive_forcing).type
  let mut binders := 0
  let some selected := selection.readouts[0]? | throwError "A readout selection is required"
  for step in selected.path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected original readout occurrence is absent"
  unless binders == 8 && e.getAppFn == .bvar 7 &&
      e.getAppArgs[0]? == some (.bvar 1) do
    throwError "The selected readout is not the original function at its state binder"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_forcing) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers.Positive.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Positive
namespace Symmetric
open scoped BigOperators ComplexOrder
open Matrix Filter
universe u

abbrev signature : Signature where
  Params := Σ V : Type u, (ℝ → V → ℝ) × V
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p t => p.2.1 t p.2.2

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p := fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} := realize signature (fun _ _ _ => 0) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (o : V) (_ho : 0 < A o o)
    (y : ℝ → V → ℝ) (_y0 : y 0 = Pi.single o 1)
    (_hy : ∀ t, 0 ≤ t → ∀ i,
      HasDerivAt (fun u => y u i) (-(A *ᵥ y t) i) t),
    ∃ lam c : V → ℝ,
      (∀ j, 0 ≤ lam j ∧ 0 ≤ c j) ∧ (∑ j, c j) = 1 ∧
      (∃ j, 0 < lam j * c j) ∧
      (∀ t, 0 ≤ t → R.readout () ⟨V, y, o⟩ t = ∑ j, c j * Real.exp (-lam j * t)) ∧
      (∀ t, 0 ≤ t → deriv (fun u => y u o) t < 0) ∧
      ∃ l : V → ℝ, (∀ i, Tendsto (fun t => y t i) atTop (nhds (l i))) ∧
        A *ᵥ l = 0 ∧
        (lam = hA.1.eigenvalues ∧
          c = fun j => (hA.1.eigenvectorUnitary : Matrix V V ℝ) o j ^ 2) ∧
        ∀ t, 0 ≤ t → ∀ i, y t i =
          ∑ j, (hA.1.eigenvectorUnitary : Matrix V V ℝ) i j *
            (hA.1.eigenvectorUnitary : Matrix V V ℝ) o j * Real.exp (-lam j * t)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let y : ℝ → V → ℝ := fun t _ => Real.exp (-t)
  have y0 : y 0 = Pi.single (ULift.up ()) 1 := by
    funext i
    cases i with
    | up i => cases i; simp [y]
  have hy (t : ℝ) (_ht : 0 ≤ t) (i : V) :
      HasDerivAt (fun u => y u i) (-((1 : Matrix V V ℝ) *ᵥ y t) i) t := by
    simpa [y] using (hasDerivAt_id' t).neg.exp
  obtain ⟨lam, c, _, hc, _, hrep, _⟩ :=
    h (1 : Matrix V V ℝ) Matrix.PosSemidef.one (ULift.up ())
      (by simp) y y0 hy
  have hb := hrep 0 le_rfl
  change (0 : ℝ) = _ at hb
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hb
  rw [hc] at hb
  norm_num at hb

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, (fun t _ => t), ULift.up ()⟩, 0, 1, ?_⟩
  norm_num [actual, realize, actualReadout]

def family : Registration arena.{u} (type_of% @symmetric_return_data.{u}) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@symmetric_return_data.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntryFiveState
  definition := none
  coordinates := #[0, 5, 7]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
      "arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg"]
    stateBinder := 12
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``symmetric_return_data).type
  let mut binders := 0
  let some selected := selection.readouts[0]? | throwError "A readout selection is required"
  for step in selected.path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected symmetric-return occurrence is absent"
  unless binders == 14 && e.getAppFn == .bvar 6 &&
      e.getAppArgs[0]? == some (.bvar 1) && e.getAppArgs[1]? == some (.bvar 8) do
    throwError "The selected return coordinate is not the original trajectory at its state binder"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@symmetric_return_data.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers.Symmetric.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers.Symmetric.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Symmetric
end Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.Helpers
