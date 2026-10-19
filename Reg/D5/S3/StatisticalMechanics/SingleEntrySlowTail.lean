import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntrySlowTail
import Reg.Support.SingleDependentReadout

/-! # Source-bound audit of the conditional analytic tail transfer -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter

namespace Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail
open _root_.D5.S3.StatisticalMechanics.SingleEntrySlowTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actualReadout : ∀ role p, signature.State p → signature.Output role p := fun _ _ x => x

def actualAnchor : ∀ (_ : signature.Anchor) p, signature.State p := fun e => nomatch e

def actual : Realization signature := realize signature actualReadout actualAnchor

def rejected : Realization signature := realize signature (fun _ _ _ => 0) actualAnchor

/-- The original functions, all differential and asymptotic hypotheses, and the
limit value are retained. Only the slope occurrence in the positivity conclusion
is observed, so changing it cannot alter any premise. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D f K : ℝ → ℝ) (s l theta rInf qi qj slope : ℝ),
    l < s → 0 < theta → 0 < rInf → 0 < qi → 0 < qj → slope < 0 →
    (∀ t, 0 ≤ t → HasDerivAt D (-s * D t + f t * K t) t) →
    Tendsto (fun t => Real.exp (l * t) * f t) atTop (nhds (-theta / slope)) →
    Tendsto K atTop (nhds (rInf * qi * qj)) →
    Tendsto (fun t => Real.exp (l * t) * D t) atTop
      (nhds (-theta * rInf * qi * qj / ((s - l) * slope))) ∧
      0 < -theta * rInf * qi * qj / ((s - l) * R.readout () () slope)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun _ : ℝ => (1 : ℝ))
      (-(1 : ℝ) * 1 + 1 * 1) t := by
    intro t _
    simpa using hasDerivAt_const t (1 : ℝ)
  have hf : Tendsto (fun t : ℝ => Real.exp ((0 : ℝ) * t) * 1)
      atTop (nhds (-(1 : ℝ) / -1)) := by simp
  have hK : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds ((1 : ℝ) * 1 * 1)) :=
    by simp
  have hh := (h (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 0 1 1 1 1 (-1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd hf hK).2
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, actualReadout, realize]

def family : Registration arena (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨association_tail_from_input_tail, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySlowTail
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "body", "body", "body",
      "arg", "arg", "arg", "arg"]
    stateBinder := 9
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``association_tail_from_input_tail).type
  let path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "body", "body", "body", "body",
    "arg", "arg", "arg", "arg"]
  let mut binders := 0
  for step in path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected slow-tail slope occurrence is absent"
  unless binders == 19 && e == .bvar 9 do
    throwError "The selected occurrence is not the original real slope parameter"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    association_tail_from_input_tail (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail.family
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

def analysisSource : Analysis.Source association_tail_from_input_tail :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application association_tail_from_input_tail where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Conditional analytic functions: generator-bound probability law, pair pushforward \
       and spectral input residue are not premises of this source" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

namespace Equilibrium
open _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
open _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot (modeWeight weight_pos)
universe u

abbrev signature : Signature where
  Params := Σ I : Type u, ℝ → Option (Finset I) → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Finset p.1) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p t => p.2 t

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} := realize signature (fun _ _ _ _ => 0) actualAnchor

/-- Both conclusions and the full forward-solution premise are retained. Only
the probability curve used by the second conclusion is observed. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I] (k : Rates I)
    (p : ℝ → Option (Finset I) → ℝ), ForwardSolution k p →
    ∀ (i j : I), i ≠ j →
    Tendsto (activeMass p) atTop
      (nhds (k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅))) ∧
    Tendsto (joint (fun t => R.readout () ⟨I, p⟩ t) i j) atTop
      (nhds ((k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅)) *
        (k.a i / (k.a i + k.b i)) * (k.a j / (k.a j + k.b j))))

private def unitRates : Rates (ULift.{u} (Fin 2)) where
  a := fun _ => 1
  b := fun _ => 1
  eta := 1
  theta := 1
  a_pos _ := by norm_num
  b_pos _ := by norm_num
  eta_pos := by norm_num
  theta_pos := by norm_num

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  let k : Rates (ULift.{u} (Fin 2)) := unitRates
  obtain ⟨p, hp, _⟩ := (finite_network_strict_pair k).1
  intro h
  have hij : (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ := by decide
  have hh := (h k p hp ⟨0⟩ ⟨1⟩ hij).2
  change Tendsto (joint (fun _ : ℝ => fun _ => 0) (⟨0⟩ : ULift.{u} (Fin 2)) ⟨1⟩)
    atTop (nhds ((k.theta /
      (k.theta + k.eta * modeWeight k.a k.b ∅)) *
      (k.a ⟨0⟩ / (k.a ⟨0⟩ + k.b ⟨0⟩)) *
      (k.a ⟨1⟩ / (k.a ⟨1⟩ + k.b ⟨1⟩)))) at hh
  have hz : Tendsto (joint (fun _ : ℝ => fun _ => 0)
      (⟨0⟩ : ULift.{u} (Fin 2)) ⟨1⟩) atTop (nhds 0) := by
    have heq : joint (fun _ : ℝ => fun _ => 0)
        (⟨0⟩ : ULift.{u} (Fin 2)) ⟨1⟩ = (fun _ : ℝ => (0 : ℝ)) := by
      funext t
      simp only [_root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.joint,
        mul_zero, Finset.sum_const_zero]
    rw [heq]
    exact tendsto_const_nhds
  have hden : 0 < k.theta +
      k.eta * modeWeight k.a k.b ∅ :=
    add_pos k.theta_pos (mul_pos k.eta_pos
      (weight_pos _ _ k.a_pos k.b_pos ∅))
  have hc : 0 < (k.theta /
      (k.theta + k.eta * modeWeight k.a k.b ∅)) *
      (k.a ⟨0⟩ / (k.a ⟨0⟩ + k.b ⟨0⟩)) *
      (k.a ⟨1⟩ / (k.a ⟨1⟩ + k.b ⟨1⟩)) := by
    apply mul_pos
    · apply mul_pos (div_pos k.theta_pos hden)
      exact div_pos (k.a_pos _) (add_pos (k.a_pos _) (k.b_pos _))
    · exact div_pos (k.a_pos _) (add_pos (k.a_pos _) (k.b_pos _))
  exact (ne_of_gt hc) (tendsto_nhds_unique hz hh).symm

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, fun t _ => t⟩, 0, 1, ?_⟩
  intro heq
  have h := congrFun heq none
  norm_num [actual, realize, actualReadout] at h

def family : Registration arena.{u} (type_of% @finite_network_equilibrium_moments.{u}) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@finite_network_equilibrium_moments.{u}, rejected, rejected_law⟩
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
  owner := `D5.S3.StatisticalMechanics.SingleEntrySlowTail
  definition := none
  coordinates := #[0, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
      "arg", "fn", "fn", "arg", "fn", "fn", "arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``finite_network_equilibrium_moments).type
  let path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
    "arg", "fn", "fn", "arg", "fn", "fn", "arg"]
  let mut binders := 0
  for step in path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected full-network probability curve is absent"
  unless binders == 9 && e == .bvar 4 do
    throwError "The selected equilibrium readout is not the original probability curve"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_network_equilibrium_moments.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail.Equilibrium.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail.Equilibrium.family
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

def analysisSource : Analysis.Source (@finite_network_equilibrium_moments.{u}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@finite_network_equilibrium_moments.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "The source is the actual generator-bound network and its two-site occupancy; \
       a finite five-mode law reader and native continuation adapter are not supplied." }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

end Equilibrium

end Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail
