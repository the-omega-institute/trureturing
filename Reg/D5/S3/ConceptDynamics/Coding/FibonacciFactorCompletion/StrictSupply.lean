import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily



open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily



namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ execution : List Return, Σ j : Side, ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ q z => execute q.2.1 (q.1.take q.2.2) z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ q _ => aSide q.2.1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (execution : List Return),
      (∀ (j : Side) (p : ℕ),
        aSide j < r.readout () ⟨execution, ⟨j,p⟩⟩ (initial j model) ∧
        execute j (execution.take p) (initial j model) < hSide j) ∧
      (∀ p : ℕ, execute .high (execution.take p) (initial .high model) <
        execute .low (execution.take p) (initial .low model)) ∧
      (∀ (j : Side) (p n k : ℕ),
        let D := execute j (execution.take p) (initial j model)
        let z := hSide j - rho ^ k * (hSide j - chi ^ n * D)
        0 < z ∧ z < hSide j ∧
        0 ≤ c0 + sign j * z ∧ c0 + sign j * z ≤ T2) ∧
      (∀ (p n k : ℕ),
        hSide .high - rho ^ k * (hSide .high - chi ^ n *
          execute .high (execution.take p) (initial .high model)) <
        hSide .low - rho ^ k * (hSide .low - chi ^ n *
          execute .low (execution.take p) (initial .low model))) ∧
      (∀ (j : Side) (p : ℕ),
        coordinate (sourcePrefix j model execution)
          ((stem j).length + listWeight (execution.drop p)) =
        c0 + sign j * execute j (execution.take p) (initial j model))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  exact (lt_irrefl (aSide Side.high)) ((h .original []).1 .high 0).1

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_complete_boundary_geometry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_complete_boundary_geometry, rejected, rejected_law⟩
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
    refine ⟨⟨[], Side.high, 0⟩, 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def actual_complete_boundary_geometry_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_complete_boundary_geometry)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ q z => execute q.2.1 (q.1.take q.2.2) z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149.evidence
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
    (fun _ q z => execute q.2.1 (q.1.take q.2.2) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_complete_boundary_geometry_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal149

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses
noncomputable section

theorem empty_strict_supply (o : Ownership) :
    ∃ b : ℝ, lam - rho < b ∧ lam - g ^ 2 * chi * xSide .high < b ∧
      ActualPairSupply .original o b .strict [] := by
  let b := max (lam - rho) (lam - g ^ 2 * chi * xSide .high) + 1
  have hb : lam - rho < b := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hc : lam - g ^ 2 * chi * xSide .high < b :=
    lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  refine ⟨b, hb, hc, (actual_strict_cost_supply .original o b [] hb).mpr ?_⟩
  refine ⟨?_, ?_, trivial⟩
  · simpa only [execute, initial] using hc
  · intro h
    cases h

theorem record_interval_nonempty :
    ∃ b : ℝ, lam - g ^ 2 * chi ^ 2 * hSide .high < b ∧
      b < lam - g ^ 2 * chi ^ 2 * (aSide .high / (1 - rho * chi ^ 2)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by dsimp [g, t]; nlinarith
  have g1 : g < 1 := by linarith
  have rp : 0 < rho := pow_pos gp 6
  have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide)
  have cp : 0 < chi := pow_pos gp 20
  have c1 : chi < 1 := pow_lt_one₀ gp.le g1 (by decide)
  have sp : 0 < chi ^ 2 := pow_pos cp 2
  have s1 : chi ^ 2 < 1 := pow_lt_one₀ cp.le c1 (by decide)
  have rc : rho * chi ^ 2 < rho := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left s1 rp
  have den : 0 < 1 - rho * chi ^ 2 := by linarith
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have divlt : aSide .high / (1 - rho * chi ^ 2) < hSide .high := by
    apply (div_lt_iff₀ den).mpr
    have gain := mul_lt_mul_of_pos_right rc hp
    dsimp [aSide]
    nlinarith
  let q := lam - g ^ 2 * chi ^ 2 * hSide .high
  let p := lam - g ^ 2 * chi ^ 2 * (aSide .high / (1 - rho * chi ^ 2))
  have qp : q < p := by
    have gain := mul_lt_mul_of_pos_left divlt (mul_pos (sq_pos_of_pos gp) sp)
    dsimp [q, p]
    linarith
  exact ⟨(q + p) / 2, by linarith, by linarith⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150
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
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ)
    (execution : List Return) (hb : lam - rho < b),
    ActualPairSupply model o (r.readout () () b) .strict execution ↔
      lam - g ^ 2 * chi * execute .high execution (initial .high model) < b ∧
      (model = .anchored → lam - g ^ 2 * chi * xSide .high < b) ∧
      StrictControl .high b execution (initial .high model)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hb, _, supply⟩ := SupplyWitnesses.empty_strict_supply (fun _ => false)
  have bad := (h .original (fun _ => false) b [] hb).mpr
    ((actual_strict_cost_supply .original (fun _ => false) b [] hb).mp supply)
  obtain ⟨err, herr, _⟩ := bad .high
  have hb := herr 0
  change |err 0| < (-1 : ℝ) at hb
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_strict_cost_supply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_strict_cost_supply, rejected, rejected_law⟩
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

def actual_strict_cost_supply_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_strict_cost_supply)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence
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
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_strict_cost_supply_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal151
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
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ)
    (execution : List Return) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))),
    (ActualPairSupply model o (r.readout () () b) .strict execution ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) true .high execution
        (initial .high model)) ∧
    (ActualPairSupply model o b .recordMargin execution ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) true .high execution
        (initial .high model))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hqb, hbp⟩ := SupplyWitnesses.record_interval_nonempty
  have bad := (h .original (fun _ => false) b [] 2 (by decide) hqb hbp).1.mpr trivial
  obtain ⟨err, herr, _⟩ := bad .high
  have hb := herr 0
  change |err 0| < (-1 : ℝ) at hb
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_strict_record_supply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_strict_record_supply, rejected, rejected_law⟩
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

def actual_strict_record_supply_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.actual_strict_record_supply)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal151.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal151.evidence
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
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_strict_record_supply_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal151

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal153
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
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀
    (model : Model) (o : Ownership) (execution : List Return)
    {small large : ℝ} (hbudget : small ≤ large)
    (hsupply : ActualPairSupply model o small .closed execution),
    ActualPairSupply model o (r.readout () () large) .closed execution

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, _, _, supply⟩ := SupplyWitnesses.empty_strict_supply (fun _ => false)
  have closed : ActualPairSupply .original (fun _ => false) b .closed [] := by
    intro j
    obtain ⟨err, herr, hread, hzero, hfuture⟩ := supply j
    exact ⟨err, fun p => (herr p).le, hread, hzero, hfuture⟩
  have bad := h .original (fun _ => false) [] (small := b) (large := b) le_rfl closed
  obtain ⟨err, herr, _⟩ := bad .high
  have hb := herr 0
  change |err 0| ≤ (-1 : ℝ) at hb
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_closed_supply_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_closed_supply_mono, rejected, rejected_law⟩
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

def uniform_closed_supply_mono_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_closed_supply_mono)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal153.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal153.evidence
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
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms uniform_closed_supply_mono_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal153
