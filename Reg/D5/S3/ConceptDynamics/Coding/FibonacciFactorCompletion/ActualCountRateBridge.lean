import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.SingleDependentReadout
import Reg.Support.FibonacciFactorWitnesses
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

theorem zero_count_positive (model : Model) (K : ℕ) (d : ℝ) (strict : Bool)
    (hK : 1 ≤ K) : 0 < actualCount model K d strict 0 := by
  letI : Finite (ActualDictionary model K d strict 0) :=
    (actual_dictionary_bound model K d strict 0 hK).1
  letI : Nonempty (ActualDictionary model K d strict 0) := ⟨⟨[], trivial, rfl⟩⟩
  exact Nat.card_pos

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ N => 3^(N+1)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (N : ℕ) (hK : 1 ≤ K),
    Finite (ActualDictionary model K d strict N) ∧
    actualCount model K d strict N ≤ factorCount (AuxiliaryLanguage K d) N ∧
    actualCount model K d strict N ≤ r.readout () () N

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have positive := zero_count_positive .original 1 0 false (by decide)
  have upper := (h .original 1 0 false 0 (by decide)).2.2
  change actualCount .original 1 0 false 0 ≤ 0 at upper
  omega

def evidence : Registration sourceArena (type_of% @actual_dictionary_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_dictionary_bound, rejected, rejected_law⟩
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

def actual_dictionary_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_dictionary_bound)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ N => 3^(N+1)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31.evidence
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
    (fun _ _ N => 3^(N+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_dictionary_bound_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℕ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ q N => Nat.card (NoCFactor q.1 q.2 N)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (N : ℕ), r.readout () ⟨K,d⟩ N ≤ 1

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := h 1 0 0
  norm_num [rejected, realize] at bad

def evidence : Registration sourceArena (type_of% @no_c_factor_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_c_factor_card, rejected, rejected_law⟩
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
    refine ⟨⟨1,0⟩, 0, 1, ?_⟩
    change Nat.card (NoCFactor 1 0 0) ≠ Nat.card (NoCFactor 1 0 1)
    have zero_card : Nat.card (NoCFactor 1 0 0) = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨⟨[], ⟨(fun _ => .u), all_u_auxiliary, 0, (by intro k; exact Fin.elim0 k)⟩, rfl⟩,
        (by simp)⟩, ?_⟩
      intro w
      apply Subtype.ext
      apply Subtype.ext
      exact word_weight_geometry.2.2 _ w.val.property.2
    letI : IsEmpty (NoCFactor 1 0 1) := ⟨by
      intro w
      exact word_weight_ne_one _ w.val.property.2⟩
    simp [zero_card]

def no_c_factor_card_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.no_c_factor_card)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ q N => Nat.card (NoCFactor q.1 q.2 N)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33.evidence
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
    (fun _ q N => Nat.card (NoCFactor q.1 q.2 N)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms no_c_factor_card_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39
noncomputable section

open Reg.Support.FibonacciFactorWitnesses
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31

theorem one_count_zero (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) :
    actualCount model K d strict 1 = 0 := by
  letI : IsEmpty (ActualDictionary model K d strict 1) := ⟨by
    intro xs
    have wt := xs.property.2
    cases eq : xs.val with
    | nil => simp [eq, listWeight] at wt
    | cons a rest =>
      have pos := a.m_pos
      simp only [eq, listWeight] at wt
      omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem budget_witness : ∃ b : ℝ,
    lam - g ^ 2 * chi ^ 2 * hSide .high < b ∧
    b < lam - g ^ 2 * chi ^ 2 * (aSide .high / (1 - rho * chi ^ 2)) := by
  have gp := tail_arithmetic.2.2.2.1
  have gl := tail_arithmetic.2.2.2.2.1
  have rp : 0 < rho := pow_pos gp 6
  have rl : rho < 1 := pow_lt_one₀ gp.le gl (by decide)
  have cp : 0 < chi := pow_pos gp 20
  have cl : chi < 1 := pow_lt_one₀ gp.le gl (by decide)
  have c2l : chi ^ 2 < 1 := pow_lt_one₀ cp.le cl (by decide)
  have rc : rho * chi ^ 2 < rho := by simpa using mul_lt_mul_of_pos_left c2l rp
  have den : 0 < 1 - rho * chi ^ 2 := by linarith
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have lt : aSide .high / (1 - rho * chi ^ 2) < hSide .high := by
    apply (div_lt_iff₀ den).mpr
    dsimp [aSide]
    have := mul_lt_mul_of_pos_right (show 1-rho < 1-rho*chi^2 by linarith) hp
    nlinarith
  have mulpos : 0 < g ^ 2 * chi ^ 2 := mul_pos (pow_pos gp _) (pow_pos cp _)
  have width := mul_lt_mul_of_pos_left lt mulpos
  exact exists_between (by linarith)

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ N => N) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ) (contract : Contract) (N K : ℕ)
    (hK : 2 ≤ K) (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    Finite (ContractDictionary model o b contract N) ∧
    contractCount model o b contract N =
      actualCount model K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) (r.readout () () N)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hb₁, hb₂⟩ := budget_witness
  have original := (contract_count_correspondence .original (fun _ => false) b .strict 0 2
    (by decide) hb₁ hb₂).2
  have changed := (h .original (fun _ => false) b .strict 0 2 (by decide) hb₁ hb₂).2
  change contractCount .original (fun _ => false) b .strict 0 =
    actualCount .original 2 ((lam-b)/g^2/chi^2) (contractStrict (fun _ => false) .strict) 1 at changed
  rw [one_count_zero] at changed
  have positive := zero_count_positive .original 2 ((lam-b)/g^2/chi^2)
    (contractStrict (fun _ => false) .strict) (by decide)
  omega

def evidence : Registration sourceArena (type_of% @contract_count_correspondence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@contract_count_correspondence, rejected, rejected_law⟩
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

def contract_count_correspondence_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.contract_count_correspondence)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ N => N) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39.evidence
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
    (fun _ _ N => N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms contract_count_correspondence_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
noncomputable section

open Reg.Support.SingleDependentReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  signature Model (fun _ => ℕ) (fun _ => ℝ → Bool → ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ model K => actualRate model K) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

/-- At cutoff zero every admissible execution is empty, for every weight and guard. -/
theorem cutoff_zero_rate (model : Model) (d : ℝ) (strict : Bool) :
    actualRate model 0 d strict = 0 := by
  have empty (N : ℕ) (xs : ActualDictionary model 0 d strict N) : xs.val = [] := by
    have guard := xs.property.1
    cases h : xs.val with
    | nil => rfl
    | cons a rest =>
      rw [h] at guard
      have bound : a.r ≤ 0 := guard.1
      have positive := a.r_pos
      omega
  have rates : actualLogRate model 0 d strict = fun _ => 0 := by
    funext N
    letI : Subsingleton (ActualDictionary model 0 d strict N) :=
      ⟨fun xs ys => Subtype.ext ((empty N xs).trans (empty N ys).symm)⟩
    have bound : actualCount model 0 d strict N ≤ 1 := by
      simpa [actualCount] using
        (Nat.card_le_card_of_injective (fun _ : ActualDictionary model 0 d strict N => ())
          (fun _ _ _ => Subsingleton.elim _ _))
    simp [actualLogRate, max_eq_left bound]
  rw [actualRate, rates, Filter.limsup_const]

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨.original, 0, 2, ?_⟩
  intro eq
  have values := congrFun (congrFun eq ((lam - budget) / g ^ 2 / chi ^ 2)) false
  change actualRate .original 0 _ false = actualRate .original 2 _ false at values
  rw [cutoff_zero_rate] at values
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  linarith

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (src dst : Model),
    r.readout () src K ((lam - b) / g ^ 2 / chi ^ K) false =
      actualRate dst K ((lam - b) / g ^ 2 / chi ^ K) true

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq := h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 .original .original
  change 0 = actualRate .original 2 ((lam - budget) / g ^ 2 / chi ^ 2) true at eq
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 true
  linarith

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_rates_equal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_rates_equal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_rates_equal_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_rates_equal)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37.evidence
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
    (fun _ model K => actualRate model K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_rates_equal_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal37

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (model : Model) (strict : Bool),
    r.readout () model K ((lam - b) / g ^ 2 / chi ^ K) strict =
      weightedFactorRate (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq := h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 .original false
  change 0 = weightedFactorRate (AuxiliaryLanguage 2 ((lam - budget) / g ^ 2 / chi ^ 2)) at eq
  have bridge := actual_auxiliary_rate_bridge (fun _ => false) budget 2 le_rfl
    budget_interval.1 budget_interval.2 .original false
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  linarith

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_auxiliary_rate_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_auxiliary_rate_bridge, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def actual_auxiliary_rate_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.actual_auxiliary_rate_bridge)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38.evidence
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
    (fun _ model K => actualRate model K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_auxiliary_rate_bridge_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal38

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40
noncomputable section

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.RateReadout
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
  (budget budget_interval)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    weightedFactorRate (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K)) = eta_b K b ∧
    (∀ (model : Model) (strict : Bool),
      r.readout () model K ((lam - b) / g ^ 2 / chi ^ K) strict = eta_b K b) ∧
    (∀ (model : Model) (contract : Contract), contractRate model o b contract = eta_b K b)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have eq := (h (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2).2.1 .original false
  change 0 = actualRate .original 2 ((lam - budget) / g ^ 2 / chi ^ 2) false at eq
  have positive :=
    _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit.actual_rate_positive
      .original (fun _ => false) budget 2 le_rfl budget_interval.1 budget_interval.2 false
  linarith

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.original_actual_count_rate_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.original_actual_count_rate_bridge, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def original_actual_count_rate_bridge_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.original_actual_count_rate_bridge)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ model K => actualRate model K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40.evidence
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
    (fun _ model K => actualRate model K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_actual_count_rate_bridge_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal40
