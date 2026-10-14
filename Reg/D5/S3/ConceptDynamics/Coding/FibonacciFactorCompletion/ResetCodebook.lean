import Reg.Support.FibonacciOriginalSourceWitness.PositiveTiling
import Reg.Support.FibonacciOriginalSourceWitness.Source135
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook

noncomputable section

abbrev seedSignature : Signature where
  Params := Σ _ : List Return, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def seedActual : Realization seedSignature :=
  realize seedSignature (fun _ p y => execute .high p.1 y) (fun e => nomatch e)

def seedRejected : Realization seedSignature :=
  realize seedSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev seedArena : Arena where
  signature := seedSignature
  Law R := ∀ (xs : List Return) (x y : ℝ),
    R.readout () ⟨xs, x⟩ y - execute .high xs x = g ^ listWeight xs * (y - x)

theorem seed_rejected_law : ¬ seedArena.Law seedRejected := by
  intro h
  have hh := h [] 0 1
  norm_num [seedRejected, realize, execute, listWeight] at hh

def seedRegistration : Registration seedArena
    (∀ (xs : List Return) (x y : ℝ),
      execute .high xs y - execute .high xs x = g ^ listWeight xs * (y - x)) where
  actual := seedActual
  bridge := Iff.rfl
  variation := ⟨execute_seed_difference, seedRejected, seed_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seedRejected, ?_, rfl, seed_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨[], 0⟩, 0, 1, ?_⟩
    norm_num [seedActual, realize, execute]

def execute_seed_difference_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.execute_seed_difference)
      (type_of% (realize.{0,0,0,0,0} seedSignature
        (fun _ p y => execute .high p.1 y) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.execute_seed_difference_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.seedRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨seedArena⟩
  objectArena := .source ⟨seedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source seedArena ⟨seedRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} seedSignature
    (fun _ p y => execute .high p.1 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms seedRegistration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := List Return
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ xs E => execute .high xs E) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => aSide .high) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K N : ℕ) (d B : ℝ) (model : Model) (xs : List Return)
    (weak : GuardTrace K d false .high xs (initial .high model))
    (weight : listWeight xs = N) (above : initial .high model < B)
    (E : ℝ) (raised : B ≤ E),
    GuardTrace K (d + (B-initial .high model)*g^N) false .high xs E ∧
    aSide .high < r.readout () xs E

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h 0 0 0 (initial .high .original + 1) .original []
    trivial rfl (by linarith) (initial .high .original + 1) le_rfl).2
  exact lt_irrefl _ impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.exact_guard_gain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.exact_guard_gain, rejected, rejected_law⟩
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
    refine ⟨[], 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def exact_guard_gain_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.exact_guard_gain)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ xs E => execute .high xs E) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ xs E => execute .high xs E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms exact_guard_gain_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal132

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℤ → List CuLetter, ℤ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p n => (blockWindow p.1 p.2 n).length) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (W : ℤ → List CuLetter) (positive : ∀ j, 0 < (W j).length) (a : ℤ) (n : ℕ),
    (r.readout () ⟨W, a⟩ n : ℤ) = blockCut W (a+n)-blockCut W a ∧
    ∀ j : ℕ, j < n → ∀ k : ℕ, k < (W (a+(j : ℤ))).length →
      (blockWindow W a n)[(blockCut W (a+(j : ℤ))-blockCut W a).toNat+k]?.getD .u =
        (W (a+(j : ℤ)))[k]?.getD .u

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h (fun _ => [.u]) (by intro j; simp) 0 0).1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.block_window_positions) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.block_window_positions, rejected, rejected_law⟩
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
    refine ⟨⟨(fun _ => [.u]), 0⟩, 0, 1, ?_⟩
    simp [actual, realize, blockWindow]

def block_window_positions_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.block_window_positions)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p n => (blockWindow p.1 p.2 n).length) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p n => (blockWindow p.1 p.2 n).length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms block_window_positions_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal134

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.SetWitness
noncomputable section

def spike (i : ℤ) : CuLetter := if i = 0 then .c else .u

theorem spike_eq_c (i : ℤ) : spike i = .c ↔ i = 0 := by
  by_cases h : i = 0 <;> simp [spike, h]

theorem spike_forward (i : ℤ) (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∀ k : Fin m, spike (i + (k : ℕ)) = .c := by
  intro h
  have h0 := (spike_eq_c _).mp (h ⟨0, by omega⟩)
  have h1 := (spike_eq_c _).mp (h ⟨1, by omega⟩)
  simp only [Nat.cast_zero, Nat.cast_one, add_zero] at h0 h1
  omega

theorem spike_backward (i : ℤ) :
    ¬ ∀ k : Fin 2, spike (i - (k : ℕ)) = .c := by
  intro h
  have h0 := (spike_eq_c _).mp (h ⟨0, by omega⟩)
  have h1 := (spike_eq_c _).mp (h ⟨1, by omega⟩)
  simp only [Nat.cast_zero, Nat.cast_one, sub_zero] at h0 h1
  omega

theorem spike_low_two : spike ∈ LowCapLanguage 2 :=
  fun i => spike_forward i 2 le_rfl

theorem spike_not_low_one : spike ∉ LowCapLanguage 1 := by
  intro h
  apply h 0
  intro k
  have hk : k.val = 0 := by omega
  simp [spike, hk]

theorem all_u_memory (side : MemorySide) (n K : ℕ) (d : ℝ) (positive : 0 < K) :
    (fun _ : ℤ => CuLetter.u) ∈ MemoryLanguage side n K d := by
  apply original_low_cap_inclusion side n K d positive
  intro i h
  have bad := h ⟨0, positive⟩
  cases bad

theorem upper_separation :
    MemoryLanguage .upper 0 1 (hSide .high + 1) ≠
      MemoryLanguage .upper 0 2 (hSide .high + 1) := by
  have yes : spike ∈ MemoryLanguage .upper 0 2 (hSide .high + 1) :=
    ⟨fun i => spike_forward i 3 (by omega), fun i h => (spike_backward i h).elim⟩
  have no : spike ∉ MemoryLanguage .upper 0 1 (hSide .high + 1) := by
    intro h
    have run : ∀ k : Fin 1, spike (0 - (k : ℕ)) = .c := by
      intro k
      have hk : k.val = 0 := by omega
      simp [spike, hk]
    have bad := h.2 0 run
    norm_num [finitePast] at bad
  intro h
  exact no (h ▸ yes)

theorem lower_separation : LowerMemoryLanguage 0 1 0 ≠ LowerMemoryLanguage 0 2 0 := by
  have yes : spike ∈ LowerMemoryLanguage 0 2 0 :=
    ⟨fun i => spike_forward i 3 (by omega), fun i h => (spike_backward i h).elim⟩
  have no : spike ∉ LowerMemoryLanguage 0 1 0 := by
    intro h
    have run : ∀ k : Fin 1, spike (0 - (k : ℕ)) = .c := by
      intro k
      have hk : k.val = 0 := by omega
      simp [spike, hk]
    have bad := h.2 0 run
    norm_num [finitePast] at bad
  intro h
  exact no (h ▸ yes)

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.SetWitness

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.SetWitness


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal136
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℕ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set (ℤ → CuLetter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p K => LowerMemoryLanguage p.1 K p.2) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (ω : ℤ → CuLetter) (n K : ℕ) (d gamma : ℝ)
    (guard : ω ∈ AuxiliaryLanguage K (d+gamma))
    (small : hSide .high*rho^n < chi^(K-1)*gamma), ω ∈ r.readout () ⟨n,d⟩ K

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have guard : (fun _ : ℤ => CuLetter.u) ∈ AuxiliaryLanguage 1 (0 + (hSide .high + 1)) := by
    constructor
    · intro i run
      have bad := run ⟨0, by norm_num⟩
      cases bad
    · intro i run
      have bad := run ⟨0, by norm_num⟩
      cases bad
  exact h (fun _ => CuLetter.u) 0 1 0 (hSide .high + 1) guard (by simp)

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.uniform_guard_lower_memory) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.uniform_guard_lower_memory, rejected, rejected_law⟩
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
    exact ⟨⟨0, 0⟩, 1, 2, lower_separation⟩

def uniform_guard_lower_memory_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.uniform_guard_lower_memory)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p K => LowerMemoryLanguage p.1 K p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal136.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal136.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p K => LowerMemoryLanguage p.1 K p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms uniform_guard_lower_memory_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal136

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal133
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature
    (fun _ K b => b -
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actualAutomaticCost K)
    (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam-g^2*chi^K*hSide .high < b)
    (hbp : b < lam-g^2*chi^K*(aSide .high/(1-rho*chi^K))),
    ∃ R : Return, R.r = 1 ∧
    (max (max (xSide .high) (ySide .high)) ((lam-b)/g^2/chi^K) <
      hSide .high-rho^R.m*(hSide .high-chi*aSide .high)) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam-b)/g^2/chi^K
    let B := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)
    let delta := B-initial .high sourceModel
    let gamma := delta*g^N
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs=N}
    0 < delta ∧ 0 < gamma ∧
    0 < min (r.readout () K b) (g^2*chi^K*gamma)/2 ∧
    (∀ (targetModel : Model) (words : List V),
      let execution := resetConcatenation R (words.map Subtype.val)
      GuardTrace K (d+gamma) false .high execution (initial .high targetModel) ∧
      ActualPairSupply targetModel o
        (b-min (b-actualAutomaticCost K) (g^2*chi^K*gamma)/2) .strict execution) ∧
    (∃ n : ℕ, K ≤ n ∧ hSide .high*rho^n < chi^(K-1)*gamma) ∧
    (∀ choices : ℤ → V,
      let W := fun j => executionWord (R::(choices j).val)
      blockCut W 0 = 0 ∧
      (∀ j, blockCut W (j+1)=blockCut W j+(W j).length) ∧
      StrictMono (blockCut W) ∧
      ∃ ω : ℤ → CuLetter, ∀ j (k : Fin (W j).length),
        ω (blockCut W j+(k : ℕ))=(W j)[k])

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hqb, hbp⟩ :=
    _root_.Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.record_interval_nonempty
  obtain ⟨R, _, _, family⟩ := h (fun _ => false) b 2 (by decide) hqb hbp
  have positive := (family .original 1 (by decide)).2.2.1
  dsimp only [rejected, realize] at positive
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg
    (min_le_left (0 : ℝ) _) (by norm_num))) positive

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.reset_codebook_construction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.reset_codebook_construction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := by
    intro i
    obtain ⟨_, x, y, different⟩ :=
      _root_.Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence i
    change x ≠ y at different
    refine ⟨2, x, y, ?_⟩
    change x - actualAutomaticCost 2 ≠ y - actualAutomaticCost 2
    exact fun equal => different (sub_left_inj.mp equal)

def reset_codebook_construction_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.reset_codebook_construction)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ K b => b -
          _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actualAutomaticCost K)
        (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal133.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal133.evidence
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
    (fun _ K b => b -
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actualAutomaticCost K)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms reset_codebook_construction_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal133

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal137
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature
    (fun _ K b => b -
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actualAutomaticCost K)
    (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam-g^2*chi^K*hSide .high < b)
    (hbp : b < lam-g^2*chi^K*(aSide .high/(1-rho*chi^K))),
    ∃ R : Return, R.r=1 ∧
    (max (max (xSide .high) (ySide .high)) ((lam-b)/g^2/chi^K) <
      hSide .high-rho^R.m*(hSide .high-chi*aSide .high)) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam-b)/g^2/chi^K
    let B := hSide .high-rho^R.m*(hSide .high-chi*aSide .high)
    let delta := B-initial .high sourceModel
    let gamma := delta*g^N
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs=N}
    0 < delta ∧ 0 < gamma ∧
    0 < min (r.readout () K b) (g^2*chi^K*gamma)/2 ∧
    (∀ (targetModel : Model) (words : List V),
      let execution := resetConcatenation R (words.map Subtype.val)
      GuardTrace K (d+gamma) false .high execution (initial .high targetModel) ∧
      ActualPairSupply targetModel o
        (b-min (b-actualAutomaticCost K) (g^2*chi^K*gamma)/2) .strict execution) ∧
    ∃ n : ℕ, K ≤ n ∧
      hSide .high*rho^n < chi^(K-1)*gamma ∧
      ∀ choices : ℤ → V,
        let W := fun j => executionWord (R::(choices j).val)
        ∃ ω : ℤ → CuLetter,
          ω ∈ AuxiliaryLanguage K (d+gamma) ∧ ω ∈ LowerMemoryLanguage n K d ∧
          (∀ j (k : Fin (W j).length), ω (blockCut W j+(k : ℕ))=(W j)[k]) ∧
          (∀ j, GuardTrace K (d+gamma) false .high (R::(choices j).val)
            (pastState ω (blockCut W j)))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hqb, hbp⟩ :=
    _root_.Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.record_interval_nonempty
  obtain ⟨R, _, _, family⟩ := h (fun _ => false) b 2 (by decide) hqb hbp
  have positive := (family .original 1 (by decide)).2.2.1
  dsimp only [rejected, realize] at positive
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg
    (min_le_left (0 : ℝ) _) (by norm_num))) positive

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.bilateral_reset_codebook) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.bilateral_reset_codebook, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := by
    intro i
    obtain ⟨_, x, y, different⟩ :=
      _root_.Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence i
    change x ≠ y at different
    refine ⟨2, x, y, ?_⟩
    change x - actualAutomaticCost 2 ≠ y - actualAutomaticCost 2
    exact fun equal => different (sub_left_inj.mp equal)

def bilateral_reset_codebook_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.bilateral_reset_codebook)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ K b => b -
          _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actualAutomaticCost K)
        (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal137.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal137.evidence
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
    (fun _ K b => b -
      _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actualAutomaticCost K)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms bilateral_reset_codebook_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.ExactOriginal137

namespace Reg.Support.FibonacciOriginalSourceWitness.Source135
noncomputable section

def original_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.compact_block_tiling)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ ω => ω) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.Support.FibonacciOriginalSourceWitness.Source135.original_unit
  realizationName := `Reg.Support.FibonacciOriginalSourceWitness.Source135.evidence
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
    (fun _ _ ω => ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_registration
end
end Reg.Support.FibonacciOriginalSourceWitness.Source135

open Reg.Support.FibonacciOriginalSourceWitness.PositiveTiling in
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.positive_block_tiling_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.positive_block_tiling)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ ω => ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.positive_block_tiling_registration_unit, realizationName := `Reg.Support.FibonacciOriginalSourceWitness.PositiveTiling.evidence,
  realizationSource := none, generated := false, arena := .source ⟨sourceArena⟩,
  objectArena := .source ⟨sourceArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sourceArena ⟨evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ ω => ω) (fun e => nomatch e)), variation := .absent,
  sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "arg", "arg", "arg", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
