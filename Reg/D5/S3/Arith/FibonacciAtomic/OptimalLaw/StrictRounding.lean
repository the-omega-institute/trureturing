import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding

namespace Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding

open scoped BigOperators Classical
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ m : ℕ, Fin m
  State := fun a => Fin a.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (a : Σ m : ℕ, Fin m), (Fin a.1 → ℝ) → Bool :=
  fun _ a p => decide (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw a.1 p a.2)

def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ (p : Fin m → ℝ) (k : Fin m),
    (∀ i, 0 < p i) → (∑ i, p i) = 1 → (∀ i, p k ≤ p i) →
    DyadicSupportLines.cost p / p k = OptimalLawStrictSlope.alpha m →
      R.readout () ⟨m, k⟩ p = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, k, hp, hs, hk, ho⟩ := OptimalLawStrictSlope.attained 2 (by decide)
  have H := h 2 (by decide) p k hp hs hk ho
  change false = true at H
  cases H

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result)) where
  actual := actual
  bridge := by simp [arena, actual, observation, realize, Realization.readout]
  variation := ⟨by
    simpa [arena, actual, observation, realize, Realization.readout] using
      _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    let q : Fin 2 → ℝ := fun j => if j = 0 then 0 else 1
    have good : _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw
        2 (fun _ => 0) 0 := by
      intro j hj
      norm_num at hj
    have bad : ¬ _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw
        2 q 0 := by
      intro h
      have hj : q 0 < q 1 := by norm_num [q]
      obtain ⟨D, hD, hg, hleast, hr⟩ := h 1 hj
      apply hleast 0 (by omega)
      refine ⟨1, ?_⟩
      norm_num [q]
    refine ⟨⟨2, 0⟩, (fun _ => 0), q, ?_⟩
    change decide (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw
      2 (fun _ => 0) 0) ≠ decide (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw 2 q 0)
    simp only [good, bad, decide_true, decide_false, ne_eq, Bool.true_eq_false, not_false_eq_true]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Grid
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : Σ _ : ℕ, ℕ), ℝ → Bool :=
  fun _ a x => decide (OnGrid x a.2)
def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (D E : ℕ), D ≤ E → OnGrid x D → R.readout () ⟨D, E⟩ x = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 0 0 0 le_rfl ⟨0, by simp⟩
  change false = true at H
  cases H

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.grid_up)) where
  actual := actual
  bridge := by simp [arena, actual, observation, realize, Realization.readout]
  variation := ⟨by
    simpa [arena, actual, observation, realize, Realization.readout] using
      _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.grid_up, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    have good : OnGrid 0 0 := ⟨0, by simp⟩
    have bad : ¬OnGrid (1 / 2) 0 := by
      rintro ⟨z, hz⟩
      have F : z = ⌊(1 / 2 : ℝ)⌋ := by
        rw [show (1 / 2 : ℝ) = z by simpa using hz, Int.floor_intCast]
      norm_num at F
      subst z
      norm_num at hz
    refine ⟨⟨0, 0⟩, 0, 1 / 2, ?_⟩
    change decide (OnGrid 0 0) ≠ decide (OnGrid (1 / 2) 0)
    simp only [good, bad, decide_true, decide_false, ne_eq, Bool.true_eq_false, not_false_eq_true]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.grid_up) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.grid_up "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.Grid.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Grid

namespace Least
abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : ℕ), ℝ → ℤ := fun _ D x => ⌊(2 : ℝ) ^ D * x⌋
def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (D : ℕ), 1 ≤ D → OnGrid x D →
    (∀ d < D, ¬OnGrid x d) → R.readout () D x = 2 * ⌊(2 : ℝ) ^ (D - 1) * x⌋ + 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have grid : OnGrid (1 / 2) 1 := ⟨1, by norm_num⟩
  have least : ∀ d < 1, ¬OnGrid (1 / 2) d := by
    intro d hd
    have : d = 0 := by omega
    subst d
    rintro ⟨z, hz⟩
    have F : z = ⌊(1 / 2 : ℝ)⌋ := by rw [show (1 / 2 : ℝ) = z by simpa using hz, Int.floor_intCast]
    norm_num at F
    subst z
    norm_num at hz
  have H := h (1 / 2) 1 (by decide) grid least
  norm_num [rejected, realize, Realization.readout] at H

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.least_grid_bit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.least_grid_bit, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, observation, realize, Realization.readout]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.least_grid_bit) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.least_grid_bit "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.Least.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Least

end

end Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
