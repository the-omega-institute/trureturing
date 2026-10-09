import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
import Mathlib.NumberTheory.Real.Irrational

namespace Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

open scoped BigOperators
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Rational

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : Unit), ℕ → ℝ := fun _ _ m => OptimalLawStrictSlope.alpha m

def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∃ A : ℚ, 0 < A ∧ (A : ℝ) = R.readout () () m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA, he⟩ := h 2 (by decide)
  have he' : (A : ℝ) = 0 := he
  have hp : (0 : ℝ) < A := by exact_mod_cast hA
  linarith

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_alpha)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_alpha, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change OptimalLawStrictSlope.alpha 1 ≠ OptimalLawStrictSlope.alpha 2
    rw [OptimalLawStrictSlope.result.1, OptimalLawStrictSlope.result.2.1]
    norm_num

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_alpha) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_alpha "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.Rational.proof_record
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
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rational

namespace Full

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : Unit), ℕ → ℝ := fun _ _ m => OptimalLawStrictSlope.alpha m

def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∃ A : ℚ, 0 < A ∧ (A : ℝ) = R.readout () () m ∧
    ∀ x : ℝ, TriangularFirstSplitRecurrence.W x m 1 = 0 ↔ x = (A : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA, he, rest⟩ := h 2 (by decide)
  have he' : (A : ℝ) = 0 := he
  have hp : (0 : ℝ) < A := by exact_mod_cast hA
  linarith

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change OptimalLawStrictSlope.alpha 1 ≠ OptimalLawStrictSlope.alpha 2
    rw [OptimalLawStrictSlope.result.1, OptimalLawStrictSlope.result.2.1]
    norm_num

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.result) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.result "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.Full.proof_record
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
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Full

namespace Zero

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : ℕ), ℝ → ℝ :=
  fun _ m x => TriangularFirstSplitRecurrence.W x m 1

def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ (x : ℝ),
    R.readout () m x = 0 ↔ x = OptimalLawStrictSlope.alpha m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h 2 (by decide) 0).mp rfl
  change (0 : ℝ) = OptimalLawStrictSlope.alpha 2 at H
  rw [OptimalLawStrictSlope.result.2.1] at H
  norm_num at H

def proof_record : Registration arena
    (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, 0, 2, ?_⟩
    have zero := (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha
      2 (by decide) 2).mpr OptimalLawStrictSlope.result.2.1.symm
    have nonzero : TriangularFirstSplitRecurrence.W 0 2 1 ≠ 0 := by
      intro H
      have E := (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha
        2 (by decide) 0).mp H
      rw [OptimalLawStrictSlope.result.2.1] at E
      norm_num at E
    change TriangularFirstSplitRecurrence.W 0 2 1 ≠ TriangularFirstSplitRecurrence.W 2 2 1
    rwa [zero]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.Zero.proof_record
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
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Zero

namespace Cost

abbrev signature : Signature where
  Params := ℕ
  State := fun m => Fin m → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (m : ℕ), (Fin m → ℝ) → ℝ :=
  fun _ _ p => DyadicSupportLines.cost p

def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => Real.sqrt 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (p : Fin m → ℝ),
    (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
    (∀ i, ∃ q : ℚ, (q : ℝ) = p i) → ∃ v : ℚ, (v : ℝ) = R.readout () m p

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v, hv⟩ := h 1 (fun _ => 1) (by simp) (by simp) (fun _ => ⟨1, by simp⟩)
  exact irrational_sqrt_two.ne_rat v hv.symm

def proof_record : Registration arena
    (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_law_cost)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_law_cost,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let u : Fin 2 → ℝ := fun _ => 1 / 2
    have hu : 1 ≤ DyadicSupportLines.cost u :=
      OptimalLawStrictSlope.cost_ge_one 2 (by decide) u (by norm_num [u]) (by norm_num [u])
    have hz : DyadicSupportLines.cost (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
      simp [DyadicSupportLines.cost, DyadicSupportLines.residual]
    refine ⟨2, (fun _ => 0), u, ?_⟩
    change DyadicSupportLines.cost (fun _ : Fin 2 => (0 : ℝ)) ≠ DyadicSupportLines.cost u
    rw [hz]
    linarith

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_law_cost)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_law_cost "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.Cost.proof_record
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
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cost

end

end Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
