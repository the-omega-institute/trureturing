import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding

namespace Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding

open scoped BigOperators
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ m : ℕ, Fin m
  State := fun a => Fin a.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (a : Σ m : ℕ, Fin m), (Fin a.1 → ℝ) → Prop :=
  fun _ a p => _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw a.1 p a.2

def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ (p : Fin m → ℝ) (k : Fin m),
    (∀ i, 0 < p i) → (∑ i, p i) = 1 → (∀ i, p k ≤ p i) →
    DyadicSupportLines.cost p / p k = OptimalLawStrictSlope.alpha m →
      R.readout () ⟨m, k⟩ p

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, k, hp, hs, hk, ho⟩ := OptimalLawStrictSlope.attained 2 (by decide)
  exact h 2 (by decide) p k hp hs hk ho

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result, rejected, rejected_law⟩
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
    change _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw
      2 (fun _ => 0) 0 ≠ _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.StrictlyRoundedLaw 2 q 0
    intro E
    exact bad (E ▸ good)

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
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
