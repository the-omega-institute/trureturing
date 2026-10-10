import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient
open _root_.D5.S3.Analytic.SeriesInequalities.PartitionMobiusInversion
open LeanInformationAudit Finset

namespace Reg.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable
local instance {α : Type u} [DecidableEq α] {A : Finset α} :
    LocallyFiniteOrder (Finpartition A) := Fintype.toLocallyFiniteOrder

namespace Coefficient

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => Nat.factorial k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the literal factorial operand is replaced; the full ring-valued identity remains. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {α : Type u} [DecidableEq α] {R : Type v} [CommRing R]
    (s : Finset α) (_hs : s.Nonempty) (P : Finpartition s),
    IncidenceAlgebra.mu R P ⊤ =
      (-1 : R) ^ (P.parts.card - 1) * (r.readout () () (P.parts.card - 1) : R)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have bad := h (R := ULift.{v} ℤ) ({⟨()⟩} : Finset (ULift.{u} Unit))
    (singleton_nonempty _) ⊤
  simp [rejected, realize] at bad

def evidence : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro α _ R _ s hs P
    exact partition_mobius_coefficient s hs P, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 2, by norm_num [actual, realize]⟩

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient.partition_mobius_coefficient.{u,v})
    (type_of% (realize signature (fun _ _ k => Nat.factorial k) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient.Coefficient.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient.Coefficient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨evidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => Nat.factorial k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Coefficient

namespace Inversion

abbrev signature : Signature where
  Params := Σ α : Type u, Σ R : Type v, Finset α → R
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p A => p.2.2 A) (fun e => nomatch e)

/-- The intervention evaluates the supplied cumulant at the empty set. -/
def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p _ => p.2.2 ∅) (fun e => nomatch e)

/-- The complete refinement hypothesis and both conclusions are retained. -/
abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {α : Type u} [DecidableEq α] {R : Type v} [CommRing R]
    (A : Finset α) (_hA : A.Nonempty) (moment cumulant : Finset α → R)
    (_hrelation : ∀ P : Finpartition A,
      partitionProduct moment P = ∑ Q ∈ Iic P, partitionProduct cumulant Q),
    r.readout () ⟨α, R, cumulant⟩ A =
        ∑ P : Finpartition A, partitionMoebiusCoefficient P * partitionProduct moment P ∧
      moment A = ∑ P : Finpartition A, partitionProduct cumulant P

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A : Finset (ULift.{u} Unit) := {⟨()⟩}
  let k : Finset (ULift.{u} Unit) → ULift.{v} ℤ := fun B => if B = ∅ then 0 else 1
  let := (isAtom_singleton (⟨()⟩ : ULift.{u} Unit)).uniqueFinpartition
    (P := (⊤ : Finpartition A))
  have hrelation : ∀ P : Finpartition A,
      partitionProduct k P = ∑ Q ∈ Iic P, partitionProduct k Q := by
    intro P
    have hP : P = ⊤ := Subsingleton.elim _ _
    subst P
    rw [Iic_top, Fintype.sum_unique, Subsingleton.elim (default : Finpartition A) ⊤]
  have good := (moment_cumulant_without_mu_assumption A (singleton_nonempty _) k k hrelation).1
  have bad := (h A (singleton_nonempty _) k k hrelation).1
  rw [← good] at bad
  simp [rejected, realize, k, A] at bad

def evidence : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro α _ R _ A hA moment cumulant hrelation
    exact moment_cumulant_without_mu_assumption A hA moment cumulant hrelation,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, ULift.{v} ℤ, fun B => if B = ∅ then 0 else 1⟩,
      ∅, {⟨()⟩}, ?_⟩
    simp [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient.moment_cumulant_without_mu_assumption.{u,v})
    (type_of% (realize signature.{u,v} (fun _ p A => p.2.2 A) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient.Inversion.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient.Inversion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨evidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ p A => p.2.2 A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient
    definition := none
    coordinates := #[0, 2, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Inversion
end
end Reg.D5.S3.Analytic.SeriesInequalities.PartitionMobiusCoefficient
