import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped MonoidAlgebra

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension
universe uV
noncomputable section

abbrev signature : Signature where
  Params := Σ p : ℕ, Σ V : Type uV, Σ _ : AddCommGroup V,
    Σ _ : Module (ZMod p) V, Representation (ZMod p) (Multiplicative (ZMod p × ZMod p)) V
  State q := Subgroup (Multiplicative (ZMod q.1 × ZMod q.1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uV} :=
  realize signature (fun _ q H =>
    letI := q.2.2.1
    letI := q.2.2.2.1
    Module.Projective (ZMod q.1)[H]
      (Representation.asModule (q.2.2.2.2.comp H.subtype))) (fun e => nomatch e)

def rejected : Realization signature.{uV} :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{uV}
  Law r := ∀ {p : ℕ} [Fact p.Prime] {V : Type uV}
    [add : AddCommGroup V] [mod : Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (ρ : Representation (ZMod p) (Multiplicative (ZMod p × ZMod p)) V),
    (∀ H : Subgroup (Multiplicative (ZMod p × ZMod p)), IsCyclic H →
      r.readout () ⟨p, V, add, mod, ρ⟩ H) →
    2 * p ≤ Module.finrank (ZMod p) V

private theorem rejected_law : ¬ arena.{uV}.Law rejected := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro h
  have he := h (p := 2) (V := ULift.{uV} (ZMod 2))
    (Representation.trivial (ZMod 2) (Multiplicative (ZMod 2 × ZMod 2))
      (ULift.{uV} (ZMod 2))) (by intro H hH; trivial)
  simpa using he

def family : Registration arena.{uV}
    (type_of% @_root_.D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension.two_mul_prime_le_finrank_of_cyclic_projective.{uV}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension.two_mul_prime_le_finrank_of_cyclic_projective.{uV},
    rejected, rejected_law⟩
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
    letI : Fact (Nat.Prime 2) := ⟨by decide⟩
    let V := ULift.{uV} (ZMod 2)
    let ρ := Representation.trivial (ZMod 2) (Multiplicative (ZMod 2 × ZMod 2)) V
    have hnot : ¬ ∀ H : Subgroup (Multiplicative (ZMod 2 × ZMod 2)), IsCyclic H →
        Module.Projective (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) := by
      intro h
      have he := _root_.D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension.two_mul_prime_le_finrank_of_cyclic_projective ρ h
      simpa [V] using he
    classical
    obtain ⟨H, hH⟩ := not_forall.mp hnot
    have hbad : ¬ Module.Projective (ZMod 2)[H]
        (Representation.asModule (ρ.comp H.subtype)) := fun h => hH (fun _ => h)
    have hbot : Module.Projective (ZMod 2)[(⊥ : Subgroup (Multiplicative (ZMod 2 × ZMod 2)))]
        (Representation.asModule (ρ.comp (⊥ : Subgroup (Multiplicative (ZMod 2 × ZMod 2))).subtype)) := by
      apply (_root_.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace.projective_iff_projective_and_conjugation_trace_one _).mpr
      refine ⟨inferInstance, 1, ?_⟩
      simp [ρ, Representation.trivial]
      rfl
    refine ⟨⟨2, V, inferInstance, inferInstance, ρ⟩, ⊥, H, ?_⟩
    change Module.Projective (ZMod 2)[(⊥ : Subgroup (Multiplicative (ZMod 2 × ZMod 2)))]
      (Representation.asModule (ρ.comp (⊥ : Subgroup (Multiplicative (ZMod 2 × ZMod 2))).subtype)) ≠
      Module.Projective (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype))
    exact fun he => hbad (he ▸ hbot)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension.two_mul_prime_le_finrank_of_cyclic_projective.{uV})
    (type_of% actual.{uV}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension.two_mul_prime_le_finrank_of_cyclic_projective.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension
    definition := none
    coordinates := #[0, 2, 3, 4, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension
