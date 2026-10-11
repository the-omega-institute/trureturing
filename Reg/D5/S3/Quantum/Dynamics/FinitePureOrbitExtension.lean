import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
import Reg.Support.DependentFamily
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Field.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension

open _root_.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module

universe u v w

/-- The observed data are the natural cutoff for stabilization. -/
@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun impossible => nomatch impossible)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun impossible => nomatch impossible)

/-- The entire original telescope, with only the conclusion's cutoff observed. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (_hS : iSupIndep S) (_hne : ∀ i, S i ≠ ⊥) (_hcard : 2 ≤ Fintype.card ι)
    (x : V) (_hx : x ≠ 0)
    (_hprefix : ∀ j < 2 * finrank K V - 1, ∃ i, (A ^ j) x ∈ S i),
    (∃ L, 1 ≤ L ∧ L < R.readout () () (2 * finrank K V - 1) ∧
      wordPotential A S (L + 1) = wordPotential A S L) ∧
    ∀ k : ℕ, ∃ i, (A ^ k) x ∈ S i

private theorem actual_law : arena.{u,v,w}.Law actual :=
  @pure_prefix_potential_stabilizes.{u,v,w}

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let K := ULift.{u} ℚ
  let V := ULift.{v} (Fin 2 → ℚ)
  let ι := ULift.{w} (Fin 2)
  let b0 : Basis (Fin 2) K (Fin 2 → ℚ) :=
    (Pi.basisFun ℚ (Fin 2)).mapCoeffs ULift.ringEquiv.symm (fun _ _ => rfl)
  let b : Basis ι K V := (b0.map ULift.moduleEquiv.symm).reindex Equiv.ulift.symm
  letI : Module.Finite K V := Module.Finite.of_basis b
  let S : ι → Submodule K V := fun i => Submodule.span K {b i}
  have hS : iSupIndep S := b.linearIndependent.iSupIndep_span_singleton
  have hne (i : ι) : S i ≠ ⊥ := by
    intro hz
    exact b.ne_zero i (Submodule.span_singleton_eq_bot.mp hz)
  let z : ι := ULift.up 0
  have hx : b z ≠ 0 := b.ne_zero z
  have hp : ∀ j < 2 * finrank K V - 1,
      ∃ i, ((LinearEquiv.refl K V) ^ j) (b z) ∈ S i := by
    intro j _
    refine ⟨z, ?_⟩
    change ((1 : V ≃ₗ[K] V) ^ j) (b z) ∈ S z
    rw [one_pow]
    exact Submodule.subset_span (Set.mem_singleton (b z))
  obtain ⟨L, _, hL, _⟩ :=
    (h (LinearEquiv.refl K V) S hS hne (by simp [ι]) (b z) hx hp).1
  exact Nat.not_lt_zero L hL

def registration : Registration arena.{u,v,w} (arena.{u,v,w}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    exact ⟨(), 0, 1, Nat.zero_ne_one⟩

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@pure_prefix_potential_stabilizes.{u,v,w})
      (type_of% (realize signature (fun _ _ n => n) (fun impossible => nomatch impossible)))
      Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.informationUnit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => n) (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some ℕ,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FinitePureOrbitExtension,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #[],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
