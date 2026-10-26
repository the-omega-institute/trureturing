import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum

open LeanInformationAudit
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum
open _root_.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => maximumWeight n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 1 ≤ n),
    (∀ (A : Type*) [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
      (ι : Type*) [Fintype ι] (hd : Module.finrank ℂ A = n)
      (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (b : Module.Basis ι ℂ A),
      (∀ i j : ι, i ≠ j → μ (b i) (b j) = 0) → productSpan μ = ⊤ →
        Finite (Aut μ) ∧ Nat.card (Aut μ) ≤ R.readout () () n) ∧
    (∃ μ : Product n, Module.finrank ℂ (Coord n) = n ∧ commutative μ ∧
      hasNaturalBasis μ ∧ productSpan μ = ⊤ ∧
      Finite (Aut μ) ∧ Nat.card (Aut μ) = R.readout () () n)

theorem actual_law : arena.Law actual := result

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨μ, hd, hc, hb, hp, hf, hcard⟩ := (h 1 (by decide)).2
  haveI : Finite (Aut μ) := hf
  have hpos : 0 < Nat.card (Aut μ) := Nat.card_pos
  change Nat.card (Aut μ) = 0 at hcard
  omega

def registration : Registration arena (type_of% (@result)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change maximumWeight 1 ≠ maximumWeight 2
    rw [maximum_weight_small.1, maximum_weight_small.2.1]
    decide }

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (type_of% actual) (Unit → Type) Unit := {
  unitName := `D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum.result.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismMaximum
