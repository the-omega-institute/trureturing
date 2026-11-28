import D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
import Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.Common

/-! Source-bound observations of the rotation term and orbital Casimir. -/

open _root_.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace Rotations

abbrev Params :=
  Σ V : Type u, Σ lie : LieRing V, Σ _ : @LieAlgebra ℝ V _ lie, Σ _ : Fin 3 → V, Fin 3

abbrev signature : Signature where
  Params := Params.{u}
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev actual : Realization signature.{u} :=
  realize signature (fun _ p j => by
    rcases p with ⟨V, lie, algebra, L, i⟩
    letI := lie
    letI := algebra
    exact rungeLenzRotation L i j) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [LieRing V] [LieAlgebra ℝ V] (L A : Fin 3 → V),
    (∀ i j, ⁅L i, L j⁆ = r.readout () ⟨V, inferInstance, inferInstance, L, i⟩ j ∧
      ⁅L i, A j⁆ = rungeLenzRotation A i j ∧ ⁅A i, A j⁆ = rungeLenzRotation L i j) ↔
    (∀ i j, ⁅jPlus L A i, jPlus L A j⁆ = rungeLenzRotation (jPlus L A) i j ∧
      ⁅jMinus L A i, jMinus L A j⁆ = rungeLenzRotation (jMinus L A) i j ∧
      ⁅jPlus L A i, jMinus L A j⁆ = 0)

private noncomputable def nonzeroIfAvailable {V : Type*} [Zero V] : V := by
  classical
  exact if h : ∃ v : V, v ≠ 0 then Classical.choose h else 0

private abbrev perturbed : Realization signature.{u} :=
  realize signature (fun _ p _ => by
    letI := p.2.1
    exact nonzeroIfAvailable) (fun e => nomatch e)

private theorem perturbed_rejected : ¬ arena.{u}.Law perturbed := by
  let _ : LieRing (ULift.{u} ℝ) := LieRing.ofAssociativeRing
  intro h
  have hright : ∀ i j : Fin 3,
      ⁅jPlus (0 : Fin 3 → ULift.{u} ℝ) 0 i, jPlus (0 : Fin 3 → ULift.{u} ℝ) 0 j⁆ =
        rungeLenzRotation (jPlus (0 : Fin 3 → ULift.{u} ℝ) 0) i j ∧
      ⁅jMinus (0 : Fin 3 → ULift.{u} ℝ) 0 i, jMinus (0 : Fin 3 → ULift.{u} ℝ) 0 j⁆ =
        rungeLenzRotation (jMinus (0 : Fin 3 → ULift.{u} ℝ) 0) i j ∧
      ⁅jPlus (0 : Fin 3 → ULift.{u} ℝ) 0 i, jMinus (0 : Fin 3 → ULift.{u} ℝ) 0 j⁆ = 0 := by
    intro i j
    simp [jPlus, jMinus, rungeLenzRotation]
  have e := (((h (V := ULift.{u} ℝ) 0 0).2 hright) 0 0).1
  have hExists : ∃ v : ULift.{u} ℝ, v ≠ 0 := ⟨1, one_ne_zero⟩
  have hn : (nonzeroIfAvailable : ULift.{u} ℝ) ≠ 0 := by
    unfold nonzeroIfAvailable
    rw [dite_eq_left hExists]
    exact Classical.choose_spec hExists
  exact hn (by simpa [perturbed, realize] using e.symm)

private theorem varies : ObservationalDependence signature.{u} actual := by
  let _ : LieRing (ULift.{u} ℝ) := LieRing.ofAssociativeRing
  let L : Fin 3 → ULift.{u} ℝ := fun _ => 1
  intro _
  refine ⟨⟨ULift.{u} ℝ, inferInstance, inferInstance, L, 0⟩, 0, 1, ?_⟩
  change rungeLenzRotation L 0 0 ≠ rungeLenzRotation L 0 1
  intro h
  have e := congrArg ULift.down h
  change ULift.down (∑ i : Fin 3,
    crossProduct (Pi.single 0 (1 : ℝ)) (Pi.single 0 1) i • L i) =
      ULift.down (∑ i : Fin 3, crossProduct (Pi.single 0 (1 : ℝ)) (Pi.single 1 1) i • L i) at e
  norm_num [L, Fin.sum_univ_three, cross_apply, Pi.single_apply] at e

def family : Registration arena.{u} (type_of% (@runge_lenz_split_iff.{u})) :=
  { actual := actual
    bridge := Iff.rfl
    variation := ⟨@runge_lenz_split_iff, perturbed, perturbed_rejected⟩
    sensitivity := ⟨fun i => ⟨perturbed, fun j h => (h (Subsingleton.elim j i)).elim,
      rfl, perturbed_rejected⟩, fun e => nomatch e⟩
    dependence := varies }

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@runge_lenz_split_iff.{u}) (Realization signature.{u}) Unit Unit :=
  diracBind%
    `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.runge_lenz_split_iff.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.Rotations.family
    arena family (realize signature (fun _ p j => by
    rcases p with ⟨V, lie, algebra, L, i⟩
    letI := lie
    letI := algebra
    exact rungeLenzRotation L i j) (fun e => nomatch e))
    #[0, 3, 5]
    #[⟨diracPath% runge_lenz_split_iff rungeLenzRotation 6 0, 6, false, none, false⟩]

end Rotations

namespace OrbitalSquares

abbrev Params := Σ R : Type u, Σ _ : Ring R, Fin 3 → R

abbrev signature : Signature where
  Params := Params.{u}
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev actual : Realization signature.{u} :=
  realize signature (fun _ p i => by
    rcases p with ⟨R, ring, L⟩
    letI := ring
    exact L i ^ 2) (fun e => nomatch e)

private abbrev perturbation : Realization signature.{u} :=
  realize signature (fun _ p _ => by
    letI := p.2.1
    exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {R : Type u} [Ring R] [Algebra ℝ R]
    (L A : Fin 3 → R) (_ : ∀ i, L i * A i = A i * L i),
    (∑ i, (r.readout () ⟨R, inferInstance, L⟩ i + A i ^ 2)) =
      (2 : ℝ) • (∑ i, (jPlus L A i ^ 2 + jMinus L A i ^ 2)) ∧
      (∑ i, L i * A i) = (∑ i, (jPlus L A i ^ 2 - jMinus L A i ^ 2))

private theorem perturbation_rejected : ¬ arena.{u}.Law perturbation := by
  intro h
  have hzero := (h (R := ULift.{u} ℝ) 0 0 (fun _ => rfl)).1
  have e := congrArg ULift.down hzero
  simp [perturbation, realize, jPlus, jMinus] at e

private theorem varies : ObservationalDependence signature.{u} actual := by
  intro _
  let L : Fin 3 → ULift.{u} ℝ := fun i => if i = 0 then 1 else 0
  refine ⟨⟨ULift.{u} ℝ, inferInstance, L⟩, 0, 1, ?_⟩
  change L 0 ^ 2 ≠ L 1 ^ 2
  intro h
  have e := congrArg ULift.down h
  norm_num [L] at e

def family : Registration arena.{u} (type_of% (@runge_lenz_casimir_identities.{u})) :=
  { actual := actual
    bridge := Iff.rfl
    variation := ⟨@runge_lenz_casimir_identities, perturbation, perturbation_rejected⟩
    sensitivity := ⟨fun i => ⟨perturbation, fun j h => (h (Subsingleton.elim j i)).elim,
      rfl, perturbation_rejected⟩, fun e => nomatch e⟩
    dependence := varies }

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@runge_lenz_casimir_identities.{u}) (Realization signature.{u}) Unit Unit :=
  diracBind%
    `D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.runge_lenz_casimir_identities.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D.OrbitalSquares.family
    arena family (realize signature (fun _ p i => by
    rcases p with ⟨R, ring, L⟩
    letI := ring
    exact L i ^ 2) (fun e => nomatch e))
    #[0, 3]
    #[⟨diracPath% runge_lenz_casimir_identities HPow.hPow 6 0, 6, false, none, false⟩]

end OrbitalSquares
end
end Reg.D5.S3.Quantum.Gauge.DiracHydrogenFineStructure4D
