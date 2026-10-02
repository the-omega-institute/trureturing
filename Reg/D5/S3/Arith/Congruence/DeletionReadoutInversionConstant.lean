import D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean Elab Command
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant

@[reducible] def signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State p := (∀ i, Fin (p.2 i)) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (∀ i, Fin (p.2 i)) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z ↦ z) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z c ↦ z c + 1) (fun e ↦ nomatch e)

def arena : Arena where
  signature := signature
  Law readout := ∀ (r : ℕ) (m : Fin r → ℕ) (hm : ∀ i, 2 ≤ m i)
      (z : (∀ i, Fin (m i)) → ℝ),
    (∀ c, |(readout.readout () ⟨r, m⟩ z) c| ≤ kappa m * obsNorm m hm z) ∧
      ∀ cstar : ∀ i, Fin (m i),
        let w : (∀ i, Fin (m i)) → ℝ := fun c ↦
          ∏ i, if c i = cstar i then 2 * (m i : ℝ) - 3 else -1
        obsNorm m hm w = ∏ i, ((m i : ℝ) - 1) ∧
          |w cstar| = kappa m * obsNorm m hm w

theorem actual_law : arena.Law actual := by
  intro r m hm z
  simpa only [actual, realize] using deletion_readout_inversion_constant r m hm z

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let m : Fin 0 → ℕ := fun i ↦ nomatch i
  let point : ∀ i, Fin (m i) := fun i ↦ nomatch i
  let zero : (∀ i, Fin (m i)) → ℝ := fun _ ↦ 0
  have hbound := (h 0 m (fun i ↦ nomatch i) zero).1 point
  norm_num [rejected, realize, signature, kappa, obsNorm, R, m, point, zero] at hbound

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  let p : signature.Params := ⟨0, fun i ↦ nomatch i⟩
  let zero : signature.State p := fun _ ↦ 0
  let one : signature.State p := fun _ ↦ 1
  refine ⟨p, zero, one, ?_⟩
  intro h
  have hvalue := congrFun h (fun i ↦ nomatch i)
  norm_num [actual, realize, zero, one] at hvalue

def registration : Registration arena
    (∀ (r : ℕ) (m : Fin r → ℕ) (hm : ∀ i, 2 ≤ m i)
      (z : (∀ i, Fin (m i)) → ℝ),
      (∀ c, |z c| ≤ kappa m * obsNorm m hm z) ∧
        ∀ cstar : ∀ i, Fin (m i),
          let w : (∀ i, Fin (m i)) → ℝ := fun c ↦
            ∏ i, if c i = cstar i then 2 * (m i : ℝ) - 3 else -1
          obsNorm m hm w = ∏ i, ((m i : ℝ) - 1) ∧
            |w cstar| = kappa m * obsNorm m hm w) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

run_cmd do
  let root := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
  let sourceName :=
    `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant ++
      `deletion_readout_inversion_constant
  let identity :=
    "sha256:e966c7ce23573134dc68ddf3e326660ce55e57c5de082808fe605407e9440a1d"
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

register_information_theorem deletion_readout_inversion_constant in arena
  readout via (realize signature (fun _ _ z ↦ z) (fun e ↦ nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body",
        "fn", "arg", "arg", "fn"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
