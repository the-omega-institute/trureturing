import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
import Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
import Reg.Support.DependentFamily

namespace Reg.Catalogs.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.RootCatalog
open LeanInformationAudit

def rootCatalog.{u_1} : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.RootCatalog,
  expected := #[{ statement := (∀ {A : Type u_1} [inst : Fintype.{u_1} A] [inst_1 : Nonempty.{u_1 + 1} A] (c : List.{u_1} A → A → Real) (hc : ∀ (h : List.{u_1} A) (x : A), @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (c h x)), List.TFAE (@List.cons.{0} Prop (∀ (omega : Nat → A), @Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => @D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.pathClock.{u_1} A c (@List.ofFn.{u_1} A n fun (i : Fin n) => omega (@Fin.val n i))) (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)) (@List.cons.{0} Prop (@Filter.Tendsto.{0, 0} Nat Real (@D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.minimumPathClock.{u_1} A inst inst_1 c) (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)) (@List.cons.{0} Prop (∀ (b : Real), @Set.Finite.{u_1} (List.{u_1} A) (@Set.ofPred.{u_1} (List.{u_1} A) fun (h : List.{u_1} A) => @LE.le.{0} Real Real.instLE (@D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.pathClock.{u_1} A c h) b)) (@List.nil.{0} Prop))))), proof := (@_root_.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.finite_branching_path_clock_criterion.{u_1}), theoremName := `D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.finite_branching_path_clock_criterion, objectArenaName := `Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.arena, statementIdentity := none, registrationModuleName := `Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion }],
  source := #[{ statement := (∀ {A : Type u_1} [inst : Fintype.{u_1} A] [inst_1 : Nonempty.{u_1 + 1} A] (c : List.{u_1} A → A → Real) (hc : ∀ (h : List.{u_1} A) (x : A), @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (c h x)), List.TFAE (@List.cons.{0} Prop (∀ (omega : Nat → A), @Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => @D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.pathClock.{u_1} A c (@List.ofFn.{u_1} A n fun (i : Fin n) => omega (@Fin.val n i))) (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)) (@List.cons.{0} Prop (@Filter.Tendsto.{0, 0} Nat Real (@D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.minimumPathClock.{u_1} A inst inst_1 c) (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)) (@List.cons.{0} Prop (∀ (b : Real), @Set.Finite.{u_1} (List.{u_1} A) (@Set.ofPred.{u_1} (List.{u_1} A) fun (h : List.{u_1} A) => @LE.le.{0} Real Real.instLE (@D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.pathClock.{u_1} A c h) b)) (@List.nil.{0} Prop))))), proof := (@_root_.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.finite_branching_path_clock_criterion.{u_1}), theoremName := `D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.finite_branching_path_clock_criterion, objectArenaName := `Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.arena, statementIdentity := none, registrationModuleName := `Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion } }

end Reg.Catalogs.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.RootCatalog
