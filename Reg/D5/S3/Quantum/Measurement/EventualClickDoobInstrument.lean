import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.EventualClickDoobInstrument
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Measurement.EventualClickDoobInstrument
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open Filter LeanInformationAudit Matrix Topology
open Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument

@[reducible] def effectSignature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization effectSignature :=
  realize effectSignature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization effectSignature :=
  realize effectSignature (fun _ _ F => F + 1) (fun e => nomatch e)

def arena : Arena where
  signature := effectSignature
  Law S := ∀ {d : ℕ} {α ξ β : Type}
    [Fintype α] [Fintype ξ] [Fintype β]
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ξ → β → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ x, ∑ b, (L x b)ᴴ * L x b = 1)
    (F : Matrix (Fin d) (Fin d) ℂ)
    (_hF : Tendsto (survival Q) atTop (𝓝 F)),
    let N := PhyslibLeaf.MatrixMap.of_kraus Q Q
    let C := fun x => PhyslibLeaf.MatrixMap.of_kraus (L x) (L x)
    let R := 1 - S.readout () d F
    let P := spectralSupport R
    let G := cfc (fun t : ℝ => Real.sqrt t) R
    let Gplus := spectralInverseSqrt R
    let Ntilde := fun X => G * N (Gplus * X * Gplus) * G
    let Ctilde := fun x X => C x (Gplus * X * Gplus)
    R = noClickDual Q R + ∑ x, noClickDual (L x) 1 ∧
    (∀ a, P * Q a * (1 - P) = 0) ∧
    (∀ x b, L x b * (1 - P) = 0) ∧
    (∀ H, H = P * H * P → noClickDual Q H = P * noClickDual Q H * P) ∧
    (∀ x Z, noClickDual (L x) Z = P * noClickDual (L x) Z * P) ∧
    Gplus * G = P ∧ G * Gplus = P ∧ P * G = G ∧
    (∀ X, Ntilde X =
      ∑ a, (G * Q a * Gplus) * X * (G * Q a * Gplus)ᴴ) ∧
    (∀ x X, Ctilde x X =
      ∑ b, (L x b * Gplus) * X * (L x b * Gplus)ᴴ) ∧
    (∑ a, (G * Q a * Gplus)ᴴ * P * (G * Q a * Gplus) +
      ∑ x, ∑ b, (L x b * Gplus)ᴴ * (L x b * Gplus) = P) ∧
    (∀ X, Ntilde (G * X * G) = G * N X * G) ∧
    (∀ x X, Ctilde x (G * X * G) = C x X) ∧
    ∀ (rho : DensityState (Fin d)) (n : ℕ), 1 ≤ n →
      let rhoMatrix : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm rho.1
      let r := (rhoMatrix * R).trace.re
      0 < r → ∀ x,
        let original := C x ((N^[n - 1]) rhoMatrix)
        let conditioned := Ctilde x ((Ntilde^[n - 1])
          (((r : ℂ)⁻¹) • (G * rhoMatrix * G)))
        conditioned = ((r : ℂ)⁻¹) • original ∧
        conditioned.trace = original.trace / (r : ℂ) ∧
        (original.trace ≠ 0 → conditioned.trace ≠ 0 ∧
          (conditioned.trace)⁻¹ • conditioned = (original.trace)⁻¹ • original)



theorem actual_law : arena.Law actual := by
  intro d α ξ β _ _ _ Q L hcomp F hF
  simpa only [actual, realize, effectSignature] using
    eventual_click_doob_instrument Q L hcomp F hF

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let Q : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 0
  let L : Unit → Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 1
  have hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ x, ∑ b, (L x b)ᴴ * L x b = 1 := by
    simp [Q, L]
  have hF : Tendsto (survival Q) atTop
      (𝓝 (0 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    cases n with
    | zero => omega
    | succ n => simp [survival, noClickDual, Q]
  have hbad := (h Q L hcomp 0 hF).1
  have hentry := congrFun (congrFun hbad 0) 0
  norm_num [rejected, realize, effectSignature, noClickDual] at hentry

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

theorem dependence_proof : ObservationalDependence effectSignature actual := by
  intro i
  cases i
  refine ⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ),
    (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num [actual, realize, effectSignature] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.eventual_click_doob_instrument) (type_of% (realize.{0, 0, 0, 0, 0} effectSignature (fun _ _ F => F) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "EventualClickDoobInstrument") "eventual_click_doob_instrument") "Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument/Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} effectSignature (fun _ _ F => F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.EventualClickDoobInstrument, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.EventualClickDoobInstrument
