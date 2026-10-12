import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open LeanInformationAudit
open scoped MatrixOrder ComplexOrder

namespace Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation

universe u

abbrev signature : Signature where
  Params := Type u
  State p := CStarMatrix p p ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize.{u + 1, u, 0, u, 0} signature
    (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e)

noncomputable def negativeIdentity (p : Type u) : Matrix p p ℂ := by
  classical
  exact fun i j => if i = j then -1 else 0

noncomputable def rejected : Realization signature.{u} :=
  realize.{u + 1, u, 0, u, 0} signature
    (fun _ (p : Type u) _ => negativeIdentity p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (rho : DensityState n), (R.readout () n rho.1).PosSemidef

theorem actual_law : arena.{u}.Law actual := by
  intro n _ _ rho
  exact density_posSemidef rho

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  let rho : DensityState n :=
    ⟨1, by
      constructor
      · exact zero_le_one
      · change Matrix.trace (1 : Matrix n n ℂ) = 1
        rw [Matrix.trace_one]
        norm_num
    ⟩
  have hp := h rho
  have hq := hp.2 (Finsupp.single (ULift.up ()) (1 : ℂ))
  norm_num [rejected, negativeIdentity, realize,
    dotProduct, Matrix.mulVec, Finsupp.sum_single_index] at hq

theorem dependence_proof : ObservationalDependence signature.{u} actual := by
  intro i
  let n : signature.{u}.Params := ULift.{u} Unit
  refine ⟨n, 0, 1, ?_⟩
  intro h
  have he := congrArg (fun M : Matrix n n ℂ => M (ULift.up ()) (ULift.up ())) h
  change (0 : Matrix n n ℂ) (ULift.up ()) (ULift.up ()) =
    (1 : Matrix n n ℂ) (ULift.up ()) (ULift.up ()) at he
  simpa using he

noncomputable def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef.{u_1})
    (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1}
      (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "PartialTraceMutualInformation") "density_posSemidef") "Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation/Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u_1}⟩,
  objectArena := .source ⟨arena.{u_1}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨registration.{u_1}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1}
    (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.PartialTraceMutualInformation, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration_1

end Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation
