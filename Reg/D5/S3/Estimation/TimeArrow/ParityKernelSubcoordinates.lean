import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import Reg.Support.ParityKernelRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates
open _root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
open LeanInformationAudit
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates



/-! ### The coordinate-record law -/

def lawActual : Realization subcoordinateRecordSignature :=
  realize subcoordinateRecordSignature
    (fun _ p w => (subcoordinateLaw p.2.1 p.2.2.1 p.2.2.2 w : ℝ)) (fun e => nomatch e)

def lawRejected : Realization subcoordinateRecordSignature :=
  realize subcoordinateRecordSignature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def lawArena : Arena where
  signature := subcoordinateRecordSignature
  Law R := ∀ {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (S : Finset (Fin d)) (_hS : S ≠ Finset.univ) (T : ℕ)
    (w : Fin (T + 1) → Fin d → ℤˣ),
    R.readout () ⟨d, a, S, T⟩ w = ((1 / 2 ^ S.card : ℝ)) ^ (T + 1)

/-- With every coordinate observed, the record law is the full path law of the recorded path. -/
theorem subcoordinateLaw_univ {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (T : ℕ)
    (w : Fin (T + 1) → Fin d → ℤˣ) :
    subcoordinateLaw a Finset.univ T w =
      (1 / 2 ^ d : ℝ) * ∏ t : Fin T, parityKernel a (w t.castSucc) (w t.succ) := by
  unfold subcoordinateLaw
  rw [Finset.sum_eq_single w]
  · simp
  · intro x _ hx
    obtain ⟨t, ht⟩ : ∃ t, x t ≠ w t := by
      by_contra h
      exact hx (funext fun t => by_contra fun ht => h ⟨t, ht⟩)
    have hzero : (if ∀ j ∈ (Finset.univ : Finset (Fin d)), x t j = w t j then (1 : ℝ) else 0) = 0 :=
      if_neg fun h => ht (funext fun j => h j (Finset.mem_univ j))
    rw [Finset.prod_eq_zero (Finset.mem_univ t) hzero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

def onePath : Fin 2 → Fin 1 → ℤˣ := fun _ _ => 1

def flipPath : Fin 2 → Fin 1 → ℤˣ := fun t _ => if t = 0 then 1 else -1

theorem parity_one : parity (fun _ : Fin 1 => (1 : ℤˣ)) = 1 := by simp [parity]

theorem parity_neg_one : parity (fun _ : Fin 1 => (-1 : ℤˣ)) = -1 := by simp [parity]

theorem lawActual_onePath :
    lawActual.readout () ⟨1, fun _ => 1 / 2, Finset.univ, 1⟩ onePath = (3 / 8 : ℝ) := by
  show subcoordinateLaw (d := 1) (fun _ => (1 / 2 : ℝ)) Finset.univ 1 onePath = (3 / 8 : ℝ)
  rw [subcoordinateLaw_univ]
  have h1 : onePath (Fin.succ 0) = fun _ => 1 := rfl
  simp only [parityKernel, Fin.prod_univ_one, h1, parity_one]
  norm_num

theorem lawActual_flipPath :
    lawActual.readout () ⟨1, fun _ => 1 / 2, Finset.univ, 1⟩ flipPath = (1 / 8 : ℝ) := by
  show subcoordinateLaw (d := 1) (fun _ => (1 / 2 : ℝ)) Finset.univ 1 flipPath = (1 / 8 : ℝ)
  rw [subcoordinateLaw_univ]
  have h0 : flipPath (Fin.castSucc 0) = fun _ => 1 := by funext j; simp [flipPath]
  have h1 : flipPath (Fin.succ 0) = fun _ => -1 := by funext j; simp [flipPath]
  simp only [Fin.prod_univ_one, parityKernel, h0, h1, parity_neg_one]
  norm_num

theorem lawRejected_law : ¬ lawArena.Law lawRejected := by
  intro h
  have hs : (∅ : Finset (Fin 1)) ≠ Finset.univ := by
    intro he
    have : (0 : Fin 1) ∈ (∅ : Finset (Fin 1)) := he ▸ Finset.mem_univ _
    simp at this
  have := h (d := 1) (fun _ => 0) ∅ hs 0 (fun _ _ => 1)
  change (0 : ℝ) = _ at this
  norm_num at this

theorem law_sensitivity : Sensitivity lawArena lawActual := by
  constructor
  · intro i
    refine ⟨lawRejected, ?_, rfl, lawRejected_law⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem law_dependence : ObservationalDependence subcoordinateRecordSignature lawActual := by
  intro i
  refine ⟨⟨1, fun _ => 1 / 2, Finset.univ, 1⟩, onePath, flipPath, ?_⟩
  cases i
  rw [lawActual_onePath, lawActual_flipPath]
  intro h
  have h' : (3 / 8 : ℝ) = 1 / 8 := h
  norm_num at h'

def lawRegistration : Registration lawArena (lawArena.Law lawActual) where
  actual := lawActual
  bridge := Iff.rfl
  variation := ⟨fun a S hS T w => subcoordinateLaw_eq a S hS T w, lawRejected, lawRejected_law⟩
  sensitivity := law_sensitivity
  dependence := law_dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq) (type_of% (realize.{0, 0, 0, 0, 0} subcoordinateRecordSignature
    (fun _ p w => (subcoordinateLaw p.2.1 p.2.2.1 p.2.2.2 w : ℝ)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "ParityKernelSubcoordinates") "subcoordinateLaw_eq") "Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates/Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(lawArena)⟩,
  objectArena := .source ⟨(lawArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (lawArena) ⟨(lawRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} subcoordinateRecordSignature
    (fun _ p w => (subcoordinateLaw p.2.1 p.2.2.1 p.2.2.2 w : ℝ)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, definition := none, coordinates := #[0, 1, 2, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.observationFact0, `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.anchorEnumeration }


#print axioms lawRejected_law
#print axioms law_sensitivity
#print axioms law_dependence


end Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates


noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawArena) (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration).actual

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"subcoordinateLaw_eq\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration).bridge

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.observation0 : {d : Nat} →
  (a : (Fin d → @Units.{0} Int Int.instMonoid) → Real) →
    (S : Finset.{0} (Fin d)) →
      (hS : @Ne.{1} (Finset.{0} (Fin d)) S (@Finset.univ.{0} (Fin d) (Fin.fintype d))) →
        (T : Nat) →
          (w :
              Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) T
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Fin d → @Units.{0} Int Int.instMonoid) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.subcoordinateRecordSignature
              PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat
                (fun (d : Nat) =>
                  @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                    fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                    @Sigma.{0, 0} (Finset.{0} (Fin d)) fun (x : Finset.{0} (Fin d)) => Nat)
                d
                (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                  (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                    @Sigma.{0, 0} (Finset.{0} (Fin d)) fun (x : Finset.{0} (Fin d)) => Nat)
                  a (@Sigma.mk.{0, 0} (Finset.{0} (Fin d)) (fun (x : Finset.{0} (Fin d)) => Nat) S T))) :=
  fun {d : Nat} (a : (Fin d → @Units.{0} Int Int.instMonoid) → Real) (S : Finset.{0} (Fin d))
    (hS : @Ne.{1} (Finset.{0} (Fin d)) S (@Finset.univ.{0} (Fin d) (Fin.fintype d))) (T : Nat)
    (w :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) T
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Fin d → @Units.{0} Int Int.instMonoid) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.subcoordinateRecordSignature
    Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (d : Nat) =>
        @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
          fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
          @Sigma.{0, 0} (Finset.{0} (Fin d)) fun (x : Finset.{0} (Fin d)) => Nat)
      d
      (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
        (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
          @Sigma.{0, 0} (Finset.{0} (Fin d)) fun (x : Finset.{0} (Fin d)) => Nat)
        a (@Sigma.mk.{0, 0} (Finset.{0} (Fin d)) (fun (x : Finset.{0} (Fin d)) => Nat) S T)))
    w

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"subcoordinateLaw_eq\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"subcoordinateLaw_eq\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration).actual (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration).variation.2.choose (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration).variation.1 (Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityKernelSubcoordinates\",\"lawRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.lawRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
