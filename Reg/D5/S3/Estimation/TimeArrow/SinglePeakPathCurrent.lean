import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
import Reg.Support.PathCurrentRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.PathCurrentRegistrationTemplates
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open LeanInformationAudit
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent

universe u

def actual : Realization signedPeakPathSignature.{u} :=
  realize signedPeakPathSignature.{u}
    (fun _ p x => Real.log
      (forwardLaw (kernel p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2 /
        reverseLaw (kernel p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2))
    (fun e => nomatch e)

def rejected : Realization signedPeakPathSignature.{u} :=
  realize signedPeakPathSignature.{u} (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signedPeakPathSignature.{u}
  Law R := ∀ {X : Type u} (χ : X → ℝ) (_hχ : ∀ x, χ x = 1 ∨ χ x = -1) (z : X) (_hz : χ z = 1)
    (r q N : ℝ) (_hr : |r| < 1) (_hq : |q| < 1) (_hN : 0 < N) (T : ℕ) (x : ℕ → X),
    R.readout () ⟨X, χ, z, r, q, N, T⟩ x =
      (Real.log ((1 + r) / (1 - q)) + Real.log (1 + q) - Real.log (1 - r)) *
          ((transitions (region χ z) x T Region.opposite Region.peak : ℝ) -
            (transitions (region χ z) x T Region.peak Region.opposite : ℝ)) +
        Real.log ((1 + r) / (1 - q)) * endpointDefect (region χ z) x T Region.peak -
          Real.log (1 + q) * endpointDefect (region χ z) x T Region.opposite



/-- The two-state sign space used for the rejected intervention and the dependence witness. -/
def sign (b : ULift.{u} Bool) : ℝ := if b.down then 1 else -1

def peakPath : ℕ → ULift.{u} Bool := fun t => if t = 0 then ⟨false⟩ else ⟨true⟩

def restPath : ℕ → ULift.{u} Bool := fun _ => ⟨true⟩

theorem sign_cases (b : ULift.{u} Bool) : sign b = 1 ∨ sign b = -1 := by
  cases b with | up b => cases b <;> simp [sign]

theorem sign_peak : sign (⟨true⟩ : ULift.{u} Bool) = 1 := by simp [sign]

theorem region_false :
    region sign (⟨true⟩ : ULift.{u} Bool) ⟨false⟩ = Region.opposite := by
  simp [region, sign]
  norm_num

theorem region_true : region sign (⟨true⟩ : ULift.{u} Bool) ⟨true⟩ = Region.peak := by
  simp [region]

/-- A single opposite-to-peak step carries log-likelihood `-log (1 - r) = log 2` at `r = 1/2`. -/
theorem peakPath_value :
    actual.{u}.readout () ⟨ULift.{u} Bool, sign, ⟨true⟩, 1 / 2, 0, 1, 1⟩ peakPath =
      Real.log 2 := by
  have h := log_forward_div_reverse_eq_current (sign : ULift.{u} Bool → ℝ) sign_cases ⟨true⟩
    sign_peak (1 / 2) 0 1 (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 peakPath
  have h0 : peakPath.{u} 0 = ⟨false⟩ := rfl
  have h1 : peakPath.{u} 1 = ⟨true⟩ := rfl
  have ht1 : transitions (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1 Region.opposite
      Region.peak = 1 := by
    simp [transitions, Finset.filter_singleton, h0, h1, region_false, region_true]
  have ht2 : transitions (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1 Region.peak
      Region.opposite = 0 := by
    simp [transitions, Finset.filter_singleton, h0, h1, region_false, region_true]
  have he1 : endpointDefect (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1 Region.peak =
      -1 := by
    simp [endpointDefect, h0, h1, region_false, region_true]
  have he2 : endpointDefect (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1
      Region.opposite = 1 := by
    simp [endpointDefect, h0, h1, region_false, region_true]
  change Real.log _ = _
  rw [h, ht1, ht2, he1, he2]
  have hhalf : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
  rw [hhalf, Real.log_inv]
  simp

theorem restPath_value :
    actual.{u}.readout () ⟨ULift.{u} Bool, sign, ⟨true⟩, 1 / 2, 0, 1, 1⟩ restPath =
      (0 : ℝ) := by
  have h := log_forward_div_reverse_eq_current (sign : ULift.{u} Bool → ℝ) sign_cases ⟨true⟩
    sign_peak (1 / 2) 0 1 (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 restPath
  have h0 : restPath.{u} 0 = ⟨true⟩ := rfl
  have h1 : restPath.{u} 1 = ⟨true⟩ := rfl
  change Real.log _ = _
  rw [h]
  simp [transitions, endpointDefect, Finset.filter_singleton, h0, h1, region_true]

theorem log_two_ne_zero' : Real.log 2 ≠ 0 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact this.ne'

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hlaw := h (X := ULift.{u} Bool) sign sign_cases ⟨true⟩ sign_peak (1 / 2) 0 1
    (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 peakPath
  have hact := log_forward_div_reverse_eq_current (sign : ULift.{u} Bool → ℝ) sign_cases ⟨true⟩
    sign_peak
    (1 / 2) 0 1 (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 peakPath
  have hv := peakPath_value.{u}
  change Real.log _ = _ at hv
  change (0 : ℝ) = _ at hlaw
  rw [← hact, hv] at hlaw
  exact log_two_ne_zero' hlaw.symm

theorem sensitivity_proof : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem dependence_proof :
    ObservationalDependence signedPeakPathSignature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} Bool, sign, ⟨true⟩, 1 / 2, 0, 1, 1⟩, peakPath, restPath, ?_⟩
  cases i
  rw [peakPath_value, restPath_value]
  exact log_two_ne_zero'

def registration : Registration arena.{u} (arena.{u}.Law actual.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun χ hχ z hz r q N hr hq hN T x =>
      log_forward_div_reverse_eq_current χ hχ z hz r q N hr hq hN T x,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, 0, 0} signedPeakPathSignature.{u_1}
    (fun _ p x => Real.log
      (forwardLaw.{u_1} (kernel.{u_1} p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2 /
        reverseLaw.{u_1} (kernel.{u_1} p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "SinglePeakPathCurrent") "log_forward_div_reverse_eq_current") "Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent/Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, 0, 0} signedPeakPathSignature.{u_1}
    (fun _ p x => Real.log
      (forwardLaw.{u_1} (kernel.{u_1} p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2 /
        reverseLaw.{u_1} (kernel.{u_1} p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, definition := none, coordinates := #[0, 1, 3, 5, 6, 7, 11], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 12, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.observationFact0, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent


noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
      Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena.{u_1}
      Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.actual.{u_1})
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration.{u_1})

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"log_forward_div_reverse_eq_current\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena.{u_1}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.actual.{u_1})
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration.{u_1})

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.observation0.{u_1} : {X : Type u_1} →
  (χ : X → Real) →
    (hχ :
        ∀ (x : X),
          Or (@Eq.{1} Real (χ x) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@Eq.{1} Real (χ x)
              (@Neg.neg.{0} Real Real.instNeg
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))) →
      (z : X) →
        (hz : @Eq.{1} Real (χ z) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          (r q N : Real) →
            (hr :
                @LT.lt.{0} Real Real.instLT (@abs.{0} Real Real.lattice Real.instAddGroup r)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
              (hq :
                  @LT.lt.{0} Real Real.instLT (@abs.{0} Real Real.lattice Real.instAddGroup q)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                (hN :
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) N) →
                  (T : Nat) →
                    (x : Nat → X) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, 0, 0}
                        D5.S3.ConceptDynamics.InformationEscape.PathCurrentRegistrationTemplates.signedPeakPathSignature.{u_1}
                        PUnit.unit.{1}
                        (@Sigma.mk.{u_1 + 1, u_1} (Type u_1)
                          (fun (X : Type u_1) =>
                            @Sigma.{u_1, u_1} (X → Real) fun (x : X → Real) =>
                              @Sigma.{u_1, 0} X fun (x : X) =>
                                @Sigma.{0, 0} Real fun (x : Real) =>
                                  @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat)
                          X
                          (@Sigma.mk.{u_1, u_1} (X → Real)
                            (fun (x : X → Real) =>
                              @Sigma.{u_1, 0} X fun (x : X) =>
                                @Sigma.{0, 0} Real fun (x : Real) =>
                                  @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat)
                            χ
                            (@Sigma.mk.{u_1, 0} X
                              (fun (x : X) =>
                                @Sigma.{0, 0} Real fun (x : Real) =>
                                  @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat)
                              z
                              (@Sigma.mk.{0, 0} Real
                                (fun (x : Real) =>
                                  @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat)
                                r
                                (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat) q
                                  (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) N T)))))) :=
  fun {X : Type u_1} (χ : X → Real)
    (hχ :
      ∀ (x : X),
        Or (@Eq.{1} Real (χ x) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Eq.{1} Real (χ x)
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
    (z : X) (hz : @Eq.{1} Real (χ z) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (r q N : Real)
    (hr :
      @LT.lt.{0} Real Real.instLT (@abs.{0} Real Real.lattice Real.instAddGroup r)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (hq :
      @LT.lt.{0} Real Real.instLT (@abs.{0} Real Real.lattice Real.instAddGroup q)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (hN : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) N)
    (T : Nat) (x : Nat → X) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.PathCurrentRegistrationTemplates.signedPeakPathSignature.{u_1}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1)
      (fun (X : Type u_1) =>
        @Sigma.{u_1, u_1} (X → Real) fun (x : X → Real) =>
          @Sigma.{u_1, 0} X fun (x : X) =>
            @Sigma.{0, 0} Real fun (x : Real) =>
              @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat)
      X
      (@Sigma.mk.{u_1, u_1} (X → Real)
        (fun (x : X → Real) =>
          @Sigma.{u_1, 0} X fun (x : X) =>
            @Sigma.{0, 0} Real fun (x : Real) =>
              @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat)
        χ
        (@Sigma.mk.{u_1, 0} X
          (fun (x : X) =>
            @Sigma.{0, 0} Real fun (x : Real) =>
              @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat)
          z
          (@Sigma.mk.{0, 0} Real
            (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat) r
            (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Nat) q
              (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) N T))))))
    x

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"log_forward_div_reverse_eq_current\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"log_forward_div_reverse_eq_current\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration.{u_1}).actual (Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration.{u_1}).variation.2.choose (Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration.{u_1}).variation.1 (Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakPathCurrent\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
