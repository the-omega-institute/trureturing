import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open Finset LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
universe u

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := ⟨{⟨()⟩}, fun x => by
    have hx : x = ⟨()⟩ := Subsingleton.elim _ _
    simp only [hx, Finset.mem_singleton]⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => phi x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [Fintype X]
    (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1)
    (r q : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (M : ℕ) (hcard : Fintype.card X = 2 * M)
    (hplus : (univ.filter fun x => chi x = 1).card = M) (hM : 2 ≤ M)
    (hq : q = r / ((M : ℝ) - 1)),
    let P := kernel chi z r q (Fintype.card X)
    let L := fun x y => Real.log ((Fintype.card X : ℝ) * P x y)
    let k := (M : ℝ) - 1
    let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
    let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
    let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
    (∀ x, ∑ y, P x y * L x y = R.readout ⟨()⟩ () (profile chi z r q x)) ∧
    (∀ y, ∑ x, P x y * L x y = I + J * chi y) ∧
    (∀ n, pathExpectation P (n + 1)
      (fun x => logIncrement chi z r q (Fin.last n) x) = I) ∧
    pathCovariance P 2 (fun x => logIncrement chi z r q 0 x)
      (fun x => logIncrement chi z r q 1 x) = I * J ∧
    (∀ j, 2 ≤ j → pathCovariance P (j + 1) (fun x => logIncrement chi z r q 0 x)
      (fun x => logIncrement chi z r q (Fin.last j) x) = 0) ∧
    ∀ s, 1 ≤ s → pathVariance P s (logLikelihoodSum chi z r q s) =
      (s : ℝ) * v + 2 * ((s - 1 : ℕ) : ℝ) * I * J

theorem actual_law : arena.Law actual := by
  exact exact_single_peak_log_likelihood_covariances

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let chi : ULift.{u} (Fin 4) → ℝ := fun x => if x.down.val < 2 then 1 else -1
  have hchi : ∀ x, chi x = 1 ∨ chi x = -1 := by
    intro x
    dsimp [chi]
    split_ifs <;> simp
  have hplus : (univ.filter fun x => chi x = 1).card = 2 := by
    rw [Finset.card_filter]
    rw [← (Equiv.ulift.symm : Fin 4 ≃ ULift.{u} (Fin 4)).sum_comp]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    norm_num [chi]
  have hcase := h chi hchi ⟨0⟩ (by norm_num [chi]) (1/2) (1/2)
    (by norm_num) (by norm_num) 2 (by simp) hplus (by omega) (by norm_num)
  have impossible := hcase.1 (⟨2⟩ : ULift.{u} (Fin 4))
  have hne : (⟨2⟩ : ULift.{u} (Fin 4)) ≠ ⟨0⟩ := by
    intro he
    have hv := congrArg (fun x : ULift.{u} (Fin 4) => x.down.val) he
    norm_num at hv
  have hprofile : profile chi ⟨0⟩ (1/2) (1/2) (⟨2⟩ : ULift.{u} (Fin 4)) = 0 := by
    norm_num [profile, region, chi, hne]
  norm_num [rejected, realize, kernel, hprofile] at impossible

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change phi 0 ≠ phi 1
    intro he
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    norm_num [phi] at he
    linarith

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.exact_single_peak_log_likelihood_covariances.{u_1}) (type_of% (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => phi x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "SinglePeakLogLikelihoodCovariance") "exact_single_peak_log_likelihood_covariances") "Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance/Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => phi x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.exact_single_peak_log_likelihood_covariances, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.observationFact0, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance


noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, 0} (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.arena.) (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"exact_single_peak_log_likelihood_covariances\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.exact_single_peak_log_likelihood_covariances, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.roleEnumeration.{u_1} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u_1, 0} Unit) where
  values := [@ULift.up.{u_1, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.observation0.{u_1} : {X : Type u_1} →
  [inst : Fintype.{u_1} X] →
    (chi : X → Real) →
      (hchi :
          ∀ (x : X),
            Or (@Eq.{1} Real (chi x) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (@Eq.{1} Real (chi x)
                (@Neg.neg.{0} Real Real.instNeg
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))) →
        (z : X) →
          (hz : @Eq.{1} Real (chi z) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (r q : Real) →
              (_hr0 :
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
                (_hr1 :
                    @LT.lt.{0} Real Real.instLT r
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  (M : Nat) →
                    (hcard :
                        @Eq.{1} Nat (@Fintype.card.{u_1} X inst)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) M)) →
                      (hplus :
                          @Eq.{1} Nat
                            (@Finset.card.{u_1} X
                              (@Finset.filter.{u_1} X
                                (fun (x : X) =>
                                  @Eq.{1} Real (chi x)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                (fun (a : X) =>
                                  Real.decidableEq (chi a)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                (@Finset.univ.{u_1} X inst)))
                            M) →
                        (hM :
                            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) M) →
                          (hq :
                              @Eq.{1} Real q
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) r
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (@Nat.cast.{0} Real Real.instNatCast M)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))) →
                            (x : X) →
                              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u_1, 0, 0}
                                Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.signature.{u_1}
                                (@ULift.up.{u_1, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun {X : Type u_1} [inst : Fintype.{u_1} X] (chi : X → Real)
    (hchi :
      ∀ (x : X),
        Or (@Eq.{1} Real (chi x) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Eq.{1} Real (chi x)
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
    (z : X) (hz : @Eq.{1} Real (chi z) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (r q : Real)
    (_hr0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
    (_hr1 : @LT.lt.{0} Real Real.instLT r (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (M : Nat)
    (hcard :
      @Eq.{1} Nat (@Fintype.card.{u_1} X inst)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) M))
    (hplus :
      @Eq.{1} Nat
        (@Finset.card.{u_1} X
          (@Finset.filter.{u_1} X
            (fun (x : X) =>
              @Eq.{1} Real (chi x) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (fun (a : X) =>
              Real.decidableEq (chi a) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@Finset.univ.{u_1} X inst)))
        M)
    (hM : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) M)
    (hq :
      @Eq.{1} Real q
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) r
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@Nat.cast.{0} Real Real.instNatCast M)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))) =>
  have P : (x y : X) → Real :=
    @D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.kernel.{u_1} X chi z r q
      (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} X inst));
  have L : (x y : X) → Real := fun (x y : X) =>
    Real.log
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} X inst)) (P x y));
  have k : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@Nat.cast.{0} Real Real.instNatCast M)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne));
  have I : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.phi r)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) k
          (D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.phi q)))
      (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} X inst));
  have J : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.xi r)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) k
          (D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.xi q)))
      (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} X inst));
  have v : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.psi r)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) k
            (D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.psi q)))
        (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} X inst)))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) I
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))));
  fun (x : X) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u_1, 0, 0}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.signature.{u_1}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.actual.{u_1} (@ULift.up.{u_1, 0} Unit Unit.unit)
    PUnit.unit.{1} (@D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.profile.{u_1} X chi z r q x)

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"exact_single_peak_log_likelihood_covariances\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"function\",\"argument\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.exact_single_peak_log_likelihood_covariances, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .letBody, .function, .argument, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"exact_single_peak_log_likelihood_covariances\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.exact_single_peak_log_likelihood_covariances, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration.{u_1}).actual (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration.{u_1}).variation.2.choose (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration.{u_1}).variation.1 (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodCovariance\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
