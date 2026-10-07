import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
open Finset LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
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
  realize signature (fun _ _ x => 2 * x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [Fintype X]
    (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1)
    (r q : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (M : ℕ) (hcard : Fintype.card X = 2 * M)
    (hplus : (univ.filter fun x => chi x = 1).card = M) (hM : 2 ≤ M)
    (hq : q = r / ((M : ℝ) - 1)),
    let P := kernel chi z r q (Fintype.card X)
    let k := (M : ℝ) - 1
    let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
    let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
    let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
    let Prev := Function.swap P
    let Lrev : (s : ℕ) → (Fin (s + 1) → X) → ℝ :=
      fun s x ↦ logLikelihoodSum chi z r q s (fun t ↦ x t.rev)
    (∀ u, |u| < 1 → psi u ≤ R.readout ⟨()⟩ () (phi u)) ∧
    J ≤ 0 ∧
    v ≤ 2 * I ∧
    0 ≤ I ∧
    (∀ s, pathVariance P s (logLikelihoodSum chi z r q s) ≤ 2 * s * I) ∧
    ∀ s, pathVariance Prev s (Lrev s) ≤ 2 * s * I

theorem actual_law : arena.Law actual := by
  exact uniform_single_peak_log_likelihood_variance_bound

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
  have impossible := hcase.1 0 (by norm_num)
  norm_num [rejected, realize, psi] at impossible

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (2 : ℝ) * 0 ≠ 2 * 1; norm_num⟩

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.uniform_single_peak_log_likelihood_variance_bound.{u_1}) (type_of% (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => 2 * x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "SinglePeakLogLikelihoodVarianceBound") "uniform_single_peak_log_likelihood_variance_bound") "Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound/Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => 2 * x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.uniform_single_peak_log_likelihood_variance_bound, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.observationFact0, `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.anchorEnumeration }


end Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound


noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, 0} (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.arena.) (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"uniform_single_peak_log_likelihood_variance_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.uniform_single_peak_log_likelihood_variance_bound, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.roleEnumeration.{u_1} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u_1, 0} Unit) where
  values := [@ULift.up.{u_1, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.observation0.{u_1} : {X : Type u_1} →
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
              (hr0 :
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
                (hr1 :
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
                            (u : Real) →
                              @LT.lt.{0} Real Real.instLT (@abs.{0} Real Real.lattice Real.instAddGroup u)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u_1, 0,
                                    0}
                                  Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.signature.{u_1}
                                  (@ULift.up.{u_1, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun {X : Type u_1} [inst : Fintype.{u_1} X] (chi : X → Real)
    (hchi :
      ∀ (x : X),
        Or (@Eq.{1} Real (chi x) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Eq.{1} Real (chi x)
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
    (z : X) (hz : @Eq.{1} Real (chi z) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (r q : Real)
    (hr0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
    (hr1 : @LT.lt.{0} Real Real.instLT r (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
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
  have Prev : (y x : X) → Real := @Function.swap.{u_1 + 1, u_1 + 1, 1} X X (fun (x y : X) => Real) P;
  have Lrev :
    (s : Nat) →
      (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          X) →
        Real :=
    fun (s : Nat)
      (x :
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          X) =>
    @D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.logLikelihoodSum.{u_1} X inst chi z r q s
      fun
        (t :
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      x
        (@Fin.rev
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          t);
  fun (u : Real)
    (a :
      @LT.lt.{0} Real Real.instLT (@abs.{0} Real Real.lattice Real.instAddGroup u)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u_1, 0, 0}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.signature.{u_1}
    Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.actual.{u_1} (@ULift.up.{u_1, 0} Unit Unit.unit)
    PUnit.unit.{1} (D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance.phi u)

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"uniform_single_peak_log_likelihood_variance_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"function\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.uniform_single_peak_log_likelihood_variance_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .letBody, .letBody, .function, .argument, .body, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"uniform_single_peak_log_likelihood_variance_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.uniform_single_peak_log_likelihood_variance_bound, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration.{u_1}).actual (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration.{u_1}).variation.2.choose (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration.{u_1}).variation.1 (Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"SinglePeakLogLikelihoodVarianceBound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound, declaration := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
