import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal BigOperators
noncomputable section
universe u

namespace Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
open _root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => ENNReal.ofReal x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (1 : ℝ≥0∞)) (fun e => nomatch e)

open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open _root_.D5.S3.TotalVariation.Pinsker _root_.D5.S3.TotalVariation.Metric

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (U : Finset A) (hm : 3 ≤ U.card) (a : ℝ) (ha : 0 ≤ a)
    (w : Block A → ℝ) (hw : ∀ B, 0 ≤ w B)
    (hrow : ∀ i, ∑ B, experiment w i B = 1)
    (hcap : ∀ B : Block A, B.1 ⊆ U → B.1.card = 2 → a ≤ w B),
    let v := plus w U a
    let ep := a * ((U.card : ℝ) - 2) / (U.card : ℝ)
    let em := a * ((U.card : ℝ) - 2) / 2
    (∀ B, 0 ≤ v B) ∧
    (∀ i, ∑ B, experiment v i B = 1) ∧
    (∀ i j : A, i ≠ j →
      (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then v B else 0) =
      (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then w B else 0)) ∧
    finiteDeficiency (experiment w) (experiment v) = R.readout ⟨()⟩ () ep ∧
    finiteDeficiency (experiment v) (experiment w) = ENNReal.ofReal em ∧
    ∃ KP KM : FiniteMarkovKernel (Block A) (Block A),
      (∀ i, totalVariation (experiment w i) (channelOutput KP.1 (experiment v i)) =
        if i ∈ U then ep else 0) ∧
      (∀ i, totalVariation (experiment v i) (channelOutput KM.1 (experiment w i)) =
        if i ∈ U then em else 0) ∧
      (∀ K : FiniteMarkovKernel (Block A) (Block A),
        ep ≤ uniformSimulationError (experiment w) (experiment v) K) ∧
      (∀ K : FiniteMarkovKernel (Block A) (Block A),
        em ≤ uniformSimulationError (experiment v) (experiment w) K)

theorem actual_law : arena.{u}.Law actual := by
  intro A _ _ _ U hm a ha w hw hrow hcap
  exact _root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result
    U hm a ha w hw hrow hcap

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} (Fin 3)
  let U : Finset A := Finset.univ
  let w : Block A → ℝ := fun B => if B.1 = Finset.univ then 1 else 0
  have hm : 3 ≤ U.card := by simp [U, A]
  have hw : ∀ B, 0 ≤ w B := by intro B; dsimp [w]; split_ifs <;> norm_num
  let full : Block A := ⟨Finset.univ, Finset.univ_nonempty⟩
  have hr : ∀ i, ∑ B, experiment w i B = 1 := by
    intro i
    rw [Finset.sum_eq_single full]
    · simp [experiment, w, full]
    · intro B _ hne
      have hn : B.1 ≠ Finset.univ := fun hh => hne (Subtype.ext hh)
      simp [experiment, w, hn]
    · intro hfull
      exact (hfull (Finset.mem_univ full)).elim
  have hc : ∀ B : Block A, B.1 ⊆ U → B.1.card = 2 → (0 : ℝ) ≤ w B :=
    fun B _ _ => hw B
  have hb := (h U hm 0 le_rfl w hw hr hc).2.2.2.1
  have hg := (_root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result
    U hm 0 le_rfl w hw hr hc).2.2.2.1
  have hh := hg.symm.trans hb
  norm_num [rejected, realize] at hh

theorem dependence_proof : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j h
    exact (h (@Subsingleton.elim (ULift.{u} Unit) _ j i)).elim
  · intro i
    exact nomatch i

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result.{u_1}) (type_of% (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => ENNReal.ofReal x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DecisionRisk") "LocalCARDeficiency") "result") "Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency/Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => ENNReal.ofReal x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.observationFact0, `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.anchorEnumeration }


end Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, 0} (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.arena.) (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.roleEnumeration.{u_1} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u_1, 0} Unit) where
  values := [@ULift.up.{u_1, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.observation0.{u_1} : {A : Type u_1} →
  [inst : Fintype.{u_1} A] →
    [inst_1 : DecidableEq.{u_1 + 1} A] →
      [Nonempty.{u_1 + 1} A] →
        (U : Finset.{u_1} A) →
          (hm :
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Finset.card.{u_1} A U)) →
            (a : Real) →
              (ha :
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a) →
                (w : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A → Real) →
                  (hw :
                      ∀ (B : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A),
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w B)) →
                    (hrow :
                        ∀ (i : A),
                          @Eq.{1} Real
                            (@Finset.sum.{u_1, 0} (D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A) Real
                              Real.instAddCommMonoid
                              (@Finset.univ.{u_1} (D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A)
                                (@D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.blockFintype.{u_1} A inst))
                              fun (B : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A) =>
                              @D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.experiment.{u_1} A inst_1 w i B)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                      (hcap :
                          ∀ (B : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A),
                            @LE.le.{u_1} (Finset.{u_1} A)
                                (@Preorder.toLE.{u_1} (Finset.{u_1} A)
                                  (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} A) (@Finset.instPartialOrder.{u_1} A)))
                                (@Subtype.val.{u_1 + 1} (Finset.{u_1} A)
                                  (fun (B : Finset.{u_1} A) => @Finset.Nonempty.{u_1} A B) B)
                                U →
                              @Eq.{1} Nat
                                  (@Finset.card.{u_1} A
                                    (@Subtype.val.{u_1 + 1} (Finset.{u_1} A)
                                      (fun (B : Finset.{u_1} A) => @Finset.Nonempty.{u_1} A B) B))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                @LE.le.{0} Real Real.instLE a (w B)) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u_1, 0, 0}
                          Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.signature.{u_1}
                          (@ULift.up.{u_1, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun {A : Type u_1} [Fintype.{u_1} A] [inst_1 : DecidableEq.{u_1 + 1} A] [Nonempty.{u_1 + 1} A] (U : Finset.{u_1} A)
    (hm :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Finset.card.{u_1} A U))
    (a : Real)
    (ha : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
    (w : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A → Real)
    (hw :
      ∀ (B : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w B))
    (hrow :
      ∀ (i : A),
        @Eq.{1} Real
          (@Finset.sum.{u_1, 0} (D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A) Real
            Real.instAddCommMonoid
            (@Finset.univ.{u_1} (D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A)
              (@D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.blockFintype.{u_1} A inst))
            fun (B : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A) =>
            @D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.experiment.{u_1} A inst_1 w i B)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (hcap :
      ∀ (B : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A),
        @LE.le.{u_1} (Finset.{u_1} A)
            (@Preorder.toLE.{u_1} (Finset.{u_1} A)
              (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} A) (@Finset.instPartialOrder.{u_1} A)))
            (@Subtype.val.{u_1 + 1} (Finset.{u_1} A) (fun (B : Finset.{u_1} A) => @Finset.Nonempty.{u_1} A B) B) U →
          @Eq.{1} Nat
              (@Finset.card.{u_1} A
                (@Subtype.val.{u_1 + 1} (Finset.{u_1} A) (fun (B : Finset.{u_1} A) => @Finset.Nonempty.{u_1} A B) B))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            @LE.le.{0} Real Real.instLE a (w B)) =>
  have v : D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.Block.{u_1} A → Real :=
    @D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.plus.{u_1} A inst_1 w U a;
  have ep : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_1} A U))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_1} A U));
  have em : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_1} A U))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))));
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u_1, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.signature.{u_1}
    Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.actual.{u_1} (@ULift.up.{u_1, 0} Unit Unit.unit) PUnit.unit.{1}
    ep

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .argument, .argument, .argument, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration.{u_1}).actual (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration.{u_1}).variation.2.choose (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration.{u_1}).variation.1 (Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"LocalCARDeficiency\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.LocalCARDeficiency.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
