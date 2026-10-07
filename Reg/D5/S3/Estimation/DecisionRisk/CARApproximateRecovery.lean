import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u

namespace Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
open _root_.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => min 1 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

open scoped BigOperators ENNReal
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open _root_.D5.S3.TotalVariation.Pinsker _root_.D5.S3.TotalVariation.Metric

def arena : Arena where
  signature := signature.{u}
  Law observation := ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (w v : Block A → ℝ) (hw : ∀ B, 0 ≤ w B) (hv : ∀ C, 0 ≤ v C)
    (hwrow : ∀ i, ∑ B, row w i B = 1) (hvrow : ∀ i, ∑ C, row v i C = 1)
    (H : FiniteMarkovKernel (Block A) (Block A)),
    let ε := fun i => totalVariation (channelOutput H.1 (row w i)) (row v i)
    let Δ := fun i j => pair v i j - pair w i j
    let b := fun i => (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i, (Δ i j + ε i + ε j)
    let εmax := Finset.univ.sup' Finset.univ_nonempty ε
    let η := Finset.univ.sup' Finset.univ_nonempty
      (fun ij : A × A => if ij.1 = ij.2 then (0 : ℝ) else |Δ ij.1 ij.2|)
    let bmax := Finset.univ.sup' Finset.univ_nonempty b
    ∃ R : FiniteMarkovKernel (Block A) (Block A),
      (∀ i j, 0 ≤ Δ i j + ε i + ε j) ∧
      (∀ i, totalVariation (channelOutput R.1 (row v i)) (row w i) ≤ b i) ∧
      finiteDeficiency (row w) (row v) ≤ ENNReal.ofReal (min 1 bmax) ∧
      min 1 bmax ≤ observation.readout ⟨()⟩ () (((Fintype.card A : ℝ) - 1) * η / 2 +
        ((Fintype.card A : ℝ) - 1) * εmax) ∧
      ((∀ i, ε i = 0) → ∀ B C, 0 < v C →
        R.1 C B = if B.1 ⊆ C.1 then
          (B.1.card : ℝ) * (w B * H.1 B C) / ((C.1.card : ℝ) * v C) else 0)

theorem actual_law : arena.{u}.Law actual := by
  intro A _ _ _ w v hw hv hwrow hvrow H
  exact _root_.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result
    w v hw hv hwrow hvrow H

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} Unit
  have hmem (i : A) (B : Block A) : i ∈ B.1 := by
    obtain ⟨j, hj⟩ := B.2
    simpa only [Subsingleton.elim j i] using hj
  letI : Unique (Block A) := {
    default := ⟨Finset.univ, Finset.univ_nonempty⟩
    uniq := fun B => Subtype.ext (Finset.eq_univ_of_forall (fun i => hmem i B)) }
  let w : Block A → ℝ := fun _ => 1
  have hw : ∀ B, 0 ≤ w B := fun _ => zero_le_one
  have hr : ∀ i, ∑ B, row w i B = 1 := by
    intro i
    simp [row, w, hmem]
  let H : FiniteMarkovKernel (Block A) (Block A) :=
    ⟨fun B C => if B = C then 1 else 0, by
      constructor
      · intro B C; exact ite_nonneg zero_le_one le_rfl
      · intro B
        change (∑ C : Block A, if B = C then (1 : ℝ) else 0) = 1
        simp only [Finset.univ_unique, Finset.sum_singleton, if_pos (Subsingleton.elim B default)]⟩
  obtain ⟨R, _, _, _, hb, _⟩ := h w w hw hw hr hr H
  have herase (i : A) : Finset.univ.erase i = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  simp only [herase, Finset.sum_empty, mul_zero] at hb
  norm_num [rejected, realize] at hb

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

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result.{u_1}) (type_of% (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => min.{0} 1 x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DecisionRisk") "CARApproximateRecovery") "result") "Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery/Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u_1, 0, 0} signature.{u_1} (fun _ _ x => min.{0} 1 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.observationFact0, `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.anchorEnumeration }


end Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u_1, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena.{u_1}
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, u_1, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, 0}
      Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena.{u_1}
      Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.actual.{u_1})
    Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration.{u_1})

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, u_1, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u_1, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.arena.{u_1}
    Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.actual.{u_1})
  Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration.{u_1})

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.roleEnumeration.{u_1} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u_1, 0} Unit) where
  values := [@ULift.up.{u_1, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.observation0.{u_1} : {A : Type u_1} →
  [inst : Fintype.{u_1} A] →
    [inst_1 : DecidableEq.{u_1 + 1} A] →
      [Nonempty.{u_1 + 1} A] →
        (w v : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A → Real) →
          (hw :
              ∀ (B : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A),
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (w B)) →
            (hv :
                ∀ (C : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A),
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v C)) →
              (hwrow :
                  ∀ (i : A),
                    @Eq.{1} Real
                      (@Finset.sum.{u_1, 0} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) Real
                        Real.instAddCommMonoid
                        (@Finset.univ.{u_1} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
                          (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A)
                            (@Finset.decidableNonempty.{u_1} A) (@Finset.fintype.{u_1} A inst)))
                        fun (B : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) =>
                        @D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.row.{u_1} A inst_1 w i B)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                (hvrow :
                    ∀ (i : A),
                      @Eq.{1} Real
                        (@Finset.sum.{u_1, 0} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) Real
                          Real.instAddCommMonoid
                          (@Finset.univ.{u_1} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
                            (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A)
                              (@Finset.decidableNonempty.{u_1} A) (@Finset.fintype.{u_1} A inst)))
                          fun (C : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) =>
                          @D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.row.{u_1} A inst_1 v i C)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  (H R :
                      @D5.S3.Estimation.DecisionRisk.DescentDefectBounds.FiniteMarkovKernel.{u_1, u_1}
                        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
                        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
                        (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A)
                          (@Finset.decidableNonempty.{u_1} A) (@Finset.fintype.{u_1} A inst))) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u_1, 0, 0}
                      Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.signature.{u_1}
                      (@ULift.up.{u_1, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun {A : Type u_1} [inst : Fintype.{u_1} A] [inst_1 : DecidableEq.{u_1 + 1} A] [inst_2 : Nonempty.{u_1 + 1} A]
    (w v : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A → Real)
    (hw :
      ∀ (B : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w B))
    (hv :
      ∀ (C : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (v C))
    (hwrow :
      ∀ (i : A),
        @Eq.{1} Real
          (@Finset.sum.{u_1, 0} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) Real
            Real.instAddCommMonoid
            (@Finset.univ.{u_1} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
              (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A) (@Finset.decidableNonempty.{u_1} A)
                (@Finset.fintype.{u_1} A inst)))
            fun (B : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) =>
            @D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.row.{u_1} A inst_1 w i B)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (hvrow :
      ∀ (i : A),
        @Eq.{1} Real
          (@Finset.sum.{u_1, 0} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) Real
            Real.instAddCommMonoid
            (@Finset.univ.{u_1} (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
              (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A) (@Finset.decidableNonempty.{u_1} A)
                (@Finset.fintype.{u_1} A inst)))
            fun (C : D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A) =>
            @D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.row.{u_1} A inst_1 v i C)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (H :
      @D5.S3.Estimation.DecisionRisk.DescentDefectBounds.FiniteMarkovKernel.{u_1, u_1}
        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
        (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A) (@Finset.decidableNonempty.{u_1} A)
          (@Finset.fintype.{u_1} A inst))) =>
  have ε : (i : A) → Real := fun (i : A) =>
    @D5.S3.TotalVariation.Pinsker.totalVariation.{u_1}
      (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
      (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A) (@Finset.decidableNonempty.{u_1} A)
        (@Finset.fintype.{u_1} A inst))
      (@D5.S3.Divergence.ClassicalDPI.channelOutput.{u_1, u_1}
        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
        (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A) (@Finset.decidableNonempty.{u_1} A)
          (@Finset.fintype.{u_1} A inst))
        (@Subtype.val.{u_1 + 1}
          (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A →
            D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A → Real)
          (fun
              (K :
                D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A →
                  D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A → Real) =>
            @D5.S3.Estimation.DecisionRisk.DescentDefectBounds.IsRowStochastic.{u_1, u_1}
              (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
              (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
              (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A) (@Finset.decidableNonempty.{u_1} A)
                (@Finset.fintype.{u_1} A inst))
              K)
          H)
        (@D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.row.{u_1} A inst_1 w i))
      (@D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.row.{u_1} A inst_1 v i);
  have Δ : (i j : A) → Real := fun (i j : A) =>
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.pair.{u_1} A inst_1 inst v i j)
      (@D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.pair.{u_1} A inst_1 inst w i j);
  have b : (i : A) → Real := fun (i : A) =>
    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@Finset.sum.{u_1, 0} A Real Real.instAddCommMonoid (@Finset.erase.{u_1} A inst_1 (@Finset.univ.{u_1} A inst) i)
        fun (j : A) =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (Δ i j) (ε i)) (ε j));
  have εmax : Real :=
    @Finset.sup'.{0, u_1} Real A Real.instSemilatticeSup (@Finset.univ.{u_1} A inst)
      (@Finset.univ_nonempty.{u_1} A inst inst_2) ε;
  have η : Real :=
    @Finset.sup'.{0, u_1} Real (Prod.{u_1, u_1} A A) Real.instSemilatticeSup
      (@Finset.univ.{u_1} (Prod.{u_1, u_1} A A) (@instFintypeProd.{u_1, u_1} A A inst inst))
      (@Finset.univ_nonempty.{u_1} (Prod.{u_1, u_1} A A) (@instFintypeProd.{u_1, u_1} A A inst inst)
        (@instNonemptyProd.{u_1, u_1} A A inst_2 inst_2))
      fun (ij : Prod.{u_1, u_1} A A) =>
      @ite.{1} Real (@Eq.{u_1 + 1} A (@Prod.fst.{u_1, u_1} A A ij) (@Prod.snd.{u_1, u_1} A A ij))
        (inst_1 (@Prod.fst.{u_1, u_1} A A ij) (@Prod.snd.{u_1, u_1} A A ij))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@abs.{0} Real Real.lattice Real.instAddGroup (Δ (@Prod.fst.{u_1, u_1} A A ij) (@Prod.snd.{u_1, u_1} A A ij)));
  have bmax : Real :=
    @Finset.sup'.{0, u_1} Real A Real.instSemilatticeSup (@Finset.univ.{u_1} A inst)
      (@Finset.univ_nonempty.{u_1} A inst inst_2) b;
  fun
    (R :
      @D5.S3.Estimation.DecisionRisk.DescentDefectBounds.FiniteMarkovKernel.{u_1, u_1}
        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
        (D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.Block.{u_1} A)
        (@Subtype.fintype.{u_1} (Finset.{u_1} A) (@Finset.Nonempty.{u_1} A) (@Finset.decidableNonempty.{u_1} A)
          (@Finset.fintype.{u_1} A inst))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u_1, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.signature.{u_1}
    Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.actual.{u_1} (@ULift.up.{u_1, 0} Unit Unit.unit)
    PUnit.unit.{1}
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} A inst))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          η)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} A inst))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        εmax))

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .letBody, .argument, .body, .argument, .argument, .argument, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration.{u_1}).actual (Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration.{u_1}).variation.2.choose (Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration.{u_1}).variation.1 (Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"CARApproximateRecovery\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery, declaration := `Reg.D5.S3.Estimation.DecisionRisk.CARApproximateRecovery.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
