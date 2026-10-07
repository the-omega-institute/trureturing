import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open MeasureTheory ProbabilityTheory Matrix LeanInformationAudit
open scoped CStarAlgebra MatrixOrder ComplexOrder ComplexConjugate ENNReal BigOperators Kronecker

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.seminormedAddCommGroup
local instance (I : Type*) : MeasurableSpace (Matrix I I ℂ) :=
  inferInstanceAs (MeasurableSpace (I → I → ℂ))
local instance (I : Type*) [Fintype I] : ContinuousENorm (Matrix I I ℂ) :=
  inferInstanceAs (ContinuousENorm (I → I → ℂ))

namespace Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ β => β) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law W := ∀ {A : Type} [Fintype A] [DecidableEq A]
    (e : ℕ) (he : 2 ≤ e) (β : ℝ) (hβ : 0 < β)
    (N : ℕ) (F : Fin (N+1) → Type u) [∀ i, MeasurableSpace (F i)]
    (D : Type u) [MeasurableSpace D] (P : FiniteStoppedPolicy N F D A)
    (H_A : Matrix A A ℂ) (hH_A : H_A.IsHermitian)
    (h₀ : F (historyIndex N 0)) (ρ₀ : Matrix A A ℂ) (hρ₀ : ρ₀.PosSemidef)
    (hρ₀trace : Matrix.trace ρ₀ = 1)
    (G : DensityState (Fin e) → ∀ i, ActualHistory (F i) (A × Fin e))
    (hinit : ∀ σ, (G σ (historyIndex N 0)).law = Measure.dirac h₀)
    (hproduct : ∀ σ, (G σ (historyIndex N 0)).density =ᵐ[(G σ (historyIndex N 0)).law]
      (fun _ => ρ₀ ⊗ₖ CStarMatrix.ofMatrix.symm σ.1))
    (hnormalized : ∀ σ n hn, ∀ᵐ h ∂(G σ (historyIndex N n)).law, h ∉ P.stop n hn →
      ∀ X : Matrix A A ℂ, Matrix.trace (CStarMatrix.ofMatrix.symm
        ((P.stage n hn).operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X)
    (hphysical : ∀ σ n hn E, MeasurableSet E → ∀ i j,
      (∫ h in E, (G σ (historyIndex N (n+1))).density h i j ∂(G σ (historyIndex N (n+1))).law) =
        ∫ h, actualFiniteStep P H_A n hn h E ((G σ (historyIndex N n)).density h) i j
          ∂(G σ (historyIndex N n)).law),
    letI : NeZero e := ⟨by omega⟩
    let θ := fun σ : DensityState (Fin e) => (Real.log e - vonNeumannEntropy σ) / W.readout () () β
    ∃ μ : Measure (F (historyIndex N N)), IsProbabilityMeasure μ ∧
      (∀ σ, (G σ (historyIndex N N)).law = μ) ∧
      (∀ σ, (G σ (historyIndex N N)).law.map (P.record (historyIndex N N)) =
        μ.map (P.record (historyIndex N N))) ∧
      (∀ σ n hn, ∀ E : Set (ℕ × D), MeasurableSet E →
        (G σ (historyIndex N (n+1))).law ((P.stage n hn).preceding ⁻¹' P.stop n hn ∩
          P.record (historyIndex N (n+1)) ⁻¹' E) =
          (G σ (historyIndex N n)).law (P.stop n hn ∩ P.record (historyIndex N n) ⁻¹' E)) ∧
      (⨅ κ : RealOutput (ℕ × D), ⨆ σ : DensityState (Fin e),
        ∫⁻ z : ℝ, ENNReal.ofReal |z - θ σ|
          ∂(((G σ (historyIndex N N)).law.map (P.record (historyIndex N N))).bind κ.kernel)) =
        ENNReal.ofReal (Real.log e / (2 * β))

theorem actual_law : arena.{u}.Law actual := by
  exact visible_adaptive_record_law_and_absolute_minimax

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q := PUnit.{u+1}
  letI : MeasurableSpace Q := ⊤
  let P : FiniteStoppedPolicy 0 (fun _ => Q) Q Unit :=
    { stop := fun n hn => False.elim (by omega)
      measurable_stop := fun n hn => False.elim (by omega)
      stage := fun n hn => False.elim (by omega)
      time := fun n hn => False.elim (by omega)
      measurable_time := fun n hn => False.elim (by omega)
      cemetery := fun n hn => False.elim (by omega)
      measurable_cemetery := fun n hn => False.elim (by omega)
      preceding_cemetery := fun n hn => False.elim (by omega)
      stopped_cemetery := fun n hn => False.elim (by omega)
      record := fun _ _ => (0, PUnit.unit)
      measurable_record := fun _ => measurable_const
      stopped_record := fun n hn => False.elim (by omega)
      active_length := fun n hn => False.elim (by omega) }
  have hσ (σ : DensityState (Fin 2)) : (CStarMatrix.ofMatrix.symm σ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)
  let G : DensityState (Fin 2) → ∀ _ : Fin 1, ActualHistory Q (Unit × Fin 2) := fun σ _ =>
    { law := Measure.dirac PUnit.unit
      probability := inferInstance
      density := fun _ => (1 : Matrix Unit Unit ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.1
      measurable_density := measurable_const
      integrable_density := integrable_const _
      state_density := fun _ => ⟨Matrix.PosSemidef.one.kronecker (hσ σ), by
        have ht : Matrix.trace (CStarMatrix.ofMatrix.symm σ.1) = 1 := σ.2.2
        rw [Matrix.trace_kronecker, ht, mul_one]
        simp⟩ }
  obtain ⟨μ, hprob, hlaw, hrecord, hstop, hrisk⟩ :=
    h (A := Unit) 2 (by norm_num) 1 (by norm_num) 0 (fun _ => Q) Q P
      0 Matrix.isHermitian_zero PUnit.unit 1 Matrix.PosSemidef.one (by simp) G
      (fun _ => rfl) (fun _ => Filter.EventuallyEq.rfl)
      (fun σ n hn => False.elim (by omega))
      (fun σ n hn => False.elim (by omega))
  have hzero : (⨅ κ : RealOutput (ℕ × Q), ⨆ σ : DensityState (Fin 2),
      ∫⁻ z : ℝ, ENNReal.ofReal |z|
        ∂(((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))).bind κ.kernel)) = 0 := by
    apply le_antisymm
    · let κ : RealOutput (ℕ × Q) := ⟨Kernel.const _ (Measure.dirac (0 : ℝ)), inferInstance⟩
      refine (iInf_le _ κ).trans (iSup_le fun σ => ?_)
      change (∫⁻ z : ℝ, ENNReal.ofReal |z|
        ∂(((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))).bind
          (fun _ => Measure.dirac (0 : ℝ)))) ≤ 0
      haveI : IsProbabilityMeasure
          ((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))) := by
        constructor
        rw [Measure.map_apply (P.measurable_record _) MeasurableSet.univ]
        simp [G]
      rw [Measure.bind_const, measure_univ, one_smul, lintegral_dirac]
      simp
    · exact bot_le
  have hrisk' : (⨅ κ : RealOutput (ℕ × Q), ⨆ σ : DensityState (Fin 2),
      ∫⁻ z : ℝ, ENNReal.ofReal |z|
        ∂(((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))).bind κ.kernel)) =
      ENNReal.ofReal (Real.log 2 / 2) := by
    simpa only [rejected, realize, signature, div_zero, sub_zero, mul_one, Nat.cast_ofNat] using hrisk
  have hpos : 0 < Real.log (2 : ℝ) / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hne := ENNReal.ofReal_pos.mpr hpos
  rw [hzero] at hrisk'
  exact (ne_of_gt hne) hrisk'.symm

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact False.elim (hji (Subsingleton.elim j i))
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num [actual, realize, signature]

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.visible_adaptive_record_law_and_absolute_minimax.{u}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ β => β) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "VisibleAdaptiveRecordLaw") "visible_adaptive_record_law_and_absolute_minimax") "Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw/Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ β => β) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.visible_adaptive_record_law_and_absolute_minimax, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw


noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena.{u}
      Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.actual)
    Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"visible_adaptive_record_law_and_absolute_minimax\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.visible_adaptive_record_law_and_absolute_minimax, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.arena.{u}
    Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.actual)
  Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.observation0.{u} : {A : Type} →
  [inst : Fintype.{0} A] →
    [inst_1 : DecidableEq.{1} A] →
      (e : Nat) →
        (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
          (β : Real) →
            (hβ :
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  β) →
              (N : Nat) →
                (F :
                    Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      Type u) →
                  [inst_2 :
                      (i :
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        MeasurableSpace.{u} (F i)] →
                    (D : Type u) →
                      [inst_3 : MeasurableSpace.{u} D] →
                        (P :
                            @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.{u} N F D A inst_2
                              inst_3 inst inst_1) →
                          (H_A : Matrix.{0, 0, 0} A A Complex) →
                            (hH_A :
                                @Matrix.IsHermitian.{0, 0} Complex A
                                  (@InvolutiveStar.toStar.{0} Complex
                                    (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                      (@AddCommMonoid.toAddMonoid.{0} Complex
                                        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                                Complex.instNonUnitalCommRing)))))
                                      (@StarRing.toStarAddMonoid.{0} Complex
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                              Complex.instNonUnitalCommRing)))
                                        Complex.instStarRing)))
                                  H_A) →
                              (h₀ :
                                  F
                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                                (ρ₀ : Matrix.{0, 0, 0} A A Complex) →
                                  (hρ₀ :
                                      @Matrix.PosSemidef.{0, 0} A Complex Complex.instRing Complex.partialOrder
                                        Complex.instStarRing ρ₀) →
                                    (hρ₀trace :
                                        @Eq.{1} Complex
                                          (@Matrix.trace.{0, 0} A Complex inst Complex.instAddCommMonoid ρ₀)
                                          (@OfNat.ofNat.{0} Complex (nat_lit 1)
                                            (@One.toOfNat1.{0} Complex Complex.instOne))) →
                                      (G :
                                          @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0}
                                              (Fin e) (Fin.fintype e) (instDecidableEqFin e) →
                                            (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                              @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.{u, 0}
                                                (F i) (Prod.{0, 0} A (Fin e)) (inst_2 i)
                                                (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))) →
                                        (hinit :
                                            ∀
                                              (σ :
                                                @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0}
                                                  (Fin e) (Fin.fintype e) (instDecidableEqFin e)),
                                              @Eq.{u + 1}
                                                (@MeasureTheory.Measure.{u}
                                                  (F
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                  (inst_2
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                                (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u,
                                                      0}
                                                  (F
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                  (Prod.{0, 0} A (Fin e))
                                                  (inst_2
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                  (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                  (G σ
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                                (@MeasureTheory.Measure.dirac.{u}
                                                  (F
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                  (inst_2
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                  h₀)) →
                                          (hproduct :
                                              ∀
                                                (σ :
                                                  @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0}
                                                    (Fin e) (Fin.fintype e) (instDecidableEqFin e)),
                                                @Filter.EventuallyEq.{u, 0}
                                                  (F
                                                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                  (Matrix.{0, 0, 0} (Prod.{0, 0} A (Fin e)) (Prod.{0, 0} A (Fin e))
                                                    Complex)
                                                  (@MeasureTheory.ae.{u, u}
                                                    (F
                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                    (@MeasureTheory.Measure.{u}
                                                      (F
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0)))))
                                                      (inst_2
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0))))))
                                                    (@MeasureTheory.Measure.instFunLike.{u}
                                                      (F
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0)))))
                                                      (inst_2
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0))))))
                                                    (@MeasureTheory.Measure.instOuterMeasureClass.{u}
                                                      (F
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0)))))
                                                      (inst_2
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0))))))
                                                    (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u,
                                                          0}
                                                      (F
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0)))))
                                                      (Prod.{0, 0} A (Fin e))
                                                      (inst_2
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0)))))
                                                      (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                      (G σ
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0)))))))
                                                  (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.density.{u,
                                                        0}
                                                    (F
                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                    (Prod.{0, 0} A (Fin e))
                                                    (inst_2
                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                    (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                    (G σ
                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                                  fun
                                                    (x :
                                                      F
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                            (instOfNatNat (nat_lit 0))))) =>
                                                  @Matrix.kroneckerMap.{0, 0, 0, 0, 0, 0, 0} Complex Complex Complex A A
                                                    (Fin e) (Fin e)
                                                    (fun (x1 x2 : Complex) =>
                                                      @HMul.hMul.{0, 0, 0} Complex Complex Complex
                                                        (@instHMul.{0} Complex Complex.instMul) x1 x2)
                                                    ρ₀
                                                    (@DFunLike.coe.{1, 1, 1}
                                                      (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                        (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex))
                                                      (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                      (fun (x : CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex) =>
                                                        Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                      (@EquivLike.toFunLike.{1, 1, 1}
                                                        (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                          (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex))
                                                        (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                        (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                        (@Equiv.instEquivLike.{1, 1}
                                                          (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                          (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)))
                                                      (@Equiv.symm.{1, 1} (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                        (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                        (@CStarMatrix.ofMatrix.{0, 0, 0} (Fin e) (Fin e) Complex))
                                                      (@Subtype.val.{1} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                        (fun (rho : CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex) =>
                                                          And
                                                            (@LE.le.{0} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                              (@Preorder.toLE.{0}
                                                                (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                                (@PartialOrder.toPreorder.{0}
                                                                  (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                                  (@CStarMatrix.instPartialOrder.{0, 0} Complex
                                                                    (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                      Complex
                                                                      (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                        Complex instCommCStarAlgebraComplex))
                                                                    Complex.partialOrder
                                                                    (@RCLike.toStarOrderedRing.{0} Complex
                                                                      Complex.instRCLike)
                                                                    (Fin e) (Fin.fintype e))))
                                                              (@OfNat.ofNat.{0}
                                                                (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                                (nat_lit 0)
                                                                (@Zero.toOfNat0.{0}
                                                                  (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                                                                  (@CStarMatrix.instZero.{0, 0, 0} (Fin e) (Fin e)
                                                                    Complex Complex.instZero)))
                                                              rho)
                                                            (@Eq.{1} Complex
                                                              (@Matrix.trace.{0, 0} (Fin e) Complex (Fin.fintype e)
                                                                Complex.instAddCommMonoid rho)
                                                              (@OfNat.ofNat.{0} Complex (nat_lit 1)
                                                                (@One.toOfNat1.{0} Complex Complex.instOne))))
                                                        σ))) →
                                            (hnormalized :
                                                ∀
                                                  (σ :
                                                    @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0}
                                                      (Fin e) (Fin.fintype e) (instDecidableEqFin e))
                                                  (n : Nat) (hn : @LT.lt.{0} Nat instLTNat n N),
                                                  @Filter.Eventually.{u}
                                                    (F
                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                                        n))
                                                    (fun
                                                        (h :
                                                          F
                                                            (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                              N n)) =>
                                                      Not
                                                          (@Membership.mem.{u, u}
                                                            (F
                                                              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                N n))
                                                            (Set.{u}
                                                              (F
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N n)))
                                                            (@Set.instMembership.{u}
                                                              (F
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N n)))
                                                            (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.stop.{u}
                                                              N F D A inst_2 inst_3 inst inst_1 P n hn)
                                                            h) →
                                                        ∀ (X : Matrix.{0, 0, 0} A A Complex),
                                                          @Eq.{1} Complex
                                                            (@Matrix.trace.{0, 0} A Complex inst
                                                              Complex.instAddCommMonoid
                                                              (@DFunLike.coe.{1, 1, 1}
                                                                (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} A A Complex)
                                                                  (Matrix.{0, 0, 0} A A Complex))
                                                                (CStarMatrix.{0, 0, 0} A A Complex)
                                                                (fun (x : CStarMatrix.{0, 0, 0} A A Complex) =>
                                                                  Matrix.{0, 0, 0} A A Complex)
                                                                (@EquivLike.toFunLike.{1, 1, 1}
                                                                  (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} A A Complex)
                                                                    (Matrix.{0, 0, 0} A A Complex))
                                                                  (CStarMatrix.{0, 0, 0} A A Complex)
                                                                  (Matrix.{0, 0, 0} A A Complex)
                                                                  (@Equiv.instEquivLike.{1, 1}
                                                                    (CStarMatrix.{0, 0, 0} A A Complex)
                                                                    (Matrix.{0, 0, 0} A A Complex)))
                                                                (@Equiv.symm.{1, 1} (Matrix.{0, 0, 0} A A Complex)
                                                                  (CStarMatrix.{0, 0, 0} A A Complex)
                                                                  (@CStarMatrix.ofMatrix.{0, 0, 0} A A Complex))
                                                                (@DFunLike.coe.{1, 1, 1}
                                                                  (@CompletelyPositiveMap.{0, 0}
                                                                    (CStarMatrix.{0, 0, 0} A A Complex)
                                                                    (CStarMatrix.{0, 0, 0} A A Complex)
                                                                    (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0}
                                                                      Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0}
                                                                      Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instPartialOrder.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instPartialOrder.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst))
                                                                  (CStarMatrix.{0, 0, 0} A A Complex)
                                                                  (fun (x : CStarMatrix.{0, 0, 0} A A Complex) =>
                                                                    CStarMatrix.{0, 0, 0} A A Complex)
                                                                  (@CompletelyPositiveMap.instFunLike.{0, 0}
                                                                    (CStarMatrix.{0, 0, 0} A A Complex)
                                                                    (CStarMatrix.{0, 0, 0} A A Complex)
                                                                    (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0}
                                                                      Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0}
                                                                      Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instPartialOrder.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instPartialOrder.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst)
                                                                    (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                                                                      (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0}
                                                                        Complex
                                                                        (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0}
                                                                          Complex instCommCStarAlgebraComplex))
                                                                      Complex.partialOrder
                                                                      (@RCLike.toStarOrderedRing.{0} Complex
                                                                        Complex.instRCLike)
                                                                      A inst))
                                                                  (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualEventStage.operation.{u,
                                                                        0}
                                                                    (F
                                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                        N n))
                                                                    (F
                                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                        N
                                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                          (@instHAdd.{0} Nat instAddNat) n
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                            (instOfNatNat (nat_lit 1))))))
                                                                    A
                                                                    (inst_2
                                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                        N n))
                                                                    (inst_2
                                                                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                        N
                                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                          (@instHAdd.{0} Nat instAddNat) n
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                            (instOfNatNat (nat_lit 1))))))
                                                                    inst inst_1
                                                                    (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.stage.{u}
                                                                      N F D A inst_2 inst_3 inst inst_1 P n hn)
                                                                    h
                                                                    (@Set.univ.{u}
                                                                      (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualEventStage.Outcome.{u,
                                                                            0}
                                                                        (F
                                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                            N n))
                                                                        (F
                                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                            N
                                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                              (@instHAdd.{0} Nat instAddNat) n
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                (instOfNatNat (nat_lit 1))))))
                                                                        A
                                                                        (inst_2
                                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                            N n))
                                                                        (inst_2
                                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                            N
                                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                              (@instHAdd.{0} Nat instAddNat) n
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                (instOfNatNat (nat_lit 1))))))
                                                                        inst inst_1
                                                                        (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.stage.{u}
                                                                          N F D A inst_2 inst_3 inst inst_1 P n hn)
                                                                        h)))
                                                                  (@DFunLike.coe.{1, 1, 1}
                                                                    (Equiv.{1, 1} (Matrix.{0, 0, 0} A A Complex)
                                                                      (CStarMatrix.{0, 0, 0} A A Complex))
                                                                    (Matrix.{0, 0, 0} A A Complex)
                                                                    (fun (x : Matrix.{0, 0, 0} A A Complex) =>
                                                                      CStarMatrix.{0, 0, 0} A A Complex)
                                                                    (@EquivLike.toFunLike.{1, 1, 1}
                                                                      (Equiv.{1, 1} (Matrix.{0, 0, 0} A A Complex)
                                                                        (CStarMatrix.{0, 0, 0} A A Complex))
                                                                      (Matrix.{0, 0, 0} A A Complex)
                                                                      (CStarMatrix.{0, 0, 0} A A Complex)
                                                                      (@Equiv.instEquivLike.{1, 1}
                                                                        (Matrix.{0, 0, 0} A A Complex)
                                                                        (CStarMatrix.{0, 0, 0} A A Complex)))
                                                                    (@CStarMatrix.ofMatrix.{0, 0, 0} A A Complex) X))))
                                                            (@Matrix.trace.{0, 0} A Complex inst
                                                              Complex.instAddCommMonoid X))
                                                    (@MeasureTheory.ae.{u, u}
                                                      (F
                                                        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                          N n))
                                                      (@MeasureTheory.Measure.{u}
                                                        (F
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n))
                                                        (inst_2
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n)))
                                                      (@MeasureTheory.Measure.instFunLike.{u}
                                                        (F
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n))
                                                        (inst_2
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n)))
                                                      (@MeasureTheory.Measure.instOuterMeasureClass.{u}
                                                        (F
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n))
                                                        (inst_2
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n)))
                                                      (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u,
                                                            0}
                                                        (F
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n))
                                                        (Prod.{0, 0} A (Fin e))
                                                        (inst_2
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n))
                                                        (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                        (G σ
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N n))))) →
                                              (hphysical :
                                                  ∀
                                                    (σ :
                                                      @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0}
                                                        (Fin e) (Fin.fintype e) (instDecidableEqFin e))
                                                    (n : Nat) (hn : @LT.lt.{0} Nat instLTNat n N)
                                                    (E :
                                                      Set.{u}
                                                        (F
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) n
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))))),
                                                    @MeasurableSet.{u}
                                                        (F
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) n
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))))
                                                        (inst_2
                                                          (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                            N
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) n
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))))
                                                        E →
                                                      ∀ (i j : Prod.{0, 0} A (Fin e)),
                                                        @Eq.{1} Complex
                                                          (@MeasureTheory.integral.{u, 0}
                                                            (F
                                                              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                N
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) n
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1))))))
                                                            Complex Complex.instNormedAddCommGroup
                                                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                                              Real.instRCLike
                                                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                                                Complex.instNormedAddCommGroup)
                                                              instInnerProductSpaceRealComplex)
                                                            (inst_2
                                                              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                N
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) n
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1))))))
                                                            (@MeasureTheory.Measure.restrict.{u}
                                                              (F
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) n
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))))
                                                              (inst_2
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) n
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))))
                                                              (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u,
                                                                    0}
                                                                (F
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) n
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))))
                                                                (Prod.{0, 0} A (Fin e))
                                                                (inst_2
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) n
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))))
                                                                (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                                (G σ
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) n
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1)))))))
                                                              E)
                                                            fun
                                                              (h :
                                                                F
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) n
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1)))))) =>
                                                            @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.density.{u,
                                                                  0}
                                                              (F
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) n
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))))
                                                              (Prod.{0, 0} A (Fin e))
                                                              (inst_2
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) n
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))))
                                                              (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                              (G σ
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) n
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))))
                                                              h i j)
                                                          (@MeasureTheory.integral.{u, 0}
                                                            (F
                                                              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                N n))
                                                            Complex Complex.instNormedAddCommGroup
                                                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex
                                                              Real.instRCLike
                                                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex
                                                                Complex.instNormedAddCommGroup)
                                                              instInnerProductSpaceRealComplex)
                                                            (inst_2
                                                              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                N n))
                                                            (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u,
                                                                  0}
                                                              (F
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N n))
                                                              (Prod.{0, 0} A (Fin e))
                                                              (inst_2
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N n))
                                                              (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                              (G σ
                                                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                  N n)))
                                                            fun
                                                              (h :
                                                                F
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N n)) =>
                                                            @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.actualFiniteStep.{u}
                                                              N F D A (Fin e) inst_2 inst_3 inst inst_1 (Fin.fintype e)
                                                              (instDecidableEqFin e) P H_A n hn h E
                                                              (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.density.{u,
                                                                    0}
                                                                (F
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N n))
                                                                (Prod.{0, 0} A (Fin e))
                                                                (inst_2
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N n))
                                                                (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                                                                (G σ
                                                                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex
                                                                    N n))
                                                                h)
                                                              i j)) →
                                                (σ :
                                                    @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0}
                                                      (Fin e) (Fin.fintype e) (instDecidableEqFin e)) →
                                                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0,
                                                      0, 0, 0, 0}
                                                    Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.signature
                                                    PUnit.unit.{1} PUnit.unit.{1} :=
  fun {A : Type} [Fintype.{0} A] [DecidableEq.{1} A] (e : Nat)
    (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) (β : Real)
    (hβ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β)
    (N : Nat)
    (F :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Type u)
    [(i :
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        MeasurableSpace.{u} (F i)]
    (D : Type u) [MeasurableSpace.{u} D]
    (P : @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.{u} N F D A inst_2 inst_3 inst inst_1)
    (H_A : Matrix.{0, 0, 0} A A Complex)
    (hH_A :
      @Matrix.IsHermitian.{0, 0} Complex A
        (@InvolutiveStar.toStar.{0} Complex
          (@StarAddMonoid.toInvolutiveStar.{0} Complex
            (@AddCommMonoid.toAddMonoid.{0} Complex
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
            (@StarRing.toStarAddMonoid.{0} Complex
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
              Complex.instStarRing)))
        H_A)
    (h₀ :
      F
        (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (ρ₀ : Matrix.{0, 0, 0} A A Complex)
    (hρ₀ : @Matrix.PosSemidef.{0, 0} A Complex Complex.instRing Complex.partialOrder Complex.instStarRing ρ₀)
    (hρ₀trace :
      @Eq.{1} Complex (@Matrix.trace.{0, 0} A Complex inst Complex.instAddCommMonoid ρ₀)
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (G :
      @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0} (Fin e) (Fin.fintype e)
          (instDecidableEqFin e) →
        (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.{u, 0} (F i) (Prod.{0, 0} A (Fin e))
            (inst_2 i) (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e)))
    (hinit :
      ∀
        (σ :
          @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0} (Fin e) (Fin.fintype e)
            (instDecidableEqFin e)),
        @Eq.{u + 1}
          (@MeasureTheory.Measure.{u}
            (F
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (inst_2
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
          (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u, 0}
            (F
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (Prod.{0, 0} A (Fin e))
            (inst_2
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
            (G σ
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
          (@MeasureTheory.Measure.dirac.{u}
            (F
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (inst_2
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            h₀))
    (hproduct :
      ∀
        (σ :
          @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0} (Fin e) (Fin.fintype e)
            (instDecidableEqFin e)),
        @Filter.EventuallyEq.{u, 0}
          (F
            (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (Matrix.{0, 0, 0} (Prod.{0, 0} A (Fin e)) (Prod.{0, 0} A (Fin e)) Complex)
          (@MeasureTheory.ae.{u, u}
            (F
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (@MeasureTheory.Measure.{u}
              (F
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (inst_2
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            (@MeasureTheory.Measure.instFunLike.{u}
              (F
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (inst_2
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            (@MeasureTheory.Measure.instOuterMeasureClass.{u}
              (F
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (inst_2
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u, 0}
              (F
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (Prod.{0, 0} A (Fin e))
              (inst_2
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
              (G σ
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.density.{u, 0}
            (F
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (Prod.{0, 0} A (Fin e))
            (inst_2
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
            (G σ
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
          fun
            (x :
              F
                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) =>
          @Matrix.kroneckerMap.{0, 0, 0, 0, 0, 0, 0} Complex Complex Complex A A (Fin e) (Fin e)
            (fun (x1 x2 : Complex) =>
              @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) x1 x2)
            ρ₀
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex) (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex))
              (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
              (fun (x : CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex) => Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                  (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex))
                (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex) (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                (@Equiv.instEquivLike.{1, 1} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                  (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)))
              (@Equiv.symm.{1, 1} (Matrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                (@CStarMatrix.ofMatrix.{0, 0, 0} (Fin e) (Fin e) Complex))
              (@Subtype.val.{1} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                (fun (rho : CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex) =>
                  And
                    (@LE.le.{0} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                      (@Preorder.toLE.{0} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                        (@PartialOrder.toPreorder.{0} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                          (@CStarMatrix.instPartialOrder.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) (Fin e)
                            (Fin.fintype e))))
                      (@OfNat.ofNat.{0} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex) (nat_lit 0)
                        (@Zero.toOfNat0.{0} (CStarMatrix.{0, 0, 0} (Fin e) (Fin e) Complex)
                          (@CStarMatrix.instZero.{0, 0, 0} (Fin e) (Fin e) Complex Complex.instZero)))
                      rho)
                    (@Eq.{1} Complex
                      (@Matrix.trace.{0, 0} (Fin e) Complex (Fin.fintype e) Complex.instAddCommMonoid rho)
                      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))
                σ)))
    (hnormalized :
      ∀
        (σ :
          @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0} (Fin e) (Fin.fintype e)
            (instDecidableEqFin e))
        (n : Nat) (hn : @LT.lt.{0} Nat instLTNat n N),
        @Filter.Eventually.{u} (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
          (fun (h : F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)) =>
            Not
                (@Membership.mem.{u, u} (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                  (Set.{u} (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)))
                  (@Set.instMembership.{u} (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)))
                  (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.stop.{u} N F D A inst_2
                    inst_3 inst inst_1 P n hn)
                  h) →
              ∀ (X : Matrix.{0, 0, 0} A A Complex),
                @Eq.{1} Complex
                  (@Matrix.trace.{0, 0} A Complex inst Complex.instAddCommMonoid
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} A A Complex) (Matrix.{0, 0, 0} A A Complex))
                      (CStarMatrix.{0, 0, 0} A A Complex)
                      (fun (x : CStarMatrix.{0, 0, 0} A A Complex) => Matrix.{0, 0, 0} A A Complex)
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (CStarMatrix.{0, 0, 0} A A Complex) (Matrix.{0, 0, 0} A A Complex))
                        (CStarMatrix.{0, 0, 0} A A Complex) (Matrix.{0, 0, 0} A A Complex)
                        (@Equiv.instEquivLike.{1, 1} (CStarMatrix.{0, 0, 0} A A Complex)
                          (Matrix.{0, 0, 0} A A Complex)))
                      (@Equiv.symm.{1, 1} (Matrix.{0, 0, 0} A A Complex) (CStarMatrix.{0, 0, 0} A A Complex)
                        (@CStarMatrix.ofMatrix.{0, 0, 0} A A Complex))
                      (@DFunLike.coe.{1, 1, 1}
                        (@CompletelyPositiveMap.{0, 0} (CStarMatrix.{0, 0, 0} A A Complex)
                          (CStarMatrix.{0, 0, 0} A A Complex)
                          (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instPartialOrder.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instPartialOrder.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst))
                        (CStarMatrix.{0, 0, 0} A A Complex)
                        (fun (x : CStarMatrix.{0, 0, 0} A A Complex) => CStarMatrix.{0, 0, 0} A A Complex)
                        (@CompletelyPositiveMap.instFunLike.{0, 0} (CStarMatrix.{0, 0, 0} A A Complex)
                          (CStarMatrix.{0, 0, 0} A A Complex)
                          (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instNonUnitalCStarAlgebra.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instPartialOrder.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instPartialOrder.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst)
                          (@CStarMatrix.instStarOrderedRing.{0, 0} Complex
                            (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
                              (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
                            Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) A inst))
                        (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualEventStage.operation.{u, 0}
                          (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                          (F
                            (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          A (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                          (inst_2
                            (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          inst inst_1
                          (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.stage.{u} N F D A
                            inst_2 inst_3 inst inst_1 P n hn)
                          h
                          (@Set.univ.{u}
                            (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualEventStage.Outcome.{u, 0}
                              (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                              (F
                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              A (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                              (inst_2
                                (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              inst inst_1
                              (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.FiniteStoppedPolicy.stage.{u} N F D A
                                inst_2 inst_3 inst inst_1 P n hn)
                              h)))
                        (@DFunLike.coe.{1, 1, 1}
                          (Equiv.{1, 1} (Matrix.{0, 0, 0} A A Complex) (CStarMatrix.{0, 0, 0} A A Complex))
                          (Matrix.{0, 0, 0} A A Complex)
                          (fun (x : Matrix.{0, 0, 0} A A Complex) => CStarMatrix.{0, 0, 0} A A Complex)
                          (@EquivLike.toFunLike.{1, 1, 1}
                            (Equiv.{1, 1} (Matrix.{0, 0, 0} A A Complex) (CStarMatrix.{0, 0, 0} A A Complex))
                            (Matrix.{0, 0, 0} A A Complex) (CStarMatrix.{0, 0, 0} A A Complex)
                            (@Equiv.instEquivLike.{1, 1} (Matrix.{0, 0, 0} A A Complex)
                              (CStarMatrix.{0, 0, 0} A A Complex)))
                          (@CStarMatrix.ofMatrix.{0, 0, 0} A A Complex) X))))
                  (@Matrix.trace.{0, 0} A Complex inst Complex.instAddCommMonoid X))
          (@MeasureTheory.ae.{u, u} (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
            (@MeasureTheory.Measure.{u} (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
              (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)))
            (@MeasureTheory.Measure.instFunLike.{u}
              (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
              (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)))
            (@MeasureTheory.Measure.instOuterMeasureClass.{u}
              (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
              (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)))
            (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u, 0}
              (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)) (Prod.{0, 0} A (Fin e))
              (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
              (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
              (G σ (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)))))
    (hphysical :
      ∀
        (σ :
          @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0} (Fin e) (Fin.fintype e)
            (instDecidableEqFin e))
        (n : Nat) (hn : @LT.lt.{0} Nat instLTNat n N)
        (E :
          Set.{u}
            (F
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))),
        @MeasurableSet.{u}
            (F
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (inst_2
              (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            E →
          ∀ (i j : Prod.{0, 0} A (Fin e)),
            @Eq.{1} Complex
              (@MeasureTheory.integral.{u, 0}
                (F
                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (inst_2
                  (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@MeasureTheory.Measure.restrict.{u}
                  (F
                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (inst_2
                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u, 0}
                    (F
                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (Prod.{0, 0} A (Fin e))
                    (inst_2
                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                    (G σ
                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  E)
                fun
                  (h :
                    F
                      (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
                @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.density.{u, 0}
                  (F
                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (Prod.{0, 0} A (Fin e))
                  (inst_2
                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                  (G σ
                    (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  h i j)
              (@MeasureTheory.integral.{u, 0} (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.law.{u, 0}
                  (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)) (Prod.{0, 0} A (Fin e))
                  (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                  (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                  (G σ (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)))
                fun (h : F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)) =>
                @D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.actualFiniteStep.{u} N F D A (Fin e) inst_2 inst_3
                  inst inst_1 (Fin.fintype e) (instDecidableEqFin e) P H_A n hn h E
                  (@D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.ActualHistory.density.{u, 0}
                    (F (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)) (Prod.{0, 0} A (Fin e))
                    (inst_2 (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n))
                    (@instFintypeProd.{0, 0} A (Fin e) inst (Fin.fintype e))
                    (G σ (D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.historyIndex N n)) h)
                  i j))
    (σ :
      @D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState.{0} (Fin e) (Fin.fintype e)
        (instDecidableEqFin e)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.signature
    Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.actual PUnit.unit.{1} PUnit.unit.{1} β

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"visible_adaptive_record_law_and_absolute_minimax\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letValue\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.visible_adaptive_record_law_and_absolute_minimax, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letValue, .body, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"visible_adaptive_record_law_and_absolute_minimax\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.visible_adaptive_record_law_and_absolute_minimax, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration.{u}).actual (Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration.{u}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration.{u}).variation.1 (Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"VisibleAdaptiveRecordLaw\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw, declaration := `Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
