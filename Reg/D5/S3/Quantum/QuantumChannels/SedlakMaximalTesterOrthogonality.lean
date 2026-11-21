import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
import Reg.Support.DependentFamily

/-! Source-bound audit of the maximal one-step tester incompatibility characterization. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality

open _root_.Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality
open _root_.D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality (IsTester TesterCompatibleAt testerRobustness)
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private abbrev Input (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
private abbrev Joint (d0 d1 : ℕ) := Matrix (Fin d1 × Fin d0) (Fin d1 × Fin d0) ℂ

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

/-- Observe maximality at the actual robustness value and retain both equivalences. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (d0 d1 p q : ℕ),
      0 < d0 → 0 < d1 → 0 < p → 0 < q →
      ∀ (A : Fin p → Joint d0 d1) (B : Fin q → Joint d0 d1) (ρ σ : Input d0),
        IsDensity ρ → IsDensity σ →
        IsTester A → IsTester B →
        ((∀ j, (A j).PosSemidef) ∧
          (∑ j, A j = Matrix.kronecker (1 : Input d1) ρ)) →
        ((∀ k, (B k).PosSemidef) ∧
          (∑ k, B k = Matrix.kronecker (1 : Input d1) σ)) →
        (R.readout () () (testerRobustness A B) (1 / 2 : ℝ) ↔ ρ * σ = 0) ∧
        (ρ * σ = 0 ↔ ∀ j k, A j * B k = 0)

private theorem one_density : IsDensity (1 : Input 1) :=
  ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩

private theorem one_normalization :
    (∀ _ : Fin 1, (1 : Joint 1 1).PosSemidef) ∧
      (∑ _ : Fin 1, (1 : Joint 1 1)) = Matrix.kronecker (1 : Input 1) 1 :=
  ⟨fun _ => Matrix.PosSemidef.one, by
    calc
      (∑ _ : Fin 1, (1 : Joint 1 1)) = 1 := by simp
      _ = Matrix.kronecker (1 : Input 1) 1 := Matrix.one_kronecker_one.symm⟩

private theorem one_tester : IsTester (fun _ : Fin 1 => (1 : Joint 1 1)) :=
  ⟨one_normalization.1, 1, one_density, one_normalization.2⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have observed := law 1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    (fun _ => 1) (fun _ => 1) 1 1 one_density one_density one_tester one_tester
    one_normalization one_normalization
  exact one_ne_zero (by simpa only [mul_one] using observed.1.mp True.intro)

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 1 / 2, 0, fun equality => ?_⟩
    have transported := congrFun equality (1 / 2 : ℝ)
    change ((1 / 2 : ℝ) = 1 / 2) = ((0 : ℝ) = 1 / 2) at transported
    have impossible := Eq.mp transported (rfl : (1 / 2 : ℝ) = 1 / 2)
    norm_num at impossible

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
      name := `Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

namespace NormalizationOrthogonalIffEffectwise

abbrev productSignature : Signature where
  Params := ℕ
  State d := Input d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Input d → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def productActual : Realization productSignature :=
  realize productSignature (fun _ _ X Y => X = Y) (fun e => nomatch e)

def productRejected : Realization productSignature :=
  realize productSignature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev productArena : Arena where
  signature := productSignature
  Law R :=
    ∀ {d0 d1 p q : ℕ} {A : Fin p → Joint d0 d1} {B : Fin q → Joint d0 d1}
      {ρ σ : Input d0},
      0 < d1 → IsDensity ρ →
      ((∀ j, (A j).PosSemidef) ∧
        (∑ j, A j = Matrix.kronecker (1 : Input d1) ρ)) →
      ((∀ k, (B k).PosSemidef) ∧
        (∑ k, B k = Matrix.kronecker (1 : Input d1) σ)) →
      (R.readout () d0 (ρ * σ) 0 ↔ ∀ j k, A j * B k = 0)

private theorem product_rejected : ¬ productArena.Law productRejected := by
  intro law
  have observed := law (d0 := 1) (d1 := 1) (p := 1) (q := 1)
    (A := fun _ => 1) (B := fun _ => 1) (ρ := 1) (σ := 1)
    (by decide) one_density one_normalization one_normalization
  have zero := observed.mp True.intro 0 0
  exact one_ne_zero (by simpa only [mul_one] using zero)

def productEvidence :
    Registration productArena (type_of% @normalization_orthogonal_iff_effectwise) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨@normalization_orthogonal_iff_effectwise, productRejected, product_rejected⟩
  sensitivity := ⟨fun i => ⟨productRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, product_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1, fun equality => ?_⟩
    have transported := congrFun equality 0
    change ((0 : Input 1) = 0) = ((1 : Input 1) = 0) at transported
    exact one_ne_zero (Eq.mp transported rfl)

def productRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.normalization_orthogonal_iff_effectwise)
      (Realization productSignature) Unit Unit := {
  unitName :=
    `Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.normalization_orthogonal_iff_effectwise.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality.NormalizationOrthogonalIffEffectwise.productEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨productArena⟩
  objectArena := .source ⟨productArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena ⟨productEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize productSignature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms productEvidence
#print axioms productRegistration

end NormalizationOrthogonalIffEffectwise

namespace NonorthogonalUpperBound

def boundActual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def boundRejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev boundArena : Arena where
  signature := signature
  Law R :=
    ∀ {d0 d1 p q : ℕ} {A : Fin p → Joint d0 d1} {B : Fin q → Joint d0 d1}
      {ρ σ : Input d0}, 0 < d0 → 0 < d1 → 0 < p → 0 < q →
      IsDensity ρ → IsDensity σ →
      ((∀ j, (A j).PosSemidef) ∧
        (∑ j, A j = Matrix.kronecker (1 : Input d1) ρ)) →
      ((∀ k, (B k).PosSemidef) ∧
        (∑ k, B k = Matrix.kronecker (1 : Input d1) σ)) →
      ρ * σ ≠ 0 →
      let t : ℝ := 2 - (ρ * σ).trace.re ^ 2 / ((max (p : ℝ) (q : ℝ))^2 * d0)
      1 ≤ t ∧ testerRobustness A B ≤ 1 - t⁻¹ ∧ R.readout () () (1 - t⁻¹) (1 / 2)

private theorem bound_rejected : ¬ boundArena.Law boundRejected := by
  intro law
  have nonzero : (1 : Input 1) * 1 ≠ 0 := by simp
  have observed := law (d0 := 1) (d1 := 1) (p := 1) (q := 1)
    (A := fun _ => 1) (B := fun _ => 1) (ρ := 1) (σ := 1)
    (by decide) (by decide) (by decide) (by decide)
    one_density one_density one_normalization one_normalization nonzero
  exact observed.2.2

def boundEvidence : Registration boundArena (type_of% @nonorthogonal_upper_bound) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@nonorthogonal_upper_bound, boundRejected, bound_rejected⟩
  sensitivity := ⟨fun i => ⟨boundRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bound_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, fun equality => ?_⟩
    have transported := congrFun equality 1
    change ((0 : ℝ) < 1) = ((1 : ℝ) < 1) at transported
    exact (lt_irrefl _) (Eq.mp transported zero_lt_one)

def boundRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.nonorthogonal_upper_bound)
      (Realization signature) Unit Unit := {
  unitName :=
    `Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.nonorthogonal_upper_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality.NonorthogonalUpperBound.boundEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena ⟨boundEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms boundEvidence
#print axioms boundRegistration

end NonorthogonalUpperBound

namespace CompatibleAtOfJointCover

abbrev traceSignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e)

def traceRejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev traceArena : Arena where
  signature := traceSignature
  Law R :=
    ∀ {d0 d1 p q : ℕ} {A : Fin p → Joint d0 d1} {B : Fin q → Joint d0 d1}
      {ρ σ : Input d0}, 0 < d1 → IsDensity ρ → IsDensity σ →
      ((∀ j, (A j).PosSemidef) ∧
        (∑ j, A j = Matrix.kronecker (1 : Input d1) ρ)) →
      ((∀ k, (B k).PosSemidef) ∧
        (∑ k, B k = Matrix.kronecker (1 : Input d1) σ)) →
      ∀ {C : Fin p × Fin q → Joint d0 d1} {H : Input d0},
      IsJointCover A B C H →
      let t := R.readout () () H.trace
      1 ≤ t ∧ TesterCompatibleAt (1 - t⁻¹) A B

private theorem one_cover :
    IsJointCover (fun _ : Fin 1 => (1 : Joint 1 1)) (fun _ : Fin 1 => (1 : Joint 1 1))
      (fun _ => 1) (1 : Input 1) := by
  refine ⟨fun _ => Matrix.PosSemidef.one, ?_, fun _ => ?_, fun _ => ?_⟩
  · change (∑ _ : Fin 1 × Fin 1, (1 : Joint 1 1)) = Matrix.kronecker (1 : Input 1) 1
    calc
      (∑ _ : Fin 1 × Fin 1, (1 : Joint 1 1)) = 1 := by simp
      _ = Matrix.kronecker (1 : Input 1) 1 := Matrix.one_kronecker_one.symm
  · simp
  · simp

private theorem trace_rejected : ¬ traceArena.Law traceRejected := by
  intro law
  have observed := law (d0 := 1) (d1 := 1) (p := 1) (q := 1) (ρ := 1) (σ := 1)
    (by decide) one_density one_density one_normalization one_normalization one_cover
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) observed.1

def traceEvidence : Registration traceArena (type_of% @compatibleAt_of_jointCover) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@compatibleAt_of_jointCover, traceRejected, trace_rejected⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, trace_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by simp [traceActual, realize]⟩

def traceRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.compatibleAt_of_jointCover)
      (Realization traceSignature) Unit Unit := {
  unitName :=
    `Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.compatibleAt_of_jointCover.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality.CompatibleAtOfJointCover.traceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms traceEvidence
#print axioms traceRegistration

end CompatibleAtOfJointCover

namespace ExplicitJointCover

abbrev totalSignature : Signature where
  Params := ℕ
  State d := Input d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Input d → Input d
  Anchor := Empty
  finiteAnchor := inferInstance

def totalActual : Realization totalSignature :=
  realize totalSignature (fun _ _ X Y => X + Y) (fun e => nomatch e)

def totalRejected : Realization totalSignature :=
  realize totalSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev totalArena : Arena where
  signature := totalSignature
  Law R :=
    ∀ {d0 d1 p q : ℕ} {A : Fin p → Joint d0 d1} {B : Fin q → Joint d0 d1}
      {ρ σ : Input d0}, 0 < p → 0 < q → IsDensity ρ → IsDensity σ →
      ((∀ j, (A j).PosSemidef) ∧
        (∑ j, A j = Matrix.kronecker (1 : Input d1) ρ)) →
      ((∀ k, (B k).PosSemidef) ∧
        (∑ k, B k = Matrix.kronecker (1 : Input d1) σ)) →
      ∀ {ε M : ℝ}, 0 ≤ ε → ε ≤ (p : ℝ)⁻¹ → ε ≤ (q : ℝ)⁻¹ →
      (p : ℝ)^2 ≤ M → (q : ℝ)^2 ≤ M →
      IsJointCover A B (fun jk => coverEntry p q ε M (A jk.1) (B jk.2))
        (R.readout () d0 (ρ + σ - ε • (ρ * σ + σ * ρ)) ((M * ε^2) • 1))

private theorem total_rejected : ¬ totalArena.Law totalRejected := by
  intro law
  have cover := law (d0 := 1) (d1 := 1) (p := 1) (q := 1)
    (A := fun _ => 1) (B := fun _ => 1) (ρ := 1) (σ := 1)
    (by decide) (by decide) one_density one_density one_normalization one_normalization
    (ε := 0) (M := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have impossible := cover.total
  change
    (∑ _ : Fin 1 × Fin 1,
      coverEntry (↑(1 : ℕ)) (↑(1 : ℕ)) 0 1 (1 : Joint 1 1) 1) =
      Matrix.kronecker (1 : Input 1) 0 at impossible
  have entry := congrFun (congrFun impossible (0, 0)) (0, 0)
  norm_num [coverEntry, Matrix.kronecker_apply, Matrix.ofNat_apply] at entry

def totalEvidence : Registration totalArena (type_of% @explicitJointCover) where
  actual := totalActual
  bridge := Iff.rfl
  variation := ⟨@explicitJointCover, totalRejected, total_rejected⟩
  sensitivity := ⟨fun i => ⟨totalRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, total_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1, fun equality => ?_⟩
    have evaluated := congrFun equality 0
    change (0 : Input 1) + 0 = 1 + 0 at evaluated
    exact one_ne_zero (by simpa only [add_zero] using evaluated.symm)

def totalRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.explicitJointCover)
      (Realization totalSignature) Unit Unit := {
  unitName :=
    `Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.explicitJointCover.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality.ExplicitJointCover.totalEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨totalArena⟩
  objectArena := .source ⟨totalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source totalArena ⟨totalEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize totalSignature (fun _ _ X Y => X + Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms totalEvidence
#print axioms totalRegistration

end ExplicitJointCover

end
end Reg.D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality
