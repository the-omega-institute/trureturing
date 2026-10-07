import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.GaussianObservationLaw
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit ContinuousLinearMap MeasureTheory ProbabilityTheory WithLp Set
open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace ProbabilityTheory MatrixOrder Topology
noncomputable section
namespace Reg.D5.S3.Observer.Linear.GaussianObservationLaw
open _root_.D5.S3.Observer.Linear.GaussianObservationLaw
structure Parameters where
  n : Type
  p : Type
  finiteN : Fintype n
  decN : DecidableEq n
  finiteP : Fintype p
  decP : DecidableEq p
  matrix : Matrix p n ℝ
  beta : ℝ
  sigma : ℝ
abbrev signature : Signature where
  Params := Parameters
  State := fun q => E (q.n ⊕ q.p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ q => E q.p × E q.n
  Anchor := Empty
  finiteAnchor := inferInstance
def emptyAnchor : ∀ (_ : Empty) q, signature.State q := fun e => nomatch e
def actual : Realization signature := realize signature
  (fun _ q z => by
    letI := q.finiteN
    letI := q.decN
    letI := q.finiteP
    letI := q.decP
    exact (action (observation q.matrix) z, action (signal (n := q.n) (p := q.p)) z)) emptyAnchor
def modified : Realization signature := realize signature (fun _ _ _ => (0,0)) emptyAnchor
variable {n p : Type} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
def parameters (M : Matrix p n ℝ) (β σ : ℝ) : Parameters :=
  ⟨n,p,inferInstance,inferInstance,inferInstance,inferInstance,M,β,σ⟩
def readJoint (family : Realization signature) (M : Matrix p n ℝ) (β σ : ℝ) : Measure (E p × E n) :=
  (inputLaw (n := n) (p := p) β (σ^2)⁻¹).map (family.readout () (parameters M β σ))
def readData (family : Realization signature) (M : Matrix p n ℝ) (β σ : ℝ) : Measure (E p) :=
  (inputLaw (n := n) (p := p) β (σ^2)⁻¹).map (fun z => (family.readout () (parameters M β σ) z).1)
def readInformation (family : Realization signature) (M : Matrix p n ℝ) (β σ : ℝ) : ℝ≥0∞ :=
  InformationTheory.klDiv (readJoint family M β σ)
    ((readJoint family M β σ).fst.prod (readJoint family M β σ).snd)
def theoremLaw (family : Realization signature) : Prop :=
  ∀ {n p : Type} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (M : Matrix p n ℝ) (β σ : ℝ), 0 < β → 0 < σ ^ 2 →
  let τ := (σ ^ 2)⁻¹
  readInformation family M β σ ≠ ∞ ∧
    Integrable
      (llr (readJoint family M β σ)
        ((readJoint family M β σ).fst.prod (readJoint family M β σ).snd))
      (readJoint family M β σ) ∧
    (∫ z : E p × E n,
      llr (readJoint family M β σ)
        ((readJoint family M β σ).fst.prod (readJoint family M β σ).snd) z
        ∂readJoint family M β σ) =
      (Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
        Real.log ((covariance M β τ).det)) / 2 ∧
    (readInformation family M β σ).toReal =
      (Real.log ((β⁻¹ • (1 : Matrix n n ℝ)).det) -
        Real.log ((covariance M β τ).det)) / 2 ∧
    (readInformation family M β σ).toReal =
      Real.log ((1 + (τ / β) • (M.transpose * M)).det) / 2 ∧
    ((∫ y : E p, physicalFreeEnergy β (posteriorKernel M β τ y)
        ∂readData family M β σ) -
      physicalFreeEnergy β
        (multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ)))) =
      β⁻¹ * (readInformation family M β σ).toReal ∧
    readJoint family M β σ = readData family M β σ ⊗ₘ posteriorKernel M β τ ∧
    ((inputLaw (n := n) (p := p) β τ).map (action signal) =
      multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ)) ∧
    (inputLaw (n := n) (p := p) β τ).map (action noise) =
      multivariateGaussian 0 (τ⁻¹ • (1 : Matrix p p ℝ)) ∧
    IndepFun (action (signal (n := n) (p := p))) (action noise) (inputLaw β τ))

def arena : Arena where
  signature := signature
  Law := theoremLaw

theorem actual_law : arena.Law actual := by
  intro n p fn dn fp dp M β σ hβ hσ
  exact _root_.D5.S3.Observer.Linear.GaussianObservationLaw.gaussian_observation_law M β σ hβ hσ

theorem modified_law : ¬ arena.Law modified := by
  intro h
  let E1 := E (Fin 1)
  have hv := h (n := Fin 1) (p := Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 zero_lt_one (by norm_num)
  have hdis := hv.2.2.2.2.2.2.1
  simp only [one_pow, inv_one] at hdis
  letI : IsProbabilityMeasure (inputLaw (n := Fin 1) (p := Fin 1) 1 (1^2)⁻¹) := by
    unfold inputLaw
    infer_instance
  have hj : readJoint modified (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 =
      Measure.dirac ((0 : E1), (0 : E1)) := by
    change (inputLaw (n := Fin 1) (p := Fin 1) 1 (1^2)⁻¹).map (fun _ => ((0:E1),(0:E1))) = _
    rw [Measure.map_const, measure_univ, one_smul]
  have hd : readData modified (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 =
      Measure.dirac (0 : E1) := by
    change (inputLaw (n := Fin 1) (p := Fin 1) 1 (1^2)⁻¹).map (fun _ => (0:E1)) = _
    rw [Measure.map_const, measure_univ, one_smul]
  rw [hj, hd] at hdis
  let K : Kernel E1 E1 := posteriorKernel (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 1
  letI : IsMarkovKernel K := by
    dsimp [K, posteriorKernel, translatedKernel]
    exact Kernel.IsMarkovKernel.map _ (by fun_prop)
  have htrans (L : E1 →L[ℝ] E1) (ν : Measure E1) [IsProbabilityMeasure ν] (y : E1) :
      translatedKernel L ν y = ν.map (fun r => L y + r) := by
    have hm : Measurable (fun z : E1 × E1 => L z.1 + z.2) := by fun_prop
    ext s hs
    rw [translatedKernel, Kernel.map_apply' _ hm _ hs,
      Kernel.id_prod_apply' _ _ (hm hs), Kernel.const_apply,
      Measure.map_apply (by fun_prop) hs]
    rfl
  have hpost : K (0 : E1) =
      multivariateGaussian (0 : E1) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [show K = posteriorKernel (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 from rfl,
      posteriorKernel, htrans]
    simp [_root_.D5.S3.Observer.Linear.GaussianObservationLaw.covariance, precision, gain]
  have hcomp : Measure.dirac (0 : E1) ⊗ₘ K = (K 0).map (Prod.mk (0:E1)) := by
    ext s hs
    rw [Measure.dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]
  change Measure.dirac ((0:E1),(0:E1)) = Measure.dirac (0:E1) ⊗ₘ K at hdis
  rw [hcomp] at hdis
  have hs := congrArg (fun ν : Measure (E1 × E1) => ν.map Prod.snd) hdis
  rw [Measure.map_dirac' measurable_snd,
    Measure.map_map measurable_snd measurable_prodMk_left] at hs
  change Measure.dirac (0:E1) = (K 0).map id at hs
  rw [Measure.map_id, hpost] at hs
  have hh := congrArg (fun ν : Measure E1 => Var[fun x : E1 => x (0 : Fin 1); ν]) hs
  rw [variance_dirac, variance_eval_multivariateGaussian Matrix.PosSemidef.one] at hh
  norm_num at hh

theorem dependence_proof : ObservationalDependence signature actual := by
  intro role
  let E1 := E (Fin 1)
  let z : E (Fin 1 ⊕ Fin 1) := toLp 2 (Sum.elim (fun _ => (1:ℝ)) (fun _ => (0:ℝ)))
  refine ⟨parameters (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 1, 0, z, ?_⟩
  intro h
  have hh := congrArg (fun q : E1 × E1 => q.2 (0 : Fin 1)) h
  change ((action (signal (n := Fin 1) (p := Fin 1))) (0 : E (Fin 1 ⊕ Fin 1))) (0:Fin 1) =
    ((action (signal (n := Fin 1) (p := Fin 1))) z) (0:Fin 1) at hh
  have ha (L : Matrix (Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (x : E (Fin 1 ⊕ Fin 1)) :
    action L x = toLp 2 (L.mulVec (ofLp x)) := rfl
  simp only [map_zero, PiLp.zero_apply, ha, ofLp_toLp] at hh
  norm_num [signal, Matrix.fromCols, Matrix.mulVec, dotProduct, z,
    Fintype.sum_sum_type] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, modified, modified_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨modified, ?_, rfl, modified_law⟩
      intro other hne
      exact (hne (by cases role; cases other; rfl)).elim
    · intro e; exact nomatch e
  dependence := dependence_proof
noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Linear.GaussianObservationLaw.gaussian_observation_law) (type_of% (realize.{1, 0, 0, 0, 0} signature
    (fun _ q z => by
      letI := q.finiteN
      letI := q.decN
      letI := q.finiteP
      letI := q.decP
      exact (action (observation q.matrix) z, action (signal (n := q.n) (p := q.p)) z)) emptyAnchor)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Linear") "GaussianObservationLaw") "gaussian_observation_law") "Reg.D5.S3.Observer.Linear.GaussianObservationLaw/Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature
    (fun _ q z => by
      letI := q.finiteN
      letI := q.decN
      letI := q.finiteP
      letI := q.decP
      exact (action (observation q.matrix) z, action (signal (n := q.n) (p := q.p)) z)) emptyAnchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Linear.GaussianObservationLaw, definition := none, coordinates := #[0, 1, 6, 7, 8], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `D5.S3.Observer.Linear.GaussianObservationLaw.gaussian_observation_law, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.observationFact0, `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.anchorEnumeration }

end Reg.D5.S3.Observer.Linear.GaussianObservationLaw


noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena
noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena
noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{1, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena Reg.D5.S3.Observer.Linear.GaussianObservationLaw.actual)
    Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration)

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"gaussian_observation_law\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `D5.S3.Observer.Linear.GaussianObservationLaw.gaussian_observation_law, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{1, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.GaussianObservationLaw.arena Reg.D5.S3.Observer.Linear.GaussianObservationLaw.actual)
  Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration)

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.observation0 : {n p : Type} →
  [inst : Fintype.{0} n] →
    [inst_1 : DecidableEq.{1} n] →
      [inst_2 : Fintype.{0} p] →
        [inst_3 : DecidableEq.{1} p] →
          (M : Matrix.{0, 0, 0} p n Real) →
            (β σ : Real) →
              (hβ :
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β) →
                (hσ :
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) σ
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  (z : D5.S3.Observer.Linear.GaussianObservationLaw.E (Sum.{0, 0} n p)) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
                      Reg.D5.S3.Observer.Linear.GaussianObservationLaw.signature PUnit.unit.{1}
                      (Reg.D5.S3.Observer.Linear.GaussianObservationLaw.Parameters.mk n p inst inst_1 inst_2 inst_3 M β
                        σ) :=
  fun {n p : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] [inst_2 : Fintype.{0} p]
    [inst_3 : DecidableEq.{1} p] (M : Matrix.{0, 0, 0} p n Real) (β σ : Real)
    (hβ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β)
    (hσ :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) σ
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
  have τ : Real :=
    @Inv.inv.{0} Real Real.instInv
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) σ
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))));
  fun (z : D5.S3.Observer.Linear.GaussianObservationLaw.E (Sum.{0, 0} n p)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.GaussianObservationLaw.signature Reg.D5.S3.Observer.Linear.GaussianObservationLaw.actual
    PUnit.unit.{1} (Reg.D5.S3.Observer.Linear.GaussianObservationLaw.Parameters.mk n p inst inst_1 inst_2 inst_3 M β σ)
    z

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"gaussian_observation_law\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `D5.S3.Observer.Linear.GaussianObservationLaw.gaussian_observation_law, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .argument, .function, .argument, .function, .argument, .function, .argument, .function, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"gaussian_observation_law\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `D5.S3.Observer.Linear.GaussianObservationLaw.gaussian_observation_law, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration).actual (Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration).variation.2.choose (Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration).variation.1 (Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"GaussianObservationLaw\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw, declaration := `Reg.D5.S3.Observer.Linear.GaussianObservationLaw.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
