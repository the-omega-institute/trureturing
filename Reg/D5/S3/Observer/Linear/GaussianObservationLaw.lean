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
register_information_theorem _root_.D5.S3.Observer.Linear.GaussianObservationLaw.gaussian_observation_law in arena
  readout via (realize signature
    (fun _ q z => by
      letI := q.finiteN
      letI := q.decN
      letI := q.finiteP
      letI := q.decP
      exact (action (observation q.matrix) z, action (signal (n := q.n) (p := q.p)) z)) emptyAnchor)
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Linear.GaussianObservationLaw,
    coordinates := #[0,1,6,7,8],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "body"],
      stateOperand := some #["arg","arg"] }] })
  escape continues (open)
end Reg.D5.S3.Observer.Linear.GaussianObservationLaw
