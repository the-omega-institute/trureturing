import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Riemannian.GradientDissipation
/-! Source-bound whole-family audits for actual Riemannian curves and their readouts. -/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle Topology ContDiff ENNReal NNReal InnerProductSpace
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Original172
noncomputable section
universe u v
local notation "IR" => 𝓘(ℝ, ℝ)
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Reg.D5.S3.Geometry.Riemannian.GradientDissipation
namespace ZeroGeometry
abbrev E0 := PUnit.{u+1}
abbrev M0 := PUnit.{v+1}
instance : ChartedSpace E0 M0 := ChartedSpace.ofDiscreteTopology
instance (p : M0) : Subsingleton (TangentSpace 𝓘(ℝ, E0) p) := by
  change Subsingleton E0
  infer_instance
instance : IsManifold 𝓘(ℝ, E0) ∞ M0 := IsManifold.of_discreteTopology ∞
noncomputable def metric : Bundle.RiemannianMetric
    (TangentSpace 𝓘(ℝ, E0) : M0 → Type _) where
  inner _ := 0
  symm _ _ _ := rfl
  pos _ w hw := (hw (Subsingleton.elim w 0)).elim
  continuousAt _ := continuous_const.continuousAt
  isVonNBounded _ := Bornology.IsVonNBounded.of_subsingleton
noncomputable instance : RiemannianBundle
    (TangentSpace 𝓘(ℝ, E0) : M0 → Type _) := ⟨metric⟩
instance : IsContinuousRiemannianBundle E0
    (TangentSpace 𝓘(ℝ, E0) : M0 → Type _) := by
  refine ⟨fun _ => 0, continuous_of_discreteTopology, ?_⟩
  intro p w v
  have hw : w = 0 := Subsingleton.elim _ _
  rw [hw]
  simp
end ZeroGeometry



namespace Dissipation
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ (s : ℝ) (n : ℕ) => s ^ n) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [hT2 : T2Space M] [hConnected : ConnectedSpace M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)],
∀ {T : ℝ} (hT : 0 < T) (V : M → ℝ) (x : ℝ → M)
    (hV : ContMDiff 𝓘(ℝ, E) IR 1 V)
    (hx : ContMDiffOn IR 𝓘(ℝ, E) 1 x (Icc (0 : ℝ) T))
    (hflow : ∀ t ∈ Icc (0 : ℝ) T,
      mfderivWithin IR 𝓘(ℝ, E) x (Icc (0 : ℝ) T) t 1 = -actualGradient V (x t)),
    IntervalIntegrable (fun t => ‖mfderiv IR 𝓘(ℝ, E) x t 1‖) volume 0 T ∧
    IntervalIntegrable (fun t => ‖mfderiv IR 𝓘(ℝ, E) x t 1‖ ^ 2) volume 0 T ∧
    V (x 0) - V (x T) = ∫ t in (0 : ℝ)..T, R.readout () () ‖mfderiv IR 𝓘(ℝ, E) x t 1‖ 2

theorem bad_law : ¬ arena.{u,v}.Law bad := by
  intro h
  let E := ZeroGeometry.E0.{u}
  let M := ZeroGeometry.M0.{v}
  let z : ℝ → M := fun _ => PUnit.unit
  have hV : ContMDiff 𝓘(ℝ, E) IR 1 (fun _ : M => (0 : ℝ)) := contMDiff_const
  have hz : ContMDiffOn IR 𝓘(ℝ, E) 1 z (Icc (0 : ℝ) 1) := contMDiff_const.contMDiffOn
  have hf : ∀ t ∈ Icc (0 : ℝ) 1,
      mfderivWithin IR 𝓘(ℝ, E) z (Icc (0 : ℝ) 1) t 1 =
        -actualGradient (fun _ : M => (0 : ℝ)) (z t) := by
    intro t ht
    exact Subsingleton.elim _ _
  have hs := h (E := E) (M := M) (T := 1) (by norm_num)
    (fun _ => 0) z hV hz hf
  norm_num [bad, realize] at hs

def evidence : Registration arena (type_of% (@Original172.S2_dissipation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(@Original172.S2_dissipation), bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h2 := congrFun h 2
    norm_num [actual, realize] at h2

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Original172.S2_dissipation) (type_of% (realize signature (fun _ _ (s : ℝ) (n : ℕ) => s ^ n) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Riemannian.GradientDissipation.Dissipation.__information_unit,
  realizationName := `Reg.D5.S3.Geometry.Riemannian.GradientDissipation.Dissipation.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ (s : ℝ) (n : ℕ) => s ^ n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Riemannian.GradientDissipation,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "fn", "fn", "arg", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms registration
end Dissipation

end Reg.D5.S3.Geometry.Riemannian.GradientDissipation
