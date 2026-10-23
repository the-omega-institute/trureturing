import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.PhysicalHeatGenerator
import Reg.Support.DependentFamily

set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory SchwartzMap
open scoped Topology ENNReal NNReal InnerProductSpace ComplexConjugate lp
open D5.S3.Quantum.Analysis.SchwartzCutoffGraph
open D5.S3.Quantum.Analysis.SchwartzWeakAdjoint
open D5.S3.Quantum.Analysis.Hermite.PhysicalProductTotality
open D5.S3.Quantum.Analysis.PhysicalHeatGenerator
open MarkovProcess.Semigroup
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Analysis.PhysicalHeatGenerator

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature (fun _ _ x => Real.exp x) (fun a => nomatch a)
def rejected := realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law := fun obs => ∀ (d : ℕ) (h : ℝ) (m w : Fin d → ℝ)
    (hh : 0 < h) (hm : ∀ j, 0 < m j) (hw : ∀ j, 0 < w j),
    let K := (schwartzOperator d (fun j => h^2/(2*m j)) (fun j => m j*w j^2/2)).closure
    let E := fun n : Fin d → ℕ => ∑ j, h*w j*((n j : ℝ)+1/2)
    ∃ (e : HilbertBasis (Fin d → ℕ) ℂ (Hilbert d))
      (T : ℝ≥0 → Hilbert d →L[ℂ] Hilbert d)
      (S : StronglyContinuousContractionSemigroup (Hilbert d)),
      (∀ n, (e n : Space d → ℂ) =ᵐ[volume] physicalHermite d h m w n) ∧
      (∀ t, S t = (T t).restrictScalars ℝ) ∧
      (∀ t f n, e.repr (T t f) n = (obs.readout () () (-(t : ℝ)*E n) : ℂ)*e.repr f n) ∧
      (∀ t, (T t).IsPositive) ∧
      (∀ f v : Hilbert d,
        Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t f-f)) (𝓝[>] 0) (𝓝 v) ↔
          (f,-v) ∈ K.graph) ∧
      (∀ R : StronglyContinuousContractionSemigroup (Hilbert d),
        (∀ f v, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t f-f))
          (𝓝[>] 0) (𝓝 v) ↔ (f,-v) ∈ K.graph) → R = S) ∧
      ((∀ n, E n = 0) → ∀ t, T t = ContinuousLinearMap.id ℂ (Hilbert d))

theorem actual_law : arena.Law actual := physical_heat_generator

theorem rejected_law : ¬ arena.Law rejected := by
  intro hb
  obtain ⟨e,T,S,hphys,hrestrict,hcoeff,hpos,hgraph,huniq,hzero⟩ :=
    hb 0 1 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (by norm_num) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
  let n : Fin 0 → ℕ := fun j => Fin.elim0 j
  have hT : T 0 (e n) = e n := by
    have h := DFunLike.congr_fun (hrestrict 0) (e n)
    simpa only [S.zero_apply,ContinuousLinearMap.coe_restrictScalars'] using h.symm
  have hc := hcoeff 0 (e n) n
  rw [hT,e.repr_self] at hc
  simpa [rejected,realize,lp.single_apply] using hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change Real.exp 0 ≠ Real.exp 1
  exact Real.exp_injective.ne (by norm_num)

def family : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := dependence

-- The observation is the real exponential in the heat multiplier; the law
-- retains the original physical parameters and full generator characterization.
def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Quantum.Analysis.PhysicalHeatGenerator.physical_heat_generator)
    (type_of% (realize signature (fun _ _ x => Real.exp x) (fun a => nomatch a)))
    Unit Unit := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Analysis") "PhysicalHeatGenerator") "physical_heat_generator") "Reg.D5.S3.Quantum.Analysis.PhysicalHeatGenerator/Reg.D5.S3.Quantum.Analysis.PhysicalHeatGenerator.arena/[anonymous]") "__information_unit")
  realizationName := `Reg.D5.S3.Quantum.Analysis.PhysicalHeatGenerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.exp x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.PhysicalHeatGenerator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "body",
        "body", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Analysis.PhysicalHeatGenerator
