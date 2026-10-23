import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.ContractionSemigroup
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter
open scoped Topology NNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.ContractionSemigroup.Slope

/-- The source ranges over arbitrary real normed spaces, without completeness. -/
structure NormedInput where
  E : Type u
  [normed : NormedAddCommGroup E]
  [realSpace : NormedSpace ℝ E]
attribute [instance] NormedInput.normed NormedInput.realSpace

abbrev signature : Signature where
  Params := NormedInput.{u}
  State p := p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => 0) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {F' : E} {a : ℝ} (hF : HasDerivAt F F' a),
    Tendsto (fun h : NNReal => (h : ℝ)⁻¹ • (F (a + h) - F a))
      (𝓝[>] 0) (𝓝 (R.readout () ⟨E⟩ F'))

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_slope_add_of_hasDerivAt.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K := EuclideanSpace ℝ (ULift.{u} Unit)
  let v : K := EuclideanSpace.single ⟨()⟩ 1
  have hd : HasDerivAt (fun s : ℝ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hbad := h (E := K) hd
  have hgood :=
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_slope_add_of_hasDerivAt hd
  have hz : v = (0 : K) := tendsto_nhds_unique hgood hbad
  have he := congrArg (fun x : K => x (⟨()⟩ : ULift.{u} Unit)) hz
  have hn : (1 : ℝ) = 0 := by
    simpa only [v, EuclideanSpace.single, PiLp.zero_apply, PiLp.single_eq_same] using he
  exact one_ne_zero hn

def family : Registration arena.{u}
    (type_of% (@MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_slope_add_of_hasDerivAt.{u})) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    let K := EuclideanSpace ℝ (ULift.{u} Unit)
    let v : K := EuclideanSpace.single ⟨()⟩ 1
    refine ⟨(⟨K⟩ : NormedInput.{u}), (0 : K), v, ?_⟩
    intro h
    have hz : (0 : K) = v := by simpa [actual, realize] using h
    have he := congrArg (fun x : K => x (⟨()⟩ : ULift.{u} Unit)) hz
    have hn : (0 : ℝ) = 1 := by
      simpa only [v, EuclideanSpace.single, PiLp.zero_apply, PiLp.single_eq_same] using he
    exact zero_ne_one hn

-- The positive law and equivalence retain the complete original telescope.
-- The whole-family zero intervention has a genuine nonzero-derivative witness.
-- Raw source selection/reconstruction is not supplied: this is an audit attempt,
-- not a claim of a declared_validated four-slot registration.
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_slope_add_of_hasDerivAt.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.ContractionSemigroup.Slope.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.ContractionSemigroup.Slope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Analysis.ContractionSemigroup.Slope
