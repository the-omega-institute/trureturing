import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Convexity.StrongConcavityAttainment
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Set Topology
open _root_.D5.S3.Analytic.Convexity.StrongConcavityAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.Convexity.StrongConcavityAttainment
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f : E → ℝ} {m : ℝ},
    s.Nonempty → IsComplete s → 0 < m → StrongConcaveOn s m f →
    UpperSemicontinuousOn f s → BddAbove (f '' s) →
    ∃ x ∈ s, IsMaxOn (fun z => R.readout () () (f z)) s x ∧
      (∀ y ∈ s, m / 4 * ‖y - x‖ ^ 2 ≤
        R.readout () () (f x) - R.readout () () (f y)) ∧
      ∀ y ∈ s, IsMaxOn (fun z => R.readout () () (f z)) s y → y = x

private theorem parabola_strong {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    StrongConcaveOn (Set.univ : Set E) 2 (fun x : E => -(‖x‖ ^ 2)) := by
  have heq : (fun x : E => -(‖x‖ ^ 2) + (2 : ℝ) / 2 * ‖x‖ ^ 2) =
      (fun _ : E => (0 : ℝ)) := by
    funext x
    ring
  rw [strongConcaveOn_iff_convex, heq]
  exact concaveOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  let e : E := EuclideanSpace.single (ULift.up ()) 1
  have hcont : Continuous (fun x : E => -(‖x‖ ^ 2)) := by fun_prop
  have hbdd : BddAbove ((fun x : E => -(‖x‖ ^ 2)) '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact neg_nonpos.mpr (sq_nonneg ‖x‖)
  obtain ⟨x, hx, hmax, hdeficit, huniq⟩ :=
    @h E _ _ Set.univ (fun x : E => -(‖x‖ ^ 2)) 2 Set.univ_nonempty
      isComplete_univ (by norm_num) parabola_strong
      hcont.continuousOn.upperSemicontinuousOn hbdd
  have hzero : IsMaxOn (fun z : E => rejected.readout () () (-(‖z‖ ^ 2)))
      Set.univ (x + e) := by
    intro y hy
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have heq := huniq (x + e) (Set.mem_univ _) hzero
  have he : e = 0 := add_left_cancel (heq.trans (add_zero x).symm)
  have hev := congrArg (fun z : E => z (ULift.up ())) he
  simp [E, e, EuclideanSpace.single] at hev

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

-- The positive law keeps the complete original telescope, including arbitrary E.
-- The failed constant readout refutes the law already on the real parabola.
def family : Registration arena.{u} (type_of% (@exists_unique_maximizer.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unique_maximizer.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_unique_maximizer.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Convexity.StrongConcavityAttainment.unit
  realizationName := `Reg.D5.S3.Analytic.Convexity.StrongConcavityAttainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Convexity.StrongConcavityAttainment
