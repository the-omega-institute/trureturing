import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation

noncomputable section

namespace Reg.D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation

abbrev signature : Signature where
  Params := (u : ℕ) × (v : ℕ) × (m : ℝ) × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => sharpValue p.1 p.2.1 p.2.2.1 p.2.2.2 t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete source telescope and all five attaining implications are retained. -/
def arena : Arena where
  signature := signature
  Law obs := ∀ (u v : ℕ) (_hu : 1 ≤ u) (_huv : u < v)
    (m s t : ℝ) (_hm : 0 < m) (_hst : s < t),
    IsLeast (distances u v m s t) (obs.readout () ⟨u, v, m, s⟩ t) ∧
    (s ≤ -(v : ℝ) / 2 → -(v : ℝ) / 2 ≤ t → Attains u v m s t m m) ∧
    (-(v : ℝ) / 2 < s → s + v / 2 ≤ ((v : ℝ) - u) / 2 →
      Attains u v m s t (m * (1 + (t - s) * (2 / (u + 2 * (s + v / 2))))) m) ∧
    (-(v : ℝ) / 2 < s → ((v : ℝ) - u) / 2 ≤ s + v / 2 →
      Attains u v m s t (m * (1 + (t - s) * (1 / (s + v / 2)))) m) ∧
    (t < -(v : ℝ) / 2 → -t - v / 2 ≤ (u : ℝ) / 2 →
      Attains u v m s t m (m * (1 + (t - s) * (2 / ((v : ℝ) - u + 2 * (-t - v / 2)))))) ∧
    (t < -(v : ℝ) / 2 → (u : ℝ) / 2 ≤ -t - v / 2 →
      Attains u v m s t m (m * (1 + (t - s) * (1 / (-t - v / 2)))))

theorem positiveLaw : arena.Law actual := @quadratic_three_index_separation

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have good := (quadratic_three_index_separation 1 3 (by norm_num) (by norm_num)
    1 0 1 (by norm_num) (by norm_num)).1
  have bad := (h 1 3 (by norm_num) (by norm_num) 1 0 1 (by norm_num) (by norm_num)).1.1
  have bound := good.2 bad
  norm_num [sharpValue, kRight, kLeft, rejected, realize] at bound

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (@Subsingleton.elim Unit _ j i)).elim
  · intro e
    exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 3, 1, 0⟩, 0, 1, ?_⟩
  norm_num [actual, realize, sharpValue, kRight, kLeft]

def registration : Registration arena (arena.Law actual) :=
  Registration.mk actual Iff.rfl ⟨positiveLaw, rejected, rejected_law⟩ sensitivity dependence

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quadratic_three_index_separation)
    (type_of% (realize signature
      (fun _ p t => sharpValue p.1 p.2.1 p.2.2.1 p.2.2.2 t) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation.quadratic_three_index_separation.__information_unit
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p t => sharpValue p.1 p.2.1 p.2.2.1 p.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Observer.MetricGeometry.QuadraticThreeIndexSeparation
