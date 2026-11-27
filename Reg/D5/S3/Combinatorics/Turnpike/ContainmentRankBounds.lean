import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Turnpike.ContainmentRankBounds
import Mathlib.Data.Fin.VecNotation

namespace Reg.D5.S3.Combinatorics.Turnpike.ContainmentRankBounds
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Omega.Turnpike
open scoped BigOperators
noncomputable section

/-- All point counts and all original intervals form the observation domain. -/
def signature : DependentFamily.Signature where
  Params := ℕ
  State := Interval
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ n e => (e.1.1.val + 1) * (n - e.1.2.val)) (fun e => nomatch e)

/-- The full original telescope; only the lower-bound arithmetic occurrence varies. -/
def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {n d : ℕ} {y : Fin d → ℝ} {mu : Fin d → ℕ} {x : Fin n → ℝ}
    (_hy : StrictAnti y) (_hx : Realizes y mu x)
    (e : Interval n) (q : Fin d) (_heq : x e.1.2 - x e.1.1 = y q),
    R.readout () n e ≤ (∑ r ∈ Finset.univ.filter (· < q), mu r) + 1 ∧
    (∑ r ∈ Finset.univ.filter (· ≤ q), mu r) ≤
      n.choose 2 - (e.1.2.val - e.1.1.val + 1).choose 2 + 1 ∧ RankAllowed mu e q

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Combinatorics.Turnpike.ContainmentRankBounds.containment_rank_bounds)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem actual_positive : arena.Law actual :=
  @_root_.D5.S3.Combinatorics.Turnpike.ContainmentRankBounds.containment_rank_bounds

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem fixture :
    Realizes (![2,1,-1] : Fin 3 → ℝ) (![0,1,0] : Fin 3 → ℕ)
      (![0,1] : Fin 2 → ℝ) := by
  classical
  have hu : (Finset.univ : Finset (Interval 2)) = {⟨(0,1),by decide⟩} := by
    ext ⟨⟨i,j⟩,h⟩
    fin_cases i <;> fin_cases j <;> norm_num at h
    all_goals simp
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro ⟨⟨i,j⟩,h⟩
    fin_cases i <;> fin_cases j <;> norm_num at h
    all_goals exact ⟨1,by norm_num⟩
  · intro q
    fin_cases q <;> norm_num [hu,Finset.filter_singleton]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hy : StrictAnti (![2,1,-1] : Fin 3 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals norm_num
  have bad := (h hy fixture (⟨(0,1),by decide⟩ : Interval 2) 1 (by norm_num)).1
  norm_num [rejected,DependentFamily.realize] at bad

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨3, (⟨(0,1),by decide⟩ : Interval 3), ⟨(0,2),by decide⟩, ?_⟩
  norm_num [actual,DependentFamily.realize]

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.Turnpike.ContainmentRankBounds.containment_rank_bounds)
      (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Turnpike.ContainmentRankBounds.containment_rank_bounds.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Turnpike.ContainmentRankBounds.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ n e => (e.1.1.val + 1) * (n - e.1.2.val)) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Turnpike.ContainmentRankBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "fn","arg","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Turnpike.ContainmentRankBounds
