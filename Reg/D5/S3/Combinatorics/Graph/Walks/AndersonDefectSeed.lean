import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
open _root_.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
noncomputable section

abbrev boundSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def boundActual : Realization boundSignature := realize boundSignature
  (fun _ m r => defectSite r m + 1) (fun e => nomatch e)
def boundRejected : Realization boundSignature := realize boundSignature
  (fun _ m r => r * m) (fun e => nomatch e)
abbrev boundArena : Arena where
  signature := boundSignature
  Law R := ∀ (r m : ℕ), 3 ≤ r → 2 ≤ m → R.readout () m r < r * m
private theorem boundRejectedFails : ¬ boundArena.Law boundRejected := by
  intro h
  have hh := h 3 2 (by omega) (by omega)
  change 3 * 2 < 3 * 2 at hh
  exact (Nat.lt_irrefl _) hh

def boundSource : Registration boundArena (type_of% @defect_bounds) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨defect_bounds,boundRejected,boundRejectedFails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨boundRejected,?_,rfl,boundRejectedFails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨2,3,4,?_⟩
    norm_num [boundActual,realize,defectSite]

abbrev seedSignature : Signature where
  Params := {p : ℕ × ℕ // 3 ≤ p.1 ∧ 2 ≤ p.2}
  State p := Set (Matrix (Fin (p.val.1 * p.val.2)) (Fin (p.val.1 * p.val.2)) ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Subalgebra ℝ (Matrix (Fin (p.val.1 * p.val.2)) (Fin (p.val.1 * p.val.2)) ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def seedActual : Realization seedSignature := realize seedSignature
  (fun _ _ S => Algebra.adjoin ℝ S) (fun e => nomatch e)
def seedRejected : Realization seedSignature := realize seedSignature
  (fun _ _ _ => ⊥) (fun e => nomatch e)
abbrev seedArena : Arena where
  signature := seedSignature
  Law R := ∀ (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m),
    ∃ j : Fin (r*m),
      Matrix.single j j (1 : ℝ) ∈ R.readout () ⟨(r,m),hr,hm⟩
        {(SimpleGraph.cycleGraph (r*m)).lapMatrix ℝ, Matrix.diagonal (signWord r m)} ∧
      Matrix.single (j + ⟨1, by have := defect_bounds r m hr hm; omega⟩)
        (j + ⟨1, by have := defect_bounds r m hr hm; omega⟩) (1 : ℝ) ∈
        R.readout () ⟨(r,m),hr,hm⟩
          {(SimpleGraph.cycleGraph (r*m)).lapMatrix ℝ, Matrix.diagonal (signWord r m)}

private theorem single_not_bot (j : Fin 6) :
    Matrix.single j j (1 : ℝ) ∉ (⊥ : Subalgebra ℝ (Matrix (Fin 6) (Fin 6) ℝ)) := by
  intro h
  obtain ⟨c,hc⟩ := Algebra.mem_bot.mp h
  obtain ⟨k,hk⟩ := exists_ne j
  have h1 := congrFun (congrFun hc j) j
  have h0 := congrFun (congrFun hc k) k
  simp [Matrix.algebraMap_eq_diagonal,Matrix.single,Matrix.diagonal] at h1
  simp [Matrix.algebraMap_eq_diagonal,Matrix.single,Matrix.diagonal,hk,hk.symm] at h0
  exact zero_ne_one (h0.symm.trans h1)

private theorem seedRejectedFails : ¬ seedArena.Law seedRejected := by
  intro h
  obtain ⟨j,hj,_⟩ := h 3 2 (by omega) (by omega)
  exact single_not_bot j hj

def seedSource : Registration seedArena (type_of% @defect_diagonal_seed) where
  actual := seedActual
  bridge := Iff.rfl
  variation := ⟨defect_diagonal_seed,seedRejected,seedRejectedFails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seedRejected,?_,rfl,seedRejectedFails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(3,2),by omega,by omega⟩,∅,Set.univ,?_⟩
    intro h
    change Algebra.adjoin ℝ (∅ : Set (Matrix (Fin 6) (Fin 6) ℝ)) = Algebra.adjoin ℝ Set.univ at h
    simp only [Algebra.adjoin_empty, Algebra.adjoin_univ] at h
    have hh : Matrix.single (0 : Fin 6) 0 (1 : ℝ) ∈
        (⊥ : Subalgebra ℝ (Matrix (Fin 6) (Fin 6) ℝ)) := by rw [h]; trivial
    exact single_not_bot 0 hh

def boundRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@defect_bounds) (Realization boundSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed.boundUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed.boundSource
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena ⟨boundSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ m r => defectSite r m + 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def seedRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@defect_diagonal_seed) (Realization seedSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed.seedUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed.seedSource
  realizationSource := none
  generated := false
  arena := .source ⟨seedArena⟩
  objectArena := .source ⟨seedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source seedArena ⟨seedSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seedSignature (fun _ _ S => Algebra.adjoin ℝ S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
