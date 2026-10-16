import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
open _root_.D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
open _root_.D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix
set_option autoImplicit false
noncomputable section

private lemma bounds (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    defectSite r m + 1 < r * m := by
  have h : (m - 1) * r + r = r * m := by
    calc
      _ = ((m - 1) + 1) * r := by ring
      _ = m * r := by rw [Nat.sub_add_cancel (show 1 ≤ m by omega)]
      _ = _ := Nat.mul_comm _ _
  dsimp [defectSite]
  omega

abbrev signature : Signature where
  Params := {p : ℕ × ℕ // 3 ≤ p.1 ∧ 2 ≤ p.2}
  State p := Fin (p.val.1 * p.val.2) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p z => z ⟨defectSite p.val.1 p.val.2,
    by have := bounds p.val.1 p.val.2 p.property.1 p.property.2; omega⟩)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p z => z ⟨defectSite p.val.1 p.val.2 + 1,
    bounds p.val.1 p.val.2 p.property.1 p.property.2⟩)
  (fun e => nomatch e)

/-- The full source telescope is preserved; only the normalized node readout varies. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m),
    (∀ X : Matrix (Fin (r * m)) (Fin (r * m)) ℂ,
      Commute X (((SimpleGraph.cycleGraph (r * m)).lapMatrix ℝ).map Complex.ofReal) →
      Commute X ((Matrix.diagonal (signWord (K := ℝ) r m)).map Complex.ofReal) →
      ∃ c : ℂ, X = c • (1 : Matrix (Fin (r * m)) (Fin (r * m)) ℂ)) ∧
    (∀ O : Matrix (Fin (r * m)) (Fin (r * m)) ℝ,
      O ∈ Matrix.orthogonalGroup (Fin (r * m)) ℝ →
      Commute O ((SimpleGraph.cycleGraph (r * m)).lapMatrix ℝ) →
      Commute O (Matrix.diagonal (signWord r m)) → O = 1 ∨ O = -1) ∧
    (3 ≤ m →
      D5.S3.Combinatorics.Graph.AndersonSymmetryConverseRefutation.bad
        (signWord (K := ℝ) r m) ∧
      (∀ t : ℝ, ∃ (μ : ℝ) (z : Fin (r * m) → ℝ),
        z ≠ 0 ∧ hamiltonian r m t *ᵥ z = μ • z ∧
        R.readout () ⟨(r,m),hr,hm⟩ z = 0 ∧
        z ⟨defectSite r m + 1, by have := bounds r m hr hm; omega⟩ = 1) ∧
      (nodeFactor r m hr hm
        (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X)).Monic ∧
      ∃ G : Polynomial (Polynomial ℝ), G.Monic ∧
        G.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) =
          nodeFactor r m hr hm (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) ∧
        G ∣ (hamiltonian r m (Polynomial.X : Polynomial ℝ)).charpoly ∧
        G ∣ (deleted r m (Polynomial.X : Polynomial ℝ)
          ⟨defectSite r m, by have := bounds r m hr hm; omega⟩).charpoly ∧
        (∀ t : ℝ, (G.map (Polynomial.evalRingHom t)).Monic ∧
          G.map (Polynomial.evalRingHom t) ∣ (hamiltonian r m t).charpoly ∧
          G.map (Polynomial.evalRingHom t) ∣ (deleted r m t
            ⟨defectSite r m, by have := bounds r m hr hm; omega⟩).charpoly) ∧
        (∃ F : Polynomial (Polynomial ℝ), F.Monic ∧ 0 < F.natDegree ∧ F ∣ G) ∧
        ∀ π : Polynomial (RatFunc ℝ), π.Monic → Irreducible π →
          π ∣ traceFactors r m (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) →
          π ∣ nodeFactor r m hr hm (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) ∧
          ∃ Fπ : Polynomial (Polynomial ℝ), Fπ.Monic ∧
            Fπ.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) = π ∧ Fπ ∣ G ∧
            ∀ t : ℝ, (Fπ.map (Polynomial.evalRingHom t)).Monic ∧
              Fπ.map (Polynomial.evalRingHom t) ∣ (hamiltonian r m t).charpoly ∧
              Fπ.map (Polynomial.evalRingHom t) ∣ (deleted r m t
                ⟨defectSite r m, by have := bounds r m hr hm; omega⟩).charpoly)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨μ,z,hz,he,hq,hn⟩ := ((h 3 3 (by omega) (by omega)).2.2 (by omega)).2.1 0
  change z ⟨8, by omega⟩ = 0 at hq
  change z ⟨8, by omega⟩ = 1 at hn
  exact zero_ne_one (hq.symm.trans hn)

def source_registration : Registration arena (type_of% @defect_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨defect_family,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(3,3),by omega,by omega⟩,(fun _ => 0),(fun _ => 1),?_⟩
    intro he
    change (0 : ℝ) = 1 at he
    exact zero_ne_one he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@defect_family) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p z => z ⟨defectSite p.val.1 p.val.2,
      by have := bounds p.val.1 p.val.2 p.property.1 p.property.2; omega⟩)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body","body","body","body","arg","arg","body",
        "arg","fn","arg","body","arg","body","arg","body",
        "arg","arg","fn","arg","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
