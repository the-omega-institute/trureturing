import D5.S3.Geometry.Hyperideal.PolarCoefficientPolytope
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Hyperideal.PolarCoefficientPolytope
open _root_.D5.S3.Geometry.Hyperideal.PolarCoefficientPolytope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

/-- The matrix parameters and coefficient vectors vary over their full real domains. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 4 → Fin 4 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Coeff
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ G => (polytope G).extremePoints ℝ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

/-- Intervention replaces only the extreme-point predicate; all original conclusions remain. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (G : Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, G i i = 1) (ho : ∀ i j, i ≠ j → G i j < -1)
    (hs : ∀ i j, G i j = G j i),
    R.readout () () G = endpoints G ∧
    ((∀ i j, i≠j → endpoint G i j∈polytope G ∧
      (∀ k,row G (endpoint G i j) k=0 ↔ k=i) ∧
      (∀ k,k≠i → row G (endpoint G i j) k<0) ∧
      (∀ k,endpoint G i j k=0 ↔ k≠i ∧ k≠j)) ∧
      (∀ i j k l,i≠j → k≠l → endpoint G i j=endpoint G k l → i=k ∧ j=l)) ∧
    (∀ S T : Finset (Fin 4), supportingFace G S T=convexHull ℝ
      {a | ∃ i j,i≠j ∧ (∀ h∈S,h≠i ∧ h≠j) ∧ (∀ k∈T,k=i) ∧ a=endpoint G i j})

private def witnessMatrix (i j : Fin 4) : ℝ := if i=j then 1 else -2

private theorem witness_diagonal : ∀ i, witnessMatrix i i=1 := by
  intro i; simp [witnessMatrix]

private theorem witness_offdiag : ∀ i j, i≠j → witnessMatrix i j < -1 := by
  intro i j hij; simp [witnessMatrix,hij]

private theorem witness_symmetric : ∀ i j, witnessMatrix i j=witnessMatrix j i := by
  intro i j; simp [witnessMatrix,eq_comm]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h witnessMatrix witness_diagonal witness_offdiag witness_symmetric).1
  have hm : endpoint witnessMatrix 0 1 ∈ endpoints witnessMatrix := ⟨0,1,by decide,rfl⟩
  rw [←he] at hm
  exact hm

private theorem dependence_proof : ObservationalDependence signature actual := by
  intro r
  let M : Fin 4 → Fin 4 → ℝ := fun i j => if i=j then 1 else -3
  have hd : ∀ i, M i i=1 := by intro i; simp [M]
  have ho : ∀ i j, i≠j → M i j < -1 := by intro i j hij; simp [M,hij]
  have hs : ∀ i j, M i j=M j i := by intro i j; simp [M,eq_comm]
  have h := marked_coefficient_classification witnessMatrix
    witness_diagonal witness_offdiag witness_symmetric
  have hM := marked_coefficient_classification M hd ho hs
  have hgood : endpoint witnessMatrix 0 1 ∈ (polytope witnessMatrix).extremePoints ℝ := by
    rw [h.1]; exact ⟨0,1,by decide,rfl⟩
  have hrows : ∀ k, row M (endpoint witnessMatrix 0 1) k < 0 := by
    intro k
    fin_cases k <;> norm_num [row,endpoint,witnessMatrix,M,Fin.sum_univ_four]
  have hbad : endpoint witnessMatrix 0 1 ∉ (polytope M).extremePoints ℝ := by
    intro he
    rw [hM.1] at he
    obtain ⟨i,j,hij,he⟩ := he
    have hz := (hM.2.1.1 i j hij).2.1 i |>.mpr rfl
    rw [←he] at hz
    linarith [hrows i]
  refine ⟨(),witnessMatrix,M,?_⟩
  change (polytope witnessMatrix).extremePoints ℝ ≠ (polytope M).extremePoints ℝ
  intro he
  exact hbad (he ▸ hgood)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨marked_coefficient_classification,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := dependence_proof

register_information_theorem marked_coefficient_classification in arena
  readout via (realize signature
    (fun _ _ G => (polytope G).extremePoints ℝ) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.PolarCoefficientPolytope
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Geometry.Hyperideal.PolarCoefficientPolytope
