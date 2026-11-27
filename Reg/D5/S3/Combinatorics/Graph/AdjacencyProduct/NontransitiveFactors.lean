import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors
import Reg.Support.SingleDependentReadout

/-! The target-matrix readout in the order-17 adjacency factorization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors

open _root_.D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph

abbrev IntegerMatrix := Matrix (Fin 17) (Fin 17) ℤ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => IntegerMatrix) (fun _ => IntegerMatrix)

def actual : Realization signature :=
  realize signature (fun _ _ A => A - 1) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Matrix.of (-1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∃ H K : SimpleGraph (Fin 17),
      ∃ (dH : DecidableRel H.Adj) (dK : DecidableRel K.Adj),
        letI : DecidableRel H.Adj := dH
        letI : DecidableRel K.Adj := dK
        H.adjMatrix ℤ * K.adjMatrix ℤ = R.readout () () (Matrix.of 1) ∧
        (¬ ∀ i j, ∃ e : H ≃g H, e i = j) ∧
        (¬ ∀ i j, ∃ e : K ≃g K, e i = j)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨H, K, dH, dK, h, _, _⟩
  letI : DecidableRel H.Adj := dH
  letI : DecidableRel K.Adj := dK
  have h00 : (H.adjMatrix ℤ * K.adjMatrix ℤ) 0 0 = -1 :=
    congrFun (congrFun h (0 : Fin 17)) (0 : Fin 17)
  have hnonneg (G : SimpleGraph (Fin 17)) [DecidableRel G.Adj] (i j : Fin 17) :
      0 ≤ G.adjMatrix ℤ i j := by
    rw [adjMatrix_apply]
    split <;> decide
  have hpos : 0 ≤ (H.adjMatrix ℤ * K.adjMatrix ℤ) 0 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hnonneg H 0 j) (hnonneg K j 0)
  rw [h00] at hpos
  exact (by decide : ¬ (0 : ℤ) ≤ -1) hpos

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), Matrix.of 1, 0, ?_⟩
    intro h
    have h00 := congrFun (congrFun h (0 : Fin 17)) (0 : Fin 17)
    change (0 : ℤ) = -1 at h00
    exact (by decide : (0 : ℤ) ≠ -1) h00

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.AdjacencyProduct.NontransitiveFactors
