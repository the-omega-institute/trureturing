import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer
import Reg.Support.DependentFamily

/-! Source-bound audit of the transfer-time coordinate for blow-ups with clone matchings. -/

namespace Reg.D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer

open _root_.D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer
open _root_.D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
  (HasPST hamiltonianPropagator_neg)
open _root_.D5.S3.Zeros.Convolution.PerfectMatchingCount (FixedPointFreeInvolution)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The division by two in the transfer time is observed as a real-valued coordinate. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x / 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- All graph, matching, spectral support and divisibility hypotheses remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (m n : ℕ) (g : SimpleGraph (Fin m)) [DecidableRel g.Adj]
    (v : Fin m) (ρ : FixedPointFreeInvolution (Fin n)) (_hv : IntegralSupport g v)
    (_hn : 4 ∣ n) (j : Fin n),
    HasPST (blowUpMatching g n ρ.val) (r.readout () () Real.pi) (v, j) (v, ρ.val j)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let ρ : FixedPointFreeInvolution (Fin 4) :=
    ⟨Fin.revPerm, Fin.rev_involutive, by decide⟩
  have hv : IntegralSupport (⊥ : SimpleGraph (Fin 1)) 0 := by
    intro l x hx hne
    refine ⟨0, ?_⟩
    have he := congrFun hx 0
    simp only [SimpleGraph.adjMatrix_bot, Matrix.zero_mulVec, Pi.zero_apply,
      Pi.smul_apply, smul_eq_mul] at he
    have hl : (l : ℂ) = 0 := (mul_eq_zero.mp he.symm).resolve_right hne
    exact_mod_cast hl
  have he := h 1 4 ⊥ 0 ρ hv (by decide) 0
  change HasPST (blowUpMatching (⊥ : SimpleGraph (Fin 1)) 4 ρ.val)
    0 (0, 0) (0, ρ.val 0) at he
  have hne : (0, (0 : Fin 4)) ≠ ((0 : Fin 1), ρ.val 0) := by decide
  unfold HasPST at he
  rw [hamiltonianPropagator_neg] at he
  simp [hne] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer
