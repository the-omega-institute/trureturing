import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity

/-! Source-bound readout of the rank-one BKM active block classification. -/

noncomputable section

universe u
open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceLeft)
open _root_.D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (lift bkmGap)
open _root_.D5.S3.Quantum.Recovery.BKMObservableProductRigidity
  (relativeDensity bkmGap_eq_zero_iff_eq_marginals_kronecker)
open _root_.D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity

namespace Reg.D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def gapEquality : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejectEquality : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature gapEquality := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  change ((0 : ℝ) = 1) = ((1 : ℝ) = 1) at he
  exact zero_ne_one (he.mpr rfl)

private abbrev Singleton := ULift.{u} Unit

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) (_htrace : A.trace = 1)
    (w : R → ℂ) (_hw : star w ⬝ᵥ w = 1),
    let P := activeProjection (partialTraceRight_posDef A hA).isHermitian w
    let Q := 1 - P
    let B := relativeDensity A
    r.readout () () (bkmGap A (vecMulVec w (star w))) 0 ↔
      ∃! T : Matrix E E ℂ, T.PosDef ∧ T.trace = 1 ∧
        B = P ⊗ₖ T + lift Q * B * lift Q ∧
        partialTraceRight (lift Q * B * lift Q) = Q ∧
        ∀ x : R × E → ℂ, x ≠ 0 → lift Q *ᵥ x = x →
          0 < star x ⬝ᵥ ((lift Q * B * lift Q) *ᵥ x)

private theorem rejected : ¬ arena.{u}.Law rejectEquality := by
  intro h
  let A : Matrix (Singleton.{u} × Singleton.{u}) (Singleton.{u} × Singleton.{u}) ℂ := 1
  let w : Singleton.{u} → ℂ := fun _ => 1
  let K := vecMulVec w (star w)
  have hA : A.PosDef := Matrix.PosDef.one
  have ht : A.trace = 1 := by simp [A, Matrix.trace]
  have hw : star w ⬝ᵥ w = 1 := by simp [w, dotProduct]
  have hK : K.IsHermitian := by simp [K, Matrix.IsHermitian, Matrix.conjTranspose_vecMulVec]
  have connected (G : SimpleGraph Singleton.{u}) : G.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let o : Singleton.{u} := ⟨()⟩
    refine ⟨o, fun j => ?_⟩
    rw [Subsingleton.elim j o]
  have hz : bkmGap A K = 0 := by
    apply (bkmGap_eq_zero_iff_eq_marginals_kronecker A hA K hK ht
      (fun _ _ _ => Subsingleton.elim _ _) (connected _)).mpr
    ext ⟨i,e⟩ ⟨j,f⟩
    have hij : i = j := Subsingleton.elim _ _
    have hef : e = f := Subsingleton.elim _ _
    subst j
    subst f
    simp [A, partialTraceRight, partialTraceLeft]
  exact (h A hA ht w hw).mpr
    ((bkmGap_rankOne_eq_zero_iff_activeBlock A hA ht w hw).mp hz)

def family : Registration arena.{u} (type_of% @bkmGap_rankOne_eq_zero_iff_activeBlock.{u}) where
  actual := gapEquality
  bridge := Iff.rfl
  variation := ⟨@bkmGap_rankOne_eq_zero_iff_activeBlock.{u}, rejectEquality, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejectEquality, ?_, ?_, rejected⟩
      · intro other h
        cases role
        cases other
        exact (h rfl).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bkmGap_rankOne_eq_zero_iff_activeBlock.{u}) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity.bkmGap_rankOne_eq_zero_iff_activeBlock
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity
