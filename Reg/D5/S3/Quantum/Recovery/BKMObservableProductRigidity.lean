import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Recovery.BKMObservableProductRigidity

/-! Source-bound readouts of the BKM equality criteria and ratio-piece identities. -/

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

namespace Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity

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

namespace Grouped

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) (K : Matrix R R ℂ) (_hK : K.IsHermitian),
    r.readout () () (bkmGap A K) 0 ↔ ∀ v : ℝ, Commute (relativeDensity A)
      (lift (modularPiece (partialTraceRight_posDef A hA).isHermitian v K))

private theorem rejected : ¬ arena.{u}.Law rejectEquality := by
  intro h
  let A : Matrix (Singleton.{u} × Singleton.{u}) (Singleton.{u} × Singleton.{u}) ℂ := 1
  let K : Matrix Singleton.{u} Singleton.{u} ℂ := 0
  have hz : bkmGap A K = 0 := by simp [bkmGap, K, lift]
  have hA : A.PosDef := Matrix.PosDef.one
  have hK : K.IsHermitian := Matrix.isHermitian_zero
  exact (h A hA K hK).mpr ((bkmGap_eq_zero_iff_commute_ratioPieces A hA K hK).mp hz)

def family : Registration arena.{u} (type_of% @bkmGap_eq_zero_iff_commute_ratioPieces.{u}) where
  actual := gapEquality
  bridge := Iff.rfl
  variation := ⟨@bkmGap_eq_zero_iff_commute_ratioPieces.{u}, rejectEquality, rejected⟩
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
    (@bkmGap_eq_zero_iff_commute_ratioPieces.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMObservableProductRigidity.bkmGap_eq_zero_iff_commute_ratioPieces.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity.Grouped.family
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
    owner := `D5.S3.Quantum.Recovery.BKMObservableProductRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Grouped

namespace Product

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) (K : Matrix R R ℂ) (hK : K.IsHermitian),
    ∀ (_htrace : A.trace = 1),
    let S := partialTraceRight A
    let hS := partialTraceRight_posDef A hA
    let U : Matrix R R ℂ := hS.isHermitian.eigenvectorUnitary
    let K₀ := Uᴴ * K * U
    let hK₀ : K₀.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U hK
    Function.Injective hS.isHermitian.eigenvalues →
      (observableGraph K₀ hK₀).Connected →
        (r.readout () () (bkmGap A K) 0 ↔ A = S ⊗ₖ partialTraceLeft A)

private theorem rejected : ¬ arena.{u}.Law rejectEquality := by
  intro h
  classical
  let A : Matrix (Singleton × Singleton) (Singleton × Singleton) ℂ := 1
  have ht : A.trace = 1 := by simp [A, Matrix.trace]
  have connected (G : SimpleGraph Singleton.{u}) : G.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let o : Singleton.{u} := ⟨()⟩
    refine ⟨o, fun j => ?_⟩
    rw [Subsingleton.elim j o]
  have link := h (R := Singleton) (E := Singleton) A Matrix.PosDef.one
    (0 : Matrix Singleton Singleton ℂ) Matrix.isHermitian_zero ht
    (fun _ _ _ => Subsingleton.elim _ _) (connected _)
  apply link.mpr
  ext ⟨i,e⟩ ⟨j,f⟩
  have hij : i = j := Subsingleton.elim _ _
  have hef : e = f := Subsingleton.elim _ _
  subst j
  subst f
  simp [A, partialTraceRight, partialTraceLeft]

def family : Registration arena.{u} (type_of% @bkmGap_eq_zero_iff_eq_marginals_kronecker.{u}) where
  actual := gapEquality
  bridge := Iff.rfl
  variation := ⟨@bkmGap_eq_zero_iff_eq_marginals_kronecker.{u}, rejectEquality, rejected⟩
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
    (@bkmGap_eq_zero_iff_eq_marginals_kronecker.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMObservableProductRigidity.bkmGap_eq_zero_iff_eq_marginals_kronecker.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity.Product.family
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
    owner := `D5.S3.Quantum.Recovery.BKMObservableProductRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Product

namespace MatrixEquality

private abbrev signature : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨Singleton.{u}, 0, 1, ?_⟩
  intro h
  have he : (1 : Matrix (Singleton.{u}) (Singleton.{u}) ℂ) = 0 :=
    Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

private theorem sensitivity (law : Realization signature.{u} → Prop) (hbad : ¬ law rejected) :
    Sensitivity ⟨signature.{u}, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, hbad⟩
  · intro e
    exact nomatch e

namespace Sum

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : Type u} [Fintype n] {s : n → ℝ} (_hs : ∀ i, 0 < s i)
    (K : Matrix n n ℂ), r.readout () n (∑ v ∈ ratios s, ratioPiece s v K) K

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := Singleton.{u}) (s := fun _ => 1) (fun _ => zero_lt_one) 0

def family : Registration arena.{u} (type_of% @sum_ratioPiece.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_ratioPiece.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.{u}.Law rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_ratioPiece.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity.MatrixEquality.Sum.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity.MatrixEquality.Sum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMObservableProductRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Sum

namespace Adjoint

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : Type u} (s : n → ℝ) (K : Matrix n n ℂ) (_hK : K.IsHermitian)
    {v : ℝ} (_hv : v ≠ 0), r.readout () n (ratioPiece s v K)ᴴ (ratioPiece s v⁻¹ K)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := Singleton.{u}) (fun _ => 1) 0 Matrix.isHermitian_zero (v := 1) one_ne_zero

def family : Registration arena.{u} (type_of% @ratioPiece_adjoint.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ratioPiece_adjoint.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.{u}.Law rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ratioPiece_adjoint.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity.MatrixEquality.Adjoint.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity.MatrixEquality.Adjoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMObservableProductRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Adjoint
end MatrixEquality

end Reg.D5.S3.Quantum.Recovery.BKMObservableProductRigidity
