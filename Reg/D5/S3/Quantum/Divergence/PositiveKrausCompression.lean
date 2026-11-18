import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.PositiveKrausCompression

/-! Literal channel, universal trace premise and joint residual-Gram readout. -/

noncomputable section
universe u
open Set Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer

structure Parameters where
  a : Type u
  b : Type u
  fa : Fintype a
  da : DecidableEq a
  na : Nonempty a
  fb : Fintype b
  db : DecidableEq b
  nb : Nonempty b
  channel : @QuantumChannel a b fa da fb db

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := I p.b → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (I p.b × p.a) (I p.b × p.a) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => by
    letI := p.fa
    letI := p.da
    letI := p.na
    letI := p.fb
    letI := p.db
    letI := p.nb
    exact D p.channel x * (D p.channel x)ᴴ) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => by
    letI := p.da
    letI := p.db
    exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {a b : Type u} [fa : Fintype a] [da : DecidableEq a] [na : Nonempty a]
    [fb : Fintype b] [db : DecidableEq b] [nb : Nonempty b]
    (channel : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k) (i₀ : I b)
    (hUniversal : UniversalPositiveTraceTest channel k),
    ∃ x : I b → ℂ,
      ((k : ℂ) • (C channel * (C channel)ᴴ) -
        R.readout () ⟨a, b, fa, da, na, fb, db, nb, channel⟩ x).PosSemidef

theorem source_equivalence :
    (type_of% @selected_column_joint_gram.{u}) ↔ arena.{u}.Law actual := Iff.rfl

def singletonChannel : QuantumChannel (ULift.{u} Unit) (ULift.{u} Unit) where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (StarAlgEquiv.refl ℂ (CStarMatrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ))
  trace_preserving _ := rfl

theorem singleton_test : UniversalPositiveTraceTest singletonChannel.{u} 0 := by
  intro R _ _ Y Z hZ
  let t : ULift.{u} Unit := ⟨()⟩
  let X : Matrix R R ℂ := fun r s => PhiR singletonChannel Y (r,t) (s,t)
  have hres : PhiR singletonChannel Y - Matrix.kronecker X
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 0 := by
    ext ⟨r,x⟩ ⟨s,y⟩
    have hx : x = t := Subsingleton.elim _ _
    have hy : y = t := Subsingleton.elim _ _
    subst x
    subst y
    change PhiR singletonChannel Y (r,t) (s,t) - X r s *
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) t t = 0
    simp [X]
  have hb : BddBelow (Set.range (fun W : Matrix R R ℂ =>
      (Z * ((PhiR singletonChannel Y - Matrix.kronecker W
        (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)) *
        (PhiR singletonChannel Y - Matrix.kronecker W 1)ᴴ)).trace.re)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact RHLinalg.trace_mul_nonneg_of_posSemidef hZ.posSemidef
      (Matrix.posSemidef_self_mul_conjTranspose _)
  have hle := csInf_le hb (Set.mem_range_self X)
  simpa only [hres, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.trace_zero, Complex.zero_re, Complex.ofReal_zero, zero_smul] using hle

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := h singletonChannel 0 (by norm_num) (⟨()⟩, ⟨()⟩) singleton_test
  change ((0 : ℂ) • (C singletonChannel * (C singletonChannel)ᴴ) - 1).PosSemidef at hx
  have hd := (Complex.nonneg_iff.mp (hx.diag_nonneg
    (i := ((⟨()⟩, ⟨()⟩), ⟨()⟩)))).1
  norm_num [Matrix.one_apply] at hd

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let q := ULift.{u} Unit
  let t : q := ⟨()⟩
  let p : Parameters.{u} := ⟨q, q, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, singletonChannel⟩
  let x : I q → ℂ := fun j => Phi singletonChannel (E j) t t
  let y : I q → ℂ := fun j => x j + 1
  refine ⟨p, x, y, ?_⟩
  have hx : D singletonChannel x = 0 := by
    ext ⟨j,r⟩ s
    have hr : r = t := Subsingleton.elim _ _
    have hs : s = t := Subsingleton.elim _ _
    subst r
    subst s
    simp [D, x, Matrix.one_apply]
  have hy : D singletonChannel y = (fun _ _ => -1) := by
    ext ⟨j,r⟩ s
    have hj : j = (t,t) := Subsingleton.elim _ _
    have hr : r = t := Subsingleton.elim _ _
    have hs : s = t := Subsingleton.elim _ _
    subst j
    subst r
    subst s
    simp [D, y, x, Matrix.one_apply]
  intro he
  change D singletonChannel x * (D singletonChannel x)ᴴ =
    D singletonChannel y * (D singletonChannel y)ᴴ at he
  rw [hx, hy] at he
  have hd := congrArg (fun M : Matrix (I q × q) (I q × q) ℂ =>
    M ((t,t),t) ((t,t),t)) he
  change (∑ _ : q, (0 : ℂ) * star (0 : ℂ)) =
    ∑ _ : q, (-1 : ℂ) * star (-1 : ℂ) at hd
  simp [q] at hd

def family : Registration arena.{u} (type_of% @selected_column_joint_gram.{u}) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@selected_column_joint_gram.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@selected_column_joint_gram.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UniversalPositiveScalarizer.selected_column_joint_gram.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => by
    letI := p.fa
    letI := p.da
    letI := p.na
    letI := p.fb
    letI := p.db
    letI := p.nb
    exact D p.channel x * (D p.channel x)ᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.PositiveKrausCompression
    definition := none
    coordinates := #[0, 1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_equivalence
#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
