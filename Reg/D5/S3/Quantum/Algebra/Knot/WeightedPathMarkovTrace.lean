import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
import Reg.Support.DependentFamily

open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
universe u
attribute [local instance] Classical.propDecidable
local instance {L : Type u} (R : L → L → Prop) (n : ℕ) (s t : L) :
    DecidableEq (LegalPath R n s t) := Classical.decEq _

structure NativeData where
  L : Type u
  finite : Fintype L
  eq : DecidableEq L
  R : L → L → Prop
  d : L → ℝ
  δ : ℝ
  n : ℕ
  s : L

def data {L : Type u} [Fintype L] [DecidableEq L] (R : L → L → Prop)
    (d : L → ℝ) (δ : ℝ) (n : ℕ) (s : L) : NativeData where
  L := L
  finite := inferInstance
  eq := inferInstance
  R := R
  d := d
  δ := δ
  n := n
  s := s

abbrev signature : Signature where
  Params := NativeData.{u}
  State p := C p.R (p.n + 1) p.s
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := C p.R p.n p.s
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p Y => by
    letI := p.finite
    letI := p.eq
    exact F p.R p.d p.δ p.n p.s Y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) [DecidableRel R]
    (hR : Std.Symm R) (d : L → ℝ) (hd : ∀ t, 0 < d t)
    (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ t, (∑ u : L with R t u, d u) = δ * d t),
    ∀ (n : ℕ) (s : L),
      Function.Injective (iotaHom R n s) ∧
      (∀ (t u : L) (h : R t u), (J R n s t u h)ᴴ * J R n s t u h = 1) ∧
      (∀ (t v u : L) (ht : R t u) (hv : R v u), t ≠ v →
        (J R n s t u ht)ᴴ * J R n s v u hv = 0) ∧
      (∀ (t u : L) (h : R t u) (Y : C R (n + 1) s),
        (J R n s t u h)ᴴ * Y u * J R n s t u h =
          (Y u).submatrix (append R n s t u h) (append R n s t u h)) ∧
      (∀ X : C R n s, F R d δ n s (iota R n s X) = X) ∧
      (∀ (A B : C R n s) (Y : C R (n + 1) s),
        F R d δ n s (iota R n s A * Y * iota R n s B) =
          A * F R d δ n s Y * B) ∧
      (∀ Y : C R (n + 1) s, tau R d δ n s (r.readout () (data R d δ n s) Y) = tau R d δ (n + 1) s Y) ∧
      (∀ X : C R n s, tau R d δ (n + 1) s (iota R n s X) = tau R d δ n s X) ∧
      tau R d δ n s 1 = 1 ∧
      (∀ hn : 0 < n,
        F R d δ n s (lastProjection R d δ n hn s) = ((δ : ℂ)⁻¹ ^ 2) • 1 ∧
        (∀ X : C R n s,
          tau R d δ (n + 1) s (iota R n s X * lastProjection R d δ n hn s) =
            ((δ : ℂ)⁻¹ ^ 2) * tau R d δ n s X) ∧
        star (lastProjection R d δ n hn s) = lastProjection R d δ n hn s ∧
        lastProjection R d δ n hn s * lastProjection R d δ n hn s =
          lastProjection R d δ n hn s)

def actual_law : arena.Law actual := by
  intro L _ _ R _ hR d hd δ hδ hPF
  exact weighted_path_markov_trace R hR d hd δ hδ hPF


private def testRelation : ULift.{u} Unit → ULift.{u} Unit → Prop := fun _ _ => True
private def testStart : ULift.{u} Unit := ⟨()⟩

private def unit_ne_zero : (0 : C testRelation 0 testStart) ≠ 1 := by
  intro h
  let p : LegalPath testRelation 0 testStart testStart :=
    ⟨fun _ => testStart, rfl, rfl, fun k => Fin.elim0 k⟩
  have hh := congrArg (fun X : C testRelation 0 testStart => X testStart p p) h
  simpa using hh

private def test_law := weighted_path_markov_trace testRelation
  (⟨fun _ _ _ => trivial⟩ : Std.Symm testRelation) (fun _ => (1 : ℝ))
  (by intro; norm_num) 1 (by norm_num)
  (by intro; simp [testRelation])

def rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance testRelation inferInstance
    (⟨fun _ _ _ => trivial⟩ : Std.Symm testRelation) (fun _ => (1 : ℝ))
    (by intro; norm_num) 1 (by norm_num) (by intro; simp [testRelation]) 0 testStart
  have ht := hh.2.2.2.2.2.2.1 (iota testRelation 0 testStart 1)
  change tau testRelation (fun _ => 1) 1 0 testStart 0 =
    tau testRelation (fun _ => 1) 1 1 testStart (iota testRelation 0 testStart 1) at ht
  rw [(test_law.{u} 0 testStart).2.2.2.2.2.2.2.1 1,
    (test_law.{u} 0 testStart).2.2.2.2.2.2.2.2.1] at ht
  simp [tau] at ht

def registration : Registration arena (type_of% (@weighted_path_markov_trace.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨data testRelation (fun _ => 1) 1 0 testStart,
      iota testRelation 0 testStart 0, iota testRelation 0 testStart 1, ?_⟩
    change F testRelation (fun _ => 1) 1 0 testStart (iota testRelation 0 testStart 0) ≠
      F testRelation (fun _ => 1) 1 0 testStart (iota testRelation 0 testStart 1)
    rw [(test_law.{u} 0 testStart).2.2.2.2.1 0, (test_law.{u} 0 testStart).2.2.2.2.1 1]
    exact unit_ne_zero

#print axioms registration

-- The public scalar-linearity helper keeps its original unrestricted telescope.
abbrev scalarSignature : Signature where
  Params := NativeData.{u}
  State p := C p.R p.n p.s
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def scalarActual : Realization scalarSignature := realize scalarSignature
  (fun _ p X => by
    letI := p.finite
    letI := p.eq
    exact tau p.R p.d p.δ p.n p.s X) (fun e => nomatch e)
def scalarRejected : Realization scalarSignature := realize scalarSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev scalarArena : Arena where
  signature := scalarSignature
  Law r := ∀ {L : Type u} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s : L) (c : ℂ) (X : C R n s),
    r.readout () (data R d δ n s) (c • X) =
      c * r.readout () (data R d δ n s) X

def scalarActual_law : scalarArena.Law scalarActual := by
  intro L _ _ R d δ n s c X
  exact tau_smul R d δ n s c X

def scalarRejected_law : ¬ scalarArena.{u}.Law scalarRejected.{u} := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance inferInstance testRelation
    (fun _ => 1) 1 0 testStart 0 1
  norm_num [scalarRejected, realize] at hh

def scalarFamily : Registration scalarArena (type_of% (@tau_smul.{u})) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨scalarActual_law, scalarRejected, scalarRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarRejected, ?_, rfl, scalarRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨data testRelation (fun _ => 1) 1 0 testStart, 0, 1, ?_⟩
    change tau testRelation (fun _ => 1) 1 0 testStart 0 ≠
      tau testRelation (fun _ => 1) 1 0 testStart 1
    rw [(test_law.{u} 0 testStart).2.2.2.2.2.2.2.2.1]
    simp [tau]

#print axioms scalarFamily

def scalarRegistration_1.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tau_smul.{u_1}) (Realization scalarSignature.{u_1}) Unit Unit where
  unitName := `D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace.tau_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace.scalarFamily
  realizationSource := none
  generated := false
  arena := .source ⟨scalarArena.{u_1}⟩
  objectArena := .source ⟨scalarArena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scalarArena.{u_1} ⟨scalarFamily.{u_1}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature.{u_1}
    (fun _ p X => by
      letI := p.finite
      letI := p.eq
      exact tau p.R p.d p.δ p.n p.s X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false
    }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scalarRegistration_1


end Reg.D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
