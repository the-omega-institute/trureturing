import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
import Reg.Support.DependentFamily
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (weight)

universe u v w
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing

abbrev signature : Signature where
  Params := Σ H : Type u, H →₀ ℕ
  State p := (p.1 →₀ ℕ) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ p f => f p.2) (fun e => nomatch e)

def rejectedZero : Realization signature.{u} :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

def rejectedOne : Realization signature.{u} :=
  realize _ (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u+1}, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def rowArena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [Fintype H] [DecidableEq H]
    {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (hsym : ∀ i j, K i j = K j i) (d : X →₀ ℕ),
    ∃ p : MvPolynomial H ℂ,
      (fun n => R.readout () ⟨H, n⟩
        (polynomialGaussian (fun i j => K (.inr i) (.inr j)) p)) = row K d

private theorem row_rejected_fails : ¬ rowArena.{u,v}.Law rejectedZero := by
  intro h
  obtain ⟨p, hp⟩ := @h PUnit.{u+1} inferInstance inferInstance
    PUnit.{v+1} inferInstance inferInstance 0 (fun _ _ => rfl) 0
  have hh := congrFun hp 0
  simpa [rejectedZero, realize, row] using hh

def rowEvidence : Registration rowArena.{u,v} (type_of% (@row_polynomial.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_polynomial.{u,v}, rejectedZero, row_rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedZero, ?_, rfl, row_rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def rowAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@row_polynomial.{u,v}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.rowUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.rowEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rowArena.{u,v}⟩
  objectArena := .source ⟨rowArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowArena.{u,v} ⟨rowEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def convergenceArena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [Fintype H] [DecidableEq H]
    {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ)
    (hK : ∀ i j, K i j = K j i) (hL : ∀ i j, L i j = L j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => K (.inr i) (.inr j))‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => L (.inr i) (.inr j))‖ < 1)
    (d : X →₀ ℕ) (e : Y →₀ ℕ),
    Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
      R.readout () ⟨H,n⟩ (row K d) * R.readout () ⟨H,n⟩ (row L e)‖)

private theorem convergence_rejected_fails : ¬ convergenceArena.{u,v,w}.Law rejectedOne := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance PUnit.{v+1} PUnit.{w+1}
    inferInstance inferInstance inferInstance inferInstance 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp) 0 0
  have hs : Summable (fun _ : PUnit.{u+1} →₀ ℕ => (1 : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ => zero_le_one) _ hh
    intro n
    simp only [rejectedOne, realize, mul_one, Complex.norm_natCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (_root_.D5.S3.VertexAlgebra.FactorialFockMetric.weight_pos n))
  simpa only [summable_const_iff, one_ne_zero, or_false] using hs

def convergenceEvidence : Registration convergenceArena.{u,v,w}
    (type_of% (@row_pair_norm_summable.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_pair_norm_summable.{u,v,w}, rejectedOne, convergence_rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedOne, ?_, rfl, convergence_rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def convergenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@row_pair_norm_summable.{u,v,w}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.convergenceUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.convergenceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨convergenceArena.{u,v,w}⟩
  objectArena := .source ⟨convergenceArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source convergenceArena.{u,v,w} ⟨convergenceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
