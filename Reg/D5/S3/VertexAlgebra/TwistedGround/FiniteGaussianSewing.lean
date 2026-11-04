import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
import Reg.Support.DependentFamily
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Ring
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (weight)
open _root_.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate (gaussianCoefficient gaussianCoefficient_zero)

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
  simpa [rejectedZero, realize, row, gaussianCoefficient_zero] using hh

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
  have hn : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (0 : Matrix PUnit.{u+1} PUnit.{u+1} ℂ)‖ < 1 := by simp
  have hh := @h PUnit.{u+1} inferInstance inferInstance PUnit.{v+1} PUnit.{w+1}
    inferInstance inferInstance inferInstance inferInstance 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) hn hn 0 0
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



def expansionArena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [Fintype H] [DecidableEq H]
    {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ)
    (hK : ∀ i j, K i j = K j i) (hL : ∀ i j, L i j = L j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => K (.inr i) (.inr j))‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => L (.inr i) (.inr j))‖ < 1)
    (d : X →₀ ℕ) (e : Y →₀ ℕ),
    ∃ p q : MvPolynomial H ℂ,
      (fun n => R.readout () ⟨H,n⟩
        (polynomialGaussian (fun i j => K (.inr i) (.inr j)) p)) = row K d ∧
      (fun n => R.readout () ⟨H,n⟩
        (polynomialGaussian (fun i j => L (.inr i) (.inr j)) q)) = row L e ∧
      Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
        gaussianCoefficient K (d.sumElim n) * gaussianCoefficient L (e.sumElim n)‖) ∧
      (∑' n : H →₀ ℕ, (weight n : ℂ) * gaussianCoefficient K (d.sumElim n) *
        gaussianCoefficient L (e.sumElim n)) =
        ∑ α ∈ p.support, ∑ β ∈ q.support, p.coeff α * q.coeff β *
          bilinearMoment (fun i j => K (.inr i) (.inr j))
            (fun i j => L (.inr i) (.inr j)) α β

private theorem expansion_rejected_fails : ¬ expansionArena.{u,v,w}.Law rejectedZero := by
  intro h
  have hn : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (0 : Matrix PUnit.{u+1} PUnit.{u+1} ℂ)‖ < 1 := by simp
  obtain ⟨p, q, hp, hq, hs, heq⟩ := @h PUnit.{u+1} inferInstance inferInstance
    PUnit.{v+1} PUnit.{w+1} inferInstance inferInstance inferInstance inferInstance
    0 0 (fun _ _ => rfl) (fun _ _ => rfl) hn hn 0 0
  have hh := congrFun hp 0
  simpa [rejectedZero, realize, row, gaussianCoefficient_zero] using hh

def expansionEvidence : Registration expansionArena.{u,v,w}
    (type_of% (@row_pair_moments.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_pair_moments.{u,v,w}, rejectedZero, expansion_rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedZero, ?_, rfl, expansion_rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def expansionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@row_pair_moments.{u,v,w}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.expansionUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.expansionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨expansionArena.{u,v,w}⟩
  objectArena := .source ⟨expansionArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source expansionArena.{u,v,w} ⟨expansionEvidence⟩
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

namespace Moment

abbrev signature : Signature where
  Params := Σ H : Type u, H
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ p f => f p.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [Fintype H] [DecidableEq H]
    (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (α β : H →₀ ℕ),
    (fun i => R.readout () ⟨H,i⟩
      (fun j => bilinearMoment A B (α + Finsupp.single j 1) β)) =
      Matrix.mulVec (1 - B * A)⁻¹ʳ
        (Matrix.mulVec B (fun i => (α i : ℂ) *
          bilinearMoment A B (α - Finsupp.single i 1) β) +
          fun i => (β i : ℂ) * bilinearMoment A B α (β - Finsupp.single i 1))

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  let I := PUnit.{u+1}
  let i : I := PUnit.unit
  have hv := @_root_.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.vacuum_trace_log
    I inferInstance inferInstance 0 0 (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp)
  have h00 : bilinearMoment (0 : Matrix I I ℂ) 0 0 0 = 1 := by
    simpa [bilinearMoment,
      _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.created_zero,
      _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.pairing] using hv.2.2
  have hh := congrFun (@h I inferInstance inferInstance 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp) 0 (Finsupp.single i 1)) i
  simpa [rejected, realize, Matrix.zero_mul, Ring.inverse_one, h00] using hh

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u+1}, PUnit.unit⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena.{u} (type_of% (@bilinearMoment_resolvent_step.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilinearMoment_resolvent_step.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bilinearMoment_resolvent_step.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.Moment.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.Moment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
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


def wickArena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [Fintype H] [DecidableEq H]
    (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1),
    (∀ i j, covariance A B i j = covariance A B j i) ∧
    (∀ (α β : H →₀ ℕ) (i : H),
      R.readout () ⟨H,i⟩ (fun j => bilinearMoment A B (α + Finsupp.single j 1) β) =
        (∑ j, covariance A B (.inl i) (.inl j) * (α j : ℂ) *
          bilinearMoment A B (α - Finsupp.single j 1) β) +
        ∑ j, covariance A B (.inl i) (.inr j) * (β j : ℂ) *
          bilinearMoment A B α (β - Finsupp.single j 1)) ∧
    (∀ (α β : H →₀ ℕ) (i : H),
      R.readout () ⟨H,i⟩ (fun j => bilinearMoment A B α (β + Finsupp.single j 1)) =
        (∑ j, covariance A B (.inr i) (.inl j) * (α j : ℂ) *
          bilinearMoment A B (α - Finsupp.single j 1) β) +
        ∑ j, covariance A B (.inr i) (.inr j) * (β j : ℂ) *
          bilinearMoment A B α (β - Finsupp.single j 1))

private theorem wick_rejected_fails : ¬ wickArena.{u}.Law rejected := by
  intro h
  let I := PUnit.{u+1}
  let i : I := PUnit.unit
  have hv := @_root_.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.vacuum_trace_log
    I inferInstance inferInstance 0 0 (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp)
  have h00 : bilinearMoment (0 : Matrix I I ℂ) 0 0 0 = 1 := by
    simpa [bilinearMoment,
      _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.created_zero,
      _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.pairing] using hv.2.2
  have hh := (@h I inferInstance inferInstance 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp)).2.1
      0 (Finsupp.single i 1) i
  have hd : (default : I) = i := Subsingleton.elim _ _
  simpa [rejected, realize, covariance, Ring.inverse_one, hd, h00] using hh

def wickEvidence : Registration wickArena.{u}
    (type_of% (@bilinearMoment_wick_recursion.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilinearMoment_wick_recursion.{u}, rejected, wick_rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, wick_rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def wickAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bilinearMoment_wick_recursion.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.Moment.wickUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.Moment.wickEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨wickArena.{u}⟩
  objectArena := .source ⟨wickArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wickArena.{u} ⟨wickEvidence⟩
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

end Moment


def nativeArena : Arena where
  signature := signature.{u}
  Law W := ∀ {H : Type u} [Fintype H] [DecidableEq H]
    (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (α β : H →₀ ℕ),
    bilinearMoment A B α β = W.readout () ⟨H ⊕ H, α.sumElim β⟩
      (fun r => Complex.exp ((1 / 2 : ℂ) *
        ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) *
        _root_.D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment.nativeMoment
          (covariance A B) r)

private theorem native_rejected_fails : ¬ nativeArena.{u}.Law rejectedZero := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp) 0 0
  have hv := @bilinearMoment_native PUnit.{u+1} inferInstance inferInstance 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp) 0 0
  have h00 : bilinearMoment (0 : Matrix PUnit.{u+1} PUnit.{u+1} ℂ) 0 0 0 = 1 := by
    simpa [_root_.D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment.nativeMoment,
      _root_.D5.S3.VertexAlgebra.FactorialFockMetric.weight,
      gaussianCoefficient_zero] using hv
  simpa [rejectedZero, realize, h00] using hh

def sewingArena : Arena where
  signature := signature.{u}
  Law W := ∀ {H : Type u} [Fintype H] [DecidableEq H]
    {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Matrix H H ℂ) (R : Matrix X H ℂ) (S : Matrix H Y ℂ)
    (hP : ∀ i j, P i j = P j i) (hQ : ∀ i j, Q i j = Q j i)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (d : X →₀ ℕ) (e : Y →₀ ℕ),
    Summable (fun n : H →₀ ℕ => ‖W.readout () ⟨H,n⟩ (fun m => (weight m : ℂ) *
      gaussianCoefficient (Matrix.fromBlocks P R R.transpose A) (d.sumElim m) *
      gaussianCoefficient (Matrix.fromBlocks B S S.transpose Q) (m.sumElim e))‖) ∧
    (∑' n : H →₀ ℕ, W.readout () ⟨H,n⟩ (fun m => (weight m : ℂ) *
      gaussianCoefficient (Matrix.fromBlocks P R R.transpose A) (d.sumElim m) *
      gaussianCoefficient (Matrix.fromBlocks B S S.transpose Q) (m.sumElim e))) =
      Complex.exp ((1 / 2 : ℂ) *
        ∑' k : ℕ, Matrix.trace ((A * B) ^ (k + 1)) / (k + 1 : ℂ)) *
      gaussianCoefficient (effectiveKernel P Q A B R S) (d.sumElim e)

private theorem sewing_rejected_fails : ¬ sewingArena.{u,v,w}.Law rejectedOne := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance PUnit.{v+1} PUnit.{w+1}
    inferInstance inferInstance inferInstance inferInstance 0 0 0 0 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by simp) (by simp) 0 0
  have hs : Summable (fun _ : PUnit.{u+1} →₀ ℕ => (1 : ℝ)) := by
    simpa [rejectedOne, realize] using hh.1
  simpa only [summable_const_iff, one_ne_zero, or_false] using hs


def nativeEvidence : Registration nativeArena.{u}
    (type_of% (@bilinearMoment_native.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilinearMoment_native.{u}, rejectedZero, native_rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedZero, ?_, rfl, native_rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def nativeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bilinearMoment_native.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.nativeUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.nativeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨nativeArena.{u}⟩
  objectArena := .source ⟨nativeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nativeArena.{u} ⟨nativeEvidence⟩
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

def sewingEvidence : Registration sewingArena.{u,v,w}
    (type_of% (@finite_sewing.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_sewing.{u,v,w}, rejectedOne, sewing_rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedOne, ?_, rfl, sewing_rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def sewingAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_sewing.{u,v,w}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.sewingUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing.sewingEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sewingArena.{u,v,w}⟩
  objectArena := .source ⟨sewingArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sewingArena.{u,v,w} ⟨sewingEvidence⟩
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
