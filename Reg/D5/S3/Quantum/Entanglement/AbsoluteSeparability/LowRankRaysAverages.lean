import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.CompositeCones
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
open scoped BigOperators ComplexOrder Kronecker

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages

namespace Product

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ}, A.PosSemidef → B.PosSemidef →
      separableCone (R.readout () ⟨m, n⟩ A ⊗ₖ B)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) (A := 1) (B := 1) PosSemidef.one PosSemidef.one
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤
    ((-1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (0, 0) (0, 0) at hd
  norm_num [Matrix.kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply,
    Complex.le_def] at hd

def family : Registration arena (type_of% @separable_kronecker) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨separable_kronecker, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    intro h
    have he := congrFun (congrFun h 0) 0
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separable_kronecker) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages.Product.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages.Product.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Product

namespace RowAverage

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Fin p.1 × Fin p.2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p ψ => vecMulVec ψ (star ψ) + (1 : Matrix (Fin p.1) (Fin p.1) ℂ) ⊗ₖ reduced ψ)
  (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} (ψ : Fin m × Fin n → ℂ),
    separableCone (R.readout () ⟨m, n⟩ ψ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) 0
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd

def family : Registration arena (type_of% @separable_rankOne_add_reduced) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨separable_rankOne_add_reduced, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrFun (congrFun h (0, 0)) (0, 0)
    change
      (vecMulVec (fun _ : Fin 1 × Fin 1 => (0 : ℂ))
          (star (fun _ : Fin 1 × Fin 1 => (0 : ℂ))) +
        (1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ reduced (fun _ : Fin 1 × Fin 1 => (0 : ℂ))) (0, 0) (0, 0)
          =
      (vecMulVec (fun _ : Fin 1 × Fin 1 => (1 : ℂ))
          (star (fun _ : Fin 1 × Fin 1 => (1 : ℂ))) +
        (1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ reduced (fun _ : Fin 1 × Fin 1 => (1 : ℂ))) (0, 0) (0, 0)
          at he
    norm_num [reduced, Matrix.add_apply, Matrix.one_apply, Matrix.kroneckerMap_apply,
      Matrix.vecMulVec_apply, Pi.star_apply] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separable_rankOne_add_reduced) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages.RowAverage.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages.RowAverage.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end RowAverage

namespace ProjectedAverage

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Fin p.1 × Fin p.2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.2) (Fin p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ χ => reduced χ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} (χ : Fin m × Fin n → ℂ) (u : Fin m → ℂ) (v : Fin n → ℂ)
    (a : ℝ) (P : Matrix (Fin m) (Fin m) ℂ),
    P.IsHermitian → P * P = P →
      (∀ j, P *ᵥ (fun i => χ (i, j)) = fun i => χ (i, j)) →
        let ψ : Fin m × Fin n → ℂ := fun ij => (a : ℂ) * u ij.1 * v ij.2 + χ ij
        separableCone (vecMulVec ψ (star ψ) +
          (P + ((2 * a ^ 2 : ℝ) : ℂ) • vecMulVec u (star u)) ⊗ₖ R.readout () ⟨m, n⟩ χ +
          (1 / 2 : ℂ) • (P ⊗ₖ vecMulVec v (star v)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) 0 0 0 0 1 isHermitian_one (by simp) (by intro j; simp)
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤
    (vecMulVec (fun _ : Fin 1 × Fin 1 => ((0 : ℝ) : ℂ) * 0 * 0 + 0)
        (star (fun _ : Fin 1 × Fin 1 => ((0 : ℝ) : ℂ) * 0 * 0 + 0)) +
      ((1 : Matrix (Fin 1) (Fin 1) ℂ) +
        ((2 * (0 : ℝ) ^ 2 : ℝ) : ℂ) •
          vecMulVec (fun _ : Fin 1 => (0 : ℂ)) (star (fun _ : Fin 1 => (0 : ℂ)))) ⊗ₖ
        (-1 : Matrix (Fin 1) (Fin 1) ℂ) +
      (1 / 2 : ℂ) • ((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ
        vecMulVec (fun _ : Fin 1 => (0 : ℂ)) (star (fun _ : Fin 1 => (0 : ℂ)))))
          (0, 0) (0, 0) at hd
  norm_num [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.neg_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.le_def] at hd

def family : Registration arena (type_of% @separable_projected_rankOne) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨separable_projected_rankOne, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrFun (congrFun h 0) 0
    change
      reduced (fun _ : Fin 1 × Fin 1 => (0 : ℂ)) 0 0 =
      reduced (fun _ : Fin 1 × Fin 1 => (1 : ℂ)) 0 0 at he
    norm_num [reduced] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separable_projected_rankOne) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages.ProjectedAverage.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages.ProjectedAverage.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end ProjectedAverage

end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
