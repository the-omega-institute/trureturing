import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.QuadraticForms.ConicGDNN.Duality
import Mathlib.Tactic
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
open _root_.D5.S3.QuadraticForms.ConicGDNN.Defs
namespace Reg.D5.S3.QuadraticForms.ConicGDNN.Duality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev Shape := Σ _p : ℕ, Σ r : ℕ, Fin r → ℕ
abbrev Shape.p (s : Shape) : ℕ := s.1
abbrev Shape.r (s : Shape) : ℕ := s.2.1
abbrev Shape.k (s : Shape) : Fin s.r → ℕ := s.2.2

abbrev Vec (s : Shape) := Idx s.p s.r s.k → ℝ
abbrev Mat (s : Shape) := Matrix (Idx s.p s.r s.k) (Idx s.p s.r s.k) ℝ
private def line : Shape := ⟨1, 0, Fin.elim0⟩

private lemma zero_mem_dnnNN (p r : ℕ) (k : Fin r → ℕ) :
    (0 : Matrix (Idx p r k) (Idx p r k) ℝ) ∈ dnnNN p r k := by
  constructor
  · exact Matrix.isSymm_zero
  · intro A hA
    simp

private lemma zero_mem_cone (p r : ℕ) (k : Fin r → ℕ) :
    (0 : Idx p r k → ℝ) ∈ cone p r k := by
  simp [cone]

private lemma eval_sos4_nonneg {ι : Type*} (x : ι → ℝ)
    {f : MvPolynomial ι ℝ} (hf : f ∈ sos4 ι) : 0 ≤ eval x f := by
  apply convexHull_min (t := {f : MvPolynomial ι ℝ | 0 ≤ eval x f}) ?_ ?_ hf
  · rintro _ ⟨θ, hθ, rfl⟩
    simpa using sq_nonneg (eval x θ)
  · intro f hf g hg a b ha hb hab
    change 0 ≤ eval x (a • f + b • g)
    simp only [map_add, smul_eq_C_mul, map_mul, eval_C]
    exact add_nonneg (mul_nonneg ha hf) (mul_nonneg hb hg)

private lemma negative_not_knn0 :
    (fun _ _ => (-1 : ℝ) : Mat line) ∉ knn0 line.p line.r line.k := by
  intro h
  have H := eval_sos4_nonneg (fun _ => 1) h.2
  norm_num [quartic, jsq, line, Idx, Fintype.sum_sum_type, Fin.sum_univ_succ] at H

private lemma negative_not_psd :
    ¬ Matrix.PosSemidef (fun _ _ => (-1 : ℝ) : Mat line) := by
  intro h
  have H := h.dotProduct_mulVec_nonneg (fun _ => 1)
  norm_num [Matrix.mulVec, dotProduct, line, Idx, Fintype.sum_sum_type,
    Fin.sum_univ_succ] at H

private lemma negative_not_cone : (fun _ => (-1 : ℝ) : Vec line) ∉
    cone line.p line.r line.k := by
  intro h
  have H := h.1 (0 : Fin 1)
  norm_num at H


open _root_.D5.S3.QuadraticForms.ConicGDNN.Duality
abbrev rankSignature : Signature where
  Params := Shape
  State s := Vec s
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := Mat s
  Anchor := Empty
  finiteAnchor := inferInstance

def rankActual : Realization rankSignature :=
  realize rankSignature (fun _ _ w => vecMulVec w w) (fun e => nomatch e)
def rankBad : Realization rankSignature :=
  realize rankSignature (fun _ _ _ => fun _ _ => -1) (fun e => nomatch e)
abbrev rankArena : Arena where
  signature := rankSignature
  Law R := ∀ {p r : ℕ} {k : Fin r → ℕ} (w : Idx p r k → ℝ),
    R.readout () ⟨p, r, k⟩ w ∈ knn0 p r k
private lemma rankRejected : ¬ rankArena.Law rankBad := by
  intro h
  exact negative_not_knn0 (h (p := 1) (r := 0) (k := Fin.elim0) 0)
def rankFamily : Registration rankArena (type_of% @quartic_rankOne) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨quartic_rankOne, rankBad, rankRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rankRejected
  dependence := by
    intro i
    refine ⟨line, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have H := congrFun (congrFun h (Sum.inl (⟨0, by decide⟩ : Fin line.p))) (Sum.inl (⟨0, by decide⟩ : Fin line.p))
    norm_num [rankActual, realize, vecMulVec, Pi.zero_apply] at H

abbrev psdSignature : Signature where
  Params := Shape
  State s := Mat s
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := Mat s
  Anchor := Empty
  finiteAnchor := inferInstance

def psdActual : Realization psdSignature :=
  realize psdSignature (fun _ _ Xm => Xm) (fun e => nomatch e)
def psdBad : Realization psdSignature :=
  realize psdSignature (fun _ _ _ => fun _ _ => -1) (fun e => nomatch e)
abbrev psdArena : Arena where
  signature := psdSignature
  Law R := ∀ {p r : ℕ} {k : Fin r → ℕ}
    {Xm : Matrix (Idx p r k) (Idx p r k) ℝ}, Xm ∈ dnnNN p r k →
      Matrix.PosSemidef (R.readout () ⟨p, r, k⟩ Xm)
private lemma psdRejected : ¬ psdArena.Law psdBad := by
  intro h
  exact negative_not_psd (h (zero_mem_dnnNN 1 0 Fin.elim0))
def psdFamily : Registration psdArena (type_of% @posSemidef_of_mem_dnnNN) where
  actual := psdActual
  bridge := Iff.rfl
  variation := ⟨posSemidef_of_mem_dnnNN, psdBad, psdRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ psdRejected
  dependence := by
    intro i
    refine ⟨line, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    intro h
    have H := congrFun (congrFun h (Sum.inl (⟨0, by decide⟩ : Fin line.p))) (Sum.inl (⟨0, by decide⟩ : Fin line.p))
    norm_num [psdActual, realize, Matrix.zero_apply] at H

abbrev VectorParameter := Σ p : ℕ, Σ r : ℕ, Σ k : Fin r → ℕ, Idx p r k → ℝ
abbrev vectorShape (s : VectorParameter) : Shape := ⟨s.1, s.2.1, s.2.2.1⟩
abbrev parameterVector (s : VectorParameter) : Vec (vectorShape s) := s.2.2.2

abbrev symSignature : Signature where
  Params := VectorParameter
  State p := Vec (vectorShape p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Mat (vectorShape p)
  Anchor := Empty
  finiteAnchor := inferInstance

def symActual : Realization symSignature :=
  realize symSignature (fun _ p u => (1 / 2 : ℝ) •
    (vecMulVec (parameterVector p) u + vecMulVec u (parameterVector p))) (fun e => nomatch e)
def symBad : Realization symSignature :=
  realize symSignature (fun _ _ _ => fun _ _ => -1) (fun e => nomatch e)
abbrev symArena : Arena where
  signature := symSignature
  Law R := ∀ {p r : ℕ} {k : Fin r → ℕ} (u v : Idx p r k → ℝ),
    u ∈ cone p r k → v ∈ cone p r k → R.readout () ⟨p, r, k, u⟩ v ∈ knn0 p r k
private lemma symRejected : ¬ symArena.Law symBad := by
  intro h
  exact negative_not_knn0 (h 0 0 (zero_mem_cone 1 0 Fin.elim0)
    (zero_mem_cone 1 0 Fin.elim0))
def symFamily : Registration symArena (type_of% @sym_mem_knn0) where
  actual := symActual
  bridge := Iff.rfl
  variation := ⟨sym_mem_knn0, symBad, symRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ symRejected
  dependence := by
    intro i
    refine ⟨⟨1, 0, Fin.elim0, (fun _ => 1)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have H := congrFun (congrFun h (Sum.inl (⟨0, by decide⟩ : Fin line.p))) (Sum.inl (⟨0, by decide⟩ : Fin line.p))
    norm_num [symActual, realize, vecMulVec, Matrix.smul_apply, Matrix.add_apply, Pi.zero_apply] at H

abbrev MatrixParameter := Σ p : ℕ, Σ r : ℕ, Σ k : Fin r → ℕ,
  Matrix (Idx p r k) (Idx p r k) ℝ
abbrev matrixShape (s : MatrixParameter) : Shape := ⟨s.1, s.2.1, s.2.2.1⟩
abbrev parameterMatrix (s : MatrixParameter) : Mat (matrixShape s) := s.2.2.2

abbrev mulSignature : Signature where
  Params := MatrixParameter
  State p := Vec (matrixShape p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Vec (matrixShape p)
  Anchor := Empty
  finiteAnchor := inferInstance

def mulActual : Realization mulSignature :=
  realize mulSignature (fun _ p v => parameterMatrix p *ᵥ v) (fun e => nomatch e)
def mulBad : Realization mulSignature :=
  realize mulSignature (fun _ _ _ => fun _ => -1) (fun e => nomatch e)
abbrev mulArena : Arena where
  signature := mulSignature
  Law R := ∀ {p r : ℕ} {k : Fin r → ℕ}
    {Xm : Matrix (Idx p r k) (Idx p r k) ℝ}, Xm ∈ dnnNN p r k →
      ∀ {v : Idx p r k → ℝ}, v ∈ cone p r k →
        R.readout () ⟨p, r, k, Xm⟩ v ∈ cone p r k
private lemma mulRejected : ¬ mulArena.Law mulBad := by
  intro h
  exact negative_not_cone (h (zero_mem_dnnNN 1 0 Fin.elim0)
    (zero_mem_cone 1 0 Fin.elim0))
def mulFamily : Registration mulArena (type_of% @mulVec_mem_cone) where
  actual := mulActual
  bridge := Iff.rfl
  variation := ⟨mulVec_mem_cone, mulBad, mulRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ mulRejected
  dependence := by
    intro i
    refine ⟨⟨1, 0, Fin.elim0, (fun _ _ => 1)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have H := congrFun h (Sum.inl (⟨0, by decide⟩ : Fin line.p))
    norm_num [mulActual, realize, Matrix.mulVec, dotProduct, Pi.zero_apply, line, Idx,
      Fintype.sum_sum_type, Fin.sum_univ_succ] at H


open LeanInformationAudit

def rankAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quartic_rankOne) (Realization rankSignature) Unit Unit where
  unitName := `D5.S3.QuadraticForms.ConicGDNN.Duality.quartic_rankOne.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Duality.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena⟩
  objectArena := .source ⟨rankArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena ⟨rankFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature (fun _ _ w => vecMulVec w w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ConicGDNN.Duality
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def psdAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@posSemidef_of_mem_dnnNN) (Realization psdSignature) Unit Unit where
  unitName := `D5.S3.QuadraticForms.ConicGDNN.Duality.posSemidef_of_mem_dnnNN.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Duality.psdFamily
  realizationSource := none
  generated := false
  arena := .source ⟨psdArena⟩
  objectArena := .source ⟨psdArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source psdArena ⟨psdFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize psdSignature (fun _ _ Xm => Xm) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ConicGDNN.Duality
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def symAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sym_mem_knn0) (Realization symSignature) Unit Unit where
  unitName := `D5.S3.QuadraticForms.ConicGDNN.Duality.sym_mem_knn0.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Duality.symFamily
  realizationSource := none
  generated := false
  arena := .source ⟨symArena⟩
  objectArena := .source ⟨symArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source symArena ⟨symFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize symSignature (fun _ p u => (1 / 2 : ℝ) • (vecMulVec (parameterVector p) u + vecMulVec u (parameterVector p))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ConicGDNN.Duality
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def mulAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mulVec_mem_cone) (Realization mulSignature) Unit Unit where
  unitName := `D5.S3.QuadraticForms.ConicGDNN.Duality.mulVec_mem_cone.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.ConicGDNN.Duality.mulFamily
  realizationSource := none
  generated := false
  arena := .source ⟨mulArena⟩
  objectArena := .source ⟨mulArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mulArena ⟨mulFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize mulSignature (fun _ p v => parameterMatrix p *ᵥ v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ConicGDNN.Duality
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.QuadraticForms.ConicGDNN.Duality
