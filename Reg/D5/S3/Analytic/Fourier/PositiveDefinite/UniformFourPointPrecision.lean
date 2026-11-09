import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Matrix
open scoped Interval ComplexOrder
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision

namespace Reg.D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision

namespace Outer
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ × ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ v t => v t.1 * v t.2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {v h g : ℝ → ℝ} {δ : ℝ}, CuspControl v h g δ →
    ∀ {p q r : ℝ}, 0 < p → 0 < q → 0 < r → p+q+r ≤ δ →
    R.readout () v (p,r) ≤ (64*(1+Real.log 3)^2)*(p+q+r)*(L (p+q+r))^2*weight v p q r
theorem bridge : (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.uniform_outer_deficit_bound) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.uniform_outer_deficit_bound) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.uniform_outer_deficit_bound, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep

end Outer

namespace Integrals
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ g t => g t) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {v h g : ℝ → ℝ} {δ p q r : ℝ}, CuspControl v h g δ →
    0 < p → 0 < q → 0 < r → p+q+r ≤ δ →
    (IntervalIntegrable (fun u => ∫ w in (0 : ℝ)..q, R.readout () g (u+w)) volume 0 p ∧
      psi v p q = ∫ u in (0 : ℝ)..p, ∫ w in (0 : ℝ)..q, R.readout () g (u+w)) ∧
    (IntervalIntegrable (fun u => ∫ w in (0 : ℝ)..r, R.readout () g (q+u+w)) volume 0 p ∧
      interaction v p q r = ∫ u in (0 : ℝ)..p, ∫ w in (0 : ℝ)..r, R.readout () g (q+u+w))
theorem bridge : (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.deficit_integrals) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.deficit_integrals) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.deficit_integrals, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep

end Integrals

namespace RealPosDef
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℝ) (fun n => Matrix (Fin n) (Fin n) ℝ)
def actual : Realization signature := realize signature (fun _ _ A => A) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ},
    Matrix.PosDef (fun i j => (A i j : ℂ)) → Matrix.PosDef (R.readout () n A)
theorem bridge : (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.real_posDef_of_complex) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.real_posDef_of_complex) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.real_posDef_of_complex, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep


def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Matrix.PosDef (fun i j => ((1 : Matrix (Fin 1) (Fin 1) ℝ) i j : ℂ)) := by
    have he : (fun i j => ((1 : Matrix (Fin 1) (Fin 1) ℝ) i j : ℂ)) =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      ext i j
      fin_cases i
      fin_cases j
      norm_num [Matrix.one_apply]
    rw [he]
    exact Matrix.PosDef.one
  have hh := (h (A := 1) hp).diag_pos (i := (0 : Fin 1))
  change (0 : ℝ) < 0 at hh
  exact (lt_irrefl 0 hh)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have hh := congrArg (fun A => A 0 0) h
  change (0 : ℝ) = 1 at hh
  exact zero_ne_one hh
def closedEvidence := evidence rejected rejected_law actual_dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.real_posDef_of_complex) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.real_posDef_of_complex.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.RealPosDef.closedEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨closedEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RealPosDef

namespace Cross
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ z t => schurCross t z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ k d a b c e f : ℝ, R.readout () (d,a,b,c,e,f) k =
    f - ((!![a,b] : Matrix (Fin 1) (Fin 2) ℝ) * (!![k,d;d,k])⁻¹ *
      (!![c;e] : Matrix (Fin 2) (Fin 1) ℝ)) 0 0
theorem bridge : (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.schurCross_eq_matrix) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.schurCross_eq_matrix) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.schurCross_eq_matrix, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep


def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 0 0 0 0 1
  norm_num [rejected, realize, Matrix.mul_apply, Fin.sum_univ_two] at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(0,1,0,1,0,0), 1, 2, ?_⟩
  norm_num [actual, realize, schurCross]
def closedEvidence := evidence rejected rejected_law actual_dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.schurCross_eq_matrix) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.schurCross_eq_matrix.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.Cross.closedEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨closedEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z t => schurCross t z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision
    definition := none
    coordinates := #[1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cross

namespace Endpoint
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ((ℝ → ℝ) × ℝ) (fun _ => ℝ × ℝ × ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ z t => schurCross z.2 (z.2-z.1 t.2.1) (z.2-z.1 t.1)
    (z.2-z.1 (t.1+t.2.1)) (z.2-z.1 (t.2.1+t.2.2)) (z.2-z.1 t.2.2)
    (z.2-z.1 (t.1+t.2.1+t.2.2))) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {v h g : ℝ → ℝ} {δ₀ k : ℝ}, CuspControl v h g δ₀ → 0 < k →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ p q r : ℝ,
      0 < p → 0 < q → 0 < r → p+q+r ≤ δ → 0 < R.readout () (v,k) (p,q,r)
theorem bridge : (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.exists_uniform_endpoint_cross_pos) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.exists_uniform_endpoint_cross_pos) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.exists_uniform_endpoint_cross_pos, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep

end Endpoint

namespace Ratio
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ((ℝ → ℝ) × ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ z t => psi z.1 z.2 t / z.1 t) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {v h g : ℝ → ℝ} {δ p : ℝ}, CuspControl v h g δ →
    StrictConvexOn ℝ (Ioo 0 δ) (fun u => Real.log (h u)) → 0 < p →
    StrictAntiOn (R.readout () (v,p)) (Ioc 0 (δ-p))
theorem bridge : (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.strictAntiOn_deficit_ratio) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.strictAntiOn_deficit_ratio) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.strictAntiOn_deficit_ratio, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep

end Ratio

namespace Precision
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ((ℝ → ℝ) × ℝ) (fun _ => Fin 4 → ℝ) (fun _ => Matrix (Fin 4) (Fin 4) ℝ)
def actual : Realization signature :=
  realize signature (fun _ z x => (fun i j => z.2-z.1 |x i-x j|)⁻¹) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {v h g : ℝ → ℝ} {δ₀ k : ℝ}, CuspControl v h g δ₀ → 0 < k →
    (∀ t ∈ Icc 0 δ₀, 0 < k-v t) →
    StrictConvexOn ℝ (Icc 0 δ₀) (fun t => Real.log (k-v t)) →
    StrictConvexOn ℝ (Ioo 0 δ₀) (fun t => Real.log (h t)) →
    (∀ x : Fin 4 → ℝ, Function.Injective x → (∀ i j, |x i-x j| ≤ δ₀) →
      Matrix.PosDef (fun i j => k-v |x i-x j|)) →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ x : Fin 4 → ℝ,
      Function.Injective x → (∀ i j, |x i-x j| ≤ δ) →
      ∀ i j : Fin 4, i ≠ j → R.readout () (v,k) x i j < 0
theorem bridge : (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.exists_uniform_four_point_precision) ↔ arena.Law actual := Iff.rfl

def evidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdep : ObservationalDependence signature actual) :
    Registration arena (type_of% @D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.exists_uniform_four_point_precision) where
  actual := actual
  bridge := bridge
  variation := ⟨@D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision.exists_uniform_four_point_precision, bad, hbad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad
  dependence := hdep

end Precision

end Reg.D5.S3.Analytic.Fourier.PositiveDefinite.UniformFourPointPrecision
