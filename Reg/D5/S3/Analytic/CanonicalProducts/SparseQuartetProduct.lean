import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
import Reg.Support.DependentFamily

/-! Source-bound interventions on actual comparisons, equality or product convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

open Filter
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct

private def emptyData : Data (ULift.{u} Empty) where
  β i := nomatch i.down
  γ i := nomatch i.down
  m i := nomatch i.down
  beta_pos i := nomatch i.down
  beta_lt_one i := nomatch i.down
  gamma_pos i := nomatch i.down
  reciprocal_summable := by simp

namespace coefficient_norm_budget

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} (S : Data I),
    Summable (fun k : Slot S.m => ‖coefficient S.β S.γ S.m k‖) ∧
    R.readout () () (∑' k : Slot S.m, ‖coefficient S.β S.γ S.m k‖)
      (4 * ∑' i : I, (S.m i : ℝ) / S.γ i)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (@h (ULift.{u} Empty) emptyData).2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hh

def source_registration : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.coefficient_norm_budget.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.coefficient_norm_budget.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.coefficient_norm_budget.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.coefficient_norm_budget.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.coefficient_norm_budget.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end coefficient_norm_budget

namespace actual_product_hasProd

abbrev signature : Signature.{u+1,u,0,u,0} where
  Params := Type u
  State I := I → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := ℂ → SummationFilter I → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ f a L => HasProd f a L) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} (S : Data I) (z : ℂ),
    R.readout () I (fun i : I => C (S.β i) (S.γ i) z ^ S.m i)
      (∏' k : Slot S.m, (1 + z * coefficient S.β S.γ S.m k)) (SummationFilter.unconditional I)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Empty) emptyData 0

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ => (1 : ℂ)), (fun _ => (0 : ℂ)), ?_⟩
  intro h
  have hp : HasProd (fun _ : ULift.{u} Unit => (1 : ℂ)) 1 := by
    simpa using hasProd_fintype (fun _ : ULift.{u} Unit => (1 : ℂ))
  have hz : HasProd (fun _ : ULift.{u} Unit => (0 : ℂ)) 0 := by
    simpa using hasProd_fintype (fun _ : ULift.{u} Unit => (0 : ℂ))
  have hb : HasProd (fun _ : ULift.{u} Unit => (0 : ℂ)) 1 :=
    (congrFun (congrFun h 1) (SummationFilter.unconditional (ULift.{u} Unit))).mp hp
  exact zero_ne_one (hz.unique hb)

def source_registration : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_hasProd.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_hasProd.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_hasProd.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_hasProd.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_hasProd.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ f a L => HasProd f a L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end actual_product_hasProd

namespace actual_product_analytic

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} (S : Data I),
    (∀ z : ℂ, Multipliable (fun i : I => C (S.β i) (S.γ i) z ^ S.m i)) ∧
    Differentiable ℂ S.product ∧
    R.readout () () (S.product 0) 1 ∧ S.product 1 = 1 ∧
    (∀ z : ℂ, S.product (1 - z) = S.product z) ∧
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧
      ∀ z : ℂ, ‖S.product z‖ ≤ A * Real.exp (ε * ‖z‖)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (@h (ULift.{u} Empty) emptyData).2.2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hh

def source_registration : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_analytic.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_analytic.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_analytic.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_analytic.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_analytic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end actual_product_analytic

namespace actual_product_real

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} (S : Data I),
    (∀ x : ℝ, Multipliable (fun i : I => realFactor (S.β i) (S.γ i) x ^ S.m i)) ∧
    (∀ x : ℝ, S.product (x : ℂ) = (S.realProduct x : ℂ)) ∧
    (∀ x : ℝ, 1 ≤ x → R.readout () () 1 (S.realProduct x)) ∧
    Tendsto (fun x : ℝ => Real.log (S.realProduct x) / x) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (@h (ULift.{u} Empty) emptyData).2.2.1 1 le_rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hh

def source_registration : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_real.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_real.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_real.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_real.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.actual_product_real.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end actual_product_real

namespace difference_analytic

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} {J : Type v} (S : Data I) (T : Data J) (b : ℂ),
    Differentiable ℂ (difference S T b) ∧
    (∀ z : ℂ, R.readout () () (difference S T b (1 - z)) (difference S T b z)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧
      ∀ z : ℂ, ‖difference S T b z‖ ≤ A * Real.exp (ε * ‖z‖)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  exact (@h (ULift.{u} Empty) (ULift.{v} Empty) emptyData emptyData 0).2.1 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hh

def source_registration : Registration arena.{u, v} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.difference_analytic.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.difference_analytic.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.difference_analytic.{u, v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.difference_analytic.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.difference_analytic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end difference_analytic

namespace reflected_difference_zero

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℂ → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} {J : Type v} (S : Data I) (T : Data J)
    (b : ℂ)
    (hlim : Tendsto (fun x : ℝ => difference S T b (x : ℂ)) atTop (𝓝 0)),
    R.readout () () (difference S T b) 0

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  apply @h (ULift.{u} Empty) (ULift.{v} Empty) emptyData emptyData 0
  simpa [difference, emptyData, Data.product, actualProduct] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ → ℂ), (1 : ℂ → ℂ), ?_⟩
  intro h
  have hh : (1 : ℂ → ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero (congrFun hh 0)

def source_registration : Registration arena.{u, v} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.reflected_difference_zero.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.reflected_difference_zero.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.reflected_difference_zero.{u, v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.reflected_difference_zero.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.reflected_difference_zero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end reflected_difference_zero

namespace fast_ratio_rigidity

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} {J : Type v} (S : Data I) (T : Data J)
    (a b : ℂ) (Cerr c : ℝ) (hCerr : 0 ≤ Cerr) (hc : 0 < c)
    (herror : ∀ᶠ x : ℝ in atTop,
      ‖Complex.exp (a * (x : ℂ) + b) * S.product (x : ℂ) / T.product (x : ℂ) - 1‖ ≤
        Cerr * Real.exp (-c * x)),
    R.readout () () a 0 ∧ Complex.exp b = 1 ∧ S.product = T.product

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Empty) (ULift.{v} Empty) emptyData emptyData
    0 0 0 1 le_rfl zero_lt_one (by simp [emptyData, Data.product, actualProduct])
  exact hh.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hh

def source_registration : Registration arena.{u, v} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.fast_ratio_rigidity.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.fast_ratio_rigidity.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.fast_ratio_rigidity.{u, v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.fast_ratio_rigidity.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct.fast_ratio_rigidity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end fast_ratio_rigidity

end Reg.D5.S3.Analytic.CanonicalProducts.SparseQuartetProduct
