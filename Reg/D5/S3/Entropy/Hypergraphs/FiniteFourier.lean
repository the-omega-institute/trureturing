import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.Hypergraphs.FiniteFourier
namespace Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.Hypergraphs.FiniteFourier
open LeanInformationAudit
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace finite_mass_le_one
universe u
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℕ) (k : ℕ),
    R.readout () () (((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω) 1
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (Ω := ULift.{u} Unit) (fun _ => 0) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh
def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_mass_le_one.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_mass_le_one.{u},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_mass_le_one.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_mass_le_one.unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_mass_le_one.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.FiniteFourier
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end finite_mass_le_one

namespace finite_entropy_lower
universe u
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℕ) (n : ℕ) (_hX : ∀ ω, X ω ≤ n) (C : ℝ)
    (_hC : 0 < C)
    (_hbound : ∀ k, ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) /
      Fintype.card Ω ≤ C),
    R.readout () () (-Real.logb 2 C) (∑ k ∈ Finset.range (n + 1),
      let p := ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω;
      -p * Real.logb 2 p)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (Ω := ULift.{u} Unit) (fun _ => 0) 0 (by simp) 1 (by norm_num)
    (fun k => finite_mass_le_one (fun _ : ULift.{u} Unit => 0) k)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh
def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_entropy_lower.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_entropy_lower.{u},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_entropy_lower.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_entropy_lower.unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_entropy_lower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.FiniteFourier
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end finite_entropy_lower

namespace finite_uniform_mass_bound
universe u
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℤ) (k : ℤ) {A : ℝ} (_hA : R.readout () () 0 A)
    (_hφ : ∀ t : ℝ,
      ‖(∑ ω : Ω, Complex.exp ((X ω : ℂ) * Complex.I * (t : ℂ))) /
        (Fintype.card Ω : ℂ)‖ ≤ Real.exp (-A * Real.sin (t / 2) ^ 2)),
    (((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω) ≤
      Real.sqrt Real.pi / (2 * Real.sqrt A)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hφ (t : ℝ) :
      ‖(∑ ω : ULift.{u} Unit, Complex.exp (((0 : ℤ) : ℂ) * Complex.I * (t : ℂ))) /
        (Fintype.card (ULift.{u} Unit) : ℂ)‖ ≤ Real.exp (-(-1 : ℝ) * Real.sin (t / 2) ^ 2) := by
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_ulift, Fintype.card_unit, one_smul, Nat.cast_one,
      div_one, norm_one, neg_neg, one_mul]
    exact Real.one_le_exp (sq_nonneg _)
  have hb := h (Ω := ULift.{u} Unit) (fun _ => 0) 0 (A := -1) trivial hφ
  norm_num [Real.sqrt_eq_zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)] at hb
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
  exact (lt_irrefl (1 : ℝ)) hh
def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_uniform_mass_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_uniform_mass_bound.{u},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_uniform_mass_bound.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_uniform_mass_bound.unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier.finite_uniform_mass_bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.FiniteFourier
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end finite_uniform_mass_bound

end
end Reg.D5.S3.Entropy.Hypergraphs.FiniteFourier
