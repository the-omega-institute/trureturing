import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.Hypergraphs.FiniteFiber
namespace Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.Hypergraphs.FiniteFiber
open LeanInformationAudit
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace block_average_product
universe u v w
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {J : Type v} [Fintype ι] [Fintype J] [DecidableEq ι]
    (β : ι → Type w) [∀ i, Fintype (β i)] (D : J → Finset ι)
    [∀ i, Nonempty (β i)] (_hD : ∀ j k, j ≠ k → Disjoint (D j) (D k))
    (F : ∀ j, (∀ i : D j, β i.val) → ℝ),
    R.readout () () ((∑ o : ∀ i, β i, ∏ j, F j (fun i => o i.val)) /
        (Fintype.card (∀ i, β i) : ℝ))
      (∏ j, ((∑ b : ∀ i : D j, β i.val, F j b) /
        (Fintype.card (∀ i : D j, β i.val) : ℝ)))
private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} Unit) (J := ULift.{v} Unit)
    (fun _ => ULift.{w} Unit) (fun _ => ∅) (by simp) (fun _ _ => 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hh
def family : Registration arena.{u,v,w}
    (type_of% (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.block_average_product.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.block_average_product.{u,v,w},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.block_average_product.{u,v,w}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.block_average_product.unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.block_average_product.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.FiniteFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end block_average_product

namespace two_block_event_average
universe u v
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [DecidableEq ι]
    (β : ι → Type v) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    [∀ i, DecidableEq (β i)]
    (L R' : Finset ι) (_hLR : Disjoint L R')
    (u : ∀ i : L, β i.val) (v : ∀ i : R', β i.val)
    (A B z : ℝ)
    (_ha : (∑ a : ∀ i : L, β i.val,
        if (∀ i : L, a i ≠ u i) then (1 : ℝ) else 0) /
        Fintype.card (∀ i : L, β i.val) = A)
    (_hb : (∑ b : ∀ i : R', β i.val,
        if (∀ i : R', b i ≠ v i) then (1 : ℝ) else 0) /
        Fintype.card (∀ i : R', β i.val) = B),
    R.readout () () ((∑ o : ∀ i : (L ∪ R' : Finset ι), β i.val,
      if ((∀ i : L,
            o ⟨i.val, Finset.mem_union_left R' i.property⟩ ≠ u i) ∧
          ¬ (∀ i : R',
            o ⟨i.val, Finset.mem_union_right L i.property⟩ ≠ v i))
        then z else 1) /
      Fintype.card (∀ i : (L ∪ R' : Finset ι), β i.val))
        (1 - A * (1 - B) + A * (1 - B) * z)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} Unit) (fun _ => ULift.{v} Unit) ∅ ∅ (by simp)
    (fun i => (Finset.notMem_empty i.val i.property).elim)
    (fun i => (Finset.notMem_empty i.val i.property).elim) 1 1 0
    (by simp) (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hh
def family : Registration arena.{u,v}
    (type_of% (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.two_block_event_average.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.two_block_event_average.{u,v},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.two_block_event_average.{u,v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.two_block_event_average.unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.two_block_event_average.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.FiniteFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end two_block_event_average

namespace double_uniform_mean_norm_le
universe u v
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B → ℂ) (W : A → B → ℝ)
    (_h : ∀ a b, ‖(∑ b' : B, f a b') / (Fintype.card B : ℂ)‖ ≤ W a b),
    R.readout () () (‖(∑ x : A × B, f x.1 x.2) / (Fintype.card (A × B) : ℂ)‖)
      ((∑ x : A × B, W x.1 x.2) / (Fintype.card (A × B) : ℝ))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (A := ULift.{u} Unit) (B := ULift.{v} Unit)
    (fun _ _ => 0) (fun _ _ => 0) (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hh
def family : Registration arena.{u,v}
    (type_of% (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.double_uniform_mean_norm_le.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.double_uniform_mean_norm_le.{u,v},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.double_uniform_mean_norm_le.{u,v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.double_uniform_mean_norm_le.unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.double_uniform_mean_norm_le.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.FiniteFiber
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
end double_uniform_mean_norm_le

namespace split_fiber_average
universe u v
abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {V : Type v} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset ι)
    (_hS : ∀ i j : S, i ≠ j → Disjoint (E i.val) (E j.val))
    (r : ℕ) (_hr : 0 < r) (_hcard : ∀ i, (E i).card = r)
    (a : ∀ i : {i // i ∉ S}, ↥(E i.val)) (z : ℂ),
    R.readout () () ((∑ b : ∀ i : S, ↥(E i.val),
      Complex.exp (z * (Finset.univ.image
        (fun i => (splitCompletion E S a b i).val)).card)) /
      (Fintype.card (∀ i : S, ↥(E i.val)) : ℂ))
    (Complex.exp (z * (splitRevealedImage E S a).card) * ∏ i : S,
      (1 - (((E i.val) \ splitRevealedImage E S a).card : ℂ) / r +
        (((E i.val) \ splitRevealedImage E S a).card : ℂ) / r * Complex.exp z))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} Unit) (V := ULift.{v} Unit)
    (fun _ => {⟨()⟩}) ∅ (by simp) 1 (by norm_num) (by simp)
    (fun _ => ⟨⟨()⟩, by simp⟩) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hh
def family : Registration arena.{u,v}
    (type_of% (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.split_fiber_average.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.split_fiber_average.{u,v},
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.Hypergraphs.FiniteFiber.split_fiber_average.{u,v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.split_fiber_average.unit
  realizationName := `Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber.split_fiber_average.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.Hypergraphs.FiniteFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end split_fiber_average

end
end Reg.D5.S3.Entropy.Hypergraphs.FiniteFiber
