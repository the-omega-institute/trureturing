import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic

/-! Source-bound whole-family observations with explicit open residuals. -/

set_option autoImplicit false
open Finset
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
attribute [local instance] _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.subgroupFintype

abbrev signature : Signature where
  Params := Σ G : Type, Group G × Fintype G
  State p := @Subgroup p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p H => @pairCount p.1 p.2.1 p.2.2 H) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def rejectedHigh : Realization signature :=
  realize signature (fun _ _ _ => 10000) (fun e => nomatch e)

abbrev C2 := Multiplicative (ZMod 2)
private theorem top_prime : (Nat.card (⊤ : Subgroup C2)).Prime := by
  simpa [Nat.card_eq_fintype_card] using Nat.prime_two
private theorem top_count : pairCount (⊤ : Subgroup C2) = 3 := by
  rw [pairCount_prime _ top_prime]
  norm_num [Nat.card_eq_fintype_card]
private theorem top_ne_bot : (⊤ : Subgroup C2) ≠ ⊥ := by
  intro h
  have hh := top_count
  rw [h,pairCount_bot] at hh
  norm_num at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨C2,inferInstance,inferInstance⟩,⊥,⊤,?_⟩
  change pairCount (⊥ : Subgroup C2) ≠ pairCount (⊤ : Subgroup C2)
  rw [pairCount_bot,top_count]
  norm_num
private theorem S3_nonabelian : ∃ a b : Equiv.Perm (Fin 3), a*b ≠ b*a := by
  refine ⟨Equiv.swap 0 1,Equiv.swap 1 2,?_⟩
  intro he
  have hh := congrArg (fun p => p 0) he
  norm_num [Equiv.Perm.mul_apply,Equiv.swap_apply_def] at hh

namespace pairCount_botAudit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], R.readout () ⟨G,inferInstance,inferInstance⟩ ⊥ = 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h PUnit inferInstance inferInstance
  change (0 : ℕ) = 1 at hh
  omega
def family : Registration arena (type_of% (@pairCount_bot)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pairCount_bot,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairCount_bot) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.pairCount_bot.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.pairCount_botAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pairCount_botAudit

namespace pairCount_ge_threeAudit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (H : Subgroup G) (_ : H ≠ ⊥) (_ : 0 < pairCount H),
      3 ≤ R.readout () ⟨G,inferInstance,inferInstance⟩ H
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h C2 inferInstance inferInstance ⊤ top_ne_bot (by rw [top_count]; omega)
  change 3 ≤ (0 : ℕ) at hh
  omega
def family : Registration arena (type_of% (@pairCount_ge_three)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pairCount_ge_three,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairCount_ge_three) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.pairCount_ge_three.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.pairCount_ge_threeAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pairCount_ge_threeAudit

namespace exists_large_fiberAudit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (_ : ∃ a b : G, a*b ≠ b*a),
      ∃ H : Subgroup G, 6 ≤ R.readout () ⟨G,inferInstance,inferInstance⟩ H
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨H,hh⟩ := @h (Equiv.Perm (Fin 3)) inferInstance inferInstance S3_nonabelian
  change 6 ≤ (0 : ℕ) at hh
  omega
def family : Registration arena (type_of% (@exists_large_fiber)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_large_fiber,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_large_fiber) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.exists_large_fiber.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.exists_large_fiberAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end exists_large_fiberAudit

namespace sum_pairCountAudit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], (∑ H : Subgroup G, R.readout () ⟨G,inferInstance,inferInstance⟩ H) = Fintype.card G^2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h PUnit inferInstance inferInstance
  norm_num [rejected,realize] at hh
def family : Registration arena (type_of% (@sum_pairCount)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_pairCount,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_pairCount) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.sum_pairCount.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.sum_pairCountAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","arg","body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sum_pairCountAudit

namespace pairCount_primeAudit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (H : Subgroup G) (_ : (Nat.card H).Prime),
      R.readout () ⟨G,inferInstance,inferInstance⟩ H = (Nat.card H)^2-1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h C2 inferInstance inferInstance ⊤ top_prime
  norm_num [rejected,realize,Nat.card_eq_fintype_card] at hh
def family : Registration arena (type_of% (@pairCount_prime)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pairCount_prime,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairCount_prime) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.pairCount_prime.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.pairCount_primeAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end pairCount_primeAudit

namespace exists_prime_fiberAudit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (_ : 1 < Fintype.card G),
      ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ Nat.card H = p ∧
        R.readout () ⟨G,inferInstance,inferInstance⟩ H = p^2-1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p,H,hp,_,hh⟩ := @h C2 inferInstance inferInstance (by norm_num [C2])
  change (0 : ℕ) = p^2-1 at hh
  have hs : 4 ≤ p^2 := by nlinarith [hp.two_le]
  omega
def family : Registration arena (type_of% (@exists_prime_fiber)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_prime_fiber,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_prime_fiber) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.exists_prime_fiber.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.exists_prime_fiberAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg","body","arg","arg","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end exists_prime_fiberAudit

namespace sqrt_sum_le_deficitAudit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G], ∀ (_ : ∃ a b : G, a*b ≠ b*a),
      (∑ H : Subgroup G, Real.sqrt (R.readout () ⟨G,inferInstance,inferInstance⟩ H)) ≤
        (Fintype.card G : ℝ)^2 - (positiveFibers (G := G)).card
private theorem rejected_law : ¬ arena.Law rejectedHigh := by
  intro h
  have hh := @h (Equiv.Perm (Fin 3)) inferInstance inferInstance S3_nonabelian
  change (∑ _ : Subgroup (Equiv.Perm (Fin 3)), Real.sqrt (10000 : ℝ)) ≤ _ at hh
  have hs : Real.sqrt (10000 : ℝ) = 100 := by
    rw [show (10000 : ℝ) = (100 : ℝ)^2 by norm_num,Real.sqrt_sq_eq_abs]
    norm_num
  rw [hs] at hh
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hn : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by norm_num [Fintype.card_perm]
  rw [hn] at hh
  have ht : (0 : ℝ) ≤ (positiveFibers (G := Equiv.Perm (Fin 3))).card := Nat.cast_nonneg _
  have hk : (1 : ℝ) ≤ Fintype.card (Subgroup (Equiv.Perm (Fin 3))) := by
    exact_mod_cast (Fintype.card_pos (α := Subgroup (Equiv.Perm (Fin 3))))
  norm_num at hh
  linarith

def family : Registration arena (type_of% (@sqrt_sum_le_deficit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sqrt_sum_le_deficit,rejectedHigh,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedHigh,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sqrt_sum_le_deficit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.sqrt_sum_le_deficit.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers.sqrt_sum_le_deficitAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","arg","body","arg","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sqrt_sum_le_deficitAudit

end Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
