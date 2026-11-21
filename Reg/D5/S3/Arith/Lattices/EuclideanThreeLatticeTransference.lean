import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference
import Mathlib.Tactic

/-! Source registration for the squared covering error. -/

namespace Reg.D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference

open Module LeanInformationAudit
open scoped InnerProductSpace RealInnerProductSpace
open _root_.D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference (exists_dual_covering)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ r => r ^ (2 : ℕ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin 3)))
    [DiscreteTopology L] [IsZLattice ℝ L],
    ∃ y ∈ LinearMap.BilinForm.dualSubmodule (innerₗ (EuclideanSpace ℝ (Fin 3))) L, y ≠ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), ∃ v ∈ L,
        R.readout () () ‖x - v‖ * ‖y‖ ^ 2 ≤ 11 / 12

private abbrev E := EuclideanSpace ℝ (Fin 3)
private abbrev standardBasis : Basis (Fin 3) ℝ E := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
private abbrev standardLattice : Submodule ℤ E := Submodule.span ℤ (Set.range standardBasis)

private theorem standard_dual_norm_ge_one {y : E}
    (hy : y ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) standardLattice) (hy0 : y ≠ 0) : 1 ≤ ‖y‖ := by
  classical
  have hcoord : ∃ i : Fin 3, y i ≠ 0 := by
    by_contra! h
    apply hy0
    apply PiLp.ext
    intro i
    simpa using h i
  obtain ⟨i, hi⟩ := hcoord
  have hmem : standardBasis i ∈ standardLattice := Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp
    ((LinearMap.BilinForm.mem_dualSubmodule (innerₗ E)).mp hy (standardBasis i) hmem)
  have hcast : (m : ℝ) = y i := by
    change (m : ℝ) = inner ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i) at hm
    simpa only [EuclideanSpace.inner_basisFun_real] using hm
  have hm0 : m ≠ 0 := by
    intro hz
    apply hi
    rw [← hcast, hz, Int.cast_zero]
  have hone : (1 : ℝ) ≤ |y i| := by
    rw [← hcast, ← Int.cast_abs]
    exact_mod_cast (Int.one_le_abs hm0)
  exact hone.trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let : DiscreteTopology standardLattice := inferInstanceAs
    (DiscreteTopology (Submodule.span ℤ (Set.range standardBasis)))
  let : IsZLattice ℝ standardLattice := inferInstanceAs
    (IsZLattice ℝ (Submodule.span ℤ (Set.range standardBasis)))
  obtain ⟨y, hy, hy0, hcover⟩ := h standardLattice
  obtain ⟨v, hv, hbound⟩ := hcover 0
  change (1 : ℝ) * ‖y‖ ^ 2 ≤ 11 / 12 at hbound
  have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
    (standard_dual_norm_ge_one hy hy0) 2
  linarith only [hsquare, hbound]

def family : Registration arena (type_of% (@exists_dual_covering)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_dual_covering, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ (2 : ℕ) ≠ (1 : ℝ) ^ (2 : ℕ)
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_dual_covering) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference.exists_dual_covering.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => r ^ (2 : ℕ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "body",
        "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference
