import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount
open _root_.D5.S3.ConceptDynamics.InformationEscape

def signature : DependentFamily.Signature where
  Params := ℕ
  State := Matrix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ M => Admissible M) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ n : ℕ, 1 ≤ n →
    32 * (Nat.card {M : Matrix n // R.readout () n M} : ℤ) =
      2 * (n : ℤ) ^ 3 + 11 * (n : ℤ) ^ 2 + 31 * n + 27 +
        ((n : ℤ) ^ 2 + n + 5) * (-1 : ℤ) ^ n

abbrev sourceScope := type_of% (@result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1 (by omega)
  change 32 * (Nat.card {M : Matrix 1 // False} : ℤ) =
    2 * (1 : ℤ) ^ 3 + 11 * (1 : ℤ) ^ 2 + 31 * 1 + 27 +
      ((1 : ℤ) ^ 2 + 1 + 5) * (-1 : ℤ) ^ 1 at h1
  norm_num at h1

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, (fun _ _ => false), (fun _ _ => true), ?_⟩
    change Admissible (fun (_ : Fin 1) (_ : Fin 2) => false) ≠
      Admissible (fun (_ : Fin 1) (_ : Fin 2) => true)
    have hz : Admissible (fun (_ : Fin 1) (_ : Fin 2) => false) := by
      refine ⟨?_, Or.inl (fun _ => rfl), ?_⟩
      · intro x y hxy
        simp [rank]
      · intro k hk hkn j hj hj2
        simp [ones, cell]
    have ho : ¬ Admissible (fun (_ : Fin 1) (_ : Fin 2) => true) := by
      intro h
      have hh := h.2.2 1 le_rfl le_rfl 1 le_rfl (by omega)
      norm_num [ones, cell, Finset.sum_range_succ] at hh
    intro he
    exact ho (he ▸ hz)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ M => Admissible M) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (@Matrix)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount
    definition := some {
      owner := `D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount
      name := `D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount.Arrays
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.PermutationArrays.EtiennePrefixCount
