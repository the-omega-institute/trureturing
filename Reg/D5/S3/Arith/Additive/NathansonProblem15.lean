import D5.S3.Arith.Additive.NathansonProblem15
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the sumset in the prescribed-start equivalence. -/

namespace Reg.D5.S3.Arith.Additive.NathansonProblem15

open _root_.D5.S3.Arith.NathansonProblem15
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

set_option autoImplicit false

private abbrev signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun _ => Finset ℤ) (fun _ => Set ℤ)

private def actual : Realization signature :=
  realize signature (fun _ h A => h • (A : Set ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h q n : ℕ) (N : ℤ), 2 ≤ h → 2 ≤ q → 1 ≤ n → (n : ℤ) + 2 ≤ N →
    ∀ c : Fin q → ℤ, (∀ i j : Fin q, j.val = i.val + 1 → N ≤ c j - c i) →
      ∃ A : Finset ℤ,
        A.card ≤ 2 * q * (n + 1) ∧
        (∀ x : ℤ, Set.Icc x (x + (n : ℤ)) ⊆ R.readout () h A ↔
          ∃ i : Fin q, x = c i) ∧
        (∀ x : ℤ, Set.Icc x (x + 1) ⊆ h • (A : Set ℤ) ↔
          ∃ i : Fin q,
            Set.Icc x (x + 1) ⊆ Set.Icc (c i) (c i + (n : ℤ)) ∧
              Set.Icc (c i) (c i + (n : ℤ)) ⊆ h • (A : Set ℤ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let c (i : Fin 2) : ℤ := 3 * i.val
  have gap (i j : Fin 2) (hij : j.val = i.val + 1) : (3 : ℤ) ≤ c j - c i := by
    dsimp [c]
    omega
  obtain ⟨A, _, starts, _⟩ := law 2 2 1 3 (by decide) (by decide) (by decide) (by decide) c gap
  have covered := (starts (c 0)).mpr ⟨0, rfl⟩
  exact covered (show c 0 ∈ Set.Icc (c 0) (c 0 + (1 : ℤ)) from ⟨le_rfl, by omega⟩)

def family : Registration arena (type_of% (@nathanson_problem15)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nathanson_problem15, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨2, {0}, {1}, ?_⟩
    change (2 : ℕ) • (({0} : Finset ℤ) : Set ℤ) ≠ (2 : ℕ) • (({1} : Finset ℤ) : Set ℤ)
    simp only [Finset.coe_singleton, Set.nsmul_singleton]
    intro heq
    have hz : (0 : ℤ) ∈ ({(2 : ℕ) • (0 : ℤ)} : Set ℤ) := by simp
    rw [heq] at hz
    norm_num at hz

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@nathanson_problem15) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.NathansonProblem15.nathanson_problem15.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.NathansonProblem15.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h A => h • (A : Set ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.NathansonProblem15
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Additive.NathansonProblem15
