import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
import Reg.Support.DependentFamily

/-! The per-coordinate fixed count depends on the parity of the multiplicities. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → Fin 2 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin (n + 2) → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b i =>
    2 * (∑ p, ∑ q, ∑ c, if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0))
    (fun e => nomatch e)

def alwaysOne : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k : ℕ} (b : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → Fin 2 → ℕ),
    (∀ p c, ∑ q, b p q c = k) →
    (∀ q, ∑ p, (b p q 0 + b p q 1) = 2 * k) →
    (∀ p q, p.val ≠ 1 → b p q 0 = b p q 1) →
    RealizableSeedCounts n k (R.readout () n b)

private theorem always_one_fails : ¬ arena.Law alwaysOne := by
  intro law
  obtain ⟨S, _, _, _, size, _, _, counts⟩ :=
    law (n := 0) (k := 0) (fun _ _ _ => 0) (by simp) (by simp) (by simp)
  have empty : IsEmpty S := Fintype.card_eq_zero_iff.mp (by simpa using size)
  letI := empty
  have h := counts (0 : Fin 2)
  change fixedSeedCount (n := 0) S 0 = 1 at h
  simp [fixedSeedCount] at h

private theorem all_one_mass_nonzero :
    actual.readout () 0 (fun _ _ _ => 1) ≠ actual.readout () 0 (fun _ _ _ => 0) := by
  intro same
  let p : ParityClass 2 0 := ⟨fun _ => 1, by rw [parity, Fin.sum_univ_two]; rfl⟩
  let q : ParityClass 2 1 := ⟨Fin.cons 1 (fun _ => 0), by rw [parity, Fin.sum_univ_two]; rfl⟩
  have observed := congrFun same 0
  have bound : 1 ≤
      ∑ x : ParityClass 2 0, ∑ y : ParityClass 2 1, ∑ _c : Fin 2,
        if x.val (0 : Fin 2) = 1 ∧ y.val (0 : Fin 2) = 1 then 1 % 2 else 0 := by
    have cell : 1 ≤ ∑ c : Fin 2,
        (if p.val (0 : Fin 2) = 1 ∧ q.val (0 : Fin 2) = 1 then 1 % 2 else 0) := by
      simp [p, q]
    let term (x : ParityClass 2 0) (y : ParityClass 2 1) : ℕ :=
      ∑ _c : Fin 2, if x.val (0 : Fin 2) = 1 ∧ y.val (0 : Fin 2) = 1 then 1 % 2 else 0
    have a : term p q ≤ ∑ y, term p y :=
      single_le_sum (f := term p) (fun _ _ => Nat.zero_le _) (mem_univ q)
    have b : (∑ y, term p y) ≤ ∑ x, ∑ y, term x y :=
      single_le_sum (f := fun x => ∑ y, term x y) (fun _ _ => Nat.zero_le _) (mem_univ p)
    exact cell.trans (a.trans b)
  have zero : actual.readout () 0 (fun _ _ _ => 0) 0 = 0 := by
    simp [actual, realize]
  have positive : 0 < actual.readout () 0 (fun _ _ _ => 1) 0 := by
    exact Nat.mul_pos (by decide) bound
  rw [observed, zero] at positive
  exact (Nat.lt_irrefl 0) positive

def family : Registration arena (type_of% (@realize_coloured_table)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realize_coloured_table, alwaysOne, always_one_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysOne, ?_, rfl, always_one_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨0, fun _ _ _ => 1, fun _ _ _ => 0, all_one_mass_nonzero⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@realize_coloured_table) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization.counts
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b i =>
    2 * (∑ p, ∑ q, ∑ c, if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
