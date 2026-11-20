import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
import Reg.Support.SingleDependentReadout

/-! The freeness law depends on the denominator used in the prime-divisibility test. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness

open _root_.D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

noncomputable section

universe u v

private abbrev Profile (I : Type*) [Fintype I] (m : ℕ) :=
  {p : I → ℕ // ∑ i, p i = m}

private abbrev relabel {I : Type*} [Fintype I] {m : ℕ} (g : Equiv.Perm I) (p : Profile I m) :
    Profile I m :=
  ⟨fun i => p.val (g⁻¹ i), (Equiv.sum_comp (g⁻¹ : Equiv.Perm I) p.val).trans p.property⟩

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} {S : Type v} [Fintype I] [DecidableEq I] [Fintype S]
    [MulAction (Equiv.Perm I) S] {m : ℕ},
    (∀ p : ℕ, p.Prime → p ≤ Fintype.card I → p ∣ R.readout () () m) →
    ∀ (w : S → ℝ), (∀ s, 0 < w s) → ∀ (f : Profile I m → S → I),
    (∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ)) →
    (∀ g p s, f (relabel g p) (g • s) = g (f p s)) →
    ∀ s : S, MulAction.stabilizer (Equiv.Perm I) s = ⊥

private theorem one_hot {I : Type*} [Fintype I] (p : Profile I 1) :
    ∃! i, p.val i = 1 := by
  classical
  have nonzero : (∑ i, p.val i) ≠ 0 := by rw [p.property]; decide
  obtain ⟨i, hi, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  have atMost (j : I) : p.val j ≤ 1 := by
    calc
      p.val j ≤ ∑ a, p.val a :=
        Finset.single_le_sum (fun a _ => Nat.zero_le (p.val a)) (Finset.mem_univ j)
      _ = 1 := p.property
  have one : p.val i = 1 := by
    have := atMost i
    omega
  refine ⟨i, one, ?_⟩
  intro j hj
  by_contra ne
  have bound : p.val j ≤ ∑ a ∈ (Finset.univ : Finset I).erase i, p.val a :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (p.val a))
      (Finset.mem_erase.mpr ⟨ne, Finset.mem_univ j⟩)
  have total := (Finset.sum_erase_add Finset.univ p.val hi).trans p.property
  omega

private def chosen {I : Type*} [Fintype I] (p : Profile I 1) : I := (one_hot p).choose

private theorem chosen_value {I : Type*} [Fintype I] (p : Profile I 1) :
    p.val (chosen p) = 1 := (one_hot p).choose_spec.1

private theorem chosen_unique {I : Type*} [Fintype I] (p : Profile I 1)
    (i : I) (h : p.val i = 1) :
    i = chosen p := (one_hot p).choose_spec.2 i h

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let I := ULift.{u} (Fin 2)
  let S := ULift.{v} Unit
  letI : MulAction (Equiv.Perm I) S :=
    { smul := fun _ s => s, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
  let f (p : Profile I 1) (_ : S) : I := chosen p
  have mass (p : Profile I 1) (i : I) :
      ∑ s : S, (if f p s = i then (1 : ℝ) else 0) = (p.val i : ℝ) := by
    have sum := p.property
    have le := Finset.single_le_sum (s := Finset.univ) (f := p.val)
      (fun j _ => Nat.zero_le (p.val j)) (Finset.mem_univ i)
    by_cases out : chosen p = i
    · have one : p.val i = 1 := out ▸ chosen_value p
      simp [S, f, out, one]
    · have ne : p.val i ≠ 1 := fun one => out (chosen_unique p i one).symm
      have zero : p.val i = 0 := by omega
      simp [S, f, out, zero]
  have covariance (g : Equiv.Perm I) (p : Profile I 1) (s : S) :
      f (relabel g p) (g • s) = g (f p s) := by
    symm
    apply chosen_unique (relabel g p)
    change p.val (g.symm (g (chosen p))) = 1
    rw [Equiv.symm_apply_apply]
    exact chosen_value p
  let seed : S := ⟨()⟩
  have bot :=
    h (I := I) (S := S) (m := 1) (fun p _ _ => dvd_zero p)
      (fun _ => 1) (fun _ => by norm_num) f mass covariance seed
  let a : I := ⟨0⟩
  let b : I := ⟨1⟩
  let swap := Equiv.swap a b
  have member : swap ∈ MulAction.stabilizer (Equiv.Perm I) seed :=
    MulAction.mem_stabilizer_iff.mpr rfl
  rw [bot, Subgroup.mem_bot] at member
  have eq : b = a := by
    simpa only [swap, Equiv.swap_apply_left, Equiv.Perm.one_apply] using
      congrArg (fun g : Equiv.Perm I => g a) member
  exact (by decide : (1 : Fin 2) ≠ 0) (congrArg ULift.down eq)

def family : Registration arena (type_of% (@free_of_prime_divisibility)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨free_of_prime_divisibility, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    exact ⟨(), 0, 1, (by decide : (0 : ℕ) ≠ 1)⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@free_of_prime_divisibility) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness.information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain",
        "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
