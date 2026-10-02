import D5.S1.Digit.ZeckendorfCarryBarrier
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.ZeckendorfCarryBarrier
open D5.S0.Conventions

namespace Reg.D5.S1.Digit.ZeckendorfCarryBarrier
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ P : List ℕ, Σ m : ℕ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ k => k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : List ℕ) (m j : ℕ), P.IsZeckendorfRep → 4 ≤ m →
    (∀ k ∈ P, m ≤ k) → m - 1 ≤ j →
    ∀ k ∈ wdigits ((P.map Nat.fib).sum + Nat.fib j), m - 2 ≤
      R.readout () ⟨P, ⟨m, j⟩⟩ k

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [] 4 3 (by simp [List.IsZeckendorfRep]) (by omega) (by simp) (by omega)
  have hwd : wdigits (Nat.fib 3) = [3] := by
    norm_num [Nat.fib]
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]
  change ∀ k ∈ wdigits (Nat.fib 3), 4 - 2 ≤ rejected.readout () ⟨[], ⟨4, 3⟩⟩ k at hh
  rw [hwd] at hh
  have := hh 3 (by simp)
  simp [rejected, realize] at this

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lower_support_carry_barrier, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨[], ⟨4, 3⟩⟩, 0, 1, ?_⟩
    simp [actual, realize]

register_information_theorem lower_support_carry_barrier in arena
  readout via (realize signature (fun _ _ k => k) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Digit.ZeckendorfCarryBarrier
    coordinates := #[0, 1, 2]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 7}]})
  escape continues (open)

#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfCarryBarrier
