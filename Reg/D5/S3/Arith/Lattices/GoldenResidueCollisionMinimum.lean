import D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum

open Finset
open _root_.D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State := fun p => Fin p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p c => ∑ i : Fin p.1, (c i : ℤ) * ((c i : ℤ) - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (m n : ℕ) (hm : 0 < m),
    (∀ c : Fin m → ℕ, (∑ i, c i) = n →
      (m : ℤ) * ((n / m : ℕ) : ℤ) * (((n / m : ℕ) : ℤ) - 1) +
          2 * ((n % m : ℕ) : ℤ) * ((n / m : ℕ) : ℤ) ≤
        r.readout () ⟨m, n⟩ c) ∧
    (∃ c : Fin m → ℕ, (∑ i, c i) = n ∧
      (∑ i, (c i : ℤ) * ((c i : ℤ) - 1)) =
        (m : ℤ) * ((n / m : ℕ) : ℤ) * (((n / m : ℕ) : ℤ) - 1) +
          2 * ((n % m : ℕ) : ℤ) * ((n / m : ℕ) : ℤ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 1 (by omega)).1 (fun _ : Fin 1 => 1) (by simp)
  change (1 : ℤ) * 1 * (1 - 1) + 2 * 0 * 1 ≤ -1 at hbad
  omega

def registration : Registration arena
    (∀ (m n : ℕ) (hm : 0 < m),
      (∀ c : Fin m → ℕ, (∑ i, c i) = n →
        (m : ℤ) * ((n / m : ℕ) : ℤ) * (((n / m : ℕ) : ℤ) - 1) +
            2 * ((n % m : ℕ) : ℤ) * ((n / m : ℕ) : ℤ) ≤
          ∑ i, (c i : ℤ) * ((c i : ℤ) - 1)) ∧
      (∃ c : Fin m → ℕ, (∑ i, c i) = n ∧
        (∑ i, (c i : ℤ) * ((c i : ℤ) - 1)) =
          (m : ℤ) * ((n / m : ℕ) : ℤ) * (((n / m : ℕ) : ℤ) - 1) +
            2 * ((n % m : ℕ) : ℤ) * ((n / m : ℕ) : ℤ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨balanced_collision_cost_minimum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, 1⟩, (fun _ : Fin 1 => 0), (fun _ : Fin 1 => 2), ?_⟩
    norm_num [actual, realize]
    change (0 : ℤ) ≠ (2 : ℤ)
    decide

register_information_theorem
  _root_.D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum.balanced_collision_cost_minimum
  in arena
  readout via (realize signature
    (fun _ p c => ∑ i : Fin p.1, (c i : ℤ) * ((c i : ℤ) - 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Lattices.GoldenResidueCollisionMinimum
