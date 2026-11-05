
namespace PairedDeletionLawApplicationChecks
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.PairedDeletionLaw
open scoped BigOperators

/-- Exact arbitrary-label, full-carrier n>=4 application; no family restriction. -/
theorem general_probability_application {α : Type*} [DecidableEq α]
    (A : Finset α) (hA : 4 ≤ A.card) (a b c : α)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ ν : FixedCycles A → ℝ)
    (hμ : (∀ C, 0 ≤ μ C) ∧ ∑ C, μ C = 1)
    (hν : (∀ C, 0 ≤ ν C) ∧ ∑ C, ν C = 1)
    (hF : pushforward (fun C : FixedCycles A => (delete a C.val,delete b C.val)) μ =
      pushforward (fun C : FixedCycles A => (delete a C.val,delete b C.val)) ν)
    (hG : pushforward (fun C : FixedCycles A => (delete b C.val,delete c C.val)) μ =
      pushforward (fun C : FixedCycles A => (delete b C.val,delete c C.val)) ν) : μ = ν := by
  exact full_probability_injective hA ha hb hc hab hbc hac μ ν hμ hν hF hG

def C0 : FixedCycles (Finset.univ : Finset (Fin 4)) :=
  ⟨([0,1,2,3] : List (Fin 4)), by constructor <;> decide⟩
def C1 : FixedCycles (Finset.univ : Finset (Fin 4)) :=
  ⟨([1,0,2,3] : List (Fin 4)), by constructor <;> decide⟩

/-- An inhabited size-four collision for F, separated by G. -/
theorem nontrivial_four : C0 ≠ C1 ∧
    paired 0 1 C0.val = paired 0 1 C1.val ∧
    paired 1 2 C0.val ≠ paired 1 2 C1.val := by
  decide

noncomputable def pointMass (C : FixedCycles (Finset.univ : Finset (Fin 4)))
    (D : FixedCycles (Finset.univ : Finset (Fin 4))) : ℝ :=
  if D = C then 1 else 0

theorem inhabited_probability :
    (∀ C, 0 ≤ pointMass C0 C) ∧ ∑ C, pointMass C0 C = 1 := by
  classical
  constructor
  · intro D
    simp only [pointMass]
    split_ifs <;> norm_num
  · simp [pointMass]

/-- The excluded three-label boundary really has two different originals
with identical values for both paired channels. -/
theorem failure_at_three :
    let P : Cycle (Fin 3) := ([0,1,2] : List (Fin 3))
    let Q : Cycle (Fin 3) := ([0,2,1] : List (Fin 3))
    P.Nodup ∧ Q.Nodup ∧ P.toFinset = Finset.univ ∧ Q.toFinset = Finset.univ ∧
      P ≠ Q ∧ paired 0 1 P = paired 0 1 Q ∧ paired 1 2 P = paired 1 2 Q := by
  decide

end PairedDeletionLawApplicationChecks
