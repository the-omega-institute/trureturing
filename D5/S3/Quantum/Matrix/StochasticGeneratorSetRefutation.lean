/- GID: D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/StochasticGeneratorSetRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.claim; result=D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.result; claim=D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.claim
   digest: A six-cycle stochastic matrix refutes the proposed twenty-factor generator bound. -/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic

set_option linter.style.longLine false

namespace D5.S3.Quantum.Matrix.StochasticGeneratorSetRefutation

/-- The first nonidentity vertex in Eq. (10). -/
def V1 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 1; 0, 1, 0; 0, 0, 0]

/-- The second nonidentity vertex in Eq. (10). -/
def V2 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 1; 0, 0, 0; 0, 1, 0]

/-- The cyclic permutation vertex in Eq. (10). -/
def V3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- The transposition exchanging the first two coordinates. -/
def swap12 : Matrix (Fin 3) (Fin 3) ℝ :=
  (Equiv.swap (0 : Fin 3) 1).permMatrix ℝ

/-- The generator set of Eq. (10). -/
noncomputable def gen : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {swap12} ∪ convexHull ℝ {1, V1, V2, V3}

/-- Products of exactly the specified number of generators. -/
noncomputable def genPow : ℕ → Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  Nat.rec {1} (fun _ s => {A | ∃ g ∈ gen, ∃ w ∈ s, A = g * w})

/-- The proposed optimal generator length twenty. -/
def claim : Prop :=
  (∀ A ∈ Matrix.colStochastic ℝ (Fin 3), A ∈ genPow 20) ∧
  (∃ A ∈ Matrix.colStochastic ℝ (Fin 3), A ∉ genPow 19)

private noncomputable def witness : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/4, 0, 1/4; 3/4, 1/2, 0; 0, 1/2, 3/4]

private theorem witness_stochastic : witness ∈ Matrix.colStochastic ℝ (Fin 3) := by
  rw [Matrix.mem_colStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witness]
  · intro j
    fin_cases j <;> norm_num [witness, Fin.sum_univ_succ]

private theorem gen_stochastic {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ gen) :
    M ∈ Matrix.colStochastic ℝ (Fin 3) := by
  rcases hM with hM | hM
  · rcases hM with rfl
    exact Matrix.permMatrix_mem_colStochastic
  · apply convexHull_min ?_ Matrix.convex_colStochastic hM
    intro N hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl | rfl
    · exact (Matrix.colStochastic ℝ (Fin 3)).one_mem
    all_goals
      simp only [SetLike.mem_coe]
      rw [Matrix.mem_colStochastic_iff_sum]
      constructor
      · intro i j
        fin_cases i <;> fin_cases j <;> norm_num [V1, V2, V3]
      · intro j
        fin_cases j <;> norm_num [V1, V2, V3, Fin.sum_univ_succ]

private theorem power_stochastic {m : ℕ} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ genPow m) : M ∈ Matrix.colStochastic ℝ (Fin 3) := by
  induction m generalizing M with
  | zero =>
    change M ∈ ({1} : Set _) at hM
    rcases hM with rfl
    exact (Matrix.colStochastic ℝ (Fin 3)).one_mem
  | succ m ih =>
    change ∃ g ∈ gen, ∃ w ∈ genPow m, M = g * w at hM
    obtain ⟨g, hg, w, hw, rfl⟩ := hM
    exact (Matrix.colStochastic ℝ (Fin 3)).mul_mem (gen_stochastic hg) (ih hw)

end D5.S3.Quantum.Matrix.StochasticGeneratorSetRefutation
