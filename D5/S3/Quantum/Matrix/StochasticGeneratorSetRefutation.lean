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

private theorem column_positive {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ Matrix.colStochastic ℝ (Fin 3)) (j : Fin 3) :
    ∃ i, 0 < M i j := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i _ => hM.1 i j)).mp (by
      rw [Matrix.sum_col_of_mem_colStochastic hM]
      norm_num)
  exact ⟨i, hi⟩

private theorem permutation_of_matching {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ Matrix.colStochastic ℝ (Fin 3)) (f : Fin 3 → Fin 3)
    (hf : Function.Bijective f) (hz : ∀ i j, i ≠ f j → M i j = 0) :
    ∃ p : Equiv.Perm (Fin 3), M = p.permMatrix ℝ := by
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hf
  refine ⟨e.symm, ?_⟩
  ext i j
  by_cases hij : i = f j
  · subst i
    have hc := Matrix.sum_col_of_mem_colStochastic hM j
    rw [Finset.sum_eq_single (f j)] at hc
    · simpa [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, e] using hc
    · intro k _ hk
      exact hz k j hk
    · simp
  · rw [hz i j hij]
    simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply,
      Equiv.symm_apply_eq, e, hij]

private theorem permutation_of_single_columns {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ Matrix.colStochastic ℝ (Fin 3))
    (hs : ∀ k i j, 0 < M i k → 0 < M j k → i = j)
    (hr : ∀ i, ∃ j, 0 < M i j) :
    ∃ p : Equiv.Perm (Fin 3), M = p.permMatrix ℝ := by
  classical
  choose f hf using column_positive hM
  have hsurj : Function.Surjective f := by
    intro i
    obtain ⟨j, hj⟩ := hr i
    exact ⟨j, hs j (f j) i (hf j) hj⟩
  apply permutation_of_matching hM f
    ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  intro i j hij
  exact le_antisymm (le_of_not_gt fun hi => hij (hs j i (f j) hi (hf j))) (hM.1 i j)

private theorem permutation_of_single_rows {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ Matrix.colStochastic ℝ (Fin 3))
    (hs : ∀ k i j, 0 < M k i → 0 < M k j → i = j) :
    ∃ p : Equiv.Perm (Fin 3), M = p.permMatrix ℝ := by
  classical
  choose f hf using column_positive hM
  have hinj : Function.Injective f := by
    intro i j hij
    exact hs (f i) i j (hf i) (by simpa only [hij] using hf j)
  apply permutation_of_matching hM f
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  intro i j hij
  apply le_antisymm _ (hM.1 i j)
  apply le_of_not_gt
  intro hi
  obtain ⟨k, hk⟩ := Finite.injective_iff_surjective.mp hinj i
  apply hij
  have hjk := hs i j k hi (by simpa only [hk] using hf k)
  rw [hjk, hk]

private theorem hull_shape {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ convexHull ℝ {1, V1, V2, V3}) :
    M 0 1 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧
      M 1 1 ≤ M 0 0 ∧ M 2 2 ≤ M 1 1 := by
  apply convexHull_min (t := {M : Matrix (Fin 3) (Fin 3) ℝ |
    M 0 1 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧
      M 1 1 ≤ M 0 0 ∧ M 2 2 ≤ M 1 1}) ?_ ?_ hM
  · intro N hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl | rfl <;> norm_num [V1, V2, V3, Matrix.one_apply, Matrix.cons_val_two, Fin.ext_iff]
  · intro M hM N hN a b ha hb _
    rcases hM with ⟨h01, h12, h20, h10, h21⟩
    rcases hN with ⟨k01, k12, k20, k10, k21⟩
    change _ = 0 ∧ _ = 0 ∧ _ = 0 ∧ _ ≤ _ ∧ _ ≤ _
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨by rw [h01, k01]; ring, by rw [h12, k12]; ring,
      by rw [h20, k20]; ring, ?_, ?_⟩
    · exact add_le_add (mul_le_mul_of_nonneg_left h10 ha)
        (mul_le_mul_of_nonneg_left k10 hb)
    · exact add_le_add (mul_le_mul_of_nonneg_left h21 ha)
        (mul_le_mul_of_nonneg_left k21 hb)

private def edge_row : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

private def edge_col : Fin 6 → Fin 3 := ![1, 2, 0, 2, 0, 1]

set_option maxRecDepth 10000 in
private theorem edge_partition : ∀ w : Fin 6 → Fin 3,
    (∀ e f, w e = w f → edge_row e ≠ edge_col f) →
    (w 0 = w 1 ∧ w 2 = w 3 ∧ w 4 = w 5 ∧
      w 0 ≠ w 2 ∧ w 0 ≠ w 4 ∧ w 2 ≠ w 4) ∨
    (w 0 = w 5 ∧ w 1 = w 3 ∧ w 2 = w 4 ∧
      w 0 ≠ w 1 ∧ w 0 ≠ w 2 ∧ w 1 ≠ w 2) := by
  decide

private theorem single_columns_of_stars (b c : Fin 3 → Fin 3 → Prop)
    (hd : ∀ i k, ¬ (b i k ∧ c k i)) (k0 k1 k2 : Fin 3)
    (hk : ∀ k, k = k0 ∨ k = k1 ∨ k = k2)
    (hc : c k0 1 ∧ c k0 2 ∧ c k1 0 ∧ c k1 2 ∧ c k2 0 ∧ c k2 1) :
    ∀ k i j, b i k → b j k → i = j := by
  intro k i j hi hj
  rcases hk k with rfl | rfl | rfl
  all_goals
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (hd _ _ ⟨hi, by tauto⟩).elim

private theorem support_dichotomy (b c : Fin 3 → Fin 3 → Prop)
    (h : ∀ i j, i ≠ j ↔ ∃ k, b i k ∧ c k j) :
    (∀ k i j, b i k → b j k → i = j) ∨
    (∀ k i j, c k i → c k j → i = j) := by
  classical
  have hd : ∀ i k, ¬ (b i k ∧ c k i) := by
    intro i k hk
    exact (h i i).mpr ⟨k, hk⟩ rfl
  have he : ∀ e, edge_row e ≠ edge_col e := by decide
  choose w hw using fun e => (h (edge_row e) (edge_col e)).mp (he e)
  have hp : ∀ e f, w e = w f → edge_row e ≠ edge_col f := by
    intro e f hef heq
    exact hd (edge_row e) (w e) ⟨(hw e).1, by
      simpa only [hef, heq] using (hw f).2⟩
  have h0 : b 0 (w 0) ∧ c (w 0) 1 := hw 0
  have h1 : b 0 (w 1) ∧ c (w 1) 2 := hw 1
  have h2 : b 1 (w 2) ∧ c (w 2) 0 := hw 2
  have h3 : b 1 (w 3) ∧ c (w 3) 2 := hw 3
  have h4 : b 2 (w 4) ∧ c (w 4) 0 := hw 4
  have h5 : b 2 (w 5) ∧ c (w 5) 1 := hw 5
  rcases edge_partition w hp with ⟨h01, h23, h45, h02, h04, h24⟩ |
    ⟨h05, h13, h24, h01, h02, h12⟩
  · left
    apply single_columns_of_stars b c hd (w 0) (w 2) (w 4)
    · intro k
      omega
    · exact ⟨h0.2, by simpa only [← h01] using h1.2,
        h2.2, by simpa only [← h23] using h3.2,
        h4.2, by simpa only [← h45] using h5.2⟩
  · right
    apply single_columns_of_stars (fun i k => c k i) (fun k i => b i k)
      (fun i k hk => hd i k ⟨hk.2, hk.1⟩) (w 2) (w 0) (w 1)
    · intro k
      omega
    · exact ⟨h2.1, by simpa only [← h24] using h4.1,
        h0.1, by simpa only [← h05] using h5.1,
        h1.1, by simpa only [← h13] using h3.1⟩

end D5.S3.Quantum.Matrix.StochasticGeneratorSetRefutation
