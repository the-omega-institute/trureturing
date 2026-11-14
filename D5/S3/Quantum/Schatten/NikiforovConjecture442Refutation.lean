/- GID: D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Schatten/NikiforovConjecture442Refutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.claim; result=D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.result; claim=D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.claim
   digest: The modulus condition does not suffice for equality in Conjecture 4.42. -/

import D5.S3.Quantum.NormCompression.SchattenContinuity
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Schatten.NikiforovConjecture442Refutation
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction

/-- A surjective coloring describes nonempty common row and column parts. -/
def rPartite {n : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : Fin n → Fin r, Function.Surjective c ∧ ∀ i j, c i = c j → A i j = 0

/-- The complex adjacency matrix of the balanced Turán graph. -/
def turanMatrix (n r : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (SimpleGraph.turanGraph n r).adjMatrix ℂ

/-- Entrywise modulus agrees with the Turán adjacency after one common relabeling. -/
def isTuranModulus {n : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ i j, (‖A i j‖ : ℂ) = turanMatrix n r (e i) (e j)

/-- The entire assertion of Nikiforov, arXiv:1510.02850v2, Conjecture 4.42. -/
def claim : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (n r : ℕ), 2 ≤ r → r ≤ n →
    ∀ A : Matrix (Fin n) (Fin n) ℂ,
      (∀ i j, ‖A i j‖ ≤ 1) → rPartite r A →
        schattenNorm p A ≤ schattenNorm p (turanMatrix n r) ∧
          (schattenNorm p A = schattenNorm p (turanMatrix n r) ↔ isTuranModulus r A)

private theorem parts_iff {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    rPartite r A ↔ ∃ S : Fin r → Finset (Fin n),
      (∀ k, (S k).Nonempty) ∧ (∀ i, ∃! k, i ∈ S k) ∧
        ∀ k i j, i ∈ S k → j ∈ S k → A i j = 0 := by
  classical
  constructor
  · rintro ⟨c, hc, hz⟩
    refine ⟨fun k => Finset.univ.filter (fun i => c i = k), ?_, ?_, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := hc k
      exact ⟨i, by simp [hi]⟩
    · intro i
      refine ⟨c i, by simp, ?_⟩
      intro k hk
      exact (Finset.mem_filter.mp hk).2.symm
    · intro k i j hi hj
      exact hz i j ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  · rintro ⟨S, hS, hu, hz⟩
    choose c hc using fun i => (hu i).exists
    refine ⟨c, ?_, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := hS k
      exact ⟨i, (hu i).unique (hc i) hi⟩
    · intro i j hij
      exact hz (c i) i j (hc i) (hij ▸ hc j)

private theorem max_bound_iff {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (∀ i j, ‖A i j‖ ≤ 1) ↔ (Finset.univ.sup' (by simp : (Finset.univ : Finset (Fin n × Fin n)).Nonempty)
      (fun ij => ‖A ij.1 ij.2‖) ≤ 1) := by
  constructor
  · intro h
    exact Finset.sup'_le fun ij _ => h ij.1 ij.2
  · intro h i j
    exact (Finset.le_sup' (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖) (by simp : (i,j) ∈ Finset.univ)).trans h

private theorem balanced_relabel {n r : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hP : P.IsEquipartition) (hr : P.parts.card = r) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j,
      (if P.part i = P.part j then (0 : ℂ) else 1) = turanMatrix n r (e i) (e j) := by
  classical
  obtain ⟨f, hf⟩ := hP.exists_partPreservingEquiv
  have hn : (Finset.univ : Finset (Fin n)).card = n := by simp
  let e : Equiv.Perm (Fin n) :=
    (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans (f.trans (finCongr hn))
  refine ⟨e, ?_⟩
  intro i j
  have h := hf ⟨i, Finset.mem_univ i⟩ ⟨j, Finset.mem_univ j⟩
  simp only [hr] at h
  simp only [turanMatrix, SimpleGraph.adjMatrix_apply, SimpleGraph.turanGraph_adj]
  change (if P.part i = P.part j then (0 : ℂ) else 1) =
    if (f ⟨i, Finset.mem_univ i⟩).val % r ≠ (f ⟨j, Finset.mem_univ j⟩).val % r then 1 else 0
  by_cases hij : P.part i = P.part j <;> simp [hij, ← h]

private theorem schatten_reindex {n : ℕ} (p : ℝ) (hp : 0 < p)
    (A : Matrix (Fin n) (Fin n) ℂ) (e : Equiv.Perm (Fin n)) :
    schattenNorm p (Matrix.reindex e e A) = schattenNorm p A := by
  unfold schattenNorm
  congr 1
  rw [schattenPow_eq_columnGram p hp, schattenPow_eq_columnGram p hp]
  have hg : (Matrix.reindex e e A)ᴴ * Matrix.reindex e e A =
      Matrix.reindex e e (Aᴴ * A) := by
    rw [Matrix.conjTranspose_reindex, Matrix.reindex_mul]
  have he := (Matrix.isHermitian_conjTranspose_mul_self (Matrix.reindex e e A)).eigenvalues_eq_eigenvalues_iff
    (Matrix.isHermitian_conjTranspose_mul_self A)
  have hc : ((Matrix.reindex e e A)ᴴ * Matrix.reindex e e A).charpoly = (Aᴴ * A).charpoly := by
    rw [hg, Matrix.charpoly_reindex]
  rw [he.mpr hc]

private theorem modulus_partition_iff {n r : ℕ} (hr : 0 < r) (hn : r ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    isTuranModulus r A ↔ ∃ P : Finpartition (Finset.univ : Finset (Fin n)),
      P.IsEquipartition ∧ P.parts.card = r ∧ ∀ i j,
        (‖A i j‖ : ℂ) = if P.part i = P.part j then 0 else 1 := by
  classical
  constructor
  · rintro ⟨e, he⟩
    let G : SimpleGraph (Fin n) := (SimpleGraph.turanGraph n r).comap e
    let iso : G ≃g SimpleGraph.turanGraph n r :=
      { toEquiv := e, map_rel_iff' := by intro i j; rfl }
    have hG := SimpleGraph.isTuranMaximal_of_iso iso hr
    refine ⟨hG.finpartition, hG.isEquipartition, ?_, ?_⟩
    · simpa [hn, Nat.min_eq_right] using hG.card_parts
    · intro i j
      rw [he i j]
      have hij := hG.not_adj_iff_part_eq (s := i) (t := j)
      simp only [turanMatrix, SimpleGraph.adjMatrix_apply]
      change (if G.Adj i j then (1 : ℂ) else 0) = _
      by_cases h : G.Adj i j <;> simp [h, ← hij]
  · rintro ⟨P, hP, hcard, hmod⟩
    obtain ⟨e, he⟩ := balanced_relabel P hP hcard
    exact ⟨e, fun i j => (hmod i j).trans (he i j)⟩

private theorem balanced_norm {n r : ℕ} (p : ℝ) (hp : 0 < p)
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hP : P.IsEquipartition) (hr : P.parts.card = r) :
    schattenNorm p (fun i j => if P.part i = P.part j then (0 : ℂ) else 1) =
      schattenNorm p (turanMatrix n r) := by
  obtain ⟨e, he⟩ := balanced_relabel P hP hr
  have hm : (fun i j => if P.part i = P.part j then (0 : ℂ) else 1) =
      Matrix.reindex e.symm e.symm (turanMatrix n r) := by
    ext i j
    exact he i j
  rw [hm]
  exact schatten_reindex p hp _ e.symm

private theorem source_equality {n r : ℕ} (h : claim) (p : ℝ) (hp : 2 < p)
    (hr : 2 ≤ r) (hn : r ≤ n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hbound : ∀ i j, ‖A i j‖ ≤ 1) (hparts : rPartite r A)
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hP : P.IsEquipartition) (hcard : P.parts.card = r)
    (hmod : ∃ Q : Finpartition (Finset.univ : Finset (Fin n)),
      Q.IsEquipartition ∧ Q.parts.card = r ∧ ∀ i j,
        (‖A i j‖ : ℂ) = if Q.part i = Q.part j then 0 else 1) :
    schattenNorm p A = schattenNorm p (fun i j => if P.part i = P.part j then (0 : ℂ) else 1) := by
  rw [balanced_norm p (by linarith) P hP hcard]
  exact (h p hp n r hr hn A hbound hparts).2.mpr
    ((modulus_partition_iff (by omega) hn A).mpr hmod)

private def witness : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 1; -1, 0, 1; -1, -1, 0]

private theorem six_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    schattenPow 6 A = ((Aᴴ * A) ^ 3).trace.re := by
  rw [D5.S3.Quantum.NormCompression.SchattenContinuity.schattenPow_trace (by norm_num)]
  have he : (fun x : ℝ => x ^ ((6 : ℝ) / 2)) = (fun x : ℝ => x ^ (3 : ℕ)) := by
    funext x
    norm_num [Real.rpow_natCast]
  rw [he, cfc_pow_id (Matrix.isHermitian_conjTranspose_mul_self A).isSelfAdjoint]

private theorem witness_parts : rPartite 3 witness := by
  apply (parts_iff witness).mpr
  refine ⟨fun k => {k}, ?_, ?_, ?_⟩
  · intro k; exact Finset.singleton_nonempty k
  · intro i; exact ⟨i, by simp, by simp⟩
  · intro k i j hi hj
    simp only [Finset.mem_singleton] at hi hj
    subst i; subst j
    fin_cases k <;> norm_num [witness]

private theorem witness_modulus : isTuranModulus 3 witness := by
  refine ⟨Equiv.refl _, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witness, turanMatrix, SimpleGraph.adjMatrix_apply, SimpleGraph.turanGraph_adj]

private theorem witness_bound : ∀ i j, ‖witness i j‖ ≤ 1 := by
  apply (max_bound_iff witness).mpr
  apply Finset.sup'_le
  intro ij _
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> norm_num [witness]

/-- The equality-sufficiency clause fails for the complex skew-symmetric 3 by 3 witness. -/
theorem result : ¬ claim := by
  intro h
  let P : Finpartition (Finset.univ : Finset (Fin 3)) := ⊥
  have hcard : P.parts.card = 3 := by simp [P, Finpartition.card_bot]
  have hmod := (modulus_partition_iff (by norm_num : 0 < 3) (by norm_num : 3 ≤ 3)
    witness).mp witness_modulus
  have he := source_equality h 6 (by norm_num) (by norm_num) (by norm_num)
    witness witness_bound witness_parts P (Finpartition.bot_isEquipartition _) hcard hmod
  rw [balanced_norm 6 (by norm_num) P (Finpartition.bot_isEquipartition _) hcard] at he
  have hp := congrArg (fun x : ℝ => x ^ (6 : ℝ)) he
  rw [schattenNorm_rpow (by norm_num), schattenNorm_rpow (by norm_num),
    six_trace, six_trace] at hp
  norm_num [witness, turanMatrix, SimpleGraph.adjMatrix_apply, SimpleGraph.turanGraph_adj,
    pow_succ, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, Matrix.conjTranspose_apply] at hp

end D5.S3.Quantum.Schatten.NikiforovConjecture442Refutation
