/- GID: D5/S3/Combinatorics/Apollonian/SecondEigenvalueLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apollonian/SecondEigenvalueLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: The second ordinary-adjacency eigenvalue of the inner-face Apollonian stages. -/

import D5.S3.Combinatorics.Apollonian.CutoffGramLimit
import D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum
import Mathlib.Analysis.CStarAlgebra.Basic

noncomputable section
namespace D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit
open InnerFaceStages CutoffGramLimit CutoffOrderedSpectrum Matrix Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def weight (k : ℕ) (v : Vertex k) : ℝ := (faceCount k v : ℝ) / (2:ℝ)^k

private theorem weight_old (k : ℕ) (v : Vertex k) :
    weight (k+1) (Sum.inl v) = weight k v := by
  simp only [weight, faceCount_old, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp
  <;> ring

private theorem weight_seed (k : ℕ) (v : Fin 4) :
    weight k (seed k v) = if v = 3 then 3 else 2 := by
  induction k with
  | zero =>
    revert v
    decide +kernel
  | succ k ih => simpa only [seed, weight_old] using ih

private theorem weight_other_le (k : ℕ) (v : Vertex k) (hv : v ≠ seed k 3) :
    weight k v ≤ 2 := by
  induction k with
  | zero =>
    revert v
    decide +kernel
  | succ k ih =>
    cases v with
    | inl v =>
      rw [weight_old]
      exact ih v (by simpa only [seed, ne_eq, Sum.inl.injEq] using hv)
    | inr f =>
      simp only [weight, faceCount_new, Nat.cast_ofNat]
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(k+1))).mpr
      have h : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      nlinarith

private theorem diagonal_hermitian (k : ℕ) : (limitingDiagonal k).IsHermitian := by
  exact isHermitian_diagonal_iff.mpr (fun _ => by simp [IsSelfAdjoint])

/-- At every fixed cutoff, the second decreasing eigenvalue of the face-weight diagonal is two. -/
theorem limiting_diagonal_second (k : ℕ) :
    (diagonal_hermitian k).eigenvalues₀ (secondIndex k) = 2 := by
  classical
  let c := seed k 3
  let a := seed k 0
  let s : Finset (Vertex k) := Finset.univ.erase c
  let r : Finset (Vertex k) := s.erase a
  have hac : a ≠ c := by
    exact fun h => (by decide : (0:Fin 4) ≠ 3) (seed_injective k h)
  have ha : a ∈ s := by simp [s, hac]
  have hsplit : (Finset.univ : Finset (Vertex k)).val = c ::ₘ a ::ₘ r.val := by
    rw [← Finset.cons_erase (Finset.mem_univ c)]
    change c ::ₘ s.val = c ::ₘ a ::ₘ r.val
    congr 1
    exact (Finset.cons_erase ha).symm
  have hwc : weight k c = 3 := by simpa [c] using weight_seed k 3
  have hwa : weight k a = 2 := by simpa [a] using weight_seed k 0
  have hrest : ∀ v ∈ r.val, weight k v ≤ 2 := by
    intro v hv
    exact weight_other_le k v (by
      have := Finset.mem_erase.mp ((Finset.mem_erase.mp hv).2)
      exact this.1)
  have hsort : ((Finset.univ.val.map (weight k)).sort (· ≥ ·))[1]? = some 2 := by
    rw [hsplit, Multiset.map_cons, Multiset.map_cons, hwc, hwa]
    rw [Multiset.sort_cons, Multiset.sort_cons]
    · rfl
    · intro b hb
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hb
      exact hrest v hv
    · intro b hb
      rcases Multiset.mem_cons.mp hb with h | h
      · subst b; norm_num
      · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp h
        exact (hrest v hv).trans (by norm_num)
  have he := (diagonal_hermitian k).sort_roots_charpoly_eq_eigenvalues₀
  have hr : (limitingDiagonal k).charpoly.roots = Finset.univ.val.map (weight k) := by
    rw [limitingDiagonal, charpoly_diagonal, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
      rfl
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [hr] at he
  simp only [Multiset.map_map, RCLike.re_to_real, Function.id_comp] at he
  rw [he] at hsort
  simpa [secondIndex] using hsort

end D5.S3.Combinatorics.Apollonian.SecondEigenvalueLimit
