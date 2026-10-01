/- GID: D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/AverageMixingTraceMaximum
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: K_n maximizes the adjacency average mixing trace over connected graphs. -/

/-
proof_shape: result: content; private vertex_bound: content; private simplex_bound: content;
  private complete_diag: content
escape_witness: vertex_bound shows (E_θ)_aa ≤ 1 - 1/n at every vertex a with a neighbour,
  by Cauchy–Schwarz on the eigen-equation of E_θ e_a at a and at one neighbour of a;
  complete_diag evaluates the diagonal of the average mixing matrix of K_n.
admission_basis: open-problem-resolution (#11821; Proved)
Direct frozen dependencies: none (Mathlib only).
Utility: none; the result is a theorem over every n.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Algebra.Order.Chebyshev

open Matrix Finset

namespace D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum

variable {n : ℕ}

/-- The spectral idempotent `E_θ` of the adjacency matrix `A(G)`: the sum of `v vᵀ` over the
vectors `v` of an orthonormal eigenbasis of `A(G)` with eigenvalue `θ`. It is the orthogonal
projection onto the `θ`-eigenspace, whatever the orthonormal eigenbasis, and it is zero when `θ`
is not an eigenvalue. -/
noncomputable def idempotent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (θ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let hA : (G.adjMatrix ℝ).IsHermitian := isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  ∑ i with hA.eigenvalues i = θ, vecMulVec ⇑(hA.eigenvectorBasis i) ⇑(hA.eigenvectorBasis i)

/-- The average mixing matrix `M̂_A = Σ_θ E_θ ∘ E_θ` of the continuous-time quantum walk with
Hamiltonian `A(G)`, the sum running over the distinct eigenvalues `θ` of `A(G)` and `∘` being
the Schur (entrywise) product. -/
noncomputable def avgMixing (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℝ :=
  let hA : (G.adjMatrix ℝ).IsHermitian := isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  ∑ θ ∈ univ.image hA.eigenvalues, idempotent G θ ⊙ idempotent G θ

/-- Conjecture 9.1 of Godsil, Guo and Sobchuk (arXiv:1910.02039), read over connected graphs:
for every `n` and every connected graph `G` on `n` vertices, the trace of the average mixing
matrix of `G` is at most that of the complete graph `K_n`. `result` proves it. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected →
    (avgMixing G).trace ≤ (avgMixing (⊤ : SimpleGraph (Fin n))).trace


/-- The vertex bound: if `a` has a neighbour, `A u = θ u`, and `‖u‖² = u a`, then
`n · u a ≤ n - 1`. Applied to `u = E_θ e_a` it gives `(E_θ)_aa ≤ 1 - 1/n`. -/
private theorem vertex_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n → ℝ)
    (θ : ℝ) {a b : Fin n} (hab : G.Adj a b)
    (heig : ∀ c, ∑ d ∈ G.neighborFinset c, u d = θ * u c)
    (hnorm : ∑ c, u c ^ 2 = u a) : (n : ℝ) * u a ≤ n - 1 := by
  have hrest : ∑ c ∈ univ.erase a, u c ^ 2 = u a - u a ^ 2 := by
    have := add_sum_erase univ (fun c => u c ^ 2) (mem_univ a)
    linarith
  have hr : 0 ≤ u a - u a ^ 2 := by
    rw [← hrest]
    exact sum_nonneg fun _ _ => sq_nonneg _
  have hn : (2 : ℝ) ≤ n := by
    have : 2 ≤ n := Fin.nontrivial_iff_two_le.mp ⟨⟨a, b, hab.ne⟩⟩
    exact_mod_cast this
  have hdeg : ∀ c, ((G.neighborFinset c).card : ℝ) ≤ n - 1 := by
    intro c
    have h1 := G.degree_lt_card_verts c
    rw [Fintype.card_fin, ← G.card_neighborFinset_eq_degree] at h1
    have : ((G.neighborFinset c).card : ℝ) + 1 ≤ n := by exact_mod_cast h1
    linarith
  -- Cauchy–Schwarz at `a`.
  have h1 : θ ^ 2 * u a ^ 2 ≤ (n - 1) * (u a - u a ^ 2) := by
    have cs := sq_sum_le_card_mul_sum_sq (s := G.neighborFinset a) (f := u)
    rw [heig a] at cs
    have hsub : ∑ d ∈ G.neighborFinset a, u d ^ 2 ≤ u a - u a ^ 2 := by
      rw [← hrest]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
      intro d hd
      exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset a d).mp hd)).symm, mem_univ d⟩
    have hnn : 0 ≤ ∑ d ∈ G.neighborFinset a, u d ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    calc θ ^ 2 * u a ^ 2 = (θ * u a) ^ 2 := by ring
      _ ≤ (G.neighborFinset a).card * ∑ d ∈ G.neighborFinset a, u d ^ 2 := cs
      _ ≤ (n - 1) * (u a - u a ^ 2) := mul_le_mul (hdeg a) hsub hnn (by linarith)
  -- Cauchy–Schwarz at the neighbour `b`.
  have h2 : u a ^ 2 ≤ (θ ^ 2 + (n - 2)) * (u a - u a ^ 2) := by
    set T := (G.neighborFinset b).erase a with hT
    have haN : a ∈ G.neighborFinset b := (G.mem_neighborFinset b a).mpr hab.symm
    have hbT : b ∉ T := fun h => G.notMem_neighborFinset_self b (mem_of_mem_erase h)
    have hsplit : θ * u b = u a + ∑ d ∈ T, u d := by
      rw [← heig b, hT, add_sum_erase _ _ haN]
    let w : Fin n → ℝ := fun c => if c = b then θ else -1
    have hwb : w b = θ := if_pos rfl
    have hwT : ∀ c ∈ T, w c = -1 := fun c hc => if_neg fun (h : c = b) => hbT (h ▸ hc)
    have hcs := sum_mul_sq_le_sq_mul_sq (insert b T) w u
    have hlhs : ∑ c ∈ insert b T, w c * u c = u a := by
      rw [sum_insert hbT, hwb]
      have : ∑ c ∈ T, w c * u c = -∑ c ∈ T, u c := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun c hc => by rw [hwT c hc]; ring
      rw [this]
      linarith
    have hw2 : ∑ c ∈ insert b T, w c ^ 2 ≤ θ ^ 2 + (n - 2) := by
      rw [sum_insert hbT, hwb]
      have hTsq : ∑ c ∈ T, w c ^ 2 = T.card := by
        rw [card_eq_sum_ones, Nat.cast_sum]
        exact sum_congr rfl fun c hc => by rw [hwT c hc]; norm_num
      have hTc : (T.card : ℝ) ≤ n - 2 := by
        have hb := hdeg b
        have hpos : 1 ≤ (G.neighborFinset b).card := card_pos.mpr ⟨a, haN⟩
        rw [hT, card_erase_of_mem haN, Nat.cast_sub hpos]
        push_cast
        linarith
      rw [hTsq]
      linarith
    have hu2 : ∑ c ∈ insert b T, u c ^ 2 ≤ u a - u a ^ 2 := by
      rw [← hrest]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
      intro c hc
      rcases mem_insert.mp hc with rfl | hc
      · exact mem_erase.mpr ⟨hab.ne.symm, mem_univ _⟩
      · exact mem_erase.mpr ⟨ne_of_mem_erase hc, mem_univ _⟩
    have hnn : 0 ≤ ∑ c ∈ insert b T, u c ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    rw [hlhs] at hcs
    calc u a ^ 2 ≤ (∑ c ∈ insert b T, w c ^ 2) * ∑ c ∈ insert b T, u c ^ 2 := hcs
      _ ≤ (θ ^ 2 + (n - 2)) * (u a - u a ^ 2) :=
        mul_le_mul hw2 hu2 hnn (by nlinarith [sq_nonneg θ])
  -- Eliminate `θ`.
  have h4 : u a ^ 2 * u a ^ 2 ≤
      (n - 1) * (u a - u a ^ 2) ^ 2 + (n - 2) * (u a - u a ^ 2) * u a ^ 2 := by
    have e1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (u a))
    have e2 := mul_le_mul_of_nonneg_right h1 hr
    nlinarith [e1, e2]
  have h3 : u a ^ 2 ≤ (n - 1) * (u a - u a ^ 2) := by
    by_contra hc
    push Not at hc
    have hnr : 0 ≤ ((n : ℝ) - 1) * (u a - u a ^ 2) := mul_nonneg (by linarith) hr
    have hpos : 0 < u a ^ 2 + (u a - u a ^ 2) := by linarith
    have := mul_pos (sub_pos.mpr hc) hpos
    nlinarith [this, h4]
  have hua : 0 ≤ u a := by nlinarith [hr, sq_nonneg (u a)]
  rcases hua.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    linarith
  · have : (n : ℝ) * u a * u a ≤ (n - 1) * u a := by nlinarith [h3]
    exact le_of_mul_le_mul_right this hpos

/-- A probability vector whose entries are at most `1 - 1/n` has squared norm at most
`1 - 2/n + 2/n²`. -/
private theorem simplex_bound (I : Finset ℝ) (P : ℝ → ℝ) (hn : (2 : ℝ) ≤ n)
    (hP0 : ∀ θ ∈ I, 0 ≤ P θ) (hP1 : ∀ θ ∈ I, (n : ℝ) * P θ ≤ n - 1)
    (hsum : ∑ θ ∈ I, P θ = 1) :
    (n : ℝ) ^ 2 * ∑ θ ∈ I, P θ ^ 2 ≤ n ^ 2 - 2 * n + 2 := by
  have hI : I.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hsum
    exact zero_ne_one hsum
  obtain ⟨θ₀, h₀, hmax⟩ := exists_max_image I P hI
  have hrest : ∑ θ ∈ I.erase θ₀, P θ = 1 - P θ₀ := by
    have := add_sum_erase I P h₀
    linarith
  have hsq : ∑ θ ∈ I, P θ ^ 2 ≤ P θ₀ ^ 2 + (1 - P θ₀) ^ 2 := by
    rw [← add_sum_erase I (fun θ => P θ ^ 2) h₀]
    have hoth : ∀ θ ∈ I.erase θ₀, P θ ^ 2 ≤ (1 - P θ₀) * P θ := by
      intro θ hθ
      have hle1 : P θ ≤ 1 - P θ₀ := by
        rw [← hrest]
        exact single_le_sum (fun x hx => hP0 x (mem_of_mem_erase hx)) hθ
      have := hP0 θ (mem_of_mem_erase hθ)
      nlinarith
    have := sum_le_sum hoth
    rw [← mul_sum, hrest] at this
    nlinarith [this]
  have hsq2 : ∑ θ ∈ I, P θ ^ 2 ≤ P θ₀ := by
    calc ∑ θ ∈ I, P θ ^ 2 ≤ ∑ θ ∈ I, P θ₀ * P θ :=
          sum_le_sum fun θ hθ => by nlinarith [hmax θ hθ, hP0 θ hθ]
      _ = P θ₀ := by rw [← mul_sum, hsum, mul_one]
  have hm1 := hP1 θ₀ h₀
  rcases le_or_gt 1 ((n : ℝ) * P θ₀) with hbig | hsmall
  · have key : 0 ≤ ((n : ℝ) - 1 - n * P θ₀) * (n * P θ₀ - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (n : ℝ)), key]
  · have hn0 : (0 : ℝ) < n := by linarith
    have hfac : 0 ≤ ((n : ℝ) - 1) * (n - 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hsq2 (sq_nonneg (n : ℝ)),
      mul_lt_mul_of_pos_left hsmall hn0]


/-- On `K_n`, every diagonal entry of `M̂_A` is `1 - 2/n + 2/n²`; only `≥` is used. The
hypotheses are the unit norms of the row of the eigenbasis matrix at `a` and of its columns. -/
private theorem complete_diag (hA : ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ).IsHermitian)
    (hn : 1 ≤ n) (a : Fin n)
    (hrow : ∑ i, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1)
    (hcol : ∀ i, ∑ c, hA.eigenvectorBasis i c * hA.eigenvectorBasis i c = 1) :
    (n : ℝ) ^ 2 - 2 * n + 2 ≤ (n : ℝ) ^ 2 * ∑ θ ∈ univ.image hA.eigenvalues,
      (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 := by
  have hsum : ∑ θ ∈ univ.image hA.eigenvalues,
      ∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1 := by
    rw [sum_fiberwise_of_maps_to (fun i _ => mem_image_of_mem _ (mem_univ i))]
    exact hrow
  have hnn : 0 ≤ ∑ θ ∈ univ.image hA.eigenvalues,
      (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : (n : ℝ) = 1 := by exact_mod_cast (show n = 1 by omega)
    have hcs := sq_sum_le_card_mul_sum_sq (s := univ.image hA.eigenvalues)
      (f := fun θ => ∑ i with hA.eigenvalues i = θ,
        hA.eigenvectorBasis i a * hA.eigenvectorBasis i a)
    rw [hsum] at hcs
    have hcard : ((univ.image hA.eigenvalues).card : ℝ) ≤ 1 := by
      have : (univ.image hA.eigenvalues).card ≤ n := card_image_le.trans (by simp)
      rw [← hn1]
      exact_mod_cast this
    rw [hn1]
    nlinarith [mul_le_mul_of_nonneg_right hcard hnn]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    -- every eigenvector with eigenvalue other than `-1` is constant, with eigenvalue `n - 1`
    have eig : ∀ i, hA.eigenvalues i ≠ -1 →
        hA.eigenvalues i = n - 1 ∧ ∀ c, hA.eigenvectorBasis i c ^ 2 = 1 / n := by
      intro i hi
      have hno := hcol i
      have heq := hA.mulVec_eigenvectorBasis i
      generalize hA.eigenvalues i = l at heq hi ⊢
      generalize ⇑(hA.eigenvectorBasis i) = v at heq hno ⊢
      have hrows : ∀ c, ∑ d, v d = (l + 1) * v c := by
        intro c
        have h := congrFun heq c
        rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.neighborFinset_top] at h
        simp only [Pi.smul_apply, smul_eq_mul] at h
        rw [← sum_compl_add_sum {c} v, sum_singleton, h]
        ring
      have hl : l + 1 ≠ 0 := fun h => hi (by linarith)
      obtain ⟨κ, hc⟩ : ∃ κ, ∀ c, v c = κ :=
        ⟨(∑ d, v d) / (l + 1), fun c => by rw [eq_div_iff hl, hrows c]; ring⟩
      have hnorm : (n : ℝ) * κ ^ 2 = 1 := by
        simp only [hc, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hno
        linear_combination hno
      have hκ : κ ≠ 0 := by
        rintro rfl
        simp at hnorm
      have hl' : l = n - 1 := by
        have h := hrows ⟨0, by omega⟩
        simp only [hc, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
        have := mul_right_cancel₀ hκ h
        linarith
      refine ⟨hl', fun c => ?_⟩
      rw [hc c, eq_div_iff hn0.ne']
      linarith
    have hsub : univ.image hA.eigenvalues ⊆ {(n : ℝ) - 1, -1} := by
      intro θ hθ
      obtain ⟨i, -, rfl⟩ := mem_image.mp hθ
      by_cases h : hA.eigenvalues i = -1
      · simp only [mem_insert, mem_singleton]
        exact Or.inr h
      · simp only [mem_insert, mem_singleton]
        exact Or.inl (eig i h).1
    have hne : (n : ℝ) - 1 ≠ -1 := by linarith
    have hzero : ∀ θ ∈ ({(n : ℝ) - 1, -1} : Finset ℝ), θ ∉ univ.image hA.eigenvalues →
        ∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 0 :=
      fun θ _ hθ => sum_eq_zero fun i hi =>
        absurd ((mem_filter.mp hi).2 ▸ mem_image_of_mem _ (mem_univ i)) hθ
    -- the trace of `A(K_n)` is zero, so exactly one eigenvalue is `n - 1`
    have htr : ∑ i, hA.eigenvalues i = 0 := by
      have h := hA.trace_eq_sum_eigenvalues
      rw [SimpleGraph.trace_adjMatrix] at h
      simpa using h.symm
    have hK : ∑ i, (if hA.eigenvalues i = (n : ℝ) - 1 then (1 : ℝ) else 0) = 1 := by
      have hsplit : ∀ i, hA.eigenvalues i =
          n * (if hA.eigenvalues i = (n : ℝ) - 1 then (1 : ℝ) else 0) - 1 := by
        intro i
        by_cases h : hA.eigenvalues i = -1
        · have hne2 : hA.eigenvalues i ≠ (n : ℝ) - 1 := by
            rw [h]
            exact hne.symm
          rw [if_neg hne2, h]
          ring
        · rw [if_pos (eig i h).1, (eig i h).1]
          ring
      rw [sum_congr rfl fun i _ => hsplit i, sum_sub_distrib, ← mul_sum] at htr
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at htr
      generalize (∑ i, if hA.eigenvalues i = (n : ℝ) - 1 then (1 : ℝ) else 0) = K at htr ⊢
      have hprod : (n : ℝ) * (K - 1) = 0 := by linarith
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h hn0.ne'
      · linarith
    have hp1 : ∑ i with hA.eigenvalues i = (n : ℝ) - 1,
        hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1 / n := by
      rw [sum_filter]
      have : ∀ i, (if hA.eigenvalues i = (n : ℝ) - 1 then
          hA.eigenvectorBasis i a * hA.eigenvectorBasis i a else 0) =
          (1 / n) * (if hA.eigenvalues i = (n : ℝ) - 1 then (1 : ℝ) else 0) := by
        intro i
        by_cases h : hA.eigenvalues i = (n : ℝ) - 1
        · rw [if_pos h, if_pos h, mul_one, ← sq]
          exact (eig i (by rw [h]; exact hne)).2 a
        · rw [if_neg h, if_neg h, mul_zero]
      rw [sum_congr rfl fun i _ => this i, ← mul_sum, hK, mul_one]
    have hsum1 : (∑ i with hA.eigenvalues i = (n : ℝ) - 1,
        hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) +
        ∑ i with hA.eigenvalues i = -1, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1 := by
      have hp : ∑ θ ∈ ({(n : ℝ) - 1, -1} : Finset ℝ),
          ∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a =
          (∑ i with hA.eigenvalues i = (n : ℝ) - 1,
            hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) +
          ∑ i with hA.eigenvalues i = -1, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a :=
        sum_pair hne
      rw [← hp, ← sum_subset hsub hzero]
      exact hsum
    have hsq : ∑ θ ∈ univ.image hA.eigenvalues,
        (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 =
        (∑ i with hA.eigenvalues i = (n : ℝ) - 1,
          hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 +
        (∑ i with hA.eigenvalues i = -1,
          hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 := by
      have hp2 : ∑ θ ∈ ({(n : ℝ) - 1, -1} : Finset ℝ),
          (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 =
          (∑ i with hA.eigenvalues i = (n : ℝ) - 1,
            hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 +
          (∑ i with hA.eigenvalues i = -1, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 :=
        sum_pair hne
      rw [← hp2]
      exact sum_subset hsub fun θ h hθ => by rw [hzero θ h hθ]; ring
    have hm1 : ∑ i with hA.eigenvalues i = -1,
        hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1 - 1 / n := by linarith
    rw [hsq, hp1, hm1]
    have hval : (n : ℝ) ^ 2 * ((1 / n) ^ 2 + (1 - 1 / n) ^ 2) = n ^ 2 - 2 * n + 2 := by
      field_simp
      ring
    linarith

theorem result : claim := by
  intro n G _ hG
  -- the rows and the columns of the matrix of an orthonormal eigenbasis are orthonormal
  have rows : ∀ {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (a : Fin n),
      ∑ i, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1 := by
    intro A hA a
    have h := congrFun (congrFun (mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2) a) a
    simpa [mul_apply, star_apply, one_apply] using h
  have cols : ∀ {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (i j : Fin n),
      ∑ c, hA.eigenvectorBasis i c * hA.eigenvectorBasis j c = if i = j then 1 else 0 := by
    intro A hA i j
    have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2) i) j
    simpa [mul_apply, star_apply, one_apply] using h
  -- the trace as the sum of the squared diagonal entries of the spectral idempotents
  have htrace : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
      (hH : (H.adjMatrix ℝ).IsHermitian),
      (avgMixing H).trace = ∑ a, ∑ θ ∈ univ.image hH.eigenvalues,
        (∑ i with hH.eigenvalues i = θ, hH.eigenvectorBasis i a * hH.eigenvectorBasis i a) ^ 2 := by
    intro H _ hH
    simp only [avgMixing, idempotent, trace, diag_apply, Matrix.sum_apply, hadamard_apply,
      vecMulVec_apply, sq]
  have hpos : 0 < n := (hG.nonempty.some).pos
  have hA : (G.adjMatrix ℝ).IsHermitian := isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  -- every diagonal entry of `M̂_A(G)` is at most `1 - 2/n + 2/n²`
  have hdiag : ∀ a, (n : ℝ) ^ 2 * ∑ θ ∈ univ.image hA.eigenvalues,
      (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2 ≤
        n ^ 2 - 2 * n + 2 := by
    intro a
    have hsum : ∑ θ ∈ univ.image hA.eigenvalues,
        ∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a = 1 := by
      rw [sum_fiberwise_of_maps_to (fun i _ => mem_image_of_mem _ (mem_univ i))]
      exact rows hA a
    have hnonneg : ∀ θ, 0 ≤ ∑ i with hA.eigenvalues i = θ,
        hA.eigenvectorBasis i a * hA.eigenvectorBasis i a :=
      fun θ => sum_nonneg fun i _ => mul_self_nonneg _
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : (n : ℝ) = 1 := by exact_mod_cast (show n = 1 by omega)
      rw [hn1]
      have hle : ∑ θ ∈ univ.image hA.eigenvalues,
          (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2
            ≤ 1 := by
        calc _ ≤ ∑ θ ∈ univ.image hA.eigenvalues,
              ∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a := by
              refine sum_le_sum fun θ hθ => ?_
              have hle1 : ∑ i with hA.eigenvalues i = θ,
                  hA.eigenvectorBasis i a * hA.eigenvectorBasis i a ≤ 1 := by
                rw [← hsum]
                exact single_le_sum (fun x _ => hnonneg x) hθ
              nlinarith [hnonneg θ]
          _ = 1 := hsum
      linarith
    · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h2
      obtain ⟨b, hb⟩ := exists_ne a
      obtain ⟨w⟩ := hG.preconnected a b
      cases w with
      | nil => exact absurd rfl hb
      | cons hadj _ =>
        refine simplex_bound _ _ (by exact_mod_cast h2) (fun θ _ => hnonneg θ) (fun θ _ => ?_) hsum
        -- the column `u = E_θ e_a` satisfies `A u = θ u` and `‖u‖² = u a`
        have hvec : (fun c => ∑ i with hA.eigenvalues i = θ,
            hA.eigenvectorBasis i c * hA.eigenvectorBasis i a) =
            ∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a • ⇑(hA.eigenvectorBasis i) := by
          ext c
          rw [Finset.sum_apply]
          refine sum_congr rfl fun i _ => ?_
          simp [mul_comm]
        have hmul : G.adjMatrix ℝ *ᵥ (fun c => ∑ i with hA.eigenvalues i = θ,
            hA.eigenvectorBasis i c * hA.eigenvectorBasis i a) =
            θ • fun c => ∑ i with hA.eigenvalues i = θ,
              hA.eigenvectorBasis i c * hA.eigenvectorBasis i a := by
          rw [hvec, mulVec_sum, Finset.smul_sum]
          refine sum_congr rfl fun i hi => ?_
          rw [mulVec_smul, hA.mulVec_eigenvectorBasis, (mem_filter.mp hi).2, smul_comm]
        have hnorm : ∑ c, (∑ i with hA.eigenvalues i = θ,
            hA.eigenvectorBasis i c * hA.eigenvectorBasis i a) ^ 2 =
            ∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a := by
          set S := (univ : Finset (Fin n)).filter (fun i => hA.eigenvalues i = θ)
          calc ∑ c, (∑ i ∈ S, hA.eigenvectorBasis i c * hA.eigenvectorBasis i a) ^ 2
              = ∑ c, ∑ i ∈ S, ∑ j ∈ S, (hA.eigenvectorBasis i a * hA.eigenvectorBasis j a) *
                  (hA.eigenvectorBasis i c * hA.eigenvectorBasis j c) := by
                refine sum_congr rfl fun c _ => ?_
                rw [sq, sum_mul_sum]
                exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
            _ = ∑ i ∈ S, ∑ j ∈ S, (hA.eigenvectorBasis i a * hA.eigenvectorBasis j a) *
                  ∑ c, hA.eigenvectorBasis i c * hA.eigenvectorBasis j c := by
                rw [sum_comm]
                refine sum_congr rfl fun i _ => ?_
                rw [sum_comm]
                exact sum_congr rfl fun j _ => by rw [mul_sum]
            _ = ∑ i ∈ S, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a := by
                refine sum_congr rfl fun i hi => ?_
                simp_rw [cols hA, mul_ite, mul_one, mul_zero]
                rw [sum_ite_eq S i]
                simp [hi]
        exact vertex_bound G _ θ hadj
          (fun c => by simpa [SimpleGraph.adjMatrix_mulVec_apply] using congrFun hmul c) hnorm
  have hT : ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ).IsHermitian :=
    isHermitian_iff_isSymm.mpr (⊤ : SimpleGraph (Fin n)).isSymm_adjMatrix
  have hG' : (n : ℝ) ^ 2 * (avgMixing G).trace ≤ n * (n ^ 2 - 2 * n + 2) := by
    rw [htrace G hA, mul_sum]
    calc ∑ a, (n : ℝ) ^ 2 * ∑ θ ∈ univ.image hA.eigenvalues,
          (∑ i with hA.eigenvalues i = θ, hA.eigenvectorBasis i a * hA.eigenvectorBasis i a) ^ 2
        ≤ ∑ _a : Fin n, ((n : ℝ) ^ 2 - 2 * n + 2) := sum_le_sum fun a _ => hdiag a
      _ = n * (n ^ 2 - 2 * n + 2) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hK : (n : ℝ) * (n ^ 2 - 2 * n + 2) ≤
      (n : ℝ) ^ 2 * (avgMixing (⊤ : SimpleGraph (Fin n))).trace := by
    rw [htrace ⊤ hT, mul_sum]
    calc (n : ℝ) * (n ^ 2 - 2 * n + 2) = ∑ _a : Fin n, ((n : ℝ) ^ 2 - 2 * n + 2) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun a _ =>
          complete_diag hT hpos a (rows hT a) (fun i => by simpa using cols hT i i)
  exact le_of_mul_le_mul_left (hG'.trans hK) (by positivity)

end D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
