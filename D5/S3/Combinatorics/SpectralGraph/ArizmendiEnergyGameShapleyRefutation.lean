/- GID: D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.claim
   digest: Complete bipartite graphs refute Shapley core membership for graph energy games. -/

/-
admission_basis: open-problem-resolution (#21951; Refuted).
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The source coalition total is inlined as Finset.sum; the proof uses Mathlib's
SimpleGraph.comap and adjMatrix for the complete bipartite graph and its matrix.
All theorem proofs are bind-only after same-module helpers are expanded;
the square-root sum bounds use Finset.sum_range_sub and sum_le_sum.
Direct frozen dependencies (declaration statement_id, not module pin):
F1: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind: sha256:3827af1eb14b3504427589ed624d2885edf890b3c9beb1a338e89ef0bf630e07
F2: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind.adjacency: sha256:5616222076d5da762c3aed4da7ec6cfc488ab6894e557456a8d4e9b1e49fb7d5
F3: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.averageDegree: sha256:9fbbbe8438abb272efbe2dc83c765fa8f00edfabbb5074403bdf58a01d9b6b77
F4: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy: sha256:73c5df8acc52e2401bee70c7828941498e9f333a24ecd1c074fd01b21c5d932c
F5: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy.match_1: sha256:7ac06afa51302fdec401c5f42703eb98f80dc17e6b55ad7579b090b065d44435
F6: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphSpectrum: sha256:8291dd1bc1d0040d3639bb40b905a235544695acdae1180a66d04c2470b4cc2b
F7: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.sourceMatrix: sha256:8494c96c2289763860006d56dd8768fdf7477f0c0b187d6e22a611010d1e9331
F8: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.source_matrix_isHermitian: sha256:0dab7839d261448f5717a90dac6d7793bf90588b6bf86799335cb21107b03899
F9: D5.S3.Arith.Lattices.Klartag.trace_mul_self_eq_sum_sq: sha256:889efcaa7ec27788f1354f8b3dfb39a05f10851ecb85104a8989f649d25f6ae6
Per-declaration classification (definitions introduce no proof witness):
worth: proof_shape: definition; escape_witness: none;
  Direct frozen dependencies: F2, F4; consumers: claim, worth_cut, two_scarce_profiles, family_not_core.
core: proof_shape: definition; escape_witness: none;
  Direct frozen dependencies: none; consumers: claim, family_not_core.
shapley: proof_shape: definition; escape_witness: none;
  Direct frozen dependencies: none; consumers: claim, scarce_payoff, family_not_core.
claim: proof_shape: definition; escape_witness: none;
  Direct frozen dependencies: F2, F4; consumers: result.
energy_of_cubic: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F9; consumers: cut_energy.
cut_matrix_square: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cut_matrix_cubic, cut_matrix_trace.
cut_matrix_cubic: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cut_energy.
cut_matrix_trace: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cut_energy.
cut_energy: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F6, F3, F1, F5, F4, F8, F2, F7, F9; consumers: worth_cut.
worth_cut: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F6, F3, F1, F5, F4, F8, F2, F7, F9; consumers: two_scarce_profiles.
sqrt_increment_lower: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: sum_sqrt_lower.
cube_sqrt_increment_upper: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: sum_cube_sqrt_upper.
sum_sqrt_lower: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: scarce_formula_gap.
sum_cube_sqrt_upper: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: scarce_formula_gap.
family_polynomial_positive: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: scarce_formula_gap.
scarce_formula_gap: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_not_core.
weight: proof_shape: definition; escape_witness: none;
  Direct frozen dependencies: none; consumers: choose_weight_first, choose_weight_second, scarce_payoff.
choose_weight_first: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: scarce_payoff.
choose_weight_second: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: scarce_payoff.
scarce_payoff: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_not_core.
two_scarce_profiles: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F6, F3, F1, F5, F4, F8, F2, F7, F9; consumers: family_not_core.
family_not_core: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F6, F3, F1, F5, F4, F8, F2, F7, F9; consumers: result.
result: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F6, F3, F1, F5, F4, F8, F2, F7, F9; consumers: none.
-/



import D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
import D5.S3.Arith.Lattices.Klartag.Drift.OneStep

/-! Binding definitions for Arizmendi--Arizmendi, arXiv:2012.14114v2,
Conjecture 3.10. Ordinary adjacency energy is reused from its existing D5
owner with MatrixKind.adjacency, which has center zero. -/

namespace D5.S3.Combinatorics.SpectralGraph.ArizmendiEnergyGameShapleyRefutation

open Finset

/-- Definition 3.1: w(S) is the ordinary energy of the induced graph I(S). -/
noncomputable def worth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℝ :=
  D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy
    (G.induce (S : Set V)) .adjacency

/-- Definition 2.7, displayed core formula, including all coalitions. -/
def core {V : Type} [Fintype V] (w : Finset V → ℝ) : Set (V → ℝ) :=
  {x | (∀ S : Finset V, (∑ i ∈ S, x i) ≥ w S) ∧
    (∑ i ∈ Finset.univ, x i) = w Finset.univ}

/-- Section 2.4, the literal factorial formula for the Shapley value.
The sum ranges over all subsets of N minus {i}. -/
noncomputable def shapley {V : Type} [Fintype V] [DecidableEq V]
    (w : Finset V → ℝ) (i : V) : ℝ :=
  ∑ S ∈ (Finset.univ.erase i).powerset,
    ((Nat.factorial S.card : ℝ) *
      (Nat.factorial (Fintype.card V - S.card - 1) : ℝ) /
      (Nat.factorial (Fintype.card V) : ℝ)) * (w (insert i S) - w S)

/-- Conjecture 3.10: for every finite simple undirected graph, the Shapley
value of its energy game is in its core. Fin n lists all finite sizes,
including the empty graph. No connectedness or bipartiteness restriction. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), shapley (worth G) ∈ core (worth G)

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

open Matrix Finset Unitary
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

private theorem energy_of_cubic {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (h3 : A * A * A = c • A) (h2 : (A * A).trace = 2 * c) :
    (∑ i, |hA.eigenvalues i|) = 2 * Real.sqrt c := by
  have hs (i : V) : hA.eigenvalues i = 0 ∨ hA.eigenvalues i ^ 2 = c := by
    have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ ⇑(hA.eigenvectorBasis i)) h3
    simp only [← mulVec_mulVec, smul_mulVec, mulVec_smul,
      hA.mulVec_eigenvectorBasis, smul_smul] at h
    have hn : (⇑(hA.eigenvectorBasis i) : V → ℝ) ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
    have he := smul_left_injective ℝ hn h
    have hf : hA.eigenvalues i * (hA.eigenvalues i ^ 2 - c) = 0 := by nlinarith [he]
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have ht : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 :=
    D5.S3.Arith.Lattices.Klartag.trace_mul_self_eq_sum_sq hA
  rcases eq_or_lt_of_le hc with rfl | hc
  · have hz (i : V) : hA.eigenvalues i = 0 := by
      rcases hs i with h | h
      · exact h
      · nlinarith [sq_nonneg (hA.eigenvalues i)]
    simp [hz]
  · have hq : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
    apply mul_left_cancel₀ hq
    rw [Finset.mul_sum]
    calc
      (∑ i, Real.sqrt c * |hA.eigenvalues i|) = ∑ i, hA.eigenvalues i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rcases hs i with h | h
        · simp [h]
        · have ha : |hA.eigenvalues i| = Real.sqrt c := by
            rw [← Real.sqrt_sq_eq_abs, h]
          rw [ha, ← pow_two, Real.sq_sqrt hc.le, h]
      _ = 2 * c := ht.symm.trans h2
      _ = Real.sqrt c * (2 * Real.sqrt c) := by nlinarith [Real.sq_sqrt hc.le]

private theorem cut_matrix_square {V : Type} [Fintype V] (b : V → Bool) (i j : V) :
    ((((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) * (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ)) i j =
      if b i = b j then
        if b i = false then ((univ.filter fun v => b v = true).card : ℝ)
        else ((univ.filter fun v => b v = false).card : ℝ)
      else 0 := by
  classical
  have ht (x : V) : (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) i x * (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) x j =
      if b i = b j then
        if b i = false then (if b x = true then (1 : ℝ) else 0)
        else (if b x = false then (1 : ℝ) else 0)
      else 0 := by
    cases hi : b i <;> cases hj : b j <;> cases hx : b x <;> norm_num [SimpleGraph.adjMatrix, SimpleGraph.comap, hi, hj, hx]
  rw [Matrix.mul_apply]
  simp_rw [ht]
  cases hi : b i <;> cases hj : b j <;> simp [hi, hj, Finset.sum_boole]

private theorem cut_matrix_cubic {V : Type} [Fintype V] (b : V → Bool) :
    (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) * (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) * (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) =
      (((univ.filter fun v => b v = false).card : ℝ) *
       ((univ.filter fun v => b v = true).card : ℝ)) • (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) := by
  classical
  ext i j
  have ht (x : V) : ((((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) * (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ)) i x * (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) x j =
      if b i = b j then 0 else
        if b i = false then
          (if b x = false then ((univ.filter fun v => b v = true).card : ℝ) else 0)
        else (if b x = true then ((univ.filter fun v => b v = false).card : ℝ) else 0) := by
    rw [cut_matrix_square]
    cases hi : b i <;> cases hj : b j <;> cases hx : b x <;> norm_num [SimpleGraph.adjMatrix, SimpleGraph.comap, hi, hj, hx]
  rw [Matrix.mul_apply]
  simp_rw [ht]
  cases hi : b i <;> cases hj : b j <;>
    simp [hi, hj, SimpleGraph.adjMatrix, SimpleGraph.comap, ← Finset.sum_filter, Finset.sum_const, Matrix.smul_apply] <;> ring

private theorem cut_matrix_trace {V : Type} [Fintype V] (b : V → Bool) :
    ((((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ) * (((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ)).trace =
      2 * (((univ.filter fun v => b v = false).card : ℝ) *
       ((univ.filter fun v => b v = true).card : ℝ)) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, cut_matrix_square, ite_true]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have he : (univ.filter fun v => ¬ b v = false) = (univ.filter fun v => b v = true) := by
    ext v; cases b v <;> simp
  rw [he]
  ring

private theorem cut_energy {V : Type} [Fintype V] (b : V → Bool) :
    graphEnergy (((⊤ : SimpleGraph Bool).comap b)) .adjacency =
      2 * Real.sqrt (((univ.filter fun v => b v = false).card : ℝ) *
        ((univ.filter fun v => b v = true).card : ℝ)) := by
  classical
  have hm : sourceMatrix ((⊤ : SimpleGraph Bool).comap b) .adjacency =
      ((⊤ : SimpleGraph Bool).comap b).adjMatrix ℝ := by
    ext i j
    simp [sourceMatrix, SimpleGraph.adjMatrix]
  have hA := source_matrix_isHermitian (((⊤ : SimpleGraph Bool).comap b)) .adjacency
  have he := energy_of_cubic _ hA
    (((univ.filter fun v => b v = false).card : ℝ) *
     ((univ.filter fun v => b v = true).card : ℝ)) (by positivity)
    (by simpa only [hm] using cut_matrix_cubic b)
    (by simpa only [hm] using cut_matrix_trace b)
  simpa only [graphEnergy, graphSpectrum, Multiset.map_map, Function.comp_def,
    sub_zero, RCLike.ofReal_real_eq_id, id_eq, Finset.sum] using he

private theorem worth_cut {V : Type} [Fintype V] [DecidableEq V]
    (b : V → Bool) (S : Finset V) :
    worth (((⊤ : SimpleGraph Bool).comap b)) S =
      2 * Real.sqrt (((S.filter fun v => b v = false).card : ℝ) *
        ((S.filter fun v => b v = true).card : ℝ)) := by
  classical
  have hg : (((⊤ : SimpleGraph Bool).comap b)).induce (S : Set V) = ((⊤ : SimpleGraph Bool).comap (fun v : (S : Set V) => b v.val)) := rfl
  unfold worth
  rw [hg, cut_energy]
  have hcount (t : Bool) :
      (univ.filter fun v : (S : Set V) => b v.val = t).card =
        (S.filter fun v => b v = t).card := by
    change (S.attach.filter fun v => b v.val = t).card = _
    rw [Finset.filter_attach (fun v : V => b v = t) S, Finset.card_map, Finset.card_attach]
  rw [hcount false, hcount true]

open Finset

private theorem sqrt_increment_lower (n : ℕ) :
    (2 / 3 : ℝ) * (n + 1) * Real.sqrt (n + 1) ≤
      (2 / 3 : ℝ) * n * Real.sqrt n + Real.sqrt (n + 1) := by
  rcases n with _ | n
  · norm_num
  · have hx : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hs : (((2 * ((n + 1 : ℕ) : ℝ) - 1) * Real.sqrt (((n + 1 : ℕ) : ℝ) + 1))) ^ 2 ≤
        (2 * ((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1),
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
      nlinarith
    have hl : 0 ≤ (2 * ((n + 1 : ℕ) : ℝ) - 1) * Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hr : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
    have hh := (sq_le_sq₀ hl hr).mp hs
    push_cast at hh ⊢
    nlinarith

private theorem cube_sqrt_increment_upper (n : ℕ) :
    ((2 / 5 : ℝ) * n ^ 2 + n) * Real.sqrt n ≤
      (2 / 5 : ℝ) * (n + 1) ^ 2 * Real.sqrt (n + 1) := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n : ℝ), mul_nonneg hn (sq_nonneg (n : ℝ))]

private theorem sum_sqrt_lower (n : ℕ) :
    (2 / 3 : ℝ) * n * Real.sqrt n ≤ ∑ k ∈ range (n + 1), Real.sqrt k := by
  let f (k : ℕ) : ℝ := (2 / 3 : ℝ) * k * Real.sqrt k
  have hs : (∑ k ∈ range n, (f (k + 1) - f k)) ≤
      ∑ k ∈ range n, Real.sqrt (k + 1 : ℕ) := by
    apply Finset.sum_le_sum
    intro k _
    have hk := sqrt_increment_lower k
    dsimp [f]
    push_cast at hk ⊢
    linarith
  rw [Finset.sum_range_sub] at hs
  have he := Finset.sum_range_succ' (fun k : ℕ => Real.sqrt k) n
  simp only [Nat.cast_zero, Real.sqrt_zero, add_zero] at he
  rw [← he] at hs
  simpa [f] using hs

private theorem sum_cube_sqrt_upper (n : ℕ) :
    (∑ k ∈ range (n + 1), (k : ℝ) * Real.sqrt k) ≤
      (2 / 5 : ℝ) * n ^ 2 * Real.sqrt n + n * Real.sqrt n := by
  let f (k : ℕ) : ℝ := (2 / 5 : ℝ) * k ^ 2 * Real.sqrt k
  have hs : (∑ k ∈ range n, (k : ℝ) * Real.sqrt k) ≤
      ∑ k ∈ range n, (f (k + 1) - f k) := by
    apply Finset.sum_le_sum
    intro k _
    have hk := cube_sqrt_increment_upper k
    dsimp [f]
    push_cast at hk ⊢
    nlinarith
  rw [Finset.sum_range_sub] at hs
  have hs' : (∑ k ∈ range n, (k : ℝ) * Real.sqrt k) ≤
      (2 / 5 : ℝ) * n ^ 2 * Real.sqrt n := by
    simpa [f] using hs
  rw [Finset.sum_range_succ]
  linarith

private theorem family_polynomial_positive (m : ℕ) (hm : 50 ≤ m) :
    0 < ((13 - 9 * Real.sqrt 2) / 15) * (m : ℝ) ^ 2 +
      (1 - 4 * Real.sqrt 2 / 3) * m + 2 - 2 * Real.sqrt 2 := by
  have hq : Real.sqrt 2 < (99 / 70 : ℝ) :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 99 / 70)).mpr (by norm_num)
  have hmR : (50 : ℝ) ≤ m := by exact Nat.ofNat_le_cast.mpr hm
  have hR : 0 < (19 * (m : ℝ) ^ 2 - 930 * m - 870) / 1050 := by
    nlinarith [sq_nonneg ((m : ℝ) - 50)]
  have hp : 0 < ((99 / 70 : ℝ) - Real.sqrt 2) *
      ((3 / 5 : ℝ) * (m : ℝ) ^ 2 + (4 / 3 : ℝ) * m + 2) := by
    apply mul_pos (sub_pos.mpr hq)
    positivity
  nlinarith

private theorem scarce_formula_gap (m : ℕ) (hm : 50 ≤ m) :
    2 * (Real.sqrt 2 - 1) * Real.sqrt m <
      (2 * (((m : ℝ) + Real.sqrt 2) * (∑ k ∈ range (m + 1), Real.sqrt k) +
        (Real.sqrt 2 - 2) * (∑ k ∈ range (m + 1), (k : ℝ) * Real.sqrt k))) /
        (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have hq : Real.sqrt 2 < (2 : ℝ) :=
    Real.sqrt_lt_self_iff.mpr (by norm_num)
  have h1 := mul_le_mul_of_nonneg_left (sum_sqrt_lower m)
    (show 0 ≤ (m : ℝ) + Real.sqrt 2 by positivity)
  have h3 := mul_le_mul_of_nonpos_left (sum_cube_sqrt_upper m)
    (show Real.sqrt 2 - 2 ≤ 0 by linarith)
  have hp := family_polynomial_positive m hm
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < m by omega))
  have hp' := mul_pos hs hp
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 2))).mpr
  nlinarith

open Finset

private noncomputable def weight (n k : ℕ) : ℝ :=
  (k.factorial : ℝ) * ((n - k - 1).factorial : ℝ) / (n.factorial : ℝ)

private theorem choose_weight_first (m k : ℕ) (hk : k ≤ m) :
    (m.choose k : ℝ) * weight (m + 2) k =
      ((m : ℝ) + 1 - k) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have hfac : (m.choose k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ) = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hsub : m + 2 - k - 1 = (m - k) + 1 := by omega
  have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub hk
  have hf : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  unfold weight
  rw [hsub, Nat.factorial_succ (m - k), Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast
  rw [hcast]
  calc
    _ = (((m : ℝ) + 1 - k) * ((m.choose k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ))) /
      ((((m : ℝ) + 1) * ((m : ℝ) + 2)) * (m.factorial : ℝ)) := by ring
    _ = _ := by rw [hfac]; field_simp

private theorem choose_weight_second (m k : ℕ) (hk : k ≤ m) :
    (m.choose k : ℝ) * weight (m + 2) (k + 1) =
      ((k : ℝ) + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have hfac : (m.choose k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ) = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hsub : m + 2 - (k + 1) - 1 = m - k := by omega
  have hf : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  unfold weight
  rw [hsub, Nat.factorial_succ k, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast
  calc
    _ = (((k : ℝ) + 1) * ((m.choose k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ))) /
      ((((m : ℝ) + 1) * ((m : ℝ) + 2)) * (m.factorial : ℝ)) := by ring
    _ = _ := by rw [hfac]; field_simp

private theorem scarce_payoff {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (a b : V) (B : Finset V) (hbB : b ∉ B)
    (hB : univ.erase a = insert b B) (hcard : B.card = m)
    (w : Finset V → ℝ)
    (h0 : ∀ T ∈ B.powerset, w T = 0)
    (ha : ∀ T ∈ B.powerset, w (insert a T) = 2 * Real.sqrt (T.card : ℝ))
    (hb : ∀ T ∈ B.powerset, w (insert b T) = 2 * Real.sqrt (T.card : ℝ))
    (hab : ∀ T ∈ B.powerset, w (insert a (insert b T)) = 2 * Real.sqrt 2 * Real.sqrt (T.card : ℝ)) :
    shapley w a =
      (2 * (((m : ℝ) + Real.sqrt 2) * (∑ k ∈ range (m + 1), Real.sqrt k) +
        (Real.sqrt 2 - 2) * (∑ k ∈ range (m + 1), (k : ℝ) * Real.sqrt k))) /
        (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  classical
  have hV : Fintype.card V = m + 2 := by
    have h := congrArg Finset.card hB
    rw [card_erase_of_mem (mem_univ a), card_insert_of_notMem hbB, card_univ, hcard] at h
    have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
    omega
  have hn (T : Finset V) (hT : T ∈ B.powerset) : b ∉ T :=
    notMem_mono (mem_powerset.mp hT) hbB
  unfold shapley
  rw [hB, Finset.sum_powerset_insert hbB]
  change (∑ T ∈ B.powerset, weight (Fintype.card V) T.card * (w (insert a T) - w T)) +
    (∑ T ∈ B.powerset, weight (Fintype.card V) (insert b T).card *
      (w (insert a (insert b T)) - w (insert b T))) = _
  rw [← sum_add_distrib]
  calc
    _ = ∑ T ∈ B.powerset,
        (weight (m + 2) T.card * (2 * Real.sqrt (T.card : ℝ)) +
          weight (m + 2) (T.card + 1) * ((2 * Real.sqrt 2 - 2) * Real.sqrt (T.card : ℝ))) := by
      apply sum_congr rfl
      intro T hT
      rw [hV, h0 T hT, ha T hT, hb T hT, hab T hT, card_insert_of_notMem (hn T hT)]
      ring
    _ = ∑ k ∈ range (m + 1), (m.choose k : ℝ) *
        (weight (m + 2) k * (2 * Real.sqrt (k : ℝ)) +
          weight (m + 2) (k + 1) * ((2 * Real.sqrt 2 - 2) * Real.sqrt (k : ℝ))) := by
      simpa only [hcard, nsmul_eq_mul] using
        (sum_powerset_apply_card (x := B) (fun k =>
          weight (m + 2) k * (2 * Real.sqrt (k : ℝ)) +
            weight (m + 2) (k + 1) * ((2 * Real.sqrt 2 - 2) * Real.sqrt (k : ℝ))))
    _ = ∑ k ∈ range (m + 1),
        (2 * (((m : ℝ) + Real.sqrt 2) * Real.sqrt k +
          (Real.sqrt 2 - 2) * ((k : ℝ) * Real.sqrt k))) /
          (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
      apply sum_congr rfl
      intro k hk
      have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
      rw [mul_add]
      simp only [← mul_assoc]
      rw [choose_weight_first m k hkm, choose_weight_second m k hkm]
      ring
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

open Finset

private theorem two_scarce_profiles {V : Type} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (T : Finset V) (haT : a ∉ T) (hbT : b ∉ T) :
    (let G := ((⊤ : SimpleGraph Bool).comap (fun i => decide (i ≠ a ∧ i ≠ b)))
    worth G T = 0 ∧
    worth G (insert a T) = 2 * Real.sqrt (T.card : ℝ) ∧
    worth G (insert b T) = 2 * Real.sqrt (T.card : ℝ) ∧
    worth G (insert a (insert b T)) = 2 * Real.sqrt 2 * Real.sqrt (T.card : ℝ)) := by
  classical
  let col : V → Bool := fun i => decide (i ≠ a ∧ i ≠ b)
  have hfalse : T.filter (fun i => col i = false) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hit := (mem_filter.mp hi).1
    have hn : i ≠ a ∧ i ≠ b := ⟨by intro h; exact haT (h ▸ hit), by intro h; exact hbT (h ▸ hit)⟩
    simpa [col, hn] using (mem_filter.mp hi).2
  have htrue : T.filter (fun i => col i = true) = T := by
    apply filter_eq_self.mpr
    intro i hi
    have hn : i ≠ a ∧ i ≠ b := ⟨by intro h; exact haT (h ▸ hi), by intro h; exact hbT (h ▸ hi)⟩
    simp [col, hn]
  change worth (((⊤ : SimpleGraph Bool).comap col)) T = 0 ∧
    worth (((⊤ : SimpleGraph Bool).comap col)) (insert a T) = 2 * Real.sqrt (T.card : ℝ) ∧
    worth (((⊤ : SimpleGraph Bool).comap col)) (insert b T) = 2 * Real.sqrt (T.card : ℝ) ∧
    worth (((⊤ : SimpleGraph Bool).comap col)) (insert a (insert b T)) = 2 * Real.sqrt 2 * Real.sqrt (T.card : ℝ)
  have hca : col a = false := by simp [col]
  have hcb : col b = false := by simp [col]
  simp only [worth_cut, filter_insert, hca, hcb, Bool.false_eq_true,
    if_true, if_false, hfalse, htrue]
  simp [hab, haT, hbT, Real.sqrt_mul (zero_le_two : (0 : ℝ) ≤ 2), mul_assoc]

private theorem family_not_core {V : Type} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 50 ≤ m) (hV : Fintype.card V = m + 2)
    (a b : V) (hab : a ≠ b) :
    (let G := ((⊤ : SimpleGraph Bool).comap (fun i => decide (i ≠ a ∧ i ≠ b)))
    shapley (worth G) ∉ core (worth G)) := by
  classical
  let G := ((⊤ : SimpleGraph Bool).comap (fun i : V => decide (i ≠ a ∧ i ≠ b)))
  change shapley (worth G) ∉ core (worth G)
  let B : Finset V := (univ.erase a).erase b
  have haB : a ∉ B := by simp [B]
  have hbB : b ∉ B := by exact notMem_erase b (univ.erase a)
  have hB : univ.erase a = insert b B := by simp [B, hab.symm]
  have hcard : B.card = m := by
    simp only [B, card_erase_of_mem (by simp [hab.symm] : b ∈ univ.erase a),
      card_erase_of_mem (mem_univ a), card_univ, hV]
    omega
  have hnot (T : Finset V) (hT : T ∈ B.powerset) : a ∉ T ∧ b ∉ T :=
    ⟨notMem_mono (mem_powerset.mp hT) haB, notMem_mono (mem_powerset.mp hT) hbB⟩
  have hphi := scarce_payoff m a b B hbB hB hcard (worth G)
    (fun T hT => (two_scarce_profiles a b hab T (hnot T hT).1 (hnot T hT).2).1)
    (fun T hT => (two_scarce_profiles a b hab T (hnot T hT).1 (hnot T hT).2).2.1)
    (fun T hT => (two_scarce_profiles a b hab T (hnot T hT).1 (hnot T hT).2).2.2.1)
    (fun T hT => (two_scarce_profiles a b hab T (hnot T hT).1 (hnot T hT).2).2.2.2)
  have hgap : 2 * (Real.sqrt 2 - 1) * Real.sqrt m < shapley (worth G) a := by
    rw [hphi]
    exact scarce_formula_gap m hm
  have hgrandset : insert a (insert b B) = univ := by rw [← hB]; simp
  have hprof := two_scarce_profiles a b hab B haB hbB
  have hgrand : worth G univ = 2 * Real.sqrt 2 * Real.sqrt m := by
    rw [← hgrandset]
    simpa only [hcard] using hprof.2.2.2
  have hcomp : worth G (univ.erase a) = 2 * Real.sqrt m := by
    rw [hB]
    simpa only [hcard] using hprof.2.2.1
  intro hcore
  change (∀ S : Finset V, (∑ i ∈ S, shapley (worth G) i) ≥ worth G S) ∧
    (∑ i ∈ univ, shapley (worth G) i) = worth G univ at hcore
  have hc := hcore.1 (univ.erase a)
  rw [hcomp] at hc
  have hsum := Finset.add_sum_erase (s := (univ : Finset V))
    (f := shapley (worth G)) (mem_univ a)
  change shapley (worth G) a + (∑ i ∈ univ.erase a, shapley (worth G) i) =
    (∑ i ∈ univ, shapley (worth G) i) at hsum
  rw [hcore.2, hgrand] at hsum
  nlinarith

theorem result : ¬ D5.S3.Combinatorics.SpectralGraph.ArizmendiEnergyGameShapleyRefutation.claim := by
  intro h
  exact family_not_core 50 (le_refl 50) (Fintype.card_fin 52)
    (0 : Fin 52) (1 : Fin 52) zero_ne_one
    (h 52 (((⊤ : SimpleGraph Bool).comap (fun i : Fin 52 => decide (i ≠ 0 ∧ i ≠ 1)))))

end D5.S3.Combinatorics.SpectralGraph.ArizmendiEnergyGameShapleyRefutation
