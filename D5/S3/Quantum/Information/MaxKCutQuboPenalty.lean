/- GID: D5/S3/Quantum/Information/MaxKCutQuboPenalty
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/MaxKCutQuboPenalty
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Conjectures 1 and 2 of arXiv:2511.01108 on tight max k-cut QUBO penalties. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the averaged
  colour-deletion moves `stepA` and `stepA2` (deleting one colour from every multiply coloured
  vertex and summing the change over all colours, with the edge bounds `hL` and `hD`) and the
  averaged colour-insertion move `stepB` for an empty vertex; the rearrangements `pair_regroup`
  and `pair_count` only support these moves
admission_basis: open-problem-resolution (issue #11239)
Direct frozen dependencies: D5/S3/Quantum/Entanglement/PhaseHistoryBound (module statement_id
  sha256:e4719c87fa3f8264afd02a8de664b52d595e2d47f4a42a82fe15d1c014db4a45):
  `bit` (sha256:7706541dc9903a7c132d1b1b7f22c9e43f2c374be384ba8d4e6974b1e067c424)
-/

import D5.S3.Quantum.Entanglement.PhaseHistoryBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.MaxKCutQuboPenalty

open Finset
open D5.S3.Quantum.Entanglement.PhaseHistoryBound (bit)

/-!
A. Harkness, H. Validi, R. Fakhimi, I. V. Hicks, S. Stein, T. Terlaky and L. F. Zuluaga,
*Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing*,
arXiv:2511.01108v3. With vertices `Fin n`, parts `Fin k` and symmetric real weights `w`, the
QUBO objective `q(x) = Σ_{u<v} w_uv (1 − Σ_j x_uj x_vj) − Σ_v c_v (Σ_j x_vj − 1)²` is maximised
over `x ∈ {0,1}^{n×k}`. The paper proves that every maximiser is an optimal k-cut when
`c_v > max(d⁺_v / k, −(3/2) d⁻_v)` and conjectures (Conjecture 1) the same for
`c_v > max(d⁺_v / k, −d⁻_v / 2)`; for the reduced objective on `k − 1` columns it proves the
bound `c_v > d⁺_v − 2 d⁻_v` and conjectures (Conjecture 2) `c_v > d⁺_v − d⁻_v`. Both hold:
deleting one colour from every vertex with several colours and averaging over the colours
gains at least `Σ_v (c_v + d⁻_v / 2) t_v (2 t_v − 3)`, respectively
`Σ_v (c_v − d⁺_v + d⁻_v) t_v (t_v − 1)`, which is positive, and an empty vertex gains on
average `c_v − d⁺_v / k` from receiving a colour.
-/

/-- `d⁺_v`: the sum of the positive weights at `v`. -/
noncomputable def dplus {n : ℕ} (w : Fin n → Fin n → ℝ) (v : Fin n) : ℝ :=
  ∑ u ∈ univ.filter (fun u => u ≠ v ∧ 0 < w u v), w u v

/-- `d⁻_v`: the sum of the negative weights at `v`. -/
noncomputable def dminus {n : ℕ} (w : Fin n → Fin n → ℝ) (v : Fin n) : ℝ :=
  ∑ u ∈ univ.filter (fun u => u ≠ v ∧ w u v < 0), w u v

/-- The BQO objective `g(x) = Σ_{u<v} w_uv (1 − Σ_j x_uj x_vj)`, the weight of the cut. -/
noncomputable def cutValue {n k : ℕ} (w : Fin n → Fin n → ℝ) (x : Fin n → Fin k → Bool) : ℝ :=
  ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (1 - ∑ j, bit (x u j) * bit (x v j))

/-- The QUBO objective `q(x) = g(x) − Σ_v c_v (Σ_j x_vj − 1)²`. -/
noncomputable def quboObjective {n k : ℕ} (w : Fin n → Fin n → ℝ) (c : Fin n → ℝ)
    (x : Fin n → Fin k → Bool) : ℝ :=
  cutValue w x - ∑ v, c v * (∑ j, bit (x v j) - 1) ^ 2

/-- The BQO constraint `Σ_j x_vj = 1` for every vertex. -/
def OneHot {n k : ℕ} (x : Fin n → Fin k → Bool) : Prop := ∀ v, ∑ j, bit (x v j) = 1

/-- The R-BQO objective on `k − 1` columns,
`Σ_{u<v} w_uv (1 − Σ_j x_uj x_vj − (1 − Σ_j x_uj)(1 − Σ_j x_vj))`. -/
noncomputable def reducedCutValue {n m : ℕ} (w : Fin n → Fin n → ℝ)
    (x : Fin n → Fin m → Bool) : ℝ :=
  ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v *
    (1 - ∑ j, bit (x u j) * bit (x v j) - (1 - ∑ j, bit (x u j)) * (1 - ∑ j, bit (x v j)))

/-- The R-QUBO objective `q̄(x) = ḡ(x) − Σ_v c_v Σ_{i<j} x_vi x_vj`. -/
noncomputable def reducedQuboObjective {n m : ℕ} (w : Fin n → Fin n → ℝ) (c : Fin n → ℝ)
    (x : Fin n → Fin m → Bool) : ℝ :=
  reducedCutValue w x -
    ∑ v, c v * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), bit (x v i) * bit (x v j)

/-- The R-BQO constraint `Σ_j x_vj ≤ 1` for every vertex. -/
def AtMostOneHot {n m : ℕ} (x : Fin n → Fin m → Bool) : Prop := ∀ v, ∑ j, bit (x v j) ≤ 1

/-- Conjecture 1: for `k ≥ 3` and `c_v > max(d⁺_v / k, −d⁻_v / 2)`, every maximiser of the
QUBO objective is BQO-feasible and maximises the cut weight among feasible points. -/
def quboPenaltyConjecture : Prop :=
  ∀ (n k : ℕ) (w : Fin n → Fin n → ℝ) (c : Fin n → ℝ), 3 ≤ k → (∀ u v, w u v = w v u) →
    (∀ v, max (dplus w v / k) (-dminus w v / 2) < c v) →
    ∀ xh : Fin n → Fin k → Bool,
      (∀ x : Fin n → Fin k → Bool, quboObjective w c x ≤ quboObjective w c xh) →
      OneHot xh ∧ ∀ x : Fin n → Fin k → Bool, OneHot x → cutValue w x ≤ cutValue w xh

/-- Conjecture 2: for `k − 1 = m ≥ 2` columns and `c_v > d⁺_v − d⁻_v`, every maximiser of the
R-QUBO objective is R-BQO-feasible and maximises the R-BQO objective among feasible points. -/
def reducedQuboPenaltyConjecture : Prop :=
  ∀ (n m : ℕ) (w : Fin n → Fin n → ℝ) (c : Fin n → ℝ), 2 ≤ m → (∀ u v, w u v = w v u) →
    (∀ v, dplus w v - dminus w v < c v) →
    ∀ xh : Fin n → Fin m → Bool,
      (∀ x : Fin n → Fin m → Bool, reducedQuboObjective w c x ≤ reducedQuboObjective w c xh) →
      AtMostOneHot xh ∧
        ∀ x : Fin n → Fin m → Bool, AtMostOneHot x → reducedCutValue w x ≤ reducedCutValue w xh

/-- Conjectures 1 and 2 of arXiv:2511.01108. -/
def claim : Prop := quboPenaltyConjecture ∧ reducedQuboPenaltyConjecture

set_option maxHeartbeats 2000000 in
-- The averaged moves expand large finite sums inside this single declaration.
/-- Both conjectures hold. -/
theorem result : claim := by
  have bit_sq :
      ∀ (b : Bool), bit b * bit b = bit b := by
    intro b
    cases b <;> simp [bit]
  have bit_nonneg :
      ∀ (b : Bool), 0 ≤ bit b := by
    intro b
    cases b <;> simp [bit]
  have bit_le_one :
      ∀ (b : Bool), bit b ≤ 1 := by
    intro b
    cases b <;> simp [bit]
  have pair_regroup : ∀ {n : ℕ} (F : Fin n → Fin n → ℝ), (∀ u v, F u v = F v u) →
      ∀ G : Fin n → ℝ,
      ∑ u, ∑ v ∈ univ.filter (fun v => u < v), F u v * (G u + G v) =
        ∑ v, G v * ∑ u ∈ univ.filter (fun u => u ≠ v), F u v := by
    intro n F hF G
    simp only [Finset.sum_filter, Finset.mul_sum]
    have h1 : ∀ u v : Fin n, (if u < v then F u v * (G u + G v) else 0) =
        (if u < v then G u * F v u else 0) + (if u < v then G v * F u v else 0) := by
      intro u v; split_ifs <;> simp [hF u v]; ring
    simp_rw [h1, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun u v => if u < v then G v * F u v else 0)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rcases lt_trichotomy u v with h | h | h
    · simp [h, not_lt.2 h.le, h.ne]
    · subst h; simp
    · simp [h, not_lt.2 h.le, h.ne', hF u v]
  have dminus_eq : ∀ {n : ℕ} (w : Fin n → Fin n → ℝ) (v : Fin n),
      ∑ u ∈ univ.filter (fun u => u ≠ v), min (w u v) 0 = dminus w v := by
    intro n w v
    unfold dminus
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h1 : u ≠ v
    · by_cases h2 : w u v < 0
      · simp [h1, h2, min_eq_left h2.le]
      · simp [h1, h2, min_eq_right (not_lt.1 h2)]
    · simp [h1]
  have stepA : ∀ {n k : ℕ} (w : Fin n → Fin n → ℝ) (c : Fin n → ℝ), (∀ u v, w u v = w v u) →
      (∀ v, -dminus w v / 2 < c v) → ∀ xh : Fin n → Fin k → Bool,
      (∀ x : Fin n → Fin k → Bool, quboObjective w c x ≤ quboObjective w c xh) →
      ∀ v, ∑ j, bit (xh v j) ≤ 1 := by
    intro n k w c hw hc xh hopt
    by_contra hcon
    push Not at hcon
    obtain ⟨v0, hv0⟩ := hcon
    set a : Fin n → Fin k → ℝ := fun v j => bit (xh v j) with ha
    set T : Fin n → ℝ := fun v => ∑ j, a v j with hTdef
    have hTnat : ∀ v, T v = ((univ.filter (fun j => xh v j = true)).card : ℝ) := by
      intro v
      simp only [T, a, bit, Finset.sum_boole]
    let V2 : Finset (Fin n) := univ.filter (fun v => 1 < T v)
    let e : Fin n → ℝ := fun v => if v ∈ V2 then 1 else 0
    let δ : Fin k → Fin k → ℝ := fun i j => if i = j then 1 else 0
    let y : Fin k → Fin n → Fin k → Bool :=
      fun j v i => xh v i && !(decide (v ∈ V2) && decide (i = j))
    have hy : ∀ j v i, bit (y j v i) = a v i * (1 - e v * δ i j) := by
      intro j v i
      simp only [y, a, e, δ, bit]
      by_cases h1 : v ∈ V2 <;> by_cases h2 : i = j <;> by_cases h3 : xh v i = true <;>
        simp [h1, h2, h3]
    have ha01 : ∀ v i, a v i * a v i = a v i := fun v i => bit_sq _
    have hδ : ∀ i, ∑ j, δ i j = 1 := by intro i; simp [δ]
    -- the averaged edge identity
    have hI1 : ∀ u v, ∑ j, ∑ i, bit (y j u i) * bit (y j v i) =
        (k - (e u + e v - e u * e v)) * ∑ i, a u i * a v i := by
      intro u v
      simp_rw [hy]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have : ∀ j, a u i * (1 - e u * δ i j) * (a v i * (1 - e v * δ i j)) =
          a u i * a v i * (1 - (e u + e v - e u * e v) * δ i j) := by
        intro j
        have hδ2 : δ i j * δ i j = δ i j := by simp only [δ]; split_ifs <;> simp
        linear_combination (a u i * a v i * e u * e v) * hδ2
      simp_rw [this, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hδ]
      simp
      ring
    -- the averaged penalty identity
    have hI2 : ∀ v, ∑ j, (∑ i, bit (y j v i) - 1) ^ 2 =
        k * (T v - 1) ^ 2 - e v * T v * (2 * T v - 3) := by
      intro v
      have hrow : ∀ j, ∑ i, bit (y j v i) = T v - e v * a v j := by
        intro j
        simp_rw [hy]
        simp only [T, mul_sub, mul_one, Finset.sum_sub_distrib]
        congr 1
        simp only [δ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
      simp_rw [hrow]
      have he2 : e v * e v = e v := by simp only [e]; split_ifs <;> simp
      have : ∀ j, (T v - e v * a v j - 1) ^ 2 =
          (T v - 1) ^ 2 - (2 * (T v - 1) * e v - e v) * a v j := by
        intro j
        linear_combination (e v * e v) * ha01 v j + (a v j) * he2
      simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [T]
      ring
    -- the averaged gain
    let M : Fin n → Fin n → ℝ := fun u v => ∑ i, a u i * a v i
    let τ : Fin n → Fin n → ℝ := fun u v => e u + e v - e u * e v
    let P : Fin n → ℝ := fun v => e v * T v * (2 * T v - 3)
    have hcut : ∑ j, cutValue w (y j) =
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (k - (k - τ u v) * M u v) := by
      unfold cutValue
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hI1]
      simp [M, τ]
    have hpen : ∑ j, ∑ v, c v * (∑ i, bit (y j v i) - 1) ^ 2 =
        ∑ v, c v * (k * (T v - 1) ^ 2 - P v) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, hI2]
    have hxh : quboObjective w c xh =
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (1 - M u v) -
          ∑ v, c v * (T v - 1) ^ 2 := by
      simp [quboObjective, cutValue, M, T, a]
    have key : ∑ j, (quboObjective w c (y j) - quboObjective w c xh) =
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (τ u v * M u v) +
          ∑ v, c v * P v := by
      have hyobj : ∑ j, quboObjective w c (y j) =
          ∑ j, cutValue w (y j) - ∑ j, ∑ v, c v * (∑ i, bit (y j v i) - 1) ^ 2 := by
        simp only [quboObjective, Finset.sum_sub_distrib]
      rw [Finset.sum_sub_distrib, hyobj, hcut, hpen, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hxh]
      have hA : ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (k - (k - τ u v) * M u v) -
          (k : ℝ) * ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (1 - M u v) =
          ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (τ u v * M u v) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      have hB : (k : ℝ) * ∑ v, c v * (T v - 1) ^ 2 - ∑ v, c v * (k * (T v - 1) ^ 2 - P v) =
          ∑ v, c v * P v := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      linear_combination hA + hB
    -- bounds on the overlaps and the sizes
    have ha0 : ∀ v i, 0 ≤ a v i := fun v i => bit_nonneg _
    have ha1 : ∀ v i, a v i ≤ 1 := fun v i => bit_le_one _
    have hM0 : ∀ u v, 0 ≤ M u v := fun u v =>
      Finset.sum_nonneg fun i _ => mul_nonneg (ha0 u i) (ha0 v i)
    have hMu : ∀ u v, M u v ≤ T u := fun u v =>
      Finset.sum_le_sum fun i _ => by nlinarith [ha0 u i, ha0 v i, ha1 v i]
    have hMv : ∀ u v, M u v ≤ T v := fun u v =>
      Finset.sum_le_sum fun i _ => by nlinarith [ha0 u i, ha0 v i, ha1 u i]
    have hin : ∀ v, v ∈ V2 → 2 ≤ T v := by
      intro v hv
      have h1 : 1 < T v := (Finset.mem_filter.1 hv).2
      rw [hTnat] at h1 ⊢
      have : 1 < (univ.filter (fun j => xh v j = true)).card := by exact_mod_cast h1
      exact_mod_cast this
    have hout : ∀ v, v ∉ V2 → T v ≤ 1 := by
      intro v hv
      by_contra h
      exact hv (Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
    have hP0 : ∀ v, 0 ≤ P v := by
      intro v
      by_cases hv : v ∈ V2
      · have := hin v hv
        simp only [P, e, hv, if_true, one_mul]
        nlinarith
      · simp [P, e, hv]
    have hL : ∀ u v, τ u v * M u v ≤ (P u + P v) / 2 := by
      intro u v
      by_cases hu : u ∈ V2 <;> by_cases hv : v ∈ V2
      · have h1 := hin u hu; have h2 := hin v hv
        simp only [τ, P, e, hu, hv, if_true]
        nlinarith [hMu u v, hMv u v]
      · have h1 := hin u hu; have h2 := hout v hv
        simp only [τ, P, e, hu, hv, if_true, if_false]
        nlinarith [hMv u v]
      · have h1 := hout u hu; have h2 := hin v hv
        simp only [τ, P, e, hu, hv, if_true, if_false]
        nlinarith [hMu u v]
      · simp only [τ, P, e, hu, hv, if_false]
        nlinarith
    have hτ0 : ∀ u v, 0 ≤ τ u v * M u v := by
      intro u v
      apply mul_nonneg _ (hM0 u v)
      simp only [τ, e]
      split_ifs <;> norm_num
    have hedge : ∀ u v, min (w u v) 0 / 2 * (P u + P v) ≤ w u v * (τ u v * M u v) := by
      intro u v
      by_cases hw0 : 0 ≤ w u v
      · rw [min_eq_right hw0]
        simp only [zero_div, zero_mul]
        exact mul_nonneg hw0 (hτ0 u v)
      · push Not at hw0
        rw [min_eq_left hw0.le]
        nlinarith [hL u v]
    have hgain : ∑ v, P v * (c v + dminus w v / 2) ≤
        ∑ j, (quboObjective w c (y j) - quboObjective w c xh) := by
      rw [key]
      have hsym : ∀ u v, min (w u v) 0 / 2 = min (w v u) 0 / 2 := by intro u v; rw [hw u v]
      have hreg := pair_regroup (fun u v => min (w u v) 0 / 2) hsym P
      have hle : ∑ u, ∑ v ∈ univ.filter (fun v => u < v), min (w u v) 0 / 2 * (P u + P v) ≤
          ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (τ u v * M u v) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hedge u v
      rw [hreg] at hle
      have hdm : ∀ v, ∑ u ∈ univ.filter (fun u => u ≠ v), min (w u v) 0 / 2 = dminus w v / 2 := by
        intro v
        rw [← Finset.sum_div, dminus_eq]
      simp only [hdm] at hle
      have : ∑ v, P v * (c v + dminus w v / 2) = ∑ v, P v * (dminus w v / 2) + ∑ v, c v * P v := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [this]
      linarith
    have hpos : 0 < ∑ v, P v * (c v + dminus w v / 2) := by
      have hv0m : v0 ∈ V2 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hv0⟩
      apply Finset.sum_pos' (fun v _ => mul_nonneg (hP0 v) (by linarith [hc v]))
      refine ⟨v0, Finset.mem_univ _, mul_pos ?_ (by linarith [hc v0])⟩
      have := hin v0 hv0m
      simp only [P, e, hv0m, if_true, one_mul]
      nlinarith
    obtain ⟨j, _, hj⟩ := Finset.exists_lt_of_sum_lt
      (show ∑ _j : Fin k, (0 : ℝ) < ∑ j, (quboObjective w c (y j) - quboObjective w c xh) by
        simp only [Finset.sum_const_zero]; linarith)
    linarith [hopt (y j)]
  have dplus_eq : ∀ {n : ℕ} (w : Fin n → Fin n → ℝ) (v : Fin n),
      ∑ u ∈ univ.filter (fun u => u ≠ v), max (w u v) 0 = dplus w v := by
    intro n w v
    unfold dplus
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h1 : u ≠ v
    · by_cases h2 : 0 < w u v
      · simp [h1, h2, max_eq_left h2.le]
      · simp [h1, h2, max_eq_right (not_lt.1 h2)]
    · simp [h1]
  have stepB : ∀ {n k : ℕ} (w : Fin n → Fin n → ℝ) (c : Fin n → ℝ), (∀ u v, w u v = w v u) →
      0 < k → (∀ v, dplus w v / k < c v) → ∀ xh : Fin n → Fin k → Bool,
      (∀ x : Fin n → Fin k → Bool, quboObjective w c x ≤ quboObjective w c xh) →
      (∀ v, ∑ j, bit (xh v j) ≤ 1) → ∀ v, 1 ≤ ∑ j, bit (xh v j) := by
    intro n k w c hw hk hc xh hopt hA
    by_contra hcon
    push Not at hcon
    obtain ⟨v0, hv0⟩ := hcon
    let a : Fin n → Fin k → ℝ := fun v j => bit (xh v j)
    let T : Fin n → ℝ := fun v => ∑ j, a v j
    have ha0 : ∀ v i, 0 ≤ a v i := fun v i => bit_nonneg _
    have ha1 : ∀ v i, a v i ≤ 1 := fun v i => bit_le_one _
    have hzero : ∀ j, a v0 j = 0 := by
      intro j
      have hle : a v0 j ≤ T v0 := Finset.single_le_sum (fun i _ => ha0 v0 i) (Finset.mem_univ j)
      have : a v0 j < 1 := lt_of_le_of_lt hle hv0
      simp only [a, bit] at this ⊢
      split_ifs at this ⊢ <;> simp_all
    have hT0 : T v0 = 0 := Finset.sum_eq_zero fun j _ => hzero j
    have hT01 : ∀ v, 0 ≤ T v ∧ T v ≤ 1 := fun v =>
      ⟨Finset.sum_nonneg fun i _ => ha0 v i, hA v⟩
    let ε : Fin n → ℝ := fun v => if v = v0 then 1 else 0
    let δ : Fin k → Fin k → ℝ := fun j i => if j = i then 1 else 0
    let z : Fin k → Fin n → Fin k → Bool :=
      fun i v j => xh v j || (decide (v = v0) && decide (j = i))
    have hz : ∀ i v j, bit (z i v j) = a v j + ε v * δ j i := by
      intro i v j
      by_cases h1 : v = v0
      · subst h1
        have := hzero j
        simp only [a, bit] at this
        by_cases h2 : j = i <;> by_cases h3 : xh v j = true <;> simp_all [z, ε, δ, bit]
      · simp [z, ε, δ, bit, h1, a]
    have hεT : ∀ v, ε v * T v = 0 := by
      intro v; by_cases h : v = v0
      · simp [ε, h, hT0]
      · simp [ε, h]
    have hεε : ∀ u v, u < v → ε u * ε v = 0 := by
      intro u v huv
      by_cases h : u = v0
      · have : v ≠ v0 := by rintro rfl; exact absurd huv (by rw [h]; exact lt_irrefl _)
        simp [ε, this]
      · simp [ε, h]
    have hδ : ∀ j, ∑ i, δ j i = 1 := by intro j; simp [δ]
    have hedgesum : ∀ u v, u < v → ∑ i, ∑ j, bit (z i u j) * bit (z i v j) =
        k * (∑ j, a u j * a v j) + ε v * T u + ε u * T v := by
      intro u v huv
      simp_rw [hz]
      have : ∀ i j, (a u j + ε u * δ j i) * (a v j + ε v * δ j i) =
          a u j * a v j + ε v * (a u j * δ j i) + ε u * (a v j * δ j i) +
            ε u * ε v * (δ j i * δ j i) := by intro i j; ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hεε u v huv, zero_mul, add_zero]
      rw [Finset.sum_comm (f := fun i j => a u j * δ j i),
        Finset.sum_comm (f := fun i j => a v j * δ j i)]
      simp only [δ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, T]
    have key : ∑ i, (quboObjective w c (z i) - quboObjective w c xh) =
        k * c v0 - ∑ u ∈ univ.filter (fun u => u ≠ v0), w u v0 * T u := by
      -- edge part via regrouping
      have hreg := pair_regroup (fun u v => w u v * (T u + T v))
        (fun u v => by rw [hw u v, add_comm]) ε
      have hreg' : ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (ε v * T u + ε u * T v) =
          ∑ u ∈ univ.filter (fun u => u ≠ v0), w u v0 * T u := by
        have e1 : ∀ u v, w u v * (ε v * T u + ε u * T v) =
            w u v * (T u + T v) * (ε u + ε v) := by
          intro u v
          linear_combination (-(w u v)) * hεT u + (-(w u v)) * hεT v
        simp_rw [e1]
        rw [hreg]
        rw [Finset.sum_eq_single v0]
        · simp only [ε, if_true, one_mul]
          apply Finset.sum_congr rfl
          intro u _
          rw [hT0, add_zero]
        · intro v _ hv; simp [ε, hv]
        · intro h; exact absurd (Finset.mem_univ v0) h
      have hcutz : ∑ i, cutValue w (z i) =
          ∑ u, ∑ v ∈ univ.filter (fun v => u < v),
            w u v * (k - (k * (∑ j, a u j * a v j) + ε v * T u + ε u * T v)) := by
        unfold cutValue
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hedgesum u v (Finset.mem_filter.1 hv).2]
        simp
      have hpenz : ∑ i, ∑ v, c v * (∑ j, bit (z i v j) - 1) ^ 2 =
          ∑ v, c v * (k * (T v + ε v - 1) ^ 2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.mul_sum]
        congr 1
        have hrow : ∀ i, ∑ j, bit (z i v j) = T v + ε v := by
          intro i
          simp_rw [hz, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [δ, T]
        simp [hrow]
      have hxh : quboObjective w c xh =
          ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (1 - ∑ j, a u j * a v j) -
            ∑ v, c v * (T v - 1) ^ 2 := by
        simp [quboObjective, cutValue, T, a]
      have hzobj : ∑ i, quboObjective w c (z i) =
          ∑ i, cutValue w (z i) - ∑ i, ∑ v, c v * (∑ j, bit (z i v j) - 1) ^ 2 := by
        simp only [quboObjective, Finset.sum_sub_distrib]
      rw [Finset.sum_sub_distrib, hzobj, hcutz, hpenz, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hxh]
      have hE : ∑ u, ∑ v ∈ univ.filter (fun v => u < v),
            w u v * (k - (k * (∑ j, a u j * a v j) + ε v * T u + ε u * T v)) -
          (k : ℝ) * ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (1 - ∑ j, a u j * a v j) =
          -∑ u ∈ univ.filter (fun u => u ≠ v0), w u v0 * T u := by
        rw [← hreg', Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      have hP : (k : ℝ) * ∑ v, c v * (T v - 1) ^ 2 - ∑ v, c v * (k * (T v + ε v - 1) ^ 2) =
          k * c v0 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single v0]
        · simp [ε, hT0]
        · intro v _ hv; simp [ε, hv]; ring
        · intro h; exact absurd (Finset.mem_univ v0) h
      linear_combination hE + hP
    have hbound : ∑ u ∈ univ.filter (fun u => u ≠ v0), w u v0 * T u ≤ dplus w v0 := by
      rw [← dplus_eq]
      apply Finset.sum_le_sum
      intro u _
      obtain ⟨h0, h1⟩ := hT01 u
      by_cases hw0 : 0 ≤ w u v0
      · rw [max_eq_left hw0]; nlinarith
      · push Not at hw0
        rw [max_eq_right hw0.le]; nlinarith
    have hkc : dplus w v0 < k * c v0 := by
      have := hc v0
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [div_lt_iff₀ hk'] at this
      linarith
    obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt
      (show ∑ _i : Fin k, (0 : ℝ) < ∑ i, (quboObjective w c (z i) - quboObjective w c xh) by
        rw [key]; simp only [Finset.sum_const_zero]; linarith)
    linarith [hopt (z i)]
  have conj1_holds :
      quboPenaltyConjecture := by
    intro n k w c hk hw hc xh hopt
    have hA := stepA w c hw (fun v => lt_of_le_of_lt (le_max_right _ _) (hc v)) xh hopt
    have hB := stepB w c hw (by omega) (fun v => lt_of_le_of_lt (le_max_left _ _) (hc v)) xh hopt hA
    have hone : OneHot xh := fun v => le_antisymm (hA v) (hB v)
    refine ⟨hone, fun x hx => ?_⟩
    have e1 : ∀ y : Fin n → Fin k → Bool, OneHot y → quboObjective w c y = cutValue w y := by
      intro y hy
      have : ∀ v, (∑ j, bit (y v j) - 1) ^ 2 = 0 := fun v => by rw [hy v]; ring
      simp [quboObjective, this]
    have := hopt x
    rw [e1 x hx, e1 xh hone] at this
    exact this
  have pair_count : ∀ {m : ℕ} (b : Fin m → Bool),
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), bit (b i) * bit (b j) =
        ((∑ j, bit (b j)) ^ 2 - ∑ j, bit (b j)) / 2 := by
    intro m b
    have hreg := pair_regroup (n := m) (fun i j => bit (b i) * bit (b j)) (fun i j => mul_comm _ _)
      (fun _ => (1 / 2 : ℝ))
    have e1 : ∀ i j : Fin m, bit (b i) * bit (b j) * (1 / 2 + 1 / 2) = bit (b i) * bit (b j) := by
      intro i j; ring
    simp only [e1] at hreg
    rw [hreg]
    have hsq : (∑ j, bit (b j)) ^ 2 = ∑ j, ∑ i, bit (b i) * bit (b j) := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_comm]
    have hsplit : ∀ j, ∑ i, bit (b i) * bit (b j) =
        ∑ i ∈ univ.filter (fun i => i ≠ j), bit (b i) * bit (b j) + bit (b j) := by
      intro j
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => i ≠ j)]
      congr 1
      rw [Finset.sum_eq_single j]
      · simp [bit_sq]
      · intro i hi hij; exact absurd (by simpa using hi) hij
      · intro h; simp at h
    rw [hsq]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    ring
  have stepA2 : ∀ {n m : ℕ} (w : Fin n → Fin n → ℝ) (c : Fin n → ℝ), (∀ u v, w u v = w v u) →
      (∀ v, dplus w v - dminus w v < c v) → ∀ xh : Fin n → Fin m → Bool,
      (∀ x : Fin n → Fin m → Bool,
        reducedQuboObjective w c x ≤ reducedQuboObjective w c xh) →
      ∀ v, ∑ j, bit (xh v j) ≤ 1 := by
    intro n m w c hw hc xh hopt
    by_contra hcon
    push Not at hcon
    obtain ⟨v0, hv0⟩ := hcon
    let a : Fin n → Fin m → ℝ := fun v j => bit (xh v j)
    let T : Fin n → ℝ := fun v => ∑ j, a v j
    have hTnat : ∀ v, T v = ((univ.filter (fun j => xh v j = true)).card : ℝ) := by
      intro v
      simp only [T, a, bit, Finset.sum_boole]
    let V2 : Finset (Fin n) := univ.filter (fun v => 1 < T v)
    let e : Fin n → ℝ := fun v => if v ∈ V2 then 1 else 0
    let δ : Fin m → Fin m → ℝ := fun i j => if i = j then 1 else 0
    let y : Fin m → Fin n → Fin m → Bool :=
      fun j v i => xh v i && !(decide (v ∈ V2) && decide (i = j))
    have hy : ∀ j v i, bit (y j v i) = a v i * (1 - e v * δ i j) := by
      intro j v i
      simp only [y, a, e, δ, bit]
      by_cases h1 : v ∈ V2 <;> by_cases h2 : i = j <;> by_cases h3 : xh v i = true <;>
        simp [h1, h2, h3]
    have ha01 : ∀ v i, a v i * a v i = a v i := fun v i => bit_sq _
    have hδ : ∀ i, ∑ j, δ i j = 1 := by intro i; simp [δ]
    have he2 : ∀ v, e v * e v = e v := by intro v; simp only [e]; split_ifs <;> simp
    let M : Fin n → Fin n → ℝ := fun u v => ∑ i, a u i * a v i
    let τ : Fin n → Fin n → ℝ := fun u v => e u + e v - e u * e v
    have hI1 : ∀ u v, ∑ j, ∑ i, bit (y j u i) * bit (y j v i) = (m - τ u v) * M u v := by
      intro u v
      simp_rw [hy]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have : ∀ j, a u i * (1 - e u * δ i j) * (a v i * (1 - e v * δ i j)) =
          a u i * a v i * (1 - (e u + e v - e u * e v) * δ i j) := by
        intro j
        have hδ2 : δ i j * δ i j = δ i j := by simp only [δ]; split_ifs <;> simp
        linear_combination (a u i * a v i * e u * e v) * hδ2
      simp_rw [this, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hδ]
      simp [τ]
      ring
    have hrow : ∀ j v, ∑ i, bit (y j v i) = T v - e v * a v j := by
      intro j v
      simp_rw [hy]
      simp only [T, mul_sub, mul_one, Finset.sum_sub_distrib]
      congr 1
      simp only [δ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    -- the averaged edge term of the reduced objective
    let D : Fin n → Fin n → ℝ := fun u v =>
      -(τ u v * M u v) + e u * T u * (1 - T v) + e v * T v * (1 - T u) + e u * e v * M u v
    have hIO : ∀ u v, ∑ j, (1 - ∑ i, bit (y j u i) * bit (y j v i) -
        (1 - ∑ i, bit (y j u i)) * (1 - ∑ i, bit (y j v i))) =
        m * (1 - M u v - (1 - T u) * (1 - T v)) - D u v := by
      intro u v
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hI1]
      simp_rw [hrow]
      have : ∀ j, (1 - (T u - e u * a u j)) * (1 - (T v - e v * a v j)) =
          (1 - T u) * (1 - T v) + (1 - T u) * e v * a v j + (1 - T v) * e u * a u j +
            e u * e v * (a u j * a v j) := by intro j; ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [D, M, T]
      ring
    -- the averaged penalty term
    have hIP : ∀ v, ∑ j, ∑ i, ∑ l ∈ univ.filter (fun l => i < l), bit (y j v i) * bit (y j v l) =
        m * ((T v ^ 2 - T v) / 2) - e v * T v * (T v - 1) := by
      intro v
      have : ∀ j, ∑ i, ∑ l ∈ univ.filter (fun l => i < l), bit (y j v i) * bit (y j v l) =
          ((T v - e v * a v j) ^ 2 - (T v - e v * a v j)) / 2 := by
        intro j
        rw [pair_count, hrow]
      simp_rw [this]
      have e1 : ∀ j, ((T v - e v * a v j) ^ 2 - (T v - e v * a v j)) / 2 =
          (T v ^ 2 - T v) / 2 - (e v * (T v - 1)) * a v j := by
        intro j
        linear_combination (e v * e v / 2) * ha01 v j + (a v j / 2) * he2 v
      simp_rw [e1, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [T]
      ring
    let ψ : Fin n → ℝ := fun v => e v * T v * (T v - 1)
    have hcut : ∑ j, reducedCutValue w (y j) =
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v),
          w u v * (m * (1 - M u v - (1 - T u) * (1 - T v)) - D u v) := by
      unfold reducedCutValue
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, hIO]
    have hpen : ∑ j, ∑ v, c v * ∑ i, ∑ l ∈ univ.filter (fun l => i < l),
        bit (y j v i) * bit (y j v l) = ∑ v, c v * (m * ((T v ^ 2 - T v) / 2) - ψ v) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, hIP]
    have hxh : reducedQuboObjective w c xh =
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), w u v * (1 - M u v - (1 - T u) * (1 - T v)) -
          ∑ v, c v * ((T v ^ 2 - T v) / 2) := by
      unfold reducedQuboObjective reducedCutValue
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      rw [pair_count]
    have key : ∑ j, (reducedQuboObjective w c (y j) - reducedQuboObjective w c xh) =
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), -(w u v * D u v) + ∑ v, c v * ψ v := by
      have hyobj : ∑ j, reducedQuboObjective w c (y j) =
          ∑ j, reducedCutValue w (y j) - ∑ j, ∑ v, c v * ∑ i, ∑ l ∈ univ.filter (fun l => i < l),
            bit (y j v i) * bit (y j v l) := by
        simp only [reducedQuboObjective, Finset.sum_sub_distrib]
      rw [Finset.sum_sub_distrib, hyobj, hcut, hpen, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hxh]
      have hA : ∑ u, ∑ v ∈ univ.filter (fun v => u < v),
            w u v * (m * (1 - M u v - (1 - T u) * (1 - T v)) - D u v) -
          (m : ℝ) * ∑ u, ∑ v ∈ univ.filter (fun v => u < v),
            w u v * (1 - M u v - (1 - T u) * (1 - T v)) =
          ∑ u, ∑ v ∈ univ.filter (fun v => u < v), -(w u v * D u v) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      have hB : (m : ℝ) * ∑ v, c v * ((T v ^ 2 - T v) / 2) -
          ∑ v, c v * (m * ((T v ^ 2 - T v) / 2) - ψ v) = ∑ v, c v * ψ v := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      linear_combination hA + hB
    have ha0 : ∀ v i, 0 ≤ a v i := fun v i => bit_nonneg _
    have ha1 : ∀ v i, a v i ≤ 1 := fun v i => bit_le_one _
    have hM0 : ∀ u v, 0 ≤ M u v := fun u v =>
      Finset.sum_nonneg fun i _ => mul_nonneg (ha0 u i) (ha0 v i)
    have hMu : ∀ u v, M u v ≤ T u := fun u v =>
      Finset.sum_le_sum fun i _ => by nlinarith [ha0 u i, ha0 v i, ha1 v i]
    have hMv : ∀ u v, M u v ≤ T v := fun u v =>
      Finset.sum_le_sum fun i _ => by nlinarith [ha0 u i, ha0 v i, ha1 u i]
    have hin : ∀ v, v ∈ V2 → 2 ≤ T v := by
      intro v hv
      have h1 : 1 < T v := (Finset.mem_filter.1 hv).2
      rw [hTnat] at h1 ⊢
      have : 1 < (univ.filter (fun j => xh v j = true)).card := by exact_mod_cast h1
      exact_mod_cast this
    have hout : ∀ v, v ∉ V2 → T v = 0 ∨ T v = 1 := by
      intro v hv
      have hle : T v ≤ 1 := by
        by_contra h
        exact hv (Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
      rw [hTnat] at hle ⊢
      have : (univ.filter (fun j => xh v j = true)).card ≤ 1 := by exact_mod_cast hle
      interval_cases h : (univ.filter (fun j => xh v j = true)).card <;> simp
    have hψ0 : ∀ v, 0 ≤ ψ v := by
      intro v
      by_cases hv : v ∈ V2
      · have := hin v hv
        simp only [ψ, e, hv, if_true, one_mul]
        nlinarith
      · simp [ψ, e, hv]
    have hD : ∀ u v, |D u v| ≤ ψ u + ψ v := by
      intro u v
      rw [abs_le]
      by_cases hu : u ∈ V2 <;> by_cases hv : v ∈ V2
      · have h1 := hin u hu; have h2 := hin v hv
        simp only [D, τ, ψ, e, hu, hv, if_true]
        constructor <;> nlinarith [hMu u v, hMv u v, sq_nonneg (T u - T v)]
      · have h1 := hin u hu
        simp only [D, τ, ψ, e, hu, hv, if_true, if_false]
        rcases hout v hv with h2 | h2
        · have hm : M u v = 0 := le_antisymm (by linarith [hMv u v]) (hM0 u v)
          rw [h2, hm]
          constructor <;> nlinarith
        · rw [h2]
          constructor <;> nlinarith [hMv u v, hM0 u v]
      · have h2 := hin v hv
        simp only [D, τ, ψ, e, hu, hv, if_true, if_false]
        rcases hout u hu with h1 | h1
        · have hm : M u v = 0 := le_antisymm (by linarith [hMu u v]) (hM0 u v)
          rw [h1, hm]
          constructor <;> nlinarith
        · rw [h1]
          constructor <;> nlinarith [hMu u v, hM0 u v]
      · simp only [D, τ, ψ, e, hu, hv, if_false]
        constructor <;> nlinarith
    have hedge : ∀ u v, -(|w u v| * (ψ u + ψ v)) ≤ -(w u v * D u v) := by
      intro u v
      have h1 := hD u v
      have h2 : |w u v * D u v| ≤ |w u v| * (ψ u + ψ v) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      have h3 := neg_abs_le (w u v * D u v)
      have h4 := le_abs_self (w u v * D u v)
      linarith
    have habs : ∀ v, ∑ u ∈ univ.filter (fun u => u ≠ v), |w u v| = dplus w v - dminus w v := by
      intro v
      rw [← dplus_eq, ← dminus_eq, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rcases le_or_gt 0 (w u v) with h | h
      · rw [abs_of_nonneg h, max_eq_left h, min_eq_right h, sub_zero]
      · rw [abs_of_neg h, max_eq_right h.le, min_eq_left h.le, zero_sub]
    have hgain : ∑ v, ψ v * (c v - (dplus w v - dminus w v)) ≤
        ∑ j, (reducedQuboObjective w c (y j) - reducedQuboObjective w c xh) := by
      rw [key]
      have hreg := pair_regroup (fun u v => |w u v|) (fun u v => by rw [hw u v]) ψ
      have hle : ∑ u, ∑ v ∈ univ.filter (fun v => u < v), -(|w u v| * (ψ u + ψ v)) ≤
          ∑ u, ∑ v ∈ univ.filter (fun v => u < v), -(w u v * D u v) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hedge u v
      simp only [Finset.sum_neg_distrib] at hle
      rw [hreg] at hle
      simp only [habs] at hle
      have : ∑ v, ψ v * (c v - (dplus w v - dminus w v)) =
          ∑ v, c v * ψ v - ∑ v, ψ v * (dplus w v - dminus w v) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [this]
      simp only [Finset.sum_neg_distrib]
      linarith
    have hpos : 0 < ∑ v, ψ v * (c v - (dplus w v - dminus w v)) := by
      have hv0m : v0 ∈ V2 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hv0⟩
      apply Finset.sum_pos' (fun v _ => mul_nonneg (hψ0 v) (by linarith [hc v]))
      refine ⟨v0, Finset.mem_univ _, mul_pos ?_ (by linarith [hc v0])⟩
      have := hin v0 hv0m
      simp only [ψ, e, hv0m, if_true, one_mul]
      nlinarith
    obtain ⟨j, _, hj⟩ := Finset.exists_lt_of_sum_lt
      (show ∑ _j : Fin m, (0 : ℝ) <
          ∑ j, (reducedQuboObjective w c (y j) - reducedQuboObjective w c xh) by
        simp only [Finset.sum_const_zero]; linarith)
    linarith [hopt (y j)]
  have conj2_holds :
      reducedQuboPenaltyConjecture := by
    intro n m w c hm hw hc xh hopt
    have hA := stepA2 w c hw hc xh hopt
    refine ⟨hA, fun x hx => ?_⟩
    have e1 : ∀ y : Fin n → Fin m → Bool, AtMostOneHot y →
        reducedQuboObjective w c y = reducedCutValue w y := by
      intro y hy
      have hz : ∀ v, ∑ i, ∑ j ∈ univ.filter (fun j => i < j), bit (y v i) * bit (y v j) = 0 := by
        intro v
        rw [pair_count]
        have h0 : 0 ≤ ∑ j, bit (y v j) := Finset.sum_nonneg fun j _ => bit_nonneg _
        have hnat : ∑ j, bit (y v j) = ((univ.filter (fun j => y v j = true)).card : ℝ) := by
          simp only [bit, Finset.sum_boole]
        have h1 := hy v
        rw [hnat] at h1 ⊢
        have : (univ.filter (fun j => y v j = true)).card ≤ 1 := by exact_mod_cast h1
        interval_cases h : (univ.filter (fun j => y v j = true)).card <;> norm_num
      simp [reducedQuboObjective, hz]
    have := hopt x
    rw [e1 x hx, e1 xh hA] at this
    exact this
  exact ⟨conj1_holds, conj2_holds⟩

end D5.S3.Quantum.Information.MaxKCutQuboPenalty
