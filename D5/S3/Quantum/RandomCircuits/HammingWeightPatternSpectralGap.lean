/- GID: D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap
   generality: G
   mirror-B: D5/B/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Connected gate patterns have a polynomial spectral gap at fixed Hamming weight. -/

import D5.S3.Arith.Congruence.ConditionalComparison.CommonTreeUnion
import D5.S3.Zeros.EdgeTranspositionGeneration
import Mathlib.Data.Set.PowersetCard
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Spectral contraction of products of Hamming-weight-preserving gate averages. -/

open scoped BigOperators
open Matrix Finset
open Erdos7.CommonTreeUnion (Choice)

namespace D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap

/-- A gate exchanges its two qubits, including on the sectors it fixes. -/
def swapConfig {n k : ℕ} (a b : Fin n) (s : Choice n k) : Choice n k :=
  Set.powersetCard.map k (Equiv.swap a b).toEmbedding s

/-- Squared RBS/FBS entries at angle π/4; the FBS signs disappear on squaring. -/
noncomputable def gateMatrix {n k : ℕ} (a b : Fin n) :
    Matrix (Choice n k) (Choice n k) ℝ :=
  fun s t => (if s = t then 1 / 2 else 0) +
    (if s = swapConfig a b t then 1 / 2 else 0)

/-- The first gate in the list acts first on a column vector. -/
noncomputable def patternMatrix {n k : ℕ} (pat : List (Fin n × Fin n)) :
    Matrix (Choice n k) (Choice n k) ℝ :=
  (pat.map fun e => gateMatrix e.1 e.2).reverse.prod

/-- The undirected qubit graph, with an edge in either orientation for each gate. -/
def qubitGraph {n : ℕ} (pat : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun x y => (x, y) ∈ pat)

/-- The source's bidirectional strong connectivity, with distinct gate endpoints. -/
def connectedPattern {n : ℕ} (pat : List (Fin n × Fin n)) : Prop :=
  (∀ e ∈ pat, e.1 ≠ e.2) ∧ (qubitGraph pat).Connected

/-- Uniform polynomial lower bound for the gap on the sum-zero subspace. -/
def claim : Prop :=
  ∀ (k c a : ℕ), 1 ≤ k → ∀ pat : (n : ℕ) → List (Fin n × Fin n),
    (∀ n, 2 ≤ n → connectedPattern (pat n) ∧ (pat n).length ≤ c * n ^ a) →
    ∃ d : ℝ, 0 < d ∧ ∃ b : ℕ, ∀ n, k < n → 2 ≤ n →
    ∀ (μ : ℂ) (v : Choice n k → ℂ), v ≠ 0 → ∑ s, v s = 0 →
      (patternMatrix (pat n)).map (fun x : ℝ => (x : ℂ)) *ᵥ v = μ • v →
      ‖μ‖ ≤ 1 - d / (n : ℝ) ^ b

private def swapEquiv {n k : ℕ} (a b : Fin n) :
    Equiv.Perm (Choice n k) :=
  (Equiv.finsetCongr (Equiv.swap a b)).subtypeEquiv
    (fun s => by
      change s.card = k ↔ (s.map (Equiv.swap a b).toEmbedding).card = k
      rw [Finset.card_map])

private noncomputable def average {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  midpoint ℂ v (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s.symm v)

private noncomputable def run {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) : EuclideanSpace ℂ (Choice n k) :=
  pat.foldl (fun w e => average (swapEquiv e.1 e.2) w) v

private noncomputable def staticEnergy {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) : ℝ :=
  (pat.map fun e => ‖v - average (swapEquiv e.1 e.2) v‖ ^ 2).sum

private def configGraph {n k : ℕ} (pat : List (Fin n × Fin n)) :
    SimpleGraph (Choice n k) where
  Adj s t := s ≠ t ∧ ∃ e ∈ pat, swapConfig e.1 e.2 s = t
  symm := ⟨by
    rintro s t ⟨hne, e, he, h⟩
    exact ⟨hne.symm, e, he, h ▸ (swapEquiv e.1 e.2).apply_symm_apply s⟩⟩
  loopless := ⟨by intro s h; exact h.1 rfl⟩

private lemma config_card_le (n k : ℕ) : Fintype.card (Choice n k) ≤ n ^ k := by
  have h : Fintype.card (Choice n k) = n.choose k := by
    simpa only [Fintype.card_fin] using Fintype.card_finset_len (α := Fin n) k
  rw [h]
  exact Nat.choose_le_pow n k

private lemma gate_apply {n k : ℕ} (a b : Fin n)
    (v : EuclideanSpace ℂ (Choice n k)) :
    (gateMatrix a b).map (fun x : ℝ => (x : ℂ)) *ᵥ WithLp.ofLp v =
      WithLp.ofLp (average (swapEquiv a b) v) := by
  classical
  simp only [average, midpoint_eq_smul_add, invOf_eq_inv, ← one_div]
  ext s
  have hswap (t : Choice n k) :
      s = swapConfig a b t ↔ swapConfig a b s = t :=
    (swapEquiv a b).symm_apply_eq.symm
  change (∑ t, (((if s = t then 1 / 2 else 0) +
    (if s = swapConfig a b t then 1 / 2 else 0) : ℝ) : ℂ) * v t) =
      (1 / 2 : ℂ) * (v s + v (swapConfig a b s))
  simp only [hswap]
  have hcast (p : Prop) [Decidable p] :
      (((if p then 1 / 2 else 0) : ℝ) : ℂ) = if p then 1 / 2 else 0 := by
    simpa using apply_ite Complex.ofReal p (1 / 2 : ℝ) 0
  simp only [Complex.ofReal_add, hcast, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  simp [mul_add]

private lemma pattern_apply {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) :
    (patternMatrix pat).map (fun x : ℝ => (x : ℂ)) *ᵥ WithLp.ofLp v =
      WithLp.ofLp (run pat v) := by
  classical
  induction pat generalizing v with
  | nil =>
    change ((1 : Matrix (Choice n k) (Choice n k) ℝ).map _) *ᵥ _ = _
    simp only [Matrix.map_one, Complex.ofReal_zero, Complex.ofReal_one, Matrix.one_mulVec]
    rfl
  | cons e pat ih =>
    unfold patternMatrix
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
    change (((pat.map fun e : Fin n × Fin n => gateMatrix (k := k) e.1 e.2).reverse.prod *
      gateMatrix e.1 e.2).map Complex.ofRealHom) *ᵥ _ = _
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec]
    change (patternMatrix pat).map (fun x : ℝ => (x : ℂ)) *ᵥ
      ((gateMatrix e.1 e.2).map (fun x : ℝ => (x : ℂ)) *ᵥ v.ofLp) = _
    rw [gate_apply]
    exact ih (average (swapEquiv e.1 e.2) v)

private lemma residual_eq {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (v : EuclideanSpace ℂ ι) :
    v - average s v = (1 / 2 : ℂ) •
      (v - LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s.symm v) := by
  simpa only [midpoint_eq_smul_add, invOf_eq_inv, one_div, average] using
    (left_sub_midpoint (R := ℂ) v
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s.symm v))

private lemma projection_energy {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (v : EuclideanSpace ℂ ι) :
    ‖average s v‖ ^ 2 + ‖v - average s v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [residual_eq]
  rw [average.eq_1, midpoint_eq_smul_add, invOf_eq_inv, ← one_div]
  rw [norm_smul, norm_smul, mul_pow, mul_pow, norm_div, norm_one]
  have h := parallelogram_law_with_norm ℂ v
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s.symm v)
  rw [LinearIsometryEquiv.norm_map] at h
  norm_num
  nlinarith

private lemma residual_contract {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (v : EuclideanSpace ℂ ι) : ‖v - average s v‖ ≤ ‖v‖ := by
  rw [residual_eq, norm_smul, norm_div, norm_one]
  norm_num
  calc
    1 / 2 * ‖v - LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s.symm v‖ ≤
        1 / 2 * (‖v‖ + ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s.symm v‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖v‖ := by rw [LinearIsometryEquiv.norm_map]; ring

private lemma residual_lipschitz {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (v w : EuclideanSpace ℂ ι) :
    ‖v - average s v‖ ≤ ‖v - w‖ + ‖w - average s w‖ := by
  have h : v - average s v =
      (v - w - average s (v - w)) + (w - average s w) := by
    simp only [average, midpoint_eq_smul_add, invOf_eq_inv, ← one_div]
    ext x
    change v x - (1 / 2 : ℂ) * (v x + v (s x)) =
      (v x - w x - (1 / 2 : ℂ) * (v x - w x + (v (s x) - w (s x)))) +
      (w x - (1 / 2 : ℂ) * (w x + w (s x)))
    ring
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (residual_contract s (v - w)) le_rfl)

private noncomputable def increments {n k : ℕ} (pat : List (Fin n × Fin n)) :
    EuclideanSpace ℂ (Choice n k) → List ℝ :=
  pat.rec (fun _ => []) (fun e _ next v =>
    ‖v - average (swapEquiv e.1 e.2) v‖ :: next (average (swapEquiv e.1 e.2) v))

private lemma increments_length {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) : (increments pat v).length = pat.length := by
  induction pat generalizing v with
  | nil => rfl
  | cons e pat ih => exact congrArg Nat.succ (ih _)

private lemma increments_nonneg {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) : ∀ t ∈ increments pat v, 0 ≤ t := by
  induction pat generalizing v with
  | nil => intro t ht; exact False.elim (List.not_mem_nil ht)
  | cons e pat ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact norm_nonneg _
    · exact ih _ t ht

private lemma increments_energy {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) :
    ((increments pat v).map (fun t => t ^ 2)).sum = ‖v‖ ^ 2 - ‖run pat v‖ ^ 2 := by
  induction pat generalizing v with
  | nil => exact (sub_self _).symm
  | cons e pat ih =>
    change ‖v - average (swapEquiv e.1 e.2) v‖ ^ 2 +
      ((increments pat (average (swapEquiv e.1 e.2) v)).map (fun t => t ^ 2)).sum =
      ‖v‖ ^ 2 - ‖run pat (average (swapEquiv e.1 e.2) v)‖ ^ 2
    rw [ih]
    have h := projection_energy (swapEquiv e.1 e.2) v
    linarith

private lemma defect_le_increments {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) (e : Fin n × Fin n) (he : e ∈ pat) :
    ‖v - average (swapEquiv e.1 e.2) v‖ ≤ (increments pat v).sum := by
  induction pat generalizing v with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons d pat ih =>
    rcases List.mem_cons.mp he with rfl | he
    · change _ ≤ _ + (increments pat (average (swapEquiv e.1 e.2) v)).sum
      exact le_add_of_nonneg_right (List.sum_nonneg (increments_nonneg _ _))
    · change _ ≤ _ + (increments pat (average (swapEquiv d.1 d.2) v)).sum
      exact (residual_lipschitz (swapEquiv e.1 e.2) v
        (average (swapEquiv d.1 d.2) v)).trans
          (add_le_add le_rfl (ih (average (swapEquiv d.1 d.2) v) he))

private lemma energy_control {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (Choice n k)) :
    staticEnergy pat v ≤ (pat.length : ℝ) ^ 2 * (‖v‖ ^ 2 - ‖run pat v‖ ^ 2) := by
  have hs : staticEnergy pat v ≤ (pat.length : ℝ) * (increments pat v).sum ^ 2 := by
    unfold staticEnergy
    have h := List.sum_le_length_nsmul
      (pat.map fun e => ‖v - average (swapEquiv e.1 e.2) v‖ ^ 2)
      ((increments pat v).sum ^ 2) (by
        intro t ht
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
        exact pow_le_pow_left₀ (norm_nonneg _) (defect_le_increments pat v e he) 2)
    simpa only [List.length_map, nsmul_eq_mul] using h
  have hcs : (increments pat v).sum ^ 2 ≤ (pat.length : ℝ) *
      ((increments pat v).map (fun t => t ^ 2)).sum := by
    simpa only [Multiset.sum_coe, Multiset.coe_card, Multiset.map_coe, increments_length]
      using Multiset.sq_sum_le_card_mul_sum_sq (↑(increments pat v) : Multiset ℝ)
  calc
    staticEnergy pat v ≤ (pat.length : ℝ) * (increments pat v).sum ^ 2 := hs
    _ ≤ (pat.length : ℝ) * ((pat.length : ℝ) *
        ((increments pat v).map (fun t => t ^ 2)).sum) :=
      mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)
    _ = _ := by rw [increments_energy]; ring

private lemma edge_energy {n k : ℕ} (a b : Fin n)
    (v : EuclideanSpace ℂ (Choice n k)) :
    ‖v - average (swapEquiv a b) v‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ s, ‖v s - v (swapConfig a b s)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have h : (v - average (swapEquiv a b) v) s =
      (1 / 2 : ℂ) * (v s - v (swapConfig a b s)) := by
    simp only [average, midpoint_eq_smul_add, invOf_eq_inv, ← one_div]
    change v s - (1 / 2 : ℂ) * (v s + v (swapConfig a b s)) = _
    ring
  rw [h, norm_mul, mul_pow, norm_div, norm_one]
  norm_num

private lemma configuration_connected {n k : ℕ} (pat : List (Fin n × Fin n))
    (hc : connectedPattern pat) : (configGraph (k := k) pat).Preconnected := by
  classical
  let f (σ : Equiv.Perm (Fin n)) (s : Choice n k) : Choice n k :=
    Set.powersetCard.map k σ.toEmbedding s
  have hone (s : Choice n k) : f 1 s = s := by
    apply Subtype.ext
    exact Finset.map_refl
  have hmul (σ τ : Equiv.Perm (Fin n)) (s : Choice n k) :
      f (σ * τ) s = f σ (f τ s) := by
    apply Subtype.ext
    change s.val.map _ = (s.val.map _).map _
    rw [Finset.map_map]
    rfl
  let h : Subgroup (Equiv.Perm (Fin n)) := {
    carrier := {σ | ∀ s, (configGraph pat).Reachable s (f σ s)}
    one_mem' := by intro s; rw [hone]
    mul_mem' := by
      intro σ τ hσ hτ s
      rw [hmul]
      exact (hτ s).trans (hσ (f τ s))
    inv_mem' := by
      intro σ hσ s
      have hh := hσ (f σ⁻¹ s)
      rw [← hmul, mul_inv_cancel, hone] at hh
      exact hh.symm }
  have hgate (e : Fin n × Fin n) (he : e ∈ pat) : Equiv.swap e.1 e.2 ∈ h := by
    intro s
    change (configGraph pat).Reachable s (swapConfig e.1 e.2 s)
    by_cases hs : s = swapConfig e.1 e.2 s
    · rw [← hs]
    · exact SimpleGraph.Adj.reachable ⟨hs, e, he, rfl⟩
  have hedge (x y : Fin n) (hxy : (qubitGraph pat).Adj x y) : Equiv.swap x y ∈ h := by
    rcases hxy with ⟨_, hxy | hyx⟩
    · exact hgate (x, y) hxy
    · rw [Equiv.swap_comm]
      exact hgate (y, x) hyx
  have htop : h = ⊤ := by
    apply top_unique
    rw [← D5.S3.Zeros.EdgeTranspositionGeneration.connected_edge_transpositions_generate
      (qubitGraph pat) hc.2, Subgroup.closure_le]
    rintro σ ⟨x, y, hxy, rfl⟩
    exact hedge x y hxy
  intro s t
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq s.val t.val
    (s.property.trans t.property.symm)
  have hm : σ ∈ h := htop ▸ Subgroup.mem_top σ
  have heq : f σ s = t := Subtype.ext hσ
  exact heq ▸ hm s

private lemma path_variation {ι : Type*} [Fintype ι] (g : SimpleGraph ι)
    [DecidableRel g.Adj] (f : ι → ℝ) {x y : ι} (p : g.Walk x y) (hp : p.IsPath) :
    (f x - f y) ^ 2 ≤ (Fintype.card ι : ℝ) *
      ∑ i, ∑ j, if g.Adj i j then (f i - f j) ^ 2 else 0 := by
  classical
  have htel : (p.darts.map (fun d => f d.fst - f d.snd)).sum = f x - f y := by
    clear hp
    induction p with
    | nil => simp
    | cons h p ih =>
      simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
      ring
  have hcs : (f x - f y) ^ 2 ≤ (p.length : ℝ) *
      (p.darts.map (fun d => (f d.fst - f d.snd) ^ 2)).sum := by
    have h := Multiset.sq_sum_le_card_mul_sum_sq
      (↑(p.darts.map (fun d => f d.fst - f d.snd)) : Multiset ℝ)
    simpa only [Multiset.sum_coe, Multiset.coe_card, Multiset.map_coe, List.map_map,
      List.length_map, SimpleGraph.Walk.length_darts, htel, Function.comp_def] using h
  have hs : (p.darts.map (fun d => (f d.fst - f d.snd) ^ 2)).sum ≤
      ∑ i, ∑ j, if g.Adj i j then (f i - f j) ^ 2 else 0 := by
    rw [← List.sum_toFinset _ (SimpleGraph.Walk.darts_nodup_of_support_nodup
      hp.support_nodup)]
    rw [← Finset.sum_product Finset.univ Finset.univ
      (fun q : ι × ι => if g.Adj q.1 q.2 then (f q.1 - f q.2) ^ 2 else 0)]
    refine Finset.sum_le_sum_of_injOn (fun d : g.Dart => d.toProd) ?_
      (by intro d hd; simp) ?_ ?_
    · intro d hd e he h
      exact SimpleGraph.Dart.ext d e h
    · intro d hd
      rw [ite_eq_left d.adj]
    · intro q hq hnot
      split_ifs <;> positivity
  calc
    (f x - f y) ^ 2 ≤ (p.length : ℝ) *
        (p.darts.map (fun d => (f d.fst - f d.snd) ^ 2)).sum := hcs
    _ ≤ (Fintype.card ι : ℝ) *
        ∑ i, ∑ j, if g.Adj i j then (f i - f j) ^ 2 else 0 := by
      apply mul_le_mul (by exact_mod_cast hp.length_lt.le) hs
      · exact List.sum_nonneg (by
          intro t ht
          obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
          exact sq_nonneg _)
      · exact Nat.cast_nonneg _

private lemma real_poincare {ι : Type*} [Fintype ι] (g : SimpleGraph ι)
    [DecidableRel g.Adj] (hc : g.Preconnected) (f : ι → ℝ) (hz : ∑ i, f i = 0) :
    4 * ∑ i, (f i) ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 *
      ∑ i, ∑ j, if g.Adj i j then (f i - f j) ^ 2 else 0 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp
  | inr h =>
    obtain ⟨x, _, hx⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    obtain ⟨y, _, hy⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    have hsum : (∑ i, (f i) ^ 2) ≤ -(Fintype.card ι : ℝ) * (f x * f y) := by
      calc
        (∑ i, (f i) ^ 2) ≤ ∑ i, ((f x + f y) * f i - f x * f y) := by
          apply Finset.sum_le_sum
          intro i _
          have h := mul_nonneg (sub_nonneg.mpr (hx i (Finset.mem_univ _)))
            (sub_nonneg.mpr (hy i (Finset.mem_univ _)))
          nlinarith
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
          simp
    have hpop : 4 * ∑ i, (f i) ^ 2 ≤
        (Fintype.card ι : ℝ) * (f x - f y) ^ 2 := by
      have h := mul_nonneg (Nat.cast_nonneg (Fintype.card ι) :
        (0 : ℝ) ≤ Fintype.card ι) (sq_nonneg (f x + f y))
      nlinarith
    obtain ⟨p, hp⟩ := (hc x y).exists_isPath
    calc
      4 * ∑ i, (f i) ^ 2 ≤ (Fintype.card ι : ℝ) * (f x - f y) ^ 2 := hpop
      _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) *
          ∑ i, ∑ j, if g.Adj i j then (f i - f j) ^ 2 else 0) :=
        mul_le_mul_of_nonneg_left (path_variation g f p hp) (Nat.cast_nonneg _)
      _ = _ := by ring

open Classical in
private lemma adjacency_energy {n k : ℕ} (pat : List (Fin n × Fin n))
    (f : Choice n k → ℝ) :
    (∑ s, ∑ t, if (configGraph pat).Adj s t then (f s - f t) ^ 2 else 0) ≤
      (pat.map fun e => ∑ s, (f s - f (swapConfig e.1 e.2 s)) ^ 2).sum := by
  classical
  have hrow (s : Choice n k) :
      (∑ t, if (configGraph pat).Adj s t then (f s - f t) ^ 2 else 0) ≤
        (pat.map fun e => (f s - f (swapConfig e.1 e.2 s)) ^ 2).sum := by
    induction pat with
    | nil =>
      have hnone (t : Choice n k) : ¬ (configGraph ([] : List (Fin n × Fin n))).Adj s t := by
        rintro ⟨_, e, he, _⟩
        exact List.not_mem_nil he
      simp only [hnone, ite_false, Finset.sum_const_zero, List.map_nil, List.sum_nil,
        le_refl]
    | cons e pat ih =>
      calc
        _ ≤ ∑ t, ((if t = swapConfig e.1 e.2 s then (f s - f t) ^ 2 else 0) +
            if (configGraph pat).Adj s t then (f s - f t) ^ 2 else 0) := by
          apply Finset.sum_le_sum
          intro t _
          by_cases ht : (configGraph (e :: pat)).Adj s t
          · rcases ht with ⟨hne, d, hd, hd'⟩
            have ht : (configGraph (e :: pat)).Adj s t := ⟨hne, d, hd, hd'⟩
            rw [ite_eq_left ht]
            rcases List.mem_cons.mp hd with rfl | hd
            · rw [ite_eq_left hd'.symm]
              split_ifs <;> nlinarith [sq_nonneg (f s - f t)]
            · rw [ite_eq_left (show (configGraph pat).Adj s t from ⟨hne, d, hd, hd'⟩)]
              split_ifs <;> nlinarith [sq_nonneg (f s - f t)]
          · rw [ite_eq_right ht]
            positivity
        _ = (f s - f (swapConfig e.1 e.2 s)) ^ 2 +
            ∑ t, if (configGraph pat).Adj s t then (f s - f t) ^ 2 else 0 := by
          rw [Finset.sum_add_distrib]
          simp
        _ ≤ _ := add_le_add le_rfl ih
  calc
    _ ≤ ∑ s, (pat.map fun e => (f s - f (swapConfig e.1 e.2 s)) ^ 2).sum :=
      Finset.sum_le_sum (fun s _ => hrow s)
    _ = (pat.map fun e => ∑ s, (f s - f (swapConfig e.1 e.2 s)) ^ 2).sum := by
      clear hrow
      induction pat with
      | nil => simp
      | cons e pat ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

private lemma poincare_bound {n k : ℕ} (pat : List (Fin n × Fin n))
    (hc : connectedPattern pat) (v : EuclideanSpace ℂ (Choice n k))
    (hv : ∑ s, v s = 0) :
    ‖v‖ ^ 2 ≤ (Fintype.card (Choice n k) : ℝ) ^ 2 * staticEnergy pat v := by
  classical
  have hrz : ∑ s, (v s).re = 0 := by simpa using congrArg Complex.re hv
  have hiz : ∑ s, (v s).im = 0 := by simpa using congrArg Complex.im hv
  have hr := (real_poincare (configGraph pat) (configuration_connected pat hc)
    (fun s => (v s).re) hrz).trans (mul_le_mul_of_nonneg_left
      (adjacency_energy pat (fun s => (v s).re)) (sq_nonneg _))
  have hi := (real_poincare (configGraph pat) (configuration_connected pat hc)
    (fun s => (v s).im) hiz).trans (mul_le_mul_of_nonneg_left
      (adjacency_energy pat (fun s => (v s).im)) (sq_nonneg _))
  have hparts (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa only [sq, RCLike.re_to_complex, RCLike.im_to_complex] using
      RCLike.norm_sq_eq_def (z := z)
  have hn : ‖v‖ ^ 2 = (∑ s, (v s).re ^ 2) + ∑ s, (v s).im ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hparts, Finset.sum_add_distrib]
  have hsplit : (pat.map fun e => ∑ s, ‖v s - v (swapConfig e.1 e.2 s)‖ ^ 2).sum =
      (pat.map fun e => ∑ s, ((v s).re - (v (swapConfig e.1 e.2 s)).re) ^ 2).sum +
      (pat.map fun e => ∑ s, ((v s).im - (v (swapConfig e.1 e.2 s)).im) ^ 2).sum := by
    simp only [hparts, Complex.sub_re, Complex.sub_im, Finset.sum_add_distrib,
      List.sum_map_add]
  have he : staticEnergy pat v = (1 / 4 : ℝ) *
      (pat.map fun e => ∑ s, ‖v s - v (swapConfig e.1 e.2 s)‖ ^ 2).sum := by
    unfold staticEnergy
    simp only [edge_energy, List.sum_map_mul_left]
  rw [hn, he, hsplit]
  nlinarith

private lemma pattern_length_pos {n : ℕ} (hn : 2 ≤ n)
    (pat : List (Fin n × Fin n)) (hc : connectedPattern pat) : 0 < pat.length := by
  by_contra h
  have hp : pat = [] := List.length_eq_zero_iff.mp (by omega)
  have hg : qubitGraph pat = ⊥ := by
    subst pat
    ext x y
    change (x ≠ y ∧ ((x, y) ∈ ([] : List (Fin n × Fin n)) ∨ (y, x) ∈ [])) ↔ False
    simp
  have hxy := hc.2.preconnected (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
  rw [hg, SimpleGraph.reachable_bot] at hxy
  have := congrArg Fin.val hxy
  norm_num at this

private lemma spectral_core {n k : ℕ} (hn : 2 ≤ n) (pat : List (Fin n × Fin n))
    (hc : connectedPattern pat) (μ : ℂ) (v : Choice n k → ℂ) (hv : v ≠ 0)
    (hz : ∑ s, v s = 0)
    (he : (patternMatrix pat).map (fun x : ℝ => (x : ℂ)) *ᵥ v = μ • v) :
    ‖μ‖ ≤ 1 - 1 / (2 * (pat.length : ℝ) ^ 2 * (Fintype.card (Choice n k) : ℝ) ^ 2) := by
  let w : EuclideanSpace ℂ (Choice n k) := WithLp.toLp 2 v
  have hwne : w ≠ 0 := by
    intro h
    apply hv
    exact (WithLp.ofLp_eq_zero 2).mpr h
  have hw : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwne)
  have hrun : run pat w = μ • w := by
    apply (WithLp.ext_iff 2).mpr
    exact (pattern_apply pat w).symm.trans he
  have h := (poincare_bound pat hc w hz).trans
    (mul_le_mul_of_nonneg_left (energy_control pat w) (sq_nonneg _))
  rw [hrun, norm_smul, mul_pow] at h
  have hj : (0 : ℝ) < pat.length := by exact_mod_cast pattern_length_pos hn pat hc
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hv
  have hn' : (0 : ℝ) < Fintype.card (Choice n k) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨s⟩
  let d : ℝ := (pat.length : ℝ) ^ 2 * (Fintype.card (Choice n k) : ℝ) ^ 2
  have hd : 0 < d := mul_pos (sq_pos_of_pos hj) (sq_pos_of_pos hn')
  have hb : ‖w‖ ^ 2 * 1 ≤ ‖w‖ ^ 2 * (d * (1 - ‖μ‖ ^ 2)) := by
    convert h using 1 <;> (try dsimp only [d]) <;> ring
  have hc' : 1 ≤ d * (1 - ‖μ‖ ^ 2) := le_of_mul_le_mul_left hb hw
  have hdiv : 1 / d ≤ 1 - ‖μ‖ ^ 2 := (div_le_iff₀ hd).mpr (by nlinarith [hc'])
  have hlast : ‖μ‖ ≤ 1 - (1 / d) / 2 := by nlinarith [sq_nonneg (‖μ‖ - 1)]
  simpa only [div_div, d, mul_comm, mul_left_comm, mul_assoc] using hlast

private lemma polynomial_gap (k c a : ℕ) (pat : (n : ℕ) → List (Fin n × Fin n))
    (hp : ∀ n, 2 ≤ n → connectedPattern (pat n) ∧ (pat n).length ≤ c * n ^ a) :
    ∀ n, k < n → 2 ≤ n → ∀ (μ : ℂ) (v : Choice n k → ℂ), v ≠ 0 →
    ∑ s, v s = 0 →
    (patternMatrix (pat n)).map (fun x : ℝ => (x : ℂ)) *ᵥ v = μ • v →
    ‖μ‖ ≤ 1 - (1 / (2 * (max c 1 : ℕ) ^ 2 : ℝ)) /
      (n : ℝ) ^ (2 * a + 2 * k) := by
  intro n hkn hn μ v hv hz he
  have hj : (pat n).length ≤ max c 1 * n ^ a :=
    (hp n hn).2.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hj' : ((pat n).length : ℝ) ≤ (max c 1 : ℕ) * (n : ℝ) ^ a := by
    exact_mod_cast hj
  have hcard : (Fintype.card (Choice n k) : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast config_card_le n k
  have hden : 2 * ((pat n).length : ℝ) ^ 2 * (Fintype.card (Choice n k) : ℝ) ^ 2 ≤
      (2 * (max c 1 : ℕ) ^ 2 : ℝ) * (n : ℝ) ^ (2 * a + 2 * k) := by
    calc
      _ ≤ 2 * ((max c 1 : ℕ) * (n : ℝ) ^ a) ^ 2 * ((n : ℝ) ^ k) ^ 2 := by
        gcongr
      _ = _ := by
        rw [show 2 * a + 2 * k = (a + a) + (k + k) by omega,
          pow_add, pow_add, pow_add]
        ring
  have hjpos : (0 : ℝ) < (pat n).length := by
    exact_mod_cast pattern_length_pos hn (pat n) (hp n hn).1
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hv
  have hnpos : (0 : ℝ) < Fintype.card (Choice n k) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨s⟩
  have hpos : 0 < 2 * ((pat n).length : ℝ) ^ 2 *
      (Fintype.card (Choice n k) : ℝ) ^ 2 := by positivity
  have hrat := one_div_le_one_div_of_le hpos hden
  have hgap := (spectral_core hn (pat n) (hp n hn).1 μ v hv hz he).trans
    (sub_le_sub_left hrat 1)
  simpa only [div_div] using hgap

/-- Connected patterns with polynomially many gates have an inverse-polynomial gap. -/
theorem result : claim := by
  intro k c a hk pat hp
  refine ⟨1 / (2 * (max c 1 : ℕ) ^ 2 : ℝ), by positivity, 2 * a + 2 * k, ?_⟩
  exact polynomial_gap k c a pat hp

end D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap
