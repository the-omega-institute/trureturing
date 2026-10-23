/- GID: D5/S3/Combinatorics/Graph/QuadraticLoad/StarExtrema
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/QuadraticLoad/StarExtrema
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Star]
   utility: none
   digest: Sharp star extrema and the maximum-degree lower bound for quadratic loads. -/

import D5.S3.Combinatorics.Graph.QuadraticEdgeLoad
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Combinatorics.SimpleGraph.Star

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.QuadraticEdgeLoad

namespace D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema

/-- A maximum-degree star gives a lower bound even when its leaves have additional edges. -/
theorem maximum_degree_lower_bound {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hD : 1 ≤ G.maxDegree) :
    (G.maxDegree : ℝ) / (1 + Real.sqrt G.maxDegree) ^ 2 ≤ kappa G := by
  classical
  obtain ⟨b, hb⟩ := G.exists_maximal_degree_vertex
  obtain ⟨a, ha, hk⟩ := minimum_attained G
  let s : ℝ := Real.sqrt G.maxDegree
  let t : ℝ := 1 / (1 + s)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hD)
  have hs2 : s ^ 2 = (G.maxDegree : ℝ) := Real.sq_sqrt (by positivity)
  have ht : (1 + s) * t = 1 := by dsimp [t]; field_simp
  have load_bound (v : V) : load G a v ≤ kappa G := by
    rw [← hk]
    exact le_sup' _ (mem_univ v)
  have leaf_bound (v : V) (hv : v ∈ G.neighborFinset b) :
      (a v b) ^ 2 ≤ kappa G := by
    apply le_trans (single_le_sum (fun i _ => sq_nonneg (a v i)) ?_) (load_bound v)
    exact (G.mem_neighborFinset v b).2 ((G.mem_neighborFinset b v).1 hv).symm
  have edge_bound (v : V) (hv : v ∈ G.neighborFinset b) :
      s * t ≤ s * (a b v) ^ 2 + (a v b) ^ 2 := by
    have he := ha.2 b v ((G.mem_neighborFinset b v).1 hv)
    have hn := mul_nonneg (le_of_lt (by linarith : 0 < 1 + s)) (sq_nonneg (a b v - t))
    have hid : s * (a b v) ^ 2 + (1 - a b v) ^ 2 - s * t =
        (1 + s) * (a b v - t) ^ 2 := by
      dsimp [t]
      field_simp
      ring
    nlinarith only [he, hid, hn, sq_nonneg (a b v - t)]
  have hsum := sum_le_sum edge_bound
  have hleaves : (∑ v ∈ G.neighborFinset b, (a v b) ^ 2) ≤
      (G.maxDegree : ℝ) * kappa G := by
    calc
      _ ≤ ∑ _v ∈ G.neighborFinset b, kappa G := sum_le_sum leaf_bound
      _ = _ := by simp [SimpleGraph.card_neighborFinset_eq_degree, ← hb]
  have hcenter : s * load G a b ≤ s * kappa G :=
    mul_le_mul_of_nonneg_left (load_bound b) hs.le
  have htotal : (G.maxDegree : ℝ) * (s * t) ≤
      (s + (G.maxDegree : ℝ)) * kappa G := by
    calc
      _ = ∑ _v ∈ G.neighborFinset b, s * t := by
        simp [SimpleGraph.card_neighborFinset_eq_degree, ← hb]
      _ ≤ ∑ v ∈ G.neighborFinset b, (s * (a b v) ^ 2 + (a v b) ^ 2) := hsum
      _ = s * load G a b + ∑ v ∈ G.neighborFinset b, (a v b) ^ 2 := by
        simp only [sum_add_distrib, ← mul_sum, load]
      _ ≤ _ := by nlinarith
  have heq : (G.maxDegree : ℝ) / (1 + s) ^ 2 * (s + (G.maxDegree : ℝ)) =
      (G.maxDegree : ℝ) * (s * t) := by
    dsimp [t]
    rw [← hs2]
    field_simp
  change (G.maxDegree : ℝ) / (1 + s) ^ 2 ≤ kappa G
  apply (mul_le_mul_iff_left₀ (by nlinarith : 0 < s + (G.maxDegree : ℝ))).mp
  nlinarith only [heq, htotal]

/-- Both explicit extrema on the full star carriers, including boundary probability vectors. -/
theorem star_extrema (m : ℕ) (hm : 1 ≤ m) :
    let H := SimpleGraph.starGraph (none : Option (Fin m))
    let t : ℝ := 1 / (1 + Real.sqrt m)
    let a : Option (Fin m) → Option (Fin m) → ℝ :=
      fun b _ => if b = none then t else 1 - t
    let μ : Option (Fin m) → ℝ := fun b =>
      if b = none then t else 1 / (Real.sqrt m * (1 + Real.sqrt m))
    let Φ : (Option (Fin m) → ℝ) → ℝ := fun p =>
      ∑ e ∈ H.edgeFinset, Sym2.lift
        ⟨fun b c => p b * p c / (p b + p c),
          fun b c => by simp [mul_comm, add_comm]⟩ e
    let q : ℝ := m / (1 + Real.sqrt m) ^ 2
    Feasible H a ∧ (∀ b, load H a b = q) ∧ kappa H = q ∧
      μ ∈ stdSimplex ℝ (Option (Fin m)) ∧ Φ μ = q ∧
      (∀ p ∈ stdSimplex ℝ (Option (Fin m)), Φ p ≤ q) ∧
      (m = 1 → kappa H = 1 / 4) ∧
      (m = 2 → kappa H = 2 * (3 - 2 * Real.sqrt 2)) := by
  classical
  dsimp only
  let H := SimpleGraph.starGraph (none : Option (Fin m))
  let s : ℝ := Real.sqrt m
  let t : ℝ := 1 / (1 + s)
  let a : Option (Fin m) → Option (Fin m) → ℝ :=
    fun b _ => if b = none then t else 1 - t
  let μ : Option (Fin m) → ℝ := fun b =>
    if b = none then t else 1 / (s * (1 + s))
  let Φ : (Option (Fin m) → ℝ) → ℝ := fun p =>
    ∑ e ∈ H.edgeFinset, Sym2.lift
      ⟨fun b c => p b * p c / (p b + p c),
        fun b c => by simp [mul_comm, add_comm]⟩ e
  let q : ℝ := m / (1 + s) ^ 2
  change Feasible H a ∧ (∀ b, load H a b = q) ∧ kappa H = q ∧
    μ ∈ stdSimplex ℝ (Option (Fin m)) ∧ Φ μ = q ∧
    (∀ p ∈ stdSimplex ℝ (Option (Fin m)), Φ p ≤ q) ∧
    (m = 1 → kappa H = 1 / 4) ∧
    (m = 2 → kappa H = 2 * (3 - 2 * Real.sqrt 2))
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hs2 : s ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
  have ht : 0 ≤ t ∧ t ≤ 1 := by
    dsimp [t]
    constructor
    · positivity
    · apply (div_le_one (by linarith : 0 < 1 + s)).2
      linarith
  have hts : 1 - t = s * t := by
    dsimp [t]
    field_simp
    <;> ring
  have hq : (m : ℝ) * t ^ 2 = q := by simp [t, q, div_pow, div_eq_mul_inv]
  have hqt : (1 - t) ^ 2 = q := by rw [hts, mul_pow, hs2, hq]
  have ha : Feasible H a := by
    constructor
    · intro b c; dsimp [a]; split_ifs <;> constructor <;> linarith [ht.1, ht.2]
    · intro b c hbc
      have he := SimpleGraph.starGraph_adj.mp hbc
      rcases he.2 with hb | hc
      · subst b; simp [a, Ne.symm he.1]
      · subst c; simp [a, he.1]
  have hdegree : ∀ b : Option (Fin m), H.degree b = if b = none then m else 1 := by
    intro b
    cases b with
    | none => simp [H, SimpleGraph.degree_starGraph_center]
    | some i => simpa [H] using
        (SimpleGraph.degree_starGraph_of_ne_center (r := (none : Option (Fin m)))
          (v := some i) (by simp))
  have hl (b : Option (Fin m)) : load H a b = q := by
    simp only [load, a, sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree, hdegree]
    cases b <;> simp [hq, hqt]
  have hmax : maxLoad H a = q := by simp [maxLoad, hl]
  have hD : H.maxDegree = m := by
    apply le_antisymm (H.maxDegree_le_of_forall_degree_le m ?_) ?_
    · intro b; rw [hdegree]; split_ifs <;> omega
    · simpa [hdegree] using H.degree_le_maxDegree none
  have hk : kappa H = q := by
    apply le_antisymm ?_ ?_
    · rw [← hmax]
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro r ⟨u, hu, rfl⟩
        exact le_trans (sum_nonneg (fun c _ => sq_nonneg (u none c)))
          (show load H u none ≤ maxLoad H u from le_sup' _ (mem_univ none))
      · exact ⟨a, ha, rfl⟩
    · simpa only [hD] using maximum_degree_lower_bound H (by omega)
  have hμ : μ ∈ stdSimplex ℝ (Option (Fin m)) := by
    constructor
    · intro b; dsimp [μ]; split_ifs <;> positivity
    · rw [Fintype.sum_option]
      simp only [μ, if_pos rfl, Option.some_ne_none, if_false, sum_const,
        card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [t]
      field_simp
      nlinarith only [hs2]
  have hedges : H.edgeFinset = univ.image (fun i : Fin m => s(none, some i)) := by
    ext e
    refine Sym2.ind (fun b c => ?_) e
    cases b <;> cases c <;>
      simp [H, SimpleGraph.mem_edgeFinset, SimpleGraph.starGraph_adj]
  have hΦ (p : Option (Fin m) → ℝ) :
      Φ p = ∑ i : Fin m, p none * p (some i) / (p none + p (some i)) := by
    dsimp [Φ]
    rw [hedges, sum_image]
    · rfl
    · intro i hi j hj hij
      simpa [Sym2.eq_iff] using hij
  have hΦμ : Φ μ = q := by
    rw [hΦ]
    have hh : t * (1 / (s * (1 + s))) / (t + 1 / (s * (1 + s))) = t ^ 2 := by
      have hn : t + 1 / (s * (1 + s)) ≠ 0 := by dsimp [t]; positivity
      apply (div_eq_iff hn).2
      dsimp [t]
      field_simp
      <;> ring
    simp only [μ, if_pos rfl, Option.some_ne_none, if_false, hh, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, hq]
  have hu : ∀ p ∈ stdSimplex ℝ (Option (Fin m)), Φ p ≤ q := by
    intro p hp
    have hedge (i : Fin m) : p none * p (some i) / (p none + p (some i)) ≤
        p none * t ^ 2 + p (some i) * (1 - t) ^ 2 := by
      by_cases hz : 0 < p none + p (some i)
      · apply (div_le_iff₀ hz).2
        nlinarith [sq_nonneg (p none * t - p (some i) * (1 - t))]
      · have h0 : p none = 0 := by linarith [hp.1 none, hp.1 (some i)]
        have h1 : p (some i) = 0 := by linarith [hp.1 none, hp.1 (some i)]
        simp [h0, h1]
    rw [hΦ]
    calc
      _ ≤ ∑ i : Fin m, (p none * t ^ 2 + p (some i) * (1 - t) ^ 2) :=
        sum_le_sum (fun i _ => hedge i)
      _ = q * (p none + ∑ i : Fin m, p (some i)) := by
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul, hqt]
        rw [← sum_mul]
        calc
          _ = p none * ((m : ℝ) * t ^ 2) + (∑ i : Fin m, p (some i)) * q := by ring
          _ = _ := by rw [hq]; ring
      _ = q := by rw [← Fintype.sum_option, hp.2, mul_one]
  refine ⟨ha, hl, hk, hμ, hΦμ, hu, ?_, ?_⟩
  · intro hm1
    rw [hk]
    simp [q, s, hm1]
    <;> norm_num
  · intro hm2
    rw [hk]
    simp only [q, s, hm2, Nat.cast_ofNat]
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
      calc _ = Real.sqrt 2 * (Real.sqrt 2) ^ 2 := by ring
           _ = _ := by rw [h2]; ring
    apply (div_eq_iff (by positivity : (1 + Real.sqrt 2) ^ 2 ≠ 0)).2
    nlinarith only [h2, h3]

#check (show Option (Fin 1) from none)
#check (show ∃ m : ℕ, 1 ≤ m from ⟨1, by decide⟩)
#check (show 1 ≤ (SimpleGraph.starGraph (none : Option (Fin 1))).maxDegree from by decide)
#check (show ∃ p : Option (Fin 1) → ℝ, p ∈ stdSimplex ℝ (Option (Fin 1)) from
  ⟨fun b => if b = none then 1 else 0, by
    constructor
    · intro b
      change 0 ≤ (if b = none then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · simp [Fintype.sum_option]⟩)
#print axioms maximum_degree_lower_bound
#print axioms star_extrema

end D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema
