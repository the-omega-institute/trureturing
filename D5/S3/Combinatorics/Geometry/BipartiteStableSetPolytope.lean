/- GID: D5/S3/Combinatorics/Geometry/BipartiteStableSetPolytope
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/BipartiteStableSetPolytope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bipartiteness characterizes the bounded edge description of the independent-set hull. -/

module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Independent-set hulls and bounded edge inequalities on finite vertex types. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

public section

namespace D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope

universe u
variable {V : Type u}

noncomputable section
open scoped BigOperators

/-- The zero-one vector of a finite set on the original vertex type. -/
def vertexIndicator (A : Finset V) : V → ℝ :=
  (A : Set V).indicator (fun _ => 1)

/-- The real convex hull of all independent finite-set indicators. -/
def stableSetPolytope (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ (Set.range (fun A : {A : Finset V // G.IsIndepSet (A : Set V)} =>
    vertexIndicator A.val))

/-- Bounds at every vertex, together with one inequality for every edge. -/
def edgeRegion (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧ ∀ v w, G.Adj v w → x v + x w ≤ 1}

private lemma indicator_mem_region (G : SimpleGraph V) (A : Finset V)
    (hA : G.IsIndepSet (A : Set V)) : vertexIndicator A ∈ edgeRegion G := by
  classical
  constructor
  · intro v
    by_cases hv : v ∈ A <;> simp [vertexIndicator, hv]
  · intro v w hvw
    have hnot : ¬ (v ∈ A ∧ w ∈ A) := by
      rintro ⟨hv, hw⟩
      exact hA hv hw hvw.ne hvw
    by_cases hv : v ∈ A <;> by_cases hw : w ∈ A <;>
      simp_all [vertexIndicator]

private lemma region_convex (G : SimpleGraph V) : Convex ℝ (edgeRegion G) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro v
    change 0 ≤ a * x v + b * y v ∧ a * x v + b * y v ≤ 1
    exact ⟨add_nonneg (mul_nonneg ha (hx.1 v).1) (mul_nonneg hb (hy.1 v).1), by
      nlinarith [mul_le_mul_of_nonneg_left (hx.1 v).2 ha,
        mul_le_mul_of_nonneg_left (hy.1 v).2 hb]⟩
  · intro v w hvw
    change a * x v + b * y v + (a * x w + b * y w) ≤ 1
    nlinarith [mul_le_mul_of_nonneg_left (hx.2 v w hvw) ha,
      mul_le_mul_of_nonneg_left (hy.2 v w hvw) hb]

private lemma hull_subset_region (G : SimpleGraph V) :
    stableSetPolytope G ⊆ edgeRegion G := by
  apply convexHull_min _ (region_convex G)
  rintro x ⟨⟨A, hA⟩, rfl⟩
  exact indicator_mem_region G A hA

private def flip (G : SimpleGraph V) (c : G.Coloring (Fin 2)) (y : V → ℝ) : V → ℝ :=
  fun v => if c v = 0 then y v else 1 - y v

private lemma flip_involution (G : SimpleGraph V) (c : G.Coloring (Fin 2)) (y : V → ℝ) :
    flip G c (flip G c y) = y := by
  funext v
  by_cases hc : c v = 0 <;> simp [flip, hc]

private lemma edge_colors (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    {v w : V} (hvw : G.Adj v w) :
    (c v = 0 ∧ c w ≠ 0) ∨ (c v ≠ 0 ∧ c w = 0) := by
  have hn := c.valid hvw
  have hv := (c v).isLt
  have hw := (c w).isLt
  simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at *
  omega

/-- The positive support determines an independent threshold vertex after one color is complemented. -/
private lemma positive_vertex [Finite V] (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (y : V → ℝ)
    (horder : ∀ v w, G.Adj v w → c v = 0 → y v ≤ y w) :
    flip G c (fun v => if 0 < y v then 1 else 0) ∈ stableSetPolytope G := by
  classical
  let _ := Fintype.ofFinite V
  let A : Finset V := Finset.univ.filter (fun v =>
    if c v = 0 then 0 < y v else ¬ 0 < y v)
  have hA : G.IsIndepSet (A : Set V) := by
    intro v hv w hw _ hvw
    have hv' : (if c v = 0 then 0 < y v else ¬ 0 < y v) :=
      (Finset.mem_filter.mp hv).2
    have hw' : (if c w = 0 then 0 < y w else ¬ 0 < y w) :=
      (Finset.mem_filter.mp hw).2
    rcases edge_colors G c hvw with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · simp only [hc, hd, ite_true, ite_false] at hv' hw'
      exact hw' (lt_of_lt_of_le hv' (horder v w hvw hc))
    · simp only [hc, hd, ite_true, ite_false] at hv' hw'
      exact hv' (lt_of_lt_of_le hw' (horder w v hvw.symm hd))
  have heq : flip G c (fun v => if 0 < y v then 1 else 0) = vertexIndicator A := by
    funext v
    simp only [flip, vertexIndicator, Set.indicator_apply, Finset.mem_coe]
    by_cases hc : c v = 0 <;> by_cases hy : 0 < y v <;>
      simp [A, hc, hy]
  rw [heq]
  exact subset_convexHull ℝ _ ⟨⟨A, hA⟩, rfl⟩

/-- Successively remove a minimum positive level; tied minima disappear together. -/
private lemma peel_mem_hull [Finite V] (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (y : V → ℝ) (hbounds : ∀ v, 0 ≤ y v ∧ y v ≤ 1)
    (horder : ∀ v w, G.Adj v w → c v = 0 → y v ≤ y w) :
    flip G c y ∈ stableSetPolytope G := by
  classical
  let _ := Fintype.ofFinite V
  suffices ∀ n : ℕ, ∀ z : V → ℝ,
      (Finset.univ.filter (fun v => 0 < z v)).card = n →
      (∀ v, 0 ≤ z v ∧ z v ≤ 1) →
      (∀ v w, G.Adj v w → c v = 0 → z v ≤ z w) →
      flip G c z ∈ stableSetPolytope G from
    this _ y rfl hbounds horder
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hn hz ho
    let U : Finset V := Finset.univ.filter (fun v => 0 < z v)
    let b : V → ℝ := fun v => if 0 < z v then 1 else 0
    have hvertex : flip G c b ∈ stableSetPolytope G := positive_vertex G c z ho
    by_cases hU : U.Nonempty
    · obtain ⟨v₀, hv₀, hmin⟩ := U.exists_min_image z hU
      let δ := z v₀
      have hδ : 0 < δ := (Finset.mem_filter.mp hv₀).2
      have hδone : δ ≤ 1 := (hz v₀).2
      have hmin' : ∀ v, 0 < z v → δ ≤ z v := by
        intro v hv
        exact hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
      by_cases heq : δ = 1
      · have hzb : z = b := by
          funext v
          by_cases hv : 0 < z v
          · simp only [b, ite_eq_left hv]
            linarith [hmin' v hv, (hz v).2]
          · simp only [b, ite_eq_right hv]
            exact le_antisymm (le_of_not_gt hv) (hz v).1
        simpa only [hzb] using hvertex
      · have hd : 0 < 1 - δ := sub_pos.mpr (lt_of_le_of_ne hδone heq)
        let z' : V → ℝ := fun v => if 0 < z v then (z v - δ) / (1 - δ) else 0
        have hz' : ∀ v, 0 ≤ z' v ∧ z' v ≤ 1 := by
          intro v
          by_cases hv : 0 < z v
          · simp only [z', ite_eq_left hv]
            exact ⟨div_nonneg (sub_nonneg.mpr (hmin' v hv)) hd.le,
              (div_le_one hd).mpr (by linarith [(hz v).2])⟩
          · simp [z', hv]
        have ho' : ∀ v w, G.Adj v w → c v = 0 → z' v ≤ z' w := by
          intro v w hvw hc
          by_cases hv : 0 < z v
          · have hw : 0 < z w := lt_of_lt_of_le hv (ho v w hvw hc)
            simp only [z', ite_eq_left hv, ite_eq_left hw]
            exact (div_le_div_iff_of_pos_right hd).mpr (by linarith [ho v w hvw hc])
          · simpa only [z', ite_eq_right hv] using (hz' w).1
        have hsmall : (Finset.univ.filter (fun v => 0 < z' v)).card < n := by
          rw [← hn]
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro v hv
            have hp := (Finset.mem_filter.mp hv).2
            have : 0 < z v := by
              by_contra hv
              simp [z', hv] at hp
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
          · intro he
            have hm : v₀ ∈ Finset.univ.filter (fun v => 0 < z' v) := by
              rw [he]
              exact hv₀
            have hp := (Finset.mem_filter.mp hm).2
            simp [z', show 0 < z v₀ from hδ, δ] at hp
        have hrest : flip G c z' ∈ stableSetPolytope G := ih _ hsmall z' rfl hz' ho'
        have hrec : ∀ v, z v = δ * b v + (1 - δ) * z' v := by
          intro v
          by_cases hv : 0 < z v
          · simp only [b, z', ite_eq_left hv, mul_one]
            rw [mul_div_cancel₀ _ (ne_of_gt hd)]
            ring
          · have hvzero : z v = 0 := le_antisymm (le_of_not_gt hv) (hz v).1
            simp [b, z', hvzero]
        have hrecflip : δ • flip G c b + (1 - δ) • flip G c z' = flip G c z := by
          funext v
          change δ * flip G c b v + (1 - δ) * flip G c z' v = flip G c z v
          by_cases hc : c v = 0 <;> simp only [flip, hc, ite_true, ite_false]
          · linarith [hrec v]
          · linarith [hrec v]
        rw [← hrecflip]
        exact convex_convexHull ℝ _ hvertex hrest hδ.le hd.le (by ring)
    · have hzb : z = b := by
        funext v
        have hv : ¬ 0 < z v := by
          intro hv
          exact hU ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
        have hvzero : z v = 0 := le_antisymm (le_of_not_gt hv) (hz v).1
        simp [b, hvzero]
      simpa only [hzb] using hvertex

private lemma region_subset_hull [Finite V] (G : SimpleGraph V) (hG : G.IsBipartite) :
    edgeRegion G ⊆ stableSetPolytope G := by
  classical
  obtain ⟨c⟩ := hG
  intro x hx
  have hb : ∀ v, 0 ≤ flip G c x v ∧ flip G c x v ≤ 1 := by
    intro v
    by_cases hc : c v = 0 <;> simp only [flip, hc, ite_true, ite_false]
    · exact hx.1 v
    · constructor <;> linarith [(hx.1 v).1, (hx.1 v).2]
  have ho : ∀ v w, G.Adj v w → c v = 0 → flip G c x v ≤ flip G c x w := by
    intro v w hvw hc
    have hd : c w ≠ 0 := by
      intro he
      exact c.valid hvw (hc.trans he.symm)
    simp only [flip, hc, hd, ite_true, ite_false]
    linarith [hx.2 v w hvw]
  simpa only [flip_involution] using peel_mem_hull G c (flip G c x) hb ho

/-- A single positive summand of the half-vector meets every edge exactly once. -/
private lemma bipartite_of_half_mem (G : SimpleGraph V)
    (hh : (fun _ : V => (1 / 2 : ℝ)) ∈ stableSetPolytope G) : G.IsBipartite := by
  classical
  obtain ⟨ι, _, a, z, ha, hsum, hz, hrep⟩ := mem_convexHull_iff_exists_fintype.mp hh
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => ha i)).mp
    (show 0 < ∑ i, a i by rw [hsum]; norm_num)
  obtain ⟨⟨A, hA⟩, hAj⟩ := hz j
  change vertexIndicator A = z j at hAj
  have hsaturate : ∀ v w, G.Adj v w → z j v + z j w = 1 := by
    intro v w hvw
    have hle : ∀ i ∈ Finset.univ, a i * (z i v + z i w) ≤ a i := by
      intro i _
      obtain ⟨⟨B, hB⟩, hBi⟩ := hz i
      change vertexIndicator B = z i at hBi
      have he := (indicator_mem_region G B hB).2 v w hvw
      rw [hBi] at he
      nlinarith [mul_le_mul_of_nonneg_left he (ha i)]
    have hv : ∑ i, a i * z i v = (1 / 2 : ℝ) := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hrep v
    have hw : ∑ i, a i * z i w = (1 / 2 : ℝ) := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hrep w
    have heq : ∑ i, a i * (z i v + z i w) = ∑ i, a i := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hv, hw, hsum]
      norm_num
    have he := (Finset.sum_eq_sum_iff_of_le hle).mp heq j (Finset.mem_univ _)
    exact mul_left_cancel₀ (ne_of_gt hj) (by simpa only [mul_one] using he)
  apply (show G.IsBipartiteWith (A : Set V) (A : Set V)ᶜ from ?_).isBipartite
  constructor
  · exact Set.disjoint_left.mpr (by intro v hv hn; exact hn hv)
  · intro v w hvw
    have he := hsaturate v w hvw
    rw [← hAj] at he
    by_cases hv : v ∈ A <;> by_cases hw : w ∈ A <;>
      simp_all [vertexIndicator]

/-- The bounded edge inequalities describe the independent-set hull exactly for bipartite graphs. -/
theorem stableSetPolytope_eq_edgeRegion_iff [Finite V] (G : SimpleGraph V) :
    stableSetPolytope G = edgeRegion G ↔ G.IsBipartite := by
  constructor
  · intro heq
    apply bipartite_of_half_mem G
    rw [heq]
    constructor
    · intro v
      norm_num
    · intro v w _
      norm_num
  · intro hG
    exact Set.Subset.antisymm (hull_subset_region G) (region_subset_hull G hG)

end
end D5.S3.Combinatorics.Geometry.BipartiteStableSetPolytope
