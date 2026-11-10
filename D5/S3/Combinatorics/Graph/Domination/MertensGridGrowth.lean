/- GID: D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MertensGridGrowth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: Actual ordinary grid and cylinder domination counts have the same unrestricted joint per-vertex limit. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverage
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Exact ordinary domination counts, finite repair and block injections. -/

set_option autoImplicit false
set_option maxRecDepth 2000

noncomputable section

namespace D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth

open Finset SimpleGraph
open DominatingSetAverage

/-- Number of all ordinary dominating vertex subsets, with no symmetry quotient. -/
def count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  (domSets G).card

/-- The actual path Cartesian product on its labelled vertex set. -/
def grid (m n : ℕ) : SimpleGraph (Fin m × Fin n) := pathGraph m □ pathGraph n

/-- The actual cycle-path Cartesian product on the same labelled vertex set. -/
def cylinder (m n : ℕ) : SimpleGraph (Fin m × Fin n) := cycleGraph m □ pathGraph n

/-- Per-vertex growth, using real powers. Only positive dimensions enter the limit. -/
def growth (a m n : ℕ) : ℝ := (a : ℝ) ^ (1 / (m * n : ℕ) : ℝ)

/-- The complete unrestricted joint-limit event. -/
def JointGrowth : Prop :=
  ∃ μ : ℝ, μ ∈ Set.Icc 1 2 ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, 3 ≤ N ∧ ∀ m n : ℕ, N ≤ m → N ≤ n →
      |growth (count (grid m n)) m n - μ| < ε ∧
      |growth (count (cylinder m n)) m n - μ| < ε

private theorem count_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (h : G ≤ H) : count G ≤ count H := by
  classical
  apply card_le_card
  intro S hS
  apply mem_domSets.mpr
  intro x
  rcases (mem_domSets.mp hS) x with hx | ⟨y, hy, hxy⟩
  · exact Or.inl hx
  · exact Or.inr ⟨y, hy, h hxy⟩

/-- Repair by filling B, retaining S ∩ B to distinguish every fibre. -/
private theorem repair_count {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (B : Finset V)
    (outside : ∀ x, x ∉ B → ∀ y, H.Adj x y → G.Adj x y) :
    count H ≤ count G * 2 ^ B.card := by
  classical
  let repair : ↥(domSets H) → ↥(domSets G) × ↥(B.powerset) := fun S =>
    (⟨S.val ∪ B, mem_domSets.mpr (by
      intro x
      by_cases hx : x ∈ B
      · exact Or.inl (mem_union_right _ hx)
      · rcases (mem_domSets.mp S.property) x with hs | ⟨y, hy, hxy⟩
        · exact Or.inl (mem_union_left _ hs)
        · exact Or.inr ⟨y, mem_union_left _ hy, outside x hx y hxy⟩)⟩,
      ⟨S.val ∩ B, mem_powerset.mpr inter_subset_right⟩)
  have hinj : Function.Injective repair := by
    intro S T h
    have hu : S.val ∪ B = T.val ∪ B := congrArg (fun p => p.1.val) h
    have hi : S.val ∩ B = T.val ∩ B := congrArg (fun p => p.2.val) h
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ B
    · have hh := congrArg (fun U : Finset V => x ∈ U) hi
      simpa [hx] using hh
    · have hh := congrArg (fun U : Finset V => x ∈ U) hu
      simpa [hx] using hh
  have hh := Fintype.card_le_of_injective repair hinj
  simpa only [count, Fintype.card_prod, Fintype.card_coe, card_powerset] using hh

private theorem cycle_interior {m : ℕ} (hm : 3 ≤ m) (x y : Fin m)
    (hx : x.val ≠ 0) (hl : x.val + 1 ≠ m) (h : (cycleGraph m).Adj x y) :
    (pathGraph m).Adj x y := by
  rw [cycleGraph_adj'] at h
  rw [pathGraph_adj]
  have hh : (x - y).val = (x.val + (m - y.val)) % m := by simp [Fin.sub_def, Nat.add_comm]
  have hh' : (y - x).val = (y.val + (m - x.val)) % m := by simp [Fin.sub_def, Nat.add_comm]
  rcases h with h | h
  · rw [hh] at h
    have hb := y.isLt
    have hb' := x.isLt
    have he : x.val + (m - y.val) < 2 * m := by omega
    have hp : x.val + (m - y.val) < m ∨ m ≤ x.val + (m - y.val) := by omega
    rcases hp with hp | hp
    · rw [Nat.mod_eq_of_lt hp] at h
      omega
    · rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rw [hh'] at h
    have hb := y.isLt
    have hb' := x.isLt
    have he : y.val + (m - x.val) < 2 * m := by omega
    by_cases hp : y.val + (m - x.val) < m
    · rw [Nat.mod_eq_of_lt hp] at h
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- Both endpoint columns; m≥3 keeps these two fibres disjoint. -/
def boundary (m n : ℕ) : Finset (Fin m × Fin n) :=
  univ.filter (fun x => x.1.val = 0 ∨ x.1.val + 1 = m)

private theorem boundary_card {m n : ℕ} (hm : 3 ≤ m) : (boundary m n).card = 2 * n := by
  classical
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨m - 1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have he : boundary m n = ({a, b} : Finset (Fin m)) ×ˢ (univ : Finset (Fin n)) := by
    ext x
    simp [boundary, a, b, Fin.ext_iff]
    omega
  rw [he, card_product, card_pair hab, card_univ, Fintype.card_fin]

/-- Finite seam comparison for every source dimension, including m=3 and n=1. -/
theorem finite_seam_bound {m n : ℕ} (hm : 3 ≤ m) :
    count (grid m n) ≤ count (cylinder m n) ∧
    count (cylinder m n) ≤ count (grid m n) * 4 ^ n := by
  constructor
  · apply count_mono
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨pathGraph_le_cycleGraph h.1, h.2⟩
    · exact Or.inr h
  · have hh := repair_count (grid m n) (cylinder m n) (boundary m n) (by
      intro x hx y h
      have hx' : x.1.val ≠ 0 ∧ x.1.val + 1 ≠ m := by simpa [boundary] using hx
      rcases h with h | h
      · exact Or.inl ⟨cycle_interior hm x.1 y.1 hx'.1 hx'.2 h.1, h.2⟩
      · exact Or.inr h)
    rw [boundary_card hm] at hh
    have hp : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; rfl
    simpa only [hp] using hh

/-- Independent local choices are recovered by restriction to disjoint embedded blocks.
Vertices outside every block are selected. Cross-block edges may be present. -/
private theorem block_count {I V W : Type*} [Fintype I] [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : I × V → W) (he : Function.Injective e)
    (hedge : ∀ i x y, G.Adj x y → H.Adj (e (i, x)) (e (i, y))) :
    count G ^ Fintype.card I ≤ count H := by
  classical
  let assemble (f : I → ↥(domSets G)) : Finset W :=
    univ.filter (fun w => ∀ i v, e (i, v) = w → v ∈ (f i).val)
  have hm (f : I → ↥(domSets G)) (i : I) (v : V) :
      e (i, v) ∈ assemble f ↔ v ∈ (f i).val := by
    constructor
    · intro h
      exact (mem_filter.mp h).2 i v rfl
    · intro hv
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro j w hjw
      have h := he hjw
      have hi : j = i := congrArg Prod.fst h
      have hv' : w = v := congrArg Prod.snd h
      subst j
      subst w
      exact hv
  have hd (f : I → ↥(domSets G)) : H.IsDominating (assemble f : Set W) := by
    intro w
    by_cases hw : ∃ p, e p = w
    · obtain ⟨⟨i, v⟩, rfl⟩ := hw
      rcases (mem_domSets.mp (f i).property) v with hv | ⟨u, hu, hvu⟩
      · exact Or.inl ((hm f i v).mpr hv)
      · exact Or.inr ⟨e (i, u), (hm f i u).mpr hu, hedge i v u hvu⟩
    · left
      apply mem_filter.mpr
      exact ⟨mem_univ _, fun i v h => (hw ⟨(i, v), h⟩).elim⟩
  let embed : (I → ↥(domSets G)) → ↥(domSets H) :=
    fun f => ⟨assemble f, mem_domSets.mpr (hd f)⟩
  have hi : Function.Injective embed := by
    intro f g h
    have hh : assemble f = assemble g := congrArg Subtype.val h
    funext i
    apply Subtype.ext
    ext v
    rw [← hm f i v, ← hm g i v, hh]
  have hh := Fintype.card_le_of_injective embed hi
  simpa only [count, Fintype.card_fun, Fintype.card_coe] using hh

private def place {a b M N q p : ℕ} (ha : q * a ≤ M) (hb : p * b ≤ N)
    (z : (Fin q × Fin p) × (Fin a × Fin b)) : Fin M × Fin N :=
  (⟨z.1.1.val * a + z.2.1.val, by have := z.1.1.isLt; have := z.2.1.isLt; nlinarith⟩,
   ⟨z.1.2.val * b + z.2.2.val, by have := z.1.2.isLt; have := z.2.2.isLt; nlinarith⟩)

private theorem place_injective {a b M N q p : ℕ} (ha : q * a ≤ M) (hb : p * b ≤ N) :
    Function.Injective (place ha hb) := by
  intro z w h
  have hx := congrArg (fun v : Fin M × Fin N => v.1.val) h
  have hy := congrArg (fun v : Fin M × Fin N => v.2.val) h
  dsimp [place] at hx hy
  have hxa := z.2.1.isLt
  have hwa := w.2.1.isLt
  have hyb := z.2.2.isLt
  have hwb := w.2.2.isLt
  have hq : z.1.1.val = w.1.1.val := by
    by_contra hn
    have : z.1.1.val + 1 ≤ w.1.1.val ∨ w.1.1.val + 1 ≤ z.1.1.val := by omega
    rcases this with h | h <;> nlinarith
  have hp : z.1.2.val = w.1.2.val := by
    by_contra hn
    have : z.1.2.val + 1 ≤ w.1.2.val ∨ w.1.2.val + 1 ≤ z.1.2.val := by omega
    rcases this with h | h <;> nlinarith
  apply Prod.ext
  · exact Prod.ext (Fin.ext hq) (Fin.ext hp)
  · exact Prod.ext (Fin.ext (by nlinarith)) (Fin.ext (by nlinarith))

/-- Actual independent block choices, padded by all leftover vertices. -/
theorem tiling_count (a b M N : ℕ) :
    count (grid a b) ^ ((M / a) * (N / b)) ≤ count (grid M N) := by
  let q := M / a
  let p := N / b
  have ha : q * a ≤ M := Nat.div_mul_le_self M a
  have hb : p * b ≤ N := Nat.div_mul_le_self N b
  have hh := block_count (I := Fin q × Fin p) (grid a b) (grid M N)
    (place ha hb) (place_injective ha hb) (by
      intro i x y h
      rcases h with h | h
      · left
        refine ⟨?_, ?_⟩
        · rw [pathGraph_adj] at h ⊢
          dsimp [place]
          omega
        · apply Fin.ext
          dsimp [place]
          have := congrArg Fin.val h.2
          omega
      · right
        refine ⟨?_, ?_⟩
        · rw [pathGraph_adj] at h ⊢
          dsimp [place]
          omega
        · apply Fin.ext
          dsimp [place]
          have := congrArg Fin.val h.2
          omega)
  simpa [Fintype.card_prod, Fintype.card_fin, q, p] using hh

open Filter Topology

private theorem count_upper {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    count G ≤ 2 ^ Fintype.card V := by
  classical
  have h : domSets G ⊆ (univ : Finset V).powerset := filter_subset _ _
  simpa only [card_powerset, card_univ, count] using card_le_card h

/-- Normalized logarithmic count of the actual grid. -/
def gridRate (z : ℕ × ℕ) : ℝ :=
  Real.log (count (grid z.1 z.2)) / ((z.1 : ℝ) * (z.2 : ℝ))

private theorem rate_nonneg (z : ℕ × ℕ) : 0 ≤ gridRate z := by
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_of_lt (domSets_card_pos (grid z.1 z.2))
  · positivity

private theorem rate_upper (z : ℕ × ℕ) : gridRate z ≤ Real.log 2 := by
  by_cases hm : z.1 = 0
  · simp [gridRate, hm, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  by_cases hn : z.2 = 0
  · simp [gridRate, hn, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hd : 0 < (z.1 : ℝ) * (z.2 : ℝ) := by positivity
  have hc : (count (grid z.1 z.2) : ℝ) ≤ 2 ^ (z.1 * z.2) := by
    have hnat : count (grid z.1 z.2) ≤ 2 ^ (z.1 * z.2) := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using count_upper (grid z.1 z.2)
    exact_mod_cast hnat
  have hl := Real.log_le_log (by exact_mod_cast domSets_card_pos (grid z.1 z.2)) hc
  rw [Real.log_pow] at hl
  apply (div_le_iff₀ hd).mpr
  simpa only [Nat.cast_mul, mul_comm] using hl

private def fraction (a M : ℕ) : ℝ := ((M / a : ℕ) : ℝ) * a / M

private theorem fraction_limit {a : ℕ} (ha : 0 < a) :
    Tendsto (fraction a) atTop (𝓝 1) := by
  have h : Tendsto (fun M : ℕ => (1 : ℝ) - (M % a : ℕ) / (M : ℝ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_mod_div_atTop_nhds_zero_nat ha)
  have he : (fraction a) =ᶠ[atTop] (fun M : ℕ => 1 - (M % a : ℕ) / (M : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hne : (M : ℝ) ≠ 0 := by positivity
    have hid : ((M / a : ℕ) : ℝ) * a + (M % a : ℕ) = (M : ℝ) := by
      have hidn : (M/a)*a + M%a = M := by simpa only [Nat.mul_comm] using Nat.div_add_mod M a
      exact_mod_cast hidn
    dsimp [fraction]
    apply (div_eq_iff hne).mpr
    field_simp
    nlinarith
  have h' : Tendsto (fun M : ℕ => (1 : ℝ) - (M % a : ℕ) / (M : ℝ)) atTop (𝓝 1) := by simpa using h
  exact h'.congr' he.symm

private theorem rate_tiling {a b M N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hM : 0 < M) (hN : 0 < N) :
    gridRate (a,b) * fraction a M * fraction b N ≤ gridRate (M,N) := by
  have hc : ((count (grid a b) ^ ((M/a)*(N/b)) : ℕ) : ℝ) ≤ count (grid M N) :=
    Nat.cast_le.mpr (tiling_count a b M N)
  have hp : (0 : ℝ) < count (grid a b) := by exact_mod_cast domSets_card_pos (grid a b)
  push_cast at hc
  have hl := Real.log_le_log (pow_pos hp _) hc
  rw [Real.log_pow] at hl
  have hd : 0 < (M : ℝ) * N := by positivity
  calc
    _ = (((M/a : ℕ) : ℝ) * (N/b : ℕ) * Real.log (count (grid a b))) /
        ((M : ℝ) * N) := by
      dsimp [gridRate, fraction]
      have ha' : (a : ℝ) ≠ 0 := by positivity
      have hb' : (b : ℝ) ≠ 0 := by positivity
      field_simp

    _ ≤ _ := by
      apply (div_le_div_iff_of_pos_right hd).mpr
      simpa only [Nat.cast_mul] using hl

/-- Supremum of all positive-area block rates (zero-area rates are zero). -/
def entropy : ℝ := sSup (Set.range gridRate)

private theorem rate_tendsto : Tendsto gridRate atTop (𝓝 entropy) := by
  have hbounded : BddAbove (Set.range gridRate) := ⟨Real.log 2, by rintro _ ⟨z,rfl⟩; exact rate_upper z⟩
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply tendsto_order.2
  constructor
  · intro r hr
    obtain ⟨v, ⟨⟨a,b⟩,rfl⟩, hv⟩ := exists_lt_of_lt_csSup (Set.range_nonempty gridRate) hr
    by_cases ha : a = 0
    · have hr0 : r < 0 := by simpa [gridRate, ha] using hv
      exact Eventually.of_forall (fun z => hr0.trans_le (rate_nonneg z))
    by_cases hb : b = 0
    · have hr0 : r < 0 := by simpa [gridRate, hb] using hv
      exact Eventually.of_forall (fun z => hr0.trans_le (rate_nonneg z))
    have ht := (((tendsto_const_nhds : Tendsto (fun _ : ℕ × ℕ => gridRate (a,b)) atTop (𝓝 (gridRate (a,b)))).mul ((fraction_limit (Nat.pos_of_ne_zero ha)).comp hfst)).mul
      ((fraction_limit (Nat.pos_of_ne_zero hb)).comp hsnd))
    have ht' : Tendsto (fun z : ℕ × ℕ => gridRate (a,b) * fraction a z.1 * fraction b z.2)
        atTop (𝓝 (gridRate (a,b))) := by simpa using ht
    have hh := (tendsto_order.1 ht').1 r hv
    filter_upwards [hh, eventually_ge_atTop (1,1)] with z hz hz1
    exact hz.trans_le (rate_tiling (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
      (lt_of_lt_of_le Nat.zero_lt_one hz1.1) (lt_of_lt_of_le Nat.zero_lt_one hz1.2))
  · intro r hr
    exact Eventually.of_forall (fun z =>
      (le_csSup hbounded (Set.mem_range_self z)).trans_lt hr)

/-- Cylinder logarithmic growth on exactly the same labels. -/
def cylinderRate (z : ℕ × ℕ) : ℝ :=
  Real.log (count (cylinder z.1 z.2)) / ((z.1 : ℝ) * (z.2 : ℝ))

private theorem cylinder_rate_bounds {m n : ℕ} (hm : 3 ≤ m) (hn : 0 < n) :
    gridRate (m,n) ≤ cylinderRate (m,n) ∧
    cylinderRate (m,n) ≤ gridRate (m,n) + Real.log 4 / m := by
  have hs := finite_seam_bound (n := n) hm
  have hg : (0 : ℝ) < count (grid m n) := by exact_mod_cast domSets_card_pos (grid m n)
  have hc : (0 : ℝ) < count (cylinder m n) := by exact_mod_cast domSets_card_pos (cylinder m n)
  have hd : 0 < (m : ℝ) * n := mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr hn)
  constructor
  · exact (div_le_div_iff_of_pos_right hd).mpr (Real.log_le_log hg (Nat.cast_le.mpr hs.1))
  · have hs' : (count (cylinder m n) : ℝ) ≤ (count (grid m n) : ℝ) * (4 : ℝ)^n := by exact_mod_cast hs.2
    have hl := Real.log_le_log hc hs'
    rw [Real.log_mul (ne_of_gt hg) (by positivity), Real.log_pow] at hl
    calc
      _ ≤ (Real.log (count (grid m n)) + (n : ℝ) * Real.log 4) / ((m : ℝ) * n) :=
        (div_le_div_iff_of_pos_right hd).mpr hl
      _ = _ := by
        dsimp [gridRate]
        have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hn' : (n : ℝ) ≠ 0 := by positivity
        field_simp
        <;> ring

private theorem cylinder_rate_tendsto : Tendsto cylinderRate atTop (𝓝 entropy) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have he : Tendsto (fun z : ℕ × ℕ => Real.log 4 / (z.1 : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 4)).comp hfst
  have hu : Tendsto (fun z : ℕ × ℕ => gridRate z + Real.log 4 / z.1) atTop (𝓝 entropy) := by
    simpa using rate_tendsto.add he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' rate_tendsto hu
  · filter_upwards [eventually_ge_atTop (3,1)] with z hz
    exact (cylinder_rate_bounds hz.1 (lt_of_lt_of_le Nat.zero_lt_one hz.2)).1
  · filter_upwards [eventually_ge_atTop (3,1)] with z hz
    exact (cylinder_rate_bounds hz.1 (lt_of_lt_of_le Nat.zero_lt_one hz.2)).2

/-- Both unrestricted joint limits exist and agree, for all sufficiently large pairs. -/
theorem result : JointGrowth := by
  have hb : BddAbove (Set.range gridRate) := ⟨Real.log 2, by rintro _ ⟨z,rfl⟩; exact rate_upper z⟩
  have h0 : 0 ≤ entropy := (rate_nonneg (1,1)).trans (le_csSup hb (Set.mem_range_self (1,1)))
  have h2 : entropy ≤ Real.log 2 := csSup_le (Set.range_nonempty gridRate) (by rintro _ ⟨z,rfl⟩; exact rate_upper z)
  have hμ : Real.exp entropy ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · simpa using Real.exp_le_exp.mpr h0
    · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr h2
  have hg : Tendsto (fun z : ℕ × ℕ => growth (count (grid z.1 z.2)) z.1 z.2)
      atTop (𝓝 (Real.exp entropy)) := by
    convert (Real.continuous_exp.tendsto entropy).comp rate_tendsto using 1
    funext z
    rw [growth, Real.rpow_def_of_pos (by exact_mod_cast domSets_card_pos (grid z.1 z.2))]
    simp [gridRate, Nat.cast_mul, div_eq_mul_inv]
  have hc : Tendsto (fun z : ℕ × ℕ => growth (count (cylinder z.1 z.2)) z.1 z.2)
      atTop (𝓝 (Real.exp entropy)) := by
    convert (Real.continuous_exp.tendsto entropy).comp cylinder_rate_tendsto using 1
    funext z
    rw [growth, Real.rpow_def_of_pos (by exact_mod_cast domSets_card_pos (cylinder z.1 z.2))]
    simp [cylinderRate, Nat.cast_mul, div_eq_mul_inv]
  refine ⟨Real.exp entropy, hμ, ?_⟩
  intro ε hε
  have hge := (Metric.tendsto_nhds.mp hg) ε hε
  have hce := (Metric.tendsto_nhds.mp hc) ε hε
  have hevent := hge.and hce
  obtain ⟨N,hN⟩ := eventually_atTop_prod_self.mp hevent
  refine ⟨max 3 N, le_max_left _ _, ?_⟩
  intro m n hm hn
  have h := hN m n (le_trans (le_max_right _ _) hm) (le_trans (le_max_right _ _) hn)
  simpa only [Real.dist_eq] using h

end D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth
