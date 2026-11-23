/- GID: D5/S3/Quantum/Semigroups/WuQuarticGraph
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuQuarticGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact simplex minima for the reduced Wu graph quartic. -/

import D5.S3.Quantum.Semigroups.WuCriticalQuartic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Graph optimization for the reduced finite signed Wu quartic. The unpenalized graph
formula is the Motzkin–Straus theorem applied to the complementary graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuQuarticGraph

open Finset Set
open WuCriticalQuartic
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V]

/-- Nonnegative masses of total one on the finite vertex type. -/
def simplex (V : Type*) [Fintype V] : Set (V → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

private theorem simplex_eq_range (V : Type*) [Fintype V] :
    simplex V = Set.range (fun w : Convexity.StdSimplex ℝ V => (w.weights : V → ℝ)) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext w
  simp [simplex]

private theorem simplex_compact (V : Type*) [Fintype V] : IsCompact (simplex V) := by
  rw [simplex_eq_range]
  exact isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous

private theorem simplex_nonempty [Nonempty V] : (simplex V).Nonempty := by
  rw [simplex_eq_range]
  obtain ⟨i⟩ := ‹Nonempty V›
  exact ⟨_, Convexity.StdSimplex.single i, rfl⟩

/-- The quartic graph objective in squared amplitudes, with both orientations of each edge. -/
def objective (G : SimpleGraph V) (η : V → ℝ) (κ : ℝ) (w : V → ℝ) : ℝ := by
  classical
  exact (∑ i, η i * w i) + κ * ((∑ i, w i ^ 2) +
    ∑ i, ∑ j, if G.Adj i j then w i * w j else 0)

private def kernel (G : SimpleGraph V) (i j : V) : ℝ := by
  classical
  exact if i = j ∨ G.Adj i j then 1 else 0

private def dot (f w : V → ℝ) : ℝ := ∑ v, f v * w v

private theorem objective_eq (G : SimpleGraph V) (η : V → ℝ) (κ : ℝ) (w : V → ℝ) :
    objective G η κ w = dot η w + κ * dot (fun i => dot (kernel G i) w) w := by
  classical
  unfold objective dot
  congr 2
  simp only [Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hdiag : (∑ j : V, if j = i then w j ^ 2 else 0) = w i ^ 2 := by simp
  rw [← hdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j
  · subst j
    simp [kernel, pow_two]
  · by_cases ha : G.Adj i j
    · simp [kernel, h, Ne.symm h, ha, mul_comm]
    · simp [kernel, h, Ne.symm h, ha]

private def shift (w : V → ℝ) (i j : V) (t : ℝ) : V → ℝ := by
  classical
  exact fun v => w v + (if v = i then t else 0) - (if v = j then t else 0)

private theorem dot_shift (f w : V → ℝ) (i j : V) (t : ℝ) :
    dot f (shift w i j t) = dot f w + t * (f i - f j) := by
  classical
  simp only [dot, shift, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem shift_mem {w : V → ℝ} (hw : w ∈ simplex V)
    {i j : V} (hij : i ≠ j) {t : ℝ} (hl : -w i ≤ t) (hr : t ≤ w j) :
    shift w i j t ∈ simplex V := by
  classical
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hi : v = i
    · subst v
      simpa [shift, hij] using (show 0 ≤ w i + t by linarith)
    · by_cases hj : v = j
      · subst v
        simpa [shift, hi] using sub_nonneg.mpr hr
      · simpa [shift, hi, hj] using hw.1 v
  · have h := dot_shift (fun _ : V => 1) w i j t
    simpa [dot, hw.2] using h

private theorem objective_shift_affine {G : SimpleGraph V} (η : V → ℝ)
    (κ : ℝ) (w : V → ℝ) {i j : V} (hij : G.Adj i j) :
    ∃ slope : ℝ, ∀ t, objective G η κ (shift w i j t) =
      objective G η κ w + t * slope := by
  let row := fun v => dot (kernel G v) w
  let diff := fun v => kernel G v i - kernel G v j
  have hi : diff i = 0 := by simp [diff, kernel, hij]
  have hj : diff j = 0 := by simp [diff, kernel, hij.symm]
  have hrow (t : ℝ) : (fun v => dot (kernel G v) (shift w i j t)) =
      fun v => row v + t * diff v := by
    funext v
    exact dot_shift _ _ _ _ _
  refine ⟨η i - η j + κ * (dot diff w + (row i - row j)), fun t => ?_⟩
  rw [objective_eq, objective_eq, hrow, dot_shift (fun v => row v + t * diff v), dot_shift η]
  have hlinear : dot (fun v => row v + t * diff v) w = dot row w + t * dot diff w := by
    simp only [dot, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hlinear, hi, hj]
  change _ = dot η w + κ * dot row w + _
  ring

/-- Indices carrying positive mass. -/
def positiveSupport (w : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun i => 0 < w i

private theorem mem_positiveSupport {w : V → ℝ} {v : V} :
    v ∈ positiveSupport w ↔ 0 < w v := by
  classical
  simp [positiveSupport]

private theorem shift_drop {w : V → ℝ} {i j : V} (hij : i ≠ j)
    (hi : 0 < w i) (hj : 0 < w j) {t : ℝ} (ht : t = -w i ∨ t = w j) :
    positiveSupport (shift w i j t) ⊂ positiveSupport w := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro v hv
    rw [mem_positiveSupport] at hv ⊢
    by_cases hvi : v = i
    · rwa [hvi]
    · by_cases hvj : v = j
      · rwa [hvj]
      · simpa [shift, hvi, hvj] using hv
  · intro heq
    rcases ht with rfl | rfl
    · have h : i ∈ positiveSupport (shift w i j (-w i)) := heq.symm ▸ mem_positiveSupport.mpr hi
      simp [mem_positiveSupport, shift, hij] at h
    · have h : j ∈ positiveSupport (shift w i j (w j)) := heq.symm ▸ mem_positiveSupport.mpr hj
      simp [mem_positiveSupport, shift, hij.symm] at h

private theorem edge_transfer {G : SimpleGraph V} (η : V → ℝ) (κ : ℝ)
    {w : V → ℝ} (hw : w ∈ simplex V) {i j : V} (hij : G.Adj i j)
    (hi : 0 < w i) (hj : 0 < w j) :
    ∃ t : ℝ, (t = -w i ∨ t = w j) ∧ shift w i j t ∈ simplex V ∧
      positiveSupport (shift w i j t) ⊂ positiveSupport w ∧
      objective G η κ (shift w i j t) ≤ objective G η κ w := by
  obtain ⟨slope, ha⟩ := objective_shift_affine η κ w hij
  have hbounds : -w i ≤ w j := by linarith
  have endpoint (t : ℝ) (ht : t = -w i ∨ t = w j) (hs : t * slope ≤ 0) :
      (t = -w i ∨ t = w j) ∧ shift w i j t ∈ simplex V ∧
        positiveSupport (shift w i j t) ⊂ positiveSupport w ∧
        objective G η κ (shift w i j t) ≤ objective G η κ w := by
    have hinterval : -w i ≤ t ∧ t ≤ w j := by
      rcases ht with rfl | rfl
      · exact ⟨le_rfl, hbounds⟩
      · exact ⟨hbounds, le_rfl⟩
    exact ⟨ht, shift_mem hw hij.ne hinterval.1 hinterval.2, shift_drop hij.ne hi hj ht,
      ha t ▸ add_le_of_nonpos_right hs⟩
  rcases le_total (0 : ℝ) slope with h | h
  · exact ⟨-w i, endpoint _ (Or.inl rfl) (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hi.le) h)⟩
  · exact ⟨w j, endpoint _ (Or.inr rfl) (mul_nonpos_of_nonneg_of_nonpos hj.le h)⟩

private theorem independent_no_worse (G : SimpleGraph V) (η : V → ℝ) (κ : ℝ)
    {w : V → ℝ} (hw : w ∈ simplex V) :
    ∃ u ∈ simplex V, G.IsIndepSet (positiveSupport u : Set V) ∧
      positiveSupport u ⊆ positiveSupport w ∧ objective G η κ u ≤ objective G η κ w := by
  classical
  suffices ∀ n (x : V → ℝ), (positiveSupport x).card = n → x ∈ simplex V →
      ∃ u ∈ simplex V, G.IsIndepSet (positiveSupport u : Set V) ∧
        positiveSupport u ⊆ positiveSupport x ∧ objective G η κ u ≤ objective G η κ x by
    exact this _ w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx hxΔ
    by_cases h : G.IsIndepSet (positiveSupport x : Set V)
    · exact ⟨x, hxΔ, h, Finset.Subset.rfl, le_rfl⟩
    · rw [SimpleGraph.isIndepSet_iff, Set.Pairwise] at h
      push Not at h
      obtain ⟨i, hi, j, hj, _, hij⟩ := h
      obtain ⟨t, _, ht, hsub, hle⟩ := edge_transfer η κ hxΔ hij
        (mem_positiveSupport.mp hi) (mem_positiveSupport.mp hj)
      obtain ⟨u, hu, hind, husub, hcost⟩ := ih _ (hx ▸ Finset.card_lt_card hsub) _ rfl ht
      exact ⟨u, hu, hind, husub.trans (Finset.ssubset_iff_subset_ne.mp hsub).1, hcost.trans hle⟩

/-- Every simplex point has an independent-support improvement, and the weighted minimum
is attained with independent support. The linear penalties and scale may be arbitrary reals. -/
theorem independent_support_minimum [Nonempty V] (G : SimpleGraph V) (η : V → ℝ) (κ : ℝ) :
    (∀ w ∈ simplex V, ∃ u ∈ simplex V, G.IsIndepSet (positiveSupport u : Set V) ∧
      positiveSupport u ⊆ positiveSupport w ∧ objective G η κ u ≤ objective G η κ w) ∧
    ∃ u ∈ simplex V, G.IsIndepSet (positiveSupport u : Set V) ∧
      ∀ w ∈ simplex V, objective G η κ u ≤ objective G η κ w := by
  classical
  refine ⟨fun _ hw => independent_no_worse G η κ hw, ?_⟩
  have hc : Continuous (objective G η κ) := by
    rw [funext (objective_eq G η κ)]
    unfold dot
    fun_prop
  obtain ⟨w, hw, hmin⟩ := (simplex_compact V).exists_isMinOn simplex_nonempty hc.continuousOn
  obtain ⟨u, hu, hind, _, hle⟩ := independent_no_worse G η κ hw
  exact ⟨u, hu, hind, fun _ hx => hle.trans (hmin hx)⟩

private theorem support_sum {w : V → ℝ} (hw : w ∈ simplex V) :
    ∑ i ∈ positiveSupport w, w i = 1 := by
  classical
  rw [← hw.2]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
    le_antisymm (le_of_not_gt (mt mem_positiveSupport.mpr hi)) (hw.1 i)

private theorem objective_zero_penalty_of_independent {G : SimpleGraph V} {w : V → ℝ}
    (hw : w ∈ simplex V) (hind : G.IsIndepSet (positiveSupport w : Set V)) (κ : ℝ) :
    objective G 0 κ w = κ * ∑ i ∈ positiveSupport w, w i ^ 2 := by
  classical
  have zero_outside (i : V) (hi : i ∉ positiveSupport w) : w i = 0 :=
    le_antisymm (le_of_not_gt (mt mem_positiveSupport.mpr hi)) (hw.1 i)
  have hedge : (∑ i, ∑ j, if G.Adj i j then w i * w j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hij
    swap
    · rfl
    by_cases hi : i ∈ positiveSupport w
    · by_cases hj : j ∈ positiveSupport w
      · exact (hind hi hj hij.ne hij).elim
      · rw [zero_outside j hj, mul_zero]
    · rw [zero_outside i hi, zero_mul]
  have hsq : ∑ i ∈ positiveSupport w, w i ^ 2 = ∑ i, w i ^ 2 :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by rw [zero_outside i hi]; norm_num
  simp [objective, hedge, hsq]

/-- Equal mass on the selected vertices and zero mass on the others. -/
def uniform (s : Finset V) (v : V) : ℝ := by
  classical
  exact if v ∈ s then 1 / (s.card : ℝ) else 0

private theorem uniform_mem (s : Finset V) (hs : 0 < s.card) : uniform s ∈ simplex V := by
  classical
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast hs
  refine ⟨fun v => by unfold uniform; split <;> positivity, ?_⟩
  calc
    (∑ v, uniform s v) = ∑ v ∈ s, uniform s v :=
      (Finset.sum_subset (Finset.subset_univ _) fun v _ hv => by simp [uniform, hv]).symm
    _ = ∑ _v ∈ s, (1 / (s.card : ℝ)) :=
      Finset.sum_congr rfl fun v hv => by simp [uniform, hv]
    _ = 1 := by simp [Finset.sum_const, nsmul_eq_mul, hpos.ne']

private theorem uniform_support (s : Finset V) (hs : 0 < s.card) :
    positiveSupport (uniform s) = s := by
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast hs
  ext v
  classical
  by_cases hv : v ∈ s <;> simp [mem_positiveSupport, uniform, hv, hpos]

omit [Fintype V] in
private theorem indepNum_pos [Finite V] [Nonempty V] (G : SimpleGraph V) : 0 < G.indepNum := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hv : G.IsIndepSet (({v} : Finset V) : Set V) := by
    simp [SimpleGraph.isIndepSet_iff]
  change 1 ≤ G.indepNum
  simpa using hv.card_le_indepNum

private theorem unpenalized_lower [Nonempty V] (G : SimpleGraph V) {κ : ℝ} (hκ : 0 < κ)
    {w : V → ℝ} (hw : w ∈ simplex V) :
    κ / (G.indepNum : ℝ) ≤ objective G 0 κ w := by
  obtain ⟨u, hu, hind, _, hcost⟩ := independent_no_worse G 0 κ hw
  refine le_trans ?_ hcost
  have hpos : 0 < (G.indepNum : ℝ) := by exact_mod_cast indepNum_pos G
  have hcard : ((positiveSupport u).card : ℝ) ≤ G.indepNum := by
    exact_mod_cast hind.card_le_indepNum
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (positiveSupport u) (fun _ => (1 : ℝ)) u
  simp only [one_mul, support_sum hu, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hn : 0 ≤ ∑ i ∈ positiveSupport u, u i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  have hlower : 1 / (G.indepNum : ℝ) ≤ ∑ i ∈ positiveSupport u, u i ^ 2 :=
    (div_le_iff₀ hpos).2 (by
      rw [mul_comm]
      exact hcs.trans (mul_le_mul_of_nonneg_right hcard hn))
  rw [objective_zero_penalty_of_independent hu hind, ← mul_one_div]
  exact mul_le_mul_of_nonneg_left hlower hκ.le

private theorem uniform_attains [Nonempty V] (G : SimpleGraph V) (κ : ℝ) :
    ∃ s : Finset V, G.IsNIndepSet G.indepNum s ∧ uniform s ∈ simplex V ∧
      objective G 0 κ (uniform s) = κ / (G.indepNum : ℝ) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hp : 0 < s.card := hs.card_eq.symm ▸ indepNum_pos G
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast hp
  refine ⟨s, hs, uniform_mem s hp, ?_⟩
  rw [objective_zero_penalty_of_independent (uniform_mem s hp)
    (by rw [uniform_support s hp]; exact hs.isIndepSet), uniform_support s hp]
  have heq : (∑ i ∈ s, uniform s i ^ 2) = 1 / (s.card : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (1 / (s.card : ℝ)) ^ 2 :=
        Finset.sum_congr rfl fun i hi => by simp [uniform, hi]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp [hpos.ne']
  rw [heq, hs.card_eq, mul_one_div]

/-- Uniform mass on a maximum independent set attains the sharp unpenalized minimum. -/
theorem unpenalized_minimum [Nonempty V] (G : SimpleGraph V) {κ : ℝ} (hκ : 0 < κ) :
    ∃ s : Finset V, G.IsNIndepSet G.indepNum s ∧ uniform s ∈ simplex V ∧
      objective G 0 κ (uniform s) = κ / (G.indepNum : ℝ) ∧
      IsLeast (objective G 0 κ '' simplex V) (κ / (G.indepNum : ℝ)) := by
  obtain ⟨s, hs, hw, heq⟩ := uniform_attains G κ
  exact ⟨s, hs, hw, heq, ⟨⟨uniform s, hw, heq⟩,
    fun _ ⟨_, hw', hm'⟩ => hm' ▸ unpenalized_lower G hκ hw'⟩⟩

/-- The positive-temperature coefficient in squared masses. Its exponential Schur factor
uses the quartic normalized by the square of the input coherence coefficient. -/
def wuCoefficient (β p r : ℝ) : ℝ :=
  let ΔA := exponentA β p - exponentA β r
  let ΔE := exponentE β p - exponentE β r
  let ΔD := exponentD β p - exponentD β r
  ((Real.sinh ((1 - 1 / p) * β / 2) / Real.sinh (β / (2 * p))) ^ 2 / 4) *
    (ΔD - ΔE ^ 2 / (4 * ΔA))

private theorem wuCoefficient_pos {β p r : ℝ} (hβ : 0 < β) (hp : 1 < p) (hpr : p < r) :
    0 < wuCoefficient β p r := by
  have hp₀ : 0 < p := by linarith
  have hinv : 1 / p < 1 := (div_lt_iff₀ hp₀).2 (by simpa using hp)
  have hnum := Real.sinh_pos_iff.mpr (show 0 < (1 - 1 / p) * β / 2 by positivity)
  have hden := Real.sinh_pos_iff.mpr (show 0 < β / (2 * p) by positivity)
  unfold wuCoefficient
  exact mul_pos (div_pos (pow_pos (div_pos hnum hden) _) (by norm_num))
    (exponent_endpoint_schur_pos hβ hp hpr).2.1

/-- A maximum independent set attains the positive-temperature Wu objective with zero
penalties. Its exact minimum recovers the graph's independence number. -/
theorem wu_unpenalized_minimum [Nonempty V] (G : SimpleGraph V) {β p r : ℝ}
    (hβ : 0 < β) (hp : 1 < p) (hpr : p < r) :
    let κ := wuCoefficient β p r
    ∃ s : Finset V, G.IsNIndepSet G.indepNum s ∧
      uniform s ∈ simplex V ∧
      objective G 0 κ (uniform s) =
        κ / (G.indepNum : ℝ) ∧
      ∀ m : ℝ, IsLeast (objective G 0 κ '' simplex V) m ↔
        m = κ / (G.indepNum : ℝ) ∧ 0 < m ∧ (G.indepNum : ℝ) = κ / m := by
  dsimp only
  let κ := wuCoefficient β p r
  have hκ : 0 < κ := wuCoefficient_pos hβ hp hpr
  have hα : 0 < (G.indepNum : ℝ) := by exact_mod_cast indepNum_pos G
  obtain ⟨s, hs, hw, heq, hmin⟩ := unpenalized_minimum G hκ
  refine ⟨s, hs, hw, heq, fun m => ?_⟩
  constructor
  · intro hm
    have he : m = κ / (G.indepNum : ℝ) := hm.unique hmin
    refine ⟨he, he ▸ div_pos hκ hα, ?_⟩
    rw [he, div_div_eq_mul_div, mul_comm κ, mul_div_cancel_right₀ _ hκ.ne']
  · rintro ⟨rfl, _, _⟩
    exact hmin

end

end D5.S3.Quantum.Semigroups.WuQuarticGraph
