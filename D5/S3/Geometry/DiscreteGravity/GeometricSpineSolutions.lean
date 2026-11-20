/- GID: D5/S3/Geometry/DiscreteGravity/GeometricSpineSolutions
   generality: G
   mirror-B: D5/B/S3/Geometry/DiscreteGravity/GeometricSpineSolutions
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Geometric-spine solutions of the tree equations on every regular tree, equal stars off the spine, curvature. -/

import D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation

/-! The infinite `(q + 1)`-regular tree `T_q`, realized on `ℤ ⊕ (ℤ × Fin (q - 1) × List (Fin q))`
(a bi-infinite spine and `q - 1` rooted `q`-ary branches at each spine vertex), carries the
geometric-spine lengths `a sₙ` on spine edges and `sₙ` on branch edges, with `sₙ = t rⁿ` and
`a = (r² + 1)/(r + 1)`. They solve the tree equations of Huang, Stoica, Xia and Zhong, every vertex
off the spine has equal incident lengths, the solution is constant exactly when `r = 1`, and the
tree curvature takes the values `4/(q+1) - 2` inside branches and `2/B + 2/(q+1) - 2` on
attachment edges.

admission_basis: escape-witness. Escape witnesses: the realization of `T_q` (graph_degree,
graph_tree), ratio_spine and dVal_spine (the cancellation `a(r + 1) = r² + 1` at spine vertices),
residual_parent and residuals, constant_iff, curvature_attach and attach_gt_iff. Consumed bind-only
helpers: parent_rank, graph_adj, mem_neighbors, neighbor_eq, graph_connected, graph_acyclic,
lengths_symm, lengths_pos, ratio_branch, dVal_branch, star_branch, curvature_branch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Geometry.DiscreteGravity.GeometricSpineSolutions

open D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation

variable (q : ℕ)

/-- Vertices: the spine `ℤ`, and branch vertices `(n, b, w)`. -/
abbrev Vtx := Sum ℤ (ℤ × Fin (q - 1) × List (Fin q))

/-- The parent map: down the spine, and from a branch word to its prefix (the root to `vₙ`). -/
def parent : Vtx q → Vtx q :=
  Sum.elim (fun n => Sum.inl (n - 1))
    (fun p => p.2.2.casesOn (Sum.inl p.1) (fun _ w => Sum.inr (p.1, p.2.1, w)))

private def rank : Vtx q → ℤ := Sum.elim id (fun p => p.1 + 1 + p.2.2.length)

variable {q}

private theorem parent_rank (i : Vtx q) : rank q (parent q i) = rank q i - 1 := by
  rcases i with n | ⟨n, b, w⟩
  · rfl
  · cases w <;> simp [parent, rank]
    omega

variable (q)

/-- The tree `T_q`: each vertex joined to its parent. -/
def graph : SimpleGraph (Vtx q) := SimpleGraph.fromRel (fun i j => parent q i = j)

variable {q}

private theorem graph_adj (i j : Vtx q) : (graph q).Adj i j ↔ parent q i = j ∨ parent q j = i := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro he
    subst j
    have hr := parent_rank i
    rcases h with h | h <;> rw [h] at hr <;> omega

variable (q)

private def neighbors : Vtx q → Finset (Vtx q) :=
  Sum.elim
    (fun n => insert (Sum.inl (n - 1)) (insert (Sum.inl (n + 1))
      (Finset.univ.image fun b => Sum.inr (n, b, []))))
    (fun p => insert (parent q (Sum.inr p))
      (Finset.univ.image fun c => Sum.inr (p.1, p.2.1, c :: p.2.2)))

variable {q}

private theorem mem_neighbors (i j : Vtx q) : j ∈ neighbors q i ↔ (graph q).Adj i j := by
  rw [graph_adj]
  rcases i with n | ⟨n, b, w⟩ <;> rcases j with m | ⟨m, b', z⟩
  · simp [neighbors, parent]; omega
  · cases z <;> simp [neighbors, parent, eq_comm]
  · cases w <;> simp [neighbors, parent, eq_comm]
  · cases w <;> cases z <;> simp [neighbors, parent]
    all_goals aesop

instance graph_finite : (graph q).LocallyFinite :=
  fun i => Fintype.ofFinset (neighbors q i) (mem_neighbors i)

private theorem neighbor_eq (i : Vtx q) : (graph q).neighborFinset i = neighbors q i :=
  Set.toFinset_ofFinset (neighbors q i) (mem_neighbors i)

private theorem graph_degree (hq : 1 ≤ q) (i : Vtx q) : (graph q).degree i = q + 1 := by
  rw [← (graph q).card_neighborFinset_eq_degree, neighbor_eq]
  rcases i with n | ⟨n, b, w⟩
  · simp only [neighbors, Sum.elim_inl]
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
    simp; omega
  · simp only [neighbors, Sum.elim_inr]
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
    · simp
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro c hc
      have hr := parent_rank (q := q) (Sum.inr (n, b, w))
      rw [← hc] at hr
      simp [rank] at hr
      omega


private theorem graph_connected : (graph q).Connected := by
  have hs : ∀ n : ℤ, (graph q).Reachable (Sum.inl n) (Sum.inl 0) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact .rfl
    | succ n ih =>
      exact (show (graph q).Adj (Sum.inl ((n : ℤ) + 1)) (Sum.inl n) from
        (graph_adj _ _).mpr (Or.inl (by simp [parent]))).reachable.trans ih
    | pred n ih =>
      exact (show (graph q).Adj (Sum.inl (-(n : ℤ) - 1)) (Sum.inl (-n)) from
        (graph_adj _ _).mpr (Or.inr rfl)).reachable.trans ih
  have hb : ∀ (n : ℤ) (b : Fin (q - 1)) (w : List (Fin q)),
      (graph q).Reachable (Sum.inr (n, b, w)) (Sum.inl n) := by
    intro n b w
    induction w with
    | nil => exact (show (graph q).Adj (Sum.inr (n, b, [])) (Sum.inl n) from
        (graph_adj _ _).mpr (Or.inl rfl)).reachable
    | cons c w ih =>
      exact (show (graph q).Adj (Sum.inr (n, b, c :: w)) (Sum.inr (n, b, w)) from
        (graph_adj _ _).mpr (Or.inl rfl)).reachable.trans ih
  apply ((graph q).connected_iff_exists_forall_reachable).mpr
  refine ⟨Sum.inl 0, ?_⟩
  rintro (n | ⟨n, b, w⟩)
  · exact (hs n).symm
  · exact ((hb n b w).trans (hs n)).symm

private theorem graph_acyclic : (graph q).IsAcyclic := by
  have down : ∀ x y, (graph q).Adj x y → rank q y ≤ rank q x → y = parent q x := by
    intro x y h hle
    rcases (graph_adj x y).mp h with h | h
    · exact h.symm
    · have hr := parent_rank y
      rw [h] at hr
      omega
  intro v c hc
  classical
  obtain ⟨x, hx, hm⟩ := Finset.exists_max_image c.support.toFinset (rank q) ⟨v, by simp⟩
  have hx : x ∈ c.support := List.mem_toFinset.mp hx
  let p := c.rotate x hx
  have hp : p.IsCycle := hc.rotate hx
  have hmax : ∀ y ∈ p.support, rank q y ≤ rank q x := by
    intro y hy
    exact hm y (List.mem_toFinset.mpr ((c.mem_support_rotate_iff x hx).mp hy))
  apply hp.snd_ne_penultimate
  exact (down x p.snd (p.adj_snd hp.not_nil)
    (hmax _ (p.getVert_mem_support 1))).trans
    (down x p.penultimate (p.adj_penultimate hp.not_nil).symm
      (hmax _ (p.getVert_mem_support (p.length - 1)))).symm

private theorem graph_tree : (graph q).IsTree := ⟨graph_connected, graph_acyclic⟩

variable (q) in
/-- Scale `s_n = t rⁿ`. -/
def scale (t r : ℝ) (n : ℤ) : ℝ := t * r ^ n

variable (q) in
/-- The geometric-spine lengths: `a s_{min(n,m)}` on spine edges, `s_n` on branch edges. -/
def lengths (t r : ℝ) : Vtx q → Vtx q → ℝ :=
  Sum.elim
    (fun n => Sum.elim (fun m => (r ^ 2 + 1) / (r + 1) * scale t r (min n m))
      (fun p => scale t r p.1))
    (fun p => Sum.elim (fun _ => scale t r p.1) (fun p' => scale t r (min p.1 p'.1)))

private theorem lengths_symm (t r : ℝ) (i j : Vtx q) : lengths q t r i j = lengths q t r j i := by
  rcases i with n | ⟨n, b, w⟩ <;> rcases j with m | ⟨m, b', z⟩ <;> simp [lengths, min_comm]

private theorem lengths_pos {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (i j : Vtx q) : 0 < lengths q t r i j := by
  have hs : ∀ n, 0 < scale t r n := fun n => mul_pos ht (zpow_pos hr n)
  rcases i with n | ⟨n, b, w⟩ <;> rcases j with m | ⟨m, b', z⟩ <;>
    simp only [lengths, Sum.elim_inl, Sum.elim_inr]
  · exact mul_pos (by positivity) (hs _)
  all_goals exact hs _

private theorem ratio_spine (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ) :
    ratio (graph q) (lengths q t r) (Sum.inl n) = scale t r n := by
  have hs : scale t r (n - 1) = scale t r n / r := by
    simp only [scale, zpow_sub_one₀ hr.ne']; ring
  have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
  unfold ratio cVal dVal
  rw [neighbor_eq]
  simp only [neighbors, Sum.elim_inl]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp),
    Finset.sum_image (fun x _ y _ h => by simpa using h),
    Finset.sum_image (fun x _ y _ h => by simpa using h)]
  simp only [lengths, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, min_eq_right (by omega : n - 1 ≤ n),
    min_eq_left (by omega : n ≤ n + 1), hs]
  have hr1 : (r + 1) ≠ 0 := by positivity
  have hr2 : (r ^ 2 + 1) ≠ 0 := by positivity
  have hq1 : ((q - 1 : ℕ) : ℝ) = q - 1 := by push_cast [hq]; ring
  rw [hq1]
  have hqpos : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  field_simp
  ring

private theorem ratio_branch (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (n : ℤ) (b : Fin (q - 1))
    (w : List (Fin q)) :
    ratio (graph q) (lengths q t r) (Sum.inr (n, b, w)) = scale t r n := by
  have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
  have hp : lengths q t r (Sum.inr (n, b, w)) (parent q (Sum.inr (n, b, w))) = scale t r n := by
    cases w <;> simp [lengths, parent]
  unfold ratio cVal dVal
  rw [neighbor_eq]
  simp only [neighbors, Sum.elim_inr]
  have hnot : parent q (Sum.inr (n, b, w)) ∉
      Finset.univ.image fun c => (Sum.inr (n, b, c :: w) : Vtx q) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro c hc
    have hr := parent_rank (q := q) (Sum.inr (n, b, w))
    rw [← hc] at hr
    simp [rank] at hr
    omega
  rw [Finset.sum_insert hnot, Finset.sum_insert hnot,
    Finset.sum_image (fun x _ y _ h => by simpa using h),
    Finset.sum_image (fun x _ y _ h => by simpa using h), hp]
  simp only [lengths, Sum.elim_inr, min_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp


private theorem dVal_spine (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ) :
    dVal (graph q) (lengths q t r) (Sum.inl n) =
      ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) / scale t r n ^ 2 := by
  have hs : scale t r (n - 1) = scale t r n / r := by
    simp only [scale, zpow_sub_one₀ hr.ne']; ring
  have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
  unfold dVal
  rw [neighbor_eq]
  simp only [neighbors, Sum.elim_inl]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp),
    Finset.sum_image (fun x _ y _ h => by simpa using h)]
  simp only [lengths, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, min_eq_right (by omega : n - 1 ≤ n),
    min_eq_left (by omega : n ≤ n + 1), hs]
  have hq1 : ((q - 1 : ℕ) : ℝ) = q - 1 := by push_cast [hq]; ring
  rw [hq1]
  field_simp
  ring

private theorem dVal_branch {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ) (b : Fin (q - 1))
    (w : List (Fin q)) :
    dVal (graph q) (lengths q t r) (Sum.inr (n, b, w)) = (q + 1) / scale t r n ^ 2 := by
  have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
  have hp : lengths q t r (Sum.inr (n, b, w)) (parent q (Sum.inr (n, b, w))) = scale t r n := by
    cases w <;> simp [lengths, parent]
  unfold dVal
  rw [neighbor_eq]
  simp only [neighbors, Sum.elim_inr]
  have hnot : parent q (Sum.inr (n, b, w)) ∉
      Finset.univ.image fun c => (Sum.inr (n, b, c :: w) : Vtx q) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro c hc
    have hr := parent_rank (q := q) (Sum.inr (n, b, w))
    rw [← hc] at hr
    simp [rank] at hr
    omega
  rw [Finset.sum_insert hnot, Finset.sum_image (fun x _ y _ h => by simpa using h), hp]
  simp only [lengths, Sum.elim_inr, min_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private theorem residual_parent (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : Vtx q) :
    tEoM (graph q) (lengths q t r) x (parent q x) = 0 := by
  unfold tEoM
  rcases x with n | ⟨n, b, w⟩
  · have hs : scale t r n = r * scale t r (n - 1) := by
      simp only [scale, zpow_sub_one₀ hr.ne']; field_simp
    have hsn : 0 < scale t r (n - 1) := mul_pos ht (zpow_pos hr _)
    simp only [parent, Sum.elim_inl]
    rw [ratio_spine hq ht hr, ratio_spine hq ht hr]
    simp only [lengths, Sum.elim_inl, min_eq_right (by omega : n - 1 ≤ n)]
    rw [hs]
    have : (r + 1) ≠ 0 := by positivity
    field_simp
    ring
  · have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
    cases w
    · simp only [parent, Sum.elim_inr]
      rw [ratio_spine hq ht hr, ratio_branch t r ht hr]
      simp only [lengths, Sum.elim_inr, Sum.elim_inl]
      field_simp; ring
    · simp only [parent, Sum.elim_inr]
      rw [ratio_branch t r ht hr, ratio_branch t r ht hr]
      simp only [lengths, Sum.elim_inr, min_self]
      field_simp; ring

private theorem residuals (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (i j : Vtx q)
    (h : (graph q).Adj i j) : tEoM (graph q) (lengths q t r) i j = 0 := by
  rcases (graph_adj i j).mp h with h | h
  · rw [← h]; exact residual_parent hq ht hr i
  · have hz := residual_parent hq ht hr j
    rw [h] at hz
    unfold tEoM at hz ⊢
    rw [lengths_symm]
    linarith


variable (q) in
/-- Tree curvature of Huang et al. (4.10). -/
def curvature (ell : Vtx q → Vtx q → ℝ) (i j : Vtx q) : ℝ :=
  2 / ell i j ^ 2 * (1 / dVal (graph q) ell i + 1 / dVal (graph q) ell j) -
    (ratio (graph q) ell i + ratio (graph q) ell j) / ell i j

private theorem star_branch (t r : ℝ) (n : ℤ) (b : Fin (q - 1)) (w : List (Fin q)) (j : Vtx q)
    (h : (graph q).Adj (Sum.inr (n, b, w)) j) : lengths q t r (Sum.inr (n, b, w)) j = scale t r n := by
  rw [← mem_neighbors, neighbors] at h
  simp only [Sum.elim_inr, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with h | ⟨c, rfl⟩
  · subst h; cases w <;> simp [lengths, parent]
  · simp [lengths]

private theorem constant_iff {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (∃ c, ∀ i j, (graph q).Adj i j → lengths q t r i j = c) ↔ r = 1 := by
  constructor
  · rintro ⟨c, h⟩
    have h0 := h (Sum.inl 1) (Sum.inl 0) ((graph_adj _ _).mpr (Or.inl (by simp [parent])))
    have h1 := h (Sum.inl 0) (Sum.inl (-1)) ((graph_adj _ _).mpr (Or.inl (by simp [parent])))
    simp only [lengths, Sum.elim_inl, scale] at h0 h1
    norm_num at h0 h1
    have hpos : 0 < (r ^ 2 + 1) / (r + 1) * t := by positivity
    have : (r ^ 2 + 1) / (r + 1) * t * r⁻¹ = (r ^ 2 + 1) / (r + 1) * t := by
      have := h0.trans h1.symm; linarith
    have hrinv : r⁻¹ = 1 := by
      have := mul_left_cancel₀ hpos.ne' (this.trans (mul_one _).symm); exact this
    exact inv_eq_one.mp hrinv
  · rintro rfl
    refine ⟨t, fun i j _ => ?_⟩
    rcases i with n | ⟨n, b, w⟩ <;> rcases j with m | ⟨m, b', z⟩ <;>
      simp [lengths, scale] <;> norm_num

private theorem curvature_branch (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ)
    (b : Fin (q - 1)) (w : List (Fin q)) (c : Fin q) :
    curvature q (lengths q t r) (Sum.inr (n, b, w)) (Sum.inr (n, b, c :: w)) = 4 / (q + 1) - 2 := by
  have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
  unfold curvature
  rw [dVal_branch ht hr, dVal_branch ht hr, ratio_branch t r ht hr, ratio_branch t r ht hr]
  simp only [lengths, Sum.elim_inr, min_self]
  field_simp
  ring

private theorem curvature_attach (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ)
    (b : Fin (q - 1)) :
    curvature q (lengths q t r) (Sum.inl n) (Sum.inr (n, b, [])) =
      2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2 := by
  have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
  have hB : 0 < (q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1) := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have : 0 < (r + 1) ^ 2 / (r ^ 2 + 1) := by positivity
    linarith
  unfold curvature
  rw [dVal_spine hq ht hr, dVal_branch ht hr, ratio_spine hq ht hr, ratio_branch t r ht hr]
  simp only [lengths, Sum.elim_inl, Sum.elim_inr]
  field_simp
  ring

private theorem attach_gt_iff (hq : 1 ≤ q) {r : ℝ} (hr : 0 < r) :
    (4 / (q + 1) - 2 : ℝ) < 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2 ↔
      r ≠ 1 := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 0 < (r ^ 2 + 1) := by positivity
  have hB : 0 < (q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1) := by
    have : 0 < (r + 1) ^ 2 / (r ^ 2 + 1) := by positivity
    linarith
  have key : (4 / (q + 1) - 2 : ℝ) < 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2
      ↔ (q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1) < q + 1 := by
    rw [show (4 / (q + 1) - 2 : ℝ) = 2 / (q + 1) + 2 / (q + 1) - 2 by ring]
    constructor
    · intro h
      have : 2 / ((q : ℝ) + 1) < 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) := by linarith
      exact (div_lt_div_iff_of_pos_left (by norm_num) (by positivity) hB).mp this
    · intro h
      have := (div_lt_div_iff_of_pos_left (by norm_num : (0:ℝ) < 2)
        (by positivity : (0:ℝ) < q + 1) hB).mpr h
      linarith
  rw [key]
  constructor
  · intro h he; subst he; norm_num at h; linarith
  · intro h
    have hsq : 0 < (r - 1) ^ 2 := by
      have : r - 1 ≠ 0 := sub_ne_zero.mpr h
      positivity
    have : (r + 1) ^ 2 / (r ^ 2 + 1) < 2 := by
      rw [div_lt_iff₀ h1]; nlinarith
    linarith


/-- Theorem 1 and Corollaries 2 and 6 of Ma and Zhang on Conjectures 3 and 4 of Huang, Stoica,
Xia and Zhong: for every `q ≥ 2`, `t > 0` and `r > 0`, the graph is a tree with every degree
`q + 1`; the geometric-spine lengths are symmetric, positive and solve the tree equations; the
spine edge `vₙvₙ₊₁` has length `a sₙ` and the vertex ratio at `vₙ` is `sₙ`; at every branch vertex the
ratio is `sₙ` and every incident length is `sₙ`; the solution is constant exactly when `r = 1`;
inside a branch the curvature is `4/(q+1) - 2`, on an attachment edge it is `2/B + 2/(q+1) - 2`
with `B = q - 1 + (r+1)²/(r²+1)`, and the second exceeds the first exactly when `r ≠ 1`. -/
theorem result (q : ℕ) (hq : 2 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (graph q).IsTree ∧ (∀ i, (graph q).degree i = q + 1) ∧
    (∀ i j, (graph q).Adj i j → lengths q t r i j = lengths q t r j i ∧ 0 < lengths q t r i j ∧
      tEoM (graph q) (lengths q t r) i j = 0) ∧
    (∀ n : ℤ, (graph q).Adj (Sum.inl n) (Sum.inl (n + 1)) ∧
      lengths q t r (Sum.inl n) (Sum.inl (n + 1)) = (r ^ 2 + 1) / (r + 1) * scale t r n ∧
      ratio (graph q) (lengths q t r) (Sum.inl n) = scale t r n) ∧
    (∀ (n : ℤ) (b : Fin (q - 1)) (w : List (Fin q)),
      ratio (graph q) (lengths q t r) (Sum.inr (n, b, w)) = scale t r n ∧
      ∀ j, (graph q).Adj (Sum.inr (n, b, w)) j → lengths q t r (Sum.inr (n, b, w)) j = scale t r n) ∧
    ((∃ c, ∀ i j, (graph q).Adj i j → lengths q t r i j = c) ↔ r = 1) ∧
    (∀ (n : ℤ) (b : Fin (q - 1)) (w : List (Fin q)) (c : Fin q),
      (graph q).Adj (Sum.inr (n, b, w)) (Sum.inr (n, b, c :: w)) ∧
      curvature q (lengths q t r) (Sum.inr (n, b, w)) (Sum.inr (n, b, c :: w)) = 4 / (q + 1) - 2) ∧
    (∀ (n : ℤ) (b : Fin (q - 1)), (graph q).Adj (Sum.inl n) (Sum.inr (n, b, [])) ∧
      curvature q (lengths q t r) (Sum.inl n) (Sum.inr (n, b, [])) =
        2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2) ∧
    ((4 / (q + 1) - 2 : ℝ) < 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2 ↔
      r ≠ 1) := by
  have hq1 : 1 ≤ q := by omega
  refine ⟨graph_tree, graph_degree hq1, fun i j h => ⟨lengths_symm t r i j, lengths_pos ht hr i j,
    residuals hq1 ht hr i j h⟩, fun n => ⟨(graph_adj _ _).mpr (Or.inr (by simp [parent])), ?_,
    ratio_spine hq1 ht hr n⟩, fun n b w => ⟨ratio_branch t r ht hr n b w,
    star_branch t r n b w⟩, constant_iff ht hr, fun n b w c => ⟨(graph_adj _ _).mpr
    (Or.inr rfl), curvature_branch hq1 ht hr n b w c⟩, fun n b => ⟨(graph_adj _ _).mpr
    (Or.inr rfl), curvature_attach hq1 ht hr n b⟩, attach_gt_iff hq1 hr⟩
  simp [lengths]


end D5.S3.Geometry.DiscreteGravity.GeometricSpineSolutions
