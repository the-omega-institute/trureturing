/- GID: D5/S3/Geometry/DiscreteGravity/GeometricSpineSolutions
   generality: G
   mirror-B: D5/B/S3/Geometry/DiscreteGravity/GeometricSpineSolutions
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Geometric-spine solutions of the tree equations on every regular tree, equal stars off the spine, curvature. -/

import D5.S3.Geometry.DiscreteGravity.TreeEquationsNonconstantRefutation

/-! The infinite `(q + 1)`-regular tree `T_q`, realized on `ℤ ⊕ (ℤ × Fin (q - 1) × List (Fin q))`
(a bi-infinite spine and `q - 1` rooted `q`-ary branches at each spine vertex), the tree equations
of Huang, Stoica, Xia and Zhong on it, and three families of solutions.

* Extension of line solutions: for positive spine lengths `L`, giving every branch edge at `n`
  the line ratio `R_n` preserves all ratios, and the tree equations hold exactly when the line
  equations hold.
* Two-choice spines: successive ratios `L (n - 1) / L n ∈ {2, 3}` give line solutions; with any
  `L₀` they define a unique positive spine, nonconstant, geometric exactly when the ratio is
  constant.
* Geometric spines: lengths `a sₙ` on the spine and `sₙ` on branches, `sₙ = t rⁿ`,
  `a = (r² + 1)/(r + 1)`; constant exactly when `r = 1`; tree curvature `4/(q+1) - 2` inside
  branches and `2/B + 2/(q+1) - 2` on attachment edges, constant exactly when `r = 1`.

admission_basis: escape-witness. Escape witnesses (content): graph_degree, mem_neighbors,
graph_connected, graph_acyclic (realization of `T_q`); gratio_spine (the cancellation `c = R d`
after attaching branches), gratio_branch, gresidual_parent, gsolves_iff; two_three_residual (the
line equations for ratios 2 and 3); recLengths_spec, recLengths_unique; lineRatio_geom and
residuals (the geometric line); dVal_spine, dVal_branch, constant_iff, curvature_branch,
curvature_attach, attach_gt_iff, curvature_one, curvature_constant_iff; two_choice_pos,
two_choice_nonconstant. Consumed bind-only helpers: parent_rank, graph_adj, neighbor_eq,
graph_tree, lineRatio_pos, spine_lengths_symm, spine_lengths_pos, gstar_branch, lengths_symm,
lengths_pos, lengths_eq, ratio_spine, ratio_branch, star_branch, attach_eq_iff,
two_choice_lengths, two_choice_geometric. -/

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

/-! ### Extension of a line solution to `T_q` -/


/-- The line ratio at `n` for spine edge lengths `L` (edge `n-1 — n` has length `L (n-1)`). -/
def lineRatio (L : ℤ → ℝ) (n : ℤ) : ℝ :=
  (1 / L (n - 1) + 1 / L n) / (1 / L (n - 1) ^ 2 + 1 / L n ^ 2)

/-- The line residual on the edge `n-1 — n`. -/
def lineResidual (L : ℤ → ℝ) (n : ℤ) : ℝ :=
  (lineRatio L n ^ 2 + lineRatio L (n - 1) ^ 2) / L (n - 1) - lineRatio L n - lineRatio L (n - 1)

variable (q) in
/-- Spine lengths `L` on the line and the line ratio `R_n` on every edge of the branches at `n`. -/
def spineLengths (L : ℤ → ℝ) : Vtx q → Vtx q → ℝ :=
  Sum.elim
    (fun n => Sum.elim (fun m => L (min n m)) (fun p => lineRatio L p.1))
    (fun p => Sum.elim (fun _ => lineRatio L p.1) (fun p' => lineRatio L (min p.1 p'.1)))

private theorem lineRatio_pos {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) (n : ℤ) : 0 < lineRatio L n := by
  have := hL n; have := hL (n - 1); unfold lineRatio; positivity

private theorem spine_lengths_symm (L : ℤ → ℝ) (i j : Vtx q) : spineLengths q L i j = spineLengths q L j i := by
  rcases i with n | ⟨n, b, w⟩ <;> rcases j with m | ⟨m, b', z⟩ <;> simp [spineLengths, min_comm]

private theorem spine_lengths_pos {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) (i j : Vtx q) :
    0 < spineLengths q L i j := by
  rcases i with n | ⟨n, b, w⟩ <;> rcases j with m | ⟨m, b', z⟩ <;>
    simp only [spineLengths, Sum.elim_inl, Sum.elim_inr]
  · exact hL _
  all_goals exact lineRatio_pos hL _

private theorem gratio_spine (hq : 1 ≤ q) {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) (n : ℤ) :
    ratio (graph q) (spineLengths q L) (Sum.inl n) = lineRatio L n := by
  have h1 := hL n; have h0 := hL (n - 1); have hρ := lineRatio_pos hL n
  unfold ratio cVal dVal
  rw [neighbor_eq]
  simp only [neighbors, Sum.elim_inl]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp),
    Finset.sum_image (fun x _ y _ h => by simpa using h),
    Finset.sum_image (fun x _ y _ h => by simpa using h)]
  simp only [spineLengths, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, min_eq_right (by omega : n - 1 ≤ n),
    min_eq_left (by omega : n ≤ n + 1)]
  have hq1 : ((q - 1 : ℕ) : ℝ) = q - 1 := by push_cast [hq]; ring
  rw [hq1]
  have hq0 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hc : 1 / L (n - 1) + 1 / L n = lineRatio L n * (1 / L (n - 1) ^ 2 + 1 / L n ^ 2) := by
    unfold lineRatio; field_simp
  generalize lineRatio L n = ρ at hρ hc ⊢
  have hden : 0 < 1 / L (n - 1) ^ 2 + (1 / L n ^ 2 + (q - 1) * (1 / ρ ^ 2)) := by positivity
  rw [div_eq_iff hden.ne']
  have : 1 / L (n - 1) + (1 / L n + (q - 1) * (1 / ρ)) =
      (1 / L (n - 1) + 1 / L n) + (q - 1) * (1 / ρ) := by ring
  rw [this, hc]
  field_simp
  ring

private theorem gratio_branch {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) (n : ℤ) (b : Fin (q - 1))
    (w : List (Fin q)) :
    ratio (graph q) (spineLengths q L) (Sum.inr (n, b, w)) = lineRatio L n := by
  have hρ := lineRatio_pos hL n
  have hp : spineLengths q L (Sum.inr (n, b, w)) (parent q (Sum.inr (n, b, w))) = lineRatio L n := by
    cases w <;> simp [spineLengths, parent]
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
  simp only [spineLengths, Sum.elim_inr, min_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

private theorem gresidual_parent (hq : 1 ≤ q) {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) (x : Vtx q) :
    tEoM (graph q) (spineLengths q L) x (parent q x) =
      Sum.elim (fun n => lineResidual L n) (fun _ => 0) x := by
  unfold tEoM
  rcases x with n | ⟨n, b, w⟩
  · simp only [parent, Sum.elim_inl]
    rw [gratio_spine hq hL, gratio_spine hq hL]
    simp only [spineLengths, Sum.elim_inl, min_eq_right (by omega : n - 1 ≤ n), lineResidual]
    ring
  · have hρ := lineRatio_pos hL n
    cases w
    · simp only [parent, Sum.elim_inr]
      rw [gratio_spine hq hL, gratio_branch hL]
      simp only [spineLengths, Sum.elim_inr, Sum.elim_inl]
      field_simp; ring
    · simp only [parent, Sum.elim_inr]
      rw [gratio_branch hL, gratio_branch hL]
      simp only [spineLengths, Sum.elim_inr, min_self]
      field_simp; ring

/-- The extension solves the tree equations exactly when the line solves its own. -/
private theorem gsolves_iff (hq : 1 ≤ q) {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) :
    (∀ i j, (graph q).Adj i j → tEoM (graph q) (spineLengths q L) i j = 0) ↔
      ∀ n, lineResidual L n = 0 := by
  constructor
  · intro h n
    have := h (Sum.inl n) (parent q (Sum.inl n)) ((graph_adj _ _).mpr (Or.inl rfl))
    rw [gresidual_parent hq hL] at this
    simpa using this
  · intro h i j hij
    have key : ∀ x, tEoM (graph q) (spineLengths q L) x (parent q x) = 0 := fun x => by
      rw [gresidual_parent hq hL]; rcases x with n | p
      · exact h n
      · rfl
    rcases (graph_adj i j).mp hij with e | e
    · rw [← e]; exact key i
    · have hz := key j
      rw [e] at hz
      unfold tEoM at hz ⊢
      rw [spine_lengths_symm]
      linarith

private theorem gstar_branch (L : ℤ → ℝ) (n : ℤ) (b : Fin (q - 1)) (w : List (Fin q)) (j : Vtx q)
    (h : (graph q).Adj (Sum.inr (n, b, w)) j) :
    spineLengths q L (Sum.inr (n, b, w)) j = lineRatio L n := by
  rw [← mem_neighbors, neighbors] at h
  simp only [Sum.elim_inr, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with h | ⟨c, rfl⟩
  · subst h; cases w <;> simp [spineLengths, parent]
  · simp [spineLengths]

/-- Theorem 10 of Huang et al.: ratios `2` or `3` give line solutions. -/
private theorem two_three_residual {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) (β : ℤ → ℝ)
    (hβ : ∀ n, β n = 2 ∨ β n = 3) (hrec : ∀ n, L (n - 1) = β n * L n) (n : ℤ) :
    lineResidual L n = 0 := by
  have h1 := hL n; have h0 := hL (n - 1)
  have hn : lineRatio L n = L (n - 1) * ((β n + 1) / (β n ^ 2 + 1)) := by
    have hb : 0 < β n := by rcases hβ n with h | h <;> rw [h] <;> norm_num
    unfold lineRatio; rw [hrec n]; field_simp; ring
  have hm : lineRatio L (n - 1) = L (n - 1) * (6 / 5) := by
    unfold lineRatio
    rw [show n - 1 - 1 = n - 1 - 1 from rfl, hrec (n - 1)]
    rcases hβ (n - 1) with h | h <;> rw [h] <;> field_simp <;> ring
  unfold lineResidual
  rw [hn, hm]
  rcases hβ n with h | h <;> rw [h] <;> field_simp <;> ring

/-- The forward recursion from `L₀`. -/
private def fwd (β : ℤ → ℝ) (L0 : ℝ) : ℕ → ℝ
  | 0 => L0
  | k + 1 => fwd β L0 k / β (k + 1)

private def bwd (β : ℤ → ℝ) (L0 : ℝ) : ℕ → ℝ
  | 0 => L0
  | k + 1 => β (-(k : ℤ)) * bwd β L0 k

private def recLengths (β : ℤ → ℝ) (L0 : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then fwd β L0 n.toNat else bwd β L0 (-n).toNat

private theorem recLengths_spec (β : ℤ → ℝ) (hβ : ∀ n, 0 < β n) {L0 : ℝ} (h0 : 0 < L0) :
    recLengths β L0 0 = L0 ∧ (∀ n, 0 < recLengths β L0 n) ∧
      ∀ n, recLengths β L0 (n - 1) = β n * recLengths β L0 n := by
  have pf : ∀ k, 0 < fwd β L0 k := by
    intro k; induction k with
    | zero => exact h0
    | succ k ih => exact div_pos ih (hβ _)
  have pb : ∀ k, 0 < bwd β L0 k := by
    intro k; induction k with
    | zero => exact h0
    | succ k ih => exact mul_pos (hβ _) ih
  refine ⟨by simp [recLengths, fwd], fun n => ?_, fun n => ?_⟩
  · unfold recLengths; split_ifs
    · exact pf _
    · exact pb _
  · unfold recLengths
    rcases le_or_gt 1 n with hn | hn
    · rw [if_pos (by omega), if_pos (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
      rw [show ((k : ℤ) + 1 - 1).toNat = k by omega, show ((k : ℤ) + 1).toNat = k + 1 by omega]
      simp only [fwd]
      have := hβ ((k : ℤ) + 1)
      push_cast
      field_simp
    · rw [if_neg (by omega)]
      by_cases h0n : n = 0
      · subst h0n
        simp [fwd, bwd]
      · rw [if_neg (by omega)]
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
        rw [show (-(-(k : ℤ) - 1)).toNat = k + 1 by omega, show (-(-(k : ℤ))).toNat = k by omega]
        simp only [bwd]

private theorem recLengths_unique {β : ℤ → ℝ} {L M : ℤ → ℝ} (h0 : L 0 = M 0)
    (hL : ∀ n, L (n - 1) = β n * L n) (hM : ∀ n, M (n - 1) = β n * M n)
    (hβ : ∀ n, β n ≠ 0) : L = M := by
  funext n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ k ih =>
    have a := hL ((k : ℤ) + 1); have b := hM ((k : ℤ) + 1)
    simp only [add_sub_cancel_right] at a b
    rw [ih] at a
    exact mul_left_cancel₀ (hβ _) (a.symm.trans b)
  | pred k ih =>
    have a := hL (-(k : ℤ)); have b := hM (-(k : ℤ))
    rw [a, b, ih]


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

private theorem lineRatio_geom {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ) :
    lineRatio (fun m => (r ^ 2 + 1) / (r + 1) * scale t r m) n = scale t r n := by
  have hs : scale t r (n - 1) = scale t r n / r := by
    simp only [scale, zpow_sub_one₀ hr.ne']; ring
  have hsn : 0 < scale t r n := mul_pos ht (zpow_pos hr n)
  unfold lineRatio
  beta_reduce
  rw [hs]
  have : (r + 1) ≠ 0 := by positivity
  have : (r ^ 2 + 1) ≠ 0 := by positivity
  field_simp

private theorem lengths_eq {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    lengths q t r = spineLengths q (fun m => (r ^ 2 + 1) / (r + 1) * scale t r m) := by
  funext i j
  rcases i with n | ⟨n, b, w⟩ <;> rcases j with m | ⟨m, b', z⟩ <;>
    simp [lengths, spineLengths, lineRatio_geom ht hr]

private theorem ratio_spine (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ) :
    ratio (graph q) (lengths q t r) (Sum.inl n) = scale t r n := by
  have hL : ∀ m, 0 < (r ^ 2 + 1) / (r + 1) * scale t r m := fun m =>
    mul_pos (by positivity) (mul_pos ht (zpow_pos hr m))
  rw [lengths_eq ht hr, gratio_spine hq hL, lineRatio_geom ht hr]

private theorem ratio_branch (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (n : ℤ) (b : Fin (q - 1))
    (w : List (Fin q)) :
    ratio (graph q) (lengths q t r) (Sum.inr (n, b, w)) = scale t r n := by
  have hL : ∀ m, 0 < (r ^ 2 + 1) / (r + 1) * scale t r m := fun m =>
    mul_pos (by positivity) (mul_pos ht (zpow_pos hr m))
  rw [lengths_eq ht hr, gratio_branch hL, lineRatio_geom ht hr]

private theorem residuals (hq : 1 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (i j : Vtx q)
    (h : (graph q).Adj i j) : tEoM (graph q) (lengths q t r) i j = 0 := by
  have hL : ∀ m, 0 < (r ^ 2 + 1) / (r + 1) * scale t r m := fun m =>
    mul_pos (by positivity) (mul_pos ht (zpow_pos hr m))
  rw [lengths_eq ht hr]
  refine (gsolves_iff hq hL).mpr (fun n => ?_) i j h
  have hs : scale t r n = r * scale t r (n - 1) := by
    simp only [scale, zpow_sub_one₀ hr.ne']; field_simp
  have hsn : 0 < scale t r (n - 1) := mul_pos ht (zpow_pos hr _)
  unfold lineResidual
  rw [lineRatio_geom ht hr, lineRatio_geom ht hr, hs]
  have : (r + 1) ≠ 0 := by positivity
  field_simp
  ring

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

variable (q) in
/-- Tree curvature of Huang et al. (4.10). -/
def curvature (ell : Vtx q → Vtx q → ℝ) (i j : Vtx q) : ℝ :=
  2 / ell i j ^ 2 * (1 / dVal (graph q) ell i + 1 / dVal (graph q) ell j) -
    (ratio (graph q) ell i + ratio (graph q) ell j) / ell i j

private theorem star_branch {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (n : ℤ) (b : Fin (q - 1))
    (w : List (Fin q)) (j : Vtx q) (h : (graph q).Adj (Sum.inr (n, b, w)) j) :
    lengths q t r (Sum.inr (n, b, w)) j = scale t r n := by
  rw [lengths_eq ht hr, gstar_branch _ n b w j h, lineRatio_geom ht hr]

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
      simp [lengths, scale]

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


private theorem curvature_one (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t) (i j : Vtx q) :
    curvature q (lengths q t 1) i j = 4 / (q + 1) - 2 := by
  have hl : ∀ a b : Vtx q, lengths q t 1 a b = t := fun a b => by
    rcases a with n | ⟨n, b, w⟩ <;> rcases b with m | ⟨m, b', z⟩ <;> simp [lengths, scale]
  have hd : ∀ a : Vtx q, dVal (graph q) (lengths q t 1) a = (q + 1) / t ^ 2 := fun a => by
    rcases a with n | ⟨n, b, w⟩
    · rw [dVal_spine hq ht one_pos]; simp [scale]; norm_num; ring
    · rw [dVal_branch ht one_pos]; simp [scale]
  have hR : ∀ a : Vtx q, ratio (graph q) (lengths q t 1) a = t := fun a => by
    rcases a with n | ⟨n, b, w⟩
    · rw [ratio_spine hq ht one_pos]; simp [scale]
    · rw [ratio_branch t 1 ht one_pos]; simp [scale]
  unfold curvature
  rw [hl, hd, hd, hR, hR]
  have : (0 : ℝ) < q + 1 := by positivity
  field_simp
  ring

private theorem curvature_constant_iff (hq : 2 ≤ q) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (∃ c, ∀ i j, (graph q).Adj i j → curvature q (lengths q t r) i j = c) ↔ r = 1 := by
  constructor
  · rintro ⟨c, h⟩
    have b0 : Fin (q - 1) := ⟨0, by omega⟩
    have c0 : Fin q := ⟨0, by omega⟩
    have e1 := h (Sum.inr (0, b0, [])) (Sum.inr (0, b0, [c0])) ((graph_adj _ _).mpr (Or.inr rfl))
    have e2 := h (Sum.inl 0) (Sum.inr (0, b0, [])) ((graph_adj _ _).mpr (Or.inr rfl))
    rw [curvature_branch (by omega) ht hr] at e1
    rw [curvature_attach (by omega) ht hr] at e2
    by_contra hne
    have := (attach_gt_iff (q := q) (by omega) hr).mpr hne
    linarith
  · rintro rfl
    exact ⟨_, fun i j _ => curvature_one (by omega) ht i j⟩

private theorem attach_eq_iff (hq : 1 ≤ q) {r : ℝ} (hr : 0 < r) :
    (4 / (q + 1) - 2 : ℝ) ≤ 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2 ∧
    ((4 / (q + 1) - 2 : ℝ) = 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2 ↔
      r = 1) := by
  have hone : (4 / (q + 1) - 2 : ℝ) =
      2 / ((q - 1 : ℝ) + (1 + 1) ^ 2 / (1 ^ 2 + 1)) + 2 / (q + 1) - 2 := by
    have : (0 : ℝ) < q + 1 := by positivity
    norm_num
    ring
  have hgt := attach_gt_iff (q := q) hq hr
  refine ⟨?_, ⟨fun h => ?_, fun h => h ▸ hone⟩⟩
  · by_cases h : r = 1
    · subst h; exact hone.le
    · exact (hgt.mpr h).le
  · by_contra hne
    exact (hgt.mpr hne).ne h

/-- The two-choice line lengths: for `β n ∈ {2, 3}` and `L₀ > 0` there is exactly one sequence
with `L 0 = L₀` and `L (n - 1) = β n · L n`; it is positive. -/
private theorem two_choice_lengths (β : ℤ → ℝ) (hβ : ∀ n, β n = 2 ∨ β n = 3) {L0 : ℝ}
    (h0 : 0 < L0) :
    ∃! L : ℤ → ℝ, L 0 = L0 ∧ ∀ n, L (n - 1) = β n * L n := by
  have hpos : ∀ n, 0 < β n := fun n => by rcases hβ n with h | h <;> rw [h] <;> norm_num
  obtain ⟨e0, -, erec⟩ := recLengths_spec β hpos h0
  exact ⟨recLengths β L0, ⟨e0, erec⟩, fun M ⟨m0, mrec⟩ =>
    recLengths_unique (m0.trans e0.symm) mrec erec (fun n => (hpos n).ne')⟩

private theorem two_choice_pos {β : ℤ → ℝ} (hβ : ∀ n, β n = 2 ∨ β n = 3) {L : ℤ → ℝ}
    (h0 : 0 < L 0) (hrec : ∀ n, L (n - 1) = β n * L n) : ∀ n, 0 < L n := by
  have hpos : ∀ n, 0 < β n := fun n => by rcases hβ n with h | h <;> rw [h] <;> norm_num
  intro n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ k ih =>
    have := hrec ((k : ℤ) + 1)
    simp only [add_sub_cancel_right] at this
    rw [this] at ih
    exact pos_of_mul_pos_right ih (hpos _).le
  | pred k ih =>
    rw [hrec]; exact mul_pos (hpos _) ih

private theorem two_choice_nonconstant {β : ℤ → ℝ} (hβ : ∀ n, β n = 2 ∨ β n = 3)
    {L : ℤ → ℝ} (hL : ∀ n, 0 < L n) (hrec : ∀ n, L (n - 1) = β n * L n) :
    ¬ ∃ c, ∀ i j, (graph q).Adj i j → spineLengths q L i j = c := by
  rintro ⟨c, h⟩
  have e1 := h (Sum.inl 1) (Sum.inl 0) ((graph_adj _ _).mpr (Or.inl (by simp [parent])))
  have e0 := h (Sum.inl 0) (Sum.inl (-1)) ((graph_adj _ _).mpr (Or.inl (by simp [parent])))
  simp only [spineLengths, Sum.elim_inl] at e1 e0
  norm_num at e1 e0
  have hr := hrec 0
  norm_num at hr
  have h1 := hL 0
  rcases hβ 0 with hb | hb <;> rw [hb] at hr <;> linarith

private theorem two_choice_geometric {β : ℤ → ℝ} {L : ℤ → ℝ} (hL : ∀ n, 0 < L n)
    (hrec : ∀ n, L (n - 1) = β n * L n) :
    (∃ ρ, ∀ n, L (n - 1) = ρ * L n) ↔ ∃ c, ∀ n, β n = c := by
  constructor
  · rintro ⟨ρ, h⟩
    exact ⟨ρ, fun n => mul_right_cancel₀ (hL n).ne' ((hrec n).symm.trans (h n))⟩
  · rintro ⟨c, h⟩
    exact ⟨c, fun n => by rw [hrec, h]⟩

/-- Theorem 1, Lemma 3 (for the line), and Corollaries 2, 4 and 6 of Ma and Zhang on
Conjectures 3 and 4 of Huang, Stoica, Xia and Zhong, for every `q ≥ 2`: the graph is a tree with
every degree `q + 1`. Geometric spines (`t, r > 0`): symmetric positive solutions with spine edges
`a sₙ`, ratio `sₙ` on the spine and on the branches at `n`, every incident length `sₙ` at branch
vertices, constant exactly when `r = 1`; curvature `4/(q+1) - 2` inside branches and
`2/B + 2/(q+1) - 2` on attachment edges, `B = q - 1 + (r+1)²/(r²+1)`, the second at least the
first with equality exactly when `r = 1`, and the curvature is constant exactly when `r = 1`. Any
positive spine `L` extends with branch lengths the line ratio, preserving ratios, and the tree
equations hold exactly when the line equations hold. For `β n ∈ {2, 3}` and `L₀ > 0` there is a
unique spine with `L 0 = L₀` and `L (n - 1) = β n L n`; every such spine is positive, solves
the tree equations after extension, is nonconstant, and is geometric exactly when `β` is
constant. -/
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
    ((4 / (q + 1) - 2 : ℝ) ≤ 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2 ∧
      ((4 / (q + 1) - 2 : ℝ) = 2 / ((q - 1 : ℝ) + (r + 1) ^ 2 / (r ^ 2 + 1)) + 2 / (q + 1) - 2 ↔
        r = 1)) ∧
    ((∃ c, ∀ i j, (graph q).Adj i j → curvature q (lengths q t r) i j = c) ↔ r = 1) ∧
    (∀ L : ℤ → ℝ, (∀ n, 0 < L n) →
      ((∀ i j, (graph q).Adj i j → tEoM (graph q) (spineLengths q L) i j = 0) ↔
        ∀ n, lineResidual L n = 0) ∧
      (∀ n, (graph q).Adj (Sum.inl (n - 1)) (Sum.inl n) ∧
        spineLengths q L (Sum.inl (n - 1)) (Sum.inl n) = L (n - 1) ∧
        ratio (graph q) (spineLengths q L) (Sum.inl n) = lineRatio L n) ∧
      ∀ (n : ℤ) (b : Fin (q - 1)) (w : List (Fin q)),
        ratio (graph q) (spineLengths q L) (Sum.inr (n, b, w)) = lineRatio L n ∧
        ∀ j, (graph q).Adj (Sum.inr (n, b, w)) j →
          spineLengths q L (Sum.inr (n, b, w)) j = lineRatio L n) ∧
    (∀ β : ℤ → ℝ, (∀ n, β n = 2 ∨ β n = 3) →
      (∀ L0 : ℝ, 0 < L0 → ∃! L : ℤ → ℝ, L 0 = L0 ∧ ∀ n, L (n - 1) = β n * L n) ∧
      ∀ L : ℤ → ℝ, 0 < L 0 → (∀ n, L (n - 1) = β n * L n) →
        (∀ n, 0 < L n) ∧
        (∀ i j, (graph q).Adj i j → tEoM (graph q) (spineLengths q L) i j = 0) ∧
        ¬ (∃ c, ∀ i j, (graph q).Adj i j → spineLengths q L i j = c) ∧
        ((∃ ρ, ∀ n, L (n - 1) = ρ * L n) ↔ ∃ c, ∀ n, β n = c)) := by
  have hq1 : 1 ≤ q := by omega
  refine ⟨graph_tree, graph_degree hq1, fun i j h => ⟨lengths_symm t r i j, lengths_pos ht hr i j,
    residuals hq1 ht hr i j h⟩, fun n => ⟨(graph_adj _ _).mpr (Or.inr (by simp [parent])), ?_,
    ratio_spine hq1 ht hr n⟩, fun n b w => ⟨ratio_branch t r ht hr n b w,
    star_branch ht hr n b w⟩, constant_iff ht hr, fun n b w c => ⟨(graph_adj _ _).mpr
    (Or.inr rfl), curvature_branch hq1 ht hr n b w c⟩, fun n b => ⟨(graph_adj _ _).mpr
    (Or.inr rfl), curvature_attach hq1 ht hr n b⟩, attach_eq_iff hq1 hr,
    curvature_constant_iff hq ht hr, fun L hL => ⟨gsolves_iff hq1 hL, fun n =>
    ⟨(graph_adj _ _).mpr (Or.inr rfl), by simp [spineLengths], gratio_spine hq1 hL n⟩,
    fun n b w => ⟨gratio_branch hL n b w, gstar_branch L n b w⟩⟩,
    fun β hβ => ⟨fun L0 h0 => two_choice_lengths β hβ h0, fun L h0 hrec => ?_⟩⟩
  · simp [lengths]
  · have hL := two_choice_pos hβ h0 hrec
    exact ⟨hL, (gsolves_iff hq1 hL).mpr (two_three_residual hL β hβ hrec),
      two_choice_nonconstant (q := q) hβ hL hrec, two_choice_geometric hL hrec⟩

end D5.S3.Geometry.DiscreteGravity.GeometricSpineSolutions
