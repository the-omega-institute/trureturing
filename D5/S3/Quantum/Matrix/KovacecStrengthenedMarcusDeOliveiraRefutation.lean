/- GID: D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.claim; result=D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.result; claim=D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.claim
   digest: A rational orthogonal three-by-three matrix refutes Kovačec Conjecture 7. -/

/-
proof_shape: q_unitary: bind-only; consumers: d_mem_detRange
proof_shape: determinant_exact: bind-only; consumers: d_mem_detRange
proof_shape: d_mem_detRange: bind-only; consumers: result
proof_shape: continuous_L: bind-only; consumers: closed_P, open_O, continuous_gamma
proof_shape: continuous_U: bind-only; consumers: closed_P, open_O, continuous_gamma
proof_shape: l_piece1: bind-only; consumers: endpoint_values, L_lt_U, bdry_subset_graph
proof_shape: l_piece2: bind-only; consumers: L_lt_U, bdry_subset_graph
proof_shape: l_piece3: bind-only; consumers: L_lt_U, bdry_subset_graph
proof_shape: l_piece4: bind-only; consumers: endpoint_values, L_lt_U, d_not_mem_P, bdry_subset_graph
proof_shape: u_piece1: bind-only; consumers: endpoint_values, L_lt_U, bdry_subset_graph
proof_shape: u_piece2: bind-only; consumers: endpoint_values, L_lt_U, bdry_subset_graph
proof_shape: endpoint_values: bind-only; consumers: L_le_U, P_diff_O_subset_bdry, branches_agree
proof_shape: L_lt_U: bind-only; consumers: L_le_U, injective_gamma
proof_shape: L_le_U: bind-only; consumers: bdry_subset_P
proof_shape: closed_P: bind-only; consumers: frontier_P, component_subset_P, component_closure_subset_P, inside_not_exterior
proof_shape: open_O: bind-only; consumers: frontier_P, component_subset_P
proof_shape: O_subset_P: bind-only; consumers: frontier_P, component_subset_P
proof_shape: bdry_subset_P: bind-only; consumers: bdry_subset_frontier
proof_shape: d_not_mem_P: bind-only; consumers: result
proof_shape: shift_dist: bind-only; consumers: bdry_subset_frontier, outside_exterior
proof_shape: bdry_subset_frontier: content; consumers: frontier_P
proof_shape: P_diff_O_subset_bdry: bind-only; consumers: frontier_P
proof_shape: frontier_P: content; consumers: frontier_subset_graph, jordan_frontier_P, result
proof_shape: bounded_P: bind-only; consumers: component_bounded, inside_not_exterior
proof_shape: component_subset_P: bind-only; consumers: component_bounded, component_closure_subset_P
proof_shape: component_bounded: bind-only; consumers: result
proof_shape: component_closure_subset_P: bind-only; consumers: result
proof_shape: perm_exhaustive: bind-only; consumers: graph_eq_edges
proof_shape: sigma_values: bind-only; consumers: listed_edge_graph, graph_eq_edges
proof_shape: edge_exhaustive: bind-only; consumers: graph_eq_edges
proof_shape: listed_edge_graph: bind-only; consumers: graph_eq_edges, bdry_subset_graph
proof_shape: graph_eq_edges: bind-only; consumers: graph_subset_P
proof_shape: segment_on_line: bind-only; consumers: bdry_subset_graph
proof_shape: edge_subset_P: bind-only; consumers: graph_subset_P
proof_shape: graph_subset_P: bind-only; consumers: exterior_eq
proof_shape: bdry_subset_graph: bind-only; consumers: frontier_subset_graph
proof_shape: frontier_subset_graph: content; consumers: exterior_eq
proof_shape: circle_sq: bind-only; consumers: equator, injective_gamma
proof_shape: circle_re_bounds: bind-only; consumers: xcoord_bounds
proof_shape: equator: bind-only; consumers: branches_agree
proof_shape: xcoord_bounds: bind-only; consumers: injective_gamma, gamma_mem_bdry
proof_shape: branches_agree: bind-only; consumers: continuous_gamma, gamma_range
proof_shape: continuous_xcoord: bind-only; consumers: continuous_gamma
proof_shape: continuous_gamma: bind-only; consumers: jordan_frontier_P
proof_shape: injective_gamma: bind-only; consumers: jordan_frontier_P
proof_shape: gamma_mem_bdry: bind-only; consumers: gamma_range
proof_shape: circle_of_coords: bind-only; consumers: gamma_range
proof_shape: gamma_range: content; consumers: jordan_frontier_P
proof_shape: jordan_frontier_P: content; consumers: result
proof_shape: real_shift_dist: bind-only; consumers: outside_exterior
proof_shape: outside_exterior: content; consumers: exterior_eq
proof_shape: inside_not_exterior: bind-only; consumers: exterior_eq
proof_shape: exterior_eq: content; consumers: exterior_frontier
proof_shape: exterior_frontier: content; consumers: result
proof_shape: zero_mem_O: bind-only; consumers: result
proof_shape: result: content; consumers: none
escape_witness: bdry_subset_frontier: bdry_subset_frontier (explicit exterior approximants)
escape_witness: frontier_P: bdry_subset_frontier
escape_witness: frontier_subset_graph: bdry_subset_frontier
escape_witness: gamma_range: gamma_range (explicit circle preimages of boundary points)
escape_witness: jordan_frontier_P: gamma_range
escape_witness: outside_exterior: outside_exterior (unobstructed segments of every positive length)
escape_witness: exterior_eq: outside_exterior
escape_witness: exterior_frontier: outside_exterior
escape_witness: result: gamma_range
admission_basis: open-problem-resolution (#17803; Refuted)
Direct frozen dependencies:
Module GID: D5/S3/Quantum/Matrix/ProjectionAMGMRefutation
Declaration: D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.sixPerms
Declaration statement_id: sha256:f2a4e772c640b3961fe71f88e8d792975fcdb9021ba693f05269d3c7c0d9f592
Declaration: D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.sixPerms_univ
Declaration statement_id: sha256:b2ca8ba0a7f91c5ea31019c45c9f482d9dbd6de711cad71cf40c106fe0679323
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The six public definitions state the expressions in #17803, with finite multisets represented by Fin-indexed functions.
The bounded-region assertion ranges over every bounded component of the complement of the exterior frontier.
The original convex-hull Marcus-de Oliveira conjecture is outside the conclusion.
-/

import D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
namespace D5.S3.Quantum.Matrix.KovacecStrengthenedMarcusDeOliveiraRefutation
open _root_.Matrix

/-- The sigma-point `z_sigma = ∏ᵢ (aᵢ + b_{sigma(i)})` (DMUC Preprint 26-11, §1). -/
def sigmaPoint {n : ℕ} (a b : Fin n → ℂ) (sigma : Equiv.Perm (Fin n)) : ℂ :=
  ∏ i, (a i + b (sigma i))

/-- `Δ(A, B) = {det(D_A + U D_B U*) : U ∈ U(n)}` (Conjecture 1'). -/
def detRange {n : ℕ} (a b : Fin n → ℂ) : Set ℂ :=
  {z | ∃ U ∈ unitaryGroup (Fin n) ℂ, z = (diagonal a + U * diagonal b * star U).det}

/-- The finite metric linear graph `G(A, B)`: the sigma-points joined by the segments
`[z_sigma, z_{sigma∘(i j)}]` of permutations that differ by one transposition (§2). -/
def graph {n : ℕ} (a b : Fin n → ℂ) : Set ℂ :=
  ⋃ (sigma : Equiv.Perm (Fin n)) (i : Fin n) (j : Fin n) (_ : i ≠ j),
    segment ℝ (sigmaPoint a b sigma) (sigmaPoint a b (sigma * Equiv.swap i j))

/-- Definitions 6b: `p` is an exterior point of `G` if for every `M > 0` some `q` at distance
`M` from `p` has `[p, q]` disjoint from every edge of `G`. -/
def exterior (G : Set ℂ) : Set ℂ :=
  {p | ∀ M : ℝ, 0 < M → ∃ q : ℂ, dist p q = M ∧ Disjoint (segment ℝ p q) G}

/-- A Jordan curve: the image of a continuous injective map from the circle. -/
def IsJordanCurve (J : Set ℂ) : Prop :=
  ∃ gamma : Circle → ℂ, Continuous gamma ∧ Function.Injective gamma ∧ Set.range gamma = J

/-- Kovačec, DMUC Preprint 26-11 (2026), Conjecture 7 (strengthened Marcus–de Oliveira): whenever
the boundary `J` of the exterior of `G(A, B)` is a Jordan curve, `Δ(A, B) ⊆ closure(J(A, B))` for
the bounded component `J(A, B)` of `ℂ ∖ J`. -/
def claim : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ),
    IsJordanCurve (frontier (exterior (graph a b))) →
      ∀ x ∉ frontier (exterior (graph a b)),
        Bornology.IsBounded (connectedComponentIn (frontier (exterior (graph a b)))ᶜ x) →
          detRange a b ⊆ closure (connectedComponentIn (frontier (exterior (graph a b)))ᶜ x)

private def a : Fin 3 → ℂ := ![-3 - Complex.I, -5 - 2 * Complex.I, 4 - 3 * Complex.I]
private def b : Fin 3 → ℂ := ![-2 + Complex.I, 4 + 3 * Complex.I, -2 - 5 * Complex.I]
private def Q : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 7 : ℂ) • !![-3, -2, 6; -2, -6, -3; -6, 3, -2]
private def d : ℂ := (2864 + 1840 * Complex.I) / 49

set_option maxHeartbeats 2000000 in
private theorem q_unitary : Q ∈ unitaryGroup (Fin 3) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Q, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply,
      Matrix.smul_apply, smul_eq_mul]
  all_goals norm_num [Complex.star_def, Matrix.one_apply, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, Fin.ext_iff]

set_option maxHeartbeats 2000000 in
private theorem determinant_exact : (diagonal a + Q * diagonal b * star Q).det = d := by
  rw [Matrix.det_fin_three]
  simp only [a, b, Q, d, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  norm_num [Complex.star_def, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk, Fin.ext_iff]

set_option maxHeartbeats 2000000 in
private theorem d_mem_detRange : d ∈ detRange a b := by
  exact ⟨Q, q_unitary, determinant_exact.symm⟩

private def l1 (x : ℝ) : ℝ := (-11*x-1260)/17
private def l2 (x : ℝ) : ℝ := (9*x-476)/13
private def l3 (x : ℝ) : ℝ := (99*x-3416)/52
private def l4 (x : ℝ) : ℝ := (12*x-280)/11
private def u1 (x : ℝ) : ℝ := (183*x+25600)/181
private def u2 (x : ℝ) : ℝ := -2*x+840
private def L (x : ℝ) : ℝ := max (l1 x) (max (l2 x) (min (l3 x) (l4 x)))
private def U (x : ℝ) : ℝ := min (u1 x) (u2 x)
private def P : Set ℂ := {z | -130 ≤ z.re ∧ z.re ≤ 280 ∧ L z.re ≤ z.im ∧ z.im ≤ U z.re}
private def O : Set ℂ := {z | -130 < z.re ∧ z.re < 280 ∧ L z.re < z.im ∧ z.im < U z.re}
private def Bdry : Set ℂ := {z | -130 ≤ z.re ∧ z.re ≤ 280 ∧ (z.im = L z.re ∨ z.im = U z.re)}

set_option maxHeartbeats 1000000 in
private theorem continuous_L : Continuous L := by
  unfold L l1 l2 l3 l4
  fun_prop

set_option maxHeartbeats 1000000 in
private theorem continuous_U : Continuous U := by
  unfold U u1 u2
  fun_prop

set_option maxHeartbeats 1000000 in
private theorem l_piece1 {x : ℝ} (h : x ≤ -28) : L x = l1 x := by
  dsimp [L]
  rw [max_eq_left]
  apply max_le
  · dsimp [l1,l2]; linarith
  · apply le_trans (min_le_left _ _)
    dsimp [l1,l3]; linarith

set_option maxHeartbeats 1000000 in
private theorem l_piece2 {x : ℝ} (h : -28 ≤ x) (h' : x ≤ 24) : L x = l2 x := by
  dsimp [L]
  rw [max_eq_left (show min (l3 x) (l4 x) ≤ l2 x from
    (min_le_left _ _).trans (by dsimp [l2,l3]; linarith))]
  apply max_eq_right
  dsimp [l1,l2]; linarith

set_option maxHeartbeats 1000000 in
private theorem l_piece3 {x : ℝ} (h : 24 ≤ x) (h' : x ≤ 7672/155) : L x = l3 x := by
  dsimp [L]
  rw [min_eq_left (show l3 x ≤ l4 x by dsimp [l3,l4]; linarith)]
  rw [max_eq_right (show l2 x ≤ l3 x by dsimp [l2,l3]; linarith)]
  apply max_eq_right
  dsimp [l1,l3]; linarith

set_option maxHeartbeats 1000000 in
private theorem l_piece4 {x : ℝ} (h : 7672/155 ≤ x) : L x = l4 x := by
  dsimp [L]
  rw [min_eq_right (show l4 x ≤ l3 x by dsimp [l3,l4]; linarith)]
  rw [max_eq_right (show l2 x ≤ l4 x by dsimp [l2,l4]; linarith)]
  apply max_eq_right
  dsimp [l1,l4]; linarith

set_option maxHeartbeats 1000000 in
private theorem u_piece1 {x : ℝ} (h : x ≤ 232) : U x = u1 x := by
  apply min_eq_left
  dsimp [u1,u2]; linarith

set_option maxHeartbeats 1000000 in
private theorem u_piece2 {x : ℝ} (h : 232 ≤ x) : U x = u2 x := by
  apply min_eq_right
  dsimp [u1,u2]; linarith

set_option maxHeartbeats 1000000 in
private theorem endpoint_values : L (-130) = 10 ∧ U (-130) = 10 ∧ L 280 = 280 ∧ U 280 = 280 := by
  rw [l_piece1 (x := -130) (by norm_num), u_piece1 (x := -130) (by norm_num),
    l_piece4 (x := 280) (by norm_num), u_piece2 (x := 280) (by norm_num)]
  norm_num [l1, l4, u1, u2]

set_option maxHeartbeats 1000000 in
private theorem L_lt_U {x : ℝ} (hx : -130 < x) (hx' : x < 280) : L x < U x := by
  by_cases h1 : x ≤ -28
  · rw [l_piece1 h1, u_piece1 (by linarith)]
    dsimp [l1,u1]; linarith
  by_cases h2 : x ≤ 24
  · rw [l_piece2 (by linarith) h2, u_piece1 (by linarith)]
    dsimp [l2,u1]; linarith
  by_cases h3 : x ≤ 7672/155
  · rw [l_piece3 (by linarith) h3, u_piece1 (by linarith)]
    dsimp [l3,u1]; linarith
  by_cases h4 : x ≤ 232
  · rw [l_piece4 (by linarith), u_piece1 h4]
    dsimp [l4,u1]; linarith
  · rw [l_piece4 (by linarith), u_piece2 (by linarith)]
    dsimp [l4,u2]; linarith

set_option maxHeartbeats 1000000 in
private theorem L_le_U {x : ℝ} (hx : -130 ≤ x) (hx' : x ≤ 280) : L x ≤ U x := by
  rcases eq_or_lt_of_le hx with h|h
  · subst x; rw [endpoint_values.1,endpoint_values.2.1]
  rcases eq_or_lt_of_le hx' with h'|h'
  · subst x; rw [endpoint_values.2.2.1,endpoint_values.2.2.2]
  exact (L_lt_U h h').le

set_option maxHeartbeats 1000000 in
private theorem closed_P : IsClosed P := by
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le (continuous_L.comp Complex.continuous_re) Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im (continuous_U.comp Complex.continuous_re))))

set_option maxHeartbeats 1000000 in
private theorem open_O : IsOpen O := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt (continuous_L.comp Complex.continuous_re) Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im (continuous_U.comp Complex.continuous_re))))

set_option maxHeartbeats 1000000 in
private theorem O_subset_P : O ⊆ P := by
  intro z hz
  exact ⟨hz.1.le,hz.2.1.le,hz.2.2.1.le,hz.2.2.2.le⟩

set_option maxHeartbeats 1000000 in
private theorem bdry_subset_P : Bdry ⊆ P := by
  intro z hz
  have h := L_le_U hz.1 hz.2.1
  rcases hz.2.2 with e|e <;> exact ⟨hz.1,hz.2.1,by linarith,by linarith⟩

set_option maxHeartbeats 1000000 in
private theorem d_not_mem_P : d ∉ P := by
  intro h
  have hl : 7672/155 ≤ d.re := by norm_num [d,Complex.div_re]
  have h' := h.2.2.1
  rw [l_piece4 hl] at h'
  norm_num [l4,d,Complex.div_re,Complex.div_im] at h'

set_option maxHeartbeats 1000000 in
private theorem shift_dist (z : ℂ) (t : ℝ) : dist z (z + (t : ℂ)*Complex.I) = |t| := by
  rw [dist_eq_norm, show z - (z + (t : ℂ)*Complex.I) = -((t : ℂ)*Complex.I) by ring]
  simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 1000000 in
private theorem bdry_subset_frontier : Bdry ⊆ frontier P := by
  intro z hz
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (bdry_subset_P hz), Metric.mem_closure_iff.mpr ?_⟩
  intro epsilon hepsilon
  rcases hz.2.2 with hzlo | hzup
  · refine ⟨z + ((-epsilon/2 : ℝ) : ℂ)*Complex.I, ?_, ?_⟩
    · intro hp
      have h := hp.2.2.1
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, zero_add, mul_one] at h
      rw [← hzlo] at h
      linarith
    · rw [shift_dist, abs_of_neg (by linarith)]
      linarith
  · refine ⟨z + ((epsilon/2 : ℝ) : ℂ)*Complex.I, ?_, ?_⟩
    · intro hp
      have h := hp.2.2.2
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, zero_add, mul_one] at h
      rw [← hzup] at h
      linarith
    · rw [shift_dist, abs_of_pos (by linarith)]
      linarith

set_option maxHeartbeats 1000000 in
private theorem P_diff_O_subset_bdry : P \ O ⊆ Bdry := by
  intro z hz
  obtain ⟨hx,hx',hlo,hup⟩ := hz.1
  refine ⟨hx,hx',?_⟩
  by_contra hn
  push_neg at hn
  have h1 : L z.re < z.im := lt_of_le_of_ne hlo (Ne.symm hn.1)
  have h2 : z.im < U z.re := lt_of_le_of_ne hup hn.2
  have h3 : -130 < z.re := by
    by_contra h
    have e : z.re = -130 := by linarith
    simp only [e,endpoint_values.1,endpoint_values.2.1] at h1 h2
    linarith
  have h4 : z.re < 280 := by
    by_contra h
    have e : z.re = 280 := by linarith
    simp only [e,endpoint_values.2.2.1,endpoint_values.2.2.2] at h1 h2
    linarith
  exact hz.2 ⟨h3,h4,h1,h2⟩

set_option maxHeartbeats 1000000 in
private theorem frontier_P : frontier P = Bdry := by
  apply Set.Subset.antisymm
  · intro z hz
    apply P_diff_O_subset_bdry
    refine ⟨closed_P.closure_eq ▸ frontier_subset_closure hz, ?_⟩
    intro ho
    have hInt : z ∈ interior P := interior_mono O_subset_P (open_O.interior_eq.symm ▸ ho)
    exact hz.2 hInt
  · exact bdry_subset_frontier

set_option maxHeartbeats 1000000 in
private theorem bounded_P : Bornology.IsBounded P := by
  apply (isBounded_iff_forall_norm_le).mpr
  refine ⟨2000,?_⟩
  intro z hz
  have hlo : l1 z.re ≤ z.im := (le_max_left _ _).trans hz.2.2.1
  have hup : z.im ≤ u2 z.re := hz.2.2.2.trans (min_le_right _ _)
  dsimp [l1,u2] at hlo hup
  have hr : |z.re| ≤ 280 := abs_le.mpr ⟨by linarith [hz.1],hz.2.1⟩
  have hi : |z.im| ≤ 1200 := abs_le.mpr ⟨by linarith [hz.2.1],by linarith [hz.1]⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

set_option maxHeartbeats 1000000 in
private theorem component_subset_P {x : ℂ} (hx : x ∈ O) :
    connectedComponentIn (frontier P)ᶜ x ⊆ P := by
  let C := connectedComponentIn (frontier P)ᶜ x
  have hInt : x ∈ interior P := interior_mono O_subset_P (open_O.interior_eq.symm ▸ hx)
  have hn : x ∈ (frontier P)ᶜ := fun h => h.2 hInt
  have hs : C ⊆ interior P ∪ Pᶜ := by
    intro z hz
    have hzf := connectedComponentIn_subset (frontier P)ᶜ x hz
    by_cases hp : z ∈ P
    · exact Or.inl ((mem_interior_iff_notMem_frontier hp).mpr hzf)
    · exact Or.inr hp
  have hd : Disjoint (interior P) Pᶜ := Set.disjoint_left.mpr (fun z hz hn => hn (interior_subset hz))
  have hc : C ⊆ interior P :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_interior
      closed_P.isOpen_compl hd hs ⟨x,mem_connectedComponentIn hn,hInt⟩
  exact hc.trans interior_subset

set_option maxHeartbeats 1000000 in
private theorem component_bounded {x : ℂ} (hx : x ∈ O) :
    Bornology.IsBounded (connectedComponentIn (frontier P)ᶜ x) :=
  bounded_P.subset (component_subset_P hx)

set_option maxHeartbeats 1000000 in
private theorem component_closure_subset_P {x : ℂ} (hx : x ∈ O) :
    closure (connectedComponentIn (frontier P)ᶜ x) ⊆ P :=
  closed_P.closure_subset_iff.mpr (component_subset_P hx)

private def perm (k : Fin 6) : Equiv.Perm (Fin 3) :=
  match k.val with
  | 0 => 1
  | 1 => Equiv.swap 1 2
  | 2 => Equiv.swap 0 1
  | 3 => Equiv.swap 0 1 * Equiv.swap 1 2
  | 4 => Equiv.swap 1 2 * Equiv.swap 0 1
  | _ => Equiv.swap 0 2

private def point (k : Fin 6) : ℂ :=
  match k.val with
  | 0 => -30-50*Complex.I
  | 1 => 280+280*Complex.I
  | 2 => -130+10*Complex.I
  | 3 => -28-56*Complex.I
  | 4 => 232+376*Complex.I
  | _ => 24-20*Complex.I

private def edges (k : Fin 9) : Fin 6 × Fin 6 :=
  match k.val with
  | 0 => (0,1)
  | 1 => (0,2)
  | 2 => (0,5)
  | 3 => (1,3)
  | 4 => (1,4)
  | 5 => (2,3)
  | 6 => (2,4)
  | 7 => (3,5)
  | _ => (4,5)

set_option maxHeartbeats 1000000 in
private theorem perm_exhaustive (sigma : Equiv.Perm (Fin 3)) :
    sigma = perm 0 ∨ sigma = perm 1 ∨ sigma = perm 2 ∨ sigma = perm 3 ∨ sigma = perm 4 ∨ sigma = perm 5 := by
  have h : sigma ∈ D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.sixPerms := by
    rw [D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.sixPerms_univ]
    exact Finset.mem_univ sigma
  simp only [D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.sixPerms,
    Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h
  · exact Or.inl (by simpa [perm] using h)
  · exact Or.inr (Or.inr (Or.inl (by simpa [perm] using h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [perm] using h)))))
  · exact Or.inr (Or.inl (by simpa [perm] using h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [perm] using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [perm] using h)))))

set_option maxHeartbeats 1000000 in
private theorem sigma_values (k : Fin 6) : sigmaPoint a b (perm k) = point k := by
  fin_cases k
  · simp only [sigmaPoint,Fin.prod_univ_three]
    change ((-3-Complex.I)+(-2+Complex.I)) * ((-5-2*Complex.I)+(4+3*Complex.I)) * ((4-3*Complex.I)+(-2-5*Complex.I)) = -30-50*Complex.I
    norm_num [Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  · simp only [sigmaPoint,Fin.prod_univ_three]
    change ((-3-Complex.I)+(-2+Complex.I)) * ((-5-2*Complex.I)+(-2-5*Complex.I)) * ((4-3*Complex.I)+(4+3*Complex.I)) = 280+280*Complex.I
    norm_num [Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  · simp only [sigmaPoint,Fin.prod_univ_three]
    change ((-3-Complex.I)+(4+3*Complex.I)) * ((-5-2*Complex.I)+(-2+Complex.I)) * ((4-3*Complex.I)+(-2-5*Complex.I)) = -130+10*Complex.I
    norm_num [Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  · simp only [sigmaPoint,Fin.prod_univ_three]
    change ((-3-Complex.I)+(4+3*Complex.I)) * ((-5-2*Complex.I)+(-2-5*Complex.I)) * ((4-3*Complex.I)+(-2+Complex.I)) = -28-56*Complex.I
    norm_num [Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  · simp only [sigmaPoint,Fin.prod_univ_three]
    change ((-3-Complex.I)+(-2-5*Complex.I)) * ((-5-2*Complex.I)+(-2+Complex.I)) * ((4-3*Complex.I)+(4+3*Complex.I)) = 232+376*Complex.I
    norm_num [Complex.ext_iff,Complex.mul_re,Complex.mul_im]
  · simp only [sigmaPoint,Fin.prod_univ_three]
    change ((-3-Complex.I)+(-2-5*Complex.I)) * ((-5-2*Complex.I)+(4+3*Complex.I)) * ((4-3*Complex.I)+(-2+Complex.I)) = 24-20*Complex.I
    norm_num [Complex.ext_iff,Complex.mul_re,Complex.mul_im]

set_option maxHeartbeats 1000000 in
private theorem edge_exhaustive (k : Fin 6) (i j : Fin 3) (h : i ≠ j) :
    ∃ l : Fin 6, ∃ e : Fin 9,
      perm k * Equiv.swap i j = perm l ∧
        ((k = (edges e).1 ∧ l = (edges e).2) ∨ (l = (edges e).1 ∧ k = (edges e).2)) := by
  revert k i j
  decide

set_option maxHeartbeats 1000000 in
private theorem listed_edge_graph (e : Fin 9) :
    segment ℝ (point (edges e).1) (point (edges e).2) ⊆ graph a b := by
  have h : ∀ e : Fin 9, ∃ i j : Fin 3, i ≠ j ∧
      perm (edges e).1 * Equiv.swap i j = perm (edges e).2 := by decide
  obtain ⟨i,j,hij,heq⟩ := h e
  intro z hz
  apply Set.mem_iUnion.mpr
  refine ⟨perm (edges e).1,Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hij,?_⟩⟩⟩⟩
  rw [heq,sigma_values,sigma_values]
  exact hz

set_option maxHeartbeats 1000000 in
private theorem graph_eq_edges : graph a b = ⋃ e : Fin 9,
    segment ℝ (point (edges e).1) (point (edges e).2) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨sigma,hsigma⟩ := Set.mem_iUnion.mp hz
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hsigma
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hi
    obtain ⟨hij,hz⟩ := Set.mem_iUnion.mp hj
    have hex : ∃ k : Fin 6, sigma = perm k := by
      rcases perm_exhaustive sigma with h|h|h|h|h|h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
      · exact ⟨3,h⟩
      · exact ⟨4,h⟩
      · exact ⟨5,h⟩
    obtain ⟨k,rfl⟩ := hex
    obtain ⟨l,e,heq,hkl⟩ := edge_exhaustive k i j hij
    rw [heq,sigma_values,sigma_values] at hz
    apply Set.mem_iUnion.mpr
    refine ⟨e,?_⟩
    rcases hkl with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hz
    · rw [segment_symm]; exact hz
  · intro z hz
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp hz
    exact listed_edge_graph e he

set_option maxHeartbeats 1000000 in
private theorem segment_on_line {p q z : ℂ} (hpq : p.re < q.re)
    (hx : p.re ≤ z.re) (hx' : z.re ≤ q.re)
    (hy : (q.re-p.re)*(z.im-p.im) = (z.re-p.re)*(q.im-p.im)) :
    z ∈ segment ℝ p q := by
  rw [segment_eq_image]
  let t := (z.re-p.re)/(q.re-p.re)
  have hden : 0 < q.re-p.re := sub_pos.mpr hpq
  have hden' : q.re-p.re ≠ 0 := ne_of_gt hden
  refine ⟨t,⟨div_nonneg (sub_nonneg.mpr hx) hden.le,
    (div_le_one hden).mpr (by linarith)⟩,?_⟩
  apply Complex.ext
  · simp only [Complex.add_re,Complex.smul_re,smul_eq_mul]
    dsimp [t]
    field_simp
    <;> ring
  · simp only [Complex.add_im,Complex.smul_im,smul_eq_mul]
    dsimp [t]
    apply (mul_right_inj' hden').mp
    field_simp
    nlinarith [hy]

set_option maxHeartbeats 1000000 in
private theorem edge_subset_P (e : Fin 9) :
    segment ℝ (point (edges e).1) (point (edges e).2) ⊆ P := by
  intro z hz
  rw [segment_eq_image] at hz
  obtain ⟨t,⟨ht0,ht1⟩,rfl⟩ := hz
  fin_cases e <;>
    norm_num [edges,point,P,L,U,l1,l2,l3,l4,u1,u2,Complex.smul_re,Complex.smul_im,
      smul_eq_mul, max_le_iff,le_min_iff,min_le_iff]
  all_goals refine ⟨by linarith, by linarith, ?_, ?_⟩
  all_goals first | (constructor <;> linarith) |
    (refine ⟨by linarith, by linarith, ?_⟩; first | (left; linarith) | (right; linarith))

set_option maxHeartbeats 1000000 in
private theorem graph_subset_P : graph a b ⊆ P := by
  rw [graph_eq_edges]
  exact Set.iUnion_subset edge_subset_P

set_option maxHeartbeats 1000000 in
private theorem bdry_subset_graph : Bdry ⊆ graph a b := by
  intro z hz
  obtain ⟨hx,hx',hlo|hup⟩ := hz
  · by_cases h1 : z.re ≤ -28
    · have hseg : z ∈ segment ℝ (point 2) (point 3) := by
        apply segment_on_line
        · norm_num [point]
        · simpa [point] using hx
        · simpa [point] using h1
        · rw [l_piece1 h1] at hlo
          norm_num [point,l1] at hlo ⊢
          linarith
      exact listed_edge_graph 5 (by simpa [edges] using hseg)
    by_cases h2 : z.re ≤ 24
    · have hseg : z ∈ segment ℝ (point 3) (point 5) := by
        apply segment_on_line
        · norm_num [point]
        · simp [point]; linarith
        · simpa [point] using h2
        · rw [l_piece2 (by linarith) h2] at hlo
          norm_num [point,l2] at hlo ⊢
          linarith
      exact listed_edge_graph 7 (by simpa [edges] using hseg)
    by_cases h3 : z.re ≤ 7672/155
    · have hseg : z ∈ segment ℝ (point 5) (point 4) := by
        apply segment_on_line
        · norm_num [point]
        · simp [point]; linarith
        · simp [point]; linarith
        · rw [l_piece3 (by linarith) h3] at hlo
          norm_num [point,l3] at hlo ⊢
          linarith
      exact listed_edge_graph 8 (by simpa [edges,segment_symm] using hseg)
    · have hseg : z ∈ segment ℝ (point 3) (point 1) := by
        apply segment_on_line
        · norm_num [point]
        · simp [point]; linarith
        · simpa [point] using hx'
        · rw [l_piece4 (by linarith)] at hlo
          norm_num [point,l4] at hlo ⊢
          linarith
      exact listed_edge_graph 3 (by simpa [edges,segment_symm] using hseg)
  · by_cases hu : z.re ≤ 232
    · have hseg : z ∈ segment ℝ (point 2) (point 4) := by
        apply segment_on_line
        · norm_num [point]
        · simpa [point] using hx
        · simpa [point] using hu
        · rw [u_piece1 hu] at hup
          norm_num [point,u1] at hup ⊢
          linarith
      exact listed_edge_graph 6 (by simpa [edges] using hseg)
    · have hseg : z ∈ segment ℝ (point 4) (point 1) := by
        apply segment_on_line
        · norm_num [point]
        · simp [point]; linarith
        · simpa [point] using hx'
        · rw [u_piece2 (by linarith)] at hup
          norm_num [point,u2] at hup ⊢
          linarith
      exact listed_edge_graph 4 (by simpa [edges,segment_symm] using hseg)

set_option maxHeartbeats 1000000 in
private theorem frontier_subset_graph : frontier P ⊆ graph a b := by
  rw [frontier_P]
  exact bdry_subset_graph

private def xcoord (z : Circle) : ℝ := 75 + 205 * (z : ℂ).re
private def gamma (z : Circle) : ℂ := (xcoord z : ℂ) +
  ((if 0 ≤ (z : ℂ).im then U (xcoord z) else L (xcoord z) : ℝ) : ℂ) * Complex.I

set_option maxHeartbeats 1000000 in
private theorem circle_sq (z : Circle) : (z : ℂ).re^2 + (z : ℂ).im^2 = 1 := by
  simpa [Complex.normSq_apply,pow_two] using Circle.normSq_coe z

set_option maxHeartbeats 1000000 in
private theorem circle_re_bounds (z : Circle) : -1 ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1 := by
  exact abs_le.mp ((Complex.abs_re_le_norm (z : ℂ)).trans_eq (Circle.norm_coe z))

set_option maxHeartbeats 1000000 in
private theorem equator (z : Circle) (h : (z : ℂ).im = 0) : (z : ℂ).re = -1 ∨ (z : ℂ).re = 1 := by
  have hs := circle_sq z
  rw [h] at hs
  have hm : ((z : ℂ).re + 1) * ((z : ℂ).re - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hm with h|h
  · left; linarith
  · right; linarith

set_option maxHeartbeats 1000000 in
private theorem xcoord_bounds (z : Circle) : -130 ≤ xcoord z ∧ xcoord z ≤ 280 := by
  obtain ⟨h,h'⟩ := circle_re_bounds z
  dsimp [xcoord]; constructor <;> linarith

set_option maxHeartbeats 1000000 in
private theorem branches_agree (z : Circle) (h : (z : ℂ).im = 0) : U (xcoord z) = L (xcoord z) := by
  rcases equator z h with h|h
  · have : xcoord z = -130 := by dsimp [xcoord]; rw [h]; norm_num
    rw [this,endpoint_values.1,endpoint_values.2.1]
  · have : xcoord z = 280 := by dsimp [xcoord]; rw [h]; norm_num
    rw [this,endpoint_values.2.2.1,endpoint_values.2.2.2]

set_option maxHeartbeats 1000000 in
private theorem continuous_xcoord : Continuous xcoord := by
  unfold xcoord
  fun_prop

set_option maxHeartbeats 1000000 in
private theorem continuous_gamma : Continuous gamma := by
  have hi : Continuous (fun z : Circle => (z : ℂ).im) := Complex.continuous_im.comp continuous_subtype_val
  have hu := continuous_U.comp continuous_xcoord
  have hl := continuous_L.comp continuous_xcoord
  have hc : Continuous (fun z : Circle => if 0 ≤ (z : ℂ).im then U (xcoord z) else L (xcoord z)) :=
    Continuous.if_le hu hl continuous_const hi (fun z hz => branches_agree z hz.symm)
  exact (Complex.continuous_ofReal.comp continuous_xcoord).add
    ((Complex.continuous_ofReal.comp hc).mul continuous_const)

set_option maxHeartbeats 1000000 in
private theorem injective_gamma : Function.Injective gamma := by
  intro z w h
  have hx := congrArg Complex.re h
  simp only [gamma,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hx
  have hr : (z : ℂ).re = (w : ℂ).re := by dsimp [xcoord] at hx; linarith
  have hy := congrArg Complex.im h
  simp only [gamma,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_zero,add_zero,zero_add,mul_one] at hy
  have hsq : (z : ℂ).im^2 = (w : ℂ).im^2 := by
    have hs := circle_sq z
    rw [hr] at hs
    linarith [circle_sq w]
  apply Circle.ext
  apply Complex.ext hr
  by_cases hz : 0 ≤ (z : ℂ).im <;> by_cases hw : 0 ≤ (w : ℂ).im
  · nlinarith
  · rw [if_pos hz,if_neg hw,← hx] at hy
    have heq : U (xcoord z) = L (xcoord z) := hy
    obtain ⟨hb,hb'⟩ := xcoord_bounds z
    have hend : xcoord z = -130 ∨ xcoord z = 280 := by
      by_contra hn
      push_neg at hn
      have hh := L_lt_U (lt_of_le_of_ne hb (Ne.symm hn.1)) (lt_of_le_of_ne hb' hn.2)
      linarith
    rcases hend with he|he <;> dsimp [xcoord] at he <;>
      nlinarith [circle_sq z,circle_sq w]
  · rw [if_neg hz,if_pos hw,← hx] at hy
    have heq : U (xcoord z) = L (xcoord z) := hy.symm
    obtain ⟨hb,hb'⟩ := xcoord_bounds z
    have hend : xcoord z = -130 ∨ xcoord z = 280 := by
      by_contra hn
      push_neg at hn
      have hh := L_lt_U (lt_of_le_of_ne hb (Ne.symm hn.1)) (lt_of_le_of_ne hb' hn.2)
      linarith
    rcases hend with he|he <;> dsimp [xcoord] at he <;>
      nlinarith [circle_sq z,circle_sq w]
  · nlinarith

set_option maxHeartbeats 1000000 in
private theorem gamma_mem_bdry (z : Circle) : gamma z ∈ Bdry := by
  obtain ⟨hb,hb'⟩ := xcoord_bounds z
  dsimp [gamma,Bdry]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,zero_add,mul_one]
  refine ⟨hb,hb',?_⟩
  by_cases hz : 0 ≤ (z : ℂ).im
  · exact Or.inr (if_pos hz)
  · exact Or.inl (if_neg hz)

set_option maxHeartbeats 1000000 in
private theorem circle_of_coords {t s : ℝ} (h : t^2+s^2=1) :
    (⟨t,s⟩ : ℂ) ∈ Metric.sphere 0 1 := by
  rw [Metric.mem_sphere,dist_zero_right,Complex.norm_def,Complex.normSq_apply]
  have hh : (⟨t,s⟩ : ℂ).re * (⟨t,s⟩ : ℂ).re + (⟨t,s⟩ : ℂ).im * (⟨t,s⟩ : ℂ).im = 1 := by
    simpa [pow_two] using h
  rw [hh,Real.sqrt_one]

set_option maxHeartbeats 1000000 in
private theorem gamma_range : Set.range gamma = Bdry := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,rfl⟩; exact gamma_mem_bdry z
  · intro p hp
    let t : ℝ := (p.re-75)/205
    have ht : -1 ≤ t ∧ t ≤ 1 := by dsimp [t]; constructor <;> linarith [hp.1,hp.2.1]
    have ht2 : 0 ≤ 1-t^2 := by nlinarith [ht.1,ht.2]
    have hs := Real.sq_sqrt ht2
    have hpos := Real.sqrt_nonneg (1-t^2)
    rcases hp.2.2 with hlo|hup
    · let z : Circle := ⟨⟨t,-Real.sqrt (1-t^2)⟩,circle_of_coords (by nlinarith)⟩
      have hx : xcoord z = p.re := by dsimp [xcoord,z,t]; ring
      refine ⟨z,?_⟩
      by_cases hh : Real.sqrt (1-t^2) = 0
      · have him : (z : ℂ).im = 0 := by dsimp [z]; simp [hh]
        have hagree := branches_agree z him
        apply Complex.ext
        · simp [gamma,hx]
        · simp [gamma,him,hx,← hlo] at hagree ⊢
          exact hagree
      · have hn : ¬ 0 ≤ (z : ℂ).im := by dsimp [z]; exact not_le.mpr (neg_neg_of_pos (lt_of_le_of_ne hpos (Ne.symm hh)))
        apply Complex.ext
        · simp [gamma,hx]
        · simpa [gamma,hn,hx] using hlo.symm
    · let z : Circle := ⟨⟨t,Real.sqrt (1-t^2)⟩,circle_of_coords (by nlinarith)⟩
      have hx : xcoord z = p.re := by dsimp [xcoord,z,t]; ring
      have him : 0 ≤ (z : ℂ).im := hpos
      refine ⟨z,?_⟩
      apply Complex.ext
      · simp [gamma,hx]
      · simpa [gamma,him,hx] using hup.symm

set_option maxHeartbeats 1000000 in
private theorem jordan_frontier_P : IsJordanCurve (frontier P) := by
  rw [frontier_P]
  exact ⟨gamma,continuous_gamma,injective_gamma,gamma_range⟩

set_option maxHeartbeats 1000000 in
private theorem real_shift_dist (z : ℂ) (t : ℝ) : dist z (z + (t : ℂ)) = |t| := by
  simp only [dist_self_add_right, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 1000000 in
private theorem outside_exterior {G : Set ℂ} (hG : G ⊆ P) : Pᶜ ⊆ exterior G := by
  intro p hp M hM
  have hout : p.re < -130 ∨ 280 < p.re ∨ p.im < L p.re ∨ U p.re < p.im := by
    by_contra hn
    push_neg at hn
    exact hp ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2⟩
  rcases hout with hx|hx|hy|hy
  · refine ⟨p + ((-M : ℝ) : ℂ),?_,?_⟩
    · rw [real_shift_dist,abs_of_neg (by linarith),neg_neg]
    · apply Set.disjoint_left.mpr
      intro z hz hzG
      rw [segment_eq_image] at hz
      obtain ⟨t,⟨ht,ht'⟩,rfl⟩ := hz
      have hpz := (hG hzG).1
      have he : ((1-t) • p + t • (p + ((-M : ℝ) : ℂ))).re = p.re-t*M := by
        simp [Complex.smul_re,smul_eq_mul]; ring
      rw [he] at hpz
      nlinarith [mul_nonneg ht hM.le]
  · refine ⟨p + (M : ℂ),?_,?_⟩
    · rw [real_shift_dist,abs_of_pos hM]
    · apply Set.disjoint_left.mpr
      intro z hz hzG
      rw [segment_eq_image] at hz
      obtain ⟨t,⟨ht,ht'⟩,rfl⟩ := hz
      have hpz := (hG hzG).2.1
      have he : ((1-t) • p + t • (p + (M : ℂ))).re = p.re+t*M := by
        simp [Complex.smul_re,smul_eq_mul]; ring
      rw [he] at hpz
      nlinarith [mul_nonneg ht hM.le]
  · refine ⟨p + ((-M : ℝ) : ℂ)*Complex.I,?_,?_⟩
    · rw [shift_dist,abs_of_neg (by linarith),neg_neg]
    · apply Set.disjoint_left.mpr
      intro z hz hzG
      rw [segment_eq_image] at hz
      obtain ⟨t,⟨ht,ht'⟩,rfl⟩ := hz
      have hpz := (hG hzG).2.2.1
      have hre : ((1-t) • p + t • (p + ((-M : ℝ) : ℂ)*Complex.I)).re = p.re := by
        simp [Complex.smul_re,smul_eq_mul,Complex.mul_re]; ring
      have him : ((1-t) • p + t • (p + ((-M : ℝ) : ℂ)*Complex.I)).im = p.im-t*M := by
        simp [Complex.smul_im,smul_eq_mul,Complex.mul_im]; ring
      rw [hre,him] at hpz
      nlinarith [mul_nonneg ht hM.le]
  · refine ⟨p + (M : ℂ)*Complex.I,?_,?_⟩
    · rw [shift_dist,abs_of_pos hM]
    · apply Set.disjoint_left.mpr
      intro z hz hzG
      rw [segment_eq_image] at hz
      obtain ⟨t,⟨ht,ht'⟩,rfl⟩ := hz
      have hpz := (hG hzG).2.2.2
      have hre : ((1-t) • p + t • (p + (M : ℂ)*Complex.I)).re = p.re := by
        simp [Complex.smul_re,smul_eq_mul,Complex.mul_re]; ring
      have him : ((1-t) • p + t • (p + (M : ℂ)*Complex.I)).im = p.im+t*M := by
        simp [Complex.smul_im,smul_eq_mul,Complex.mul_im]; ring
      rw [hre,him] at hpz
      nlinarith [mul_nonneg ht hM.le]

set_option maxHeartbeats 1000000 in
private theorem inside_not_exterior {G : Set ℂ} (hG : frontier P ⊆ G) {p : ℂ} (hp : p ∈ P) :
    p ∉ exterior G := by
  intro he
  obtain ⟨C,hC⟩ := bounded_P.exists_norm_le
  let M : ℝ := |C|+‖p‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨q,hd,hdis⟩ := he M hM
  have hq : q ∉ P := by
    intro hqp
    have htriangle : dist p q ≤ ‖p‖+‖q‖ := by
      simpa only [dist_zero_right,dist_zero_left] using dist_triangle p 0 q
    have hqn := hC q hqp
    have hc := le_abs_self C
    dsimp [M] at hd
    linarith
  let S := segment ℝ p q
  have havoid : Disjoint S (frontier P) := hdis.mono_right hG
  have hpf : p ∉ frontier P := Set.disjoint_left.mp havoid (left_mem_segment ℝ p q)
  have hpInt := (mem_interior_iff_notMem_frontier hp).mpr hpf
  have hs : S ⊆ interior P ∪ Pᶜ := by
    intro z hz
    by_cases hzp : z ∈ P
    · left
      exact (mem_interior_iff_notMem_frontier hzp).mpr (Set.disjoint_left.mp havoid hz)
    · exact Or.inr hzp
  have hcS : IsPreconnected S := (convex_segment p q).isPreconnected
  have hsub : S ⊆ interior P := hcS.subset_left_of_subset_union isOpen_interior
    closed_P.isOpen_compl (Set.disjoint_left.mpr (fun z hz hn => hn (interior_subset hz)))
    hs ⟨p,left_mem_segment ℝ p q,hpInt⟩
  exact hq (interior_subset (hsub (right_mem_segment ℝ p q)))

set_option maxHeartbeats 1000000 in
private theorem exterior_eq : exterior (graph a b) = Pᶜ := by
  apply Set.Subset.antisymm
  · intro p hp hP
    exact inside_not_exterior frontier_subset_graph hP hp
  · exact outside_exterior graph_subset_P

set_option maxHeartbeats 1000000 in
private theorem exterior_frontier : frontier (exterior (graph a b)) = frontier P := by
  rw [exterior_eq,frontier_compl]

set_option maxHeartbeats 1000000 in
private theorem zero_mem_O : (0 : ℂ) ∈ O := by
  norm_num [O,L,U,l1,l2,l3,l4,u1,u2]

set_option maxHeartbeats 1000000 in
theorem result : ¬ claim := by
  intro hc
  have hJ : IsJordanCurve (frontier (exterior (graph a b))) := by
    rw [exterior_frontier]
    exact jordan_frontier_P
  have hx : (0 : ℂ) ∉ frontier (exterior (graph a b)) := by
    rw [exterior_frontier, frontier_P]
    intro h
    rcases h.2.2 with hlo | hup
    · exact (ne_of_gt zero_mem_O.2.2.1) hlo
    · exact (ne_of_lt zero_mem_O.2.2.2) hup
  have hb : Bornology.IsBounded
      (connectedComponentIn (frontier (exterior (graph a b)))ᶜ (0 : ℂ)) := by
    rw [exterior_frontier]
    exact component_bounded zero_mem_O
  have hd := hc 3 a b hJ 0 hx hb d_mem_detRange
  rw [exterior_frontier] at hd
  exact d_not_mem_P (component_closure_subset_P zero_mem_O hd)

end D5.S3.Quantum.Matrix.KovacecStrengthenedMarcusDeOliveiraRefutation
