/- GID: D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Optimization/WeightedCrownMomentCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A feasible moment certificate with a strict weighted-crown gap. -/

/-
admission_basis: escape-witness.
escape_witness: moment_feasible.
Escape audit unfinished: issue #15610 records missing observational-dependence evidence at
n = 3, x = 0 and x = 8, plus source-selection/report-decoding evidence for the hub/leaf
registrations. No completed registration is claimed.
objective_formula: proof_shape: bind-only; escape_witness: none; consumers: moment_objective.
parameter_bounds: proof_shape: bind-only; escape_witness: none; consumers: block_coefficients_pos, gramMoment_psd.
block_coefficients_pos: proof_shape: bind-only; escape_witness: none; consumers: gramMoment_psd, gram_center_spoke, gram_spokes, residualK_eq.
residual_determinant: proof_shape: bind-only; escape_witness: none; consumers: residualK_eq.
a_ne_b: proof_shape: bind-only; escape_witness: none; consumers: _simp_1, centralEdge, encode_center, moment_feasible, moment_objective, objective_on_active, pair_shapes.
leaf_pair_injective_left: proof_shape: bind-only; escape_witness: none; consumers: encode_left.
leaf_pair_injective_right: proof_shape: bind-only; escape_witness: none; consumers: encode_right.
encode_center: proof_shape: bind-only; escape_witness: none; consumers: central_left_ne, central_right_ne, encode_center_raw, encode_center_reverse, moment_feasible, moment_objective.
encode_left: proof_shape: bind-only; escape_witness: none; consumers: central_left_ne, encode_left_raw, encode_left_reverse, leftEdge_injective, left_right_ne, moment_feasible, moment_objective.
encode_right: proof_shape: bind-only; escape_witness: none; consumers: central_right_ne, encode_right_raw, encode_right_reverse, left_right_ne, moment_feasible, moment_objective, rightEdge_injective.
encode_leaves: proof_shape: bind-only; escape_witness: none; consumers: encode_leaves_raw, moment_feasible.
edge_comm: proof_shape: bind-only; escape_witness: none; consumers: adjacent_shapes, encode_center_reverse, encode_left_reverse, encode_right_reverse, pair_shapes.
pair_shapes: proof_shape: bind-only; escape_witness: none; consumers: moment_feasible, objective_on_active.
pair_through: proof_shape: bind-only; escape_witness: none; consumers: adjacent_shapes.
adjacent_shapes: proof_shape: bind-only; escape_witness: none; consumers: moment_feasible.
gramMoment_psd: proof_shape: bind-only; escape_witness: none; consumers: gram_symmetric, moment_psd.
moment_psd: proof_shape: bind-only; escape_witness: none; consumers: moment_feasible.
covariance: proof_shape: bind-only; escape_witness: none; consumers: sum_A_entries, sum_B_entries.
residualK_eq: proof_shape: bind-only; escape_witness: none; consumers: gram_spokes.
alpha_add_beta: proof_shape: bind-only; escape_witness: none; consumers: gram_same_side.
gram_ident: proof_shape: bind-only; escape_witness: none; consumers: moment_feasible, moment_objective, moment_triangle.
gram_zero: proof_shape: bind-only; escape_witness: none; consumers: gram_zero_right, moment_feasible, moment_triangle.
gram_center_center: proof_shape: bind-only; escape_witness: none; consumers: moment_feasible.
gram_center_spoke: proof_shape: bind-only; escape_witness: none; consumers: gram_spoke_center, moment_triangle.
sum_A_entries: proof_shape: bind-only; escape_witness: none; consumers: gram_spokes.
sum_B_entries: proof_shape: bind-only; escape_witness: none; consumers: gram_spokes.
gram_spokes: proof_shape: bind-only; escape_witness: none; consumers: gram_opposite_side, gram_same_side.
gram_same_side: proof_shape: bind-only; escape_witness: none; consumers: moment_feasible, moment_triangle.
gram_opposite_side: proof_shape: bind-only; escape_witness: none; consumers: gram_opposite_reverse, moment_triangle.
gram_symmetric: proof_shape: bind-only; escape_witness: none; consumers: gram_opposite_reverse, gram_spoke_center, gram_zero_right.
gram_zero_right: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
gram_spoke_center: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
gram_opposite_reverse: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
first_moment_bounds: proof_shape: bind-only; escape_witness: none; consumers: objective_bounded.
objective_bounded: proof_shape: bind-only; escape_witness: none; consumers: objective_le_value.
objective_le_value: proof_shape: bind-only; escape_witness: none; consumers: constructed_value_gap.
encode_center_reverse: proof_shape: bind-only; escape_witness: none; consumers: encode_center_reverse_raw.
encode_left_reverse: proof_shape: bind-only; escape_witness: none; consumers: encode_left_reverse_raw.
encode_right_reverse: proof_shape: bind-only; escape_witness: none; consumers: encode_right_reverse_raw.
encode_center_raw: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
encode_center_reverse_raw: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
encode_left_raw: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
encode_left_reverse_raw: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
encode_right_raw: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
encode_right_reverse_raw: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
encode_leaves_raw: proof_shape: bind-only; escape_witness: none; consumers: moment_triangle.
moment_triangle: proof_shape: bind-only; escape_witness: none; consumers: moment_feasible.
moment_feasible: proof_shape: content; escape_witness: self; consumers: constructed_value_gap.
leftEdge_injective: proof_shape: bind-only; escape_witness: none; consumers: moment_objective.
rightEdge_injective: proof_shape: bind-only; escape_witness: none; consumers: moment_objective.
central_left_ne: proof_shape: bind-only; escape_witness: none; consumers: central_not_spokes.
central_right_ne: proof_shape: bind-only; escape_witness: none; consumers: central_not_spokes.
left_right_ne: proof_shape: bind-only; escape_witness: none; consumers: active_disjoint.
active_disjoint: proof_shape: bind-only; escape_witness: none; consumers: moment_objective.
central_not_spokes: proof_shape: bind-only; escape_witness: none; consumers: moment_objective.
objective_on_active: proof_shape: bind-only; escape_witness: none; consumers: moment_objective.
moment_objective: proof_shape: bind-only; escape_witness: none; consumers: constructed_value_gap.
constructed_value_gap: proof_shape: content; escape_witness: moment_feasible; consumers: result.
Direct frozen dependencies:
  none.
Utility none: uniform operator and real-parameter constructions, not finite enumeration.
-/

import D5.S3.Quantum.Optimization.WeightedCrownSpectralBound

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Optimization.WeightedCrownMomentCertificate
open D5.S3.Quantum.Optimization.WeightedCrownSpectralBound
attribute [local instance] Classical.propDecidable

def L (n : ℕ) : ℝ := ((n : ℝ) + 2)^2 / (4 * ((n : ℝ) + 1))

def U (n : ℕ) : ℝ := ((n : ℝ) + 2) / 3


def crownWeight (n : ℕ) (x : ℝ) (e : {s : Finset (Option (Option (Fin n))) // s.card = 2}) : ℝ :=
  if a n ∈ e.val ∧ b n ∈ e.val then x
  else if a n ∈ e.val ∨ b n ∈ e.val then 1 else 0


def npa1Feasible {n : ℕ} (M : Matrix (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) ℝ) : Prop :=
  M.IsSymm ∧ M.PosSemidef ∧ M none none = 1 ∧
  (∀ e : {s : Finset (Option (Option (Fin n))) // s.card = 2}, M (some e) (some e) = M none (some e)) ∧
  (∀ e f g : {s : Finset (Option (Option (Fin n))) // s.card = 2}, (e.val ∩ f.val).card = 1 → g.val = symmDiff e.val f.val →
    M (some e) (some f) + M (some f) (some e) =
      (M none (some e) + M none (some f) - M none (some g)) / 2)


def objective {n : ℕ} (x : ℝ) (M : Matrix (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) ℝ) : ℝ :=
  ∑ e, crownWeight n x e * M none (some e)

def npa1Value (n : ℕ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ M : Matrix (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) ℝ,
    npa1Feasible M ∧ r = objective x M}



private def p0 (n : ℕ) : ℝ := ((n : ℝ) + 1) / (2 * (n : ℝ))
private def q (n : ℕ) (x : ℝ) : ℝ := (x - L n) / (16 * (n : ℝ))
private def c (n : ℕ) (x : ℝ) : ℝ := (x + L n) / (4 * (n : ℝ))
private def p (n : ℕ) (x : ℝ) : ℝ := p0 n - c n x * q n x
private def d (n : ℕ) (x : ℝ) : ℝ := ((n : ℝ) * p n x / 2 + q n x / 4) / ((n : ℝ) - 1)
private def alpha (n : ℕ) (x : ℝ) : ℝ := ((n : ℝ) - 2) * p n x / (4 * ((n : ℝ) - 1)) - (n : ℝ) * q n x / (8 * ((n : ℝ) - 1))
private def beta (n : ℕ) (x : ℝ) : ℝ := (d n x + q n x / 4) / 2

private theorem objective_formula (n : ℕ) (hn : 3 ≤ n) (x : ℝ) :
    x * q n x + 2 * (n : ℝ) * p n x = (n : ℝ) + 1 + (x - L n)^2 / (32 * (n : ℝ)) := by
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [p, p0, c, q]
  field_simp
  ring

private theorem parameter_bounds (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    0 < q n x ∧ q n x < 1/24 ∧ 0 < c n x ∧ c n x < 1/3 ∧
    1/2 < p0 n ∧ p0 n ≤ 2/3 ∧ 1/3 < p n x := by
  have hN : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 < L n := by unfold L; positivity
  have hU : U n ≤ ((n : ℝ) + 1) / 2 := by unfold U; linarith
  have hx0 : 0 < x := lt_trans hL0 hxL
  have hL : L n < ((n : ℝ) + 1) / 2 := lt_of_lt_of_le (lt_trans hxL hxU) hU
  have hx : x < ((n : ℝ) + 1) / 2 := lt_of_lt_of_le hxU hU
  have hq0 : 0 < q n x := by unfold q; exact div_pos (sub_pos.mpr hxL) (by positivity)
  have hq1 : q n x < 1/24 := by
    unfold q
    apply (div_lt_iff₀ (by positivity : 0 < 16 * (n : ℝ))).mpr
    nlinarith
  have hc0 : 0 < c n x := by unfold c; positivity
  have hc1 : c n x < 1/3 := by
    unfold c
    apply (div_lt_iff₀ (by positivity : 0 < 4 * (n : ℝ))).mpr
    nlinarith
  have hp00 : 1/2 < p0 n := by
    unfold p0
    apply (lt_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    linarith
  have hp01 : p0 n ≤ 2/3 := by
    unfold p0
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    linarith
  refine ⟨hq0,hq1,hc0,hc1,hp00,hp01,?_⟩
  unfold p
  nlinarith [mul_lt_mul_of_pos_left hq1 hc0]

private theorem block_coefficients_pos (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    0 < alpha n x ∧ 0 < beta n x ∧ 0 < q n x * (1 - q n x) ∧
    0 < 4 * p0 n - c n x * (c n x - 1 / (2 * (n : ℝ))) := by
  obtain ⟨hq0,hq1,hc0,hc1,hp00,hp01,hp⟩ := parameter_bounds n hn x hxL hxU
  have hN : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hNm : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have ha : 0 < alpha n x := by
    unfold alpha
    rw [show ((n : ℝ)-2)*p n x / (4*((n : ℝ)-1)) - (n : ℝ)*q n x / (8*((n : ℝ)-1)) =
      (2*((n : ℝ)-2)*p n x - (n : ℝ)*q n x) / (8*((n : ℝ)-1)) by field_simp; ring]
    apply div_pos _ (by positivity)
    nlinarith [mul_pos (by linarith : 0 < (n : ℝ)-2) (sub_pos.mpr hp),
      mul_pos hN0 (sub_pos.mpr hq1)]
  have hb : 0 < beta n x := by
    unfold beta d
    positivity
  refine ⟨ha,hb,mul_pos hq0 (by linarith),?_⟩
  have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
  nlinarith [mul_pos hc0 hinv, sq_nonneg (c n x - 1/3)]

private theorem residual_determinant (n : ℕ) (hn : 3 ≤ n) (x : ℝ) :
    (p n x * c n x * q n x) * (q n x * (1 - q n x)) -
      (q n x * (1/4 - p n x))^2 =
      (q n x)^3 * (4*p0 n - c n x*(c n x - 1/(2*(n : ℝ)))) := by
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold p c q p0 L
  field_simp
  ring

private def ident {n : ℕ} : (Option (Option (Bool × Fin n))) := none
private def center {n : ℕ} : (Option (Option (Bool × Fin n))) := some none
private def spoke {n : ℕ} (side : Bool) (i : Fin n) : (Option (Option (Bool × Fin n))) := some (some (side,i))

private def edge {n : ℕ} (u v : (Option (Option (Fin n)))) (h : u ≠ v) : {s : Finset (Option (Option (Fin n))) // s.card = 2} :=
  ⟨{u,v}, by simp [h]⟩
@[simp] private theorem a_ne_b (n : ℕ) : a n ≠ b n := by simp [a,b]

private def encode {n : ℕ} (e : {s : Finset (Option (Option (Fin n))) // s.card = 2}) : Option ((Option (Option (Bool × Fin n)))) :=
  if h0 : e.val = {a n,b n} then some center
  else if h1 : ∃ i, e.val = {a n,leaf i} then some (spoke false (Classical.choose h1))
  else if h2 : ∃ i, e.val = {b n,leaf i} then some (spoke true (Classical.choose h2))
  else none

private theorem leaf_pair_injective_left {n : ℕ} (i j : Fin n) :
    ({a n,leaf i} : Finset ((Option (Option (Fin n))))) = {a n,leaf j} → i = j := by
  intro h
  have hm : leaf i ∈ ({a n,leaf j} : Finset ((Option (Option (Fin n))))) := h ▸ (by simp)
  simpa [a,leaf] using hm

private theorem leaf_pair_injective_right {n : ℕ} (i j : Fin n) :
    ({b n,leaf i} : Finset ((Option (Option (Fin n))))) = {b n,leaf j} → i = j := by
  intro h
  have hm : leaf i ∈ ({b n,leaf j} : Finset ((Option (Option (Fin n))))) := h ▸ (by simp)
  simpa [b,leaf] using hm

@[simp] private theorem encode_center (n : ℕ) : encode (edge (a n) (b n) (a_ne_b n)) = some center := by
  simp [encode,edge]
@[simp] private theorem encode_left {n : ℕ} (i : Fin n) : encode (edge (a n) (leaf i) (a_ne_leaf i)) = some (spoke false i) := by
  have h0 : ({a n,leaf i} : Finset ((Option (Option (Fin n))))) ≠ {a n,b n} := by
    intro h
    have hm : leaf i ∈ ({a n,b n} : Finset ((Option (Option (Fin n))))) := h ▸ (by simp)
    simpa [a,b,leaf] using hm
  have h1 : ∃ j : Fin n, ({a n,leaf i} : Finset ((Option (Option (Fin n))))) = {a n,leaf j} := ⟨i,rfl⟩
  dsimp only [encode,edge, edge]
  simp only [h0, h1, dite_false, dite_true, ite_false, ite_true]
  exact congrArg (fun j => some (spoke false j)) (leaf_pair_injective_left i _ (Classical.choose_spec h1)).symm
@[simp] private theorem encode_right {n : ℕ} (i : Fin n) : encode (edge (b n) (leaf i) (b_ne_leaf i)) = some (spoke true i) := by
  have h0 : ({b n,leaf i} : Finset ((Option (Option (Fin n))))) ≠ {a n,b n} := by
    intro h
    have hm : leaf i ∈ ({a n,b n} : Finset ((Option (Option (Fin n))))) := h ▸ (by simp)
    simpa [a,b,leaf] using hm
  have h1 : ¬ ∃ j : Fin n, ({b n,leaf i} : Finset ((Option (Option (Fin n))))) = {a n,leaf j} := by
    rintro ⟨j,h⟩
    have hm : b n ∈ ({a n,leaf j} : Finset ((Option (Option (Fin n))))) := h ▸ (by simp)
    simpa [a,b,leaf] using hm
  have h2 : ∃ j : Fin n, ({b n,leaf i} : Finset ((Option (Option (Fin n))))) = {b n,leaf j} := ⟨i,rfl⟩
  dsimp only [encode,edge, edge]
  simp only [h0, h1, h2, dite_false, dite_true, ite_false, ite_true]
  exact congrArg (fun j => some (spoke true j)) (leaf_pair_injective_right i _ (Classical.choose_spec h2)).symm
@[simp] private theorem encode_leaves {n : ℕ} (i j : Fin n) (h : leaf i ≠ leaf j) : encode (edge (leaf i) (leaf j) h) = none := by
  have ha : a n ∉ ({leaf i,leaf j} : Finset ((Option (Option (Fin n))))) := by simp [a,leaf]
  have hb : b n ∉ ({leaf i,leaf j} : Finset ((Option (Option (Fin n))))) := by simp [b,leaf]
  have h0 : ({leaf i,leaf j} : Finset ((Option (Option (Fin n))))) ≠ {a n,b n} := by intro he; exact ha (he.symm ▸ (by simp))
  have h1 : ¬ ∃ k : Fin n, ({leaf i,leaf j} : Finset ((Option (Option (Fin n))))) = {a n,leaf k} := by rintro ⟨k,he⟩; exact ha (he.symm ▸ (by simp))
  have h2 : ¬ ∃ k : Fin n, ({leaf i,leaf j} : Finset ((Option (Option (Fin n))))) = {b n,leaf k} := by rintro ⟨k,he⟩; exact hb (he.symm ▸ (by simp))
  simp [encode,edge,h0,h1,h2]

private theorem edge_comm {n : ℕ} (u v : (Option (Option (Fin n)))) (h : u ≠ v) : edge u v h = edge v u h.symm := by
  apply Subtype.ext
  exact Finset.pair_comm u v

private def decode {n : ℕ} : Option ({s : Finset (Option (Option (Fin n))) // s.card = 2}) → Option ((Option (Option (Bool × Fin n))))
  | none => some ident
  | some e => encode e

private theorem pair_shapes {n : ℕ} (e : {s : Finset (Option (Option (Fin n))) // s.card = 2}) :
    e = edge (a n) (b n) (a_ne_b n) ∨
    (∃ i, e = edge (a n) (leaf i) (a_ne_leaf i)) ∨
    (∃ i, e = edge (b n) (leaf i) (b_ne_leaf i)) ∨
    (∃ i j, ∃ h : leaf i ≠ leaf j, e = edge (leaf i) (leaf j) h) := by
  obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp e.property
  have he' : e = edge u v huv := Subtype.ext he
  rw [he']
  rcases u with _ | (_ | i) <;> rcases v with _ | (_ | j)
  · exact False.elim (huv rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨j,rfl⟩)
  · exact Or.inl (edge_comm _ _ huv)
  · exact False.elim (huv rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨j,rfl⟩))
  · exact Or.inr (Or.inl ⟨i,edge_comm _ _ huv⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i,edge_comm _ _ huv⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i,j,huv,rfl⟩))

private lemma pair_through {n : ℕ} (e : {s : Finset (Option (Option (Fin n))) // s.card = 2}) (j : (Option (Option (Fin n)))) (hj : j ∈ e.val) :
    ∃ i, ∃ h : i ≠ j, e = edge i j h := by
  obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp e.property
  rw [he] at hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact ⟨v,huv.symm,Subtype.ext (he.trans (Finset.pair_comm _ _))⟩
  · exact ⟨u,huv,Subtype.ext he⟩

private theorem adjacent_shapes {n : ℕ} (e f g : {s : Finset (Option (Option (Fin n))) // s.card = 2}) (h : (e.val ∩ f.val).card = 1)
    (hg : g.val = symmDiff e.val f.val) :
    ∃ i j k, ∃ (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      e = edge i j hij ∧ f = edge j k hjk ∧ g = edge i k hik := by
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp h
  have hjmem : j ∈ e.val ∩ f.val := hj.symm ▸ (by simp)
  obtain ⟨i,hij,he⟩ := pair_through e j (Finset.mem_inter.mp hjmem).1
  obtain ⟨k,hkj,hf⟩ := pair_through f j (Finset.mem_inter.mp hjmem).2
  have hf' : f = edge j k hkj.symm := hf.trans (edge_comm _ _ hkj)
  have hik : i ≠ k := by
    intro hik
    subst k
    have hef : e.val = f.val := by rw [he,hf]
    rw [hef,Finset.inter_self,f.property] at h
    norm_num at h
  refine ⟨i,j,k,hij,hkj.symm,hik,he,hf',?_⟩
  apply Subtype.ext
  rw [hg,he,hf']
  ext v
  simp only [edge,Finset.mem_symmDiff,Finset.mem_insert,Finset.mem_singleton]
  grind

private def Svec {n : ℕ} : Option ((Option (Option (Bool × Fin n)))) → ℝ
  | some (some (some _)) => 1
  | _ => 0
private def Zvec {n : ℕ} : Option ((Option (Option (Bool × Fin n)))) → ℝ
  | some (some none) => 1
  | _ => 0
private def Fvec (n : ℕ) (x : ℝ) : Option ((Option (Option (Bool × Fin n)))) → ℝ
  | some none => 1
  | some (some none) => q n x
  | some (some (some _)) => p n x
  | none => 0

private def Avec {n : ℕ} (i : Fin n) : Option ((Option (Option (Bool × Fin n)))) → ℝ
  | some (some (some (_,j))) => (if i = j then 1 else 0) - 1 / (n : ℝ)
  | _ => 0
private def Bvec {n : ℕ} (i : Fin n) : Option ((Option (Option (Bool × Fin n)))) → ℝ
  | some (some (some (side,j))) => (if side then -1 else 1) * ((if i = j then 1 else 0) - 1 / (n : ℝ))
  | _ => 0

private def residualR (n : ℕ) (x : ℝ) := q n x * (1 - q n x)
private def residualT (n : ℕ) (x : ℝ) := q n x * (1/4 - p n x)
private def residualK (n : ℕ) (x : ℝ) := (q n x)^3 * (4*p0 n - c n x*(c n x-1/(2*(n : ℝ)))) / residualR n x

private def Gvec (n : ℕ) (x : ℝ) (t : Option ((Option (Option (Bool × Fin n))))) := Zvec t + (residualT n x / residualR n x) * Svec t

private def gramMoment (n : ℕ) (x : ℝ) : Matrix (Option ((Option (Option (Bool × Fin n))))) (Option ((Option (Option (Bool × Fin n))))) ℝ :=
  Matrix.vecMulVec (Fvec n x) (star (Fvec n x)) + residualR n x • Matrix.vecMulVec (Gvec n x) (star (Gvec n x)) + residualK n x • Matrix.vecMulVec Svec (star Svec) +
    alpha n x • (∑ i : Fin n, Matrix.vecMulVec (Avec i) (star (Avec i))) + beta n x • (∑ i : Fin n, Matrix.vecMulVec (Bvec i) (star (Bvec i)))

private theorem gramMoment_psd (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    (gramMoment n x).PosSemidef := by
  obtain ⟨ha,hb,hr,hk⟩ := block_coefficients_pos n hn x hxL hxU
  have hq := (parameter_bounds n hn x hxL hxU).1
  have hkr : 0 ≤ residualK n x := by unfold residualK residualR; positivity
  have hsumA : (∑ i : Fin n, Matrix.vecMulVec (Avec i) (star (Avec i))).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _)
  have hsumB : (∑ i : Fin n, Matrix.vecMulVec (Bvec i) (star (Bvec i))).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _)
  exact ((((Matrix.posSemidef_vecMulVec_self_star _).add ((Matrix.posSemidef_vecMulVec_self_star _).smul hr.le)).add ((Matrix.posSemidef_vecMulVec_self_star _).smul hkr)).add
    (hsumA.smul ha.le)).add (hsumB.smul hb.le)

private def moment (n : ℕ) (x : ℝ) : Matrix (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) ℝ :=
  (gramMoment n x).submatrix decode decode

private theorem moment_psd (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    (moment n x).PosSemidef := (gramMoment_psd n hn x hxL hxU).submatrix _

private lemma covariance (n : ℕ) (hn : 3 ≤ n) (i j : Fin n) :
    (∑ k : Fin n, (((if k = i then 1 else 0) : ℝ) - 1/(n : ℝ)) *
      (((if k = j then 1 else 0) : ℝ) - 1/(n : ℝ))) =
    (if i = j then 1 else 0) - 1/(n : ℝ) := by
  classical
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum]
  simp [ite_mul,Finset.sum_ite, hN, eq_comm]
  all_goals ring

private lemma residualK_eq (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    residualK n x = p n x * c n x * q n x - (residualT n x)^2 / residualR n x := by
  have hr : residualR n x ≠ 0 := ne_of_gt (block_coefficients_pos n hn x hxL hxU).2.2.1
  unfold residualK
  rw [← residual_determinant n hn x]
  change ((p n x*c n x*q n x)*residualR n x - (residualT n x)^2)/residualR n x = _
  rw [sub_div,mul_div_cancel_right₀ _ hr]

private lemma alpha_add_beta (n : ℕ) (hn : 3 ≤ n) (x : ℝ) : alpha n x + beta n x = p n x/2 := by
  have hN : (n : ℝ) - 1 ≠ 0 := by
    have h : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold alpha beta d
  field_simp
  ring

@[simp] private theorem gram_ident (n : ℕ) (x : ℝ) (j : Option ((Option (Option (Bool × Fin n))))) :
    gramMoment n x (some ident) j = Fvec n x j := by
  simp [gramMoment,ident,Matrix.vecMulVec,star_trivial,Fvec,Gvec,Zvec,Svec,Avec,Bvec,Matrix.sum_apply]

@[simp] private theorem gram_zero (n : ℕ) (x : ℝ) (j : Option ((Option (Option (Bool × Fin n))))) :
    gramMoment n x none j = 0 := by
  simp [gramMoment,Matrix.vecMulVec,star_trivial,Fvec,Gvec,Zvec,Svec,Avec,Bvec,Matrix.sum_apply]

@[simp] private theorem gram_center_center (n : ℕ) (x : ℝ) :
    gramMoment n x (some center) (some center) = q n x := by
  simp [gramMoment,center,Matrix.vecMulVec,star_trivial,Fvec,Gvec,Zvec,Svec,Avec,Bvec,Matrix.sum_apply,residualR]
  ring

@[simp] private theorem gram_center_spoke (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (side : Bool) (i : Fin n) :
    gramMoment n x (some center) (some (spoke side i)) = q n x/4 := by
  have hr : residualR n x ≠ 0 := ne_of_gt (block_coefficients_pos n hn x hxL hxU).2.2.1
  simp [gramMoment,center,spoke,Matrix.vecMulVec,star_trivial,Fvec,Gvec,Zvec,Svec,Avec,Bvec,Matrix.sum_apply]
  unfold residualT
  field_simp
  ring

private lemma sum_A_entries (n : ℕ) (hn : 3 ≤ n) (side side' : Bool) (i j : Fin n) :
    (∑ k : Fin n, Matrix.vecMulVec (Avec k) (star (Avec k))) (some (spoke side i)) (some (spoke side' j)) =
      (if i = j then 1 else 0) - 1/(n : ℝ) := by
  rw [Matrix.sum_apply]
  exact covariance n hn i j

private lemma sum_B_entries (n : ℕ) (hn : 3 ≤ n) (side side' : Bool) (i j : Fin n) :
    (∑ k : Fin n, Matrix.vecMulVec (Bvec k) (star (Bvec k))) (some (spoke side i)) (some (spoke side' j)) =
      (if side then -1 else 1) * (if side' then -1 else 1) *
        ((if i = j then 1 else 0) - 1/(n : ℝ)) := by
  rw [Matrix.sum_apply]
  change (∑ k : Fin n, ((if side then (-1 : ℝ) else 1)*((if k=i then 1 else 0)-1/(n : ℝ))) *
    ((if side' then (-1 : ℝ) else 1)*((if k=j then 1 else 0)-1/(n : ℝ)))) = _
  rw [← covariance n hn i j,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem gram_spokes (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (side side' : Bool) (i j : Fin n) :
    gramMoment n x (some (spoke side i)) (some (spoke side' j)) =
    p n x * p0 n + (if side = side' then alpha n x + beta n x else alpha n x - beta n x) *
      ((if i = j then 1 else 0) - 1/(n : ℝ)) := by
  have hr : residualR n x ≠ 0 := ne_of_gt (block_coefficients_pos n hn x hxL hxU).2.2.1
  simp only [gramMoment,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    sum_A_entries n hn side side' i j,sum_B_entries n hn side side' i j]
  simp only [Matrix.vecMulVec,Matrix.of_apply,star_trivial,Matrix.of_apply,star_trivial,Fvec,Gvec,Zvec,Svec,spoke,zero_add,mul_one,one_mul]
  rw [residualK_eq n hn x hxL hxU]
  cases side <;> cases side' <;> norm_num only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true,not_false_eq_true] <;>
    unfold residualT <;> field_simp [hr] <;> simp only [p] <;> ring

private theorem gram_same_side (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (side : Bool) (i j : Fin n) :
    gramMoment n x (some (spoke side i)) (some (spoke side j)) = if i = j then p n x else p n x/2 := by
  rw [gram_spokes n hn x hxL hxU,if_pos rfl,alpha_add_beta n hn x]
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  split_ifs <;> unfold p0 <;> field_simp <;> ring

private theorem gram_opposite_side (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (i j : Fin n) :
    gramMoment n x (some (spoke false i)) (some (spoke true j)) =
      if i = j then p n x/2 - q n x/4 else d n x := by
  rw [gram_spokes n hn x hxL hxU,if_neg Bool.false_ne_true]
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hNm : (n : ℝ) - 1 ≠ 0 := by
    have h : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  split_ifs <;> unfold alpha beta d p0 <;> field_simp <;> ring

private theorem gram_symmetric (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    (gramMoment n x).IsSymm := Matrix.isHermitian_iff_isSymm.mp (gramMoment_psd n hn x hxL hxU).1

private theorem gram_zero_right (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (j : Option ((Option (Option (Bool × Fin n))))) : gramMoment n x j none = 0 := by
  rw [(gram_symmetric n hn x hxL hxU).apply,gram_zero]

private theorem gram_spoke_center (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (side : Bool) (i : Fin n) :
    gramMoment n x (some (spoke side i)) (some center) = q n x/4 := by
  rw [(gram_symmetric n hn x hxL hxU).apply,gram_center_spoke n hn x hxL hxU]

private theorem gram_opposite_reverse (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (i j : Fin n) :
    gramMoment n x (some (spoke true i)) (some (spoke false j)) =
      if i = j then p n x/2 - q n x/4 else d n x := by
  rw [(gram_symmetric n hn x hxL hxU).apply,gram_opposite_side n hn x hxL hxU]
  split_ifs <;> simp_all

private lemma first_moment_bounds {n : ℕ} (M : Matrix (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) ℝ)
    (hM : npa1Feasible M) (e : {s : Finset (Option (Option (Fin n))) // s.card = 2}) : 0 ≤ M none (some e) ∧ M none (some e) ≤ 1 := by
  classical
  obtain ⟨hs,hp,h11,hd,ha⟩ := hM
  have h0 : 0 ≤ M none (some e) := hd e ▸ hp.diag_nonneg (i := some e)
  refine ⟨h0,?_⟩
  have hq := hp.dotProduct_mulVec_nonneg (Pi.single none 1 - Pi.single (some e) 1)
  simp only [star_trivial,Matrix.mulVec,dotProduct,Pi.sub_apply] at hq
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum] at hq
  simp [Pi.single_apply, Finset.sum_ite, h11, hd e, hs.apply none (some e)] at hq
  linarith

private lemma objective_bounded {n : ℕ} (x : ℝ) (M : Matrix (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) ℝ)
    (hM : npa1Feasible M) : objective x M ≤ ∑ e : {s : Finset (Option (Option (Fin n))) // s.card = 2}, |crownWeight n x e| := by
  unfold objective
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨h0,h1⟩ := first_moment_bounds M hM e
  calc
    crownWeight n x e * M none (some e) ≤ |crownWeight n x e| * M none (some e) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |crownWeight n x e| := by simpa using mul_le_mul_of_nonneg_left h1 (abs_nonneg (crownWeight n x e))

private lemma objective_le_value {n : ℕ} (x : ℝ) (M : Matrix (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) (Option ({s : Finset (Option (Option (Fin n))) // s.card = 2})) ℝ)
    (hM : npa1Feasible M) : objective x M ≤ npa1Value n x := by
  apply le_csSup
  · refine ⟨∑ e : {s : Finset (Option (Option (Fin n))) // s.card = 2}, |crownWeight n x e|,?_⟩
    rintro r ⟨N,hN,rfl⟩
    exact objective_bounded x N hN
  · exact ⟨M,hM,rfl⟩

@[simp] private lemma encode_center_reverse (n : ℕ) (h : b n ≠ a n) : encode (edge (b n) (a n) h) = some center := by
  rw [edge_comm]; exact encode_center n
@[simp] private lemma encode_left_reverse {n : ℕ} (i : Fin n) (h : leaf i ≠ a n) :
    encode (edge (leaf i) (a n) h) = some (spoke false i) := by
  rw [edge_comm]; exact encode_left i
@[simp] private lemma encode_right_reverse {n : ℕ} (i : Fin n) (h : leaf i ≠ b n) :
    encode (edge (leaf i) (b n) h) = some (spoke true i) := by
  rw [edge_comm]; exact encode_right i

@[simp] private lemma encode_center_raw (n : ℕ) (h : (none : (Option (Option (Fin n)))) ≠ (some none : (Option (Option (Fin n))))) :
    encode (edge (none) (some none) h) = some center := encode_center n
@[simp] private lemma encode_center_reverse_raw (n : ℕ) (h : (some none : (Option (Option (Fin n)))) ≠ (none : (Option (Option (Fin n))))) :
    encode (edge (some none) (none) h) = some center := encode_center_reverse n h
@[simp] private lemma encode_left_raw (n : ℕ) (i : Fin n) (h : (none : (Option (Option (Fin n)))) ≠ (some (some i) : (Option (Option (Fin n))))) :
    encode (edge (none) (some (some i)) h) = some (spoke false i) := encode_left i
@[simp] private lemma encode_left_reverse_raw (n : ℕ) (i : Fin n) (h : (some (some i) : (Option (Option (Fin n)))) ≠ (none : (Option (Option (Fin n))))) :
    encode (edge (some (some i)) (none) h) = some (spoke false i) := encode_left_reverse i h
@[simp] private lemma encode_right_raw (n : ℕ) (i : Fin n) (h : (some none : (Option (Option (Fin n)))) ≠ (some (some i) : (Option (Option (Fin n))))) :
    encode (edge (some none) (some (some i)) h) = some (spoke true i) := encode_right i
@[simp] private lemma encode_right_reverse_raw (n : ℕ) (i : Fin n) (h : (some (some i) : (Option (Option (Fin n)))) ≠ (some none : (Option (Option (Fin n))))) :
    encode (edge (some (some i)) (some none) h) = some (spoke true i) := encode_right_reverse i h
@[simp] private lemma encode_leaves_raw (n : ℕ) (i : Fin n) (j : Fin n) (h : (some (some i) : (Option (Option (Fin n)))) ≠ (some (some j) : (Option (Option (Fin n))))) :
    encode (edge (some (some i)) (some (some j)) h) = none := encode_leaves i j h

private theorem moment_triangle (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n)
    (i j k : (Option (Option (Fin n)))) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    moment n x (some (edge i j hij)) (some (edge j k hjk)) +
      moment n x (some (edge j k hjk)) (some (edge i j hij)) =
      (moment n x none (some (edge i j hij)) + moment n x none (some (edge j k hjk)) -
        moment n x none (some (edge i k hik))) / 2 := by
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;> rcases k with _ | (_ | k)
  all_goals try exact False.elim (hij rfl)
  all_goals try exact False.elim (hjk rfl)
  all_goals try exact False.elim (hik rfl)
  all_goals simp only [ne_eq,Option.some.injEq] at hij hjk hik
  all_goals simp only [moment,Matrix.submatrix_apply,decode,encode_center,encode_left,encode_right,encode_leaves,
    encode_center_raw,encode_center_reverse_raw,encode_left_raw,encode_left_reverse_raw,
    encode_right_raw,encode_right_reverse_raw,encode_leaves_raw,
    encode_center_reverse,encode_left_reverse,encode_right_reverse,
    gram_ident,gram_zero,gram_zero_right n hn x hxL hxU,
    gram_center_spoke n hn x hxL hxU,gram_spoke_center n hn x hxL hxU,
    gram_same_side n hn x hxL hxU,gram_opposite_side n hn x hxL hxU,
    gram_opposite_reverse n hn x hxL hxU]
  all_goals simp [Fvec,center,spoke,ident,hij,hjk,hik,eq_comm]
  all_goals ring

private theorem moment_feasible (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    npa1Feasible (moment n x) := by
  have hp := moment_psd n hn x hxL hxU
  refine ⟨Matrix.isHermitian_iff_isSymm.mp hp.1,hp,?_,?_,?_⟩
  · simp only [moment,Matrix.submatrix_apply,decode,gram_ident]
    rfl
  · intro e
    rcases pair_shapes e with rfl | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,j,h,rfl⟩ <;>
      simp only [moment,Matrix.submatrix_apply,decode,encode_center,encode_left,encode_right,encode_leaves,
        gram_ident,gram_center_center,gram_same_side n hn x hxL hxU,
        gram_zero]
    all_goals simp [Fvec,ident,center,spoke]
  · intro e f g h hg
    obtain ⟨i,j,k,hij,hjk,hik,rfl,rfl,rfl⟩ := adjacent_shapes e f g h hg
    exact moment_triangle n hn x hxL hxU i j k hij hjk hik

private def centralEdge (n : ℕ) : {s : Finset (Option (Option (Fin n))) // s.card = 2} := edge (a n) (b n) (a_ne_b n)
private def leftEdge {n : ℕ} (i : Fin n) : {s : Finset (Option (Option (Fin n))) // s.card = 2} := edge (a n) (leaf i) (a_ne_leaf i)
private def rightEdge {n : ℕ} (i : Fin n) : {s : Finset (Option (Option (Fin n))) // s.card = 2} := edge (b n) (leaf i) (b_ne_leaf i)
private def activeEdges (n : ℕ) : Finset ({s : Finset (Option (Option (Fin n))) // s.card = 2}) :=
  insert (centralEdge n) (Finset.univ.image leftEdge ∪ Finset.univ.image rightEdge)

private lemma leftEdge_injective (n : ℕ) : Function.Injective (@leftEdge n) := by
  intro i j h
  have hh := congrArg encode h
  simpa [leftEdge,spoke] using hh
private lemma rightEdge_injective (n : ℕ) : Function.Injective (@rightEdge n) := by
  intro i j h
  have hh := congrArg encode h
  simpa [rightEdge,spoke] using hh
private lemma central_left_ne {n : ℕ} (i : Fin n) : centralEdge n ≠ leftEdge i := by
  intro h
  have hh := congrArg encode h
  simpa [centralEdge,leftEdge,center,spoke] using hh
private lemma central_right_ne {n : ℕ} (i : Fin n) : centralEdge n ≠ rightEdge i := by
  intro h
  have hh := congrArg encode h
  simpa [centralEdge,rightEdge,center,spoke] using hh
private lemma left_right_ne {n : ℕ} (i j : Fin n) : leftEdge i ≠ rightEdge j := by
  intro h
  have hh := congrArg encode h
  simpa [leftEdge,rightEdge,spoke] using hh

private lemma active_disjoint (n : ℕ) :
    Disjoint (Finset.univ.image (@leftEdge n)) (Finset.univ.image (@rightEdge n)) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hf
  exact left_right_ne i j heq.symm

private lemma central_not_spokes (n : ℕ) :
    centralEdge n ∉ Finset.univ.image (@leftEdge n) ∪ Finset.univ.image (@rightEdge n) := by
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,not_or]
  constructor
  · rintro ⟨i,h⟩; exact central_left_ne i h.symm
  · rintro ⟨i,h⟩; exact central_right_ne i h.symm

private lemma objective_on_active (n : ℕ) (x : ℝ) :
    objective x (moment n x) = ∑ e ∈ activeEdges n, crownWeight n x e * moment n x none (some e) := by
  classical
  unfold objective
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e he hnot
  rcases pair_shapes e with rfl | ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,j,h,rfl⟩
  · exact False.elim (hnot (by simp [activeEdges,centralEdge]))
  · exact False.elim (hnot (by simp [activeEdges,leftEdge]))
  · exact False.elim (hnot (by simp [activeEdges,rightEdge]))
  · simp [crownWeight,edge,a,b,leaf]

private theorem moment_objective (n : ℕ) (hn : 3 ≤ n) (x : ℝ) :
    objective x (moment n x) = (n : ℝ) + 1 + (x - L n)^2 / (32*(n : ℝ)) := by
  classical
  rw [objective_on_active]
  unfold activeEdges
  rw [Finset.sum_insert (central_not_spokes n),Finset.sum_union (active_disjoint n)]
  rw [Finset.sum_image (fun i _ j _ h => leftEdge_injective n h),
      Finset.sum_image (fun i _ j _ h => rightEdge_injective n h)]
  simp only [centralEdge,leftEdge,rightEdge,moment,Matrix.submatrix_apply,decode,
    encode_center,encode_left,encode_right,gram_ident]
  simp [crownWeight,edge,a,b,leaf,Fvec,ident,center,spoke]
  all_goals nlinarith [objective_formula n hn x]

theorem constructed_value_gap (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hxL : L n < x) (hxU : x < U n) :
    (n : ℝ)+1 < npa1Value n x := by
  have hm := moment_feasible n hn x hxL hxU
  have hle := objective_le_value x (moment n x) hm
  rw [moment_objective n hn x] at hle
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgap : 0 < (x-L n)^2/(32*(n : ℝ)) := by
    exact div_pos (sq_pos_of_pos (sub_pos.mpr hxL)) (by positivity)
  linarith

end D5.S3.Quantum.Optimization.WeightedCrownMomentCertificate
