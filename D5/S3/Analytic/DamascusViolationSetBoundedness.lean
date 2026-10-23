/- GID: D5/S3/Analytic/DamascusViolationSetBoundedness
   generality: G
   mirror-B: D5/B/S3/Analytic/DamascusViolationSetBoundedness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Classifies boundedness of all positive product-one Damascus violation sets. -/

/-
admission_basis: open-problem-resolution (#18584; Proved)
escape_witness: none
Direct frozen dependencies: none for every declaration below.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19895
The public definitions term, H and I are the source expressions; claim states
this repository's answer to the source's question. The scalar and confinement
proofs use Mathlib's finite-product, order and norm results.
Utility: no finite computation refutes claim; the numerical scalar evaluations
support a proof of the classification, so this module has utility: none.
term: proof_shape: bind-only; escape_witness: none; consumers: I, scalar helpers.
H: proof_shape: bind-only; escape_witness: none; consumers: I, small_coordinate.
I: proof_shape: bind-only; escape_witness: none; consumers: claim, bounded and unbounded helpers.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
escape: proof_shape: bind-only; escape_witness: none; consumers: escape_mem, unbounded_of_middle.
denom_pos: proof_shape: bind-only; escape_witness: none; consumers: term_gt_neg_one, term_pos, term_nonpos, term_lt_inv, term_small, term_mono, term_one_bound, term_four_bound, term_uniform_bound.
term_gt_neg_one: proof_shape: bind-only; escape_witness: none; consumers: escape_mem.
term_pos: proof_shape: bind-only; escape_witness: none; consumers: escape_mem.
term_nonpos: proof_shape: bind-only; escape_witness: none; consumers: term_uniform_bound, bounded_cells.
term_lt_inv: proof_shape: bind-only; escape_witness: none; consumers: term_four_bound, term_uniform_bound, bounded_of_upper.
term_small: proof_shape: bind-only; escape_witness: none; consumers: bounded_of_upper.
term_mono: proof_shape: bind-only; escape_witness: none; consumers: bounded_cells, unbounded_cells.
term_one_bound: proof_shape: bind-only; escape_witness: none; consumers: bounded_cells.
term_four_bound: proof_shape: bind-only; escape_witness: none; consumers: bounded_cells.
term_uniform_bound: proof_shape: bind-only; escape_witness: none; consumers: bounded_cells.
middle_two_one: proof_shape: bind-only; escape_witness: none; consumers: unbounded_cells.
middle_two_two: proof_shape: bind-only; escape_witness: none; consumers: unbounded_cells.
middle_three_halves: proof_shape: bind-only; escape_witness: none; consumers: unbounded_cells.
small_coordinate: proof_shape: bind-only; escape_witness: none; consumers: bounded_of_upper.
bounded_of_upper: proof_shape: bind-only; escape_witness: none; consumers: bounded_cells.
bounded_one: proof_shape: bind-only; escape_witness: none; consumers: bounded_cells.
bounded_cells: proof_shape: bind-only; escape_witness: none; consumers: result.
escape_mem: proof_shape: bind-only; escape_witness: none; consumers: unbounded_of_middle.
unbounded_of_middle: proof_shape: bind-only; escape_witness: none; consumers: unbounded_cells.
unbounded_cells: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
-/

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace D5.S3.Analytic.DamascusViolationSetBoundedness

/-- The summand `(x^n - 1) / (x^{n+1} + 1)` of the generalised Damascus inequality (1). -/
noncomputable def term (n : ℕ) (x : ℝ) : ℝ :=
  (x ^ n - 1) / (x ^ (n + 1) + 1)

/-- `H_m`: positive `m`-tuples with product `1`. -/
def H (m : ℕ) : Set (Fin m → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∏ j, x j = 1}

/-- `I_n^m`: the points of `H_m` violating (1), i.e. with `Σ_j (x_j^n - 1)/(x_j^{n+1} + 1) > 0`. -/
def I (n m : ℕ) : Set (Fin m → ℝ) :=
  {x | x ∈ H m ∧ 0 < ∑ j, term n (x j)}

/-- Question (ii) of Section 5, answered for all `m, n ≥ 1`: `I_n^m` is bounded exactly when `m ≤ 3`,
or `m = 4` and `n ≤ 4`, or `m ∈ {5, 6}` and `n = 1`. -/
def claim : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    (Bornology.IsBounded (I n m) ↔ m ≤ 3 ∨ (m = 4 ∧ n ≤ 4) ∨ ((m = 5 ∨ m = 6) ∧ n = 1))

private theorem denom_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < x ^ (n+1) + 1 :=
  add_pos (pow_pos hx _) zero_lt_one

private theorem term_gt_neg_one (n : ℕ) {x : ℝ} (hx : 0 < x) : -1 < term n x := by
  rw [term, lt_div_iff₀ (denom_pos n hx)]
  nlinarith [pow_pos hx n, pow_pos hx (n+1)]

private theorem term_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) : 0 < term n x :=
  div_pos (sub_pos.mpr (one_lt_pow₀ hx (by omega))) (denom_pos n (lt_trans zero_lt_one hx))

private theorem term_nonpos (n : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : term n x ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (pow_le_one₀ hx.le hx1)) (denom_pos n hx).le

private theorem term_lt_inv (n : ℕ) {x : ℝ} (hx : 0 < x) : term n x < 1/x := by
  rw [term, div_lt_div_iff₀ (denom_pos n hx) hx, pow_succ]
  nlinarith

private theorem term_small {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    term n x + 1 ≤ 2*x := by
  have hp : x^n ≤ x := by simpa using pow_le_pow_of_le_one hx.le hx1 hn
  have hq : x^(n+1) ≤ x := by simpa using pow_le_pow_of_le_one hx.le hx1 (show 1 ≤ n+1 by omega)
  have hprod : 0 ≤ 2*x*x^(n+1) := mul_nonneg (by positivity) (pow_nonneg hx.le _)
  have h : term n x ≤ 2*x-1 := by
    rw [term, div_le_iff₀ (denom_pos n hx)]
    nlinarith
  linarith

private theorem term_mono {n k : ℕ} (hnk : n ≤ k) {x : ℝ} (hx : 1 ≤ x) : term n x ≤ term k x := by
  have hp := pow_le_pow_right₀ hx hnk
  rw [term, term, div_le_div_iff₀ (denom_pos n (lt_of_lt_of_le zero_lt_one hx))
    (denom_pos k (lt_of_lt_of_le zero_lt_one hx))]
  simp only [pow_succ]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ x+1 by linarith)]

private theorem term_one_bound {x : ℝ} (hx : 0 < x) : term 1 x ≤ (5:ℝ)/24 := by
  rw [term, div_le_iff₀ (denom_pos 1 hx)]
  norm_num only [pow_one, Nat.reduceAdd]
  nlinarith [sq_nonneg (x - 12/5)]

private theorem term_four_bound {x : ℝ} (hx : 0 < x) : term 4 x ≤ (4999:ℝ)/10000 := by
  by_cases h3 : x ≤ 3
  · have h5 : x^5 ≤ (243:ℝ) := by exact (pow_le_pow_left₀ hx.le h3 5).trans_eq (by norm_num)
    have hc : 0 ≤ (x-8/5)^2 * (x^3 + 6/5*x^2 + 32/25*x + 128/125) := by positivity
    have hid : x^5 - 2*x^4 + 3 =
        (x-8/5)^2 * (x^3 + 6/5*x^2 + 32/25*x + 128/125) + 1183/3125 := by ring
    rw [term, div_le_iff₀ (denom_pos 4 hx)]
    norm_num only [Nat.reduceAdd]
    linarith
  · have ht := term_lt_inv 4 hx
    have hinv : 1/x < (1:ℝ)/3 := one_div_lt_one_div_of_lt (by norm_num) (lt_of_not_ge h3)
    linarith

private theorem term_uniform_bound (n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x, 0 < x → term n x ≤ c := by
  let C : ℝ := 2^(n+1)+1
  have hC : 1 < C := by dsimp [C]; have := pow_pos (show (0:ℝ) < 2 by norm_num) (n+1); linarith
  refine ⟨1-1/C, by have := (div_lt_one₀ (by linarith : 0 < C)).mpr hC; linarith,
    by have := one_div_pos.mpr (by linarith : 0 < C); linarith, ?_⟩
  intro x hx
  by_cases hx1 : x ≤ 1
  · exact (term_nonpos n hx hx1).trans (by have := (div_lt_one₀ (by linarith : 0 < C)).mpr hC; linarith)
  by_cases hx2 : x ≤ 2
  · have hp : x^(n+1)+1 ≤ C := by
      dsimp [C]; linarith [pow_le_pow_left₀ hx.le hx2 (n+1)]
    have hnum : x^n-1 ≤ x^(n+1) := by
      have := pow_le_pow_right₀ (le_of_not_ge hx1) (show n ≤ n+1 by omega)
      linarith
    have hden := denom_pos n hx
    have hi : 1/C ≤ 1/(x^(n+1)+1) := one_div_le_one_div_of_le hden hp
    have hid : term n x ≤ 1-1/(x^(n+1)+1) := by
      rw [term, le_sub_iff_add_le, ← add_div, div_le_one₀ hden]
      linarith
    linarith
  · have hi := term_lt_inv n hx
    have hx2' : 2 < x := lt_of_not_ge hx2
    have hinv : 1/x ≤ (1:ℝ)/2 := (one_div_le_one_div_of_le (by norm_num) hx2'.le)
    have h2 : 2 ≤ C := by
      dsimp [C]
      have := one_le_pow₀ (n := n+1) (show (1:ℝ) ≤ 2 by norm_num)
      linarith
    have hiC : 1/C ≤ (1:ℝ)/2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith

private theorem middle_two_one : term 1 2 = (1:ℝ)/5 := by norm_num [term]
private theorem middle_two_two : term 2 2 = (1:ℝ)/3 := by norm_num [term]
private theorem middle_three_halves : (1:ℝ)/2 < term 5 ((3:ℝ)/2) := by norm_num [term]

private theorem small_coordinate {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ H m)
    {K : ℝ} (hK : 1 < K) (i : Fin m) (hi : K^(m-1) < x i) :
    ∃ j, x j < 1/K := by
  classical
  by_contra h
  push Not at h
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hp : (1/K)^(m-1) ≤ ∏ j ∈ Finset.univ.erase i, x j := by
    simpa using Finset.prod_le_prod₀ (fun j (_ : j ∈ Finset.univ.erase i) =>
      (show 0 ≤ 1/K by positivity)) (fun j _ => h j)
  have he : (∏ j ∈ Finset.univ.erase i, x j) * x i = 1 := by
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]; exact hx.2
  have hpow : 0 < (1/K)^(m-1) := pow_pos (one_div_pos.mpr hK0) _
  have hid : (1/K)^(m-1) * K^(m-1) = (1:ℝ) := by
    rw [← mul_pow]; simp [ne_of_gt hK0]
  have hmul := mul_lt_mul_of_pos_left hi hpow
  have hle := mul_le_mul_of_nonneg_right hp (hx.1 i).le
  linarith

private theorem bounded_of_upper {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    {c : ℝ} (hmc : (m-2:ℕ)*c < 1)
    (hu : ∀ x : ℝ, 0 < x → term n x ≤ c) : Bornology.IsBounded (I n m) := by
  classical
  let d : ℝ := 1-(m-2:ℕ)*c
  have hd : 0 < d := sub_pos.mpr hmc
  let K : ℝ := 1+8/d
  have hK : 1 < K := by dsimp [K]; have := div_pos (show (0:ℝ) < 8 by norm_num) hd; linarith
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hKd : d*K = d+8 := by dsimp [K]; field_simp
  have hgap : 3/K < d := (div_lt_iff₀ hK0).mpr (by nlinarith)
  let B : ℝ := K^(m-1)
  have hKB : K ≤ B := by
    simpa [B] using pow_le_pow_right₀ hK.le (show 1 ≤ m-1 by omega)
  have hB : 0 ≤ B := (lt_of_lt_of_le hK0 hKB).le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B, fun x hx => (pi_norm_le_iff_of_nonneg hB).mpr fun i => ?_⟩
  rw [Real.norm_eq_abs, abs_of_pos (hx.1.1 i)]
  by_contra hi
  have hiB : B < x i := lt_of_not_ge hi
  obtain ⟨j, hj⟩ := small_coordinate hx.1 hK i hiB
  have hix : K < x i := lt_of_le_of_lt hKB hiB
  have hj1 : x j ≤ 1 := hj.le.trans ((div_lt_one₀ hK0).mpr hK).le
  have hji : j ≠ i := by
    intro h; subst j
    linarith
  have hti : term n (x i) < 1/K :=
    (term_lt_inv n (hx.1.1 i)).trans (one_div_lt_one_div_of_lt hK0 hix)
  have htj := term_small hn (hx.1.1 j) hj1
  have hrest : (∑ l ∈ (Finset.univ.erase i).erase j, term n (x l)) ≤ (m-2:ℕ)*c := by
    calc
      _ ≤ ∑ _l ∈ (Finset.univ.erase i).erase j, c := Finset.sum_le_sum (fun l _ => hu _ (hx.1.1 l))
      _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩), Nat.sub_sub]
  have hsum := hx.2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)] at hsum
  dsimp [d] at hgap
  simp only [div_eq_mul_inv] at hgap hti hj
  linarith only [hgap, hti, htj, hrest, hsum, hj]

private theorem bounded_one (n : ℕ) : Bornology.IsBounded (I n 1) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, fun x hx => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_⟩
  have hprod := hx.1.2
  simp at hprod
  have hj : j = 0 := Fin.eq_zero j
  simp [hj, hprod]

private theorem bounded_cells {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcell : m ≤ 3 ∨ (m=4 ∧ n≤4) ∨ ((m=5 ∨ m=6) ∧ n=1)) :
    Bornology.IsBounded (I n m) := by
  by_cases hm1 : m = 1
  · subst m; exact bounded_one n
  have hm2 : 2 ≤ m := by omega
  rcases hcell with h | ⟨rfl, hn4⟩ | ⟨hm56, rfl⟩
  · obtain ⟨c, hc0, hc1, hu⟩ := term_uniform_bound n
    apply bounded_of_upper hm2 hn (c := c) ?_ hu
    have hcast : ((m-2:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show m-2 ≤ 1 by omega)
    nlinarith
  · apply bounded_of_upper (by omega) hn (c := (4999:ℝ)/10000) (by norm_num)
    intro x hx
    by_cases hx1 : x ≤ 1
    · exact (term_nonpos n hx hx1).trans (by norm_num)
    · exact (term_mono hn4 (le_of_not_ge hx1)).trans (term_four_bound hx)
  · apply bounded_of_upper hm2 (by omega) (c := (5:ℝ)/24) ?_ (fun _ hx => term_one_bound hx)
    rcases hm56 with rfl | rfl <;> norm_num

private noncomputable def escape (k : ℕ) (r t : ℝ) : Fin (k+2) → ℝ :=
  Fin.cases t (Fin.cases (1/(t*r^k)) (fun _ => r))

private theorem escape_mem {n k : ℕ} (hn : 1 ≤ n) {r t : ℝ} (hr : 0 < r) (ht : 1 < t)
    (hmiddle : 1 ≤ (k:ℝ)*term n r) : escape k r t ∈ I n (k+2) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hs : 0 < 1/(t*r^k) := by positivity
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    refine Fin.cases ht0 (fun j => ?_) j
    exact Fin.cases hs (fun _ => hr) j
  · simp [escape, Fin.prod_univ_succ]
    field_simp
  · have hfirst := term_pos hn ht
    have hsecond := term_gt_neg_one n hs
    simp only [escape, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith

private theorem unbounded_of_middle {n k : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (hmiddle : 1 ≤ (k:ℝ)*term n r) : ¬ Bornology.IsBounded (I n (k+2)) := by
  intro hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  let t : ℝ := max 2 (R+1)
  have ht : 1 < t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hmem := escape_mem hn hr ht hmiddle
  have hnorm := (norm_le_pi_norm (escape k r t) 0).trans (hR _ hmem)
  have hpos : 0 < t := lt_trans zero_lt_one ht
  simp only [escape, Fin.cases_zero, Real.norm_eq_abs, abs_of_pos hpos] at hnorm
  have := le_max_right (2:ℝ) (R+1)
  change R+1 ≤ t at this
  linarith

private theorem unbounded_cells {m n : ℕ} (hn : 1 ≤ n)
    (hcell : ¬ (m ≤ 3 ∨ (m=4 ∧ n≤4) ∨ ((m=5 ∨ m=6) ∧ n=1))) :
    ¬ Bornology.IsBounded (I n m) := by
  have hm : 4 ≤ m := by omega
  have he : m = (m-2)+2 := by omega
  rw [he]
  by_cases hn5 : 5 ≤ n
  · apply unbounded_of_middle hn (r := (3:ℝ)/2) (by norm_num)
    have hval := (middle_three_halves).le.trans (term_mono hn5 (by norm_num))
    have hk : (2:ℝ) ≤ (m-2:ℕ) := by exact_mod_cast (show 2 ≤ m-2 by omega)
    nlinarith
  by_cases hn1 : n = 1
  · subst n
    apply unbounded_of_middle (by omega) (r := 2) (by norm_num)
    rw [middle_two_one]
    have hk : (5:ℝ) ≤ (m-2:ℕ) := by exact_mod_cast (show 5 ≤ m-2 by omega)
    linarith
  · apply unbounded_of_middle hn (r := 2) (by norm_num)
    have hval : (1:ℝ)/3 ≤ term n 2 := by
      rw [← middle_two_two]
      exact term_mono (by omega) (by norm_num)
    have hk : (3:ℝ) ≤ (m-2:ℕ) := by exact_mod_cast (show 3 ≤ m-2 by omega)
    nlinarith

theorem result : claim := by
  intro m n hm hn
  constructor
  · intro hb
    by_contra h
    exact unbounded_cells hn h hb
  · exact bounded_cells hm hn

end D5.S3.Analytic.DamascusViolationSetBoundedness
