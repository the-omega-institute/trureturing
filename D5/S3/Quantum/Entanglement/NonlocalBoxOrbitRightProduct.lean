/- GID: D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The right product maximizes CHSH over the PR-SR-I triangle orbit. -/

/-
   admission_basis: open-problem-resolution (#15165; Proved)
   Direct frozen dependencies: none (only pinned Mathlib imports).
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15358
   Utility none: universal real coefficients and arbitrary finite parenthesizations;
   multiplication-table calculations are consumed operation laws.
   prod_pr_pr: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_pr_sr: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_pr_i: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_sr_pr: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_sr_sr: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_sr_i: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_i_pr: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_i_sr: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_i_i: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_add_left: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_add_right: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_smul_left: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_smul_right: proof_shape: bind-only; escape_witness: none; consumer: prod_A
   prod_A: proof_shape: bind-only;
     escape_witness: none;
     consumer: eval_coordinates, rightPow_coordinates
   chsh_A: proof_shape: bind-only; escape_witness: none; consumer: whole_triangle_max
   hull_coordinates: proof_shape: bind-only; escape_witness: none; consumer: whole_triangle_max
   factor_nonneg: proof_shape: bind-only; escape_witness: none; consumer: K_star, root_rotation
   K_star: proof_shape: bind-only; escape_witness: none; consumer: ceval_K, root_straighten
   star_assoc_first: proof_shape: bind-only; escape_witness: none; consumer: root_straighten
   star_assoc_gap: proof_shape: bind-only; escape_witness: none; consumer: root_rotation
   root_rotation: proof_shape: bind-only; escape_witness: none; consumer: root_straighten
   right_mono: proof_shape: bind-only; escape_witness: none; consumer: iterRight_mono
   size_pos: proof_shape: content; escape_witness: none; consumer: ceval_max
   ceval_K: proof_shape: content; escape_witness: none; consumer: root_straighten, ceval_max
   iterRight_add: proof_shape: content; escape_witness: none; consumer: root_straighten
   iterRight_mono: proof_shape: content; escape_witness: none; consumer: root_straighten, ceval_max
   root_straighten: proof_shape: content; escape_witness: none; consumer: ceval_max
   cpower_succ: proof_shape: bind-only; escape_witness: none; consumer: iterRight_cpower
   iterRight_cpower: proof_shape: content; escape_witness: none; consumer: ceval_max
   ceval_max: proof_shape: content; escape_witness: none; consumer: whole_triangle_max
   eval_coordinates: proof_shape: content; escape_witness: none; consumer: whole_triangle_max
   rightPow_coordinates: proof_shape: content; escape_witness: none; consumer: whole_triangle_max
   whole_triangle_max: proof_shape: content; escape_witness: none; consumer: result
   result: proof_shape: content; escape_witness: none; consumer: settling result
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

noncomputable section

namespace D5.S3.Quantum.Entanglement.NonlocalBoxOrbitRightProduct

open scoped BigOperators


def PR : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) := fun a b x y => if a + b = x * y then 1 / 2 else 0
def P0 : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) := fun a b _ _ => if a = 0 ∧ b = 0 then 1 else 0
def P1 : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) := fun a b _ _ => if a = 1 ∧ b = 1 then 1 else 0
def SR : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) := (1 / 2 : ℝ) • (P0 + P1)
def Ibox : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) := fun _ _ _ _ => 1 / 4

def boxProd (P Q : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) :=
  fun a b x y =>
  ∑ a1 : Fin 2, ∑ a2 : Fin 2, ∑ b1 : Fin 2, ∑ b2 : Fin 2,
    P a1 b1 x y * Q a2 b2 (x * a1) (y * b1) *
      (if a = a1 + a2 then 1 else 0) * (if b = b1 + b2 then 1 else 0)

def chsh (P : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) : ℝ :=
  (1 / 4) * ∑ a : Fin 2, ∑ b : Fin 2, ∑ x : Fin 2,
    ∑ y : Fin 2 with a + b = x * y, P a b x y

inductive Paren where
  | leaf
  | node (l r : Paren)

def Paren.size : Paren → ℕ
  | .leaf => 1
  | .node l r => l.size + r.size

def eval (P : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) : Paren → (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
  | .leaf => P
  | .node l r => boxProd (eval P l) (eval P r)

def orbit (k : ℕ) (P : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) :
    Set (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) :=
  {Q | ∃ t : Paren, t.size = k ∧ Q = eval P t}

def rightPow (P : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) : ℕ → (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
  | 0 => P
  | 1 => P
  | k + 2 => boxProd (rightPow P (k + 1)) P

def claim : Prop := ∀ P : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ), P ∈ convexHull ℝ {PR, SR, Ibox} →
  3 / 4 ≤ chsh P → ∀ k : ℕ, 2 ≤ k →
  ∀ Q ∈ orbit k P, chsh Q ≤ chsh (rightPow P k)

private def A (u a : ℝ) : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) :=
  a • PR + (u - a) • SR + (1 - u) • Ibox

private theorem prod_pr_pr : boxProd PR PR = PR := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, PR, Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_pr_sr : boxProd PR SR = PR := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, PR, SR, P0, P1,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_pr_i : boxProd PR Ibox = Ibox := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, PR, Ibox,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_sr_pr : boxProd SR PR = (1 / 2 : ℝ) • PR + (1 / 2 : ℝ) • SR := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, PR, SR, P0, P1,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_sr_sr : boxProd SR SR = SR := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, SR, P0, P1,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_sr_i : boxProd SR Ibox = Ibox := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, SR, P0, P1, Ibox,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_i_pr : boxProd Ibox PR =
    (1 / 4 : ℝ) • PR + (-1 / 4 : ℝ) • SR + Ibox := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, PR, SR, P0, P1, Ibox,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_i_sr : boxProd Ibox SR = Ibox := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, SR, P0, P1, Ibox,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_i_i : boxProd Ibox Ibox = Ibox := by
  funext a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [boxProd, Ibox,
      Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]

private theorem prod_add_left (P Q R : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) :
    boxProd (P + Q) R = boxProd P R + boxProd Q R := by
  funext a b x y
  simp only [boxProd, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem prod_add_right (P Q R : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) :
    boxProd P (Q + R) = boxProd P Q + boxProd P R := by
  funext a b x y
  simp only [boxProd, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private theorem prod_smul_left (c : ℝ) (P Q : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) :
    boxProd (c • P) Q = c • boxProd P Q := by
  funext a b x y
  simp only [boxProd, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem prod_smul_right (c : ℝ) (P Q : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) :
    boxProd P (c • Q) = c • boxProd P Q := by
  funext a b x y
  simp only [boxProd, Pi.smul_apply, smul_eq_mul, mul_left_comm, mul_assoc, Finset.mul_sum]

private theorem prod_A (u a v b : ℝ) : boxProd (A u a) (A v b) =
    A (u * v) (a * v + (1 + u - 2 * a) * b / 4) := by
  simp only [A, prod_add_left, prod_add_right, prod_smul_left, prod_smul_right,
    prod_pr_pr, prod_pr_sr, prod_pr_i, prod_sr_pr, prod_sr_sr, prod_sr_i,
    prod_i_pr, prod_i_sr, prod_i_i]
  funext i j x y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem chsh_A (u a : ℝ) : chsh (A u a) = 1 / 2 + (u + a) / 4 := by
  simp only [chsh, Finset.sum_filter]
  norm_num [A, PR, SR, P0, P1, Ibox,
    Fin.sum_univ_two, Fin.mul_zero, Fin.zero_mul, Fin.one_mul, Fin.mul_one,
      (show (1 : Fin 2) + 1 = 0 by decide)]
  ring


private theorem hull_coordinates {P : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)}
    (hP : P ∈ convexHull ℝ {PR, SR, Ibox}) :
    ∃ r p : ℝ, 0 ≤ p ∧ p ≤ r ∧ r ≤ 1 ∧ P = A r p := by
  let S : Set (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) :=
  {P | ∃ r p : ℝ, 0 ≤ p ∧ p ≤ r ∧ r ≤ 1 ∧ P = A r p}
  have hs : {PR, SR, Ibox} ⊆ S := by
    intro P h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨1, 1, by norm_num, le_rfl, le_rfl, by simp [A]⟩
    · exact ⟨1, 0, le_rfl, by norm_num, le_rfl, by simp [A]⟩
    · exact ⟨0, 0, le_rfl, le_rfl, by norm_num, by simp [A]⟩
  have hc : Convex ℝ S := by
    rintro X ⟨u, a, ha, hau, hu, rfl⟩ Y ⟨v, b, hb, hbv, hv, rfl⟩
      s t hs ht hst
    refine ⟨s * u + t * v, s * a + t * b, ?_, ?_, ?_, ?_⟩
    · positivity
    · exact add_le_add (mul_le_mul_of_nonneg_left hau hs)
        (mul_le_mul_of_nonneg_left hbv ht)
    · nlinarith [mul_le_mul_of_nonneg_left hu hs,
        mul_le_mul_of_nonneg_left hv ht]
    · funext i j x y
      simp only [A, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (PR i j x y * 0 + Ibox i j x y) * hst
  exact convexHull_min hs hc hP


private def star (X Y : (ℝ × ℝ)) : (ℝ × ℝ) :=
  (X.1 * Y.1, X.2 * Y.1 + (1 + X.1 - 2 * X.2) * Y.2 / 4)

private def K (X : (ℝ × ℝ)) : Prop :=
  0 ≤ X.1 ∧ X.1 ≤ 1 ∧ 0 ≤ X.2 ∧ X.2 ≤ (1 + X.1) / 2

private theorem factor_nonneg {u a v : ℝ} (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ (1 + u) / 2) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ 2 * (1 - v) * (2 - (1 + u - 2 * a)) +
      (1 + v) * (1 + u - 2 * a) := by
  have ht : 0 ≤ 1 + u - 2 * a := by linarith
  have ht1 : 0 ≤ 2 - (1 + u - 2 * a) := by linarith
  have hv' : 0 ≤ 1 - v := by linarith
  positivity

private theorem K_star {X Y : (ℝ × ℝ)} (hX : K X) (hY : K Y) : K (star X Y) := by
  rcases X with ⟨u, a⟩
  rcases Y with ⟨v, b⟩
  rcases hX with ⟨hu, hu1, ha, ha1⟩
  rcases hY with ⟨hv, hv1, hb, hb1⟩
  have ht : 0 ≤ 1 + u - 2 * a := by linarith
  refine ⟨mul_nonneg hu hv, ?_, ?_, ?_⟩
  · change u * v ≤ 1
    nlinarith [mul_le_mul_of_nonneg_left hv1 hu]
  · change 0 ≤ a * v + (1 + u - 2 * a) * b / 4
    positivity
  · change a * v + (1 + u - 2 * a) * b / 4 ≤ (1 + u * v) / 2
    have hf := factor_nonneg hu1 ha ha1 hv hv1
    have hgap := mul_nonneg ht (sub_nonneg.mpr hb1)
    nlinarith

private theorem star_assoc_first (X Y Z : (ℝ × ℝ)) :
    (star (star X Y) Z).1 = (star X (star Y Z)).1 := by
  simp [star, mul_assoc]

private theorem star_assoc_gap (X Y Z : (ℝ × ℝ)) :
    (star (star X Y) Z).2 - (star X (star Y Z)).2 =
      Z.2 * (2 * (1 - Y.1) * (2 - (1 + X.1 - 2 * X.2)) +
        (1 + Y.1) * (1 + X.1 - 2 * X.2)) / 16 := by
  simp only [star]
  ring

private theorem root_rotation {X Y Z : (ℝ × ℝ)} (hX : K X) (hY : K Y) (hZ : K Z) :
    (star X (star Y Z)).2 ≤ (star (star X Y) Z).2 := by
  rw [← sub_nonneg, star_assoc_gap]
  exact div_nonneg (mul_nonneg hZ.2.2.1
    (factor_nonneg hX.2.1 hX.2.2.1 hX.2.2.2 hY.1 hY.2.1)) (by norm_num)

private theorem right_mono {X Y : (ℝ × ℝ)} {r p : ℝ}
    (hfirst : X.1 = Y.1) (hle : X.2 ≤ Y.2)
    (hp : 0 ≤ p) (hpr : p ≤ r) :
    (star X (r, p)).2 ≤ (star Y (r, p)).2 := by
  have hs : 0 ≤ r - p / 2 := by linarith
  have hmul := mul_nonneg (sub_nonneg.mpr hle) hs
  simp only [star]
  rw [hfirst]
  nlinarith


private def ceval (L : (ℝ × ℝ)) : Paren → (ℝ × ℝ)
  | .leaf => L
  | .node l r => star (ceval L l) (ceval L r)

private def iterRight (L X : (ℝ × ℝ)) : ℕ → (ℝ × ℝ)
  | 0 => X
  | n + 1 => star (iterRight L X n) L

private def cpower (L : (ℝ × ℝ)) : ℕ → (ℝ × ℝ)
  | 0 => L
  | 1 => L
  | n + 2 => star (cpower L (n + 1)) L

private theorem size_pos (t : Paren) : 0 < t.size := by
  induction t with
  | leaf => simp [Paren.size]
  | node l r hl hr => simp only [Paren.size]; omega

private theorem ceval_K {L : (ℝ × ℝ)} (hL : K L) (t : Paren) : K (ceval L t) := by
  induction t with
  | leaf => exact hL
  | node l r hl hr => exact K_star hl hr

private theorem iterRight_add (L X : (ℝ × ℝ)) (m n : ℕ) :
    iterRight L (iterRight L X m) n = iterRight L X (m + n) := by
  induction n with
  | zero => simp [iterRight]
  | succ n ih => simp only [iterRight, ih]; rfl

private theorem iterRight_mono {X Y : (ℝ × ℝ)} {r p : ℝ}
    (heq : X.1 = Y.1) (hle : X.2 ≤ Y.2) (hp : 0 ≤ p) (hpr : p ≤ r) (n : ℕ) :
    (iterRight (r, p) X n).1 = (iterRight (r, p) Y n).1 ∧
    (iterRight (r, p) X n).2 ≤ (iterRight (r, p) Y n).2 := by
  induction n with
  | zero => exact ⟨heq, hle⟩
  | succ n ih =>
    exact ⟨by simp only [iterRight, star]; rw [ih.1],
      right_mono ih.1 ih.2 hp hpr⟩

private theorem root_straighten {r p : ℝ} (hL : K (r, p)) (hp : 0 ≤ p) (hpr : p ≤ r)
    (t : Paren) (X : (ℝ × ℝ)) (hX : K X) :
    (star X (ceval (r, p) t)).1 = (iterRight (r, p) X t.size).1 ∧
    (star X (ceval (r, p) t)).2 ≤ (iterRight (r, p) X t.size).2 := by
  induction t generalizing X with
  | leaf => exact ⟨rfl, le_rfl⟩
  | node l s hl hs =>
    have hcl := ceval_K hL l
    have hcs := ceval_K hL s
    have hleft := hl X hX
    have hright := hs (star X (ceval (r, p) l)) (K_star hX hcl)
    have hmono := iterRight_mono hleft.1 hleft.2 hp hpr s.size
    rw [iterRight_add] at hmono
    exact ⟨(star_assoc_first X (ceval (r, p) l) (ceval (r, p) s)).symm.trans
      (hright.1.trans hmono.1),
      (root_rotation hX hcl hcs).trans (hright.2.trans hmono.2)⟩

private theorem cpower_succ (L : (ℝ × ℝ)) {n : ℕ} (hn : 0 < n) :
    cpower L (n + 1) = star (cpower L n) L := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem iterRight_cpower (L : (ℝ × ℝ)) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    iterRight L (cpower L m) n = cpower L (m + n) := by
  induction n with
  | zero => simp [iterRight]
  | succ n ih =>
    rw [iterRight, ih, Nat.add_succ, cpower_succ L (by omega)]

private theorem ceval_max {r p : ℝ} (hL : K (r, p)) (hp : 0 ≤ p) (hpr : p ≤ r)
    (t : Paren) :
    (ceval (r, p) t).1 = (cpower (r, p) t.size).1 ∧
    (ceval (r, p) t).2 ≤ (cpower (r, p) t.size).2 := by
  induction t with
  | leaf => exact ⟨rfl, le_rfl⟩
  | node l s hl _hs =>
    have ha := root_straighten hL hp hpr s (ceval (r, p) l) (ceval_K hL l)
    have hb := iterRight_mono hl.1 hl.2 hp hpr s.size
    rw [iterRight_cpower (r, p) (size_pos l)] at hb
    exact ⟨ha.1.trans hb.1, ha.2.trans hb.2⟩

private theorem eval_coordinates (L : (ℝ × ℝ)) (t : Paren) :
    eval (A L.1 L.2) t = A (ceval L t).1 (ceval L t).2 := by
  induction t with
  | leaf => rfl
  | node l r hl hr => simp only [eval, hl, hr, prod_A, ceval, star]

private theorem rightPow_coordinates (L : (ℝ × ℝ)) (n : ℕ) :
    rightPow (A L.1 L.2) n = A (cpower L n).1 (cpower L n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n hn hn1 => simp only [rightPow, hn1, prod_A, cpower, star]

theorem whole_triangle_max (P : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ))
    (hP : P ∈ convexHull ℝ {PR, SR, Ibox})
    (k : ℕ) (Q : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)) (hQ : Q ∈ orbit k P) :
    chsh Q ≤ chsh (rightPow P k) := by
  obtain ⟨r, p, hp, hpr, hr1, rfl⟩ := hull_coordinates hP
  have hr : 0 ≤ r := hp.trans hpr
  have hK : K (r, p) := ⟨hr, hr1, hp, by dsimp; linarith⟩
  obtain ⟨t, hsize, rfl⟩ := hQ
  have ht := ceval_max hK hp hpr t
  change chsh (eval (A (r, p).1 (r, p).2) t) ≤
    chsh (rightPow (A (r, p).1 (r, p).2) k)
  rw [eval_coordinates, rightPow_coordinates, chsh_A, chsh_A, ← hsize, ← ht.1]
  linarith [ht.2]

theorem result : claim := by
  intro P hP _ k _ Q hQ
  exact whole_triangle_max P hP k Q hQ


end D5.S3.Quantum.Entanglement.NonlocalBoxOrbitRightProduct
