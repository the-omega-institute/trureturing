/- GID: D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hamming/BadScienceFiveOptimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The displayed five-dimensional bad science matrix maximizes the unit-row functional. -/

/-
proof_shape: result: bind-only (cube certificates, Cauchy-Schwarz, and normalization).
escape_witness: none.
admission_basis: open-problem-resolution (#17586; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17688.
Direct frozen dependencies (declaration statement_id, not module pins):
  D5/S3/Combinatorics/IsingUniquenessSets.sgn
    sha256:1589788918111821cb994915047b9b43151423396895fcfd849105cc8fe4d481
  D5/S3/Combinatorics/IsingUniquenessSets.sgn_not
    sha256:3fea0d0608c561a90f61ba97d2e868ba6d838b7ae89eb97cdd74a8310505d819
Theorem classifications; dependencies below use these two declaration identities:
  proof_shape: neg_neg: bind-only; consumers=repr_neg,half_sum;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: sgn_neg: bind-only; consumers=lemma1,lemma4,orient_value;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: gram_cert: bind-only; consumers=cube_square;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: cube_square: bind-only; consumers=lemma1;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: pair_bound_cert: bind-only; consumers=pair_bound;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: qsum_double: bind-only; consumers=qsum_le_parity,qsum_linear;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: pair_bound: bind-only; consumers=qsum_le_parity;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: qsum_le_parity: bind-only; consumers=lemma2;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: qsum_linear: bind-only; consumers=lemma1;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: lemma1: bind-only; consumers=lemma3_sq;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: lemma2: bind-only; consumers=lemma3_sq;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: maj_nonneg: bind-only; consumers=lemma3,row_cell_le;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: lemma3_sq: bind-only; consumers=lemma3;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: lemma3: bind-only; consumers=row_cell_le;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: half_mem: bind-only; consumers=repr_of_half,half_sum;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: repr_neg: bind-only; consumers=repr_orient,cell_anti;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: repr_of_half: bind-only; consumers=orient_inj,cell_anti;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: neg_ne: bind-only; consumers=cell_anti;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: half_card: bind-only; consumers=cell_card_sum;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: half_sum: bind-only; consumers=lemma4;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: norm_attained: bind-only; consumers=win,win_spec;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: win_spec: bind-only; consumers=orient_value;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: repr_orient: bind-only; consumers=orient_inj,cell_anti;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: orient_inj: bind-only; consumers=cell_card_sum,cell_value_sum;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: orient_value: bind-only; consumers=cell_value_sum;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: cell_anti: bind-only; consumers=row_cell_le;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: cell_card_sum: bind-only; consumers=lemma4;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: cell_value_sum: bind-only; consumers=lemma4;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: row_cell_le: bind-only; consumers=lemma4;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: lemma4: bind-only; consumers=result;
    direct frozen dependencies: sgn, sgn_not; escape_witness: none.
  proof_shape: sum5: bind-only; consumers=Astar_norm;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: norm_five: bind-only; consumers=Astar_norm;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: Astar_simple: bind-only; consumers=Astar_norm;
    direct frozen dependencies: none; escape_witness: none.
  proof_shape: Astar_norm: bind-only; consumers=Astar_beta;
    direct frozen dependencies: sgn; escape_witness: none.
  proof_shape: Astar_beta: bind-only; consumers=result;
    direct frozen dependencies: sgn; escape_witness: none.
The sign-vector formula is written literally in beta; the proofs use the frozen scalar
  IsingUniquenessSets.sgn, through definitional equality, with no duplicate sign definition.
Utility none: the conclusion bounds every real five-by-five matrix with unit rows;
  the finite cube certificates are internal steps of this universal inequality.
Source: Albors et al., On the Structure of Bad Science Matrices, Section 1.4,
  arXiv:2408.00933v2; DOI 10.2140/involve.2026.19.443.
Original Lean implementation under Apache-2.0; no third-party proof code is copied.
-/

import D5.S3.Combinatorics.IsingUniquenessSets

noncomputable section

namespace D5.S3.Combinatorics.Hamming.BadScienceFiveOptimality

open Matrix

open D5.S3.Combinatorics.IsingUniquenessSets (sgn)

/-- The bad science functional `β(A) = 2^{-n} ∑_{x ∈ {-1,1}^n} ‖A x‖_∞`
(arXiv:2408.00933, Section 1).
The norm on `Fin n → ℝ` is the sup norm. -/
def beta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, ‖A *ᵥ (fun j => if x j then 1 else -1)‖

/-- Every row has unit `ℓ²` norm. -/
def UnitRows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, ∑ j, A i j ^ 2 = 1

/-- The `5 × 5` matrix of Section 1.4: `(1/(2√3))` times the displayed integer/`√3` matrix. -/
def Astar : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / (2 * Real.sqrt 3)) • !![2, 2, 0, 0, 2;
    -2, 2, 0, 2, 0;
    -2, 0, 0, -2, 2;
    0, -Real.sqrt 3, Real.sqrt 3, Real.sqrt 3, Real.sqrt 3;
    0, Real.sqrt 3, Real.sqrt 3, -Real.sqrt 3, -Real.sqrt 3]

/-- The question of Section 1.4: optimality among real `5 × 5` matrices with unit rows. -/
def claim : Prop :=
  ∀ A : Matrix (Fin 5) (Fin 5) ℝ, UnitRows A → beta A ≤ beta Astar

set_option maxRecDepth 10000
open Finset
private def Anti (S : Finset (Fin 5 → Bool)) : Prop := ∀ x ∈ S, (Bool.not ∘ x) ∉ S
private def qsum (S : Finset (Fin 5 → Bool)) : ℝ := ∑ j, (∑ x ∈ S, (sgn ∘ x) j)^2
private def maj (m : ℝ) : ℝ := (2 * Real.sqrt 3 - 2) * m + 8 - 4 * Real.sqrt 3

@[simp] private theorem neg_neg (x : Fin 5 → Bool) : (Bool.not ∘ (Bool.not ∘ x)) = x := by
  exact congrArg (fun f => f ∘ x) Bool.involutive_not.comp_self
@[simp] private theorem sgn_neg (x : Fin 5 → Bool) (j : Fin 5) : (sgn ∘ (Bool.not ∘ x)) j =
  -(sgn ∘ x) j := by
  exact D5.S3.Combinatorics.IsingUniquenessSets.sgn_not (x j)
private theorem gram_cert : ∀ i j : Fin 5,
    (∑ x : Fin 5 → Bool, ((if x i then 1 else -1):ℤ) * (if x j then 1 else -1)) =
      if i = j then 32 else 0 := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 10000000 in decide

private theorem cube_square (u : Fin 5 → ℝ) :
    (∑ x : Fin 5 → Bool, (dotProduct u (sgn ∘ x))^2) = 32 * ∑ j, (u j)^2 := by
  have gram (i j : Fin 5) : (∑ x : Fin 5 → Bool, (sgn ∘ x) i * (sgn ∘ x) j) =
      if i = j then (32:ℝ) else 0 := by
    have h := gram_cert i j
    have hc : ((∑ x : Fin 5 → Bool, ((if x i then 1 else -1):ℤ) *
      (if x j then 1 else -1)):ℝ) = if i = j then (32:ℝ) else 0 := by exact_mod_cast h
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg,
      Function.comp_apply, sgn] using hc
  calc
    _ = ∑ x : Fin 5 → Bool, ∑ i, ∑ j, (u i * u j) * ((sgn ∘ x) i * (sgn ∘ x) j) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [dotProduct, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, (u i * u j) * ∑ x : Fin 5 → Bool, (sgn ∘ x) i * (sgn ∘ x) j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ = _ := by
      simp only [gram]
      simp [Finset.mul_sum, pow_two, mul_comm]


private theorem pair_bound_cert : ∀ x y : Fin 5 → Bool,
    dotProduct (fun j => (if x j then 1 else -1 : ℤ)) (fun j => if y j then 1 else -1) ≤ (if x
      = y then 5 else if (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = (y 0 ^^ y 1 ^^ y 2 ^^ y 3 ^^ y 4)
      then 1 else 3) := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 10000000 in
      decide

private theorem qsum_double (S : Finset (Fin 5 → Bool)) :
    qsum S = ∑ x ∈ S, ∑ y ∈ S, dotProduct (sgn ∘ x) (sgn ∘ y) := by
  simp only [qsum, dotProduct, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext x
  rw [Finset.sum_comm]

private theorem pair_bound (x y : Fin 5 → Bool) :
    dotProduct (sgn ∘ x) (sgn ∘ y) ≤ 1 + (if x = y then 4 else 0) +
      (if (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) ≠ (y 0 ^^ y 1 ^^ y 2 ^^ y 3 ^^ y 4) then 2 else 0)
        := by
  have h := pair_bound_cert x y
  have hc : (dotProduct (fun j => (if x j then 1 else -1 : ℤ)) (fun j => if y j then 1 else -1)
    : ℝ) ≤
      (if x = y then (5 : ℝ) else if (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = (y 0 ^^ y 1 ^^ y 2 ^^
        y 3 ^^ y 4) then 1 else 3) := by
    simp only [dotProduct] at h ⊢
    exact_mod_cast h
  have he : (dotProduct (fun j => (if x j then 1 else -1 : ℤ)) (fun j => if y j then 1 else -1)
    : ℝ) = dotProduct (sgn ∘ x) (sgn ∘ y) := by
    simp only [Int.cast_ite, Int.cast_one, Int.cast_neg, dotProduct, Function.comp_apply, sgn]
  rw [he] at hc
  by_cases hxy : x = y
  · subst y
    norm_num at hc ⊢
    exact hc
  · by_cases hp : (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = (y 0 ^^ y 1 ^^ y 2 ^^ y 3 ^^ y 4) <;>
      simp only [hxy, hp, if_false, if_true, ne_eq, not_true_eq_false,
        not_false_eq_true, add_zero] at hc ⊢ <;> norm_num at hc ⊢ <;> exact hc

private theorem qsum_le_parity (S : Finset (Fin 5 → Bool)) :
    qsum S ≤ (S.card : ℝ)^2 + 4 * S.card +
      4 * ((S.filter fun x => (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = true).card : ℝ) *
        ((S.filter fun x => (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = false).card : ℝ) := by
  rw [qsum_double]
  have hb := Finset.sum_le_sum fun x (hx : x ∈ S) =>
    Finset.sum_le_sum fun y (_hy : y ∈ S) => pair_bound x y
  refine hb.trans_eq ?_
  simp only [Finset.sum_add_distrib]
  have hbool : ∀ x : Fin 5 → Bool, (∑ y ∈ S, if (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) ≠ (y 0 ^^ y 1
    ^^ y 2 ^^ y 3 ^^ y 4) then (2 : ℝ) else 0) =
      if (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = true then 2 * (S.filter fun y => (y 0 ^^ y 1 ^^ y
        2 ^^ y 3 ^^ y 4) = false).card
      else 2 * (S.filter fun y => (y 0 ^^ y 1 ^^ y 2 ^^ y 3 ^^ y 4) = true).card := by
    intro x
    cases hp : (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) <;>
      simp [Finset.sum_ite, mul_comm]
  simp_rw [hbool]
  simp [Finset.sum_ite, Finset.sum_ite_eq]
  ring
private theorem qsum_linear (S : Finset (Fin 5 → Bool)) :
    (∑ x ∈ S, dotProduct (fun j => ∑ y ∈ S, (sgn ∘ y) j) (sgn ∘ x)) = qsum S := by
  rw [qsum_double]
  simp only [dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp only [mul_comm]

private theorem lemma1 (S : Finset (Fin 5 → Bool)) (hS : Anti S) : qsum S ≤ 16 * S.card := by
  classical
  let u : Fin 5 → ℝ := fun j => ∑ x ∈ S, (sgn ∘ x) j
  let g : (Fin 5 → Bool) → ℝ := fun x => (dotProduct u (sgn ∘ x))^2
  have hg : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have heven : ∀ x, g ((Bool.not ∘ x)) = g x := by
    intro x
    simp only [g, dotProduct, sgn_neg, mul_neg, Finset.sum_neg_distrib, neg_sq]
  have hinj : Function.Injective (fun x : Fin 5 → Bool => Bool.not ∘ x) :=
    Function.Injective.comp_left (@Bool.not_inj)
  have hd : Disjoint S (S.image (fun x : Fin 5 → Bool => Bool.not ∘ x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    exact hS y hy hx
  have hi : ∑ x ∈ S.image (fun x : Fin 5 → Bool => Bool.not ∘ x), g x = ∑ x ∈ S, g x := by
    rw [Finset.sum_image (hinj.injOn)]
    simp_rw [heven]
  have hsub : ∑ x ∈ S ∪ S.image (fun x : Fin 5 → Bool => Bool.not ∘ x), g x ≤ ∑ x : Fin 5 →
    Bool, g x :=
    Finset.sum_le_univ_sum_of_nonneg hg
  rw [Finset.sum_union hd, hi] at hsub
  have hc := cube_square u
  change (∑ x : Fin 5 → Bool, g x) = 32 * qsum S at hc
  rw [hc] at hsub
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun x => dotProduct u (sgn ∘ x))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  change (∑ x ∈ S, dotProduct (fun j => ∑ y ∈ S, (sgn ∘ y) j) (sgn ∘ x))^2 ≤
    (S.card : ℝ) * ∑ x ∈ S, g x at hcs
  rw [qsum_linear] at hcs
  have hn : 0 ≤ qsum S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hm : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hm' := mul_le_mul_of_nonneg_left hsub hm
  by_cases hq : qsum S = 0
  · rw [hq]; positivity
  · have hq' : 0 < qsum S := lt_of_le_of_ne hn (Ne.symm hq)
    nlinarith
private theorem lemma2 (S : Finset (Fin 5 → Bool)) :
    qsum S ≤ (S.card : ℝ)^2 + 4 * S.card + 4 * (S.card^2 / 4 : ℕ) := by
  classical
  let p := (S.filter fun x => (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = true).card
  let t := (S.filter fun x => (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x 4) = false).card
  have hsum : p + t = S.card := by
    simpa only [p, t, Bool.not_eq_true] using
      (Finset.card_filter_add_card_filter_not (s := S) (fun x => (x 0 ^^ x 1 ^^ x 2 ^^ x 3 ^^ x
        4) = true))
  have hp : p * t ≤ S.card^2 / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr
    simpa only [← hsum, mul_assoc, mul_comm, mul_left_comm] using four_mul_le_sq_add p t
  have hp' : (p:ℝ) * t ≤ (S.card^2 / 4 : ℕ) := by exact_mod_cast hp
  have hb := qsum_le_parity S
  change qsum S ≤ (S.card:ℝ)^2 + 4 * S.card + 4 * p * t at hb
  nlinarith

private theorem maj_nonneg (m : ℝ) (hm : 0 ≤ m) : 0 ≤ maj m := by
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hl : (5:ℝ)/3 ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hu : Real.sqrt 3 ≤ (7:ℝ)/4 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hp := mul_nonneg (show 0 ≤ 2 * Real.sqrt 3 - 2 by linarith) hm
  unfold maj
  linarith

private theorem lemma3_sq (S : Finset (Fin 5 → Bool)) (hS : Anti S) : qsum S ≤ maj S.card ^ 2 := by
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hl : (5:ℝ)/3 ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hu : Real.sqrt 3 ≤ (7:ℝ)/4 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  by_cases hm : S.card ≤ 5
  · have hb := lemma2 S
    interval_cases h : S.card <;> norm_num [h, maj] at hb ⊢ <;> nlinarith
  · have hm' : 6 ≤ S.card := by omega
    have hm'' : (6:ℝ) ≤ S.card := Nat.ofNat_le_cast.mpr hm'
    have hb := lemma1 S hS
    have hx : 0 ≤ (2 - Real.sqrt 3) * (S.card:ℝ) * (S.card - 6) := by
      apply mul_nonneg
      · exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
      · linarith
    have hid : maj S.card^2 - 16 * S.card =
        8 * ((2 - Real.sqrt 3) * (S.card:ℝ) * (S.card - 6) + 14 - 8 * Real.sqrt 3) := by
      unfold maj
      linear_combination (4 * (S.card:ℝ)^2 - 16 * S.card + 16) * hr
    linarith

private theorem lemma3 (S : Finset (Fin 5 → Bool)) (hS : Anti S) : Real.sqrt (qsum S) ≤ maj
  S.card := by
  exact (Real.sqrt_le_iff).mpr ⟨maj_nonneg _ (Nat.cast_nonneg _), lemma3_sq S hS⟩

set_option maxRecDepth 10000
open Matrix Finset
private def half : Finset (Fin 5 → Bool) := Finset.univ.filter fun x => x 0 = true
private def repr (x : Fin 5 → Bool) : Fin 5 → Bool := if x 0 then x else (Bool.not ∘ x)
@[simp] private theorem half_mem {x : Fin 5 → Bool} : x ∈ half ↔ x 0 = true := by
  simp [half]
@[simp] private theorem repr_neg (x : Fin 5 → Bool) : repr (Bool.not ∘ x) = repr x := by
  cases h : x 0 <;> simp [repr, Function.comp_apply, h]
private theorem repr_of_half {x : Fin 5 → Bool} (hx : x ∈ half) : repr x = x := by
  simp [repr, half_mem.mp hx]
private theorem neg_ne (x : Fin 5 → Bool) : (Bool.not ∘ x) ≠ x := by
  intro h
  exact Bool.not_ne_self (x 0) (congrFun h 0)
private theorem half_card : half.card = 16 := by
  exact Eq.symm (Nat.eq_of_beq_eq_true rfl)

private theorem half_sum (f : (Fin 5 → Bool) → ℝ) (hf : ∀ x, f (Bool.not ∘ x) = f x) :
    (∑ x : Fin 5 → Bool, f x) = 2 * ∑ x ∈ half, f x := by
  classical
  have hinj : Function.Injective (fun x : Fin 5 → Bool => Bool.not ∘ x) :=
    Function.Injective.comp_left (@Bool.not_inj)
  have hd : Disjoint half (half.image (fun x : Fin 5 → Bool => Bool.not ∘ x)) := by
    exact Finset.sdiff_eq_self_iff_disjoint.mp rfl
  have hu : half ∪ half.image (fun x : Fin 5 → Bool => Bool.not ∘ x) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    by_cases hx : x 0 = true
    · exact Or.inl (half_mem.mpr hx)
    · right
      exact ⟨(Bool.not ∘ x), half_mem.mpr (by simpa [Function.comp_apply] using hx), neg_neg x⟩
  rw [← hu, Finset.sum_union hd, Finset.sum_image hinj.injOn]
  simp_rw [hf]
  ring

private theorem norm_attained (A : Matrix (Fin 5) (Fin 5) ℝ) (x : Fin 5 → Bool) :
    ∃ i, ‖A *ᵥ (sgn ∘ x)‖ = |dotProduct (A i) (sgn ∘ x)| := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (A *ᵥ (sgn ∘ x))).1
  exact ⟨i, by simpa only [Real.norm_eq_abs, Matrix.mulVec] using hi.symm⟩
private noncomputable def win (A : Matrix (Fin 5) (Fin 5) ℝ) (x : Fin 5 → Bool) : Fin 5 :=
  Classical.choose (norm_attained A x)
private theorem win_spec (A : Matrix (Fin 5) (Fin 5) ℝ) (x : Fin 5 → Bool) :
    ‖A *ᵥ (sgn ∘ x)‖ = |dotProduct (A (win A x)) (sgn ∘ x)| := by
  exact Classical.choose_spec (norm_attained A x)
attribute [irreducible] win

private noncomputable def orient (A : Matrix (Fin 5) (Fin 5) ℝ) (x : Fin 5 → Bool) : Fin 5 →
  Bool :=
  if 0 ≤ dotProduct (A (win A x)) (sgn ∘ x) then x else (Bool.not ∘ x)
@[simp] private theorem repr_orient (A : Matrix (Fin 5) (Fin 5) ℝ) (x : Fin 5 → Bool) :
    repr (orient A x) = repr x := by
  unfold orient
  split <;> simp

private theorem orient_inj (A : Matrix (Fin 5) (Fin 5) ℝ) : Set.InjOn (orient A) half := by
  exact (show Set.LeftInvOn repr (orient A) half from
    fun x hx => (repr_orient A x).trans (repr_of_half hx)).injOn

private theorem orient_value (A : Matrix (Fin 5) (Fin 5) ℝ) (x : Fin 5 → Bool) :
    dotProduct (A (win A x)) ((sgn ∘ orient A x)) = ‖A *ᵥ (sgn ∘ x)‖ := by
  rw [win_spec]
  unfold orient
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · simp only [dotProduct, sgn_neg, mul_neg, Finset.sum_neg_distrib]
    exact (abs_of_neg (lt_of_not_ge h)).symm
private noncomputable def cell (A : Matrix (Fin 5) (Fin 5) ℝ) (i : Fin 5) : Finset (Fin 5 →
  Bool) :=
  (half.filter fun x => win A x = i).image (orient A)

private theorem cell_anti (A : Matrix (Fin 5) (Fin 5) ℝ) (i : Fin 5) : Anti (cell A i) := by
  intro y hy hny
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hny
  have hx' : x ∈ half := Finset.mem_of_mem_filter x hx
  have hz' : z ∈ half := Finset.mem_of_mem_filter z hz
  have hr := congrArg repr he
  have hzx : z = x := by
    simpa only [repr_orient, repr_neg, repr_of_half hz', repr_of_half hx'] using hr
  subst z
  exact neg_ne _ he.symm

private theorem cell_card_sum (A : Matrix (Fin 5) (Fin 5) ℝ) :
    ∑ i, (cell A i).card = 16 := by
  classical
  have hc (i : Fin 5) : (cell A i).card = (half.filter fun x => win A x = i).card := by
    apply Finset.card_image_of_injOn
    exact (orient_inj A).mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  simp_rw [hc]
  have h := Finset.sum_fiberwise half (win A) (fun _ => (1:ℕ))
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id, half_card] using h

private theorem cell_value_sum (A : Matrix (Fin 5) (Fin 5) ℝ) :
    (∑ x ∈ half, ‖A *ᵥ (sgn ∘ x)‖) =
      ∑ i, dotProduct (A i) (fun j => ∑ y ∈ cell A i, (sgn ∘ y) j) := by
  classical
  rw [← Finset.sum_fiberwise half (win A) (fun x => ‖A *ᵥ (sgn ∘ x)‖)]
  apply Finset.sum_congr rfl
  intro i _
  symm
  calc
    _ = ∑ y ∈ cell A i, dotProduct (A i) (sgn ∘ y) := by
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      rw [cell, Finset.sum_image ((orient_inj A).mono
        (by intro x hx; exact (Finset.mem_filter.mp hx).1))]
      apply Finset.sum_congr rfl
      intro x hx
      have hi := (Finset.mem_filter.mp hx).2
      rw [← hi]
      exact orient_value A x

private theorem row_cell_le (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : UnitRows A) (i : Fin 5) :
    dotProduct (A i) (fun j => ∑ y ∈ cell A i, (sgn ∘ y) j) ≤ maj (cell A i).card := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i)
    (fun j => ∑ y ∈ cell A i, (sgn ∘ y) j)
  rw [hA i] at h
  simp only [one_mul] at h
  change dotProduct (A i) (fun j => ∑ y ∈ cell A i, (sgn ∘ y) j)^2 ≤ qsum (cell A i) at h
  have hb := lemma3 (cell A i) (cell_anti A i)
  have hq := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
    sq_nonneg (∑ y ∈ cell A i, (sgn ∘ y) j)))
  change (Real.sqrt (qsum (cell A i)))^2 = qsum (cell A i) at hq
  have hn := maj_nonneg ((cell A i).card : ℝ) (Nat.cast_nonneg _)
  have hs := mul_nonneg (sub_nonneg.mpr hb)
    (add_nonneg hn (Real.sqrt_nonneg (qsum (cell A i))))
  nlinarith

private theorem lemma4 (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : UnitRows A) :
    beta A ≤ (2 + 3 * Real.sqrt 3) / 4 := by
  have heven : ∀ x : Fin 5 → Bool, ‖A *ᵥ (sgn ∘ (Bool.not ∘ x))‖ = ‖A *ᵥ (sgn ∘ x)‖ := by
    intro x
    have hs : (sgn ∘ (Bool.not ∘ x)) = -(sgn ∘ x) := by
      ext j
      exact sgn_neg x j
    rw [hs, Matrix.mulVec_neg, norm_neg]
  have hhalf := half_sum (fun x => ‖A *ᵥ (sgn ∘ x)‖) heven
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => row_cell_le A hA i)
  rw [← cell_value_sum] at hb
  have hc : ∑ i, ((cell A i).card : ℝ) = 16 := by exact_mod_cast cell_card_sum A
  have hm : (∑ i : Fin 5, maj (cell A i).card) = 8 + 12 * Real.sqrt 3 := by
    simp only [maj, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
    ring
  rw [hm] at hb
  unfold beta
  change (2 ^ 5 : ℝ)⁻¹ * (∑ x : Fin 5 → Bool, ‖A *ᵥ (sgn ∘ x)‖) ≤ _
  rw [hhalf]
  norm_num
  linarith

private theorem sum5 (f : Fin 5 → ℝ) : ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + f 4))) := by
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rfl

private theorem norm_five (v : Fin 5 → ℝ) :
    ‖v‖ = max |v 0| (max |v 1| (max |v 2| (max |v 3| |v 4|))) := by
  simp [Pi.norm_def, Fin.univ_succ, Finset.sup_insert, NNReal.coe_max]

private theorem Astar_simple : Astar =
    !![Real.sqrt 3 / 3, Real.sqrt 3 / 3, 0, 0, Real.sqrt 3 / 3;
      -Real.sqrt 3 / 3, Real.sqrt 3 / 3, 0, Real.sqrt 3 / 3, 0;
      -Real.sqrt 3 / 3, 0, 0, -Real.sqrt 3 / 3, Real.sqrt 3 / 3;
      0, -(1/2:ℝ), 1/2, 1/2, 1/2;
      0, (1/2:ℝ), 1/2, -(1/2), -(1/2)] := by
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Astar, Matrix.smul_apply, smul_eq_mul] <;>
    field_simp <;> nlinarith


set_option maxHeartbeats 1000000 in
-- The 32 sign cases expand five row norms before normalization.
private theorem Astar_norm (x : Fin 5 → Bool) :
    ‖Astar *ᵥ (sgn ∘ x)‖ = if x 3 = x 4 ∧ x 1 ≠ x 3 then 2 else Real.sqrt 3 := by
  rw [Astar_simple, norm_five]
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hl : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have hu : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;>
    norm_num [Matrix.mulVec, dotProduct, sum5, sgn, h0, h1, h2, h3, h4,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases] <;>
    ring_nf <;>
    norm_num [abs_of_nonneg hn, abs_of_nonpos (neg_nonpos.mpr hn),
      max_eq_left hl, max_eq_right hl, max_eq_left hu, max_eq_right hu] <;>
    nlinarith
private theorem Astar_beta : beta Astar = (2 + 3 * Real.sqrt 3) / 4 := by
  classical
  let C : Finset (Fin 5 → Bool) := Finset.univ.filter fun x => x 3 = x 4 ∧ x 1 ≠ x 3
  have hC : C.card = 8 := Eq.symm (Nat.eq_of_beq_eq_true rfl)
  have hCn : (Finset.univ.filter (fun x : Fin 5 → Bool => ¬(x 3 = x 4 ∧ x 1 ≠ x 3))).card = 24
    := Eq.symm (Nat.eq_of_beq_eq_true rfl)
  unfold beta
  change (2 ^ 5 : ℝ)⁻¹ * (∑ x : Fin 5 → Bool, ‖Astar *ᵥ (sgn ∘ x)‖) = _
  simp_rw [Astar_norm]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (2^5:ℝ)⁻¹ * ((C.card:ℝ) * 2 +
    ((Finset.univ.filter (fun x : Fin 5 → Bool => ¬(x 3 = x 4 ∧ x 1 ≠ x 3))).card : ℝ) *
      Real.sqrt 3) = _
  rw [hC, hCn]
  norm_num
  ring


theorem result : claim := by
  intro A hA
  rw [Astar_beta]
  exact lemma4 A hA
end D5.S3.Combinatorics.Hamming.BadScienceFiveOptimality
