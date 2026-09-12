/- GID: D5/S3/Analytic/Convexity/FiniteStrongDuality
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/FiniteStrongDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both feasible valid extended linear programs attain finite opposite primal and dual values. -/

/-
Source: madvorak/duality, revision 7e6502ab40b9ea7d42bd2eadc115b6a8b653392f.
https://github.com/madvorak/duality/tree/7e6502ab40b9ea7d42bd2eadc115b6a8b653392f
Original files: LinearProgramming.lean, the dependency closure of ValidELP.strong_duality_of_both_feasible.
The mathematical source accompanies the work of Martin Dvorak and Vladimir Kolmogorov.
Modified for Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:
namespaces and theorem names, unbundled ordered algebra, current notation and APIs,
local normalization and native sum-homomorphism applications,
and removal of unused declarations and the diagnostic Linters import.
The mathematical constructions and quantified contracts are retained.
Retirement: replace with a native declaration at the Mathlib revision actually
adopted by this repository only after that declaration's exact type and direct
instantiation preserve these ordered-scalar and extended-coefficient contracts,
including finite primal/dual attainment and the standard axiom closure.
An upstream acceptance or a declaration on an unadopted revision is insufficient.
The complete upstream and historical Mathlib Apache-2.0 licenses are bundled in
D5/S3/Analytic/Convexity/FarkasAlternative.lean.
-/

import Mathlib.Tactic.Linarith
import D5.S3.Analytic.Convexity.ExtendedFarkas

open D5.S3.Analytic.Convexity.FarkasAlternative
open D5.S3.Analytic.Convexity.ExtendedFarkas

namespace D5.S3.Analytic.Convexity.FiniteStrongDuality

noncomputable section

/-- Linear program over `(Extend F)` in the standard form (i.e.,
    a system of linear inequalities with nonnegative variables).
    Variables are of type `J`. Conditions are indexed by type `I`.
    The objective function is intended to be minimized. -/
structure ExtendedLP (I J F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] where
  /-- The left-hand-side matrix. -/
  A : Matrix I J (Extend F)
  /-- The right-hand-side vector. -/
  b : I → (Extend F)
  /-- The objective function coefficients. -/
  c : J → (Extend F)

/-- Extended linear program with properties that are needed for duality theorems. -/
structure ValidELP (I J F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] extends ExtendedLP I J F where
  /-- No `⊥` and `⊤` in the same row. -/
  hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤)
  /-- No `⊥` and `⊤` in the same column. -/
  hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤)
  /-- No `⊥` in the row where the right-hand-side vector has `⊥`. -/
  hbA : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥
  /-- No `⊤` in the column where the objective function has `⊥`. -/
  hcA : ¬∃ j : J, (∃ i : I, A i j = ⊤) ∧ c j = ⊥
  /-- No `⊤` in the row where the right-hand-side vector has `⊤`. -/
  hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤
  /-- No `⊥` in the column where the objective function has `⊤`. -/
  hAc : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ c j = ⊤

open scoped Matrix

variable {I J F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A nonnegative vector `x` is a solution to a linear program `P` iff
    its multiplication by matrix `A` from the left yields a vector whose
    all entries are less or equal to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution [Fintype J] (P : ExtendedLP I J F) (x : J → (NNeg F)) : Prop :=
  P.A ₘ* x ≤ P.b

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. -/
def ExtendedLP.Reaches [Fintype J] (P : ExtendedLP I J F) (r : (Extend F)) : Prop :=
  ∃ x : J → (NNeg F), P.IsSolution x ∧ P.c ᵥ⬝ x = r

/-- Linear program `P` is feasible iff `P` reaches a value that is not `⊤`. -/
def ExtendedLP.IsFeasible [Fintype J] (P : ExtendedLP I J F) : Prop :=
  ∃ p : (Extend F), P.Reaches p ∧ p ≠ ⊤

/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded by `r` from below). -/
def ExtendedLP.IsBoundedBy [Fintype J] (P : ExtendedLP I J F) (r : F) : Prop :=
  ∀ p : (Extend F), P.Reaches p → r ≤ p

/-- Linear program `P` is unbounded iff values reached by `P` have no finite lower bound. -/
def ExtendedLP.IsUnbounded [Fintype J] (P : ExtendedLP I J F) : Prop :=
  ¬∃ r : F, P.IsBoundedBy r

/-- Dualize an extended linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function.
    Both linear programs are intended to be minimized. -/
abbrev ExtendedLP.dualize (P : ExtendedLP I J F) : ExtendedLP J I F :=
  ⟨-P.Aᵀ, P.c, P.b⟩

/-- Dualize a valid extended linear program. -/
def ValidELP.dualize (P : ValidELP I J F) : ValidELP J I F := by
  have ef_neg_eq_top_iff {x : Extend F} : -x = ⊤ ↔ x = ⊥ :=
    neg_injective.eq_iff' rfl
  have ef_neg_eq_bot_iff {x : Extend F} : -x = ⊥ ↔ x = ⊤ :=
    neg_injective.eq_iff' rfl
  exact {
  toExtendedLP := P.toExtendedLP.dualize
  hAi := by intro <;> apply P.hAj <;> aesop (add simp [ef_neg_eq_top_iff, ef_neg_eq_bot_iff])
  hAj := by intro <;> apply P.hAi <;> aesop (add simp [ef_neg_eq_top_iff, ef_neg_eq_bot_iff])
  hbA := by intro <;> apply P.hcA <;> aesop (add simp [ef_neg_eq_top_iff, ef_neg_eq_bot_iff])
  hcA := by intro <;> apply P.hbA <;> aesop (add simp [ef_neg_eq_top_iff, ef_neg_eq_bot_iff])
  hAb := by intro <;> apply P.hAc <;> aesop (add simp [ef_neg_eq_top_iff, ef_neg_eq_bot_iff])
  hAc := by intro <;> apply P.hAb <;> aesop (add simp [ef_neg_eq_top_iff, ef_neg_eq_bot_iff]) }

variable [Fintype J]

variable [Fintype I] [DecidableEq J]

variable [DecidableEq I]

lemma ValidELP.strong_duality_aux (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
  classical
  have ef_coe_strict_mono : StrictMono (toE (F := F)) :=
    WithBot.coe_strictMono.comp WithTop.coe_strictMono
  have ef_coe_injective : Function.Injective (toE (F := F)) :=
    ef_coe_strict_mono.injective
  have ef_coe_le_coe_iff {x y : F} : (x : Extend F) ≤ (y : Extend F) ↔ x ≤ y :=
    ef_coe_strict_mono.le_iff_le
  have ef_coe_lt_coe_iff {x y : F} : (x : Extend F) < (y : Extend F) ↔ x < y :=
    ef_coe_strict_mono.lt_iff_lt
  have ef_coe_eq_coe_iff {x y : F} : (x : Extend F) = (y : Extend F) ↔ x = y :=
    ef_coe_injective.eq_iff
  have ef_coe_zero : ((0 : F) : Extend F) = 0 := rfl
  have ef_bot_lt_coe (x : F) : (⊥ : Extend F) < x :=
    WithBot.bot_lt_coe _
  have ef_coe_neq_bot (x : F) : (x : Extend F) ≠ ⊥ :=
    (ef_bot_lt_coe x).ne'
  have ef_coe_lt_top (x : F) : (x : Extend F) < ⊤ :=
    WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _
  have ef_coe_neq_top (x : F) : (x : Extend F) ≠ ⊤ :=
    (ef_coe_lt_top x).ne
  have ef_zero_neq_bot : (0 : Extend F) ≠ ⊥ :=
    ef_coe_neq_bot 0
  have ef_zero_lt_top : (0 : Extend F) < ⊤ :=
    ef_coe_lt_top 0
  have ef_zero_neq_top : (0 : Extend F) ≠ ⊤ :=
    ef_coe_neq_top 0
  have ef_coe_add (x y : F) : toE (x + y) = toE x + toE y :=
    rfl
  have ef_coe_nonpos {x : F} : x ≤ (0 : Extend F) ↔ x ≤ 0 :=
    ef_coe_le_coe_iff
  have ef_coe_neg' {x : F} : x < (0 : Extend F) ↔ x < 0 :=
    ef_coe_lt_coe_iff
  have ef_add_bot (x : Extend F) : x + ⊥ = ⊥ :=
    WithBot.add_bot x
  have ef_bot_add (x : Extend F) : ⊥ + x = ⊥ :=
    WithBot.bot_add x
  have ef_top_add_top : (⊤ : Extend F) + ⊤ = ⊤ :=
    rfl
  have ef_top_add_coe (x : F) : (⊤ : Extend F) + x = ⊤ :=
    rfl
  have ef_coe_add_top (x : F) : (x : Extend F) + ⊤ = ⊤ :=
    rfl
  have ef_coe_neg (x : F) : toE (-x) = -(toE x) := rfl
  have ef_neg_eq_top_iff {x : Extend F} : -x = ⊤ ↔ x = ⊥ :=
    neg_injective.eq_iff' rfl
  have ef_neg_eq_bot_iff {x : Extend F} : -x = ⊥ ↔ x = ⊤ :=
    neg_injective.eq_iff' rfl
  have ef_pos_smul_top {c : (NNeg F)} (hc : 0 < c) : c • (⊤ : (Extend F)) = ⊤ := by
    change (if c = 0 then 0 else (⊤ : Extend F)) = ⊤
    simp [hc.ne.symm]
  have ef_smul_top_neq_bot (c : (NNeg F)) : c • (⊤ : (Extend F)) ≠ ⊥ := by
    change (if c = 0 then 0 else (⊤ : Extend F)) ≠ ⊥
    by_cases hc0 : c = 0 <;> simp [hc0, ef_zero_neq_bot]
  have ef_smul_coe_neq_bot (c : (NNeg F)) (f : F) : c • toE f ≠ (⊥ : (Extend F)) :=
    ef_coe_neq_bot (c * f)
  have ef_smul_bot (c : (NNeg F)) : c • (⊥ : (Extend F)) = ⊥ :=
    rfl
  have ef_smul_nonbot_neq_bot (c : (NNeg F)) {r : (Extend F)} (hr : r ≠ ⊥) : c • r ≠ ⊥ := by
    match r with
    | ⊥ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hr
    | ⊤ => apply ef_smul_top_neq_bot
    | (f : F) => apply ef_smul_coe_neq_bot
  have ef_zero_smul_nonbot {r : (Extend F)} (hr : r ≠ ⊥) : (0 : (NNeg F)) • r = 0 := by
    show EF.smulNN 0 r = 0
    simp [EF.smulNN]
    match r with
    | ⊥ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hr
    | ⊤ => rfl
    | (f : F) => rfl
  have ef_zero_smul_coe (f : F) : (0 : (NNeg F)) • toE f = 0 :=
    ef_zero_smul_nonbot (ef_coe_neq_bot f)
  have ef_one_smul (r : (Extend F)) : (1 : (NNeg F)) • r = r := by
    match r with
    | ⊥ => rfl
    | ⊤ =>
      exact ef_pos_smul_top (show (0 : NNeg F) < 1 from zero_lt_one)
    | (q : F) => exact congr_arg toE (one_mul q)
  have ef_sub_nonpos_iff (r s : Extend F) : r + (-s) ≤ 0 ↔ r ≤ s := by
    match r, s with
    | ⊥, _ => simp only [ef_bot_add, bot_le]
    | r, ⊤ =>
      change r + ⊥ ≤ 0 ↔ r ≤ ⊤
      simp only [ef_add_bot, bot_le, le_top]
    | ⊤, ⊥ =>
      change (⊤ : Extend F) + ⊤ ≤ 0 ↔ (⊤ : Extend F) ≤ ⊥
      simp [ef_top_add_top, ef_zero_neq_top]
    | ⊤, (q : F) =>
      change (⊤ : Extend F) + toE (-q) ≤ 0 ↔ (⊤ : Extend F) ≤ toE q
      simp [ef_top_add_coe, ef_zero_neq_top, ef_coe_neq_top]
    | (p : F), ⊥ =>
      change toE p + ⊤ ≤ 0 ↔ toE p ≤ (⊥ : Extend F)
      simp [ef_coe_add_top, ef_zero_neq_top, ef_coe_neq_bot]
    | (p : F), (q : F) =>
      change toE p + toE (-q) ≤ toE 0 ↔ toE p ≤ toE q
      rw [←ef_coe_add, ef_coe_le_coe_iff, ef_coe_le_coe_iff]
      simpa only [sub_eq_add_neg] using (sub_nonpos : p - q ≤ 0 ↔ p ≤ q)
  have smul_eq_bot (k : NNeg F) (r : Extend F) : k • r = ⊥ ↔ r = ⊥ := by
    constructor
    · intro h
      by_contra hr
      exact ef_smul_nonbot_neq_bot k hr h
    · rintro rfl
      rfl
  have ef_smul_nonpos {r : (Extend F)} (hr : r ≤ 0) (k : (NNeg F)) :
      k • r ≤ 0 := by
    match r with
    | ⊥ => apply bot_le
    | ⊤ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hr
    | (_ : F) => exact ef_coe_le_coe_iff.mpr (mul_nonpos_of_nonneg_of_nonpos k.property (ef_coe_nonpos.mp hr))
  have ef_smul_lt_smul_left {k : NNeg F} (hk : 0 < k) (r s : Extend F) :
      k • r < k • s ↔ r < s := by
    match r, s with
    | ⊥, ⊥ => rfl
    | _, ⊥ => exact iff_of_false (not_lt_bot) (not_lt_bot)
    | ⊥, ⊤ => simp only [ef_smul_bot, ef_pos_smul_top hk, bot_lt_top]
    | ⊤, ⊤ => simp only [lt_self_iff_false]
    | ⊤, (q : F) => simp only [ef_pos_smul_top hk, not_top_lt]
    | (p : F), ⊤ =>
      change toE (k * p) < k • ⊤ ↔ toE p < ⊤
      simp only [ef_pos_smul_top hk, ef_coe_lt_top]
    | ⊥, (q : F) =>
      change (⊥ : Extend F) < toE (k * q) ↔ (⊥ : Extend F) < toE q
      simp only [ef_bot_lt_coe]
    | (p : F), (q : F) =>
      change toE (k * p) < toE (k * q) ↔ toE p < toE q
      rw [ef_coe_lt_coe_iff, ef_coe_lt_coe_iff]
      exact mul_lt_mul_iff_right₀ (show (0 : F) < k.val from hk)
  have ef_smul_le_smul_left {k : (NNeg F)} (hk : 0 < k) (r s : (Extend F)) :
      k • r ≤ k • s ↔ r ≤ s := by
    simpa only [not_lt] using not_congr (ef_smul_lt_smul_left hk s r)
  have ef_add_smul (k l : (NNeg F)) (r : (Extend F)) :
      (k + l) • r = k • r + l • r := by
    match r with
    | ⊥ =>
      rewrite [ef_smul_bot, ef_smul_bot, ef_smul_bot]
      rfl
    | ⊤ =>
      if k_eq_0 : k = 0 then
        rw [k_eq_0, ef_zero_smul_nonbot top_ne_bot, zero_add, zero_add]
      else
        have k_pos : 0 < k
        · exact pos_iff_ne_zero.mpr k_eq_0
        rw [ef_pos_smul_top (add_pos_of_pos_of_nonneg k_pos l.property)]
        rw [ef_pos_smul_top k_pos]
        if l_eq_0 : l = 0 then
          rewrite [l_eq_0]
          change (⊤ : Extend F) = ⊤ + (0 : NNeg F) • (⊤ : Extend F)
          rw [ef_zero_smul_nonbot top_ne_bot, add_zero]
        else
          rewrite [ef_pos_smul_top (pos_iff_ne_zero.mpr l_eq_0)]
          rfl
    | (f : F) =>
      show toE ((k + l) * f) = toE (k * f) + toE (l * f)
      rw [←ef_coe_add, add_mul]
  have ef_smul_add {k : (NNeg F)} (hk : 0 < k) (r s : (Extend F)) :
      k • (r + s) = k • r + k • s := by
    match r, s with
    | ⊥, _ =>
      rw [ef_bot_add, ef_smul_bot, ef_bot_add]
    | _, ⊥ =>
      rw [ef_add_bot, ef_smul_bot, ef_add_bot]
    | (p : F), (q : F) =>
      show toE (k * (p + q)) = toE (k * p) + toE (k * q)
      rewrite [mul_add]
      rfl
    | (p : F), ⊤ =>
      rw [ef_coe_add_top, ef_pos_smul_top hk]
      show ⊤ = toE (k * p) + ⊤
      rw [ef_coe_add_top]
    | ⊤, (q : F) =>
      rw [ef_top_add_coe, ef_pos_smul_top hk]
      show ⊤ = ⊤ + toE (k * q)
      rw [ef_top_add_coe]
    | ⊤, ⊤ =>
      rw [ef_top_add_top, ef_pos_smul_top hk, ef_top_add_top]
  have ef_mul_smul (k l : (NNeg F)) (r : (Extend F)) :
      (k * l) • r = k • (l • r) := by
    match r with
    | ⊥ =>
      iterate 3 rw [ef_smul_bot]
    | ⊤ =>
      if l_eq_0 : l = 0 then
        rw [l_eq_0, ef_zero_smul_nonbot top_ne_bot, mul_zero, ef_zero_smul_nonbot top_ne_bot, smul_zero]
      else
        have l_pos : 0 < l
        · apply lt_of_le_of_ne l.property
          exact fun h => l_eq_0 (Subtype.ext h.symm)
        rw [ef_pos_smul_top l_pos]
        if k_eq_0 : k = 0 then
          rw [k_eq_0, ef_zero_smul_nonbot top_ne_bot, zero_mul, ef_zero_smul_nonbot top_ne_bot]
        else
          have c_pos : 0 < k
          · exact pos_iff_ne_zero.mpr k_eq_0
          rw [ef_pos_smul_top c_pos, ef_pos_smul_top (mul_pos c_pos l_pos)]
    | (f : F) =>
      show toE ((k * l) * f) = toE (k * (l * f))
      rw [mul_assoc]
  have dot_weig_add {J : Type _} [Fintype J] (x : J → (Extend F)) (v w : J → (NNeg F)) :
      x ᵥ⬝ (v + w) = x ᵥ⬝ v + x ᵥ⬝ w := by
    simp [dotWeig, ef_add_smul, Finset.sum_add_distrib]
  have dot_weig_smul {J : Type _} [Fintype J] {k : (NNeg F)} (hk : 0 < k) (x : J → (Extend F)) (v : J → (NNeg F)) :
      x ᵥ⬝ (k • v) = k • (x ᵥ⬝ v) := by
    show ∑ j : J, (k * v j) • x j = k • ∑ j : J, v j • x j
    simp_rw [ef_mul_smul]
    exact (map_sum
      (⟨⟨(k • ·), smul_zero k⟩, ef_smul_add hk⟩ : Extend F →+ Extend F)
      (fun j => v j • x j) Finset.univ).symm
  have no_bot_b (i : I) : P.b i ≠ ⊥ := by
    intro hi
    obtain ⟨x, hx, _⟩ := hP.choose_spec.left
    have hi' : P.A i ᵥ⬝ x = ⊥ := le_bot_iff.mp (hi ▸ hx i)
    obtain ⟨j, _, hj⟩ := WithBot.sum_eq_bot_iff.mp hi'
    have hA : P.A i j = ⊥ := by
      by_contra hn
      exact ef_smul_nonbot_neq_bot (x j) hn hj
    exact P.hbA ⟨i, ⟨j, hA⟩, hi⟩
  have no_bot_c (i : J) : P.dualize.b i ≠ ⊥ := by
    intro hi
    obtain ⟨x, hx, _⟩ := hQ.choose_spec.left
    have hi' : P.dualize.A i ᵥ⬝ x = ⊥ := le_bot_iff.mp (hi ▸ hx i)
    obtain ⟨j, _, hj⟩ := WithBot.sum_eq_bot_iff.mp hi'
    have hA : P.dualize.A i j = ⊥ := by
      by_contra hn
      exact ef_smul_nonbot_neq_bot (x j) hn hj
    exact P.dualize.hbA ⟨i, ⟨j, hA⟩, hi⟩
  have sum_elim_dot_weig_sum_elim {I : Type _} {J : Type _} [Fintype I] [Fintype J] (u : I → (Extend F)) (v : J → (Extend F)) (x : I → (NNeg F)) (y : J → (NNeg F)) :
      Sum.elim u v ᵥ⬝ Sum.elim x y = u ᵥ⬝ x + v ᵥ⬝ y := by
    simp [dotWeig]
  have Matrix_from_rows_mul_weig {J : Type _} [Fintype J] {I₁ : Type _} {I₂ : Type _} (M₁ : Matrix I₁ J (Extend F)) (M₂ : Matrix I₂ J (Extend F)) (w : J → (NNeg F)) :
      Matrix.fromRows M₁ M₂ ₘ* w = Sum.elim (M₁ ₘ* w) (M₂ ₘ* w) := by
    ext (_|_) <;> rfl
  have not_and_of_neq {P Q : Prop} (h : P ≠ Q) : ¬(P ∧ Q) := by tauto
  have weak_duality {p : Extend F} (hP : P.Reaches p)
      {q : Extend F} (hQ : P.dualize.Reaches q) : 0 ≤ p + q := by
    have hc : ¬∃ j : J, P.c j = ⊥ := fun ⟨j, hj⟩ => no_bot_c j hj
    obtain ⟨x, hx, rfl⟩ := hP
    obtain ⟨y, hy, rfl⟩ := hQ
    by_contra contr
    apply
      not_and_of_neq
        (extended_farkas
          (Matrix.fromRows P.A (Matrix.replicateRow Unit P.c))
          (Sum.elim P.b (fun _ => P.c ᵥ⬝ x))
          (by
            intro ⟨i, ⟨s, his⟩, ⟨t, hit⟩⟩
            cases i with
            | inl i' => exact P.hAi ⟨i', ⟨s, his⟩, ⟨t, hit⟩⟩
            | inr => exact hc ⟨s, his⟩
          )
          (by
            intro ⟨j, ⟨s, hjs⟩, ⟨t, hjt⟩⟩
            cases s with
            | inl iₛ =>
              cases t with
              | inl iₜ => exact P.hAj ⟨j, ⟨iₛ, hjs⟩, ⟨iₜ, hjt⟩⟩
              | inr => exact P.hAc ⟨j, ⟨iₛ, hjs⟩, hjt⟩
            | inr =>
              cases t with
              | inl iₜ => exact P.hcA ⟨j, ⟨iₜ, hjt⟩, hjs⟩
              | inr => simp_all
          )
          (by
            intro ⟨i, ⟨j, hij⟩, hi⟩
            cases i with
            | inl i' => exact P.hAb ⟨i', ⟨j, hij⟩, hi⟩
            | inr =>
              rw [Sum.elim_inr] at hi
              push Not at contr
              rw [hi] at contr
              match hby : P.b ᵥ⬝ y with
              | ⊥ =>
                change P.b ᵥ⬝ y = ⊥ at hby
                obtain ⟨i, _, hi⟩ := WithBot.sum_eq_bot_iff.mp hby
                exact no_bot_b i ((smul_eq_bot _ _).mp hi)
              | ⊤ =>
                dsimp only [ValidELP.dualize] at contr
                rw [hby] at contr
                change ⊤ + ⊤ < 0 at contr
                simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at contr
              | (q : F) =>
                dsimp only [ValidELP.dualize] at contr
                rw [hby] at contr
                change ⊤ + toE q < 0 at contr
                simp [ef_top_add_coe] at contr
          )
          (by
            intro ⟨i, ⟨j, hij⟩, hi⟩
            cases i with
            | inl i' => exact P.hbA ⟨i', ⟨j, hij⟩, hi⟩
            | inr => exact hc ⟨j, hij⟩
          )
        )
    constructor
    · use x
      rw [Matrix_from_rows_mul_weig, Sum.elim_le_elim_iff]
      exact ⟨hx, by rfl⟩
    · use Sum.elim y 1
      constructor
      · intro j
        have hj := (ef_sub_nonpos_iff _ _).mpr (hy j)
        simpa [ValidELP.dualize, Matrix.mulWeig, dotWeig, ef_one_smul] using hj
      · have hlt0 : P.b ᵥ⬝ y + P.c ᵥ⬝ x < 0
        · push Not at contr
          rwa [add_comm]
        rw [sum_elim_dot_weig_sum_elim]
        simp [dotWeig, ef_one_smul]
        exact hlt0
  have lp_unbounded_of_feasible_of_neg {I : Type _} {J : Type _} [Fintype J] (P : ValidELP I J F) (hP : P.IsFeasible) (nobot : ∀ i, P.b i ≠ ⊥)
      {x₀ : J → (NNeg F)} (hx₀ : P.c ᵥ⬝ x₀ < 0) (hAx₀ : P.A ₘ* x₀ + (0 : (NNeg F)) • (-P.b) ≤ 0) :
      P.IsUnbounded := by
    obtain ⟨e, ⟨xₚ, hxₚ, hce⟩, he⟩ := hP
    suffices ∀ s : F, ∃ p : Extend F, P.Reaches p ∧ p ≤ s by
      simp only [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy, not_exists, not_forall,
        exists_prop, not_le]
      intro r
      obtain ⟨p, hp, hpr⟩ := this (r - 1)
      exact ⟨p, hp, hpr.trans_lt (ef_coe_lt_coe_iff.mpr (sub_one_lt r))⟩
    intro s
    if hs : e ≤ s then
      refine ⟨e, ⟨xₚ, hxₚ, hce⟩, ?_⟩
      simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hs
    else
      push Not at hs
      match e with
      | ⊥ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hs
      | ⊤ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at he
      | (e : F) =>
        clear he
        match hcx₀ : P.c ᵥ⬝ x₀ with
        | ⊥ =>
          refine ⟨⊥, ⟨xₚ, hxₚ, ?_⟩, bot_le⟩
          change P.c ᵥ⬝ x₀ = ⊥ at hcx₀
          obtain ⟨j, _, hj⟩ := WithBot.sum_eq_bot_iff.mp hcx₀
          exact WithBot.sum_eq_bot_iff.mpr
            ⟨j, Finset.mem_univ j, (smul_eq_bot _ _).mpr ((smul_eq_bot _ _).mp hj)⟩
        | ⊤ =>
          exfalso
          rw [hcx₀] at hx₀
          exact (hx₀.trans_le le_top).false
        | (d : F) =>
          rw [hcx₀] at hx₀
          have coef_pos : 0 < (s - e) / d
          · apply div_pos_of_neg_of_neg
            · rwa [sub_neg, ←ef_coe_lt_coe_iff]
            · rwa [←ef_coe_neg']
          let k : (NNeg F) := ⟨((s - e) / d), coef_pos.le⟩
          let k_pos : 0 < k := coef_pos
          refine ⟨s, ⟨xₚ + k • x₀, ?_, ?_⟩, by rfl⟩
          · intro i
            match hi : P.b i with
            | ⊥ =>
              exfalso
              exact nobot i hi
            | ⊤ =>
              apply le_top
            | (bᵢ : F) =>
              specialize hAx₀ i
              rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hi] at hAx₀
              have zeros : (P.A ₘ* x₀) i + (0 : (Extend F)) ≤ 0
              · convert hAx₀ <;> try rfl
                show 0 = 0 • -(toE bᵢ)
                rw [←ef_coe_neg, ef_zero_smul_coe]
              rw [add_zero] at zeros
              change P.A i ᵥ⬝ (xₚ + k • x₀) ≤ toE bᵢ
              rw [dot_weig_add, dot_weig_smul k_pos]
              apply add_le_of_le_of_nonpos
              · change (P.A ₘ* xₚ) i ≤ toE bᵢ
                convert_to (P.A ₘ* xₚ) i ≤ P.b i
                · exact hi.symm
                exact hxₚ i
              · exact ef_smul_nonpos zeros k
          · rw [dot_weig_add, hce, dot_weig_smul k_pos, hcx₀]
            show toE (e + ((s - e) / d) * d) = toE s
            rw [ef_coe_eq_coe_iff, div_mul_cancel_of_imp]
            exact add_sub_cancel e s
            intro d_eq_0
            exfalso
            rw [d_eq_0] at hx₀
            exact hx₀.false
  have lp_infeasible_of_unbounded (hP : P.IsUnbounded) :
      ¬P.dualize.IsFeasible := by
    intro ⟨q, hPq, hq⟩
    simp only [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy, not_exists, not_forall,
      exists_prop, not_le] at hP
    match q with
    | ⊥ =>
      obtain ⟨p, hp, -⟩ := hP 0
      simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using weak_duality hp hPq
    | ⊤ =>
      exact hq rfl
    | (f : F) =>
      obtain ⟨p, hp, hpq⟩ := hP (-f)
      have wd := weak_duality hp hPq
      match p with
      | ⊥ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at wd
      | ⊤ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hpq
      | (_ : F) =>
        rw [←ef_coe_add, ←ef_coe_zero, ef_coe_le_coe_iff] at wd
        rw [ef_coe_lt_coe_iff] at hpq
        linarith
  have dot_weig_add_dual {J : Type _} [Fintype J] (x : J → (Extend F)) (v w : J → (NNeg F)) :
      x ᵥ⬝ (v + w) = x ᵥ⬝ v + x ᵥ⬝ w := by
    simp [dotWeig, ef_add_smul, Finset.sum_add_distrib]
  have dot_weig_smul_dual {J : Type _} [Fintype J] {k : (NNeg F)} (hk : 0 < k) (x : J → (Extend F)) (v : J → (NNeg F)) :
      x ᵥ⬝ (k • v) = k • (x ᵥ⬝ v) := by
    show ∑ j : J, (k * v j) • x j = k • ∑ j : J, v j • x j
    simp_rw [ef_mul_smul]
    exact (map_sum
      (⟨⟨(k • ·), smul_zero k⟩, ef_smul_add hk⟩ : Extend F →+ Extend F)
      (fun j => v j • x j) Finset.univ).symm
  have lp_unbounded_of_feasible_of_neg_dual {I : Type _} {J : Type _} [Fintype J] (P : ValidELP I J F) (hP : P.IsFeasible) (nobot : ∀ i, P.b i ≠ ⊥)
      {x₀ : J → (NNeg F)} (hx₀ : P.c ᵥ⬝ x₀ < 0) (hAx₀ : P.A ₘ* x₀ + (0 : (NNeg F)) • (-P.b) ≤ 0) :
      P.IsUnbounded := by
    obtain ⟨e, ⟨xₚ, hxₚ, hce⟩, he⟩ := hP
    suffices ∀ s : F, ∃ p : Extend F, P.Reaches p ∧ p ≤ s by
      simp only [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy, not_exists, not_forall,
        exists_prop, not_le]
      intro r
      obtain ⟨p, hp, hpr⟩ := this (r - 1)
      exact ⟨p, hp, hpr.trans_lt (ef_coe_lt_coe_iff.mpr (sub_one_lt r))⟩
    intro s
    if hs : e ≤ s then
      refine ⟨e, ⟨xₚ, hxₚ, hce⟩, ?_⟩
      simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hs
    else
      push Not at hs
      match e with
      | ⊥ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hs
      | ⊤ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at he
      | (e : F) =>
        clear he
        match hcx₀ : P.c ᵥ⬝ x₀ with
        | ⊥ =>
          refine ⟨⊥, ⟨xₚ, hxₚ, ?_⟩, bot_le⟩
          change P.c ᵥ⬝ x₀ = ⊥ at hcx₀
          obtain ⟨j, _, hj⟩ := WithBot.sum_eq_bot_iff.mp hcx₀
          exact WithBot.sum_eq_bot_iff.mpr
            ⟨j, Finset.mem_univ j, (smul_eq_bot _ _).mpr ((smul_eq_bot _ _).mp hj)⟩
        | ⊤ =>
          exfalso
          rw [hcx₀] at hx₀
          exact (hx₀.trans_le le_top).false
        | (d : F) =>
          rw [hcx₀] at hx₀
          have coef_pos : 0 < (s - e) / d
          · apply div_pos_of_neg_of_neg
            · rwa [sub_neg, ←ef_coe_lt_coe_iff]
            · rwa [←ef_coe_neg']
          let k : (NNeg F) := ⟨((s - e) / d), coef_pos.le⟩
          let k_pos : 0 < k := coef_pos
          refine ⟨s, ⟨xₚ + k • x₀, ?_, ?_⟩, by rfl⟩
          · intro i
            match hi : P.b i with
            | ⊥ =>
              exfalso
              exact nobot i hi
            | ⊤ =>
              apply le_top
            | (bᵢ : F) =>
              specialize hAx₀ i
              rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hi] at hAx₀
              have zeros : (P.A ₘ* x₀) i + (0 : (Extend F)) ≤ 0
              · convert hAx₀ <;> try rfl
                show 0 = 0 • -(toE bᵢ)
                rw [←ef_coe_neg, ef_zero_smul_coe]
              rw [add_zero] at zeros
              change P.A i ᵥ⬝ (xₚ + k • x₀) ≤ toE bᵢ
              rw [dot_weig_add_dual, dot_weig_smul_dual k_pos]
              apply add_le_of_le_of_nonpos
              · change (P.A ₘ* xₚ) i ≤ toE bᵢ
                convert_to (P.A ₘ* xₚ) i ≤ P.b i
                · exact hi.symm
                exact hxₚ i
              · exact ef_smul_nonpos zeros k
          · rw [dot_weig_add_dual, hce, dot_weig_smul_dual k_pos, hcx₀]
            show toE (e + ((s - e) / d) * d) = toE s
            rw [ef_coe_eq_coe_iff, div_mul_cancel_of_imp]
            exact add_sub_cancel e s
            intro d_eq_0
            exfalso
            rw [d_eq_0] at hx₀
            exact hx₀.false
  have lp_infeasible_of_unbounded_dual (hP : P.dualize.IsUnbounded) :
      ¬P.IsFeasible := by
    intro ⟨q, hPq, hq⟩
    simp only [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy, not_exists, not_forall,
      exists_prop, not_le] at hP
    match q with
    | ⊥ =>
      obtain ⟨p, hp, -⟩ := hP 0
      simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using weak_duality hPq hp
    | ⊤ =>
      exact hq rfl
    | (f : F) =>
      obtain ⟨p, hp, hpq⟩ := hP (-f)
      have wd : 0 ≤ p + toE f := by
        simpa only [add_comm] using weak_duality hPq hp
      match p with
      | ⊥ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at wd
      | ⊤ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hpq
      | (_ : F) =>
        rw [←ef_coe_add, ←ef_coe_zero, ef_coe_le_coe_iff] at wd
        rw [ef_coe_lt_coe_iff] at hpq
        linarith
  have or_of_neq {P Q : Prop} (h : P ≠ Q) : P ∨ Q := by tauto
  cases
    or_of_neq
      (extended_farkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.replicateRow Unit (Sum.elim P.c P.b)))
        (Sum.elim (Sum.elim P.b P.c) 0)
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ =>
                cases t with
                | inl jₜ => exact P.hAi ⟨i, ⟨⟨jₛ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hks⟩, ⟨jₜ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hkt⟩⟩⟩
                | inr iₜ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hkt
              | inr iₛ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hks
            | inr j =>
              cases t with
              | inl jₜ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hkt
              | inr iₜ =>
                cases s with
                | inl jₛ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hks
                | inr iₛ => exact P.hAj ⟨j, ⟨iₜ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hkt⟩, ⟨iₛ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hks⟩⟩
          | inr =>
            cases s with
            | inl jₛ => exact no_bot_c jₛ hks
            | inr iₛ => exact no_bot_b iₛ hks
        )
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl j =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => exact P.hAj ⟨j, ⟨⟨iₛ, hks⟩, ⟨iₜ, hkt⟩⟩⟩
                  | inr jₜ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hkt
                | inr => exact P.hAc ⟨j, ⟨iₛ, hks⟩, hkt⟩
              | inr jₛ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hks
            | inr => exact no_bot_c j hks
          | inr i =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hks
              | inr jₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hkt
                  | inr jₜ => exact P.hAi ⟨i, ⟨jₜ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hkt⟩, ⟨jₛ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hks⟩⟩
                | inr => exact P.hAb ⟨i, ⟨jₛ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hks⟩, hkt⟩
            | inr => exact no_bot_b i hks
        )
        (by
          intro ⟨k, ⟨t, hkt⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases t with
              | inl jₜ => exact P.hAb ⟨i, ⟨jₜ, hkt⟩, hk⟩
              | inr iₜ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hkt
            | inr j =>
              cases t with
              | inl jₜ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hkt
              | inr iₜ => exact P.hAc ⟨j, ⟨iₜ, by simpa [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hkt⟩, hk⟩
          | inr => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hk
        )
        (by
          intro ⟨k, ⟨s, hks⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ => exact no_bot_b i hk
              | inr iₛ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hks
            | inr j =>
              cases s with
              | inl jₛ => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hks
              | inr iₛ => exact no_bot_c j hk
          | inr => simp [ef_zero_neq_top, ef_zero_neq_bot, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hk
        )
      ) with
  | inl case_X =>
    obtain ⟨X, hX⟩ := case_X
    set x := X ∘ Sum.inl
    set y := X ∘ Sum.inr
    have hx : P.IsSolution x := by
      intro i
      simpa [x, Matrix.mulWeig, dotWeig] using hX (Sum.inl (Sum.inl i))
    have hy : P.dualize.IsSolution y := by
      intro j
      simpa [y, ValidELP.dualize, Matrix.mulWeig, dotWeig] using hX (Sum.inl (Sum.inr j))
    have hxy : P.c ᵥ⬝ x + P.b ᵥ⬝ y ≤ 0 := by
      simpa [x, y, Matrix.mulWeig, dotWeig] using hX (Sum.inr ())
    match hcx : P.c ᵥ⬝ x with
    | ⊥ =>
      exfalso
      obtain ⟨j, _, hj⟩ := WithBot.sum_eq_bot_iff.mp hcx
      have hj := (smul_eq_bot _ _).mp hj
      exact no_bot_c j hj
    | ⊤ =>
      exfalso
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        obtain ⟨i, _, hi⟩ := WithBot.sum_eq_bot_iff.mp hby
        have hi := (smul_eq_bot _ _).mp hi
        exact no_bot_b i hi
      | ⊤ =>
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt ef_zero_lt_top).false
      | (_ : F) =>
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt ef_zero_lt_top).false
    | (p : F) =>
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        exfalso
        obtain ⟨i, _, hi⟩ := WithBot.sum_eq_bot_iff.mp hby
        have hi := (smul_eq_bot _ _).mp hi
        exact no_bot_b i hi
      | ⊤ =>
        exfalso
        rw [hcx, hby] at hxy
        exact (hxy.trans_lt ef_zero_lt_top).false
      | (q : F) =>
        refine ⟨p, q, ⟨x, hx, hcx⟩, ⟨y, hy, hby⟩, ?_⟩
        rw [←ef_coe_le_coe_iff]
        rwa [hcx, hby] at hxy
  | inr case_Y =>
    obtain ⟨Y, hAY, hbc⟩ := case_Y
    set x := (Y ∘ Sum.inl) ∘ Sum.inr
    set y := (Y ∘ Sum.inl) ∘ Sum.inl
    set z := (Y ∘ Sum.inr) 0
    have hy : -P.Aᵀ ₘ* y + z • (-P.c) ≤ 0 := by
      intro j
      simpa [x, y, z, Matrix.mulWeig, dotWeig] using hAY (Sum.inl j)
    have hx : P.A ₘ* x + z • (-P.b) ≤ 0 := by
      intro i
      simpa [x, y, z, Matrix.mulWeig, dotWeig] using hAY (Sum.inr i)
    have hbc : P.b ᵥ⬝ y + P.c ᵥ⬝ x < 0 := by
      simpa [x, y, dotWeig] using hbc
    have z_pos : 0 < z
    · by_contra contr
      have z_eq_0 : z = 0
      · push Not at contr
        exact nonpos_iff_eq_zero.mp contr
      rw [z_eq_0] at hx hy
      clear contr z_eq_0 z
      if hxc : P.c ᵥ⬝ x < 0 then
        exact lp_infeasible_of_unbounded (lp_unbounded_of_feasible_of_neg P hP no_bot_b hxc hx) hQ
      else
        have hyb : P.b ᵥ⬝ y < 0
        · push Not at hxc
          by_contra! contr
          exact (hbc.trans_le (add_nonneg contr hxc)).false
        exact lp_infeasible_of_unbounded_dual (lp_unbounded_of_feasible_of_neg_dual P.dualize hQ no_bot_c hyb hy) hP
    match hcx : P.c ᵥ⬝ x with
    | ⊥ =>
      exfalso
      obtain ⟨j, _, hj⟩ := WithBot.sum_eq_bot_iff.mp hcx
      have hj := (smul_eq_bot _ _).mp hj
      exact no_bot_c j hj
    | ⊤ =>
      exfalso
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        obtain ⟨i, _, hi⟩ := WithBot.sum_eq_bot_iff.mp hby
        have hi := (smul_eq_bot _ _).mp hi
        exact no_bot_b i hi
      | ⊤ =>
        rw [hcx, hby] at hbc
        exact (hbc.trans ef_zero_lt_top).false
      | (_ : F) =>
        rw [hcx, hby] at hbc
        exact (hbc.trans ef_zero_lt_top).false
    | (p : F) =>
      match hby : P.b ᵥ⬝ y with
      | ⊥ =>
        exfalso
        obtain ⟨i, _, hi⟩ := WithBot.sum_eq_bot_iff.mp hby
        have hi := (smul_eq_bot _ _).mp hi
        exact no_bot_b i hi
      | ⊤ =>
        exfalso
        rw [hcx, hby] at hbc
        exact (hbc.trans ef_zero_lt_top).false
      | (q : F) =>
        have z_inv_pos : 0 < z⁻¹
        · exact inv_pos_of_pos z_pos
        refine ⟨z⁻¹ * p, z⁻¹ * q, ⟨z⁻¹ • x, ?_, ?_⟩, ⟨z⁻¹ • y, ?_, ?_⟩, ?_⟩
        · intro i
          have hi := (ef_smul_le_smul_left z_inv_pos _ _).mpr (hx i)
          change z⁻¹ • (P.A i ᵥ⬝ x + z • -P.b i) ≤ z⁻¹ • 0 at hi
          rw [smul_zero, ef_smul_add z_inv_pos, ←ef_mul_smul,
            inv_mul_cancel₀ z_pos.ne', ef_one_smul, ef_sub_nonpos_iff] at hi
          change P.A i ᵥ⬝ (z⁻¹ • x) ≤ P.b i
          rwa [dot_weig_smul z_inv_pos]
        · rewrite [dot_weig_smul z_inv_pos, hcx]
          rfl
        · intro i
          have hi := (ef_smul_le_smul_left z_inv_pos _ _).mpr (hy i)
          change z⁻¹ • ((-P.Aᵀ) i ᵥ⬝ y + z • -P.c i) ≤ z⁻¹ • 0 at hi
          rw [smul_zero, ef_smul_add z_inv_pos, ←ef_mul_smul,
            inv_mul_cancel₀ z_pos.ne', ef_one_smul, ef_sub_nonpos_iff] at hi
          change (-P.Aᵀ) i ᵥ⬝ (z⁻¹ • y) ≤ P.c i
          rwa [dot_weig_smul_dual z_inv_pos]
        · dsimp only [ValidELP.dualize]
          rewrite [dot_weig_smul_dual z_inv_pos, hby]
          rfl
        rw [hcx, hby] at hbc
        show z⁻¹ * p + z⁻¹ * q ≤ 0
        rw [←mul_add]
        have hpq : p + q < 0
        · rw [←ef_coe_lt_coe_iff, add_comm]
          exact hbc
        exact mul_nonpos_of_nonneg_of_nonpos
          (show (0 : F) ≤ ((z⁻¹ : NNeg F) : F) from z_inv_pos.le) hpq.le

lemma ValidELP.strong_duality_of_both_feasible (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : F, P.Reaches (toE (-r)) ∧ P.dualize.Reaches (toE r) := by
  classical
  have ef_coe_strict_mono : StrictMono (toE (F := F)) :=
    WithBot.coe_strictMono.comp WithTop.coe_strictMono
  have ef_coe_le_coe_iff {x y : F} : (x : Extend F) ≤ (y : Extend F) ↔ x ≤ y :=
    ef_coe_strict_mono.le_iff_le
  have ef_coe_zero : ((0 : F) : Extend F) = 0 := rfl
  have ef_coe_add (x y : F) : toE (x + y) = toE x + toE y :=
    rfl
  obtain ⟨p, q, hp, hq, hpq⟩ := P.strong_duality_aux hP hQ
  have ef_bot_lt_coe (x : F) : (⊥ : Extend F) < x :=
    WithBot.bot_lt_coe _
  have ef_coe_neq_bot (x : F) : (x : Extend F) ≠ ⊥ :=
    (ef_bot_lt_coe x).ne'
  have ef_coe_lt_top (x : F) : (x : Extend F) < ⊤ :=
    WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _
  have ef_coe_neq_top (x : F) : (x : Extend F) ≠ ⊤ :=
    (ef_coe_lt_top x).ne
  have ef_zero_neq_top : (0 : Extend F) ≠ ⊤ :=
    ef_coe_neq_top 0
  have ef_add_bot (x : Extend F) : x + ⊥ = ⊥ :=
    WithBot.add_bot x
  have ef_bot_add (x : Extend F) : ⊥ + x = ⊥ :=
    WithBot.bot_add x
  have ef_top_add_top : (⊤ : Extend F) + ⊤ = ⊤ :=
    rfl
  have ef_top_add_coe (x : F) : (⊤ : Extend F) + x = ⊤ :=
    rfl
  have ef_coe_add_top (x : F) : (x : Extend F) + ⊤ = ⊤ :=
    rfl
  have ef_pos_smul_top {c : (NNeg F)} (hc : 0 < c) : c • (⊤ : (Extend F)) = ⊤ := by
    change (if c = 0 then 0 else (⊤ : Extend F)) = ⊤
    simp [hc.ne.symm]
  have ef_one_smul (r : (Extend F)) : (1 : (NNeg F)) • r = r := by
    match r with
    | ⊥ => rfl
    | ⊤ =>
      exact ef_pos_smul_top (show (0 : NNeg F) < 1 from zero_lt_one)
    | (q : F) => exact congr_arg toE (one_mul q)
  have ef_sub_nonpos_iff (r s : Extend F) : r + (-s) ≤ 0 ↔ r ≤ s := by
    match r, s with
    | ⊥, _ => simp only [ef_bot_add, bot_le]
    | r, ⊤ =>
      change r + ⊥ ≤ 0 ↔ r ≤ ⊤
      simp only [ef_add_bot, bot_le, le_top]
    | ⊤, ⊥ =>
      change (⊤ : Extend F) + ⊤ ≤ 0 ↔ (⊤ : Extend F) ≤ ⊥
      simp [ef_top_add_top, ef_zero_neq_top]
    | ⊤, (q : F) =>
      change (⊤ : Extend F) + toE (-q) ≤ 0 ↔ (⊤ : Extend F) ≤ toE q
      simp [ef_top_add_coe, ef_zero_neq_top, ef_coe_neq_top]
    | (p : F), ⊥ =>
      change toE p + ⊤ ≤ 0 ↔ toE p ≤ (⊥ : Extend F)
      simp [ef_coe_add_top, ef_zero_neq_top, ef_coe_neq_bot]
    | (p : F), (q : F) =>
      change toE p + toE (-q) ≤ toE 0 ↔ toE p ≤ toE q
      rw [←ef_coe_add, ef_coe_le_coe_iff, ef_coe_le_coe_iff]
      simpa only [sub_eq_add_neg] using (sub_nonpos : p - q ≤ 0 ↔ p ≤ q)
  have sum_elim_dot_weig_sum_elim {I : Type _} {J : Type _} [Fintype I] [Fintype J] (u : I → (Extend F)) (v : J → (Extend F)) (x : I → (NNeg F)) (y : J → (NNeg F)) :
      Sum.elim u v ᵥ⬝ Sum.elim x y = u ᵥ⬝ x + v ᵥ⬝ y := by
    simp [dotWeig]
  have Matrix_from_rows_mul_weig {J : Type _} [Fintype J] {I₁ : Type _} {I₂ : Type _} (M₁ : Matrix I₁ J (Extend F)) (M₂ : Matrix I₂ J (Extend F)) (w : J → (NNeg F)) :
      Matrix.fromRows M₁ M₂ ₘ* w = Sum.elim (M₁ ₘ* w) (M₂ ₘ* w) := by
    ext (_|_) <;> rfl
  have not_and_of_neq {P Q : Prop} (h : P ≠ Q) : ¬(P ∧ Q) := by tauto
  have h0pq : 0 ≤ p + q := by
    rw [←ef_coe_le_coe_iff, ef_coe_add, ef_coe_zero]
    obtain ⟨x, hx, hcx⟩ := hp
    obtain ⟨y, hy, hby⟩ := hq
    have hc : ¬∃ j : J, P.c j = ⊥ := by
      intro ⟨j, hj⟩
      have hb : P.c ᵥ⬝ x = ⊥ :=
        WithBot.sum_eq_bot_iff.mpr ⟨j, Finset.mem_univ j, by rw [hj]; rfl⟩
      exact ef_coe_neq_bot p (hcx ▸ hb)
    rw [←hcx, ←hby]
    by_contra contr
    apply
      not_and_of_neq
        (extended_farkas
          (Matrix.fromRows P.A (Matrix.replicateRow Unit P.c))
          (Sum.elim P.b (fun _ => P.c ᵥ⬝ x))
          (by
            intro ⟨i, ⟨s, his⟩, ⟨t, hit⟩⟩
            cases i with
            | inl i' => exact P.hAi ⟨i', ⟨s, his⟩, ⟨t, hit⟩⟩
            | inr => exact hc ⟨s, his⟩
          )
          (by
            intro ⟨j, ⟨s, hjs⟩, ⟨t, hjt⟩⟩
            cases s with
            | inl iₛ =>
              cases t with
              | inl iₜ => exact P.hAj ⟨j, ⟨iₛ, hjs⟩, ⟨iₜ, hjt⟩⟩
              | inr => exact P.hAc ⟨j, ⟨iₛ, hjs⟩, hjt⟩
            | inr =>
              cases t with
              | inl iₜ => exact P.hcA ⟨j, ⟨iₜ, hjt⟩, hjs⟩
              | inr => simp_all
          )
          (by
            intro ⟨i, ⟨j, hij⟩, hi⟩
            cases i with
            | inl i' => exact P.hAb ⟨i', ⟨j, hij⟩, hi⟩
            | inr =>
              rw [Sum.elim_inr, hcx] at hi
              exact ef_coe_neq_top p hi
          )
          (by
            intro ⟨i, ⟨j, hij⟩, hi⟩
            cases i with
            | inl i' => exact P.hbA ⟨i', ⟨j, hij⟩, hi⟩
            | inr => exact hc ⟨j, hij⟩
          )
        )
    constructor
    · use x
      rw [Matrix_from_rows_mul_weig, Sum.elim_le_elim_iff]
      exact ⟨hx, by rfl⟩
    · use Sum.elim y 1
      constructor
      · intro j
        have hj := (ef_sub_nonpos_iff _ _).mpr (hy j)
        simpa [ValidELP.dualize, Matrix.mulWeig, dotWeig, ef_one_smul] using hj
      · have hlt0 : P.b ᵥ⬝ y + P.c ᵥ⬝ x < 0
        · push Not at contr
          rwa [add_comm]
        rw [sum_elim_dot_weig_sum_elim]
        simp [dotWeig, ef_one_smul]
        exact hlt0
  have hqp : -q = p
  · rw [neg_eq_iff_add_eq_zero, add_comm]
    exact le_antisymm hpq h0pq
  exact ⟨q, hqp ▸ hp, hq⟩

end

end D5.S3.Analytic.Convexity.FiniteStrongDuality
