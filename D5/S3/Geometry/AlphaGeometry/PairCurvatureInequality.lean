/- GID: D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/PairCurvatureInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positivity and strict ratio growth for the two-coordinate curvature pair. -/

/-

admission_basis: escape-witness
escape_witness: key_pos
Direct frozen dependencies: none; all prerequisites are pinned Mathlib or this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15483
Per-declaration judgement form (definitions carry no new-content claim):
proof_shape: E: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: P: bind-only; consumer=LogScalarCurvatureMonotone.formula; witness=none
proof_shape: E_evalSum: bind-only; consumer=PairCurvatureInequality.E_one_eq_sum; witness=none
proof_shape: P_evalSum: bind-only; consumer=LogScalarCurvatureMonotone.powerSum_perm; witness=none
proof_shape: E_one_eq_sum: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: anti2: bind-only; consumer=PairCurvatureInequality.newton2; witness=none
proof_shape: anti3: bind-only; consumer=PairCurvatureInequality.newton3; witness=none
proof_shape: anti4: bind-only; consumer=PairCurvatureInequality.newton4; witness=none
proof_shape: filt2: bind-only; consumer=PairCurvatureInequality.newton2; witness=none
proof_shape: filt3: bind-only; consumer=PairCurvatureInequality.newton3; witness=none
proof_shape: filt4: bind-only; consumer=PairCurvatureInequality.newton4; witness=none
proof_shape: newton2: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: newton3: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: newton4: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: pairT: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: pairN: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: pairK: bind-only; consumer=LogScalarCurvatureMonotone.nonnegative_pair_K; witness=none
proof_shape: pairR: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: mixProduct: bind-only; consumer=LogScalarCurvatureMonotone.strict_mix_formula_nonnegative_rest; witness=none
proof_shape: coordinateB_le_sum_sq: bind-only; consumer=LogScalarCurvatureMonotone.nonnegative_pair_invariants; witness=none
proof_shape: coordinateQ: bind-only; consumer=PairCurvatureInequality.coordinateQ_expand; witness=none
proof_shape: coordinateQ_expand: bind-only; consumer=PairCurvatureInequality.coordinate_key_identity; witness=none
proof_shape: coordinateQ_nonneg: bind-only; consumer=PairCurvatureInequality.coordinate_key_pos; witness=none
proof_shape: coordinateB_pos: bind-only; consumer=LogScalarCurvatureMonotone.strict_mix_formula_nonnegative_rest; witness=none
proof_shape: key_identity: bind-only; consumer=PairCurvatureInequality.coordinate_key_identity; witness=none
proof_shape: key_pos: content; consumer=PairCurvatureInequality.pairK_pos_of_identity; witness=key_pos
proof_shape: pairK_pos_of_identity: content; consumer=PairCurvatureInequality.coordinate_key_pos; witness=key_pos
proof_shape: pairT_pos: bind-only; consumer=LogScalarCurvatureMonotone.strict_mix_formula_nonnegative_rest; witness=none
proof_shape: secant_cross: bind-only; consumer=PairCurvatureInequality.ratio_strict_increase; witness=none
proof_shape: ratio_strict_increase: bind-only; consumer=LogScalarCurvatureMonotone.strict_mix_formula_nonnegative_rest; witness=none
proof_shape: coordinate_key_identity: bind-only; consumer=PairCurvatureInequality.coordinate_key_pos; witness=none
proof_shape: coordinate_key_pos: content; consumer=LogScalarCurvatureMonotone.nonnegative_pair_K; witness=key_pos
proof_shape: ttransform_product_increase: bind-only; consumer=LogScalarCurvatureMonotone.strict_mix_formula_nonnegative_rest; witness=none
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Algebra.Order.Archimedean.Real.Basic


noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.AlphaGeometry.PairCurvatureInequality


def E (r : ℕ) (z : Fin r → ℝ) (k : ℕ) : ℝ :=
  MvPolynomial.aeval z (MvPolynomial.esymm (Fin r) ℝ k)

def P (r : ℕ) (z : Fin r → ℝ) (k : ℕ) : ℝ :=
  MvPolynomial.aeval z (MvPolynomial.psum (Fin r) ℝ k)

lemma E_evalSum (r : ℕ) (z : Fin r → ℝ) (k : ℕ) :
    E r z k = ∑ s ∈ Finset.powersetCard k (Finset.univ : Finset (Fin r)), ∏ i ∈ s, z i := by
  simp [E, MvPolynomial.esymm, MvPolynomial.aeval_def]

lemma P_evalSum (r : ℕ) (z : Fin r → ℝ) (k : ℕ) : P r z k = ∑ i, z i ^ k := by
  simp [P, MvPolynomial.psum, MvPolynomial.aeval_def]

lemma E_one_eq_sum (r : ℕ) (z : Fin r → ℝ) : E r z 1 = ∑ i, z i := by
  simp [E_evalSum, Finset.powersetCard_one]

private lemma anti2 : (Finset.HasAntidiagonal.antidiagonal 2 : Finset (ℕ × ℕ)) =
    {(0, 2), (1, 1), (2, 0)} := by
  exact Finset.val_inj.mp rfl

private lemma anti3 : (Finset.HasAntidiagonal.antidiagonal 3 : Finset (ℕ × ℕ)) =
    {(0, 3), (1, 2), (2, 1), (3, 0)} := by
  exact Finset.val_inj.mp rfl

private lemma anti4 : (Finset.HasAntidiagonal.antidiagonal 4 : Finset (ℕ × ℕ)) =
    {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by
  exact Finset.val_inj.mp rfl

private lemma filt2 : ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)).filter
      (fun a => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by
  ext a
  rcases a with ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Set.mem_Ioo]
  constructor
  · rintro ⟨h, ha, hb⟩
    rcases h with h | h | h
    · injection h with h0 h2; omega
    · exact h
    · injection h with h2 h0; omega
  · intro h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    exact ⟨Or.inr (Or.inl h), by omega, by omega⟩

private lemma filt3 : ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)).filter
      (fun a => a.1 ∈ Set.Ioo 0 3) = {(1, 2), (2, 1)} := by
  ext a
  rcases a with ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Set.mem_Ioo]
  constructor
  · rintro ⟨h, ha, hb⟩
    rcases h with h | h | h | h
    · injection h with h0 h3; omega
    · exact Or.inl h
    · exact Or.inr h
    · injection h with h3 h0; omega
  · rintro (h | h)
    · have ha := congrArg Prod.fst h; have hb := congrArg Prod.snd h
      exact ⟨Or.inr (Or.inl h), by omega, by omega⟩
    · have ha := congrArg Prod.fst h; have hb := congrArg Prod.snd h
      exact ⟨Or.inr (Or.inr (Or.inl h)), by omega, by omega⟩

private lemma filt4 : ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)).filter
      (fun a => a.1 ∈ Set.Ioo 0 4) = {(1, 3), (2, 2), (3, 1)} := by
  ext a
  rcases a with ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Set.mem_Ioo]
  constructor
  · rintro ⟨h, ha, hb⟩
    rcases h with h | h | h | h | h
    · injection h with h0 h4; omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · injection h with h4 h0; omega
  · rintro (h | h | h)
    · have ha := congrArg Prod.fst h; have hb := congrArg Prod.snd h
      exact ⟨Or.inr (Or.inl h), by omega, by omega⟩
    · have ha := congrArg Prod.fst h; have hb := congrArg Prod.snd h
      exact ⟨Or.inr (Or.inr (Or.inl h)), by omega, by omega⟩
    · have ha := congrArg Prod.fst h; have hb := congrArg Prod.snd h
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by omega, by omega⟩

lemma newton2 (r : ℕ) (z : Fin r → ℝ) :
    P r z 2 = (E r z 1) ^ 2 - 2 * E r z 2 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin r) ℝ 2 (by norm_num)
  rw [anti2, filt2] at h
  have h' := congrArg (MvPolynomial.aeval z) h
  simp [P, E, MvPolynomial.psum, MvPolynomial.esymm,
    MvPolynomial.aeval_def, map_sum, map_prod, map_pow, Finset.powersetCard_one]
    at h' ⊢
  nlinarith [h']

lemma newton3 (r : ℕ) (z : Fin r → ℝ) :
    P r z 3 = (∑ i, z i) ^ 3 - 3 * (∑ i, z i) * E r z 2 + 3 * E r z 3 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin r) ℝ 3 (by norm_num)
  rw [anti3, filt3] at h
  have h' := congrArg (MvPolynomial.aeval z) h
  have h2 := newton2 r z
  simp [P, E, MvPolynomial.psum, MvPolynomial.esymm,
    MvPolynomial.aeval_def, map_sum, map_prod, map_pow, Finset.powersetCard_one]
    at h' h2 ⊢
  rw [h2] at h'
  nlinarith [h']

lemma newton4 (r : ℕ) (z : Fin r → ℝ) :
    P r z 4 = (∑ i, z i) ^ 4 - 4 * (∑ i, z i) ^ 2 * E r z 2 +
      2 * (E r z 2) ^ 2 + 4 * (∑ i, z i) * E r z 3 - 4 * E r z 4 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin r) ℝ 4 (by norm_num)
  rw [anti4, filt4] at h
  have h' := congrArg (MvPolynomial.aeval z) h
  have h2 := newton2 r z
  have h3 := newton3 r z
  simp [P, E, MvPolynomial.psum, MvPolynomial.esymm,
    MvPolynomial.aeval_def, map_sum, map_prod, map_pow, Finset.powersetCard_one]
    at h' h2 h3 ⊢
  rw [h2, h3] at h'
  nlinarith [h']

def pairT (u v B : ℝ) : ℝ := u ^ 2 - 2 * v + B

def pairN (u v A B E₂ E₃ E₄ : ℝ) : ℝ :=
  v * A + u * E₂ + E₃ - 4 * (v * E₂ + u * E₃ + E₄)

def pairK (u v A B E₂ E₃ E₄ : ℝ) : ℝ :=
  (A - 4 * E₂) * pairT u v B + 4 * pairN u v A B E₂ E₃ E₄

def pairR (u A B E₂ E₃ E₄ : ℝ) (v : ℝ) : ℝ :=
  2 * pairN u v A B E₂ E₃ E₄ / pairT u v B ^ 2

def mixProduct (a b t : ℝ) : ℝ :=
  ((1 - t) * a + t * b) * (t * a + (1 - t) * b)

theorem coordinateB_le_sum_sq {r : ℕ} (z : Fin r → ℝ) (hz : ∀ i, 0 ≤ z i) :
    P _ z 2 ≤ (∑ i, z i) ^ 2 := by
  simpa only [P_evalSum] using Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hz i)

private def coordinateQ {r : ℕ} (z : Fin r → ℝ) : ℝ :=
  ∑ i, z i ^ 2 * (1 - 2 * z i) ^ 2

private theorem coordinateQ_expand {r : ℕ} (z : Fin r → ℝ) :
    coordinateQ z = P _ z 2 - 4 * P r z 3 +
      4 * P r z 4 := by
  simp only [coordinateQ, P_evalSum]
  calc
    (∑ i, z i ^ 2 * (1 - 2 * z i) ^ 2) =
        ∑ i, (z i ^ 2 - 4 * z i ^ 3 + 4 * z i ^ 4) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, z i ^ 2) - 4 * (∑ i, z i ^ 3) +
        4 * (∑ i, z i ^ 4) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]

private theorem coordinateQ_nonneg {r : ℕ} (z : Fin r → ℝ) : 0 ≤ coordinateQ z := by
  dsimp [coordinateQ]
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem coordinateB_pos {r : ℕ} (z : Fin r → ℝ)
    (hz : ∃ i, 0 < z i) : 0 < P _ z 2 := by
  simp only [P_evalSum]
  apply Finset.sum_pos' (fun i hi => sq_nonneg (z i))
  rcases hz with ⟨i, hi⟩
  exact ⟨i, Finset.mem_univ _, sq_pos_of_pos hi⟩

private theorem key_identity
    (u v A B E₂ E₃ E₄ p₃ p₄ : ℝ)
    (hA : A = 1 - u)
    (h₂ : A ^ 2 = B + 2 * E₂)
    (h₃ : p₃ = A ^ 3 - 3 * A * E₂ + 3 * E₃)
    (h₄ : p₄ = A ^ 4 - 4 * A ^ 2 * E₂ + 2 * E₂ ^ 2 +
      4 * A * E₃ - 4 * E₄) :
    pairK u v A B E₂ E₃ E₄ =
      (B - 4 * p₃ + 4 * p₄) + u * (3 - 4 * u) * B +
        u ^ 2 * (1 - u) + v * (4 * B - 4 * u ^ 2 + 6 * u - 2) := by
  subst A
  subst p₃
  subst p₄
  dsimp [pairK, pairN, pairT]
  rw [← sub_eq_zero]
  calc
    _ = -4 * (-E₂ + u ^ 2 - u - v) * ((1 - u) ^ 2 - B - 2 * E₂) := by ring
    _ = 0 := by rw [h₂]; ring

theorem key_pos
    {u v B q : ℝ}
    (hq : 0 ≤ q)
    (hu₀ : 0 < u) (hu₁ : u < 1)
    (hv₀ : 0 < v) (hv₁ : v ≤ u ^ 2 / 4)
    (hB₀ : 0 < B) (hB₁ : B ≤ (1 - u) ^ 2) :
    q + u * (3 - 4 * u) * B + u ^ 2 * (1 - u) +
        v * (4 * B - 4 * u ^ 2 + 6 * u - 2) > 0 := by
  by_cases hu : u ≤ 1 / 2
  · by_cases hC : 0 ≤ 4 * B - 4 * u ^ 2 + 6 * u - 2
    · have hcoef : 0 ≤ 3 - 4 * u := by nlinarith
      have hterm : 0 ≤ u * (3 - 4 * u) * B :=
        mul_nonneg (mul_nonneg (le_of_lt hu₀) hcoef) (le_of_lt hB₀)
      have hlast : 0 < u ^ 2 * (1 - u) := by
        exact mul_pos (sq_pos_of_pos hu₀) (sub_pos.mpr hu₁)
      nlinarith
    · have hC' : 4 * B - 4 * u ^ 2 + 6 * u - 2 < 0 := lt_of_not_ge hC
      have hvC : v * (4 * B - 4 * u ^ 2 + 6 * u - 2) ≥
          (u ^ 2 / 4) * (4 * B - 4 * u ^ 2 + 6 * u - 2) := by
        nlinarith
      have hbase₁ : 0 < 3 * u * (1 - u) * B := by positivity
      have hbase₂ : 0 < u ^ 2 * (1 - u) * (u + 1 / 2 : ℝ) := by positivity
      have hbase : 0 < 3 * u * (1 - u) * B +
          u ^ 2 * (1 - u) * (u + 1 / 2 : ℝ) := add_pos hbase₁ hbase₂
      nlinarith [hbase]
  · have hu' : 1 / 2 < u := lt_of_not_ge hu
    have hC : 0 ≤ 4 * B - 4 * u ^ 2 + 6 * u - 2 := by
      nlinarith [sq_nonneg (1 - u)]
    by_cases hu₂ : u ≤ 3 / 4
    · have hlast : 0 < u ^ 2 * (1 - u) := by
        exact mul_pos (sq_pos_of_pos hu₀) (sub_pos.mpr hu₁)
      have hvterm : 0 ≤ v * (4 * B - 4 * u ^ 2 + 6 * u - 2) :=
        mul_nonneg (le_of_lt hv₀) hC
      have hcoef : 0 ≤ 3 - 4 * u := by nlinarith
      have hterm : 0 ≤ u * (3 - 4 * u) * B :=
        mul_nonneg (mul_nonneg (le_of_lt hu₀) hcoef) (le_of_lt hB₀)
      nlinarith
    · have hu₂' : 3 / 4 < u := lt_of_not_ge hu₂
      have hcoef : u * (3 - 4 * u) ≤ 0 := by nlinarith
      have hBterm : u * (3 - 4 * u) * B ≥
          u * (3 - 4 * u) * (1 - u) ^ 2 := by
        nlinarith
      have hpoly : 0 < 4 * u ^ 2 - 6 * u + 3 := by
        nlinarith [sq_nonneg (2 * u - 3 / 2)]
      have hbase : 0 < u * (1 - u) * (4 * u ^ 2 - 6 * u + 3) := by
        exact mul_pos (mul_pos hu₀ (sub_pos.mpr hu₁)) hpoly
      have hvterm : 0 ≤ v * (4 * B - 4 * u ^ 2 + 6 * u - 2) :=
        mul_nonneg (le_of_lt hv₀) hC
      nlinarith

private theorem pairK_pos_of_identity
    {u v A B E₂ E₃ E₄ q : ℝ}
    (hkey : pairK u v A B E₂ E₃ E₄ =
      q + u * (3 - 4 * u) * B + u ^ 2 * (1 - u) +
        v * (4 * B - 4 * u ^ 2 + 6 * u - 2))
    (hq : 0 ≤ q)
    (hu₀ : 0 < u) (hu₁ : u < 1)
    (hv₀ : 0 < v) (hv₁ : v ≤ u ^ 2 / 4)
    (hB₀ : 0 < B) (hB₁ : B ≤ (1 - u) ^ 2) :
    0 < pairK u v A B E₂ E₃ E₄ := by
  rw [hkey]
  exact key_pos hq hu₀ hu₁ hv₀ hv₁ hB₀ hB₁

theorem pairT_pos
    {u v B : ℝ} (hu₀ : 0 < u) (hv₁ : v ≤ u ^ 2 / 4) (hB₀ : 0 < B) :
    0 < pairT u v B := by
  dsimp [pairT]
  nlinarith [sq_nonneg u]

private theorem secant_cross
    (u A B E₂ E₃ E₄ v₁ v₂ : ℝ) :
    pairN u v₂ A B E₂ E₃ E₄ * pairT u v₁ B ^ 2 -
      pairN u v₁ A B E₂ E₃ E₄ * pairT u v₂ B ^ 2 =
      (v₂ - v₁) *
      (pairT u v₁ B * pairK u v₂ A B E₂ E₃ E₄ +
        pairT u v₂ B * pairK u v₁ A B E₂ E₃ E₄) / 2 := by
  dsimp [pairN, pairT, pairK]
  ring

theorem ratio_strict_increase
    {u A B E₂ E₃ E₄ v₁ v₂ : ℝ}
    (hv : v₁ < v₂)
    (hT₁ : 0 < pairT u v₁ B) (hT₂ : 0 < pairT u v₂ B)
    (hK₁ : 0 < pairK u v₁ A B E₂ E₃ E₄)
    (hK₂ : 0 < pairK u v₂ A B E₂ E₃ E₄) :
    2 * pairN u v₁ A B E₂ E₃ E₄ / pairT u v₁ B ^ 2 <
      2 * pairN u v₂ A B E₂ E₃ E₄ / pairT u v₂ B ^ 2 := by
  have hden₁ : 0 < pairT u v₁ B ^ 2 := sq_pos_of_pos hT₁
  have hden₂ : 0 < pairT u v₂ B ^ 2 := sq_pos_of_pos hT₂
  have hsec : 0 <
      pairN u v₂ A B E₂ E₃ E₄ * pairT u v₁ B ^ 2 -
        pairN u v₁ A B E₂ E₃ E₄ * pairT u v₂ B ^ 2 := by
    have hsum : 0 <
        pairT u v₁ B * pairK u v₂ A B E₂ E₃ E₄ +
          pairT u v₂ B * pairK u v₁ A B E₂ E₃ E₄ := by positivity
    have hcross := secant_cross u A B E₂ E₃ E₄ v₁ v₂
    have hdiff : 0 < v₂ - v₁ := sub_pos.mpr hv
    nlinarith
  apply (div_lt_div_iff₀ hden₁ hden₂).2
  nlinarith



private theorem coordinate_key_identity {r : ℕ} (z : Fin r → ℝ)
    (u v A B E₂ E₃ E₄ : ℝ)
    (hA : A = 1 - u)
    (hAsum : A = ∑ i, z i)
    (hB : B = P _ z 2)
    (hE₂ : E₂ = E r z 2) (hE₃ : E₃ = E r z 3) (hE₄ : E₄ = E r z 4) :
    pairK u v A B E₂ E₃ E₄ =
      coordinateQ z + u * (3 - 4 * u) * B + u ^ 2 * (1 - u) +
        v * (4 * B - 4 * u ^ 2 + 6 * u - 2) := by
  have hn₂ := newton2 r z
  have hn₃ := newton3 r z
  have hn₄ := newton4 r z
  have h₂ : A ^ 2 = B + 2 * E₂ := by
    have hE₁ := E_one_eq_sum r z
    rw [hE₁] at hn₂
    simp only [P_evalSum] at hn₂
    rw [hAsum, hB, hE₂]
    simp only [P_evalSum]
    nlinarith [hn₂]
  have h₃ : P r z 3 = A ^ 3 - 3 * A * E₂ + 3 * E₃ := by
    rw [hAsum, hE₂, hE₃]
    exact hn₃
  have h₄ : P r z 4 = A ^ 4 - 4 * A ^ 2 * E₂ + 2 * E₂ ^ 2 +
      4 * A * E₃ - 4 * E₄ := by
    rw [hAsum, hE₂, hE₃, hE₄]
    exact hn₄
  have hk := key_identity u v A B E₂ E₃ E₄ (P r z 3) (P r z 4)
    hA h₂ h₃ h₄
  rw [coordinateQ_expand, hB]
  rw [hB] at hk
  simp only [P_evalSum] at hk ⊢
  nlinarith [hk]


theorem coordinate_key_pos {r : ℕ} (z : Fin r → ℝ)
    (u v A B E₂ E₃ E₄ : ℝ)
    (hA : A = 1 - u)
    (hAsum : A = ∑ i, z i)
    (hB : B = P _ z 2)
    (hE₂ : E₂ = E r z 2) (hE₃ : E₃ = E r z 3) (hE₄ : E₄ = E r z 4)
    (hz : ∃ i, 0 < z i)
    (hu₀ : 0 < u) (hu₁ : u < 1)
    (hv₀ : 0 < v) (hv₁ : v ≤ u ^ 2 / 4)
    (hB₁ : B ≤ (1 - u) ^ 2) :
    0 < pairK u v A B E₂ E₃ E₄ := by
  apply pairK_pos_of_identity (q := coordinateQ z)
  · exact coordinate_key_identity z u v A B E₂ E₃ E₄ hA hAsum hB hE₂ hE₃ hE₄
  · exact coordinateQ_nonneg z
  · exact hu₀
  · exact hu₁
  · exact hv₀
  · exact hv₁
  · rw [hB]
    exact coordinateB_pos z hz
  · exact hB₁


theorem ttransform_product_increase {a b lam : ℝ}
    (hl₀ : 0 < lam) (hl₁ : lam < 1) (hab : a ≠ b) :
    a * b < (lam * a + (1 - lam) * b) * ((1 - lam) * a + lam * b) := by
  have hsq : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hl : 0 < lam * (1 - lam) := mul_pos hl₀ (sub_pos.mpr hl₁)
  nlinarith



end D5.S3.Geometry.AlphaGeometry.PairCurvatureInequality
