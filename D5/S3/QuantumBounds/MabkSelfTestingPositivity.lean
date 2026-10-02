/- GID: D5/S3/QuantumBounds/MabkSelfTestingPositivity
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/MabkSelfTestingPositivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cao-Zhang-Shi-Zhao MABK positivity for h = 1, 2 on the whole cube, all n >= 6. -/
/-
proof_shape: result: content; product_gap: content; block_bound: content
escape_witness: result, via the block product gap and the two scalar positivity estimates.
Private content: product_gap uses finite-set induction; block_bound separates the cardinality
  one and two branches and establishes the corresponding scalar estimates.
admission_basis: open-problem-resolution (#11561; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumBounds.MabkSelfTestingPositivity

open Finset

noncomputable def kappa : ℝ := 1 - 1 / Real.sqrt 2

/-- The five-term expression in the supplemental material of arXiv:2608.30851v1. -/
noncomputable def lambdaA (n : ℕ) (T : Finset (Fin n)) (v : Fin n → ℝ) : ℝ :=
  let c := (1 + Real.sqrt 2) / Real.sqrt 2
  1 + c ^ n * (∏ j : Fin n, v j * (1 - c * v j))
    + Real.sqrt 2 * ((∏ j ∈ T, (1 - c * v j)) * (∏ j ∈ Tᶜ, c * v j)
      + (∏ j ∈ T, c * v j) * (∏ j ∈ Tᶜ, (1 - c * v j)))
    - (Real.sqrt 2 + 1) ^ 2 *
      ((∏ j ∈ T, (1 - v j) ^ 2) * (∏ j ∈ Tᶜ, v j * (2 - v j))
      + (∏ j ∈ T, v j * (2 - v j)) * (∏ j ∈ Tᶜ, (1 - v j) ^ 2))
    + (2 + Real.sqrt 2) *
      ((∏ j ∈ T, (1 - c * v j) * (1 - v j)) *
          (∏ j ∈ Tᶜ, c * v j * Real.sqrt (2 * v j - v j ^ 2))
      + (∏ j ∈ T, c * v j * Real.sqrt (2 * v j - v j ^ 2)) *
          (∏ j ∈ Tᶜ, (1 - c * v j) * (1 - v j)))

def claim : Prop := ∀ n, 6 ≤ n → ∀ T : Finset (Fin n),
  (T.card = 1 ∨ T.card = 2) → ∀ v : Fin n → ℝ,
  (∀ i, 0 ≤ v i ∧ v i ≤ kappa) → 0 ≤ lambdaA n T v

/-- A block of complementary squared coordinates has an exponentially small gap. -/
private theorem product_gap {ι : Type*} (E : Finset ι)
    (u z : ι → ℝ) (hu : ∀ i ∈ E, 0 ≤ u i ∧ u i ≤ 1)
    (hz : ∀ i ∈ E, 0 ≤ z i ∧ z i ≤ 1 / 2)
    (huz : ∀ i ∈ E, u i + z i = 1) (hne : E.Nonempty) :
    (∏ i ∈ E, z i) ≤ (1 - ∏ i ∈ E, u i) * (1 / 2 : ℝ) ^ (E.card - 1) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp at hne
  | @insert i E hi ih =>
    by_cases he : E = ∅
    · subst E
      simpa using (le_of_eq (by linarith [huz i (by simp)] : z i = 1 - u i))
    · have hE : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
      have huc : ∀ j ∈ E, 0 ≤ u j ∧ u j ≤ 1 := fun j hj => hu j (mem_insert_of_mem hj)
      have hzc : ∀ j ∈ E, 0 ≤ z j ∧ z j ≤ 1 / 2 := fun j hj => hz j (mem_insert_of_mem hj)
      have hsum : ∀ j ∈ E, u j + z j = 1 := fun j hj => huz j (mem_insert_of_mem hj)
      have hprod0 : 0 ≤ ∏ j ∈ E, u j := prod_nonneg fun j hj => (huc j hj).1
      have hprod1 : (∏ j ∈ E, u j) ≤ 1 :=
        prod_le_one (fun j hj => (huc j hj).1) (fun j hj => (huc j hj).2)
      have hpower : (1 / 2 : ℝ) ^ E.card = (1 / 2 : ℝ) ^ (E.card - 1) * (1 / 2) := by
        conv_lhs =>
          rw [show E.card = (E.card - 1) + 1 by have := Finset.card_pos.mpr hE; omega,
            pow_succ]
      have hb := ih huc hzc hsum hE
      have hiu := hu i (mem_insert_self i E)
      have hiz := hz i (mem_insert_self i E)
      rw [prod_insert hi, prod_insert hi, card_insert_of_notMem hi, Nat.add_sub_cancel, hpower]
      have hp0 : 0 ≤ (1 / 2 : ℝ) ^ (E.card - 1) := by positivity
      calc z i * (∏ j ∈ E, z j)
          ≤ z i * ((1 - ∏ j ∈ E, u j) * (1 / 2 : ℝ) ^ (E.card - 1)) :=
            mul_le_mul_of_nonneg_left hb hiz.1
        _ ≤ (1 / 2) * ((1 - ∏ j ∈ E, u j) * (1 / 2 : ℝ) ^ (E.card - 1)) :=
          mul_le_mul_of_nonneg_right hiz.2 (mul_nonneg (by linarith) hp0)
        _ ≤ (1 - u i * ∏ j ∈ E, u j) * ((1 / 2 : ℝ) ^ (E.card - 1) * (1 / 2)) := by
          have hdiff : 0 ≤ (1 - u i) * (∏ j ∈ E, u j) := mul_nonneg (by linarith) hprod0
          nlinarith [mul_nonneg hdiff hp0]

private theorem block_bound {ι : Type*} (E : Finset ι) (x y b : ι → ℝ)
    (r : ℝ) (hr : 0 < r) (hr2 : r ^ 2 = 2)
    (hc : E.card = 1 ∨ E.card = 2)
    (hx : ∀ i ∈ E, 0 ≤ x i)
    (hy : ∀ i ∈ E, 0 ≤ y i ∧ y i ≤ r / 2)
    (hb : ∀ i ∈ E, 0 ≤ b i ∧ b i ≤ 1 / 2 ∧ (1 + r / 2) / 2 * y i ^ 2 ≤ b i)
    (hxy : ∀ i ∈ E, x i ^ 2 + y i ^ 2 = 1)
    (hbv : ∀ i ∈ E, b i = (1 + r / 2) * (1 - x i)) :
    0 ≤ 1 - (1 + r) ^ 2 * (∏ i ∈ E, y i) ^ 2 + r * (∏ i ∈ E, b i)
        + (2 + r) * (∏ i ∈ E, b i) * (∏ i ∈ E, y i) ∧
      (2 + r) * (∏ i ∈ E, b i) * (∏ i ∈ E, y i) ≤
        if E.card = 1 then (1 + r) / 2 else (2 + r) / 8 := by
  classical
  rcases hc with hc | hc
  · obtain ⟨i, rfl⟩ := card_eq_one.mp hc
    simp only [prod_singleton, card_singleton, ↓reduceIte]
    have hxi := hx i (by simp)
    obtain ⟨hyi, hyr⟩ := hy i (by simp)
    obtain ⟨hbi, hbhalf, hby⟩ := hb i (by simp)
    have hcircle := hxy i (by simp)
    have hbr := hbv i (by simp)
    constructor
    · set X := x i
      set Y := y i
      have hcircle : X ^ 2 + Y ^ 2 = 1 := hcircle
      have hid :
          4 * (1 + X) ^ 2 *
            (1 + (1 + r) * (1 - X) - (1 + r) ^ 2 * Y ^ 2
              + (1 + r) ^ 2 * (1 - X) * Y) =
          (1 + r) ^ 2 * (Y - (r - 1) * (1 + X)) ^ 2 *
            (Y ^ 2 + 2 * (1 + r) * Y * (1 + X) + (1 + X) ^ 2) := by
        linear_combination (-2 * r ^ 3 * X ^ 3 * Y - 6 * r ^ 3 * X ^ 2 * Y - 6 * r ^ 3 * X * Y -
          2 * r ^ 3 * Y - r ^ 2 * X ^ 4 - 2 * r ^ 2 * X ^ 3 * Y - 4 * r ^ 2 * X ^ 3 + 3 * r ^ 2
          * X ^ 2 * Y ^ 2 - 6 * r ^ 2 * X ^ 2 * Y - 6 * r ^ 2 * X ^ 2 + 6 * r ^ 2 * X * Y ^ 2 -
          6 * r ^ 2 * X * Y - 4 * r ^ 2 * X + 3 * r ^ 2 * Y ^ 2 - 2 * r ^ 2 * Y - r ^ 2 + 2 * r
          * X ^ 3 * Y + 8 * r * X ^ 2 * Y ^ 2 + 6 * r * X ^ 2 * Y + 16 * r * X * Y ^ 2 + 6 * r *
          X * Y + 8 * r * Y ^ 2 + 2 * r * Y - 2 * X ^ 3 * Y + 3 * X ^ 2 * Y ^ 2 + 2 * X ^ 2 * Y
          - 4 * X * Y ^ 3 + 6 * X * Y ^ 2 + 10 * X * Y - Y ^ 4 - 4 * Y ^ 3 + 3 * Y ^ 2 + 6 * Y)
          * hr2 + (-8 * r * X * Y - 4 * r * X - 2 * r * Y ^ 2 - 8 * r * Y - 4 * r - X ^ 2 - 12 *
          X * Y - 8 * X - 3 * Y ^ 2 - 12 * Y - 7) * hcircle
      have hpos : 0 ≤ (1 + r) ^ 2 * (Y - (r - 1) * (1 + X)) ^ 2 *
            (Y ^ 2 + 2 * (1 + r) * Y * (1 + X) + (1 + X) ^ 2) := by
        positivity
      have hscale : 0 < 4 * (1 + X) ^ 2 := by positivity
      have hf : 0 ≤ 1 + (1 + r) * (1 - X) - (1 + r) ^ 2 * Y ^ 2
              + (1 + r) ^ 2 * (1 - X) * Y :=
        (mul_nonneg_iff_of_pos_left hscale).mp (hid.symm ▸ hpos)
      have hb1 : r * b i = (1 + r) * (1 - X) := by
        rw [hbr]
        dsimp [X]
        linear_combination ((1 - x i) / 2) * hr2
      have hb2 : (2 + r) * b i = (1 + r) ^ 2 * (1 - X) := by
        rw [hbr]
        dsimp [X]
        linear_combination -((1 - x i) / 2) * hr2
      rw [hb1, hb2]
      linarith only [hf]
    · have hbyr : b i * y i ≤ (1 / 2) * (r / 2) :=
        mul_le_mul hbhalf hyr hyi (by positivity)
      have hp := mul_nonneg (show 0 ≤ 2 + r by linarith only [hr]) (sub_nonneg.mpr hbyr)
      nlinarith only [hp, hr2]
  · obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hc
    have hin : i ∉ ({j} : Finset ι) := by simpa
    simp only [prod_insert hin, prod_singleton, card_insert_of_notMem hin, card_singleton]
    simp only [show ¬(1 + 1 = (1 : ℕ)) by omega, ↓reduceIte]
    obtain ⟨hyi, hyr⟩ := hy i (by simp)
    obtain ⟨hyj, hyjr⟩ := hy j (by simp)
    obtain ⟨hbi, hbhalf, hby⟩ := hb i (by simp)
    obtain ⟨hbj, hbjhalf, hbjy⟩ := hb j (by simp)
    set B := b i * b j
    set Y := y i * y j
    have hB0 : 0 ≤ B := mul_nonneg hbi hbj
    have hY0 : 0 ≤ Y := mul_nonneg hyi hyj
    have hB1 : B ≤ 1 / 4 := by
      have h := mul_le_mul hbhalf hbjhalf hbj (by norm_num : (0 : ℝ) ≤ 1 / 2)
      nlinarith only [h]
    have hY1 : Y ≤ 1 / 2 := by
      have := mul_le_mul hyr hyjr hyj (by positivity : (0 : ℝ) ≤ r / 2)
      nlinarith only [this, hr2]
    have hBlow : (1 + r) ^ 2 / 8 * Y ^ 2 ≤ B := by
      have hcl : 0 ≤ (1 + r / 2) / 2 * y j ^ 2 := by positivity
      have h := mul_le_mul hby hbjy hcl hbi
      have hcoef : ((1 + r / 2) / 2) ^ 2 = (1 + r) ^ 2 / 8 := by
        nlinarith only [hr2]
      calc (1 + r) ^ 2 / 8 * Y ^ 2 =
          ((1 + r / 2) / 2 * y i ^ 2) * ((1 + r / 2) / 2 * y j ^ 2) := by
            rw [← hcoef]; dsimp [Y]; ring
        _ ≤ B := h
    constructor
    · let A : ℝ := 5 / 2 + 13 * r / 8
      let D : ℝ := 5 / 4 + 7 * r / 8
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hAD : 0 ≤ A - 3 / 4 * D := by dsimp [A, D]; linarith
      have hquad : 0 ≤ (1 / 2 - Y) * (Y + 1 / 4) := mul_nonneg (by linarith) (by linarith)
      have hbracket : 0 ≤ A * (Y + 1 / 2) - D * (Y ^ 2 + Y / 2 + 1 / 4) := by
        have := mul_nonneg hAD (show 0 ≤ Y + 1 / 2 by linarith)
        have h := mul_nonneg hD hquad
        nlinarith only [this, h]
      have hg : (34 - 19 * r) / 64 ≤ 1 - A * Y ^ 2 + D * Y ^ 3 := by
        have := mul_nonneg (show 0 ≤ 1 / 2 - Y by linarith) hbracket
        dsimp [A, D] at this ⊢
        nlinarith only [this]
      have hrbound : r < 3 / 2 := by nlinarith only [hr2, hr]
      have hgpos : 0 < (34 - 19 * r) / 64 := by linarith only [hrbound]
      have hf : 1 - A * Y ^ 2 + D * Y ^ 3 ≤
          1 - (1 + r) ^ 2 * Y ^ 2 + r * B + (2 + r) * B * Y := by
        have hp : 0 ≤ (r + (2 + r) * Y) * (B - (1 + r) ^ 2 / 8 * Y ^ 2) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr hBlow)
        have hid :
          (1 - (1 + r) ^ 2 * Y ^ 2 + r * B + (2 + r) * B * Y) -
            (1 - A * Y ^ 2 + D * Y ^ 3) =
            (r + (2 + r) * Y) * (B - (1 + r) ^ 2 / 8 * Y ^ 2) := by
          dsimp [A, D]
          linear_combination (Y ^ 2 * (Y * r + 4 * Y + r - 6)/8) * hr2
        linarith only [hp, hid]
      exact le_trans (le_of_lt (lt_of_lt_of_le hgpos hg)) hf
    · have := mul_le_mul hB1 hY1 hY0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have h := mul_nonneg (show 0 ≤ 2 + r by linarith only [hr]) (sub_nonneg.mpr this)
      nlinarith only [h]

theorem result : claim := by
  classical
  intro n hn T hT v hv
  let r : ℝ := Real.sqrt 2
  let c : ℝ := (1 + r) / r
  let x : Fin n → ℝ := fun i => 1 - v i
  let y : Fin n → ℝ := fun i => Real.sqrt (2 * v i - v i ^ 2)
  let a : Fin n → ℝ := fun i => 1 - c * v i
  let b : Fin n → ℝ := fun i => c * v i
  have hr : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : c = 1 + r / 2 := by
    apply (div_eq_iff (ne_of_gt hr)).mpr
    nlinarith only [hr2]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hk : kappa = 1 - r / 2 := by
    dsimp [kappa, r]
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt hr
    field_simp
    nlinarith only [hr2]
  have hck : c * (1 - r / 2) = 1 / 2 := by
    rw [hc]
    nlinarith only [hr2]
  have hv0 (i : Fin n) : 0 ≤ v i := (hv i).1
  have hvk (i : Fin n) : v i ≤ 1 - r / 2 := by simpa only [hk] using (hv i).2
  have hv1 (i : Fin n) : v i ≤ 1 := by linarith only [hvk i, hr]
  have hx0 (i : Fin n) : 0 ≤ x i := sub_nonneg.mpr (hv1 i)
  have hx1 (i : Fin n) : x i ≤ 1 := by dsimp [x]; linarith only [hv0 i]
  have hxr (i : Fin n) : r / 2 ≤ x i := by dsimp [x]; linarith only [hvk i]
  have hy0 (i : Fin n) : 0 ≤ y i := Real.sqrt_nonneg _
  have hysq (i : Fin n) : y i ^ 2 = v i * (2 - v i) := by
    have hrad : 0 ≤ 2 * v i - v i ^ 2 := by nlinarith only [hv0 i, hv1 i]
    have := Real.sq_sqrt hrad
    dsimp [y]
    nlinarith only [this]
  have hcircle (i : Fin n) : x i ^ 2 + y i ^ 2 = 1 := by rw [hysq]; dsimp [x]; ring
  have hyhalf (i : Fin n) : y i ^ 2 ≤ 1 / 2 := by
    have := mul_nonneg (sub_nonneg.mpr (hxr i)) (add_nonneg (hx0 i) (by positivity))
    nlinarith only [this, hr2, hcircle i]
  have hyr (i : Fin n) : y i ≤ r / 2 := by nlinarith only [hyhalf i, hr2, hr, hy0 i]
  have ha (i : Fin n) : x i ^ 2 ≤ a i := by
    have h := mul_nonneg (hv0 i) (sub_nonneg.mpr (hvk i))
    dsimp [x, a]
    rw [hc]
    nlinarith only [h]
  have ha0 (i : Fin n) : 0 ≤ a i := le_trans (sq_nonneg _) (ha i)
  have hb0 (i : Fin n) : 0 ≤ b i := mul_nonneg hc0 (hv0 i)
  have hbhalf (i : Fin n) : b i ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (hvk i) hc0
    dsimp [b]; nlinarith only [this, hck]
  have hby (i : Fin n) : (1 + r / 2) / 2 * y i ^ 2 ≤ b i := by
    rw [← hc, hysq]
    dsimp [b]
    nlinarith only [mul_nonneg hc0 (sq_nonneg (v i))]
  have hbv (i : Fin n) : b i = (1 + r / 2) * (1 - x i) := by dsimp [b, x]; rw [hc]; ring
  let A : Finset (Fin n) → ℝ := fun E => ∏ i ∈ E, a i
  let B : Finset (Fin n) → ℝ := fun E => ∏ i ∈ E, b i
  let X : Finset (Fin n) → ℝ := fun E => ∏ i ∈ E, x i
  let Y : Finset (Fin n) → ℝ := fun E => ∏ i ∈ E, y i
  let J := Tᶜ
  have hA0 (E : Finset (Fin n)) : 0 ≤ A E := prod_nonneg fun i _ => ha0 i
  have hB0 (E : Finset (Fin n)) : 0 ≤ B E := prod_nonneg fun i _ => hb0 i
  have hX0 (E : Finset (Fin n)) : 0 ≤ X E := prod_nonneg fun i _ => hx0 i
  have hX1 (E : Finset (Fin n)) : X E ≤ 1 := prod_le_one (fun i _ => hx0 i) (fun i _ => hx1 i)
  have hY0 (E : Finset (Fin n)) : 0 ≤ Y E := prod_nonneg fun i _ => hy0 i
  have hAX (E : Finset (Fin n)) : (X E) ^ 2 ≤ A E := by
    dsimp [X, A]
    rw [← prod_pow]
    exact prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => ha i)
  have hsq (E : Finset (Fin n)) : (Y E) ^ 2 = ∏ i ∈ E, v i * (2 - v i) := by
    dsimp [Y]; rw [← prod_pow]; exact prod_congr rfl fun i _ => hysq i
  have hx_sq (E : Finset (Fin n)) : (X E) ^ 2 = ∏ i ∈ E, (1 - v i) ^ 2 := by
    dsimp [X, x]; rw [prod_pow]
  let q := X J
  let K := (2 + r) * B T * Y T
  let w := (1 / 2 : ℝ) ^ (J.card - 1)
  have hq0 : 0 ≤ q := hX0 J
  have hq1 : q ≤ 1 := hX1 J
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [hq0, hq1]
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by linarith only [hr]) (hB0 T)) (hY0 T)
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hcard : T.card + J.card = n := by dsimp [J]; simp
  have hJ : J.Nonempty := by
    apply card_pos.mp
    rcases hT with hT | hT <;> omega
  have hgap : (Y J) ^ 2 ≤ (1 - q ^ 2) * w := by
    dsimp [Y, q, X, w]
    rw [← prod_pow, ← prod_pow]
    apply product_gap J (fun i => x i ^ 2) (fun i => y i ^ 2)
      (fun i _ => ⟨sq_nonneg _, by nlinarith only [hx0 i, hx1 i]⟩)
      (fun i _ => ⟨sq_nonneg _, hyhalf i⟩) (fun i _ => hcircle i) hJ
  have hblock := block_bound T x y b r hr hr2 hT
    (fun i _ => hx0 i) (fun i _ => ⟨hy0 i, hyr i⟩)
    (fun i _ => ⟨hb0 i, hbhalf i, hby i⟩) (fun i _ => hcircle i) (fun i _ => hbv i)
  change 0 ≤ 1 - (1 + r) ^ 2 * (Y T) ^ 2 + r * B T + K ∧
    K ≤ if T.card = 1 then (1 + r) / 2 else (2 + r) / 8 at hblock
  let C := 1 - K / 2 - (1 + r) ^ 2 * w
  let F := 1 - (1 + r) ^ 2 * (Y T) ^ 2 + r * B T + K
  have hF : 0 ≤ F := hblock.1
  have hC : 0 ≤ C := by
    have hrlt : r < 3 / 2 := by nlinarith only [hr2, hr]
    rcases hT with hT | hT
    · have hd : 4 ≤ J.card - 1 := by omega
      have hw : w ≤ 1 / 16 := by
        dsimp [w]
        calc (1 / 2 : ℝ) ^ (J.card - 1) ≤ (1 / 2 : ℝ) ^ 4 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
          _ = 1 / 16 := by norm_num
      have hK := hblock.2
      rw [if_pos hT] at hK
      have hww := mul_le_mul_of_nonneg_left hw (sq_nonneg (1 + r))
      dsimp [C]
      nlinarith only [hK, hww, hr2, hrlt]
    · have hd : 3 ≤ J.card - 1 := by omega
      have hw : w ≤ 1 / 8 := by
        dsimp [w]
        calc (1 / 2 : ℝ) ^ (J.card - 1) ≤ (1 / 2 : ℝ) ^ 3 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
          _ = 1 / 8 := by norm_num
      have hK := hblock.2
      rw [if_neg (by omega : ¬T.card = 1)] at hK
      have hww := mul_le_mul_of_nonneg_left hw (sq_nonneg (1 + r))
      dsimp [C]
      nlinarith only [hK, hww, hr2, hrlt]
  have hprod : lambdaA n T v =
      1 + A T * B T * A J * B J + r * (A T * B J + B T * A J)
        - (1 + r) ^ 2 * ((X T) ^ 2 * (Y J) ^ 2 + (Y T) ^ 2 * q ^ 2)
        + (2 + r) * (A T * X T * B J * Y J + B T * Y T * A J * q) := by
    have hfirst : c ^ n * (∏ i : Fin n, v i * (1 - c * v i)) =
        A T * B T * A J * B J := by
      have hp : c ^ n = ∏ _i : Fin n, c := by simp
      rw [hp, ← prod_mul_distrib]
      have hd : ∏ i : Fin n, c * (v i * (1 - c * v i)) =
          (∏ i ∈ T, a i * b i) * (∏ i ∈ J, a i * b i) := by
        dsimp only [J]
        rw [prod_mul_prod_compl]
        apply prod_congr rfl
        intro i _
        dsimp [a, b]; ring
      rw [hd, prod_mul_distrib (s := T) (f := a) (g := b),
        prod_mul_distrib (s := J) (f := a) (g := b)]
      dsimp only [A, B]
      ring
    dsimp only [lambdaA]
    change 1 + c ^ n * (∏ i : Fin n, v i * (1 - c * v i)) + _ - _ + _ = _
    rw [hfirst, ← hx_sq T, ← hx_sq J, ← hsq T, ← hsq J]
    dsimp [A, B, X, Y, J, q, a, b, x, y, r, c]
    simp only [prod_mul_distrib]
    ring
  have hlower :
      1 - (1 + r) ^ 2 * (X T) ^ 2 * (Y J) ^ 2
        + (r * B T - (1 + r) ^ 2 * (Y T) ^ 2) * q ^ 2 + K * q ^ 3 ≤ lambdaA n T v := by
    rw [hprod]
    have hAJ : q ^ 2 ≤ A J := hAX J
    have hAT0 := hA0 T
    have hAJ0 := hA0 J
    have hBT0 := hB0 T
    have hBJ0 := hB0 J
    have hXT0 := hX0 T
    have hYJ0 := hY0 J
    have hrem0 : 0 ≤ A T * B T * A J * B J + r * A T * B J
        + (2 + r) * A T * X T * B J * Y J := by positivity
    have hrem1 : 0 ≤ (r * B T + K * q) * (A J - q ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hAJ)
    dsimp [K] at *
    nlinarith only [hrem0, hrem1]
  have hcube : (3 * q ^ 2 - 1) / 2 ≤ q ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg (1 - q)) (show 0 ≤ 2 * q + 1 by linarith only [hq0])]
  have hXT : (X T) ^ 2 ≤ 1 := by nlinarith only [hX0 T, hX1 T]
  have hneg : (X T) ^ 2 * (Y J) ^ 2 ≤ (1 - q ^ 2) * w :=
    le_trans (mul_le_of_le_one_left (sq_nonneg _) hXT) hgap
  have hmain : C * (1 - q ^ 2) + F * q ^ 2 ≤ lambdaA n T v := by
    have h1 := mul_le_mul_of_nonneg_left hneg (sq_nonneg (1 + r))
    have h2 := mul_le_mul_of_nonneg_left hcube hK0
    dsimp [C, F]
    nlinarith only [hlower, h1, h2]
  exact le_trans (add_nonneg (mul_nonneg hC (by linarith only [hq2]))
    (mul_nonneg hF (sq_nonneg q))) hmain

#print axioms result

end D5.S3.QuantumBounds.MabkSelfTestingPositivity
