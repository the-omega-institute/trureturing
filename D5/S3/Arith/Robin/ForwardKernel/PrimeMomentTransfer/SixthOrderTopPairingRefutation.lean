/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.claim; result=D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.result; claim=D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.claim
   digest: A positive biased-cube mixture refutes sixth-order top pairing transfer. -/

/-
proof_shape: model_moments, lower_orders, top_order_bound, deviation_lower_bound, result: content.
proof_shape: model_character, model_positive, odd_card, ratio_limit: bind-only (consumers: model_moments, lower_orders, top_order_bound, deviation_lower_bound, result);
  shared mixture and parity declarations: bind-only (consumers: this module and FifthOrderTopOnlyRefutation).
escape_witness: The uniform top-order estimate keeps the sixth-order distinct defect at order N^2,
  while the four disjoint collision families force the full sixth moment above its fifteen-pairing
  comparison by a positive cubic-order amount.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FifthOrderTopOnlyRefutation
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticFourthExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectAlgebra
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PerfectPairingCount
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SixthOrderProductBounds
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SixthOrderPairingExpansion
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Ring.Nat

open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SixthOrderTopPairingRefutation

noncomputable section
set_option autoImplicit false

open D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FifthOrderTopOnlyRefutation

def claim : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∀ (D : ℕ → FifthData),
    (∀ n, (D n).ℓ 1 = 1) →
    (∀ n (y : (D n).A), 0 ≤ (D n).ℓ (y * y)) →
    (∀ n d, (D n).ℓ ((D n).Y d) = 0) →
    (∀ n d, (D n).Y d ^ 2 = (D n).a • (D n).Y d + (D n).b • 1) →
    (∀ n, (D n).L ≤ (D n).H) →
    (∀ n, 1 ≤ (D n).L) →
    (∀ n, |(D n).a| ≤ C * (D n).L) →
    (∀ n, |(D n).b| ≤ C * (D n).L) →
    (∀ n, (Fintype.card (D n).ι : ℝ) ≤ C * (D n).H) →
    (∀ n r, 2 ≤ r → r < 6 → ∀ (g : Fin r → (D n).ι → ℝ),
      (∀ i d, |g i d| ≤ 1) →
      |distinctIndexMoment (D n).ℓ (D n).Y g| ≤
        C * (Real.sqrt ((D n).H * (D n).L)) ^ r) →
    (∀ n (g : Fin 6 → (D n).ι → ℝ), (∀ i d, |g i d| ≤ 1) →
      |subsetDistinctMoment (D n).ℓ (D n).Y g Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetDistinctMoment (D n).ℓ (D n).Y g)| ≤
        C * (Real.sqrt ((D n).H * (D n).L)) ^ 6 / (D n).H) →
    Tendsto (fun n => (D n).L / (D n).H) atTop (𝓝 0) →
    Tendsto (fun n =>
      (subsetFamilyMoment (D n).ℓ (D n).Y (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (D n).ℓ (D n).Y (fun (_ : Fin 6) _ => (1 : ℝ)))) /
        (Real.sqrt ((D n).H * (D n).L)) ^ 6) atTop (𝓝 0)

private def zValue : Fin 3 → ℝ :=
  ![Real.sqrt (Real.sqrt 15), -Real.sqrt (Real.sqrt 15), 0]

private def zWeight : Fin 3 → ℝ :=
  ![1 / (2 * Real.sqrt 15), 1 / (2 * Real.sqrt 15), 1 - 1 / Real.sqrt 15]

private def moment (j : ℕ) : ℝ := ∑ z : Fin 3, zWeight z * zValue z ^ j

private def modelFunctional (N : ℕ) : ((Fin N → Bool) → ℝ) →ₗ[ℝ] ℝ :=
  mixtureFunctional N zValue zWeight

private lemma moment_values :
    moment 0 = 1 ∧ moment 1 = 0 ∧ moment 2 = 1 ∧
      moment 3 = 0 ∧ moment 4 = Real.sqrt 15 ∧ moment 5 = 0 ∧ moment 6 = 15 := by
  have hs : (Real.sqrt 15)^2 = (15 : ℝ) := by norm_num
  have hsp : 0 ≤ Real.sqrt 15 := by positivity
  have hc : (Real.sqrt (Real.sqrt 15))^2 = Real.sqrt 15 :=
    Real.sq_sqrt hsp
  norm_num [moment, zWeight, zValue, Fin.sum_univ_succ]
  all_goals field_simp [ne_of_gt (show (0 : ℝ) < Real.sqrt 15 by positivity)]
  all_goals ring_nf
  all_goals simp only [show (Real.sqrt (Real.sqrt 15)) ^ 4 =
      ((Real.sqrt (Real.sqrt 15)) ^ 2) ^ 2 by ring,
    show (Real.sqrt (Real.sqrt 15)) ^ 6 =
      ((Real.sqrt (Real.sqrt 15)) ^ 2) ^ 3 by ring, hc, hs]
  all_goals norm_num
  all_goals rw [show (Real.sqrt 15)^3 = (Real.sqrt 15)^2 * Real.sqrt 15 by ring, hs]
  all_goals ring

private lemma model_character (N : ℕ) (T : Finset (Fin N)) :
    modelFunctional N (∏ d ∈ T, modelY N d) =
      moment T.card / Real.sqrt N ^ T.card := by
  simpa only [modelFunctional, moment] using
    (mixture_character N zValue zWeight T)

private lemma model_positive (N : ℕ) (hN : 4 ≤ N) (F : (Fin N → Bool) → ℝ) :
    0 ≤ modelFunctional N (F * F) := by
  apply mixture_positive N zValue zWeight
  · intro z
    have hc : |Real.sqrt (Real.sqrt 15)| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]
      have hs4 : (Real.sqrt 15 : ℝ) ≤ 4 := by
        nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
      nlinarith [show (Real.sqrt (Real.sqrt 15))^2 = Real.sqrt 15 by
        exact Real.sq_sqrt (by positivity)]
    have hz : |zValue z| ≤ 2 := by fin_cases z <;> simp [zValue, hc]
    have hs : (2 : ℝ) ≤ Real.sqrt N := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).2
      exact_mod_cast hN
    exact hz.trans hs
  · intro z
    fin_cases z
    · norm_num [zWeight]
    · norm_num [zWeight]
    · have hs1 : (1 : ℝ) ≤ Real.sqrt 15 := by
        have hsp : (0 : ℝ) ≤ Real.sqrt 15 := by positivity
        nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num,
          hsp, sq_nonneg (Real.sqrt 15 - 1)]
      have hp : 0 < Real.sqrt 15 := by positivity
      have hi : 1 / Real.sqrt 15 ≤ (1 : ℝ) := (div_le_one₀ hp).2 hs1
      dsimp [zWeight]
      linarith
  · exact_mod_cast (show 0 < N by omega)

private lemma distinct_moments (N r : ℕ) (g : Fin r → Fin N → ℝ) :
    distinctIndexMoment (modelFunctional N) (modelY N) g =
      (moment r / Real.sqrt N ^ r) *
        ∑ x : Fin r → Fin N with Function.Injective x, ∏ i, g i (x i) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hinj := (Finset.mem_filter.mp hx).2
  have hodd : oddCoords x = Finset.univ.image x := by
    ext d
    by_cases hd : d ∈ Finset.univ.image x
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      have hf : Finset.univ.filter (fun j => x j = x i) = {i} := by
        ext j
        simp [hinj.eq_iff]
      simp [oddCoords, hf]
    · have hf : Finset.univ.filter (fun j => x j = d) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi he
        exact hd (Finset.mem_image.mpr ⟨i, hi, he⟩)
      simp [oddCoords, hf, hd]
  rw [odd_reduction x, model_character, hodd]
  simp only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  exact mul_comm _ _

private lemma distinct_bound (N r : ℕ) (hN : 0 < N) (hr : 2 ≤ r) (hr6 : r < 6)
    (g : Fin r → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |distinctIndexMoment (modelFunctional N) (modelY N) g| ≤
      4 * Real.sqrt N ^ r := by
  classical
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hm : |moment r| ≤ 4 := by
    interval_cases r <;> norm_num [moment_values.2.2.1, moment_values.2.2.2.1,
      moment_values.2.2.2.2.1, moment_values.2.2.2.2.2.1]
    · rw [abs_of_nonneg (by positivity)]
      nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
  have hsum : |∑ x : Fin r → Fin N with Function.Injective x, ∏ i, g i (x i)| ≤
      (N : ℝ)^r := by
    calc
      _ ≤ ∑ x : Fin r → Fin N with Function.Injective x, |∏ i, g i (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin r → Fin N with Function.Injective x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hg i (x i))
      _ ≤ ∑ _x : Fin r → Fin N, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = _ := by simp
  rw [distinct_moments, abs_mul, abs_div, abs_of_pos (pow_pos hs r)]
  calc
    _ ≤ (4 / Real.sqrt N ^ r) * (N : ℝ)^r :=
      mul_le_mul (div_le_div_of_nonneg_right hm (by positivity)) hsum
        (abs_nonneg _) (by positivity)
    _ = 4 * Real.sqrt N ^ r := by
      have he : (N : ℝ)^r = Real.sqrt N ^ r * Real.sqrt N ^ r := by
        rw [← mul_pow, ← pow_two, Real.sq_sqrt (by positivity)]
      rw [he]
      field_simp


private lemma subsetDistinct_univ {N : ℕ} (ℓ : ((Fin N → Bool) → ℝ) →ₗ[ℝ] ℝ)
    (Y : Fin N → (Fin N → Bool) → ℝ) (g : Fin 6 → Fin N → ℝ) :
    subsetDistinctMoment ℓ Y g (Finset.univ : Finset (Fin 6)) =
      distinctIndexMoment ℓ Y g := by
  classical
  let e : (Finset.univ : Finset (Fin 6)) ≃ Fin 6 :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [subsetDistinctMoment, ← retained_assignment_reindex ℓ Y Finset.univ g]
  convert assignment_moment_reindex ℓ Y e (fun i => g i.val) using 1
  unfold distinctIndexMoment
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

private lemma subset_unit_moment {k : ℕ} (N : ℕ) (U : Finset (Fin k)) :
    subsetDistinctMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U =
      (moment U.card / Real.sqrt N ^ U.card) * (N.descFactorial U.card : ℝ) := by
  classical
  have hc : (Finset.univ.filter (Function.Injective : (Fin (Fintype.card U) → Fin N) → Prop)).card =
      N.descFactorial (Fintype.card U) := by
    let e : {x : Fin (Fintype.card U) → Fin N // Function.Injective x} ≃ (Fin (Fintype.card U) ↪ Fin N) :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x, x.injective⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have he := Fintype.card_congr e
    rw [Fintype.card_embedding_eq] at he
    simpa only [Fintype.card_subtype, Fintype.card_fin] using he
  have hR : subsetDistinctMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U =
      distinctIndexMoment (modelFunctional N) (modelY N)
        (fun (_ : Fin (Fintype.card U)) (_ : Fin N) => (1 : ℝ)) := by
    unfold subsetDistinctMoment distinctIndexMoment
    simp only [Fintype.card_coe]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  rw [hR, distinct_moments]
  simp only [Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one, hc, Fintype.card_coe]

private lemma distinct_pair_formula (N : ℕ) (f h : Fin N → ℝ) :
    distinctIndexMoment (modelFunctional N) (modelY N) ![f, h] =
      (1 / (N : ℝ)) *
        ((∑ d, f d) * (∑ d, h d) - ∑ d, f d * h d) := by
  classical
  have hsum :
      (∑ x : Fin 2 → Fin N with Function.Injective x, ∏ i, ![f, h] i (x i)) =
        ∑ d, ∑ e with d ≠ e, f d * h e := by
    simpa [Fin.prod_univ_two] using (sum_two (fun d e => f d * h e))
  have hsplit (d : Fin N) :
      (∑ e : Fin N with d ≠ e, f d * h e) + f d * h d =
        ∑ e : Fin N, f d * h e := by
    have ht := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin N)) (fun e => d ≠ e) (fun e => f d * h e)
    have hd : Finset.univ.filter (fun e : Fin N => ¬d ≠ e) = {d} := by
      ext e
      simp [eq_comm]
    rw [hd, Finset.sum_singleton] at ht
    exact ht
  have htotal : (∑ d, ∑ e with d ≠ e, f d * h e) + (∑ d, f d * h d) =
      (∑ d, f d) * (∑ e, h e) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hsplit, ← Finset.mul_sum]
    rw [Finset.sum_mul]
  rw [distinct_moments, hsum, moment_values.2.2.1]
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)]
  congr 1
  linarith

private lemma subset_pair_formula (N : ℕ) (g : Fin 6 → Fin N → ℝ)
    (e : Finset (Fin 6)) (he : e.card = 2) :
    subsetDistinctMoment (modelFunctional N) (modelY N) g e =
      (1 / (N : ℝ)) *
        ((∏ i ∈ e, ∑ d, g i d) - ∑ d, ∏ i ∈ e, g i d) := by
  classical
  let v : e ≃ Fin 2 := Fintype.equivOfCardEq (by simpa using he)
  let q : Fin 2 → Fin N → ℝ := fun j => g (v.symm j).val
  have hR : subsetDistinctMoment (modelFunctional N) (modelY N) g e =
      distinctIndexMoment (modelFunctional N) (modelY N) q := by
    unfold subsetDistinctMoment
    rw [← retained_assignment_reindex (modelFunctional N) (modelY N) e g]
    convert assignment_moment_reindex (modelFunctional N) (modelY N) v
      (fun i => g i.val) using 1
    unfold distinctIndexMoment
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  rw [hR]
  have hq : q = ![q 0, q 1] := by funext j; fin_cases j <;> rfl
  rw [hq, distinct_pair_formula]
  have hp : (∏ i ∈ e, ∑ d, g i d) =
      (∑ d, q 0 d) * (∑ d, q 1 d) := by
    simp only [q]
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, ∑ d, g i.val d) =
        ∏ j : Fin 2, ∑ d, q j d := by
      apply Fintype.prod_equiv v
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ, Fin.prod_univ_two] using hprod
  have ht : (∑ d, ∏ i ∈ e, g i d) = ∑ d, q 0 d * q 1 d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, g i.val d) = ∏ j : Fin 2, q j d := by
      apply Fintype.prod_equiv v
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ, Fin.prod_univ_two] using hprod
  rw [← hp, ← ht]


private lemma top_order_bound (N : ℕ) (hN : 6 ≤ N)
    (g : Fin 6 → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |subsetDistinctMoment (modelFunctional N) (modelY N) g Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetDistinctMoment (modelFunctional N) (modelY N) g)| ≤
      720 * (N : ℝ)^2 := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hNs2 : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hNs6 : (Real.sqrt N)^6 = (N : ℝ)^3 := by
    calc
      _ = ((Real.sqrt N)^2)^3 := by ring
      _ = _ := by rw [hNs2]
  let A : Fin 6 → ℝ := fun i => ∑ d, g i d
  let a : Finset (Fin 6) → ℝ := fun e => (1 / (N : ℝ)) * ∏ i ∈ e, A i
  let R : Finset (Fin 6) → ℝ := subsetDistinctMoment (modelFunctional N) (modelY N) g
  have hA (i : Fin 6) : |A i| ≤ N := by
    calc
      _ ≤ ∑ d : Fin N, |g i d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun d _ => hg i d)
      _ = _ := by simp
  have ha (e : Finset (Fin 6)) (he : e.card = 2) : |a e| ≤ N := by
    dsimp only [a]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ)), Finset.abs_prod]
    calc
      _ ≤ (1 / (N : ℝ)) * ∏ _i ∈ e, (N : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA i)
      _ = _ := by simp only [Finset.prod_const, he]; field_simp [ne_of_gt hNp]
  have ht (e : Finset (Fin 6)) :
      |(1 / (N : ℝ)) * ∑ d, ∏ i ∈ e, g i d| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
    calc
      _ ≤ (1 / (N : ℝ)) * ∑ d : Fin N, |∏ i ∈ e, g i d| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (1 / (N : ℝ)) * ∑ _d : Fin N, (1 : ℝ) := by
        gcongr with d
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => hg i d)
      _ = _ := by simp [ne_of_gt hNp]
  have hRa (e : Finset (Fin 6)) (he : e.card = 2) : |R e - a e| ≤ 1 := by
    have heq : R e - a e = -(1 / (N : ℝ) * ∑ d, ∏ i ∈ e, g i d) := by
      dsimp only [R, a, A]
      rw [subset_pair_formula N g e he]
      ring
    rw [heq, abs_neg]
    exact ht e
  have hR (e : Finset (Fin 6)) (he : e.card = 2) : |R e| ≤ 2 * N := by
    calc
      _ = |R e - a e + a e| := by congr 1; ring
      _ ≤ |R e - a e| + |a e| := abs_add_le _ _
      _ ≤ 1 + N := add_le_add (hRa e he) (ha e he)
      _ ≤ _ := by linarith
  have hcount : ((Finset.univ : Finset (Finset (Finset (Fin 6)))).filter
      (IsPerfectPairing Finset.univ)).card = 15 := by
    rw [perfectPairingCount]
    norm_num [Nat.doubleFactorial]
  have hpoly : |finitePairingPolynomial Finset.univ R -
      finitePairingPolynomial Finset.univ a| ≤ 180 * (N : ℝ)^2 := by
    unfold finitePairingPolynomial
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ P : Finset (Finset (Fin 6)) with IsPerfectPairing Finset.univ P,
          |(∏ e ∈ P, R e) - ∏ e ∈ P, a e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _P : Finset (Finset (Fin 6)) with IsPerfectPairing Finset.univ _P,
          12 * (N : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro P hP
        have hp := (Finset.mem_filter.mp hP).2
        have hc := hp.card
        have hpc : P.card = 3 := by simp only [Finset.card_univ, Fintype.card_fin] at hc; omega
        have hb := scalar_prod_diff_bound P hpc R a (2 * N) (by positivity)
          (fun e he => hR e (hp.1.1 e he))
          (fun e he => (ha e (hp.1.1 e he)).trans (by linarith))
          (fun e he => hRa e (hp.1.1 e he))
        nlinarith [hb]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcount]; norm_num; ring
  have harank (e : Finset (Fin 6)) (he : e.card = 2) :
      a e = ∏ i ∈ e, A i / Real.sqrt N := by
    dsimp only [a]
    rw [Finset.prod_div_distrib, Finset.prod_const, he, hNs2]
    ring
  have hleading : finitePairingPolynomial Finset.univ a =
      (15 / Real.sqrt N ^ 6) * ∏ i, A i := by
    rw [finitePairingPolynomial_rankOne _ a (fun i => A i / Real.sqrt N) harank,
      hcount, Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
    ring
  have htop : |R Finset.univ - (15 / Real.sqrt N ^ 6) * ∏ i, A i| ≤
      540 * (N : ℝ)^2 := by
    have hi := inj_sum_product_bound N hN g hg
    have heq : R Finset.univ - (15 / Real.sqrt N ^ 6) * ∏ i, A i =
        (15 / Real.sqrt N ^ 6) *
          ((∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) -
            ∏ i, ∑ d, g i d) := by
      dsimp only [R, A]
      rw [subsetDistinct_univ, distinct_moments, moment_values.2.2.2.2.2.2]
      ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 15 / Real.sqrt N ^ 6)]
    calc
      _ ≤ (15 / Real.sqrt N ^ 6) * (36 * (N : ℝ)^5) := by
        exact mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by rw [hNs6]; field_simp [ne_of_gt hNp]; ring
  change |R Finset.univ - finitePairingPolynomial Finset.univ R| ≤ _
  rw [← hleading] at htop
  have heq : R Finset.univ - finitePairingPolynomial Finset.univ R =
      (R Finset.univ - finitePairingPolynomial Finset.univ a) -
        (finitePairingPolynomial Finset.univ R - finitePairingPolynomial Finset.univ a) := by ring
  rw [heq]
  calc
    _ ≤ |R Finset.univ - finitePairingPolynomial Finset.univ a| +
        |finitePairingPolynomial Finset.univ R - finitePairingPolynomial Finset.univ a| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (R Finset.univ - finitePairingPolynomial Finset.univ a) 0
          (finitePairingPolynomial Finset.univ R - finitePairingPolynomial Finset.univ a)
    _ ≤ _ := by linarith [htop, hpoly]

-- DEVIATION

private lemma model_unit_transfer (N : ℕ) (hN : 4 ≤ N) :
    ∃ E : ℝ,
      subsetFamilyMoment (modelFunctional N) (modelY N)
          (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (modelFunctional N) (modelY N)
            (fun (_ : Fin 6) _ => (1 : ℝ))) =
        subsetPairingDefect (modelFunctional N) (modelY N)
            (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ +
          (N : ℝ) * ∑ e ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
            subsetPairingDefect (modelFunctional N) (modelY N)
              (fun (_ : Fin 6) _ => (1 : ℝ)) (Finset.univ \ e) + E ∧
      |E| ≤ pairingDefectConstant 6 4 * Real.sqrt N ^ 6 *
        (Real.sqrt (1 / (N : ℝ)) + 1 / N) := by
  classical
  have hunit : modelFunctional N 1 = 1 := by
    simpa only [Finset.prod_empty, Finset.card_empty, pow_zero, div_one, moment_values.1]
      using model_character N ∅
  have hcenter : ∀ d, modelFunctional N (modelY N d) = 0 := by
    intro d
    simpa only [Finset.prod_singleton, Finset.card_singleton, pow_one,
      moment_values.2.1, zero_div] using model_character N {d}
  have hquad : ∀ d, modelY N d ^ 2 = (0 : ℝ) • modelY N d + (1 : ℝ) • 1 := by
    intro d
    funext ω
    change sign (ω d)^2 = 0 * sign (ω d) + 1 * 1
    cases ω d <;> norm_num [sign]
  have hR : DisjointLabelMomentBound (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) _ => (1 : ℝ)) 4 (Real.sqrt ((N : ℝ) * 1)) := by
    intro r hr hr6 labels _ _
    simp only [Finset.prod_const_one, mul_one]
    have hb := distinct_bound N r (by omega) hr hr6 (fun _ _ => 1) (by simp)
    convert hb using 1
    congr 1
    unfold distinctIndexMoment
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  obtain ⟨E, _, hE, hb⟩ := quadratic_pairing_defect_transfer
    (modelFunctional N) (modelY N) (fun (_ : Fin 6) _ => (1 : ℝ))
    0 1 4 N 1 (by norm_num) (by exact_mod_cast (show 1 ≤ N by omega))
    (by norm_num) (by norm_num) (by norm_num) hquad hunit hcenter
    (by
      simp only [Fintype.card_fin]
      have hn : (0 : ℝ) ≤ N := by positivity
      linarith) (by simp) hR
  have hcollapse := partialPairing_six_convolution (Finset.univ : Finset (Fin 6))
    (by simp) (N : ℝ)
    (subsetPairingDefect (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) _ => (1 : ℝ)))
    (fun V _ hV => subset_pairing_defect_small (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) _ => (1 : ℝ)) hunit hcenter V hV)
  simp only [subsetWeightSum, indexSum, Finset.prod_const, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at hE
  rw [hcollapse] at hE
  refine ⟨E, ?_, ?_⟩
  · simpa only [subsetFamilyMoment, quadraticFamilyMoment] using hE
  · simpa only [mul_one] using hb

private lemma model_unit_pair {k : ℕ} (N : ℕ) (hN : 4 ≤ N)
    (e : Finset (Fin k)) (he : e.card = 2) :
    subsetDistinctMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) e = (N : ℝ) - 1 := by
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hc : (N.descFactorial 2 : ℝ) = (N : ℝ) * (N - 1) := by
    norm_num [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  rw [subset_unit_moment, he, moment_values.2.2.1,
    Real.sq_sqrt (by positivity), hc]
  field_simp [hNz]

private lemma model_four_defect_lower (N : ℕ) (hN : 100 ≤ N)
    (U : Finset (Fin 6)) (hU : U.card = 4) :
    (N : ℝ) ^ 2 / 2 ≤ subsetPairingDefect (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ)) U := by
  classical
  have hpoly : finitePairingPolynomial U
      (subsetDistinctMoment (modelFunctional N) (modelY N)
        (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ))) = 3 * ((N : ℝ) - 1)^2 := by
    rw [finitePairingPolynomial_const U _ ((N : ℝ) - 1)
      (fun e he => model_unit_pair N (by omega) e he), perfectPairingCount U]
    norm_num [hU, Nat.doubleFactorial]
  have hc : (N.descFactorial 4 : ℝ) =
      (N : ℝ) * (N - 1) * (N - 2) * (N - 3) := by
    norm_num [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ N),
      Nat.cast_sub (by omega : 2 ≤ N), Nat.cast_sub (by omega : 3 ≤ N)]
    ring
  have hs : Real.sqrt N ^ 4 = (N : ℝ)^2 := by
    calc
      _ = (Real.sqrt N ^ 2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  rw [subsetPairingDefect, hpoly, subset_unit_moment N U, hU,
    moment_values.2.2.2.2.1, hs, hc]
  convert sixth_four_defect_lower (N : ℝ) (by exact_mod_cast hN) using 1 <;> ring

private lemma deviation_lower_bound (N : ℕ) (hN : 1000 ≤ N)
    (hK : pairingDefectConstant 6 4 ≤ Real.sqrt N) :
    Real.sqrt N ^ 6 ≤
      subsetFamilyMoment (modelFunctional N) (modelY N)
          (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (modelFunctional N) (modelY N)
            (fun (_ : Fin 6) _ => (1 : ℝ))) := by
  classical
  obtain ⟨E, hid, hEb⟩ := model_unit_transfer N (by omega)
  have hs : Real.sqrt N ^ 6 = (N : ℝ)^3 := by
    calc
      _ = (Real.sqrt N ^ 2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have hEs : |E| ≤ 2 * (N : ℝ)^3 := by
    rw [hs] at hEb
    exact hEb.trans (transfer_error_small N (pairingDefectConstant 6 4)
      (by exact_mod_cast (show 1 ≤ N by omega)) hK)
  let Δ := subsetPairingDefect (modelFunctional N) (modelY N)
    (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ))
  let S := ∑ e ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, Δ (Finset.univ \ e)
  have hsum : 15 * (N : ℝ)^2 / 2 ≤ S := by
    calc
      _ = ∑ _e ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, (N : ℝ)^2 / 2 := by
        norm_num [Finset.card_powersetCard, Nat.choose] <;> ring
      _ ≤ S := by
        apply Finset.sum_le_sum
        intro e he
        apply model_four_defect_lower N (by omega)
        have he' := Finset.mem_powersetCard.mp he
        rw [Finset.card_sdiff_of_subset he'.1]
        simp [he'.2]
  have h6 : |Δ Finset.univ| ≤ 720 * (N : ℝ)^2 := by
    simpa only [Δ, subsetPairingDefect] using
      top_order_bound N (by omega) (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ)) (by simp)
  have hv := sixth_defect_lower (N : ℝ) 720 (Δ Finset.univ) (S / 15) E
    (subsetFamilyMoment (modelFunctional N) (modelY N)
        (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
      finitePairingPolynomial Finset.univ
        (subsetFamilyMoment (modelFunctional N) (modelY N)
          (fun (_ : Fin 6) _ => (1 : ℝ))))
    (by exact_mod_cast (show 1 ≤ N by omega))
    (by exact_mod_cast (show 720 ≤ N by omega)) h6
    (by apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 15)).2; nlinarith)
    hEs (by dsimp only [Δ, S] at *; linarith [hid])
  simpa only [hs] using hv

private def sixthCounterData (offset n : ℕ) : FifthData where
  ι := Fin (n + offset)
  A := (Fin (n + offset) → Bool) → ℝ
  ℓ := modelFunctional (n + offset)
  Y := modelY (n + offset)
  a := 0
  b := 1
  H := ((n + offset : ℕ) : ℝ)
  L := 1

private lemma sixth_ratio_limit (offset : ℕ) :
    Tendsto (fun n : ℕ => (sixthCounterData offset n).L /
      (sixthCounterData offset n).H) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n + offset : ℕ) : ℝ)) atTop (𝓝 0)
  simp only [Nat.cast_add, one_div]
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (offset : ℝ) tendsto_natCast_atTop_atTop)


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SixthOrderTopPairingRefutation
