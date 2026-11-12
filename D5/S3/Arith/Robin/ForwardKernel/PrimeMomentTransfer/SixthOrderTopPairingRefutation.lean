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
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectAlgebra
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
  all_goals nlinarith [show (Real.sqrt 15)^3 = 15 * Real.sqrt 15 by
    rw [show (Real.sqrt 15)^3 = (Real.sqrt 15)^2 * Real.sqrt 15 by ring, hs]]

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
  unfold subsetDistinctMoment
  congr 1
  funext j
  apply congrArg g
  apply Subtype.ext
  simp

private lemma distinct_pair_formula (N : ℕ) (f h : Fin N → ℝ) :
    distinctIndexMoment (modelFunctional N) (modelY N) ![f, h] =
      (1 / (N : ℝ)) *
        ((∑ d, f d) * (∑ d, h d) - ∑ d, f d * h d) := by
  classical
  have hsum :
      (∑ x : Fin 2 → Fin N with Function.Injective x, ∏ i, ![f, h] i (x i)) =
        ∑ d, ∑ e with d ≠ e, f d * h e := by
    simpa [Finset.prod_univ_two] using
      (sum_two (fun d e => f d * h e))
  rw [distinct_moments, hsum]
  simp only [moment_values.2.2.1, Real.sq_sqrt (by positivity)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N))
    (fun e => e ≠ _)]
  simp only [Finset.sum_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

private lemma subset_pair_formula (N : ℕ) (g : Fin 6 → Fin N → ℝ)
    (e : Finset (Fin 6)) (he : e.card = 2) :
    subsetDistinctMoment (modelFunctional N) (modelY N) g e =
      (1 / (N : ℝ)) *
        ((∏ i ∈ e, ∑ d, g i d) - ∑ d, ∏ i ∈ e, g i d) := by
  classical
  let q : Fin 2 → Fin N → ℝ := fun j => g ((Fintype.equivFin e).symm j).val
  have hR : subsetDistinctMoment (modelFunctional N) (modelY N) g e =
      distinctIndexMoment (modelFunctional N) (modelY N) q := by
    unfold subsetDistinctMoment
    congr 1
    funext j
    rfl
  rw [hR]
  have hq : q = ![q 0, q 1] := by funext j; fin_cases j <;> rfl
  rw [hq, distinct_pair_formula]
  have hp : (∏ i ∈ e, ∑ d, g i d) =
      (∑ d, q 0 d) * (∑ d, q 1 d) := by
    simp only [q]
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, ∑ d, g i i.val d) =
        (∑ d, q 0 d) * (∑ d, q 1 d) := by
      rw [← Fin.prod_univ_two]
      apply Fintype.prod_equiv (Fintype.equivFin e)
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ] using hprod
  have ht : (∑ d, ∏ i ∈ e, g i d) = ∑ d, q 0 d * q 1 d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, g i.val d) = q 0 d * q 1 d := by
      rw [← Fin.prod_univ_two]
      apply Fintype.prod_equiv (Fintype.equivFin e)
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ] using hprod
  rw [← hp, ← ht]

private lemma injective_count (N : ℕ) :
    Fintype.card {x : Fin 6 → Fin N // Function.Injective x} = N.descFactorial 6 := by
  let e : {x : Fin 6 → Fin N // Function.Injective x} ≃ (Fin 6 ↪ Fin N) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x, x.injective⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq]
  rfl

private lemma inj_sum_product_bound (N : ℕ) (hN : 1 ≤ N)
    (g : Fin 6 → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |(∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) -
        ∏ i, ∑ d, g i d| ≤ 36 * (N : ℝ)^5 := by
  classical
  let all : Finset (Fin 6 → Fin N) := Finset.univ
  let good : Finset (Fin 6 → Fin N) := all.filter Function.Injective
  let bad : Finset (Fin 6 → Fin N) := all.filter (fun x => ¬Function.Injective x)
  have hsplit :
      (∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) +
        ∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i) =
        ∑ x : Fin 6 → Fin N, ∏ i, g i (x i) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ Function.Injective]
  have hall : (∑ x : Fin 6 → Fin N, ∏ i, g i (x i)) = ∏ i, ∑ d, g i d := by
    rw [← Fintype.prod_sum]
  have hcardbad : (bad.card : ℝ) ≤ 36 * (N : ℝ)^5 := by
    have hcardgood : good.card = N.descFactorial 6 := by
      simpa only [good, all, Fintype.card_subtype] using injective_count N
    have hcardall : all.card = N ^ 6 := by simp [all, Fintype.card_fun]
    have hdisj : Disjoint good bad := by
      apply Finset.disjoint_left.mpr
      intro x hxg hxb
      exact (Finset.mem_filter.mp hxb).2 (Finset.mem_filter.mp hxg).2
    have hunion : good ∪ bad = all := by
      ext x
      simp only [good, bad, all, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      tauto
    have hc : good.card + bad.card = all.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [hcardall, hcardgood] at hc
    have hcastNat : bad.card = N ^ 6 - N.descFactorial 6 := by omega
    have hcast : (bad.card : ℝ) = (N : ℝ)^6 - (N.descFactorial 6 : ℝ) := by
      exact_mod_cast hcastNat
    rw [hcast]
    norm_num [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ N),
      Nat.cast_sub (by omega : 2 ≤ N), Nat.cast_sub (by omega : 3 ≤ N),
      Nat.cast_sub (by omega : 4 ≤ N), Nat.cast_sub (by omega : 5 ≤ N)] at *
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpow : (0 : ℝ) ≤ (N : ℝ)^5 := by positivity
    nlinarith [hN', hpow]
  have hbad :
      |∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i)| ≤
        36 * (N : ℝ)^5 := by
    calc
      _ ≤ ∑ x : Fin 6 → Fin N with ¬Function.Injective x, |∏ i, g i (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : Fin 6 → Fin N with ¬Function.Injective x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hg i (x i))
      _ = (bad.card : ℝ) := by simp [bad, all]
      _ ≤ _ := hcardbad
  rw [← hall, ← hsplit]
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SixthOrderTopPairingRefutation
