/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.claim; result=D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.result; claim=D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FifthOrderTopOnlyRefutation.claim
   digest: A positive mixture of biased Boolean cubes refutes fifth-order top-only moment transfer. -/


/-
proof_shape: odd_reduction, distinct_moments, distinct_bound, collision_count_lower,
  model_fifth, normalized_fifth, result: content.
proof_shape: walsh_factor: bind-only (consumer: model_character);
  moment_values: bind-only (consumers: distinct_bound, distinct_fifth_zero, model_fifth, result);
  model_character: bind-only (consumers: distinct_moments, model_fifth, result);
  model_positive: bind-only (consumer: result);
  odd_card: bind-only (consumer: model_fifth);
  distinct_fifth_zero: bind-only (consumer: result);
  odd_duplicate: bind-only (consumer: collision_count_lower);
  ratio_limit: bind-only (consumer: result).
escape_witness: odd_reduction reduces arbitrary repeated sign products to their odd-coordinate
  character. The injection in collision_count_lower gives at least N(N-1)(N-2)(N-3) fifth-order
  tuples with three odd coordinates, and at least N^4/4 for N >= 9. Together with model_fifth
  this yields the normalized upper bound -3/11, used by result.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticMomentDefs
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Ring.Nat

/-! A positive finite probability model for the obstruction in 命题 500.4. -/

open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FifthOrderTopOnlyRefutation

noncomputable section
set_option autoImplicit false

/-- One finite algebraic moment model, with all types in universe zero. -/
structure FifthData where
  ι : Type
  [fintype : Fintype ι]
  [decidableEq : DecidableEq ι]
  A : Type
  [commRing : CommRing A]
  [algebra : Algebra ℝ A]
  ℓ : A →ₗ[ℝ] ℝ
  Y : ι → A
  a : ℝ
  b : ℝ
  H : ℝ
  L : ℝ

attribute [instance] FifthData.fintype FifthData.decidableEq FifthData.commRing FifthData.algebra

/-- The fifth-order implication with bounded lower moments and vanishing top moment. -/
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
    (∀ n r, 2 ≤ r → r < 5 → ∀ (g : Fin r → (D n).ι → ℝ),
      (∀ i d, |g i d| ≤ 1) →
      |distinctIndexMoment (D n).ℓ (D n).Y g| ≤ C * (Real.sqrt ((D n).H * (D n).L)) ^ r) →
    (∀ n (g : Fin 5 → (D n).ι → ℝ), (∀ i d, |g i d| ≤ 1) →
      distinctIndexMoment (D n).ℓ (D n).Y g = 0) →
    Tendsto (fun n => (D n).L / (D n).H) atTop (𝓝 0) →
    Tendsto (fun n => quadraticFamilyMoment (D n).ℓ (D n).Y
      (fun (_ : Fin 5) _ => (1 : ℝ)) /
        (Real.sqrt ((D n).H * (D n).L)) ^ 5) atTop (𝓝 0)


private def sign (b : Bool) : ℝ := if b then 1 else -1

private lemma walsh_factor (N : ℕ) (T : Finset (Fin N)) (μ : ℝ) :
    (∑ ω : Fin N → Bool, (∏ d, (1 + μ * sign (ω d))) *
      ∏ d ∈ T, sign (ω d)) / (2 : ℝ)^N = μ^T.card := by
  classical
  have hprod (ω : Fin N → Bool) :
      (∏ d, (1 + μ * sign (ω d))) * (∏ d ∈ T, sign (ω d)) =
        ∏ d, (1 + μ * sign (ω d)) * (if d ∈ T then sign (ω d) else 1) := by
    rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
    simp
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (d : Fin N) (b : Bool) =>
    (1 + μ * sign b) * (if d ∈ T then sign b else 1))]
  have hsum (d : Fin N) :
      (∑ b : Bool, (1 + μ * sign b) * (if d ∈ T then sign b else 1)) =
        2 * (if d ∈ T then μ else 1) := by
    by_cases h : d ∈ T <;> simp [sign, h] <;> ring
  simp_rw [hsum]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const]
  exact mul_div_cancel_left₀ _ (by positivity)

private def zValue : Fin 3 → ℝ := ![-2, 1, 3]

private def zWeight : Fin 3 → ℝ := ![8/22, 13/22, 1/22]

private def moment (j : ℕ) : ℝ := ∑ z : Fin 3, zWeight z * zValue z ^ j

private def modelY (N : ℕ) (d : Fin N) (ω : Fin N → Bool) : ℝ := sign (ω d)

private def modelFunctional (N : ℕ) : ((Fin N → Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ z : Fin 3, zWeight z *
    ((∑ ω : Fin N → Bool, (∏ d, (1 + (zValue z / Real.sqrt N) * sign (ω d))) *
      F ω) / (2 : ℝ)^N)
  map_add' F G := by
    simp [mul_add, Finset.sum_add_distrib, add_div]
  map_smul' r F := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm _ r, ← Finset.mul_sum, mul_div_assoc, mul_left_comm _ r]
    rw [Finset.mul_sum]

private lemma moment_values :
    moment 0 = 1 ∧ moment 1 = 0 ∧ moment 2 = 27/11 ∧
    moment 3 = -12/11 ∧ moment 4 = 111/11 ∧ moment 5 = 0 := by
  norm_num [moment, zWeight, zValue, Fin.sum_univ_succ]

private lemma model_character (N : ℕ) (T : Finset (Fin N)) :
    modelFunctional N (∏ d ∈ T, modelY N d) =
      moment T.card / Real.sqrt N ^ T.card := by
  classical
  change (∑ z : Fin 3, zWeight z *
    ((∑ ω : Fin N → Bool, (∏ d, (1 + (zValue z / Real.sqrt N) * sign (ω d))) *
      (∏ d ∈ T, modelY N d) ω) / (2 : ℝ)^N)) = _
  simp only [Finset.prod_apply, modelY]
  simp_rw [walsh_factor, div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  rfl

private lemma model_positive (N : ℕ) (hN : 9 ≤ N) (F : (Fin N → Bool) → ℝ) :
    0 ≤ modelFunctional N (F * F) := by
  have hN' : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 3 ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  have hspos : 0 < Real.sqrt N := by linarith
  change 0 ≤ ∑ z : Fin 3, zWeight z *
    ((∑ ω : Fin N → Bool, (∏ d, (1 + (zValue z / Real.sqrt N) * sign (ω d))) *
      (F ω * F ω)) / (2 : ℝ)^N)
  apply Finset.sum_nonneg
  intro z hz
  have hp : 0 ≤ zWeight z := by fin_cases z <;> norm_num [zWeight]
  have hzabs : |zValue z| ≤ 3 := by fin_cases z <;> norm_num [zValue]
  apply mul_nonneg hp
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg _ (mul_self_nonneg _)
  apply Finset.prod_nonneg
  intro d hd
  have ha : |(zValue z / Real.sqrt N) * sign (ω d)| ≤ 1 := by
    rw [abs_mul, abs_div, abs_of_pos hspos]
    have hb : |sign (ω d)| = 1 := by cases ω d <;> norm_num [sign]
    rw [hb, mul_one]
    exact (div_le_one₀ hspos).2 (hzabs.trans hs)
  have := (abs_le.mp ha).1
  linarith

private def oddCoords {N r : ℕ} (x : Fin r → Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun d => Odd (Finset.univ.filter (fun i => x i = d)).card)

private lemma odd_reduction {N r : ℕ} (x : Fin r → Fin N) :
    (∏ i, modelY N (x i)) = ∏ d ∈ oddCoords x, modelY N d := by
  classical
  funext ω
  simp only [Finset.prod_apply, modelY]
  rw [← Finset.prod_fiberwise' Finset.univ x (fun d => sign (ω d))]
  simp only [Finset.prod_const]
  rw [oddCoords, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro d hd
  have hs : sign (ω d)^2 = 1 := by cases ω d <;> norm_num [sign]
  rw [pow_eq_pow_mod _ hs]
  by_cases h : Odd (Finset.univ.filter (fun i => x i = d)).card
  · simp [h, Nat.odd_iff.mp h]
  · simp [h, Nat.not_odd_iff.mp h]

private lemma odd_card {N r : ℕ} (x : Fin r → Fin N) :
    (oddCoords x).card ≤ r ∧ (oddCoords x).card % 2 = r % 2 := by
  classical
  have hs : oddCoords x ⊆ Finset.univ.image x := by
    intro d hd
    apply (Finset.fiber_card_ne_zero_iff_mem_image Finset.univ x d).mp
    have ho := (Finset.mem_filter.mp hd).2
    intro hz
    rw [hz] at ho
    exact Nat.not_odd_zero ho
  constructor
  · calc
      _ ≤ (Finset.univ.image x).card := Finset.card_le_card hs
      _ ≤ r := by simpa using Finset.card_image_le (s := Finset.univ) (f := x)
  · have hsum : (∑ d : Fin N, (Finset.univ.filter (fun i : Fin r => x i = d)).card) = r := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin r)) (Finset.univ : Finset (Fin N)) x
    have hp := Finset.even_sum_iff_even_card_odd
      (s := (Finset.univ : Finset (Fin N)))
      (fun d => (Finset.univ.filter (fun i : Fin r => x i = d)).card)
    rw [hsum] at hp
    change Even r ↔ Even (oddCoords x).card at hp
    simp only [Nat.even_iff] at hp
    omega

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

private lemma distinct_bound (N r : ℕ) (hN : 0 < N) (hr : 2 ≤ r) (hr5 : r < 5)
    (g : Fin r → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |distinctIndexMoment (modelFunctional N) (modelY N) g| ≤
      11 * Real.sqrt N ^ r := by
  classical
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hm : |moment r| ≤ 11 := by
    interval_cases r <;> norm_num [moment_values.2.2.1, moment_values.2.2.2.1,
      moment_values.2.2.2.2.1]
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
    _ ≤ (11 / Real.sqrt N ^ r) * (N : ℝ)^r :=
      mul_le_mul (div_le_div_of_nonneg_right hm (by positivity)) hsum
        (abs_nonneg _) (by positivity)
    _ = 11 * Real.sqrt N ^ r := by
      have he : (N : ℝ)^r = Real.sqrt N ^ r * Real.sqrt N ^ r := by
        rw [← mul_pow, ← pow_two, Real.sq_sqrt (by positivity)]
      rw [he]
      field_simp

private lemma distinct_fifth_zero (N : ℕ) (g : Fin 5 → Fin N → ℝ) :
    distinctIndexMoment (modelFunctional N) (modelY N) g = 0 := by
  rw [distinct_moments, moment_values.2.2.2.2.2]
  simp

private def duplicate {N : ℕ} (y : Fin 4 → Fin N) : Fin 5 → Fin N :=
  ![y 0, y 0, y 1, y 2, y 3]

private lemma odd_duplicate {N : ℕ} (y : Fin 4 ↪ Fin N) :
    oddCoords (duplicate y) = {y 1, y 2, y 3} := by
  classical
  have h01 : y 0 ≠ y 1 := y.injective.ne (by decide)
  have h02 : y 0 ≠ y 2 := y.injective.ne (by decide)
  have h03 : y 0 ≠ y 3 := y.injective.ne (by decide)
  have h12 : y 1 ≠ y 2 := y.injective.ne (by decide)
  have h13 : y 1 ≠ y 3 := y.injective.ne (by decide)
  have h23 : y 2 ≠ y 3 := y.injective.ne (by decide)
  have hf (d : Fin N) :
      (Finset.univ.filter (fun i : Fin 5 => duplicate y i = d)).card =
        (if y 0 = d then 2 else 0) + (if y 1 = d then 1 else 0) +
        (if y 2 = d then 1 else 0) + (if y 3 = d then 1 else 0) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [duplicate, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    by_cases h0 : y 0 = d <;> by_cases h1 : y 1 = d <;>
      by_cases h2 : y 2 = d <;> by_cases h3 : y 3 = d <;>
      simp_all only [ite_true, ite_false] <;> omega
  ext d
  simp only [oddCoords, Finset.mem_filter, Finset.mem_univ, true_and, hf,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases h0 : y 0 = d
  · subst d; simp [*, Ne.symm]
  by_cases h1 : y 1 = d
  · subst d; simp [*, Ne.symm]
  by_cases h2 : y 2 = d
  · subst d; simp [*, Ne.symm]
  by_cases h3 : y 3 = d
  · subst d; simp [*, Ne.symm]
  · simp [*, Ne.symm]

private def fifthCount (N : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin N => (oddCoords x).card = 3)).card

private lemma collision_count_lower (N : ℕ) (hN : 9 ≤ N) :
    (N : ℝ)^4 / 4 ≤ (fifthCount N : ℝ) := by
  classical
  let f : (Fin 4 ↪ Fin N) → {x : Fin 5 → Fin N // (oddCoords x).card = 3} :=
    fun y => ⟨duplicate y, by
      rw [odd_duplicate]
      have h12 : y 1 ≠ y 2 := y.injective.ne (by decide)
      have h13 : y 1 ≠ y 3 := y.injective.ne (by decide)
      have h23 : y 2 ≠ y 3 := y.injective.ne (by decide)
      simp [h12, h13, h23]⟩
  have hinj : Function.Injective f := by
    intro y z h
    apply DFunLike.ext
    intro i
    fin_cases i
    · simpa [f, duplicate] using congrArg (fun u => u.val (0 : Fin 5)) h
    · simpa [f, duplicate] using congrArg (fun u => u.val (2 : Fin 5)) h
    · simpa [f, duplicate] using congrArg (fun u => u.val (3 : Fin 5)) h
    · simpa [f, duplicate] using congrArg (fun u => u.val (4 : Fin 5)) h
  have hc : N.descFactorial 4 ≤ fifthCount N := by
    simpa only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_subtype,
      fifthCount] using Fintype.card_le_of_injective f hinj
  have hN' : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) ≤ N := by positivity
  have hb1 : 0 ≤ (N : ℝ)-1 := by linarith
  have hb2 : 0 ≤ (N : ℝ)-2 := by linarith
  have hb3 : 0 ≤ (N : ℝ)-3 := by linarith
  have hprod : (2 * (N : ℝ) / 3)^3 ≤ ((N : ℝ)-1) * ((N : ℝ)-2) * ((N : ℝ)-3) := by
    calc
      _ = (2 * (N : ℝ) / 3) * (2 * (N : ℝ) / 3) * (2 * (N : ℝ) / 3) := by ring
      _ ≤ _ := by gcongr <;> first | positivity | linarith
  have hmul := mul_le_mul_of_nonneg_left hprod hpos
  have hcast : (N.descFactorial 4 : ℝ) =
      (N : ℝ) * ((N : ℝ)-1) * ((N : ℝ)-2) * ((N : ℝ)-3) := by
    norm_num [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ N),
      Nat.cast_sub (by omega : 2 ≤ N), Nat.cast_sub (by omega : 3 ≤ N)]
    ring
  have hc' : (N.descFactorial 4 : ℝ) ≤ (fifthCount N : ℝ) := by exact_mod_cast hc
  rw [hcast] at hc'
  nlinarith [pow_nonneg hpos 4]

private lemma model_fifth (N : ℕ) :
    quadraticFamilyMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin 5) _ => (1 : ℝ)) =
        (-12/11 / Real.sqrt N ^ 3) * (fifthCount N : ℝ) := by
  classical
  have hterm (x : Fin 5 → Fin N) :
      modelFunctional N (∏ i, modelY N (x i)) =
        if (oddCoords x).card = 3 then (-12/11 / Real.sqrt N ^ 3) else 0 := by
    rw [odd_reduction x, model_character]
    obtain ⟨hc, hp⟩ := odd_card x
    have hcases : (oddCoords x).card = 1 ∨ (oddCoords x).card = 3 ∨
        (oddCoords x).card = 5 := by omega
    rcases hcases with he | he | he <;> rw [he] <;>
      norm_num [moment_values.2.1, moment_values.2.2.2.1, moment_values.2.2.2.2.2]
  rw [quadraticFamilyMoment_eq_tuple_sum]
  simp only [Finset.prod_const, one_pow, one_mul]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_comm _ _

private lemma normalized_fifth (N : ℕ) (hN : 9 ≤ N) :
    quadraticFamilyMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin 5) _ => (1 : ℝ)) / Real.sqrt N ^ 5 ≤ -3/11 := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
  have hsq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hc := collision_count_lower N hN
  have hpow : Real.sqrt N ^ 3 * Real.sqrt N ^ 5 = (N : ℝ)^4 := by
    calc
      _ = (Real.sqrt N ^ 2)^4 := by ring
      _ = _ := by rw [hsq]
  rw [model_fifth]
  apply (div_le_iff₀ (pow_pos hs 5)).2
  apply (mul_le_mul_iff_right₀ (pow_pos hs 3)).mp
  calc
    Real.sqrt N ^ 3 * ((-12/11 / Real.sqrt N ^ 3) * (fifthCount N : ℝ)) =
        (-12/11) * (fifthCount N : ℝ) := by field_simp
    _ ≤ (-3/11) * (N : ℝ)^4 := by linarith
    _ = Real.sqrt N ^ 3 * ((-3/11) * Real.sqrt N ^ 5) := by rw [← hpow]; ring

private def counterData (n : ℕ) : FifthData where
  ι := Fin (n+9)
  A := (Fin (n+9) → Bool) → ℝ
  ℓ := modelFunctional (n+9)
  Y := modelY (n+9)
  a := 0
  b := 1
  H := ((n+9 : ℕ) : ℝ)
  L := 1

private lemma ratio_limit :
    Tendsto (fun n : ℕ => (counterData n).L / (counterData n).H) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n+9 : ℕ) : ℝ)) atTop (𝓝 0)
  simp only [Nat.cast_add, Nat.cast_ofNat, one_div]
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (9 : ℝ) tendsto_natCast_atTop_atTop)

set_option backward.isDefEq.respectTransparency false in
/-- The positive probability model refutes the fifth-order top-only implication. -/
theorem result : ¬ claim := by
  classical
  intro hclaim
  have hone : ∀ n, (counterData n).ℓ 1 = 1 := by
    intro n
    dsimp only [counterData]
    simpa only [Finset.prod_empty, Finset.card_empty, pow_zero, div_one, moment_values.1]
      using model_character (n+9) ∅
  have hpositive : ∀ n (y : (counterData n).A), 0 ≤ (counterData n).ℓ (y * y) := by
    intro n y
    exact model_positive (n+9) (by omega) y
  have hcenter : ∀ n d, (counterData n).ℓ ((counterData n).Y d) = 0 := by
    intro n d
    dsimp only [counterData] at d ⊢
    simpa only [Finset.prod_singleton, Finset.card_singleton, pow_one,
      moment_values.2.1, zero_div] using model_character (n+9) {d}
  have hquad : ∀ n d, (counterData n).Y d ^ 2 =
      (counterData n).a • (counterData n).Y d + (counterData n).b • 1 := by
    intro n d
    funext ω
    change sign (ω d)^2 = 0 * sign (ω d) + 1 * 1
    cases ω d <;> norm_num [sign]
  have hlower : ∀ n r, 2 ≤ r → r < 5 → ∀ g : Fin r → (counterData n).ι → ℝ,
      (∀ i d, |g i d| ≤ 1) →
      |distinctIndexMoment (counterData n).ℓ (counterData n).Y g| ≤
        11 * Real.sqrt ((counterData n).H * (counterData n).L)^r := by
    intro n r hr hr5 g hg
    dsimp only [counterData] at g hg ⊢
    simpa only [mul_one] using
      distinct_bound (n+9) r (by omega) hr hr5 g hg
  have htop : ∀ n (g : Fin 5 → (counterData n).ι → ℝ), (∀ i d, |g i d| ≤ 1) →
      distinctIndexMoment (counterData n).ℓ (counterData n).Y g = 0 := by
    intro n g _
    exact distinct_fifth_zero (n+9) g
  have hlimit := hclaim 11 (by norm_num) counterData hone hpositive hcenter hquad
    (by intro n; change (1 : ℝ) ≤ ((n+9 : ℕ) : ℝ)
        exact_mod_cast (show 1 ≤ n+9 by omega))
    (by intro n; exact le_refl 1)
    (by intro n; norm_num [counterData])
    (by intro n; norm_num [counterData])
    (by intro n
        change (Fintype.card (Fin (n+9)) : ℝ) ≤ 11 * ((n+9 : ℕ) : ℝ)
        rw [Fintype.card_fin]
        have hn : (0 : ℝ) ≤ ((n+9 : ℕ) : ℝ) := by positivity
        linarith)
    hlower htop ratio_limit
  have hev := hlimit.eventually (lt_mem_nhds (show -(1 : ℝ)/11 < 0 by norm_num))
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hev
  have hb : quadraticFamilyMoment (counterData n).ℓ (counterData n).Y
      (fun (_ : Fin 5) _ => (1 : ℝ)) /
        Real.sqrt ((counterData n).H * (counterData n).L)^5 ≤ -3/11 := by
    dsimp only [counterData]
    simpa only [mul_one] using normalized_fifth (n+9) (by omega)
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FifthOrderTopOnlyRefutation
