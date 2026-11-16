/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite mixtures of biased Boolean cubes have explicit Walsh characters and parity reductions. -/

/-
proof_shape: walsh_factor, mixture_character, mixture_positive, odd_reduction,
  odd_card: bind-only (consumers: FifthOrderTopOnlyRefutation,
  SixthOrderTopPairingRefutation, and mixture_distinct_moments).
proof_shape: mixture_distinct_moments: bind-only (consumers:
  FifthOrderTopOnlyRefutation.distinct_bound and distinct_fifth_zero;
  SixthOrderTopPairingRefutation.distinct_bound and subset_unit_moment).
proof_shape: mixture_distinct_bound: content (consumers:
  FifthOrderTopOnlyRefutation.distinct_bound and
  TopOrderObstructionFamily mixture moment bounds).
escape_witness: mixture_distinct_bound proves the arbitrary-order estimate for
  bounded coefficient families, controlling the distinct mixture moment by the
  absolute scalar moment times the natural square-root scale.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticMomentDefs

/-! A finite mixture of biased Boolean cubes and its parity bookkeeping. -/

open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

def sign (b : Bool) : ℝ := if b then 1 else -1

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

def mixtureFunctional {κ : Type} [Fintype κ]
    (N : ℕ) (zValue zWeight : κ → ℝ) : ((Fin N → Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ z : κ, zWeight z *
    ((∑ ω : Fin N → Bool, (∏ d, (1 + (zValue z / Real.sqrt N) * sign (ω d))) *
      F ω) / (2 : ℝ)^N)
  map_add' F G := by
    simp [mul_add, Finset.sum_add_distrib, add_div]
  map_smul' r F := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm _ r, ← Finset.mul_sum, mul_div_assoc, mul_left_comm _ r]
    rw [Finset.mul_sum]

def modelY (N : ℕ) (d : Fin N) (ω : Fin N → Bool) : ℝ := sign (ω d)

lemma mixture_character {κ : Type} [Fintype κ]
    (N : ℕ) (zValue zWeight : κ → ℝ) (T : Finset (Fin N)) :
    mixtureFunctional N zValue zWeight (∏ d ∈ T, modelY N d) =
      (∑ z : κ, zWeight z * zValue z ^ T.card) / Real.sqrt N ^ T.card := by
  classical
  change (∑ z : κ, zWeight z *
    ((∑ ω : Fin N → Bool, (∏ d, (1 + (zValue z / Real.sqrt N) * sign (ω d))) *
      (∏ d ∈ T, modelY N d) ω) / (2 : ℝ)^N)) = _
  simp only [Finset.prod_apply, modelY]
  simp_rw [walsh_factor, div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]

lemma mixture_positive {κ : Type} [Fintype κ]
    (N : ℕ) (zValue zWeight : κ → ℝ)
    (hbound : ∀ z, |zValue z| ≤ Real.sqrt N)
    (hweight : ∀ z, 0 ≤ zWeight z) (hN : 0 < N)
    (F : (Fin N → Bool) → ℝ) :
    0 ≤ mixtureFunctional N zValue zWeight (F * F) := by
  classical
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  change 0 ≤ ∑ z : κ, zWeight z *
    ((∑ ω : Fin N → Bool, (∏ d, (1 + (zValue z / Real.sqrt N) * sign (ω d))) *
      (F ω * F ω)) / (2 : ℝ)^N)
  apply Finset.sum_nonneg
  intro z hz
  apply mul_nonneg (hweight z)
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg _ (mul_self_nonneg _)
  apply Finset.prod_nonneg
  intro d hd
  have ha : |(zValue z / Real.sqrt N) * sign (ω d)| ≤ 1 := by
    rw [abs_mul, abs_div, abs_of_pos hs]
    have hb : |sign (ω d)| = 1 := by cases ω d <;> norm_num [sign]
    rw [hb, mul_one]
    exact (div_le_one₀ hs).2 (hbound z)
  have := (abs_le.mp ha).1
  linarith

def oddCoords {N r : ℕ} (x : Fin r → Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun d => Odd (Finset.univ.filter (fun i => x i = d)).card)

lemma odd_reduction {N r : ℕ} (x : Fin r → Fin N) :
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
  by_cases h : Odd (Finset.univ.filter (fun i : Fin r => x i = d)).card
  · simp [h, Nat.odd_iff.mp h]
  · simp [h, Nat.not_odd_iff.mp h]

lemma odd_card {N r : ℕ} (x : Fin r → Fin N) :
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

/-- Distinct-index moments of any finite bias mixture factor into its scalar moment
and the injective coefficient sum. -/
lemma mixture_distinct_moments {κ : Type} [Fintype κ]
    (N : ℕ) (zValue zWeight : κ → ℝ) (r : ℕ) (g : Fin r → Fin N → ℝ) :
    distinctIndexMoment (mixtureFunctional N zValue zWeight) (modelY N) g =
      ((∑ z : κ, zWeight z * zValue z ^ r) / Real.sqrt N ^ r) *
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
  rw [odd_reduction x, mixture_character, hodd]
  simp only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  exact mul_comm _ _

/-- Every bounded coefficient family has its distinct mixture moment bounded
by the absolute scalar moment times the natural square-root scale. -/
lemma mixture_distinct_bound {κ : Type} [Fintype κ]
    (N r : ℕ) (hN : 0 < N) (zValue zWeight : κ → ℝ)
    (g : Fin r → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |distinctIndexMoment (mixtureFunctional N zValue zWeight) (modelY N) g| ≤
      |∑ z : κ, zWeight z * zValue z ^ r| * Real.sqrt N ^ r := by
  classical
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
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
  rw [mixture_distinct_moments, abs_mul, abs_div, abs_of_pos (pow_pos hs r)]
  calc
    _ ≤ (|∑ z : κ, zWeight z * zValue z ^ r| / Real.sqrt N ^ r) * (N : ℝ)^r :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      have he : (N : ℝ)^r = Real.sqrt N ^ r * Real.sqrt N ^ r := by
        rw [← mul_pow, ← pow_two, Real.sq_sqrt (by positivity)]
      rw [he]
      field_simp


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
