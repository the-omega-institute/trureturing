/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionCore
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Uniform scalar leading terms and full-defect limits for finite bias mixtures. -/

/-
proof_shape: scalarMoment, scalarGaussian, scalarDefect, gaussianPairingCount,
  mixtureLeadingConstant: definitions.
proof_shape: mixture_uniform_leading_bound_all, mixture_propagation_limit: content
  (consumer: top_order_transfer_fails in TopOrderObstructionFamily).
proof_shape: scalar_product_perturbation: content
  (local helper consumed by mixture_uniform_leading_bound_all).
proof_shape: mixture_unit_pair, descFactorial_ratio_tendsto,
  mixture_subset_unit_normalized, sqrt_pow_even, mixture_subset_pairing_normalized,
  mixture_subset_defect_normalized, mixture_subset_defect_limit,
  sum_partialPairings_by_card, partialPairing_normalization: bind-only
  (local helpers consumed along the proof path of mixture_propagation_limit).
proof_shape: pairing_polynomial_normalize, pairing_polynomial_scalar_rank_one:
  bind-only (local helpers consumed by mixture_uniform_leading_bound_all).
escape_witness: mixture_uniform_leading_bound_all identifies the scalar leading
  term of the uniform normalized distinct pairing defect with error of order 1/N.
  mixture_propagation_limit groups partial pairings by cardinality and proves the
  asymptotic full-defect limit as a weighted sum of scalar defects.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.MixtureMomentLemmas
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectInversion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PerfectPairingCount
import Mathlib.Analysis.SpecialFunctions.Choose

open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open FifthOrderTopOnlyRefutation

def scalarMoment {κ : Type} [Fintype κ] (zValue zWeight : κ → ℝ) (j : ℕ) : ℝ :=
  ∑ z : κ, zWeight z * zValue z ^ j

def scalarGaussian (j : ℕ) (v : ℝ) : ℝ :=
  (if Even j then (Nat.doubleFactorial (j - 1) : ℝ) else 0) * v ^ (j / 2)

def scalarDefect {κ : Type} [Fintype κ] (zValue zWeight : κ → ℝ) (j : ℕ) : ℝ :=
  scalarMoment zValue zWeight j - scalarGaussian j (scalarMoment zValue zWeight 2)

lemma mixture_propagation_limit {κ : Type} [Fintype κ]
    (k : ℕ) (zValue zWeight : κ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hunit : scalarMoment zValue zWeight 0 = 1)
    (hcenter : scalarMoment zValue zWeight 1 = 0)
    (hmoment : ∀ r, 2 ≤ r → r < k → |scalarMoment zValue zWeight r| ≤ C) :
    Tendsto (fun N : ℕ =>
      (subsetFamilyMoment (mixtureFunctional N zValue zWeight) (modelY N)
          (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (mixtureFunctional N zValue zWeight) (modelY N)
            (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)))) / Real.sqrt N ^ k)
      atTop (𝓝 (∑ p ∈ Finset.range (k / 2 + 1),
        ((k.choose (2 * p) * Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) *
          scalarDefect zValue zWeight (k - 2 * p))) := by
  classical
  have mixture_unit_pair {κ : Type} [Fintype κ] {k : ℕ}
      (N : ℕ) (hN : 0 < N) (zValue zWeight : κ → ℝ)
      (e : Finset (Fin k)) (he : e.card = 2) :
      subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N)
        (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) e =
          scalarMoment zValue zWeight 2 * ((N : ℝ) - 1) := by
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hc : (N.descFactorial 2 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
      norm_num [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ N)]
      ring
    rw [SixthOrderTopPairingRefutation.subset_unit_moment zValue zWeight, he,
      Real.sq_sqrt (by positivity), hc]
    simp only [scalarMoment]
    field_simp [hNz] <;> ring

  have descFactorial_ratio_tendsto (j : ℕ) :
      Tendsto (fun N : ℕ => (N.descFactorial j : ℝ) / (N : ℝ)^j) atTop (𝓝 1) := by
    have hz : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ j ≠ 0 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact pow_ne_zero j (by exact_mod_cast (show N ≠ 0 by omega))
    have hh := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp
      (isEquivalent_descFactorial j)
    convert hh using 1

  have mixture_subset_unit_normalized {κ : Type} [Fintype κ] {k : ℕ}
      (N : ℕ) (hN : 0 < N) (zValue zWeight : κ → ℝ) (U : Finset (Fin k)) :
      subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N)
          (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U / Real.sqrt N ^ U.card =
        scalarMoment zValue zWeight U.card *
          ((N.descFactorial U.card : ℝ) / (N : ℝ)^U.card) := by
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have he : (N : ℝ)^U.card = Real.sqrt N ^ U.card * Real.sqrt N ^ U.card := by
      rw [← mul_pow, ← pow_two, Real.sq_sqrt (by positivity)]
    rw [SixthOrderTopPairingRefutation.subset_unit_moment zValue zWeight, he]
    simp only [scalarMoment]
    field_simp [hs.ne'] <;> ring

  have sqrt_pow_even (N j : ℕ) (hj : Even j) :
      Real.sqrt N ^ j = (N : ℝ) ^ (j / 2) := by
    obtain ⟨r, hr⟩ := hj
    have hjr : j = 2 * r := by omega
    rw [hjr, pow_mul, Real.sq_sqrt (by positivity)]
    congr 1
    omega

  have mixture_subset_pairing_normalized {κ : Type} [Fintype κ] {k : ℕ}
      (N : ℕ) (hN : 0 < N) (zValue zWeight : κ → ℝ) (U : Finset (Fin k)) :
      finitePairingPolynomial U
        (subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N)
          (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ))) / Real.sqrt N ^ U.card =
        scalarGaussian U.card (scalarMoment zValue zWeight 2) *
          (1 - 1 / (N : ℝ)) ^ (U.card / 2) := by
    rw [finitePairingPolynomial_const U _
        (scalarMoment zValue zWeight 2 * ((N : ℝ) - 1))
        (fun e he => mixture_unit_pair N hN zValue zWeight e he), perfectPairingCount]
    by_cases hU : Even U.card
    · rw [if_pos hU, sqrt_pow_even N U.card hU, scalarGaussian, if_pos hU]
      have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have ht : (N : ℝ) - 1 = (N : ℝ) * (1 - 1 / (N : ℝ)) := by
        field_simp [hNz] <;> ring
      rw [ht]
      simp only [mul_pow]
      field_simp [hNz] <;> ring
    · simp [hU, scalarGaussian]

  have mixture_subset_defect_normalized {κ : Type} [Fintype κ] {k : ℕ}
      (N : ℕ) (hN : 0 < N) (zValue zWeight : κ → ℝ) (U : Finset (Fin k)) :
      subsetPairingDefect (mixtureFunctional N zValue zWeight) (modelY N)
          (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U / Real.sqrt N ^ U.card =
        scalarMoment zValue zWeight U.card *
          ((N.descFactorial U.card : ℝ) / (N : ℝ)^U.card) -
        scalarGaussian U.card (scalarMoment zValue zWeight 2) *
          (1 - 1 / (N : ℝ)) ^ (U.card / 2) := by
    rw [subsetPairingDefect, sub_div, mixture_subset_unit_normalized N hN,
      mixture_subset_pairing_normalized N hN]

  have mixture_subset_defect_limit {κ : Type} [Fintype κ] {k : ℕ}
      (zValue zWeight : κ → ℝ) (U : Finset (Fin k)) :
      Tendsto (fun N : ℕ =>
        subsetPairingDefect (mixtureFunctional N zValue zWeight) (modelY N)
          (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U / Real.sqrt N ^ U.card)
        atTop (𝓝 (scalarDefect zValue zWeight U.card)) := by
    have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, one_div] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0))
    have hone : Tendsto (fun N : ℕ => (1 : ℝ) - 1 / (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hi :
        Tendsto (fun N : ℕ => (1 : ℝ) - 1 / (N : ℝ)) atTop (𝓝 (1 - 0)))
    have hp := (hone.pow (U.card / 2)).const_mul
      (scalarGaussian U.card (scalarMoment zValue zWeight 2))
    have hm := (descFactorial_ratio_tendsto U.card).const_mul
      (scalarMoment zValue zWeight U.card)
    have hh := hm.sub hp
    simp only [sub_zero, one_pow, mul_one] at hh
    change Tendsto _ atTop (𝓝 (scalarMoment zValue zWeight U.card -
      scalarGaussian U.card (scalarMoment zValue zWeight 2)))
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (mixture_subset_defect_normalized N (by omega) zValue zWeight U).symm

  have sum_partialPairings_by_card {α : Type} [Fintype α] [DecidableEq α]
      (U : Finset α) (F : ℕ → ℝ) :
      (∑ P : Finset (Finset α) with IsPartialPairing U P,
        F (U.card - 2 * P.card)) =
      ∑ p ∈ Finset.range (U.card / 2 + 1),
        ((U.card.choose (2 * p) * Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) *
          F (U.card - 2 * p) := by
    classical
    let A := (Finset.univ : Finset (Finset (Finset α))).filter (IsPartialPairing U)
    let B := Finset.range (U.card / 2 + 1)
    have hm : ∀ P ∈ A, P.card ∈ B := by
      intro P hPA
      have hP := (Finset.mem_filter.mp hPA).2
      have hc := (show IsPerfectPairing (pairingSupport P) P from
        ⟨⟨hP.1, hP.2.1, fun _ h => h⟩, rfl⟩).card
      have hle := Finset.card_le_card hP.2.2
      simp only [B, Finset.mem_range]
      omega
    change (∑ P ∈ A, F (U.card - 2 * P.card)) = _
    rw [← Finset.sum_fiberwise_of_maps_to hm]
    apply Finset.sum_congr rfl
    intro p hp
    have he : A.filter (fun P => P.card = p) =
        Finset.univ.filter (fun P => IsPartialPairing U P ∧ P.card = p) := by
      ext P
      simp [A, and_assoc]
    calc
      (∑ P ∈ A with P.card = p, F (U.card - 2 * P.card)) =
          ∑ _P ∈ A with _P.card = p, F (U.card - 2 * p) := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [(Finset.mem_filter.mp hP).2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, he, partialPairingCount]

  have partialPairing_normalization {k : ℕ} (N : ℕ) (hN : 0 < N)
      (P : Finset (Finset (Fin k))) (hP : IsPartialPairing Finset.univ P) (x : ℝ) :
      (N : ℝ)^P.card * x / Real.sqrt N ^ k =
        x / Real.sqrt N ^ (Finset.univ \ pairingSupport P).card := by
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have hc := (show IsPerfectPairing (pairingSupport P) P from
      ⟨⟨hP.1, hP.2.1, fun _ h => h⟩, rfl⟩).card
    have hle := Finset.card_le_card hP.2.2
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    have hj : (Finset.univ \ pairingSupport P).card = k - 2 * P.card := by
      rw [Finset.card_sdiff_of_subset hP.2.2, hc]
      simp
    have hk : k = 2 * P.card + (Finset.univ \ pairingSupport P).card := by omega
    have hpow : Real.sqrt N ^ k = (N : ℝ)^P.card *
        Real.sqrt N ^ (Finset.univ \ pairingSupport P).card := by
      conv_lhs => rw [hk, pow_add, pow_mul, Real.sq_sqrt (by positivity)]
    rw [hpow]
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hNz, hs.ne'] <;> ring

  let F : ℕ → ℝ := fun N =>
    (subsetFamilyMoment (mixtureFunctional N zValue zWeight) (modelY N)
          (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) Finset.univ -
      finitePairingPolynomial Finset.univ
        (subsetFamilyMoment (mixtureFunctional N zValue zWeight) (modelY N)
          (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)))) / Real.sqrt N ^ k
  let S : ℕ → ℝ := fun N =>
    ∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
      subsetPairingDefect (mixtureFunctional N zValue zWeight) (modelY N)
        (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ))
        (Finset.univ \ pairingSupport P) /
          Real.sqrt N ^ (Finset.univ \ pairingSupport P).card
  have hS : Tendsto S atTop
      (𝓝 (∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
        scalarDefect zValue zWeight (Finset.univ \ pairingSupport P).card)) := by
    exact tendsto_finsetSum _ (fun P _ =>
      mixture_subset_defect_limit zValue zWeight (Finset.univ \ pairingSupport P))
  have herr : ∀ᶠ N : ℕ in atTop,
      |F N - S N| ≤ pairingDefectConstant k C *
        (Real.sqrt (1 / (N : ℝ)) + 1 / N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : 0 < N := by omega
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hu : mixtureFunctional N zValue zWeight 1 = 1 := by
      calc
        _ = scalarMoment zValue zWeight 0 := by
          simpa [scalarMoment] using mixture_character N zValue zWeight ∅
        _ = 1 := hunit
    have hz : ∀ d, mixtureFunctional N zValue zWeight (modelY N d) = 0 := by
      intro d
      calc
        _ = scalarMoment zValue zWeight 1 / Real.sqrt N ^ 1 := by
          simpa [scalarMoment] using mixture_character N zValue zWeight {d}
        _ = 0 := by rw [hcenter, zero_div]
    have hq : ∀ d, modelY N d ^ 2 = (0 : ℝ) • modelY N d + (1 : ℝ) • 1 := by
      intro d
      funext ω
      change sign (ω d)^2 = 0 * sign (ω d) + 1 * 1
      cases ω d <;> norm_num [sign]
    have hR : DisjointLabelMomentBound (mixtureFunctional N zValue zWeight)
        (modelY N) (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ))
        C (Real.sqrt ((N : ℝ) * 1)) := by
      intro r hr hrk labels _ _
      simp only [Finset.prod_const_one, mul_one]
      have hb := (mixture_distinct_bound N r hn zValue zWeight
        (fun (_ : Fin r) (_ : Fin N) => (1 : ℝ))
        (by simp)).trans (mul_le_mul_of_nonneg_right (hmoment r hr hrk) (by positivity))
      convert hb using 1
      congr 1
      unfold distinctIndexMoment
      apply Finset.sum_congr
      · ext x
        simp
      · intro x hx
        rfl
    obtain ⟨E, _, hE, hb⟩ := quadratic_pairing_defect_transfer
      (mixtureFunctional N zValue zWeight) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ))
      0 1 C N 1 hC (by exact_mod_cast hN) (by norm_num)
      (by simpa using (show 0 ≤ C by linarith)) (by simpa using hC)
      hq hu hz
      (by simp only [Fintype.card_fin]; nlinarith [show (0 : ℝ) ≤ N by positivity])
      (by simp) hR
    simp only [subsetWeightSum, indexSum, Finset.prod_const_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, one_pow, one_mul, Finset.prod_const] at hE
    have heq : F N - S N = E / Real.sqrt N ^ k := by
      dsimp only [F, S]
      change (quadraticFamilyMoment _ _ _ - _) / _ - _ = _
      rw [hE, add_div, Finset.sum_div]
      rw [Finset.sum_congr rfl (fun P hP =>
        partialPairing_normalization N hn P (Finset.mem_filter.mp hP).2 _)]
      ring
    rw [heq, abs_div, abs_of_pos (pow_pos hs k)]
    apply (div_le_iff₀ (pow_pos hs k)).2
    simpa only [mul_one, mul_assoc, mul_left_comm, mul_comm] using hb
  have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0))
  have he0 : Tendsto (fun N => F N - S N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using herr)
    simpa only [Real.sqrt_zero, add_zero, mul_zero] using
      ((hi.sqrt).add hi).const_mul (pairingDefectConstant k C)
  have hf := he0.add hS
  simp only [zero_add] at hf
  have hf' : Tendsto F atTop
      (𝓝 (∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
        scalarDefect zValue zWeight (Finset.univ \ pairingSupport P).card)) := by
    convert hf using 1
    funext N
    ring
  convert hf' using 1
  have hj : (∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
        scalarDefect zValue zWeight (Finset.univ \ pairingSupport P).card) =
      ∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
        scalarDefect zValue zWeight (k - 2 * P.card) := by
    apply Finset.sum_congr rfl
    intro P hP
    have hp := (Finset.mem_filter.mp hP).2
    have hc := (show IsPerfectPairing (pairingSupport P) P from
      ⟨⟨hp.1, hp.2.1, fun _ h => h⟩, rfl⟩).card
    rw [Finset.card_sdiff_of_subset hp.2.2, hc]
    simp
  rw [hj]
  have hg := sum_partialPairings_by_card (Finset.univ : Finset (Fin k))
    (scalarDefect zValue zWeight)
  simpa only [Finset.card_univ, Fintype.card_fin] using
    congrArg (fun x : ℝ => 𝓝 x) hg.symm

def gaussianPairingCount (j : ℕ) : ℝ :=
  if Even j then (Nat.doubleFactorial (j - 1) : ℝ) else 0

def mixtureLeadingConstant {ζ : Type} [Fintype ζ]
    (zValue zWeight : ζ → ℝ) (j : ℕ) : ℝ :=
  |scalarMoment zValue zWeight j| * (j.choose 2 : ℝ) +
    gaussianPairingCount j * (j / 2 : ℕ) * |scalarMoment zValue zWeight 2| *
      (max 1 |scalarMoment zValue zWeight 2|) ^ (j / 2)


set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
lemma mixture_uniform_leading_bound_all {ζ : Type} {α : Type}
    [Fintype ζ] [Fintype α] [DecidableEq α]
    (N : ℕ) (zValue zWeight : ζ → ℝ) (U : Finset α)
    (hN : 0 < N) (hUN : U.card ≤ N)
    (f : α → Fin N → ℝ) (hf : ∀ i d, |f i d| ≤ 1) :
    |subsetPairingDefect (mixtureFunctional N zValue zWeight) (modelY N) f U /
        Real.sqrt N ^ U.card -
      scalarDefect zValue zWeight U.card *
        ∏ i ∈ U, (∑ d, f i d) / (N : ℝ)| ≤
      mixtureLeadingConstant zValue zWeight U.card / N := by
  classical

  have scalar_product_perturbation {α : Type} [DecidableEq α]
      (s : Finset α) (f g : α → ℝ) (B D : ℝ) (hB : 1 ≤ B) (hD : 0 ≤ D)
      (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B)
      (hd : ∀ i ∈ s, |f i - g i| ≤ D) :
      |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ (s.card : ℝ) * D * B ^ s.card := by
    classical
    revert hf hg hd
    induction s using Finset.induction_on with
    | empty => intro _ _ _; simp
    | @insert a s ha ih =>
      intro hf hg hd
      have hB0 : 0 ≤ B := by linarith
      have hf' : ∀ i ∈ s, |f i| ≤ B := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hg' : ∀ i ∈ s, |g i| ≤ B := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hd' : ∀ i ∈ s, |f i - g i| ≤ D :=
        fun i hi => hd i (Finset.mem_insert_of_mem hi)
      have hi := ih hf' hg' hd'
      have hprod : |∏ i ∈ s, f i| ≤ B ^ s.card := by
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _i ∈ s, B :=
            Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) hf'
          _ = _ := by simp
      have hfirst : |(f a - g a) * ∏ i ∈ s, f i| ≤ D * B ^ s.card := by
        rw [abs_mul]
        exact mul_le_mul (hd a (by simp)) hprod (abs_nonneg _) hD
      have hsecond : |g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| ≤
          B * ((s.card : ℝ) * D * B ^ s.card) := by
        rw [abs_mul]
        exact mul_le_mul (hg a (by simp)) hi (abs_nonneg _) hB0
      have hpstep : B ^ s.card ≤ B ^ (s.card + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (pow_nonneg hB0 _) hB
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      calc
        _ = |(f a - g a) * (∏ i ∈ s, f i) +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by congr 1; ring
        _ ≤ |(f a - g a) * ∏ i ∈ s, f i| +
            |g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := abs_add_le _ _
        _ ≤ D * B ^ s.card + B * ((s.card : ℝ) * D * B ^ s.card) :=
          add_le_add hfirst hsecond
        _ ≤ D * B ^ (s.card + 1) + B * ((s.card : ℝ) * D * B ^ s.card) := by
          gcongr
        _ = ((s.card + 1 : ℕ) : ℝ) * D * B ^ (s.card + 1) := by
          push_cast
          rw [pow_succ]
          ring

  have pairing_polynomial_normalize {α : Type} [Fintype α] [DecidableEq α]
      (U : Finset α) (c : Finset α → ℝ) (s : ℝ) :
      finitePairingPolynomial U (fun e => c e / s ^ 2) =
        finitePairingPolynomial U c / s ^ U.card := by
    unfold finitePairingPolynomial
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    have hp := (Finset.mem_filter.mp hP).2
    rw [Finset.prod_div_distrib, Finset.prod_const, ← pow_mul, hp.card]

  have pairing_polynomial_scalar_rank_one {α : Type}
      [Fintype α] [DecidableEq α] (U : Finset α) (a : ℝ) (x : α → ℝ) :
      finitePairingPolynomial U (fun e => a * ∏ i ∈ e, x i) =
        (((Finset.univ : Finset (Finset (Finset α))).filter
          (IsPerfectPairing U)).card : ℝ) * a ^ (U.card / 2) * ∏ i ∈ U, x i := by
    have hscale : finitePairingPolynomial U (fun e => a * ∏ i ∈ e, x i) =
        a ^ (U.card / 2) * finitePairingPolynomial U (fun e => ∏ i ∈ e, x i) := by
      unfold finitePairingPolynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      have hp := (Finset.mem_filter.mp hP).2
      have hc : P.card = U.card / 2 := by rw [hp.card]; omega
      rw [Finset.prod_mul_distrib, Finset.prod_const, hc]
    rw [hscale, finitePairingPolynomial_rankOne U _ x (by intro e he; rfl)]
    ring

  have mixture_distinct_normalized_leading {ζ : Type} {α : Type}
      [Fintype ζ] [Fintype α] [DecidableEq α]
      (N : ℕ) (zValue zWeight : ζ → ℝ) (U : Finset α)
      (hN : 0 < N) (hUN : U.card ≤ N) (hU : 1 ≤ U.card)
      (f : α → Fin N → ℝ) (hf : ∀ i d, |f i d| ≤ 1) :
      |subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) f U /
          Real.sqrt N ^ U.card -
        scalarMoment zValue zWeight U.card *
          ∏ i ∈ U, (∑ d, f i d) / (N : ℝ)| ≤
        (|scalarMoment zValue zWeight U.card| * (U.card.choose 2 : ℝ)) / N := by
    classical
    let g : Fin (Fintype.card U) → Fin N → ℝ :=
      fun i => f (((Fintype.equivFin U).symm i).val)
    have hg : ∀ i d, |g i d| ≤ 1 := fun i d => hf _ d
    have hprod : (∏ i, ∑ d, g i d) = ∏ i ∈ U, ∑ d, f i d := by
      rw [← Finset.prod_attach U]
      simpa only [Finset.attach_eq_univ] using
        (Fintype.prod_equiv (Fintype.equivFin U).symm
          (fun i => ∑ d, g i d) (fun i : U => ∑ d, f i.val d) (by intro i; rfl))
    have hi := inj_sum_product_bound (Fintype.card U) N
      (by simpa using hU) (by simpa using hUN) g hg
    simp only [Fintype.card_coe] at hi
    have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hnne := ne_of_gt hnpos
    have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 hnpos
    have hsquare : Real.sqrt N ^ U.card * Real.sqrt N ^ U.card = (N : ℝ) ^ U.card := by
      rw [← mul_pow, ← pow_two, Real.sq_sqrt hnpos.le]
    have hR : subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) f U /
        Real.sqrt N ^ U.card =
        (scalarMoment zValue zWeight U.card *
          ∑ x : Fin (Fintype.card U) → Fin N with Function.Injective x,
            ∏ i, g i (x i)) / (N : ℝ) ^ U.card := by
      have hbridge : subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) f U =
          distinctIndexMoment (mixtureFunctional N zValue zWeight) (modelY N) g := by
        unfold subsetDistinctMoment distinctIndexMoment
        apply Finset.sum_congr
        · ext x
          simp
        · intro x hx
          rfl
      rw [hbridge, mixture_distinct_moments]
      simp only [Fintype.card_coe]
      rw [div_mul_eq_mul_div, div_div, hsquare]
      rfl
    have hA : (∏ i ∈ U, (∑ d, f i d) / (N : ℝ)) =
        (∏ i ∈ U, ∑ d, f i d) / (N : ℝ) ^ U.card := by
      rw [Finset.prod_div_distrib, Finset.prod_const]
    rw [hR, hA]
    have heq : (scalarMoment zValue zWeight U.card *
        ∑ x : Fin (Fintype.card U) → Fin N with Function.Injective x, ∏ i, g i (x i)) /
          (N : ℝ) ^ U.card - scalarMoment zValue zWeight U.card *
          ((∏ i ∈ U, ∑ d, f i d) / (N : ℝ) ^ U.card) =
        (scalarMoment zValue zWeight U.card / (N : ℝ) ^ U.card) *
          ((∑ x : Fin (Fintype.card U) → Fin N with Function.Injective x,
            ∏ i, g i (x i)) - ∏ i, ∑ d, g i d) := by rw [hprod]; ring
    rw [heq, abs_mul, abs_div, abs_of_pos (pow_pos hnpos _)]
    calc
      _ ≤ (|scalarMoment zValue zWeight U.card| / (N : ℝ) ^ U.card) *
          ((U.card.choose 2 : ℝ) * (N : ℝ) ^ (U.card - 1)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by
        have hp : (N : ℝ) ^ U.card = (N : ℝ) ^ (U.card - 1) * N := by
          rw [← pow_succ, Nat.sub_add_cancel hU]
        rw [hp]
        field_simp [hnne] <;> ring

  have mixture_uniform_leading_bound {ζ : Type} {α : Type}
      [Fintype ζ] [Fintype α] [DecidableEq α]
      (N : ℕ) (zValue zWeight : ζ → ℝ) (U : Finset α)
      (hN : 0 < N) (hUN : U.card ≤ N) (hU : 1 ≤ U.card)
      (f : α → Fin N → ℝ) (hf : ∀ i d, |f i d| ≤ 1) :
      |subsetPairingDefect (mixtureFunctional N zValue zWeight) (modelY N) f U /
          Real.sqrt N ^ U.card -
        scalarDefect zValue zWeight U.card *
          ∏ i ∈ U, (∑ d, f i d) / (N : ℝ)| ≤
        mixtureLeadingConstant zValue zWeight U.card / N := by
    classical
    let M := scalarMoment zValue zWeight
    let R := subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) f
    let a : α → ℝ := fun i => (∑ d, f i d) / (N : ℝ)
    let r : Finset α → ℝ := fun e => R e / (N : ℝ)
    let c : Finset α → ℝ := fun e => M 2 * ∏ i ∈ e, a i
    let B : ℝ := max 1 |M 2|
    have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hnne := ne_of_gt hnpos
    have hsquare : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt hnpos.le
    have hA (i : α) : |∑ d, f i d| ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ d, |f i d| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun d _ => hf i d)
        _ = _ := by simp
    have ha (i : α) : |a i| ≤ 1 := by
      rw [show a i = (∑ d, f i d) / (N : ℝ) from rfl, abs_div, abs_of_pos hnpos]
      exact (div_le_one₀ hnpos).mpr (hA i)
    have hc (e : Finset α) : |c e| ≤ |M 2| := by
      rw [show c e = M 2 * ∏ i ∈ e, a i from rfl, abs_mul, Finset.abs_prod]
      calc
        _ ≤ |M 2| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => ha i)
        _ = _ := mul_one _
    have hr (e : Finset α) (he : e.card = 2) : |r e| ≤ |M 2| := by
      have hb := mixture_distinct_bound N (Fintype.card e) hN zValue zWeight
        (fun i => f (((Fintype.equivFin e).symm i).val))
        (fun i d => hf _ d)
      have hbRaw : |R e| ≤ |M (Fintype.card e)| * Real.sqrt N ^ (Fintype.card e) := by
        dsimp only [R, subsetDistinctMoment, M, scalarMoment]
        convert hb using 1
        congr 1
        unfold distinctIndexMoment
        apply Finset.sum_congr
        · ext x
          simp
        · intro x hx
          rfl
      have hb' : |R e| ≤ |M 2| * N := by
        simpa only [Fintype.card_coe, he, hsquare] using hbRaw
      change |R e / (N : ℝ)| ≤ _
      rw [abs_div, abs_of_pos hnpos]
      exact (div_le_iff₀ hnpos).mpr hb'
    have hdiag (e : Finset α) : |∑ d, ∏ i ∈ e, f i d| ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ d, |∏ i ∈ e, f i d| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d : Fin N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.abs_prod]
          exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => hf i d)
        _ = _ := by simp
    have hrc (e : Finset α) (he : e.card = 2) : |r e - c e| ≤ |M 2| / N := by
      have heq : r e - c e = -(M 2 / (N : ℝ)^2 * ∑ d, ∏ i ∈ e, f i d) := by
        dsimp only [r, c, R, a]
        rw [SixthOrderTopPairingRefutation.subset_pair_formula zValue zWeight N f e he,
          Finset.prod_div_distrib, Finset.prod_const, he]
        change _ = -(scalarMoment zValue zWeight 2 /
          (N : ℝ)^2 * ∑ d, ∏ i ∈ e, f i d)
        dsimp only [M, scalarMoment]
        field_simp [hnne] <;> ring
      rw [heq, abs_neg, abs_mul, abs_div, abs_of_pos (pow_pos hnpos _)]
      calc
        _ ≤ (|M 2| / (N : ℝ)^2) * N :=
          mul_le_mul_of_nonneg_left (hdiag e) (by positivity)
        _ = _ := by field_simp [hnne] <;> ring
    have hcount : (((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing U)).card : ℝ) = gaussianPairingCount U.card := by
      rw [perfectPairingCount]
      simp only [gaussianPairingCount]
      split_ifs <;> simp
    have hpoly : |finitePairingPolynomial U r - finitePairingPolynomial U c| ≤
        gaussianPairingCount U.card * (U.card / 2 : ℕ) *
          (|M 2| / N) * B ^ (U.card / 2) := by
      unfold finitePairingPolynomial
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ P : Finset (Finset α) with IsPerfectPairing U P,
            |(∏ e ∈ P, r e) - ∏ e ∈ P, c e| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _P : Finset (Finset α) with IsPerfectPairing U _P,
            ((U.card / 2 : ℕ) : ℝ) * (|M 2| / N) * B ^ (U.card / 2) := by
          apply Finset.sum_le_sum
          intro P hP
          have hp := (Finset.mem_filter.mp hP).2
          have hcP : P.card = U.card / 2 := by rw [hp.card]; omega
          have hpert := scalar_product_perturbation (α := Finset α) P r c B (|M 2| / N)
            (le_max_left _ _) (by positivity)
            (fun e he => (hr e (hp.1.1 e he)).trans (le_max_right _ _))
            (fun e he => (hc e).trans (le_max_right _ _))
            (fun e he => hrc e (hp.1.1 e he))
          simpa only [hcP] using hpert
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcount]; ring
    have hmain : finitePairingPolynomial U c =
        gaussianPairingCount U.card * M 2 ^ (U.card / 2) * ∏ i ∈ U, a i := by
      rw [show c = (fun e => M 2 * ∏ i ∈ e, a i) from rfl,
        pairing_polynomial_scalar_rank_one U (M 2) a, hcount]
    have hnormalize : finitePairingPolynomial U R / Real.sqrt N ^ U.card =
        finitePairingPolynomial U r := by
      rw [← pairing_polynomial_normalize U R (Real.sqrt N)]
      simp only [hsquare]
      rfl
    have hlead := mixture_distinct_normalized_leading N zValue zWeight U hN hUN hU f hf
    change |(R U - finitePairingPolynomial U R) / Real.sqrt N ^ U.card -
      (M U.card - gaussianPairingCount U.card * M 2 ^ (U.card / 2)) *
        ∏ i ∈ U, a i| ≤ _
    have hid : (R U - finitePairingPolynomial U R) / Real.sqrt N ^ U.card -
        (M U.card - gaussianPairingCount U.card * M 2 ^ (U.card / 2)) *
          (∏ i ∈ U, a i) =
        (R U / Real.sqrt N ^ U.card - M U.card * ∏ i ∈ U, a i) -
          (finitePairingPolynomial U r - finitePairingPolynomial U c) := by
      rw [← hnormalize, hmain]
      ring
    rw [hid]
    calc
      _ ≤ |R U / Real.sqrt N ^ U.card - M U.card * ∏ i ∈ U, a i| +
          |finitePairingPolynomial U r - finitePairingPolynomial U c| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (R U / Real.sqrt N ^ U.card - M U.card * ∏ i ∈ U, a i)
            0 (finitePairingPolynomial U r - finitePairingPolynomial U c)
      _ ≤ (|M U.card| * (U.card.choose 2 : ℝ)) / N +
          gaussianPairingCount U.card * (U.card / 2 : ℕ) *
            (|M 2| / N) * B ^ (U.card / 2) := add_le_add hlead hpoly
      _ = _ := by dsimp only [mixtureLeadingConstant, M, B]; ring

  classical
  by_cases hU : U.Nonempty
  · exact mixture_uniform_leading_bound N zValue zWeight U hN hUN
      (Finset.card_pos.mpr hU) f hf
  · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    have hR0 : subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) f ∅ =
        scalarMoment zValue zWeight 0 := by
      simpa [subsetDistinctMoment, distinctIndexMoment, scalarMoment,
        Function.Injective] using
        mixture_character N zValue zWeight ∅
    have hclass (P : Finset (Finset α)) : IsPerfectPairing ∅ P ↔ P = ∅ := by
      constructor
      · intro hP
        apply Finset.card_eq_zero.mp
        have hc := hP.card
        simp only [Finset.card_empty] at hc
        omega
      · rintro rfl
        simp [IsPerfectPairing, IsPartialPairing, pairingSupport]
    have hW0 : finitePairingPolynomial (∅ : Finset α)
        (subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) f) = 1 := by
      simp [finitePairingPolynomial, hclass, Finset.sum_filter]
    simp [subsetPairingDefect, hR0, hW0, scalarDefect, scalarGaussian,
      mixtureLeadingConstant, gaussianPairingCount, Nat.doubleFactorial]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
