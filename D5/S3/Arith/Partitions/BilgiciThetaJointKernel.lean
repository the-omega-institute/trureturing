/- GID: D5/S3/Arith/Partitions/BilgiciThetaJointKernel
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaJointKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The joint kernel in degree seven and weight eleven is the cubic multiplication range. -/

import D5.S3.Arith.Partitions.BilgiciThetaStraightening
import D5.S3.Arith.Partitions.BilgiciThetaDetectors
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The joint kernel in degree seven and weight eleven is the cubic multiplication range. -/

open D5.S3.Arith.Partitions.BilgiciThetaQuartic MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

private theorem TS : T S_Z = S_Z := by
  have hnorm : normalize (sSparse) =
      normalize ((scale 1 (orbitWordSparse 1 [1,7,8])) ++
        (scale (-1) (orbitWordSparse 1 [2,3,5])) ++
        (scale 1 (orbitWordSparse 1 [4,6,9]))) := by decide
  have hp := congrArg denote hnorm
  rw [denote_normalize, denote_normalize, denote_sSparse] at hp
  simp only [denote_append, denote_scale, denote_orbitWordSparse,
    map_one, one_mul] at hp
  have hone (f : R) : Tpow 1 f = T f := rfl
  rw [hone, hone, hone] at hp
  rw [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg] at hp
  have hs : S_Z = monomialWord [1,7,8] - monomialWord [2,3,5] + monomialWord [4,6,9] := by
    change S_Z = Z 1 * (Z 7 * (Z 8 * 1)) - Z 2 * (Z 3 * (Z 5 * 1)) +
      Z 4 * (Z 6 * (Z 9 * 1))
    simp only [S_Z, mul_one, mul_assoc]
  calc
    T S_Z = T (monomialWord [1,7,8]) - T (monomialWord [2,3,5]) + T (monomialWord [4,6,9]) := by
      rw [hs, map_add, map_sub]
    _ = S_Z := hp.symm

private theorem eigengrade_of_projected (m : List ℤ) {d : ℕ} {n : K} (h : P (monomialWord m) ∈ grade d n) :
    q (P (monomialWord m)) ∈ eigengrade d n :=
  eigengrade_mem.mpr ⟨⟨_, h, rfl⟩, by rw [Tbar_q, T_P, map_smul]⟩

theorem u_mem : q u ∈ eigengrade 7 11 := eigengrade_of_projected _ (grade_mem.mpr u_grades)
private theorem v_mem : q v ∈ eigengrade 7 11 := eigengrade_of_projected _ (grade_mem.mpr v_grades)
private theorem h₁_mem : q h₁ ∈ eigengrade 4 9 := eigengrade_of_projected _ (grade_mem.mpr h₁_grades)
private theorem h₂_mem : q h₂ ∈ eigengrade 4 9 := eigengrade_of_projected _ (grade_mem.mpr h₂_grades)

noncomputable def mulS : A →ₗ[K] A := LinearMap.mul K A (q S_Z)

private theorem mulS_mem {p : A} (hp : p ∈ eigengrade 4 9) : mulS p ∈ eigengrade 7 11 := by
  obtain ⟨⟨f, hf, rfl⟩, he⟩ := eigengrade_mem.mp hp
  obtain ⟨hd, hw⟩ := grade_mem.mp hf
  change q S_Z * q f ∈ eigengrade 7 11
  apply eigengrade_mem.mpr
  refine ⟨⟨S_Z * f, grade_mem.mpr ⟨S_grades.1.mul hd, S_grades.2.mul hw⟩, map_mul q _ _⟩, ?_⟩
  rw [map_mul, Tbar_q, TS, he, mul_smul_comm]

private noncomputable def comparison : Fin 4 → A := ![q u, q v, mulS (q h₁), mulS (q h₂)]

theorem ell_mulS (n : ℕ) (hn : n < 55) (f : R) :
    ell n hn (mulS (q f)) = ellR n (S_Z * f) := by
  change ell n hn (q S_Z * q f) = _
  rw [← map_mul, ell_q]

theorem cubic_trace_coordinates (z : A) (a b : K)
    (h : z = a • mulS (q h₁) + b • mulS (q h₂)) :
    a = (9 : K) * ell 30 (by decide) z ∧
      b = ell 49 (by decide) z - (9 : K) * a := by
  have h₁trace : ellR 30 (S_Z * h₁) = 17 ∧ ellR 49 (S_Z * h₁) = 9 := by
    rw [h₁, ← spProject_denote, ← denote_sSparse, ← denote_rawMul]
    rw [ellR_sparse, ellR_sparse]
    exact ⟨by decide, by decide⟩
  have h₂trace : ellR 30 (S_Z * h₂) = 0 ∧ ellR 49 (S_Z * h₂) = 1 := by
    rw [h₂, ← spProject_denote, ← denote_sSparse, ← denote_rawMul]
    rw [ellR_sparse, ellR_sparse]
    exact ⟨by decide, by decide⟩
  have h30 := congrArg (ell 30 (by decide)) h
  simp only [map_add, map_smul, ell_mulS, h₁trace.1,
    h₂trace.1, smul_eq_mul, mul_zero, add_zero] at h30
  have h49 := congrArg (ell 49 (by decide)) h
  simp only [map_add, map_smul, ell_mulS, h₁trace.2,
    h₂trace.2, smul_eq_mul, mul_one] at h49
  constructor
  · rw [h30, mul_left_comm, show (9 : K) * 17 = 1 by decide, mul_one]
  · rw [h49]
    ring

private theorem test_columns_zero (a b c d : K)
    (h : tests (a • q u + b • q v + c • mulS (q h₁) + d • mulS (q h₂)) = 0) :
    a = 0 ∧ b = 0 := by
  have h₁zero : tests (mulS (q h₁)) = 0 := tests_mul_S_Z _
  have h₂zero : tests (mulS (q h₂)) = 0 := tests_mul_S_Z _
  simp only [map_add, map_smul, quotient_u_tests, quotient_v_tests,
    h₁zero, h₂zero, smul_zero, add_zero] at h
  have hfirst := congrArg Prod.fst h
  change a * (17 : K) + b * 0 = 0 at hfirst
  rw [mul_zero, add_zero] at hfirst
  have ha : a = 0 := (mul_eq_zero.mp hfirst).resolve_right (by decide)
  rw [ha, zero_smul, zero_add] at h
  exact ⟨ha, by simpa using congrArg Prod.snd h⟩

private theorem comparison_independent : LinearIndependent K comparison := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_four] at hc
  change c 0 • q u + c 1 • q v + c 2 • mulS (q h₁) + c 3 • mulS (q h₂) = 0 at hc
  have htests := congrArg tests hc
  rw [map_zero] at htests
  obtain ⟨h0, h1⟩ := test_columns_zero _ _ _ _ htests
  rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add] at hc
  obtain ⟨h2, h3⟩ := cubic_trace_coordinates 0 _ _ hc.symm
  simp only [map_zero, mul_zero] at h2
  simp only [h2, map_zero, mul_zero, sub_zero] at h3
  intro i
  fin_cases i <;> assumption

open D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening

private noncomputable def rootFamily : Fin 4 → A :=
  ![q (P (word paper1)), q (P (word paper2)),
    q (P (word paper3)), q (P (word paper4))]

private theorem requestedSpan_family : requestedSpan = Submodule.span K (Set.range rootFamily) := by
  unfold requestedSpan
  apply congrArg (Submodule.span K)
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [rootFamily]

private theorem eigengrade_le_requestedSpan : eigengrade 7 11 ≤ requestedSpan := by
  rw [eigengrade_exact (by decide : (2 : K)*11=14*(7 : ℕ))]
  rintro _ ⟨f, hf, rfl⟩
  change q (P f) ∈ requestedSpan
  rw [← support_sum_monomial_coeff f, map_sum, map_sum]
  apply Submodule.sum_mem _
  intro e he
  obtain ⟨m, _, hlen, hw, hm⟩ := support_word hf he
  rw [hm, map_smul, map_smul]
  exact requestedSpan.smul_mem _ (centered_degree_seven_span m hlen
    ((centered_zero_iff m 7 11 hlen (by decide)).mpr hw))

private theorem comparison_span : Submodule.span K (Set.range comparison) = eigengrade 7 11 := by
  have hle : Submodule.span K (Set.range comparison) ≤ eigengrade 7 11 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact u_mem
    · exact v_mem
    · exact mulS_mem h₁_mem
    · exact mulS_mem h₂_mem
  have hupper : eigengrade 7 11 ≤ Submodule.span K (Set.range rootFamily) :=
    requestedSpan_family ▸ eigengrade_le_requestedSpan
  let : FiniteDimensional K (Submodule.span K (Set.range rootFamily)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range rootFamily)
  let : FiniteDimensional K (eigengrade 7 11) :=
    FiniteDimensional.of_injective (Submodule.inclusion hupper) (Submodule.inclusion_injective hupper)
  have hrank : Module.finrank K (eigengrade 7 11) ≤ 4 := by
    have hcard : Module.finrank K (Submodule.span K (Set.range rootFamily)) ≤ 4 := by
      simpa [Set.finrank] using (finrank_range_le_card (R := K) rootFamily)
    exact (Submodule.finrank_mono hupper).trans hcard
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_span_eq_card comparison_independent, Fintype.card_fin]
  exact hrank

theorem kernel_coordinates {x : A} (hx : x ∈ eigengrade 7 11) (ht : tests x = 0) :
    ∃ a b : K, a • mulS (q h₁) + b • mulS (q h₂) = x := by
  have hm : x ∈ Submodule.span K (Set.range comparison) := comparison_span.symm ▸ hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
  simp only [Fin.sum_univ_four] at hc
  change c 0 • q u + c 1 • q v + c 2 • mulS (q h₁) + c 3 • mulS (q h₂) = x at hc
  have htests := congrArg tests hc
  rw [ht] at htests
  obtain ⟨h0, h1⟩ := test_columns_zero _ _ _ _ htests
  rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add] at hc
  exact ⟨c 2, c 3, hc⟩

theorem joint_kernel_membership {x : A} (hx : x ∈ eigengrade 7 11) :
    tests x = 0 ↔ ∃ y ∈ eigengrade 4 9, q S_Z * y = x := by
  constructor
  · intro ht
    obtain ⟨a, b, hab⟩ := kernel_coordinates hx ht
    refine ⟨a • q h₁ + b • q h₂, (eigengrade 4 9).add_mem
      ((eigengrade 4 9).smul_mem _ h₁_mem) ((eigengrade 4 9).smul_mem _ h₂_mem), ?_⟩
    change mulS (a • q h₁ + b • q h₂) = x
    simpa only [map_add, map_smul] using hab
  · rintro ⟨y, _, rfl⟩
    exact tests_mul_S_Z y

noncomputable def mulSZComponent : eigengrade 4 9 →ₗ[K] eigengrade 7 11 :=
  (mulS.comp (eigengrade 4 9).subtype).codRestrict _ (fun y => mulS_mem y.property)

theorem joint_kernel :
    LinearMap.ker (tests.comp (eigengrade 7 11).subtype) = LinearMap.range mulSZComponent := by
  ext x
  change tests x.val = 0 ↔ ∃ y : eigengrade 4 9, mulSZComponent y = x
  rw [joint_kernel_membership x.property]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨⟨y,hy⟩, Subtype.ext he⟩
  · rintro ⟨y, he⟩
    exact ⟨y.val, y.property, congrArg Subtype.val he⟩

theorem u_not_in_range :
    (⟨q u, u_mem⟩ : eigengrade 7 11) ∉ LinearMap.range mulSZComponent := by
  rw [← joint_kernel]
  intro h
  have hu : tests (q u) = 0 := h
  have h17 := congrArg Prod.fst (quotient_u_tests.symm.trans hu)
  exact (show (17 : K) ≠ 0 by decide) h17


end D5.S3.Arith.Partitions.BilgiciThetaStructural
