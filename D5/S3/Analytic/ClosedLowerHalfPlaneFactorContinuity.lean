/- GID: D5/S3/Analytic/ClosedLowerHalfPlaneFactorContinuity
   generality: G
   mirror-B: D5/B/S3/Analytic/ClosedLowerHalfPlaneFactorContinuity
   mirror-E: none(waiver:qualitative-polynomial-continuity)
   anchors: [mathlib/module/Mathlib.Topology.Sequences]
   utility: none
   digest: Closed-lower factors are continuous on arbitrary parameter spaces. -/

import D5.S3.Analytic.LowerHalfPlaneFactorContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity

open Polynomial Filter Topology Set Metric
open scoped ComplexConjugate
open D5.S3.Analytic.LowerHalfPlaneFactorContinuity
  (root_tuple continuous_product_coeff)
open D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
  (monic_root_bound_by_coefficient_sum)

/-- Monicity and the closed lower half-plane determine a factor of its
coefficient-conjugate product, including multiplicities at real roots. -/
theorem closed_lower_factor_unique (p q : ℂ[X]) (hp : p.Monic) (hq : q.Monic)
    (hlp : ∀ z, p.eval z = 0 → z.im ≤ 0)
    (hlq : ∀ z, q.eval z = 0 → z.im ≤ 0)
    (he : p * p.map (starRingEnd ℂ) = q * q.map (starRingEnd ℂ)) : p = q := by
  classical
  have hconj (f : ℂ[X]) (z : ℂ) :
      rootMultiplicity z (f.map (starRingEnd ℂ)) = rootMultiplicity (conj z) f := by
    simpa only [starRingEnd_apply, star_star] using
      (eq_rootMultiplicity_map (p := f) (starRingEnd ℂ).injective (conj z)).symm
  have hzero (f : ℂ[X]) (hf : ∀ z, f.eval z = 0 → z.im ≤ 0)
      (z : ℂ) (hz : 0 < z.im) : rootMultiplicity z f = 0 := by
    apply rootMultiplicity_eq_zero
    intro h
    exact (not_le_of_gt hz) (hf z h)
  have hmult (z : ℂ) : rootMultiplicity z p = rootMultiplicity z q := by
    have h := congrArg (rootMultiplicity z) he
    rw [rootMultiplicity_mul (mul_ne_zero hp.ne_zero (hp.map _).ne_zero),
      rootMultiplicity_mul (mul_ne_zero hq.ne_zero (hq.map _).ne_zero),
      hconj, hconj] at h
    rcases lt_trichotomy z.im 0 with hz | hz | hz
    · have hcz : 0 < (conj z).im := by simpa using neg_pos.mpr hz
      rw [hzero p hlp _ hcz, hzero q hlq _ hcz] at h
      simpa using h
    · rw [Complex.conj_eq_iff_im.mpr hz] at h
      omega
    · rw [hzero p hlp z hz, hzero q hlq z hz]
  have hr : p.roots = q.roots := by
    apply Multiset.ext.mpr
    intro z
    simpa only [Polynomial.count_roots] using hmult z
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp
      IsAlgClosed.card_roots_eq_natDegree,
    ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hq
      IsAlgClosed.card_roots_eq_natDegree, hr]

private theorem continuous_coeff_first_countable
    {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    (H B : A → ℂ[X]) (m : ℕ)
    (hmonic : ∀ a, (B a).Monic)
    (hdegree : ∀ a, (B a).natDegree = m)
    (hlower : ∀ a z, (B a).eval z = 0 → z.im ≤ 0)
    (hfactor : ∀ a, H a = B a * (B a).map (starRingEnd ℂ))
    (hc : ∀ k, Continuous (fun a => (H a).coeff k)) :
    ∀ k, Continuous (fun a => (B a).coeff k) := by
  classical
  have hHm (a : A) : (H a).Monic := by
    rw [hfactor a]
    exact (hmonic a).mul ((hmonic a).map _)
  have hHd (a : A) : (H a).natDegree = 2*m := by
    rw [hfactor a, Polynomial.natDegree_mul (hmonic a).ne_zero
      ((hmonic a).map (starRingEnd ℂ)).ne_zero, (hmonic a).natDegree_map, hdegree a]
    omega
  have heval (z : ℂ) : Continuous (fun a => (H a).eval z) := by
    have he (a : A) : (H a).eval z =
        ∑ k ∈ Finset.range (2*m+1), (H a).coeff k * z^k := by
      rw [Polynomial.eval_eq_sum_range, hHd a]
    simp_rw [he]
    exact continuous_finsetSum _ fun k _ => (hc k).mul continuous_const
  let P : (Fin m → ℂ) → ℂ[X] := fun r => ∏ i, (X - C (r i))
  have hPc (k : ℕ) : Continuous (fun r => (P r).coeff k) := by
    refine continuous_product_coeff Finset.univ
      (fun (i : Fin m) (r : Fin m → ℂ) => X - C (r i)) ?_ k
    intro i hi k
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> fun_prop
  have hPe (z : ℂ) : Continuous
      (fun r => (P r * (P r).map (starRingEnd ℂ)).eval z) := by
    simp only [P, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    fun_prop
  have hPm (r : Fin m → ℂ) : (P r).Monic := monic_prod_X_sub_C r Finset.univ
  intro k
  apply continuous_iff_seqContinuous.mpr
  intro u a hu
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  let v : ℕ → A := fun n => u (ns n)
  have hv : Tendsto v atTop (𝓝 a) := hu.comp hns
  choose r hr using fun n => root_tuple (B (v n)) m (hmonic _) (hdegree _)
  have hroot (n : ℕ) (i : Fin m) : (B (v n)).eval (r n i) = 0 := by
    rw [hr n]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  let S : A → ℝ := fun a => ∑ j ∈ Finset.range (2*m), ‖(H a).coeff j‖
  have hS : Continuous S :=
    continuous_finsetSum _ fun j _ => (hc j).norm
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _
    (hS.continuousAt.tendsto.comp hv)).exists_norm_le
  let R : ℝ := max C 0 + 1
  have hbound (n : ℕ) (i : Fin m) : ‖r n i‖ ≤ R := by
    have hz : (H (v n)).eval (r n i) = 0 := by
      rw [hfactor, Polynomial.eval_mul, hroot, zero_mul]
    have hb := monic_root_bound_by_coefficient_sum (H (v n)) (hHm _) (r n i) hz
    rw [hHd] at hb
    have hs := hC _ (Set.mem_range_self n)
    simp only [Function.comp_apply, Real.norm_eq_abs] at hs
    change ‖r n i‖ ≤ S (v n) + 1 at hb
    exact hb.trans (by dsimp [R]; linarith [le_max_left C 0, le_abs_self (S (v n))])
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin m => closedBall (0 : ℂ) R)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  obtain ⟨r₀, _, φ, hφ, ht⟩ := hK.tendsto_subseq (x := r) (by
    intro n i hi
    exact mem_closedBall_zero_iff.mpr (hbound n i))
  have hsplit : H a = P r₀ * (P r₀).map (starRingEnd ℂ) := by
    apply Polynomial.funext
    intro z
    have hleft := (heval z).continuousAt.tendsto.comp (hv.comp hφ.tendsto_atTop)
    have hright := (hPe z).continuousAt.tendsto.comp ht
    apply tendsto_nhds_unique hleft
    convert hright using 1
    ext n
    dsimp [Function.comp_def]
    rw [hfactor, hr]
  have hrlower (i : Fin m) : (r₀ i).im ≤ 0 := by
    have hti : Tendsto (fun n => r (φ n) i) atTop (𝓝 (r₀ i)) :=
      (continuous_apply i).continuousAt.tendsto.comp ht
    exact le_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hti)
      (Filter.Eventually.of_forall fun n => hlower _ _ (hroot (φ n) i))
  have hPlower : ∀ z, (P r₀).eval z = 0 → z.im ≤ 0 := by
    intro z hz
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hz
    obtain ⟨i, hi⟩ := hz
    exact (sub_eq_zero.mp hi) ▸ hrlower i
  have heq : P r₀ = B a := closed_lower_factor_unique (P r₀) (B a)
    (hPm _) (hmonic _) hPlower (hlower a) (hsplit.symm.trans (hfactor a))
  refine ⟨φ, ?_⟩
  have hlim := (hPc k).continuousAt.tendsto.comp ht
  rw [heq] at hlim
  convert hlim using 1
  ext n
  change (B (v (φ n))).coeff k = (P (r (φ n))).coeff k
  rw [hr]

/-- Coefficient continuity of supplied fixed-degree monic closed-lower factors.
The parameter space is arbitrary; real-axis collisions and degree zero are included. -/
theorem continuous_coeff_of_monic_closed_lower_factor
    {A : Type*} [TopologicalSpace A]
    (H B : A → ℂ[X]) (m : ℕ)
    (hmonic : ∀ a, (B a).Monic)
    (hdegree : ∀ a, (B a).natDegree = m)
    (hlower : ∀ a z, (B a).eval z = 0 → z.im ≤ 0)
    (hfactor : ∀ a, H a = B a * (B a).map (starRingEnd ℂ))
    (hc : ∀ k, Continuous (fun a => (H a).coeff k)) :
    ∀ k, Continuous (fun a => (B a).coeff k) := by
  classical
  have hHd (a : A) : (H a).natDegree = 2*m := by
    rw [hfactor a, Polynomial.natDegree_mul (hmonic a).ne_zero
      ((hmonic a).map (starRingEnd ℂ)).ne_zero, (hmonic a).natDegree_map, hdegree a]
    omega
  let c : A → (Fin (2*m+1) → ℂ) := fun a i => (H a).coeff i
  let Y := Set.range c
  let s : Y → A := fun y => Classical.choose y.property
  have hs (y : Y) : c (s y) = y.val := Classical.choose_spec y.property
  have hsc : ∀ k, Continuous (fun y : Y => (H (s y)).coeff k) := by
    intro k
    by_cases hk : k < 2*m+1
    · have he (y : Y) : (H (s y)).coeff k = y.val ⟨k,hk⟩ :=
        congrFun (hs y) ⟨k,hk⟩
      simp_rw [he]
      exact (continuous_apply (⟨k,hk⟩ : Fin (2*m+1))).comp continuous_subtype_val
    · have he (y : Y) : (H (s y)).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hHd]; omega)
      simp_rw [he]
      exact continuous_const
  have hbc := continuous_coeff_first_countable (fun y : Y => H (s y))
    (fun y : Y => B (s y)) m (fun y => hmonic (s y)) (fun y => hdegree (s y))
    (fun y => hlower (s y)) (fun y => hfactor (s y)) hsc
  let f : A → Y := fun a => ⟨c a, Set.mem_range_self a⟩
  have hf : Continuous f :=
    (continuous_pi fun i : Fin (2*m+1) => hc i.val).subtype_mk (fun a => Set.mem_range_self a)
  have hsame (a : A) : B (s (f a)) = B a := by
    apply closed_lower_factor_unique _ _ (hmonic _) (hmonic _) (hlower _) (hlower _)
    rw [← hfactor, ← hfactor]
    apply Polynomial.ext
    intro k
    by_cases hk : k < 2*m+1
    · exact congrFun (hs (f a)) ⟨k,hk⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hHd]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [hHd]; omega)]
  intro k
  exact ((hbc k).comp hf).congr (fun a => congrArg (fun p : ℂ[X] => p.coeff k) (hsame a))

#print axioms closed_lower_factor_unique
#print axioms continuous_coeff_of_monic_closed_lower_factor

end D5.S3.Analytic.ClosedLowerHalfPlaneFactorContinuity
