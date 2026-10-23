/- GID: D5/S3/Analytic/LowerHalfPlaneFactorContinuity
   generality: G
   mirror-B: D5/B/S3/Analytic/LowerHalfPlaneFactorContinuity
   mirror-E: none(waiver:qualitative-polynomial-continuity)
   anchors: [mathlib/module/Mathlib.Topology.Sequences]
   utility: none
   digest: Monic lower half-plane factors vary continuously through root collisions. -/

import D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
import Mathlib.Data.Multiset.Fintype
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.LowerHalfPlaneFactorContinuity

open Polynomial Filter Topology Set Metric
open scoped ComplexConjugate
open D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
  (monic_root_bound_by_coefficient_sum)

theorem root_tuple (p : ℂ[X]) (m : ℕ) (hp : p.Monic)
    (hd : p.natDegree = m) :
    ∃ r : Fin m → ℂ, p = ∏ i, (X - C (r i)) := by
  classical
  let e : p.roots ≃ Fin m := Fintype.equivFinOfCardEq (by
    rw [Multiset.card_coe, IsAlgClosed.card_roots_eq_natDegree, hd])
  refine ⟨fun i => (e.symm i : ℂ), ?_⟩
  calc
    p = (p.roots.map fun z => X - C z).prod :=
      (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp
        IsAlgClosed.card_roots_eq_natDegree).symm
    _ = ∏ z : p.roots, (X - C (z : ℂ)) := by
      rw [← Multiset.map_univ]
      rfl
    _ = ∏ i : Fin m, (X - C (e.symm i : ℂ)) :=
      (e.symm.prod_comp (fun z : p.roots => X - C (z : ℂ))).symm

private theorem lower_coprime_conjugate (p q : ℂ[X])
    (hp : ∀ z, p.eval z = 0 → z.im < 0)
    (hq : ∀ z, q.eval z = 0 → z.im < 0) :
    IsCoprime p (q.map (starRingEnd ℂ)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ p _).2
  intro z
  simp only [aeval_def]
  by_cases hz : p.eval z = 0
  · right
    intro hqz
    have he := Polynomial.eval_map_apply (p := q) (starRingEnd ℂ) (conj z)
    simp only [starRingEnd_apply, star_star] at he
    have hzq : q.eval (conj z) = 0 := by
      apply (starRingEnd ℂ).injective
      simpa only [map_zero, starRingEnd_apply] using he.symm.trans hqz
    have h1 := hp z hz
    have h2 := hq (conj z) hzq
    simp only [Complex.conj_im] at h2
    linarith
  · exact Or.inl hz

private theorem lower_factor_unique (p q : ℂ[X]) (hp : p.Monic) (hq : q.Monic)
    (hd : q.natDegree ≤ p.natDegree)
    (hlp : ∀ z, p.eval z = 0 → z.im < 0)
    (hlq : ∀ z, q.eval z = 0 → z.im < 0)
    (he : p * p.map (starRingEnd ℂ) = q * q.map (starRingEnd ℂ)) : p = q := by
  have hdvd : p ∣ q * q.map (starRingEnd ℂ) := by
    rw [← he]
    exact dvd_mul_right _ _
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp hq
    ((lower_coprime_conjugate p q hlp hlq).dvd_of_dvd_mul_right hdvd) hd).symm

theorem continuous_product_coeff {A ι : Type*} [TopologicalSpace A]
    (s : Finset ι) (p : ι → A → ℂ[X])
    (hc : ∀ i ∈ s, ∀ k, Continuous (fun a => (p i a).coeff k)) :
    ∀ k, Continuous (fun a => (∏ i ∈ s, p i a).coeff k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k
    simpa using (continuous_const : Continuous (fun _ : A => (1 : ℂ[X]).coeff k))
  | @insert i s hi ih =>
    intro k
    simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
    apply continuous_finsetSum
    intro j hj
    exact (hc i (Finset.mem_insert_self _ _) j.1).mul
      (ih (fun i hi => hc i (Finset.mem_insert_of_mem hi)) j.2)

/-- Supplied monic factors with all roots strictly below the real axis depend
continuously on the coefficients of their conjugate product. Colliding roots
and degree zero are included. The parameter space need not be Hausdorff. -/
theorem continuous_coeff_of_monic_lower_factor
    {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    (H B : A → ℂ[X]) (m : ℕ)
    (hmonic : ∀ a, (B a).Monic)
    (hdegree : ∀ a, (B a).natDegree = m)
    (hlower : ∀ a z, (B a).eval z = 0 → z.im < 0)
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
  have hPd (r : Fin m → ℂ) : (P r).natDegree = m := by
    dsimp [P]
    rw [Polynomial.natDegree_prod _ _ (fun i _ => (monic_X_sub_C (r i)).ne_zero)]
    simp
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
  have hrlower (i : Fin m) : (r₀ i).im < 0 := by
    have hti : Tendsto (fun n => r (φ n) i) atTop (𝓝 (r₀ i)) :=
      (continuous_apply i).continuousAt.tendsto.comp ht
    have hle : (r₀ i).im ≤ 0 :=
      le_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hti)
        (Filter.Eventually.of_forall fun n => (hlower _ _ (hroot (φ n) i)).le)
    apply lt_of_le_of_ne hle
    intro him
    have hpz : (P r₀).eval (r₀ i) = 0 := by
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    have hHz : (H a).eval (r₀ i) = 0 := by
      rw [hsplit, Polynomial.eval_mul, hpz, zero_mul]
    rw [hfactor, Polynomial.eval_mul] at hHz
    have hBz : (B a).eval (r₀ i) = 0 := by
      rcases mul_eq_zero.mp hHz with h | h
      · exact h
      · have he := Polynomial.eval_map_apply (p := B a) (starRingEnd ℂ) (r₀ i)
        rw [Complex.conj_eq_iff_im.mpr him] at he
        apply (starRingEnd ℂ).injective
        simpa only [map_zero] using he.symm.trans h
    have := hlower a (r₀ i) hBz
    linarith
  have hPlower : ∀ z, (P r₀).eval z = 0 → z.im < 0 := by
    intro z hz
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hz
    obtain ⟨i, hi⟩ := hz
    exact (sub_eq_zero.mp hi) ▸ hrlower i
  have heq : P r₀ = B a := lower_factor_unique (P r₀) (B a) (hPm _) (hmonic _)
    (by rw [hdegree, hPd]) hPlower (hlower a) (hsplit.symm.trans (hfactor a))
  refine ⟨φ, ?_⟩
  have hlim := (hPc k).continuousAt.tendsto.comp ht
  rw [heq] at hlim
  convert hlim using 1
  ext n
  change (B (v (φ n))).coeff k = (P (r (φ n))).coeff k
  rw [hr]

#print axioms continuous_coeff_of_monic_lower_factor

end D5.S3.Analytic.LowerHalfPlaneFactorContinuity
