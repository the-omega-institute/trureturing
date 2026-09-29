/- GID: D5/S3/Quantum/Information/FiniteCalibrationControl
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FiniteCalibrationControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational controls realize exactly prescribed finite calibration jets. -/

import Mathlib

open Set Filter Polynomial
open scoped Topology BigOperators

namespace D5.S3.Quantum.Information.FiniteCalibrationControl
noncomputable section

def L (a : ℝ) := 1 - a
def lam (a δ : ℝ) := L a - δ
def radius (a δ p : ℝ) := Real.sqrt (a / lam a δ) * Real.sqrt ((1-p)/p)
def gamma (a δ : ℝ) := lam a δ / (2*δ)
def center (a δ : ℝ) := lam a δ / L a
def energy (a δ s : ℝ) := s^2 + (gamma a δ)^2 * (s+s⁻¹-2)^2
def beta (p : ℝ) := 1/(2*p*(1-p))
def hermite (S : Finset ℝ) : ℝ[X] :=
  1 + ∑ i ∈ S, C (beta i) * (X-C i) * (Lagrange.basis S id i)^2

/-- A positive rational control with global strict feasibility and exactly the prescribed jets. -/
def FullControl (a δ : ℝ) (S : Finset ℝ) (N D : ℝ[X]) : Prop :=
  N.natDegree ≤ 2*S.card ∧ D.natDegree ≤ 2*S.card ∧
  (∀ p : ℝ, 0 < D.eval p) ∧
  (∀ p ∈ Icc a 1, 0 < N.eval p / D.eval p ∧
    (radius a δ p)^2 * energy a δ (N.eval p / D.eval p) < 1) ∧
  AnalyticOnNhd ℝ (fun p => N.eval p / D.eval p) (Ioo a 1) ∧
  (∀ p ∈ Ioo a 1, ((N.eval p / D.eval p = 1 ∧
    deriv (fun x => N.eval x / D.eval x) p = beta p) ↔ p ∈ S)) ∧
  (S = ∅ → ∀ p, N.eval p / D.eval p = center a δ)

/-- Every finite set above the fixed threshold is the complete calibration set of a
strictly feasible rational control, with numerator and denominator degree at most twice
the number of nodes. The empty set is realized by the constant center. -/
theorem result (a δ : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hδ : 0 < δ) (hδL : δ < (1-a)/4) (_hδa : δ < (1-a^2)/16)
    (S : Finset ℝ) (hS : ∀ i ∈ S, a/(1-δ) < i ∧ i < 1) :
    ∃ N D : ℝ[X], FullControl a δ S N D := by
  classical
  have hL : 0 < L a := sub_pos.mpr ha1
  have hlam : 0 < lam a δ := by unfold lam L; linarith
  have hδ1 : 0 < 1-δ := by unfold L at hL; linarith
  have hc : 0 < center a δ := div_pos hlam hL
  have hc1 : center a δ < 1 := by
    rw [center, div_lt_one hL]; unfold lam; linarith
  have hc34 : (3:ℝ)/4 < center a δ := by
    rw [center, lt_div_iff₀ hL]; unfold lam L; linarith
  have hnodes : ∀ i ∈ S, a < i ∧ i < 1 := by
    intro i hi
    have hh := (hS i hi).1
    have hai : a < a/(1-δ) := by
      rw [lt_div_iff₀ hδ1]; nlinarith
    exact ⟨hai.trans hh, (hS i hi).2⟩
  have hbeta : ∀ i ∈ S, 0 < beta i := by
    intro i hi
    have hh := hnodes i hi
    exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (ha.trans hh.1))
      (sub_pos.mpr hh.2))
  have hradius : ∀ p ∈ Icc a 1,
      (radius a δ p)^2 = a / lam a δ * ((1-p)/p) := by
    intro p hp
    unfold radius
    rw [mul_pow, Real.sq_sqrt (le_of_lt (div_pos ha hlam)),
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hp.2) (le_of_lt (ha.trans_le hp.1)))]
  have hrbound : ∀ p ∈ Icc a 1, (radius a δ p)^2 ≤ 1 / center a δ := by
    intro p hp
    rw [hradius p hp]
    have hp0 : 0 < p := ha.trans_le hp.1
    have hcEq : 1 / center a δ = L a / lam a δ := by unfold center; field_simp
    rw [hcEq]
    calc
      a / lam a δ * ((1-p)/p) = (a*(1-p)/p) / lam a δ := by ring
      _ ≤ L a / lam a δ := by
        apply (div_le_div_iff_of_pos_right hlam).mpr
        apply (div_le_iff₀ hp0).mpr
        unfold L
        nlinarith [hp.1]
  have hec : energy a δ (center a δ) =
      (center a δ)^2 + (1-center a δ)^2/4 := by
    unfold energy gamma center
    field_simp [ne_of_gt hL, ne_of_gt hlam, ne_of_gt hδ]
    unfold lam
    ring
  have hcenter : ∀ p ∈ Icc a 1,
      (radius a δ p)^2 * energy a δ (center a δ) < 1 := by
    intro p hp
    have heg : 0 ≤ energy a δ (center a δ) := by
      unfold energy; positivity
    calc
      _ ≤ (1 / center a δ) * energy a δ (center a δ) :=
        mul_le_mul_of_nonneg_right (hrbound p hp) heg
      _ < 1 := by
        rw [hec, one_div_mul_eq_div, div_lt_one hc]
        nlinarith
  have henergyconv : ConvexOn ℝ (Ioi 0) (energy a δ) := by
    have hv : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x+x⁻¹-2) := by
      have hi : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x⁻¹) := by
        simpa using (convexOn_zpow (-1 : ℤ) : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x^(-1 : ℤ)))
      simpa only [Pi.add_apply, id_eq, sub_eq_add_neg] using!
        ((convexOn_id (convex_Ioi (0:ℝ))).add hi).add (convexOn_const (-2) (convex_Ioi (0:ℝ)))
    have hv0 : ∀ ⦃x : ℝ⦄, x ∈ Ioi 0 → 0 ≤ x+x⁻¹-2 := by
      intro x hx
      have hx0 : 0 < x := hx
      have hh := sq_nonneg (x-1)
      have hinv : x*x⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hx0)
      nlinarith
    have hs := hv.pow hv0 2
    have hsq := (convexOn_pow (𝕜 := ℝ) 2).subset Ioi_subset_Ici_self (convex_Ioi (0:ℝ))
    simpa only [energy, Pi.pow_apply, Pi.add_apply, smul_eq_mul] using! hsq.add (hs.smul (sq_nonneg (gamma a δ)))
  have henergycont : ∀ s : ℝ, 0 < s → ContinuousAt (energy a δ) s := by
    intro s hs
    unfold energy
    fun_prop (disch := exact ne_of_gt hs)
  let P : ℝ[X] := Lagrange.nodal S id
  let H : ℝ[X] := hermite S
  let c : ℝ := center a δ
  let f : ℝ → ℝ → ℝ := fun k p => (H.eval p + k*c*(P.eval p)^2)/(1+k*(P.eval p)^2)
  have hinj : Set.InjOn (id : ℝ → ℝ) ↑S := Function.injective_id.injOn
  have hbself : ∀ i ∈ S, (Lagrange.basis S id i).eval i = 1 := by
    intro i hi
    exact Lagrange.eval_basis_self hinj hi
  have hbzero : ∀ i j : ℝ, i ∈ S → j ≠ i → (Lagrange.basis S id j).eval i = 0 := by
    intro i j hi hji
    exact Lagrange.eval_basis_of_ne (v := id) hji hi
  have hPnode : ∀ i ∈ S, P.eval i = 0 := by
    intro i hi
    exact Lagrange.eval_nodal_at_node (v := id) hi
  have hPoff : ∀ p ∉ S, P.eval p ≠ 0 := by
    intro p hp
    exact Lagrange.eval_nodal_not_at_node (fun i hi hpi => hp (hpi ▸ hi))
  have hHnode : ∀ i ∈ S, H.eval i = 1 := by
    intro i hi
    simp only [H, hermite, eval_add, eval_one, eval_finsetSum, eval_mul, eval_C,
      eval_sub, eval_X, eval_pow, add_eq_left]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · simp [hbzero i j hi hji]
  have hHderiv : ∀ i ∈ S, HasDerivAt (fun p => H.eval p) (beta i) i := by
    intro i hi
    apply (H.hasDerivAt i).congr_deriv
    simp only [H, hermite, derivative_add, derivative_one, derivative_sum,
      derivative_mul, derivative_C, derivative_sub, derivative_X, derivative_pow,
      eval_add, eval_mul, eval_C, eval_sub, eval_X, eval_pow, eval_finsetSum,
      zero_mul, zero_add, sub_zero, mul_one]
    rw [Finset.sum_eq_single i]
    · simp [hbself i hi]
    · intro j hj hji
      simp [hbzero i j hi hji]
    · exact fun h => False.elim (h hi)
  have hden : ∀ k : ℝ, 0 ≤ k → ∀ p : ℝ, 0 < 1+k*(P.eval p)^2 := by
    intro k hk p
    positivity
  have hfcont : ∀ k : ℝ, 0 ≤ k → Continuous (f k) := by
    intro k hk
    exact (H.continuous.add ((continuous_const.mul continuous_const).mul
      (P.continuous.pow 2))).div (continuous_const.add (continuous_const.mul
      (P.continuous.pow 2))) (fun p => ne_of_gt (hden k hk p))
  have hfnode : ∀ k i : ℝ, i ∈ S → f k i = 1 := by
    intro k i hi
    simp [f, hPnode i hi, hHnode i hi]
  have hfjet : ∀ k i : ℝ, i ∈ S → HasDerivAt (f k) (beta i) i := by
    intro k i hi
    have hP2 := (P.hasDerivAt i).pow 2
    have hh := ((hHderiv i hi).add (hP2.const_mul (k*c))).div
      ((hP2.const_mul k).const_add 1) (ne_of_gt (by simp [hPnode i hi] : 0 < 1+k*(P.eval i)^2))
    simpa [f, hPnode i hi, hHnode i hi] using! hh
  have hrcont : ∀ p : ℝ, 0 < p → ContinuousAt (fun x => (radius a δ x)^2) p := by
    intro p hp
    unfold radius
    fun_prop (disch := exact ne_of_gt hp)
  have hrnode : ∀ i ∈ S, (radius a δ i)^2 < 1 := by
    intro i hi
    have hi0 : 0 < i := ha.trans (hnodes i hi).1
    rw [hradius i ⟨(hnodes i hi).1.le, (hnodes i hi).2.le⟩]
    have hh := (div_lt_iff₀ hδ1).mp (hS i hi).1
    calc
      a / lam a δ * ((1-i)/i) = a*(1-i)/(lam a δ*i) := by ring
      _ < 1 := by
        rw [div_lt_one (mul_pos hlam hi0)]
        unfold lam L
        nlinarith
  have hmix : ∀ p x y t : ℝ, 0 < x → 0 < y →
      (radius a δ p)^2*energy a δ x < 1 →
      (radius a δ p)^2*energy a δ y < 1 →
      0 < t → t ≤ 1 →
      0 < t*x+(1-t)*y ∧
      (radius a δ p)^2*energy a δ (t*x+(1-t)*y) < 1 := by
    intro p x y t hx hy hex hey ht ht1
    have hnt : 0 ≤ 1-t := sub_nonneg.mpr ht1
    have hcv := henergyconv.2 hx hy ht.le hnt (by ring : t+(1-t)=1)
    simp only [smul_eq_mul] at hcv
    have hmul := mul_le_mul_of_nonneg_left hcv (sq_nonneg (radius a δ p))
    have hstrict := mul_lt_mul_of_pos_left hex ht
    have hweak := mul_le_mul_of_nonneg_left hey.le hnt
    constructor
    · nlinarith [mul_pos ht hx, mul_nonneg hnt hy.le]
    · nlinarith
  have hfmono : ∀ k l : ℝ, 0 < k → k ≤ l → ∀ p : ℝ,
      0 < f k p → (radius a δ p)^2*energy a δ (f k p) < 1 →
      (radius a δ p)^2*energy a δ c < 1 →
      0 < f l p ∧ (radius a δ p)^2*energy a δ (f l p) < 1 := by
    intro k l hk hkl p hpos hgood hcgood
    have hl : 0 ≤ l := hk.le.trans hkl
    let t := (1+k*(P.eval p)^2)/(1+l*(P.eval p)^2)
    have ht : 0 < t := div_pos (hden k hk.le p) (hden l hl p)
    have ht1 : t ≤ 1 := by
      apply (div_le_one (hden l hl p)).mpr
      nlinarith [sq_nonneg (P.eval p)]
    have heq : f l p = t*f k p+(1-t)*c := by
      dsimp [f, t]
      field_simp [ne_of_gt (hden k hk.le p), ne_of_gt (hden l hl p)]
      ring
    rw [heq]
    exact hmix p (f k p) c t hpos hc hgood hcgood ht ht1
  have hfpoint : ∀ p ∈ Icc a 1, ∃ k : ℝ, 0 < k ∧ 0 < f k p ∧
      (radius a δ p)^2*energy a δ (f k p) < 1 := by
    intro p hp
    by_cases hn : p ∈ S
    · refine ⟨1, by norm_num, ?_, ?_⟩
      · rw [hfnode 1 p hn]; norm_num
      · rw [hfnode 1 p hn]
        simpa only [energy, inv_one, one_pow, show (1:ℝ)+1-2=0 by norm_num, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, mul_one] using hrnode p hn
    · have hP2 : 0 < (P.eval p)^2 := sq_pos_of_ne_zero (hPoff p hn)
      have htop : Tendsto (fun k : ℝ => 1+k*(P.eval p)^2) atTop atTop :=
        tendsto_const_nhds.add_atTop ((tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).atTop_mul_const hP2)
      have ht : Tendsto (fun k : ℝ => c+(H.eval p-c)/(1+k*(P.eval p)^2)) atTop (𝓝 c) := by
        simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop htop)
      have ht' : Tendsto (fun k : ℝ => f k p) atTop (𝓝 c) := by
        apply ht.congr'
        filter_upwards [eventually_gt_atTop (0:ℝ)] with k hk
        dsimp [f]
        field_simp [ne_of_gt (hden k hk.le p)]
        ring
      have hevent : ∀ᶠ k : ℝ in atTop, 0 < k ∧ 0 < f k p ∧
          (radius a δ p)^2*energy a δ (f k p) < 1 := by
        have hp0 := ht'.eventually (lt_mem_nhds hc)
        have hlim := ((henergycont c hc).tendsto.comp ht').const_mul ((radius a δ p)^2)
        have hp1 := hlim.eventually (gt_mem_nhds (hcenter p hp))
        filter_upwards [eventually_gt_atTop (0:ℝ), hp0, hp1] with k hk hkp hk1
        exact ⟨hk, hkp, hk1⟩
      exact hevent.exists
  let U : {k : ℝ // 0 < k} → Set ℝ := fun k =>
    {p | 0 < p ∧ (radius a δ p)^2*energy a δ c < 1 ∧
      0 < f k p ∧ (radius a δ p)^2*energy a δ (f k p) < 1}
  have hUopen : ∀ k, IsOpen (U k) := by
    intro k
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hfc := (hfcont k k.property.le).continuousAt (x := p)
    have hr := hrcont p hp.1
    have hcc := hr.mul_const (energy a δ c)
    have hpc := hr.mul ((henergycont (f k p) hp.2.2.1).comp hfc)
    filter_upwards [lt_mem_nhds hp.1,
      hcc.eventually_lt continuousAt_const hp.2.1,
      continuousAt_const.eventually_lt hfc hp.2.2.1,
      hpc.eventually_lt continuousAt_const hp.2.2.2] with x hx hx1 hx2 hx3
    exact ⟨hx, hx1, hx2, hx3⟩
  have hUcover : Icc a 1 ⊆ ⋃ k, U k := by
    intro p hp
    obtain ⟨k, hk, hkp, hkg⟩ := hfpoint p hp
    exact mem_iUnion.mpr ⟨⟨k,hk⟩, ha.trans_le hp.1, hcenter p hp, hkp, hkg⟩
  have hUdirect : Directed (· ⊆ ·) U := by
    intro i j
    let k : {k : ℝ // 0 < k} := ⟨max i.val j.val, lt_max_iff.mpr (Or.inl i.property)⟩
    refine ⟨k, ?_, ?_⟩
    · intro p hp
      exact ⟨hp.1, hp.2.1, hfmono i k i.property (le_max_left _ _) p
        hp.2.2.1 hp.2.2.2 hp.2.1⟩
    · intro p hp
      exact ⟨hp.1, hp.2.1, hfmono j k j.property (le_max_right _ _) p
        hp.2.2.1 hp.2.2.2 hp.2.1⟩
  obtain ⟨k, hkall⟩ := isCompact_Icc.elim_directed_cover U hUopen hUcover hUdirect
  have hk : 0 < k.val := k.property
  have hfall : ∀ p ∈ Icc a 1, 0 < f k p ∧
      (radius a δ p)^2*energy a δ (f k p) < 1 := fun p hp => (hkall hp).2.2
  by_cases hempty : S = ∅
  · refine ⟨C c, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro p; simp
    · intro p hp
      simpa using And.intro hc (hcenter p hp)
    · simpa using (analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : ℝ => c) (Ioo a 1))
    · intro p hp
      simp [hempty, show c ≠ 1 from ne_of_lt hc1]
    · intro _ p; simp [c]
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let w : ℝ → ℝ := fun i => beta i * (Lagrange.nodalWeight S id i)^2
  let rho : ℝ → ℝ := fun p => ∑ i ∈ S, w i / (p-i)
  let rho' : ℝ → ℝ := fun p => ∑ i ∈ S, -(w i)/(p-i)^2
  have hw : ∀ i ∈ S, 0 < w i := by
    intro i hi
    exact mul_pos (hbeta i hi) (sq_pos_of_ne_zero (Lagrange.nodalWeight_ne_zero hinj hi))
  have hHR : ∀ p ∉ S, H.eval p-1=(P.eval p)^2*rho p := by
    intro p hp
    simp only [H, hermite, eval_add, eval_one, eval_finsetSum, eval_mul, eval_C,
      eval_sub, eval_X, eval_pow, add_sub_cancel_left, rho, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi : p ≠ i := fun he => hp (he ▸ hi)
    have hb : (Lagrange.basis S id i).eval p = P.eval p *
        (Lagrange.nodalWeight S id i * (p-i)⁻¹) :=
      Lagrange.eval_basis_not_at_node hi hpi
    rw [hb]
    dsimp [w]
    field_simp [sub_ne_zero.mpr hpi]
  have hRderiv : ∀ p ∉ S, HasDerivAt rho (rho' p) p := by
    intro p hp
    apply HasDerivAt.fun_sum
    intro i hi
    have hpi : p-i ≠ 0 := sub_ne_zero.mpr (fun he => hp (he ▸ hi))
    simpa only [zero_mul, zero_sub, mul_one] using!
      ((hasDerivAt_const p (w i)).div ((hasDerivAt_id p).sub_const i) hpi)
  have hRneg : ∀ p ∉ S, rho' p < 0 := by
    intro p hp
    apply Finset.sum_neg (fun i hi => ?_) hSne
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (hw i hi))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr (fun he => hp (he ▸ hi))))
  have hfform : ∀ p ∉ S, f k p =
      1+(P.eval p)^2*(rho p-k.val*(1-c))/(1+k.val*(P.eval p)^2) := by
    intro p hp
    have hh := hHR p hp
    dsimp [f]
    field_simp [ne_of_gt (hden k hk.le p)]
    nlinarith
  have hextra : ∀ p ∉ S, f k p = 1 → deriv (f k) p < 0 := by
    intro p hp hroot
    have hP2 : 0 < (P.eval p)^2 := sq_pos_of_ne_zero (hPoff p hp)
    have hzero : rho p-k.val*(1-c)=0 := by
      have hh := hfform p hp
      rw [hroot] at hh
      have hq : (P.eval p)^2*(rho p-k.val*(1-c))/(1+k.val*(P.eval p)^2)=0 := by linarith
      exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hq).resolve_right
        (ne_of_gt (hden k hk.le p)))).resolve_left (ne_of_gt hP2)
    have hdnum := ((P.hasDerivAt p).pow 2).mul ((hRderiv p hp).sub_const (k.val*(1-c)))
    have hdden := (((P.hasDerivAt p).pow 2).const_mul k.val).const_add 1
    have hder := (hdnum.div hdden (ne_of_gt (hden k hk.le p))).const_add 1
    have hder' : HasDerivAt (f k)
        ((P.eval p)^2*rho' p/(1+k.val*(P.eval p)^2)) p := by
      have hevent : ∀ᶠ x in 𝓝 p, x ∉ S :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hp
      apply (hder.congr_of_eventuallyEq (hevent.mono (fun x hx => hfform x hx))).congr_deriv
      simp only [Pi.pow_apply, Pi.mul_apply, hzero, mul_zero, zero_add, zero_mul, sub_zero]
      field_simp [ne_of_gt (hden k hk.le p)]
    rw [hder'.deriv]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hP2 (hRneg p hp)) (hden k hk.le p)
  have hiff : ∀ p ∈ Ioo a 1, (f k p=1 ∧ deriv (f k) p=beta p) ↔ p ∈ S := by
    intro p hp
    constructor
    · intro hh
      by_contra hn
      have hneg := hextra p hn hh.1
      have hbpos : 0 < beta p := one_div_pos.mpr
        (mul_pos (mul_pos (by norm_num) (ha.trans hp.1)) (sub_pos.mpr hp.2))
      rw [hh.2] at hneg
      exact (not_lt_of_gt hbpos) hneg
    · intro hi
      exact ⟨hfnode k p hi, (hfjet k p hi).deriv⟩
  let N : ℝ[X] := H + C (k.val*c)*P^2
  let D : ℝ[X] := 1 + C k.val*P^2
  have hND : (fun p => N.eval p/D.eval p) = f k := by
    funext p
    simp [N, D, f]
  have hNDp : ∀ p, N.eval p/D.eval p=f k p := fun p => congrFun hND p
  have hDpos : ∀ p : ℝ, 0 < D.eval p := by
    intro p
    simpa [D] using hden k hk.le p
  have hPdeg : P.natDegree = S.card := Lagrange.natDegree_nodal
  have hHdeg : H.natDegree ≤ 2*S.card := by
    apply (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · apply natDegree_sum_le_of_forall_le
      intro i hi
      have hbdeg : (Lagrange.basis S id i).natDegree = S.card-1 :=
        Lagrange.natDegree_basis hinj hi
      have hterm : (C (beta i)*(X-C i)*(Lagrange.basis S id i)^2).natDegree ≤
          1+2*(S.card-1) := by
        apply natDegree_mul_le.trans
        apply add_le_add
        · exact (natDegree_C_mul_le _ _).trans (by simp)
        · exact natDegree_pow_le.trans (by rw [hbdeg])
      exact hterm.trans (by have hh := hSne.card_pos; omega)
  have hNdeg : N.natDegree ≤ 2*S.card := by
    apply (natDegree_add_le _ _).trans (max_le hHdeg ?_)
    exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by rw [hPdeg]))
  have hDdeg : D.natDegree ≤ 2*S.card := by
    apply (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by rw [hPdeg]))
  refine ⟨N, D, hNdeg, hDdeg, hDpos, ?_, ?_, ?_, ?_⟩
  · simpa only [hNDp] using hfall
  · exact ((AnalyticOnNhd.eval_polynomial N).mono (subset_univ _)).div
      ((AnalyticOnNhd.eval_polynomial D).mono (subset_univ _))
      (fun p _ => ne_of_gt (hDpos p))
  · simpa only [hND, hNDp] using hiff
  · exact fun he => (hempty he).elim

end
end D5.S3.Quantum.Information.FiniteCalibrationControl
