/- GID: D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/HermiteEnvelopeEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equality in the Hermite logarithmic bound characterizes the two moment nodes and their multiplicities. -/

import D5.S3.Analytic.Interpolation.HermiteUpperEnvelope
import D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives
import D5.S3.Analytic.Interpolation.HermiteMomentBounds
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Filter
open scoped Topology ContDiff Manifold

noncomputable section

namespace D5.S3.Analytic.Interpolation.HermiteEnvelopeEquality

private theorem extension_near_interval {s : Set ℝ} (hs : IsOpen s)
    (L H : ℝ) (hsub : Icc L H ⊆ s) (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f s) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 3 g ∧ ∀ x ∈ Icc L H, g =ᶠ[𝓝 x] f := by
  obtain ⟨K, hKnhds, hKclosed, hKs⟩ :=
    exists_mem_nhdsSet_isClosed_subset (hs.mem_nhdsSet.mpr hsub) isClosed_Icc
  let t : ℝ → Set ℝ := fun x => {y | x ∈ K → y = f x}
  have ht (x : ℝ) : Convex ℝ (t x) := (convex_singleton (f x)).setOfPred_const_imp
  have hlocal : ∀ x : ℝ, ∃ U ∈ 𝓝 x, ∃ g : ℝ → ℝ,
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 3 g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ K
    · refine ⟨s, hs.mem_nhds (hKs hx), f, hf.contMDiffOn, ?_⟩
      intro y hy hKy
      exact Eq.refl _
    · refine ⟨Kᶜ, hKclosed.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy hKy
      exact (hy hKy).elim
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local
      (I := 𝓘(ℝ, ℝ)) (n := 3) ht hlocal
  refine ⟨g, g.contMDiff.contDiff, ?_⟩
  intro x hx
  filter_upwards [mem_nhdsSet_iff_forall.mp hKnhds x hx] with y hy
  exact hg y hy


/-- A positive third derivative forces strict negativity left of a double zero. -/
theorem negative_left_of_double_node (x L H : ℝ) (g : ℝ → ℝ)
    (hxL : x < L) (hLH : L < H) (hg : ContDiff ℝ 3 g)
    (hgL : g L = 0) (hgH : g H = 0) (hdL : deriv g L = 0)
    (hpos : ∀ t ∈ Ioo x H, 0 < iteratedDeriv 3 g t) : g x < 0 := by
  by_contra hn
  have hnonneg : 0 ≤ g x := le_of_not_gt hn
  have hc1 : Continuous (deriv g) := by
    simpa only [iteratedDeriv_one] using hg.continuous_iteratedDeriv 1 (by norm_num)
  have hd1 : Differentiable ℝ (deriv g) := by
    simpa only [iteratedDeriv_one] using hg.differentiable_iteratedDeriv 1 (by norm_num)
  have hc2 : Continuous (deriv (deriv g)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hg.continuous_iteratedDeriv 2 (by norm_num)
  obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_slope g hxL hg.continuous.continuousOn
    (hg.differentiable (by norm_num)).differentiableOn
  have hu0 : deriv g u ≤ 0 := by
    rw [hdu, hgL]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hxL.le)
  obtain ⟨a, ha, hda⟩ := exists_deriv_eq_slope (deriv g) hu.2 hc1.continuousOn
    hd1.differentiableOn
  have ha0 : 0 ≤ deriv (deriv g) a := by
    rw [hda, hdL]
    exact div_nonneg (by linarith) (sub_nonneg.mpr hu.2.le)
  obtain ⟨v, hv, hdv⟩ := exists_deriv_eq_zero hLH hg.continuous.continuousOn
    (hgL.trans hgH.symm)
  obtain ⟨b, hb, hdb⟩ := exists_deriv_eq_zero hv.1 hc1.continuousOn (hdL.trans hdv.symm)
  have hm : StrictMonoOn (deriv (deriv g)) (Ioo x H) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo x H) hc2.continuousOn
    intro t ht
    have ht' : t ∈ Ioo x H := interior_subset ht
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hpos t ht'
  have hab := hm ⟨hu.1.trans ha.1, ha.2.trans hLH⟩
    ⟨hxL.trans hb.1, hb.2.trans hv.2⟩ (ha.2.trans hb.1)
  linarith


private theorem hermite_strict_majorant (L H x : ℝ) (f p : ℝ → ℝ)
    (hL : 0 < L) (hLH : L < H) (hx : 0 < x) (hxH : x ≤ H)
    (hxLne : x ≠ L) (hxHne : x ≠ H)
    (hf : ContDiffOn ℝ 3 f (Ioi 0)) (hp : ContDiff ℝ 3 p)
    (hzero : ∀ t, iteratedDeriv 3 p t = 0)
    (hvalL : p L = f L) (hderL : deriv p L = deriv f L) (hvalH : p H = f H)
    (hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < iteratedDeriv 3 f t) : f x < p x := by
  rcases lt_trichotomy x L with hxL | rfl | hLx
  · obtain ⟨g, hg, heq⟩ := extension_near_interval isOpen_Ioi x H
      (fun t ht => hx.trans_le ht.1) (f - p) (hf.sub hp.contDiffOn)
    have hLm : L ∈ Icc x H := ⟨hxL.le, hLH.le⟩
    have hHm : H ∈ Icc x H := ⟨hxH, le_rfl⟩
    have hgL : g L = 0 := by
      rw [(heq L hLm).eq_of_nhds, Pi.sub_apply, hvalL, sub_self]
    have hgH : g H = 0 := by
      rw [(heq H hHm).eq_of_nhds, Pi.sub_apply, hvalH, sub_self]
    have hdL : deriv g L = 0 := by
      rw [(heq L hLm).deriv_eq,
        deriv_sub ((hf.contDiffAt (isOpen_Ioi.mem_nhds hL)).differentiableAt (by norm_num))
          (hp.differentiable (by norm_num)).differentiableAt]
      exact sub_eq_zero.mpr hderL.symm
    have hthird (t : ℝ) (ht : t ∈ Ioo x H) : 0 < iteratedDeriv 3 g t := by
      have ht0 : t ∈ Ioi (0 : ℝ) := hx.trans ht.1
      rw [(heq t (Ioo_subset_Icc_self ht)).iteratedDeriv_eq 3,
        iteratedDeriv_sub (hf.contDiffAt (isOpen_Ioi.mem_nhds ht0)) hp.contDiffAt,
        hzero t, sub_zero]
      exact hpos t ht0
    have hneg := negative_left_of_double_node x L H g hxL hLH hg hgL hgH hdL hthird
    rw [(heq x ⟨le_rfl, hxH⟩).eq_of_nhds, Pi.sub_apply] at hneg
    linarith
  · exact (hxLne rfl).elim
  · rcases lt_or_eq_of_le hxH with hxH' | rfl
    · obtain ⟨ξ, hξ, hrem, hneg⟩ :=
      HermiteUpperEnvelope.hermite_two_point_remainder_on isOpen_Ioi L H x
        (fun t ht => hL.trans_le ht.1) f p ⟨hLx, hxH'⟩ hf hp.contDiffOn
        (fun t _ => hzero t) hvalL hderL hvalH (fun t ht => hpos t (hL.trans ht.1))
      linarith
    · exact (hxHne rfl).elim

private theorem quadratic_derivatives (a b c L : ℝ) :
    deriv (fun t : ℝ => a + b * (t - L) + c * (t - L)^2) L = b ∧
      ∀ t, iteratedDeriv 3 (fun t : ℝ => a + b * (t - L) + c * (t - L)^2) t = 0 := by
  have hd : deriv (fun t : ℝ => a + b * (t - L) + c * (t - L)^2) =
      fun t => b + 2 * c * (t - L) := by
    funext t
    convert (((hasDerivAt_const t a).add (((hasDerivAt_id t).sub_const L).const_mul b)).add
      ((((hasDerivAt_id t).sub_const L).pow 2).const_mul c)).deriv using 1
    · congr 1
    · simp only [id_eq]
      ring
  have hd2 : deriv (fun t : ℝ => b + 2 * c * (t - L)) = fun _ => 2 * c := by
    funext t
    simp
  constructor
  · rw [hd]; ring
  · simp [iteratedDeriv_succ, iteratedDeriv_zero, hd, hd2]

private theorem quadratic_sum_of_moments {k : ℕ} (x : Fin k → ℝ) (μ r a b c : ℝ)
    (hsum : ∑ i, x i = (k : ℝ) * μ)
    (hvar : ∑ i, (x i - μ) ^ 2 = (k : ℝ) * ((k : ℝ) - 1) * r ^ 2) :
    let p := fun t => a + b * (t - (μ - r)) + c * (t - (μ - r))^2
    ∑ i, p (x i) = p (μ + ((k : ℝ) - 1) * r) + ((k : ℝ) - 1) * p (μ - r) := by
  have hcenter : ∑ i, (x i - μ) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hfirst : ∑ i, (x i - (μ - r)) = (k : ℝ) * r := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    ring
  have hsecond : ∑ i, (x i - (μ - r))^2 = (k : ℝ)^2 * r^2 := by
    simp_rw [show ∀ i, (x i - (μ - r))^2 = (x i - μ)^2 + 2*r*(x i - μ) + r^2
      from fun i => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcenter, hvar]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  dsimp only
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hfirst, hsecond]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


#print axioms negative_left_of_double_node
#print axioms hermite_strict_majorant

/-- For positive variance, equality holds exactly on the two moment nodes;
there is then one upper coordinate and every other coordinate is the lower node. -/
theorem hermite_envelope_equality {k : ℕ} (hk : 2 ≤ k) (x : Fin k → ℝ)
    (hx : ∀ i, 0 < x i) :
    let μ := (∑ i, x i) / (k : ℝ)
    let V := ∑ i, (x i - μ)^2
    let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
    let L := μ - r
    let H := μ + ((k : ℝ) - 1) * r
    0 < V →
      ((∑ i, Real.log (1 - Real.exp (-x i)) =
        Real.log (1 - Real.exp (-H)) + ((k : ℝ) - 1) * Real.log (1 - Real.exp (-L))) ↔
        ∀ i, x i = L ∨ x i = H) ∧
      ((∀ i, x i = L ∨ x i = H) →
        ∃ j, x j = H ∧ ∀ i, i ≠ j → x i = L) := by
  classical
  let μ := (∑ i, x i) / (k : ℝ)
  let V := ∑ i, (x i - μ)^2
  let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
  let L := μ - r
  let H := μ + ((k : ℝ) - 1) * r
  let f := fun t : ℝ => Real.log (1 - Real.exp (-t))
  change 0 < V → ((∑ i, f (x i) = f H + ((k : ℝ) - 1) * f L) ↔
    ∀ i, x i = L ∨ x i = H) ∧ _
  intro hV
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) :=
    mul_pos hkpos (by linarith)
  have hsum : ∑ i, x i = (k : ℝ) * μ := by dsimp [μ]; field_simp
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hV hden)
  have hVr : V = (k : ℝ) * ((k : ℝ) - 1) * r^2 := by
    rw [Real.sq_sqrt (div_nonneg hV.le hden.le)]
    field_simp [ne_of_gt hkpos, ne_of_gt (by linarith : (0 : ℝ) < (k : ℝ) - 1)]
  have hbounds := HermiteMomentBounds.hermite_moment_bounds hk x hx
  change 0 < L ∧ ∀ i, x i ≤ H at hbounds
  have hHL : H - L = (k : ℝ) * r := by dsimp [H, L]; ring
  have hLH : L < H := sub_pos.mp (hHL.symm ▸ mul_pos hkpos hr)
  have hHLne : H - L ≠ 0 := (sub_pos.mpr hLH).ne'
  let c := (f H - f L - deriv f L * (H - L)) / (H - L)^2
  let p := fun t => f L + deriv f L * (t - L) + c * (t - L)^2
  have hp : ContDiff ℝ 3 p := by dsimp [p]; fun_prop
  have hpL : p L = f L := by simp [p]
  have hpH : p H = f H := by dsimp [p, c]; field_simp [hHLne]; ring
  have hpd := quadratic_derivatives (f L) (deriv f L) c L
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  have hstrict (i : Fin k) (hiL : x i ≠ L) (hiH : x i ≠ H) : f (x i) < p (x i) :=
    hermite_strict_majorant L H (x i) f p hbounds.1 hLH (hx i) (hbounds.2 i)
      hiL hiH hlog.1 hp hpd.2 hpL hpd.1 hpH (fun t ht => (hlog.2 t ht).2.2.2)
  have hpoint (i : Fin k) : f (x i) ≤ p (x i) := by
    by_cases hiL : x i = L
    · rw [hiL, hpL]
    by_cases hiH : x i = H
    · rw [hiH, hpH]
    exact (hstrict i hiL hiH).le
  have hpsum : ∑ i, p (x i) = f H + ((k : ℝ) - 1) * f L := by
    calc
      _ = p H + ((k : ℝ) - 1) * p L :=
        quadratic_sum_of_moments x μ r (f L) (deriv f L) c hsum hVr
      _ = _ := by rw [hpH, hpL]
  constructor
  · constructor
    · intro heq i
      have hgap : ∑ j, (p (x j) - f (x j)) = 0 := by
        rw [Finset.sum_sub_distrib, hpsum, heq, sub_self]
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hpoint j))).mp hgap i
          (Finset.mem_univ i)
      by_contra hn
      push Not at hn
      have := hstrict i hn.1 hn.2
      linarith
    · intro hnodes
      calc
        _ = ∑ i, p (x i) := Finset.sum_congr rfl (fun i _ => by
          rcases hnodes i with hi | hi
          · rw [hi, hpL]
          · rw [hi, hpH])
        _ = _ := hpsum
  · intro hnodes
    let S := Finset.univ.filter (fun i => x i = H)
    have hcount : (S.card : ℝ) * (H - L) = H - L := by
      calc
        _ = ∑ i, (if x i = H then H - L else 0) := by
          simp [S, Finset.sum_ite]
          ring
        _ = ∑ i, (x i - L) := Finset.sum_congr rfl (fun i _ => by
          rcases hnodes i with hi | hi
          · rw [hi, if_neg (ne_of_lt hLH), sub_self]
          · rw [hi, if_pos rfl])
        _ = H - L := by
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hsum]
          dsimp [L, H]
          ring
    have hcardR : (S.card : ℝ) = 1 := by nlinarith [sub_pos.mpr hLH]
    have hcard : S.card = 1 := by exact_mod_cast hcardR
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hjH : x j = H := by
      have : j ∈ S := by rw [hj]; exact Finset.mem_singleton_self j
      exact (Finset.mem_filter.mp this).2
    refine ⟨j, hjH, ?_⟩
    intro i hij
    rcases hnodes i with hi | hi
    · exact hi
    · have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hj, Finset.mem_singleton] at this
      exact (hij this).elim

#print axioms hermite_envelope_equality

private theorem zero_variance_coordinates {k : ℕ} (x : Fin k → ℝ) (μ : ℝ)
    (hV : ∑ i, (x i - μ) ^ 2 = 0) : ∀ i, x i = μ := by
  intro i
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j - μ))).mp hV i (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

/-- Zero total squared deviation means all coordinates and both nodes are the mean,
and the logarithmic bound is an equality. -/
theorem hermite_envelope_zero_variance {k : ℕ} (x : Fin k → ℝ) :
    let μ := (∑ i, x i) / (k : ℝ)
    let V := ∑ i, (x i - μ)^2
    let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
    let L := μ - r
    let H := μ + ((k : ℝ) - 1) * r
    V = 0 → (∀ i, x i = μ) ∧ L = μ ∧ H = μ ∧
      ∑ i, Real.log (1 - Real.exp (-x i)) =
        Real.log (1 - Real.exp (-H)) + ((k : ℝ) - 1) * Real.log (1 - Real.exp (-L)) := by
  let μ := (∑ i, x i) / (k : ℝ)
  let V := ∑ i, (x i - μ)^2
  let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
  let L := μ - r
  let H := μ + ((k : ℝ) - 1) * r
  let f := fun t : ℝ => Real.log (1 - Real.exp (-t))
  change V = 0 → (∀ i, x i = μ) ∧ L = μ ∧ H = μ ∧
    ∑ i, f (x i) = f H + ((k : ℝ) - 1) * f L
  intro hV
  have heq := zero_variance_coordinates x μ hV
  have hL : L = μ := by simp [L, r, hV]
  have hH : H = μ := by simp [H, r, hV]
  refine ⟨heq, hL, hH, ?_⟩
  rw [hL, hH]
  calc
    _ = ∑ _ : Fin k, f μ := Finset.sum_congr rfl (fun i _ => congrArg f (heq i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem sum_one_distinguished {k : ℕ} (j : Fin k) (a b : ℝ) (F : ℝ → ℝ) :
    ∑ i, F (if i = j then a else b) = F a + ((k : ℝ) - 1) * F b := by
  classical
  have h (i : Fin k) : F (if i = j then a else b) =
      F b + (if i = j then F a - F b else 0) := by
    split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- Every feasible pair of mean and total squared deviation is attained by a positive
vector with one upper node and all other coordinates at the lower node; its bound is exact. -/
theorem hermite_envelope_sharpness {k : ℕ} (hk : 2 ≤ k) (μ V : ℝ)
    (hμ : 0 < μ) (hV : 0 ≤ V) (hbound : V < (k : ℝ) * ((k : ℝ) - 1) * μ^2) :
    let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
    let L := μ - r
    let H := μ + ((k : ℝ) - 1) * r
    ∃ x : Fin k → ℝ,
      (∀ i, 0 < x i) ∧ (∑ i, x i = (k : ℝ) * μ) ∧
      (∑ i, (x i - μ)^2 = V) ∧ (∑ i, (x i)^2 = (k : ℝ) * μ^2 + V) ∧
      (∑ i, Real.log (1 - Real.exp (-x i)) =
        Real.log (1 - Real.exp (-H)) + ((k : ℝ) - 1) * Real.log (1 - Real.exp (-L))) ∧
      ∃ j, x j = H ∧ ∀ i, i ≠ j → x i = L := by
  classical
  let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
  let L := μ - r
  let H := μ + ((k : ℝ) - 1) * r
  change ∃ x : Fin k → ℝ, (∀ i, 0 < x i) ∧ (∑ i, x i = (k : ℝ) * μ) ∧
    (∑ i, (x i - μ)^2 = V) ∧ (∑ i, (x i)^2 = (k : ℝ) * μ^2 + V) ∧
    (∑ i, Real.log (1 - Real.exp (-x i)) =
      Real.log (1 - Real.exp (-H)) + ((k : ℝ) - 1) * Real.log (1 - Real.exp (-L))) ∧ _
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := mul_pos hkpos (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrμ : r < μ := (Real.sqrt_lt' hμ).mpr ((div_lt_iff₀ hden).mpr (by nlinarith))
  have hVr : V = (k : ℝ) * ((k : ℝ) - 1) * r^2 := by
    rw [Real.sq_sqrt (div_nonneg hV hden.le)]
    field_simp [ne_of_gt hkpos, ne_of_gt (by linarith : (0 : ℝ) < (k : ℝ) - 1)]
  let j : Fin k := ⟨0, by omega⟩
  let x : Fin k → ℝ := fun i => if i = j then H else L
  have hx : ∀ i, 0 < x i := by
    intro i
    dsimp [x, H, L]
    split_ifs
    · nlinarith
    · linarith
  have hsum : ∑ i, x i = (k : ℝ) * μ := by
    have hs := sum_one_distinguished j H L id
    change ∑ i, x i = H + ((k : ℝ) - 1) * L at hs
    rw [hs]
    dsimp [H, L]
    ring
  have hvar : ∑ i, (x i - μ)^2 = V := by
    have hs := sum_one_distinguished j H L (fun t => (t - μ)^2)
    change ∑ i, (x i - μ)^2 = (H - μ)^2 + ((k : ℝ) - 1) * (L - μ)^2 at hs
    rw [hs, hVr]
    dsimp [H, L]
    ring
  have hsecond : ∑ i, (x i)^2 = (k : ℝ) * μ^2 + V := by
    have hs := sum_one_distinguished j H L (fun t => t^2)
    change ∑ i, (x i)^2 = H^2 + ((k : ℝ) - 1) * L^2 at hs
    rw [hs, hVr]
    dsimp [H, L]
    ring
  have hmean : (∑ i, x i) / (k : ℝ) = μ := by rw [hsum]; field_simp
  have hnodes (i : Fin k) : x i = L ∨ x i = H := by
    dsimp [x]
    split_ifs <;> simp
  have hequality : ∑ i, Real.log (1 - Real.exp (-x i)) =
      Real.log (1 - Real.exp (-H)) + ((k : ℝ) - 1) * Real.log (1 - Real.exp (-L)) := by
    by_cases hVz : V = 0
    · have hz := hermite_envelope_zero_variance x
      dsimp only at hz
      rw [hmean, hvar] at hz
      exact (hz hVz).2.2.2
    · have hc := hermite_envelope_equality hk x hx
      dsimp only at hc
      rw [hmean, hvar] at hc
      exact ((hc (lt_of_le_of_ne hV (Ne.symm hVz))).1).mpr hnodes
  refine ⟨x, hx, hsum, hvar, hsecond, hequality, j, ?_, ?_⟩
  · simp [x, H, r]
  · intro i hi
    simp [x, hi, L, r]

-- Positive-variance hypotheses have a concrete inhabitant.
example : ∃ x : Fin 2 → ℝ, (∀ i, 0 < x i) ∧
    0 < ∑ i, (x i - (∑ j, x j) / (2 : ℝ))^2 := by
  refine ⟨![1, 3], ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]

#print axioms hermite_envelope_zero_variance
#print axioms hermite_envelope_sharpness

end D5.S3.Analytic.Interpolation.HermiteEnvelopeEquality
