/- GID: D5/S3/Geometry/Hyperideal/LengthGramPolytope
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramPolytope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.KreinMilman]
   utility: none
   digest: Twelve labeled vertices span the common six-length cut simplex. -/

import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set Filter Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramPolytope

/-- The endpoint near i on the original edge ij. -/
def endpoint (l : Fin 6 → ℝ) (i j : Fin 4) : Fin 4 → ℝ :=
  Pi.single i (-lengthGram l i j / (1 - lengthGram l i j)) +
    Pi.single j (1 / (1 - lengthGram l i j))

/-- The ordered endpoint labels. -/
abbrev EndpointLabel := {p : Fin 4 × Fin 4 // p.1 ≠ p.2}

set_option maxHeartbeats 1000000 in
-- The support classification combines both finite perturbation cases in one proof.
/-- The complete finite vertex classification of the jointly cut simplex. -/
theorem cut_body_polytope (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    (cutBody l).extremePoints ℝ =
      range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2) ∧
    convexHull ℝ (range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)) =
      cutBody l ∧
    Function.Injective (fun p : EndpointLabel => endpoint l p.val.1 p.val.2) ∧
    (∀ i j, i ≠ j →
      endpoint l i j ∈ cutBody l ∧
      0 < endpoint l i j i ∧ 0 < endpoint l i j j ∧
      (∀ k, k ≠ i → k ≠ j → endpoint l i j k = 0) ∧
      (∑ k, lengthGram l i k * endpoint l i j k) = 0 ∧
      (∀ r, r ≠ i → (∑ k, lengthGram l r k * endpoint l i j k) < 0)) := by
  classical
  let G := lengthGram l
  let row : (Fin 4 → ℝ) → Fin 4 → ℝ := fun x r => ∑ k, G r k * x k
  have hdiag (i : Fin 4) : G i i = 1 := by fin_cases i <;> rfl
  have hsym (i j : Fin 4) : G i j = G j i := by fin_cases i <;> fin_cases j <;> rfl
  have hoff (i j : Fin 4) (h : i ≠ j) : G i j < -1 := by
    have hc (k : Fin 6) : 1 < Real.cosh (l k) := Real.one_lt_cosh.mpr (ne_of_gt (hl k))
    fin_cases i <;> fin_cases j <;> first
      | exact (h rfl).elim
      | exact neg_lt_neg (hc 0)
      | exact neg_lt_neg (hc 1)
      | exact neg_lt_neg (hc 2)
      | exact neg_lt_neg (hc 3)
      | exact neg_lt_neg (hc 4)
      | exact neg_lt_neg (hc 5)
  have hrow_single (r i : Fin 4) (a : ℝ) : row (Pi.single i a) r = G r i * a := by
    simp [row, Pi.single_apply, mul_ite]
  have hrow_add (x y : Fin 4 → ℝ) (r : Fin 4) :
      row (x+y) r = row x r + row y r := by
    simp [row, mul_add, Finset.sum_add_distrib]
  have hrow_curve (x d : Fin 4 → ℝ) (t : ℝ) (r : Fin 4) :
      row (fun k => x k + t * d k) r = row x r + t * row d r := by
    simp only [row, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsum_single (i : Fin 4) (a : ℝ) : ∑ k, (Pi.single i a : Fin 4 → ℝ) k = a := by
    simp [Pi.single_apply]
  have hendpoint (i j : Fin 4) (hij : i ≠ j) :
      endpoint l i j ∈ cutBody l ∧
      0 < endpoint l i j i ∧ 0 < endpoint l i j j ∧
      (∀ k, k ≠ i → k ≠ j → endpoint l i j k = 0) ∧
      row (endpoint l i j) i = 0 ∧
      (∀ r, r ≠ i → row (endpoint l i j) r < 0) := by
    have hg := hoff i j hij
    have hd : 0 < 1 - G i j := by linarith
    have ha : 0 < -G i j / (1-G i j) := div_pos (by linarith) hd
    have hb : 0 < 1 / (1-G i j) := one_div_pos.mpr hd
    have hi : endpoint l i j i = -G i j / (1-G i j) := by
      simp [endpoint, G, hij]
    have hj : endpoint l i j j = 1 / (1-G i j) := by
      simp [endpoint, G, hij.symm]
    have hz (k : Fin 4) (hki : k ≠ i) (hkj : k ≠ j) : endpoint l i j k = 0 := by
      simp [endpoint, hki, hkj]
    have hr (r : Fin 4) : row (endpoint l i j) r =
        G r i * (-G i j / (1-G i j)) + G r j * (1 / (1-G i j)) := by
      exact (hrow_add _ _ r).trans (by rw [hrow_single, hrow_single])
    have hri : row (endpoint l i j) i = 0 := by
      rw [hr, hdiag]
      ring
    have hother (r : Fin 4) (hri : r ≠ i) : row (endpoint l i j) r < 0 := by
      rw [hr]
      by_cases hrj : r = j
      · subst r
        rw [hsym j i, hdiag]
        have hn : 1 - (G i j)^2 < 0 := by nlinarith
        calc
          _ = (1 - (G i j)^2) / (1-G i j) := by ring
          _ < 0 := div_neg_of_neg_of_pos hn hd
      · have h1 : G r i < 0 := lt_trans (hoff r i hri) (by norm_num)
        have h2 : G r j < 0 := lt_trans (hoff r j hrj) (by norm_num)
        exact add_neg (mul_neg_of_neg_of_pos h1 ha) (mul_neg_of_neg_of_pos h2 hb)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hi ▸ ha, hj ▸ hb, hz, hri, hother⟩
    · intro k
      by_cases hki : k = i
      · subst k; exact (hi ▸ ha).le
      by_cases hkj : k = j
      · subst k; exact (hj ▸ hb).le
      rw [hz k hki hkj]
    · change (∑ k, (Pi.single i (-G i j / (1-G i j)) +
          Pi.single j (1 / (1-G i j)) : Fin 4 → ℝ) k) = 1
      simp only [Pi.add_apply, Finset.sum_add_distrib, hsum_single]
      field_simp [hd.ne']
      ring
    · intro r
      by_cases h : r = i
      · subst r; exact hri.le
      exact (hother r h).le
  have hhalf (x : Fin 4 → ℝ) (hx : x ∈ cutBody l) (i : Fin 4)
      (hi : row x i = 0) : 1 / 2 < x i := by
    have hsum := hx.1.2
    have hnonneg := hx.1.1
    have hsplit : row x i = x i + ∑ j ∈ Finset.univ.erase i, G i j * x j := by
      dsimp [row]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag, one_mul, add_comm]
    have hs : (∑ j ∈ Finset.univ.erase i, x j) + x i = 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), hsum]
    have hex : ∃ j ∈ Finset.univ.erase i, 0 < x j := by
      by_contra h
      push Not at h
      have hz : ∑ j ∈ Finset.univ.erase i, G i j * x j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [le_antisymm (h j hj) (hnonneg j), mul_zero]
      have hs0 : ∑ j ∈ Finset.univ.erase i, x j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact le_antisymm (h j hj) (hnonneg j)
      rw [hi, hz] at hsplit
      rw [hs0] at hs
      linarith
    have hlt : (∑ j ∈ Finset.univ.erase i, G i j * x j) <
        ∑ j ∈ Finset.univ.erase i, -x j := by
      apply Finset.sum_lt_sum
      · intro j hj
        simpa using mul_le_mul_of_nonneg_right
          (hoff i j (Finset.ne_of_mem_erase hj).symm).le (hnonneg j)
      · obtain ⟨j,hj,hpos⟩ := hex
        refine ⟨j,hj,?_⟩
        simpa using mul_lt_mul_of_pos_right
          (hoff i j (Finset.ne_of_mem_erase hj).symm) hpos
    rw [Finset.sum_neg_distrib] at hlt
    linarith
  have honly (x : Fin 4 → ℝ) (hx : x ∈ cutBody l) (i : Fin 4)
      (hi : row x i = 0) : ∀ r, r ≠ i → row x r < 0 := by
    intro r hri
    apply lt_of_le_of_ne (hx.2 r)
    intro hr
    have hi' := hhalf x hx i hi
    have hr' := hhalf x hx r hr
    have hle : x i + x r ≤ ∑ k, x k := by
      exact Finset.add_le_sum (fun k _ => hx.1.1 k)
        (Finset.mem_univ i) (Finset.mem_univ r) hri.symm
    rw [hx.1.2] at hle
    linarith
  have hperturb (x : Fin 4 → ℝ) (hx : x ∈ (cutBody l).extremePoints ℝ)
      (d : Fin 4 → ℝ) (hs : ∑ k, d k = 0)
      (hz : ∀ k, x k = 0 → d k = 0)
      (hr : ∀ r, row x r = 0 → row d r = 0) : d = 0 := by
    let curve : ℝ → (Fin 4 → ℝ) := fun t k => x k + t*d k
    have hc (k : Fin 4) : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ curve t k := by
      by_cases h : x k = 0
      · exact Filter.Eventually.of_forall (fun t => by simp [curve, h, hz k h])
      · have hpos : 0 < x k := lt_of_le_of_ne (hx.1.1.1 k) (Ne.symm h)
        have hcont : ContinuousAt (fun t : ℝ => x k + t*d k) 0 := by fun_prop
        exact (continuousAt_const.eventually_lt hcont (by simpa using hpos)).mono
          (fun t ht => ht.le)
    have hrc (r : Fin 4) : ∀ᶠ t in nhds (0 : ℝ), row (curve t) r ≤ 0 := by
      by_cases h : row x r = 0
      · exact Filter.Eventually.of_forall (fun t => by rw [hrow_curve, h, hr r h]; simp)
      · have hneg : row x r < 0 := lt_of_le_of_ne (hx.1.2 r) h
        have hcont : ContinuousAt (fun t : ℝ => row x r + t*row d r) 0 := by fun_prop
        exact (hcont.eventually_lt continuousAt_const (by simpa using hneg)).mono
          (fun t ht => by rw [hrow_curve]; exact ht.le)
    have hnear : ∀ᶠ t in nhds (0 : ℝ), curve t ∈ cutBody l := by
      filter_upwards [Filter.eventually_all.mpr hc, Filter.eventually_all.mpr hrc] with t ht hrt
      refine ⟨⟨ht, ?_⟩, hrt⟩
      simp [curve, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hx.1.1.2]
    have hnegnear : ∀ᶠ t in nhds (0 : ℝ), curve (-t) ∈ cutBody l := by
      exact (show Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) from
        by simpa using (continuous_neg.tendsto (0 : ℝ))).eventually hnear
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hnear.and hnegnear)
    have ht : ε/2 ∈ Metric.ball (0 : ℝ) ε := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      rw [abs_of_pos (by positivity)]
      linarith
    obtain ⟨hplus,hminus⟩ := hball ht
    have hseg : x ∈ openSegment ℝ (curve (ε/2)) (curve (-(ε/2))) := by
      refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, curve]
      ring
    have heq := hx.2 hplus hminus hseg
    ext k
    have hh := congrFun heq k
    have htne : ε/2 ≠ 0 := ne_of_gt (by positivity)
    have : (ε/2)*d k = 0 := by dsimp [curve] at hh; linarith
    exact (mul_eq_zero.mp this).resolve_left htne
  have hpair (x : Fin 4 → ℝ) (hx : x ∈ cutBody l) (i : Fin 4) :
      ∃ j, j ≠ i ∧ 0 < x j := by
    by_contra h
    push Not at h
    have hz : ∀ j, j ≠ i → x j = 0 :=
      fun j hj => le_antisymm (h j hj) (hx.1.1 j)
    have hsi : ∑ j, x j = x i := by
      apply Finset.sum_eq_single i
      · intro j _ hji; exact hz j hji
      · simp
    have hri : row x i = x i := by
      dsimp [row]
      rw [Finset.sum_eq_single i]
      · rw [hdiag, one_mul]
      · intro j _ hji; rw [hz j hji, mul_zero]
      · simp
    have hcut : row x i ≤ 0 := hx.2 i
    rw [hri] at hcut
    rw [hx.1.2] at hsi
    linarith
  have hclass (x : Fin 4 → ℝ) (hx : x ∈ (cutBody l).extremePoints ℝ) :
      ∃ i j, i ≠ j ∧ x = endpoint l i j := by
    have hactive : ∃ i, row x i = 0 := by
      by_contra h
      push Not at h
      obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => hx.1.1.1 k)).mp
        (show 0 < ∑ k, x k by rw [hx.1.1.2]; norm_num)
      obtain ⟨j,hji,hj⟩ := hpair x hx.1 i
      let d : Fin 4 → ℝ := Pi.single i 1 + Pi.single j (-1)
      have hd := hperturb x hx d (by simp [d, Pi.add_apply, Finset.sum_add_distrib, hsum_single])
        (by intro k hk; simp [d, Pi.single_apply];
            have hki : k ≠ i := by intro hki; subst k; linarith
            have hkj : k ≠ j := by intro hkj; subst k; linarith
            simp [hki,hkj])
        (fun r hr => (h r hr).elim)
      have := congrFun hd i
      simp [d, hji.symm] at this
    obtain ⟨i,hi⟩ := hactive
    have hipos : 0 < x i := lt_trans (by norm_num) (hhalf x hx.1 i hi)
    obtain ⟨j,hji,hj⟩ := hpair x hx.1 i
    have hz (k : Fin 4) (hki : k ≠ i) (hkj : k ≠ j) : x k = 0 := by
      by_contra hk
      have hkpos := lt_of_le_of_ne (hx.1.1.1 k) (Ne.symm hk)
      let d : Fin 4 → ℝ := Pi.single i (G i j - G i k) +
        Pi.single j (G i k - 1) + Pi.single k (1-G i j)
      have hds : ∑ r, d r = 0 := by
        simp only [d, Pi.add_apply, Finset.sum_add_distrib, hsum_single]
        ring
      have hdz : ∀ r, x r = 0 → d r = 0 := by
        intro r hr
        have hri : r ≠ i := by intro h; subst r; linarith
        have hrj : r ≠ j := by intro h; subst r; linarith
        have hrk : r ≠ k := by intro h; subst r; linarith
        simp [d, hri, hrj, hrk]
      have hdr : ∀ r, row x r = 0 → row d r = 0 := by
        intro r hr
        have hri : r = i := by
          by_contra hri
          have := honly x hx.1 i hi r hri
          linarith
        subst r
        simp only [d, hrow_add, hrow_single, hdiag]
        ring
      have hd := hperturb x hx d hds hdz hdr
      have hdj := congrFun hd j
      have hgjk := hoff i k hki.symm
      simp [d, hji, hkj.symm] at hdj
      linarith
    have hsum : x i + x j = 1 := by
      have : ∑ k, x k = x i + x j := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        have he : ∑ k ∈ Finset.univ.erase i, x k = x j := by
          apply Finset.sum_eq_single j
          · intro k hk hkj
            exact hz k (Finset.ne_of_mem_erase hk) hkj
          · intro h; exact (h (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩)).elim
        rw [he]; ring
      rw [hx.1.1.2] at this
      linarith
    have hrow : x i + G i j*x j = 0 := by
      have hxeq : x = Pi.single i (x i) + Pi.single j (x j) := by
        ext k
        by_cases hki : k = i
        · subst k; simp [hji.symm]
        by_cases hkj : k = j
        · subst k; simp [hji]
        simp [hki,hkj,hz k hki hkj]
      rw [hxeq,hrow_add,hrow_single,hrow_single,hdiag,one_mul] at hi
      exact hi
    have hd : 1-G i j ≠ 0 := by have := hoff i j hji.symm; linarith
    have heqj : x j = 1/(1-G i j) := by apply (eq_div_iff hd).mpr; nlinarith
    have heqi : x i = -G i j/(1-G i j) := by
      apply (eq_div_iff hd).mpr
      have hscaled := congrArg (fun t : ℝ => G i j*t) hsum
      nlinarith
    refine ⟨i,j,hji.symm,?_⟩
    ext k
    by_cases hki : k = i
    · subst k; simpa [endpoint, G, Pi.single_apply, hji.symm] using heqi
    by_cases hkj : k = j
    · subst k; simpa [endpoint, G, Pi.single_apply, hji] using heqj
    simp [endpoint, hki,hkj,hz k hki hkj]
  have hext (i j : Fin 4) (hij : i ≠ j) : endpoint l i j ∈ (cutBody l).extremePoints ℝ := by
    obtain ⟨hp,hpi,hpj,hpz,hpr,hprest⟩ := hendpoint i j hij
    refine ⟨hp, ?_⟩
    intro y hy z hz hs
    obtain ⟨a,b,ha,hb,hab,heq⟩ := hs
    have hy0 (k : Fin 4) (hki : k ≠ i) (hkj : k ≠ j) : y k = 0 := by
      have h := congrFun heq k
      have hpk := hpz k hki hkj
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [hpk] at h
      have := hy.1.1 k
      have := hz.1.1 k
      nlinarith [mul_nonneg hb.le (hz.1.1 k)]
    have hyr : row y i = 0 := by
      have h : a*row y i + b*row z i = 0 := by
        calc
          _ = row (a • y + b • z) i := by
            simp [row, Fin.sum_univ_succ]
            ring
          _ = row (endpoint l i j) i := by rw [heq]
          _ = 0 := hpr
      have hyle : row y i ≤ 0 := hy.2 i
      have hzle : row z i ≤ 0 := hz.2 i
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.le hzle]
    have hyeq : y = Pi.single i (y i) + Pi.single j (y j) := by
      ext k
      by_cases hki : k = i
      · subst k; simp [hij]
      by_cases hkj : k = j
      · subst k; simp [hij.symm]
      simp [hki,hkj,hy0 k hki hkj]
    have hsum : y i + y j = 1 := by
      have h := hy.1.2
      rw [hyeq] at h
      simpa only [Pi.add_apply,Finset.sum_add_distrib,hsum_single] using h
    have hrow : y i + G i j*y j = 0 := by
      rw [hyeq,hrow_add,hrow_single,hrow_single,hdiag,one_mul] at hyr
      exact hyr
    have hd : 1-G i j ≠ 0 := by have := hoff i j hij; linarith
    have hj : y j = 1/(1-G i j) := by apply (eq_div_iff hd).mpr; nlinarith
    have hi : y i = -G i j/(1-G i j) := by
      apply (eq_div_iff hd).mpr
      have hscaled := congrArg (fun t : ℝ => G i j*t) hsum
      nlinarith only [hsum,hscaled,hrow]
    rw [hyeq, endpoint, hi,hj]
  let V := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  have hvertices : (cutBody l).extremePoints ℝ = V := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i,j,hij,heq⟩ := hclass x hx
      exact ⟨⟨(i,j),hij⟩,heq.symm⟩
    · rintro x ⟨p,rfl⟩
      exact hext p.val.1 p.val.2 p.property
  have hconv : Convex ℝ (cutBody l) := by
    apply (convex_stdSimplex ℝ (Fin 4)).inter
    intro x hx y hy a b ha hb hab r
    change row (a • x + b • y) r ≤ 0
    have heq : row (a • x + b • y) r = a*row x r + b*row y r := by
      simp [row, Fin.sum_univ_succ]
      ring
    rw [heq]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx r))
      (mul_nonpos_of_nonneg_of_nonpos hb (hy r))
  have hfinite : V.Finite := finite_range _
  have hhull : convexHull ℝ V = cutBody l := by
    have h := closure_convexHull_extremePoints (shared_radial_body l hl).1 hconv
    rw [hvertices, (hfinite.isClosed_convexHull ℝ).closure_eq] at h
    exact h
  have hinj : Function.Injective (fun p : EndpointLabel => endpoint l p.val.1 p.val.2) := by
    intro p q h
    change endpoint l p.val.1 p.val.2 = endpoint l q.val.1 q.val.2 at h
    obtain ⟨hp,hpi,hpj,hpz,hpr,hprest⟩ := hendpoint p.val.1 p.val.2 p.property
    obtain ⟨hq,hqi,hqj,hqz,hqr,hqrest⟩ := hendpoint q.val.1 q.val.2 q.property
    have hi : p.val.1 = q.val.1 := by
      by_contra hi
      have hh := hqrest p.val.1 hi
      rw [← h,hpr] at hh
      exact (lt_irrefl _ hh)
    have hj : p.val.2 = q.val.2 := by
      by_contra hj
      have hji : p.val.2 ≠ q.val.1 := by rw [← hi]; exact p.property.symm
      have hh := hqz p.val.2 hji hj
      rw [← h] at hh
      linarith
    apply Subtype.ext
    exact Prod.ext hi hj
  exact ⟨hvertices,hhull,hinj,hendpoint⟩

#print axioms cut_body_polytope
end D5.S3.Geometry.Hyperideal.LengthGramPolytope
