/- GID: D5/S3/Analytic/Asymptotics/GeometricRightUSCUniformization
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/GeometricRightUSCUniformization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonmeagre geometric sampling uniformizes right upper semicontinuous lower bounds. -/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Closure
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

/-! Eventual lower bounds from a nonmeagre family of geometric bases. -/

noncomputable section

open Set Filter Topology

namespace D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization

/-- A nonmeagre family of geometric bases with individual eventual lower
bounds yields one lower bound on a final real ray when F is right upper
semicontinuous after T. -/
theorem uniform_lower_bound_of_nonmeagre_geometric_bases_right_usc
    (F : ℝ → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hright : ∀ x : ℝ, T ≤ x →
      UpperSemicontinuousWithinAt F (Set.Ioi x) x)
    (a b : ℝ) (ha : 1 < a) (hab : a < b)
    (S : Set ℝ) (hSab : S ⊆ Ioo a b) (hS : ¬ IsMeagre S)
    (hsample : ∀ q ∈ S, ∃ M : ℝ, 0 ≤ M ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k → -M ≤ F (q ^ k)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ X : ℝ, T < X ∧
      ∀ x : ℝ, X ≤ x → -M ≤ F x := by
  classical
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt T ha
  have hn₀pos : 1 ≤ n₀ := by
    by_contra h
    have hz : n₀ = 0 := by omega
    simpa [hz] using hT.trans_lt hn₀
  have hlate (q : ℝ) (haq : a ≤ q) (k : ℕ) (hk : n₀ ≤ k) :
      T < q ^ k :=
    hn₀.trans_le ((pow_le_pow_right₀ ha.le hk).trans
      (pow_le_pow_left₀ ha0.le haq k))

  -- E_(m,N) contains exactly the bases in (a,b) with the corresponding
  -- uniform bound for every k >= max(N,n₀). These sets need not be closed:
  -- category is applied to their ambient closures.
  let E : ℕ × ℕ → Set ℝ := fun p =>
    {q | q ∈ Ioo a b ∧
      ∀ k : ℕ, max p.2 n₀ ≤ k → -(p.1 : ℝ) ≤ F (q ^ k)}
  have hcover : S ⊆ ⋃ p : ℕ × ℕ, E p := by
    intro q hq
    obtain ⟨M, _hM, N, _hN, hqbound⟩ := hsample q hq
    obtain ⟨m, hm⟩ := exists_nat_ge M
    refine mem_iUnion.mpr ⟨(m, N), ?_⟩
    refine ⟨hSab hq, ?_⟩
    intro k hk
    exact (neg_le_neg hm).trans (hqbound k ((le_max_left N n₀).trans hk))

  -- If every closure(E p) had empty interior, every E p would be nowhere
  -- dense, so their countable union would make S meagre.
  have hinterior : ∃ p : ℕ × ℕ, (interior (closure (E p))).Nonempty := by
    by_contra hn
    have hEm (p : ℕ × ℕ) : IsMeagre (E p) := by
      apply IsNowhereDense.isMeagre
      rw [IsNowhereDense]
      exact not_nonempty_iff_eq_empty.mp (fun hp => hn ⟨p, hp⟩)
    exact hS ((isMeagre_iUnion hEm).mono hcover)
  obtain ⟨p, q₀, hq₀⟩ := hinterior

  have hEsub : E p ⊆ Icc a b := by
    intro q hq
    exact ⟨hq.1.1.le, hq.1.2.le⟩
  have hclosure_sub : closure (E p) ⊆ Icc a b :=
    closure_minimal hEsub isClosed_Icc
  have hq₀ab : q₀ ∈ Ioo a b := by
    have hq₀cl : q₀ ∈ closure (E p) := interior_subset hq₀
    have hnh : closure (E p) ∈ 𝓝 q₀ :=
      mem_interior_iff_mem_nhds.mp hq₀
    obtain ⟨l₀, u₀, hq₀lu, hlu₀⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hnh
    obtain ⟨z, hzq, hz₀⟩ := exists_between hq₀lu.1
    have hzab : z ∈ Icc a b := hclosure_sub (hlu₀ ⟨hzq, hz₀.trans hq₀lu.2⟩)
    have haq₀ : a < q₀ := hzab.1.trans_lt hz₀
    obtain ⟨z', hq₀z', hz'u⟩ := exists_between hq₀lu.2
    have hz'ab : z' ∈ Icc a b := hclosure_sub (hlu₀ ⟨hq₀lu.1.trans hq₀z', hz'u⟩)
    have hq₀b : q₀ < b := hq₀z'.trans_le hz'ab.2
    exact ⟨haq₀, hq₀b⟩

  -- Localize to an open interval lying simultaneously in Ioo(a,b) and
  -- interior(closure(E p)). Every point in this interval is a closure point
  -- of E p, which is enough to find good bases strictly to its right.
  have hnhlocal : closure (E p) ∩ Ioo a b ∈ 𝓝 q₀ :=
    inter_mem (mem_interior_iff_mem_nhds.mp hq₀)
      (isOpen_Ioo.mem_nhds hq₀ab)
  obtain ⟨l, u, hq₀lu, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hnhlocal
  have hclopen (q : ℝ) (hq : q ∈ Ioo l u) : q ∈ closure (E p) :=
    (hlu hq).1
  have hbase (q : ℝ) (hq : q ∈ Ioo l u) : q ∈ Ioo a b :=
    (hlu hq).2

  -- Right upper semicontinuity transfers a fixed-k bound from good bases
  -- approaching q strictly from the right.
  have hgood (q : ℝ) (hq : q ∈ Ioo l u)
      (k : ℕ) (hk : max p.2 n₀ ≤ k) : -(p.1 : ℝ) ≤ F (q ^ k) := by
    have hqab : q ∈ Ioo a b := hbase q hq
    have hq0 : 0 ≤ q := ha0.le.trans hqab.1.le
    have hqT : T ≤ q ^ k :=
      (hlate q hqab.1.le k ((le_max_right p.2 n₀).trans hk)).le
    have hpowmaps : MapsTo (fun r : ℝ => r ^ k) (Ioi q) (Ioi (q ^ k)) := by
      intro r hr
      exact pow_lt_pow_left₀ hr hq0 (by
        have : 1 ≤ k := hn₀pos.trans ((le_max_right p.2 n₀).trans hk)
        omega)
    have hpowcont : ContinuousWithinAt (fun r : ℝ => r ^ k) (Ioi q) q :=
      (continuous_id.pow k).continuousAt.continuousWithinAt
    have hcomp : UpperSemicontinuousWithinAt
        (fun r : ℝ => F (r ^ k)) (Ioi q) q := by
      intro z hz
      exact hpowcont.tendsto_nhdsWithin hpowmaps (hright (q ^ k) hqT z hz)
    by_contra hfail
    have hstrict : F (q ^ k) < -(p.1 : ℝ) := lt_of_not_ge hfail
    have hev : {r : ℝ | F (r ^ k) < -(p.1 : ℝ)} ∈ 𝓝[Ioi q] q :=
      hcomp (-(p.1 : ℝ)) hstrict
    obtain ⟨V, hV, hqV, hVsub⟩ := mem_nhdsWithin.mp hev
    obtain ⟨v, w, hqvw, hvw⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds hqV)
    have hqmin : q < min w u := lt_min hqvw.2 hq.2
    obtain ⟨w', hqw', hw'min⟩ := exists_between hqmin
    have hclU : (closure (E p) ∩ Ioo q w').Nonempty := by
      obtain ⟨s, hsq, hsw⟩ := nonempty_Ioo.mpr hqw'
      refine ⟨s, hclopen s ⟨hq.1.trans hsq, hsw.trans (lt_min_iff.mp hw'min).2⟩,
        ⟨hsq, hsw⟩⟩
    have hEU : (E p ∩ Ioo q w').Nonempty :=
      (closure_inter_open_nonempty_iff (s := E p) (t := Ioo q w') isOpen_Ioo).mp hclU
    obtain ⟨r, hrE, hrU⟩ := hEU
    have hrV : r ∈ V := hvw ⟨hqvw.1.trans hrU.1,
      hrU.2.trans (lt_min_iff.mp hw'min).1⟩
    have hrJ : r ∈ Ioo l u :=
      ⟨hq.1.trans hrU.1, hrU.2.trans (lt_min_iff.mp hw'min).2⟩
    have hrlo : -(p.1 : ℝ) ≤ F (r ^ k) := hrE.2 k hk
    have hrhi : F (r ^ k) < -(p.1 : ℝ) :=
      hVsub ⟨hrV, hrU.1⟩
    exact (not_lt_of_ge hrlo) hrhi

  -- Every compact nondegenerate subinterval [c,d] of this open interval
  -- has overlapping power bands covering a final real ray.
  obtain ⟨c, hq₀c, hcu⟩ := exists_between hq₀lu.2
  obtain ⟨d, hcd, hdu⟩ := exists_between hcu
  have hc1 : 1 < c := ha.trans (hbase c ⟨hq₀lu.1.trans hq₀c, hcu⟩).1
  have hc0 : 0 < c := zero_lt_one.trans hc1
  have hd0 : 0 < d := hc0.trans hcd
  have hcl : l < c := hq₀lu.1.trans hq₀c
  have hband (q : ℝ) (hq : q ∈ Icc c d) : q ∈ Ioo l u :=
    ⟨hcl.trans_le hq.1, hq.2.trans_lt hdu⟩
  have hac : a ≤ c := (hbase c ⟨hcl, hcu⟩).1.le
  have hratio : 1 < d / c := (one_lt_div hc0).mpr hcd
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt c hratio
  let K : ℕ := max (max p.2 n₀) L
  have hKN : max p.2 n₀ ≤ K := le_max_left _ _
  have hKL : L ≤ K := le_max_right _ _
  have hKpos : 1 ≤ K := hn₀pos.trans ((le_max_right p.2 n₀).trans hKN)
  have hoverlap (k : ℕ) (hk : K ≤ k) : c ^ (k + 1) ≤ d ^ k := by
    have hgrow : c ≤ (d / c) ^ k :=
      hL.le.trans (pow_le_pow_right₀ hratio.le (hKL.trans hk))
    have hmul := mul_le_mul_of_nonneg_right hgrow (pow_nonneg hc0.le k)
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hc0.ne')] at hmul
    simpa only [pow_succ, mul_comm] using hmul
  refine ⟨(p.1 : ℝ), Nat.cast_nonneg _, c ^ K,
    hlate c hac K ((le_max_right p.2 n₀).trans hKN), ?_⟩
  intro x hx
  have hx1 : 1 ≤ x :=
    (one_le_pow₀ hc1.le).trans hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hx1 hc1
  have hKk : K ≤ k := by
    have : K < k + 1 := (pow_lt_pow_iff_right₀ hc1).mp (hx.trans_lt hkhi)
    omega
  have hkpos : k ≠ 0 := by omega
  have hxhi : x ≤ d ^ k := hkhi.le.trans (hoverlap k hKk)
  let q : ℝ := x ^ ((k : ℝ)⁻¹)
  have hq0 : 0 ≤ q := Real.rpow_nonneg hx0 _
  have hqpow : q ^ k = x := Real.rpow_inv_natCast_pow hx0 hkpos
  have hcq : c ≤ q := le_of_pow_le_pow_left₀ hkpos hq0 (by
    simpa [hqpow] using hklo)
  have hqd : q ≤ d := le_of_pow_le_pow_left₀ hkpos hd0.le (by
    simpa [hqpow] using hxhi)
  have hbound := hgood q (hband q ⟨hcq, hqd⟩) k (hKN.trans hKk)
  simpa only [hqpow] using hbound

end D5.S3.Analytic.Asymptotics.GeometricRightUSCUniformization
