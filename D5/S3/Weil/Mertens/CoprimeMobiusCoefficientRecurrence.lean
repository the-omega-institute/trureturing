/- GID: D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adjoining a new prime strictly decreases the coprime Mobius coefficient. -/

import D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Finset.NatDivisors

set_option autoImplicit false

open scoped BigOperators Topology
open Finset MeasureTheory Set Filter
open D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
open private divisorList from D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz

noncomputable section
namespace D5.S3.Weil.Mertens.CoprimeMobiusCoefficientRecurrence

/-- The same-sign overlap of a truncated Mobius kernel and its dilation. -/
def H (R p : ℕ) (u : ℝ) : ℝ :=
  if 0 < B R u * B R (u / p) then
    min |(B R u : ℝ)| |(B R (u / p) : ℝ)| else 0

/-- The inverse-square integral of the same-sign overlap over real numbers greater than one. -/
def J (R p : ℕ) : ℝ := ∫ u in Set.Ioi (1 : ℝ), H R p u / u ^ 2

set_option maxHeartbeats 800000 in
/-- Adjoining a prime outside a squarefree modulus gives an exact coefficient recurrence
and strictly decreases the coefficient. -/
theorem coefficient_recurrence (R p : ℕ) (hR : Squarefree R) (hR1 : 1 < R)
    (hp : p.Prime) (hpR : ¬ p ∣ R) :
    c (R * p) = (1 - ((p : ℝ)⁻¹) ^ 2) * c R -
      2 * e R * (1 - (p : ℝ)⁻¹) * J R p ∧ c (R * p) < c R := by
  classical
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hcop : R.Coprime p := (hp.coprime_iff_not_dvd.mpr hpR).symm
  have he : e (R * p) = e R * (1 - (p : ℝ)⁻¹) := by
    have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne_zero
    simp only [e, Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
      Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    field_simp [hp0.ne', hR0]
    <;> ring
  have hsplit (u : ℝ) : B (R * p) u = B R u - B R (u / p) := by
    have hd : (R * p).divisors = R.divisors ∪ R.divisors.image (p * ·) := by
      rw [Nat.divisors_mul]
      ext d
      simp only [Finset.mem_mul, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rcases hp.eq_one_or_self_of_dvd b (Nat.dvd_of_mem_divisors hb) with rfl | rfl
        · exact Or.inl (by simpa using ha)
        · exact Or.inr ⟨a, ha, by ac_rfl⟩
      · rintro (hd | ⟨a, ha, rfl⟩)
        · exact ⟨d, hd, 1, Nat.one_mem_divisors.mpr hp.ne_zero, mul_one d⟩
        · exact ⟨a, ha, p, Nat.mem_divisors_self p hp.ne_zero, mul_comm a p⟩
    have hdis : Disjoint R.divisors (R.divisors.image (p * ·)) := by
      apply Finset.disjoint_left.mpr
      intro d hd him
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp him
      exact hpR ((dvd_mul_right p a).trans (Nat.dvd_of_mem_divisors hd))
    simp only [B, sum_filter]
    rw [hd, sum_union hdis, sum_image]
    · rw [sub_eq_add_neg]
      congr 1
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro a ha
      have hpa : p.Coprime a := (hp.coprime_iff_not_dvd.mpr
        (fun h => hpR (h.trans (Nat.dvd_of_mem_divisors ha))))
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpa,
        ArithmeticFunction.moebius_apply_prime hp]
      have hle : (↑(p * a) : ℝ) ≤ u ↔ (a : ℝ) ≤ u / p := by
        rw [le_div_iff₀ hp0, Nat.cast_mul, mul_comm]
      simp only [hle]
      by_cases h : (a : ℝ) ≤ u / p <;> simp [h]
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
  have habs (x y : ℤ) : |((x - y : ℤ) : ℝ)| = |(x : ℝ)| + |(y : ℝ)| -
      2 * (if 0 < x * y then min |(x : ℝ)| |(y : ℝ)| else 0) := by
    by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
    · by_cases hxy : x ≤ y
      · have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
        have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
        have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
        by_cases hs : 0 < x * y
        · simp [hs, abs_of_nonneg hx', abs_of_nonneg hy', min_eq_left hxy',
            Int.cast_sub, abs_of_nonpos (sub_nonpos.mpr hxy')]
          <;> ring
        · have hz : x = 0 ∨ y = 0 := mul_eq_zero.mp
            (le_antisymm (not_lt.mp hs) (mul_nonneg hx hy))
          rcases hz with rfl | rfl <;> simp_all
      · have hxy' : (y : ℝ) ≤ x := by exact_mod_cast (le_of_not_ge hxy)
        have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
        have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
        by_cases hs : 0 < x * y
        · simp [hs, abs_of_nonneg hx', abs_of_nonneg hy', min_eq_right hxy',
            Int.cast_sub, abs_of_nonneg (sub_nonneg.mpr hxy')]
          <;> ring
        · have hz : x = 0 ∨ y = 0 := mul_eq_zero.mp
            (le_antisymm (not_lt.mp hs) (mul_nonneg hx hy))
          rcases hz with rfl | rfl <;> simp_all
    · have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
      have hy' : (y : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hy)
      have hs : ¬ 0 < x * y := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hx
        (le_of_not_ge hy))
      simp [hs, Int.cast_sub, abs_of_nonneg hx', abs_of_nonpos hy',
        abs_of_nonneg (sub_nonneg.mpr (hy'.trans hx'))]
      <;> ring
    · have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hx)
      have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
      have hs : ¬ 0 < x * y := not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg
        (le_of_not_ge hx) hy)
      simp [hs, Int.cast_sub, abs_of_nonpos hx', abs_of_nonneg hy',
        abs_of_nonpos (sub_nonpos.mpr (hx'.trans hy'))]
      <;> ring
    · have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hx)
      have hy' : (y : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hy)
      have hs : 0 < x * y := mul_pos_of_neg_of_neg (lt_of_not_ge hx) (lt_of_not_ge hy)
      by_cases hxy : (x : ℝ) ≤ y
      · simp [hs, Int.cast_sub, abs_of_nonpos hx', abs_of_nonpos hy',
          min_eq_right (neg_le_neg hxy), abs_of_nonpos (sub_nonpos.mpr hxy)]
        <;> ring
      · simp [hs, Int.cast_sub, abs_of_nonpos hx', abs_of_nonpos hy',
          min_eq_left (neg_le_neg (le_of_not_ge hxy)),
          abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))]
        <;> ring
  have hweight (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi a) := by
    have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
    exact hi.congr_fun (fun u hu => by
      dsimp only
      rw [Real.rpow_neg (le_of_lt (ha.trans hu)), Real.rpow_two]) measurableSet_Ioi
  have hkernel (Q q : ℕ) (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun u : ℝ => |(B Q (u / q) : ℝ)| / u ^ 2) (Ioi a) := by
    have hmeas : Measurable (fun u : ℝ => (B Q (u / q) : ℝ)) := by
      have heq : (fun u : ℝ => (B Q (u / q) : ℝ)) =
          fun u => ∑ d ∈ Q.divisors,
            if (d : ℝ) ≤ u / q then (ArithmeticFunction.moebius d : ℝ) else 0 := by
        funext u
        simp [B, Int.cast_sum, sum_filter]
      rw [heq]
      exact Finset.measurable_sum _ (fun d hd =>
        Measurable.ite (measurableSet_le measurable_const (measurable_id.div_const _))
          measurable_const measurable_const)
    have hbound (u : ℝ) : |(B Q (u / q) : ℝ)| ≤
        ∑ d ∈ Q.divisors, |(ArithmeticFunction.moebius d : ℝ)| := by
      simp only [B, Int.cast_sum]
      calc
        _ ≤ ∑ d ∈ Q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ u / q),
            |(ArithmeticFunction.moebius d : ℝ)| := abs_sum_le_sum_abs _ _
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => abs_nonneg _)
    have hmabs : Measurable (fun u : ℝ => |(B Q (u / q) : ℝ)|) := by
      simpa only [Real.norm_eq_abs] using hmeas.norm
    simpa only [IntegrableOn, div_eq_mul_inv] using (hweight a ha).bdd_mul
      hmabs.aestronglyMeasurable (ae_of_all _ (fun u => by
        simpa only [Real.norm_eq_abs, abs_abs, div_eq_mul_inv] using hbound u))
  have hrepr (Q : ℕ) (hQ : Squarefree Q) (hQ1 : 1 < Q) :
      c Q = e Q * ∫ u in Ioi (1 : ℝ), |(B Q u : ℝ)| / u ^ 2 := by
    have hQ0 : Q ≠ 0 := hQ.ne_zero
    have hQne : Q ≠ 1 := ne_of_gt hQ1
    let ds := divisorList Q
    have hds : ds = Q.divisors.sort (· ≤ ·) := rfl
    have hmem (a : ℕ) : a ∈ ds ↔ a ∈ Q.divisors := by simp [hds]
    have hsort : ds.Pairwise (· ≤ ·) := by simp [hds]
    have hgap : ∀ (l : List ℕ), l.Pairwise (· ≤ ·) →
        ∀ a b, (a, b) ∈ l.zip l.tail →
          a ∈ l ∧ b ∈ l ∧ a ≤ b ∧ ∀ d ∈ l, d ≤ a ∨ b ≤ d := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ih =>
        cases xs with
        | nil => simp
        | cons y ys =>
          intro hs a b hab
          have ht := (List.pairwise_cons.mp hs).2
          have hx := (List.pairwise_cons.mp hs).1
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hab
          rcases hab with ⟨rfl, rfl⟩ | hab
          · refine ⟨by simp, by simp, hx b (by simp), ?_⟩
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact Or.inl le_rfl
            · right
              rcases List.mem_cons.mp hd with rfl | hd
              · exact le_rfl
              · exact (List.pairwise_cons.mp ht).1 d hd
          · obtain ⟨ha, hb, hab', hg⟩ := ih ht a b hab
            refine ⟨by simp [ha], by simp [hb], hab', ?_⟩
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact Or.inl (hx a ha)
            · exact hg d hd
    have htel : ∀ (l : List ℕ) (a : ℕ) (f : ℕ → ℝ),
        (((a :: l).zip (a :: l).tail).map (fun ab => f ab.1 - f ab.2)).sum =
          f a - f ((a :: l).getLast (by simp)) := by
      intro l
      induction l with
      | nil => intro a f; simp
      | cons b l ih =>
        intro a f
        simpa [ih] using congrArg (fun z : ℝ => f a - f b + z) (ih b f)
    have hzero (u : ℝ) (hu : (Q : ℝ) ≤ u) : B Q u = 0 := by
      have hf : Q.divisors.filter (fun a : ℕ => (a : ℝ) ≤ u) = Q.divisors := by
        apply filter_eq_self.mpr
        intro a ha
        exact (Nat.cast_le.mpr
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0) (Nat.dvd_of_mem_divisors ha))).trans hu
      rw [B, hf]
      rw [← ArithmeticFunction.coe_mul_zeta_apply,
        ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply, if_neg hQne]
    have hpoint (u : ℝ) (hu : 1 ≤ u) :
        |(B Q u : ℝ)| = ((pairs Q).map (fun ab => |(B Q ab.1 : ℝ)| *
          ((if (ab.1 : ℝ) ≤ u then 1 else 0) -
            (if (ab.2 : ℝ) ≤ u then 1 else 0)))).sum := by
      have heq : ((pairs Q).map (fun ab => |(B Q ab.1 : ℝ)| *
          ((if (ab.1 : ℝ) ≤ u then 1 else 0) -
            (if (ab.2 : ℝ) ≤ u then 1 else 0)))).sum =
          ((pairs Q).map (fun ab => |(B Q u : ℝ)| *
          ((if (ab.1 : ℝ) ≤ u then 1 else 0) -
            (if (ab.2 : ℝ) ≤ u then 1 else 0)))).sum := by
        congr 1
        apply List.map_congr_left
        rintro ⟨a, b⟩ hab
        obtain ⟨ha, hb, hab', hg⟩ := hgap ds hsort a b hab
        by_cases hau : (a : ℝ) ≤ u
        · by_cases hbu : (b : ℝ) ≤ u
          · simp [hau, hbu]
          · have hf : Q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ u) =
                Q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ a) := by
              ext d
              simp only [mem_filter]
              constructor
              · rintro ⟨hd, hdu⟩
                refine ⟨hd, ?_⟩
                rcases hg d ((hmem d).mpr hd) with hda | hbd
                · exact_mod_cast hda
                · exact False.elim (hbu ((Nat.cast_le.mpr hbd).trans hdu))
              · rintro ⟨hd, hda⟩
                exact ⟨hd, hda.trans hau⟩
            have hB : B Q u = B Q a := by rw [B, hf, B]
            simp [hau, hbu, hB]
        · have hbu : ¬(b : ℝ) ≤ u := fun h => hau ((Nat.cast_le.mpr hab').trans h)
          simp [hau, hbu]
      rw [heq, List.sum_map_mul_left]
      have h1 : 1 ∈ ds := (hmem 1).mpr (Nat.one_mem_divisors.mpr hQ0)
      have hQm : Q ∈ ds := (hmem Q).mpr (Nat.mem_divisors_self Q hQ0)
      cases hdl : ds with
      | nil => simp [hdl] at h1
      | cons a l =>
        have hs : (a :: l).Pairwise (· ≤ ·) := hdl ▸ hsort
        have ha : a = 1 := by
          have hap : 0 < a := Nat.pos_of_mem_divisors ((hmem a).mp (by simp [hdl]))
          have ha1 : a ≤ 1 := hs.rel_head (by simpa [hdl] using h1)
          omega
        have hl : (a :: l).getLast (by simp) = Q := by
          apply le_antisymm
          · have hm : (a :: l).getLast (by simp) ∈ ds := by
              rw [hdl]
              exact List.getLast_mem _
            exact Nat.divisor_le ((hmem _).mp hm)
          · exact hs.rel_getLast (by simpa [hdl] using hQm)
        change |(B Q u : ℝ)| = |(B Q u : ℝ)| *
          ((ds.zip ds.tail).map _).sum
        rw [hdl, htel l a (fun k => if (k : ℝ) ≤ u then 1 else 0), hl, ha]
        by_cases hQu : (Q : ℝ) ≤ u
        · simp [hu, hQu, hzero u hQu]
        · simp [hu, hQu]
    have hstepInt (a : ℕ) : IntegrableOn
        (fun u : ℝ => (if (a : ℝ) ≤ u then (1 : ℝ) else 0) / u ^ 2) (Ioi 1) := by
      apply ((hweight 1 zero_lt_one).indicator (t := Ici (a : ℝ))
        measurableSet_Ici).congr_fun ?_ measurableSet_Ioi
      intro u hu
      dsimp only
      by_cases h : (a : ℝ) ≤ u <;> simp [Set.indicator, h]
    have hstep (a : ℕ) (ha : 1 ≤ a) :
        (∫ u in Ioi (1 : ℝ), (if (a : ℝ) ≤ u then (1 : ℝ) else 0) / u ^ 2) =
          (a : ℝ)⁻¹ := by
      have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
      calc
        _ = ∫ u in Ioi (1 : ℝ), (Ioi (a : ℝ)).indicator (fun u => (u ^ 2)⁻¹) u := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae (volume.ae_ne (a : ℝ))] with u hu
          by_cases h : (a : ℝ) < u
          · simp [Set.indicator, h, h.le]
          · have h' : ¬ (a : ℝ) ≤ u := fun hh => hu (le_antisymm (not_lt.mp h) hh)
            simp [Set.indicator, h, h']
        _ = ∫ u in Ioi (a : ℝ), (u ^ 2)⁻¹ := by
          rw [setIntegral_indicator measurableSet_Ioi,
            Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (Nat.one_le_cast.mpr ha))]
        _ = (a : ℝ)⁻¹ := by
          have hi := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha0
          have heq : (∫ u in Ioi (a : ℝ), u ^ (-2 : ℝ)) =
              ∫ u in Ioi (a : ℝ), (u ^ 2)⁻¹ := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            dsimp only
            rw [Real.rpow_neg (ha0.trans hu).le, Real.rpow_two]
          rw [heq] at hi
          norm_num [Real.rpow_neg_one] at hi
          exact hi
    let F : (ℕ × ℕ) → ℝ → ℝ := fun ab u => |(B Q ab.1 : ℝ)| *
      ((if (ab.1 : ℝ) ≤ u then 1 else 0) / u ^ 2 -
        (if (ab.2 : ℝ) ≤ u then 1 else 0) / u ^ 2)
    have hFi (ab : ℕ × ℕ) : IntegrableOn (F ab) (Ioi 1) :=
      ((hstepInt ab.1).sub (hstepInt ab.2)).const_mul _
    have hsum (l : List (ℕ × ℕ)) :
        IntegrableOn (fun u => (l.map (fun ab => F ab u)).sum) (Ioi 1) ∧
        (∫ u in Ioi (1 : ℝ), (l.map (fun ab => F ab u)).sum) =
          (l.map (fun ab => ∫ u in Ioi (1 : ℝ), F ab u)).sum := by
      induction l with
      | nil => simp
      | cons ab l ih =>
        simp only [List.map_cons, List.sum_cons]
        exact ⟨(hFi ab).add ih.1, by rw [integral_add (hFi ab) ih.1, ih.2]⟩
    have hsumval : (∫ u in Ioi (1 : ℝ), |(B Q u : ℝ)| / u ^ 2) =
        ((pairs Q).map (fun ab => |(B Q ab.1 : ℝ)| *
          ((ab.1 : ℝ)⁻¹ - (ab.2 : ℝ)⁻¹))).sum := by
      calc
        _ = ∫ u in Ioi (1 : ℝ), ((pairs Q).map (fun ab => F ab u)).sum := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          dsimp only
          rw [hpoint u hu.le, div_eq_mul_inv, ← List.sum_map_mul_right]
          congr 1
          apply List.map_congr_left
          intro ab hab
          dsimp [F]
          ring
        _ = _ := by
          rw [(hsum (pairs Q)).2]
          congr 1
          apply List.map_congr_left
          rintro ⟨a, b⟩ hab
          obtain ⟨ha, hb, _, _⟩ := hgap ds hsort a b hab
          rw [show F (a, b) = fun u => |(B Q a : ℝ)| *
              ((if (a : ℝ) ≤ u then 1 else 0) / u ^ 2 -
                (if (b : ℝ) ≤ u then 1 else 0) / u ^ 2) from rfl,
            integral_const_mul, integral_sub (hstepInt a) (hstepInt b),
            hstep a (Nat.pos_of_mem_divisors ((hmem a).mp ha)),
            hstep b (Nat.pos_of_mem_divisors ((hmem b).mp hb))]
    rw [c, if_neg hQne, hsumval]
  have hdilate : (∫ u in Ioi (1 : ℝ), |(B R (u / p) : ℝ)| / u ^ 2) =
      (p : ℝ)⁻¹ * ∫ u in Ioi (1 : ℝ), |(B R u : ℝ)| / u ^ 2 := by
    have hlow (u : ℝ) (hu : u < 1) : B R u = 0 := by
      unfold B
      apply sum_eq_zero
      intro d hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
      have hdu := (mem_filter.mp hd).2
      exact False.elim (not_le_of_gt hu ((Nat.one_le_cast.mpr hd1).trans hdu))
    have hdom : (∫ u in Ioi (p : ℝ)⁻¹, |(B R u : ℝ)| / u ^ 2) =
        ∫ u in Ioi (1 : ℝ), |(B R u : ℝ)| / u ^ 2 := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
        (Set.Ioi_subset_Ioi ((inv_lt_one₀ hp0).mpr hp1).le)
      filter_upwards [volume.ae_ne (1 : ℝ)] with u hu hmem
      have hu1 : u < 1 := lt_of_le_of_ne (not_lt.mp hmem.2) hu
      simp [hlow u hu1]
    calc
      _ = (p : ℝ)⁻¹ ^ 2 * ∫ u in Ioi (1 : ℝ),
          |(B R ((p : ℝ)⁻¹ * u) : ℝ)| / ((p : ℝ)⁻¹ * u) ^ 2 := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have hu0 : u ≠ 0 := ne_of_gt (zero_lt_one.trans hu)
        dsimp only
        rw [div_eq_inv_mul u (p : ℝ)]
        field_simp [hp0.ne', hu0]
      _ = (p : ℝ)⁻¹ * ∫ u in Ioi (p : ℝ)⁻¹, |(B R u : ℝ)| / u ^ 2 := by
        rw [integral_comp_mul_left_Ioi (fun u : ℝ => |(B R u : ℝ)| / u ^ 2)
          1 (inv_pos.mpr hp0)]
        simp only [inv_inv, mul_one, smul_eq_mul]
        field_simp [hp0.ne']
      _ = _ := by rw [hdom]
  have hJ : 0 ≤ J R p := by
    apply integral_nonneg
    intro u
    apply div_nonneg _ (sq_nonneg u)
    unfold H
    split_ifs <;> positivity
  have hcpos : 0 < c R := by
    rw [hrepr R hR hR1]
    have hepos : 0 < e R := div_pos (Nat.cast_pos.mpr
      (Nat.totient_pos.mpr (lt_trans Nat.zero_lt_one hR1))) (Nat.cast_pos.mpr
        (lt_trans Nat.zero_lt_one hR1))
    apply mul_pos hepos
    have hi : IntegrableOn (fun u : ℝ => |(B R u : ℝ)| / u ^ 2) (Ioi 1) := by
      simpa using hkernel R 1 1 zero_lt_one
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (fun u => div_nonneg (abs_nonneg _) (sq_nonneg u))) hi).mpr
    have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support (fun u : ℝ =>
        |(B R u : ℝ)| / u ^ 2) ∩ Ioi 1 := by
      intro u hu
      refine ⟨?_, hu.1⟩
      have hf : R.divisors.filter (fun d : ℕ => (d : ℝ) ≤ u) = {1} := by
        ext d
        simp only [mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hd, hdu⟩
          have hd1 := Nat.pos_of_mem_divisors hd
          have hd2 : d < 2 := by exact_mod_cast (hdu.trans_lt hu.2)
          omega
        · rintro rfl
          exact ⟨Nat.one_mem_divisors.mpr hR.ne_zero, by simpa using hu.1.le⟩
      have hB : B R u = 1 := by simp [B, hf]
      simp only [Function.mem_support, hB, Int.cast_one, abs_one]
      exact ne_of_gt (div_pos zero_lt_one (sq_pos_of_pos (zero_lt_one.trans hu.1)))
    exact lt_of_lt_of_le (by simp : 0 < volume (Ioo (1 : ℝ) 2)) (measure_mono hsub)
  have hrec : c (R * p) = (1 - ((p : ℝ)⁻¹) ^ 2) * c R -
      2 * e R * (1 - (p : ℝ)⁻¹) * J R p := by
    have hi₁ : IntegrableOn (fun u : ℝ => |(B R u : ℝ)| / u ^ 2) (Ioi 1) := by
      simpa using hkernel R 1 1 zero_lt_one
    have hi₂ := hkernel R p 1 zero_lt_one
    have hi₃ : IntegrableOn (fun u : ℝ => |(B (R * p) u : ℝ)| / u ^ 2) (Ioi 1) := by
      simpa using hkernel (R * p) 1 1 zero_lt_one
    have hpoint (u : ℝ) : H R p u / u ^ 2 =
        (|(B R u : ℝ)| / u ^ 2 + |(B R (u / p) : ℝ)| / u ^ 2 -
          |(B (R * p) u : ℝ)| / u ^ 2) / 2 := by
      rw [hsplit, habs]
      unfold H
      ring
    have hiadd : IntegrableOn (fun u : ℝ => |(B R u : ℝ)| / u ^ 2 +
        |(B R (u / p) : ℝ)| / u ^ 2) (Ioi 1) := hi₁.add hi₂
    have hiraw : IntegrableOn (fun u : ℝ => (|(B R u : ℝ)| / u ^ 2 +
        |(B R (u / p) : ℝ)| / u ^ 2 - |(B (R * p) u : ℝ)| / u ^ 2) / 2)
        (Ioi 1) := (hiadd.sub hi₃).div_const 2
    have hJi : IntegrableOn (fun u : ℝ => H R p u / u ^ 2) (Ioi 1) :=
      hiraw.congr_fun (fun u _ => (hpoint u).symm) measurableSet_Ioi
    have hsum : (∫ u in Ioi (1 : ℝ), |(B (R * p) u : ℝ)| / u ^ 2) =
        (1 + (p : ℝ)⁻¹) * (∫ u in Ioi (1 : ℝ), |(B R u : ℝ)| / u ^ 2) -
          2 * J R p := by
      calc
        _ = ∫ u in Ioi (1 : ℝ),
            (|(B R u : ℝ)| / u ^ 2 + |(B R (u / p) : ℝ)| / u ^ 2 -
              2 * (H R p u / u ^ 2)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          have hh := hpoint u
          linarith
        _ = _ := by
          rw [integral_sub hiadd (hJi.const_mul 2),
            integral_add hi₁ hi₂, integral_const_mul, hdilate]
          unfold J
          ring
    rw [hrepr (R * p) ((Nat.squarefree_mul hcop).mpr ⟨hR, hp.squarefree⟩)
      (hR1.trans_le (Nat.le_mul_of_pos_right R hp.pos)), he, hsum, hrepr R hR hR1]
    ring
  refine ⟨hrec, ?_⟩
  have hepos : 0 < e R := div_pos (Nat.cast_pos.mpr
    (Nat.totient_pos.mpr (lt_trans Nat.zero_lt_one hR1))) (Nat.cast_pos.mpr
      (lt_trans Nat.zero_lt_one hR1))
  have hi : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hi1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hsub : 0 ≤ 2 * e R * (1 - (p : ℝ)⁻¹) * J R p := by positivity
  have hdrop : 0 < ((p : ℝ)⁻¹) ^ 2 * c R := mul_pos (sq_pos_of_pos hi) hcpos
  rw [hrec]
  nlinarith

set_option maxHeartbeats 800000 in
/-- A positive same-sign overlap at one point forces its inverse-square integral to be positive. -/
theorem overlap_integral_pos (R p : ℕ) (hR : Squarefree R) (hR1 : 1 < R)
    (hp : p.Prime) {u₀ : ℝ} (hu₀ : 1 ≤ u₀)
    (hsign : 0 < B R u₀ * B R (u₀ / p)) : 0 < J R p := by
  classical
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hmeas (q : ℕ) : Measurable (fun u : ℝ => (B R (u / q) : ℝ)) := by
    have heq : (fun u : ℝ => (B R (u / q) : ℝ)) =
        fun u => ∑ d ∈ R.divisors,
          if (d : ℝ) ≤ u / q then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      funext u
      simp [B, Int.cast_sum, sum_filter]
    rw [heq]
    exact Finset.measurable_sum _ (fun d hd =>
      Measurable.ite (measurableSet_le measurable_const (measurable_id.div_const _))
        measurable_const measurable_const)
  have hm₁ : Measurable (fun u : ℝ => (B R u : ℝ)) := by simpa using hmeas 1
  have hmH : Measurable (H R p) := by
    have hs : MeasurableSet {u : ℝ | 0 < B R u * B R (u / p)} := by
      have heq : {u : ℝ | 0 < B R u * B R (u / p)} =
          {u : ℝ | (0 : ℝ) < (B R u : ℝ) * (B R (u / p) : ℝ)} := by
        ext u
        simp only [mem_ofPred_eq]
        norm_cast
      rw [heq]
      exact measurableSet_lt measurable_const (hm₁.mul (hmeas p))
    unfold H
    apply Measurable.ite hs
    · simpa only [Real.norm_eq_abs] using hm₁.norm.min (hmeas p).norm
    · exact measurable_const
  have hHnonneg (u : ℝ) : 0 ≤ H R p u := by unfold H; split_ifs <;> positivity
  have hHbound (u : ℝ) : H R p u ≤ |(B R u : ℝ)| := by
    unfold H
    split_ifs
    · exact min_le_left _ _
    · exact abs_nonneg _
  have hi : IntegrableOn (fun u : ℝ => H R p u / u ^ 2) (Ioi 1) := by
    have hweight : IntegrableOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi 1) := by
      have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)
      exact hi.congr_fun (fun u hu => by
        dsimp only
        rw [Real.rpow_neg (le_of_lt (zero_lt_one.trans hu)), Real.rpow_two]) measurableSet_Ioi
    have hbound (u : ℝ) : |(B R u : ℝ)| ≤
        ∑ d ∈ R.divisors, |(ArithmeticFunction.moebius d : ℝ)| := by
      simp only [B, Int.cast_sum]
      calc
        _ ≤ ∑ d ∈ R.divisors.filter (fun d : ℕ => (d : ℝ) ≤ u),
            |(ArithmeticFunction.moebius d : ℝ)| := abs_sum_le_sum_abs _ _
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => abs_nonneg _)
    simpa only [IntegrableOn, div_eq_mul_inv] using hweight.bdd_mul hmH.aestronglyMeasurable
      (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hHnonneg u)]
        exact (hHbound u).trans (hbound u)))
  have hcell (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
      (hy : y < (⌊x⌋₊ : ℝ) + 1) : B R y = B R x := by
    unfold B
    congr 1
    ext d
    simp only [mem_filter]
    constructor
    · rintro ⟨hd, hdy⟩
      refine ⟨hd, ?_⟩
      have hdn : d < ⌊x⌋₊ + 1 := by exact_mod_cast (hdy.trans_lt hy)
      exact (Nat.le_floor_iff hx).mp (by omega)
    · rintro ⟨hd, hdx⟩
      exact ⟨hd, hdx.trans hxy⟩
  let v : ℝ := min ((⌊u₀⌋₊ : ℝ) + 1) ((p : ℝ) * ((⌊u₀ / p⌋₊ : ℝ) + 1))
  have huv : u₀ < v := by
    apply lt_min (Nat.lt_floor_add_one u₀)
    simpa only [mul_comm] using
      (div_lt_iff₀ hp0).mp (Nat.lt_floor_add_one (u₀ / p))
  have hHpos (u : ℝ) (hu : u ∈ Ioo u₀ v) : 0 < H R p u := by
    have hB₁ : B R u = B R u₀ := hcell u₀ u (zero_le_one.trans hu₀) hu.1.le
      (hu.2.trans_le (min_le_left _ _))
    have hB₂ : B R (u / p) = B R (u₀ / p) :=
      hcell (u₀ / p) (u / p) (div_nonneg (zero_le_one.trans hu₀) hp0.le)
        (div_le_div_of_nonneg_right hu.1.le hp0.le)
        ((div_lt_iff₀ hp0).mpr (by
          simpa [mul_comm] using hu.2.trans_le (min_le_right _ _)))
    have hne₁ : B R u₀ ≠ 0 := fun h => by simp [h] at hsign
    have hne₂ : B R (u₀ / p) ≠ 0 := fun h => by simp [h] at hsign
    simp only [H, hB₁, hB₂, if_pos hsign]
    exact lt_min (abs_pos.mpr (Int.cast_ne_zero.mpr hne₁))
      (abs_pos.mpr (Int.cast_ne_zero.mpr hne₂))
  unfold J
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun u => div_nonneg (hHnonneg u) (sq_nonneg u))) hi).mpr
  have hsub : Ioo u₀ v ⊆ Function.support (fun u : ℝ => H R p u / u ^ 2) ∩ Ioi 1 := by
    intro u hu
    have hu1 : 1 < u := hu₀.trans_lt hu.1
    refine ⟨?_, hu1⟩
    exact ne_of_gt (div_pos (hHpos u hu) (sq_pos_of_pos (zero_lt_one.trans hu1)))
  exact lt_of_lt_of_le (by simpa only [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos] using huv :
    0 < volume (Ioo u₀ v)) (measure_mono hsub)

end D5.S3.Weil.Mertens.CoprimeMobiusCoefficientRecurrence
