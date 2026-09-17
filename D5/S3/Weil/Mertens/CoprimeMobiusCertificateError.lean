/- GID: D5/S3/Weil/Mertens/CoprimeMobiusCertificateError
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CoprimeMobiusCertificateError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the uniform error of the coprime truncated Mobius certificate. -/

import D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.Floor.Semifield

set_option autoImplicit false

open scoped BigOperators
open Finset
open private divisorList from D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz

noncomputable section
namespace D5.S3.Weil.Mertens.CoprimeMobiusCertificateError

/-- The Mobius sum over positive divisors up to an inclusive real endpoint. -/
def B (R : ℕ) (u : ℝ) : ℤ :=
  ∑ a ∈ R.divisors.filter (fun a : ℕ => (a : ℝ) ≤ u), ArithmeticFunction.moebius a

/-- The number of positive integers at most a real endpoint and coprime to the modulus. -/
def C (R : ℕ) (x : ℝ) : ℝ :=
  ((Icc 1 ⌊x⌋₊).filter (fun d => d.Coprime R)).card

/-- The sum of absolute truncated kernels over all positive coprime integers up to N. -/
def U (R N : ℕ) : ℝ := if R = 1 then N else
  ∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime R), |(B R ((N : ℝ) / d) : ℝ)|

/-- Consecutive pairs in the increasing list of positive divisors. -/
def pairs (R : ℕ) : List (ℕ × ℕ) :=
  (divisorList R).zip (divisorList R).tail

/-- The total absolute partial Mobius sum over the bounded divisor intervals. -/
def mass (R : ℕ) : ℝ := ((pairs R).map (fun ab => |(B R ab.1 : ℝ)|)).sum

/-- The density of integers coprime to the modulus. -/
def e (R : ℕ) : ℝ := (R.totient : ℝ) / R

/-- The linear coefficient obtained from the actual consecutive divisor intervals. -/
def c (R : ℕ) : ℝ := if R = 1 then 1 else
  e R * ((pairs R).map (fun ab => |(B R ab.1 : ℝ)| *
    ((ab.1 : ℝ)⁻¹ - (ab.2 : ℝ)⁻¹))).sum


/-- The error from the linear coefficient is bounded uniformly in the truncation parameter. -/
theorem certificate_error (N R : ℕ) (hR : Squarefree R) (hR1 : 1 < R) :
    |U R N - c R * N| ≤ 2 * R.divisors.card * mass R := by
  classical
  have hR0 : R ≠ 0 := hR.ne_zero
  have hRne : R ≠ 1 := ne_of_gt hR1
  let ds := divisorList R
  have hds : ds = R.divisors.sort (· ≤ ·) := rfl
  have hmem (a : ℕ) : a ∈ ds ↔ a ∈ R.divisors := by simp [hds]
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
  have hzero (u : ℝ) (hu : (R : ℝ) ≤ u) : B R u = 0 := by
    have hf : R.divisors.filter (fun a : ℕ => (a : ℝ) ≤ u) = R.divisors := by
      apply filter_eq_self.mpr
      intro a ha
      exact (Nat.cast_le.mpr
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hR0) (Nat.dvd_of_mem_divisors ha))).trans hu
    rw [B, hf]
    rw [← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply, if_neg hRne]
  have hpoint (u : ℝ) (hu : 1 ≤ u) :
      |(B R u : ℝ)| = ((pairs R).map (fun ab => |(B R ab.1 : ℝ)| *
        ((if (ab.1 : ℝ) ≤ u then 1 else 0) -
          (if (ab.2 : ℝ) ≤ u then 1 else 0)))).sum := by
    have heq : ((pairs R).map (fun ab => |(B R ab.1 : ℝ)| *
        ((if (ab.1 : ℝ) ≤ u then 1 else 0) -
          (if (ab.2 : ℝ) ≤ u then 1 else 0)))).sum =
        ((pairs R).map (fun ab => |(B R u : ℝ)| *
        ((if (ab.1 : ℝ) ≤ u then 1 else 0) -
          (if (ab.2 : ℝ) ≤ u then 1 else 0)))).sum := by
      congr 1
      apply List.map_congr_left
      rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb, hab', hg⟩ := hgap ds hsort a b hab
      by_cases hau : (a : ℝ) ≤ u
      · by_cases hbu : (b : ℝ) ≤ u
        · simp [hau, hbu]
        · have hf : R.divisors.filter (fun d : ℕ => (d : ℝ) ≤ u) =
              R.divisors.filter (fun d : ℕ => (d : ℝ) ≤ a) := by
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
          have hB : B R u = B R a := by rw [B, hf, B]
          simp [hau, hbu, hB]
      · have hbu : ¬(b : ℝ) ≤ u := fun h => hau ((Nat.cast_le.mpr hab').trans h)
        simp [hau, hbu]
    rw [heq, List.sum_map_mul_left]
    have h1 : 1 ∈ ds := (hmem 1).mpr (Nat.one_mem_divisors.mpr hR0)
    have hRm : R ∈ ds := (hmem R).mpr (Nat.mem_divisors_self R hR0)
    cases hdl : ds with
    | nil => simp [hdl] at h1
    | cons a l =>
      have hs : (a :: l).Pairwise (· ≤ ·) := hdl ▸ hsort
      have ha : a = 1 := by
        have hap : 0 < a := Nat.pos_of_mem_divisors ((hmem a).mp (by simp [hdl]))
        have ha1 : a ≤ 1 := hs.rel_head (by simpa [hdl] using h1)
        omega
      have hl : (a :: l).getLast (by simp) = R := by
        apply le_antisymm
        · have hm : (a :: l).getLast (by simp) ∈ ds := by
            rw [hdl]
            exact List.getLast_mem _
          exact Nat.divisor_le ((hmem _).mp hm)
        · exact hs.rel_getLast (by simpa [hdl] using hRm)
      change |(B R u : ℝ)| = |(B R u : ℝ)| *
        ((ds.zip ds.tail).map _).sum
      rw [hdl, htel l a (fun k => if (k : ℝ) ≤ u then 1 else 0), hl, ha]
      by_cases hRu : (R : ℝ) ≤ u
      · simp [hu, hRu, hzero u hRu]
      · simp [hu, hRu]
  have hcount_endpoint (a : ℕ) (ha : 0 < a) :
      (∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime R),
        (if (a : ℝ) ≤ (N : ℝ) / d then (1 : ℝ) else 0)) = C R ((N : ℝ) / a) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one, C]
    apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
    ext d
    have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp only [mem_filter, mem_Icc, Nat.le_floor_iff (div_nonneg hn ha'.le)]
    constructor
    · rintro ⟨⟨⟨hd1, hdN⟩, hc⟩, h⟩
      have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      refine ⟨⟨hd1, (le_div_iff₀ ha').mpr ?_⟩, hc⟩
      simpa [mul_comm] using (le_div_iff₀ hd').mp h
    · rintro ⟨⟨hd1, h⟩, hc⟩
      have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      have hda := (le_div_iff₀ ha').mp h
      have ha1 : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
      have hdN : d ≤ N := by
        exact_mod_cast (le_trans (le_mul_of_one_le_right hd'.le ha1) hda)
      refine ⟨⟨⟨hd1, hdN⟩, hc⟩, (le_div_iff₀ hd').mpr ?_⟩
      simpa [mul_comm] using hda
  have hcomm (l : List (ℕ × ℕ)) (f : ℕ → ℕ × ℕ → ℝ) :
      (∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime R), (l.map (f d)).sum) =
        (l.map (fun ab => ∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime R), f d ab)).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp [sum_add_distrib, ih]
  have hshell : U R N = ((pairs R).map (fun ab => |(B R ab.1 : ℝ)| *
      (C R ((N : ℝ) / ab.1) - C R ((N : ℝ) / ab.2)))).sum := by
    rw [U, if_neg hRne]
    calc
      _ = ∑ d ∈ (Icc 1 N).filter (fun d => d.Coprime R),
          ((pairs R).map (fun ab => |(B R ab.1 : ℝ)| *
          ((if (ab.1 : ℝ) ≤ (N : ℝ) / d then 1 else 0) -
            (if (ab.2 : ℝ) ≤ (N : ℝ) / d then 1 else 0)))).sum := by
        apply sum_congr rfl
        intro d hd
        have hd' := mem_Icc.mp (mem_filter.mp hd).1
        apply hpoint
        exact (le_div_iff₀ (Nat.cast_pos.mpr (by omega))).mpr
          (by simpa only [one_mul] using Nat.cast_le.mpr hd'.2)
      _ = _ := by
        rw [hcomm]
        congr 1
        apply List.map_congr_left
        rintro ⟨a, b⟩ hab
        obtain ⟨ha, hb, _, _⟩ := hgap ds hsort a b hab
        rw [← mul_sum, sum_sub_distrib,
          hcount_endpoint a (Nat.pos_of_mem_divisors ((hmem a).mp ha)),
          hcount_endpoint b (Nat.pos_of_mem_divisors ((hmem b).mp hb))]
  have hindicator (d : ℕ) (hd : 0 < d) :
      (if d.Coprime R then (1 : ℝ) else 0) =
        ∑ a ∈ R.divisors, if a ∣ d then (ArithmeticFunction.moebius a : ℝ) else 0 := by
    rw [← sum_filter]
    have hg0 : d.gcd R ≠ 0 := (Nat.gcd_pos_of_pos_left R hd).ne'
    have hg : R.divisors.filter (fun a => a ∣ d) = (d.gcd R).divisors := by
      ext a
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨haR, _⟩, had⟩
        exact ⟨⟨had, haR⟩, hg0⟩
      · rintro ⟨⟨had, haR⟩, _⟩
        exact ⟨⟨haR, hR0⟩, had⟩
    rw [hg, ← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Nat.Coprime]
  have hC (x : ℝ) : C R x =
      ∑ a ∈ R.divisors, (ArithmeticFunction.moebius a : ℝ) * (⌊x / a⌋₊ : ℝ) := by
    rw [C, natCast_card_filter]
    calc
      _ = ∑ d ∈ Icc 1 ⌊x⌋₊, ∑ a ∈ R.divisors,
          if a ∣ d then (ArithmeticFunction.moebius a : ℝ) else 0 := by
        apply sum_congr rfl
        intro d hd
        exact hindicator d (by have := (mem_Icc.mp hd).1; omega)
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha
        rw [← sum_filter]
        have hi : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext k; simp; omega
        rw [hi, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div,
          Nat.floor_div_natCast]
        ring
  have hCR : C R R = R.totient := by
    rw [C, Nat.floor_natCast, Nat.totient_eq_card_coprime]
    apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
    ext d
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨hd1, hdR⟩, hc⟩
      have hne : d ≠ R := by
        rintro rfl
        exact hRne (by simpa [Nat.Coprime] using hc)
      exact ⟨by omega, hc.symm⟩
    · rintro ⟨hdR, hc⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hRne (by simpa [Nat.Coprime] using hc)
      exact ⟨⟨by omega, by omega⟩, hc.symm⟩
  have he : e R = ∑ a ∈ R.divisors, (ArithmeticFunction.moebius a : ℝ) / a := by
    have hRn : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR0
    apply (div_eq_iff hRn).mpr
    change (R.totient : ℝ) = (∑ a ∈ R.divisors,
      (ArithmeticFunction.moebius a : ℝ) / a) * R
    rw [← hCR, hC, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [Nat.floor_div_eq_div, Nat.cast_div (Nat.dvd_of_mem_divisors ha)
      (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors ha).ne')]
    ring
  have herror (x : ℝ) (hx : 0 ≤ x) : |C R x - e R * x| ≤ R.divisors.card := by
    rw [hC, he, sum_mul, ← sum_sub_distrib]
    calc
      _ ≤ ∑ a ∈ R.divisors,
          |(ArithmeticFunction.moebius a : ℝ) * (⌊x / a⌋₊ : ℝ) -
            (ArithmeticFunction.moebius a : ℝ) / a * x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ R.divisors, (1 : ℝ) := by
        apply sum_le_sum
        intro a ha
        have hmu : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
        have hf : |(⌊x / a⌋₊ : ℝ) - x / a| ≤ 1 := by
          rw [abs_sub_comm]
          exact Nat.abs_sub_floor_le (div_nonneg hx (Nat.cast_nonneg a))
        calc
          _ = |(ArithmeticFunction.moebius a : ℝ)| * |(⌊x / a⌋₊ : ℝ) - x / a| := by
            rw [← abs_mul]
            congr 1
            ring
          _ ≤ 1 * 1 := mul_le_mul hmu hf (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      _ = _ := by simp
  have hpair_error (a b : ℕ) :
      |(C R ((N : ℝ) / a) - e R * ((N : ℝ) / a)) -
        (C R ((N : ℝ) / b) - e R * ((N : ℝ) / b))| ≤ 2 * R.divisors.card := by
    calc
      _ ≤ |C R ((N : ℝ) / a) - e R * ((N : ℝ) / a)| +
          |C R ((N : ℝ) / b) - e R * ((N : ℝ) / b)| := abs_sub _ _
      _ ≤ (R.divisors.card : ℝ) + R.divisors.card :=
        add_le_add (herror _ (by positivity)) (herror _ (by positivity))
      _ = _ := by ring
  have hweighted (a b : ℕ) :
      abs (|(B R a : ℝ)| * (C R ((N : ℝ) / a) - C R ((N : ℝ) / b)) -
        e R * (|(B R a : ℝ)| * ((a : ℝ)⁻¹ - (b : ℝ)⁻¹)) * N) ≤
          2 * R.divisors.card * |(B R a : ℝ)| := by
    have hh : |(B R a : ℝ)| * (C R ((N : ℝ) / a) - C R ((N : ℝ) / b)) -
        e R * (|(B R a : ℝ)| * ((a : ℝ)⁻¹ - (b : ℝ)⁻¹)) * N =
        |(B R a : ℝ)| * ((C R ((N : ℝ) / a) - e R * ((N : ℝ) / a)) -
          (C R ((N : ℝ) / b) - e R * ((N : ℝ) / b))) := by
      simp only [div_eq_mul_inv]
      ring
    rw [hh, abs_mul, abs_abs, mul_comm (2 * (R.divisors.card : ℝ))]
    exact mul_le_mul_of_nonneg_left (hpair_error a b) (abs_nonneg _)
  have hsum : ∀ l : List (ℕ × ℕ),
      |(l.map (fun ab => |(B R ab.1 : ℝ)| *
        (C R ((N : ℝ) / ab.1) - C R ((N : ℝ) / ab.2)))).sum -
        e R * (l.map (fun ab => |(B R ab.1 : ℝ)| *
          ((ab.1 : ℝ)⁻¹ - (ab.2 : ℝ)⁻¹))).sum * N| ≤
            2 * R.divisors.card * (l.map (fun ab => |(B R ab.1 : ℝ)|)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons ab l ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        _ = |(|(B R ab.1 : ℝ)| *
            (C R ((N : ℝ) / ab.1) - C R ((N : ℝ) / ab.2)) -
            e R * (|(B R ab.1 : ℝ)| * ((ab.1 : ℝ)⁻¹ - (ab.2 : ℝ)⁻¹)) * N) +
          ((l.map (fun ab => |(B R ab.1 : ℝ)| *
            (C R ((N : ℝ) / ab.1) - C R ((N : ℝ) / ab.2)))).sum -
            e R * (l.map (fun ab => |(B R ab.1 : ℝ)| *
              ((ab.1 : ℝ)⁻¹ - (ab.2 : ℝ)⁻¹))).sum * N)| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hweighted ab.1 ab.2) ih)
        _ = _ := by ring
  rw [hshell, c, if_neg hRne]
  exact hsum (pairs R)

end D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
