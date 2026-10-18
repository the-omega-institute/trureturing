/- GID: D5/S3/Geometry/Hyperideal/CriticalIncidenceStar
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CriticalIncidenceStar
   mirror-E: none(waiver:finite-incidence-continuous-star-bound)
   anchors: []
   utility: none
   digest: Separate exact curvature margins on both faces of a critical global edge star. -/

import D5.S3.Geometry.Hyperideal.CriticalTransitionStar
import D5.S3.Geometry.Hyperideal.FourCycleCurvature
import Mathlib.Tactic

/-!
The star is the fibre of an actual global edge label. Repeated tetrahedra and
neighbour labels remain separate local occurrences in its finite sum. The same
global coordinate function is used on either face of the length box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.CriticalIncidenceStar
open D5.S3.Geometry.Hyperideal.CriticalTransitionStar
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

variable {T E : Type*} [Fintype T] [DecidableEq E]

def ThreeHigh (s : Incidence T E) (a : T × Fin 6) : Prop :=
  let high j := s.low (coordinate s a j) = false
  (high 1 ∧ high 2 ∧ high 4) ∨
  (high 1 ∧ high 2 ∧ high 5) ∨
  (high 1 ∧ high 4 ∧ high 5) ∨
  (high 2 ∧ high 4 ∧ high 5)

def FourHigh (s : Incidence T E) (a : T × Fin 6) : Prop :=
  s.low (coordinate s a 1) = false ∧
  s.low (coordinate s a 2) = false ∧
  s.low (coordinate s a 4) = false ∧
  s.low (coordinate s a 5) = false

/-- The two curvature faces have their separate sharp star budgets, evaluated
on a single global edge-label box. -/
theorem critical_incidence_face_bounds
    (s : Incidence T E) (critical : E → Prop) (e : E)
    (good : Finset {a : T × Fin 6 // a ∈ star s e})
    (hgood : 4 ≤ good.card)
    (hcritical : ∀ f, critical f → s.low f = true ∧ degree s f = 6)
    (hecritical : critical e)
    (hthree : ∀ i : {a : T × Fin 6 // a ∈ star s e}, ThreeHigh s i.1)
    (hfavourable : ∀ i ∈ good,
      FourHigh s i.1 ∧ critical (coordinate s i.1 3))
    (x : E → ℝ)
    (hbox : ∀ f, x f ∈ Set.Icc 1 2 ∧
      (s.low f = false → x f ≤ 5/4) ∧ (critical f → 4/3 ≤ x f)) :
    (x e = 4/3 → 2*Real.pi - 6*Real.arccos (4/7) ≤ curvature s x e) ∧
    (x e = 2 → curvature s x e ≤ -(4*gamma + 2*beta - 2*Real.pi)) := by
  classical
  let I := {a : T × Fin 6 // a ∈ star s e}
  let y : I → ℝ := fun i => x (coordinate s i.1 1)
  let z : I → ℝ := fun i => x (coordinate s i.1 2)
  let o : I → ℝ := fun i => x (coordinate s i.1 3)
  let v : I → ℝ := fun i => x (coordinate s i.1 4)
  let w : I → ℝ := fun i => x (coordinate s i.1 5)
  have hdegree : degree s e = 6 := (hcritical e hecritical).2
  have hcard : Fintype.card I = 6 := by
    simpa [I, degree] using hdegree
  have hlocalbox : ∀ i, y i ∈ Set.Icc 1 2 ∧ z i ∈ Set.Icc 1 2 ∧
      o i ∈ Set.Icc 1 2 ∧ v i ∈ Set.Icc 1 2 ∧ w i ∈ Set.Icc 1 2 := by
    intro i
    exact ⟨(hbox _).1, (hbox _).1, (hbox _).1, (hbox _).1, (hbox _).1⟩
  have hsmall : ∀ i, ThreeSmall (y i) (z i) (v i) (w i) := by
    intro i
    rcases hthree i with ⟨h1,h2,h4⟩ | ⟨h1,h2,h5⟩ |
      ⟨h1,h4,h5⟩ | ⟨h2,h4,h5⟩
    · exact Or.inl ⟨(hbox _).2.1 h1, (hbox _).2.1 h2, (hbox _).2.1 h4⟩
    · exact Or.inr (Or.inl ⟨(hbox _).2.1 h1, (hbox _).2.1 h2,
        (hbox _).2.1 h5⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(hbox _).2.1 h1,
        (hbox _).2.1 h4, (hbox _).2.1 h5⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨(hbox _).2.1 h2,
        (hbox _).2.1 h4, (hbox _).2.1 h5⟩))
  have hpaired : ∀ i ∈ good, y i ≤ 5/4 ∧ z i ≤ 5/4 ∧
      v i ≤ 5/4 ∧ w i ≤ 5/4 ∧ 4/3 ≤ o i := by
    intro i hi
    obtain ⟨⟨h1,h2,h4,h5⟩,hop⟩ := hfavourable i hi
    exact ⟨(hbox _).2.1 h1, (hbox _).2.1 h2, (hbox _).2.1 h4,
      (hbox _).2.1 h5, (hbox _).2.2 hop⟩
  have htarget (i : I) : coordinate s i.1 0 = e := by
    have hi : source s i.1 = e := (Finset.mem_filter.mp i.2).2
    have hframe : coordinate s i.1 0 = source s i.1 := by
      rcases i.1 with ⟨t,j⟩
      fin_cases j <;> rfl
    exact hframe.trans hi
  have hsum (f : T × Fin 6 → ℝ) :
      (∑ i : I, f i.1) = ∑ a ∈ star s e, f a := by
    exact Finset.sum_coe_sort (star s e) f
  have quotient_le : ∀ (A B P q : ℝ), 0 < A → 0 < B → 0 ≤ q →
      P ^ 2 ≤ q ^ 2 * (A * B) → P / Real.sqrt A / Real.sqrt B ≤ q := by
    intro A B P q hA hB hq hs
    let r := Real.sqrt A * Real.sqrt B
    have hr : 0 < r := mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
    have hrsq : r^2 = A*B := by
      dsimp [r]
      rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    rw [div_div]
    change P/r ≤ q
    apply (div_le_iff₀ hr).2
    apply le_of_sq_le_sq
    · rw [mul_pow, hrsq]
      exact hs
    · exact mul_nonneg hq hr.le
  have hc1 : (1:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hc2 : (2:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hch : (5/4:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hca : (4/3:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have cmp := cosine_mixed_comparison
  let q : ℝ := 49 / Real.sqrt 6534
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqsq : q^2 = (2401:ℝ)/6534 := by
    dsimp [q]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6534)]
    norm_num
  have hqle : q ≤ 1 := by nlinarith
  have hqgamma : (43:ℝ)/99 ≤ q := by nlinarith
  have hbg : beta ≤ gamma := Real.arccos_le_arccos hqgamma
  have hlo : ∀ i, (4:ℝ)/7 ≤ cosine (4/3) (y i) (z i) (o i) (v i) (w i) := by
    intro i
    obtain ⟨hy,hz,ho,hv,hw⟩ := hlocalbox i
    have hh := cmp (4/3) 1 1 2 1 1 (y i) (z i) (o i) (v i) (w i)
      hca hc1 hc1 hc2 hc1 hc1 hy hz ho hv hw hy.1 hz.1 ho.2 hv.1 hw.1
    have he : cosine (4/3) 1 1 2 1 1 = (4:ℝ)/7 := by
      have hA : rad (4/3) 1 1 = (49:ℝ)/9 := by norm_num [rad]
      have hP : numerator (4/3) 1 1 2 1 1 = (28:ℝ)/9 := by norm_num [numerator]
      rw [cosine, hA, hP, div_div, ← pow_two,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 49/9)]
      norm_num
    simpa only [he] using hh
  have hregular : ∀ i, cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ q := by
    intro i
    obtain ⟨hy,hz,ho,hv,hw⟩ := hlocalbox i
    rcases hsmall i with ⟨hyb,hzb,hvb⟩ | ⟨hyb,hzb,hwb⟩ |
      ⟨hyb,hvb,hwb⟩ | ⟨hzb,hvb,hwb⟩
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 (5/4) (5/4) 1 (5/4) 2 :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) (5/4) 1 (5/4) 2
            hc2 hy hz ho hv hw hch hch hc1 hch hc2 hyb hzb ho.1 hvb hw.2
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 (5/4) (5/4) 1 2 (5/4) :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) (5/4) 1 2 (5/4)
            hc2 hy hz ho hv hw hch hch hc1 hc2 hch hyb hzb ho.1 hv.2 hwb
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 (5/4) 2 1 (5/4) (5/4) :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) 2 1 (5/4) (5/4)
            hc2 hy hz ho hv hw hch hc2 hc1 hch hch hyb hz.2 ho.1 hvb hwb
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 2 (5/4) 1 (5/4) (5/4) :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) 2 (5/4) 1 (5/4) (5/4)
            hc2 hy hz ho hv hw hc2 hch hc1 hch hch hy.2 hzb ho.1 hvb hwb
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
  have hfavourableBound : ∀ i ∈ good,
      cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ (43:ℝ)/99 := by
    intro i hi
    obtain ⟨hy,hz,ho,hv,hw⟩ := hlocalbox i
    obtain ⟨hyb,hzb,hvb,hwb,hoa⟩ := hpaired i hi
    have hh := cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) (5/4) (4/3) (5/4) (5/4)
      hc2 hy hz ho hv hw hch hch hca hch hch hyb hzb hoa hvb hwb
    have he : cosine 2 (5/4) (5/4) (4/3) (5/4) (5/4) = (43:ℝ)/99 := by
      have hA : rad 2 (5/4) (5/4) = (99:ℝ)/8 := by norm_num [rad]
      have hP : numerator 2 (5/4) (5/4) (4/3) (5/4) (5/4) = (43:ℝ)/8 := by
        norm_num [numerator]
      rw [cosine, hA, hP, div_div, ← pow_two,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 99/8)]
      norm_num
    simpa only [he] using hh
  have hlowerSum : (∑ i : I, Real.arccos
      (cosine (4/3) (y i) (z i) (o i) (v i) (w i))) ≤ 6*Real.arccos (4/7) := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Real.arccos_le_arccos (hlo i))
    simpa [hcard, nsmul_eq_mul] using hh
  have hupperSum : 4*gamma+2*beta ≤
      ∑ i : I, Real.arccos (cosine 2 (y i) (z i) (o i) (v i) (w i)) := by
    have hh : (∑ i : I, (beta + if i ∈ good then gamma-beta else 0)) ≤
        ∑ i : I, Real.arccos (cosine 2 (y i) (z i) (o i) (v i) (w i)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ good
      · simp only [hi, if_true]
        have ha : gamma ≤ Real.arccos (cosine 2 (y i) (z i) (o i) (v i) (w i)) :=
          Real.arccos_le_arccos (hfavourableBound i hi)
        linarith
      · simp only [hi, if_false, add_zero]
        exact Real.arccos_le_arccos (hregular i)
    have he : (∑ i : I, (beta + if i ∈ good then gamma-beta else 0)) =
        6*beta + (good.card:ℝ)*(gamma-beta) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_mem, hcard, nsmul_eq_mul]
      ring
    rw [he] at hh
    have hfour : (4:ℝ) ≤ good.card := by exact_mod_cast hgood
    have hprod := mul_nonneg (sub_nonneg.mpr hfour) (sub_nonneg.mpr hbg)
    nlinarith
  constructor
  · intro he
    have hsumLower : (∑ i : I, angle s x i.1) ≤ 6*Real.arccos (4/7) := by
      convert hlowerSum using 1
      apply Finset.sum_congr rfl
      intro i _
      simp [angle, localCosine, ← he, htarget i, y, z, o, v, w]
    rw [curvature, ← hsum (angle s x)]
    linarith
  · intro he
    have hsumUpper : 4*gamma+2*beta ≤ ∑ i : I, angle s x i.1 := by
      convert hupperSum using 1
      apply Finset.sum_congr rfl
      intro i _
      simp [angle, localCosine, ← he, htarget i, y, z, o, v, w]
    rw [curvature, ← hsum (angle s x)]
    linarith

#print axioms critical_incidence_face_bounds
end D5.S3.Geometry.Hyperideal.CriticalIncidenceStar
