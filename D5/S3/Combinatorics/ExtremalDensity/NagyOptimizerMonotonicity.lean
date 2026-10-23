/- GID: D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: The optimal T-parameter need not increase with edge density. -/

/-
admission_basis: open-problem-resolution (#15853; Refuted)
Direct dependencies frozen on the protected base: none.
Same-delivery dependency: D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.
DTR reading: DTR-Unregistered (Observe) for every public theorem in this module.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15978.
The public result is an audit target: utility: none supplies no refutation exemption.
Its graph-dependent monotone-selection negation has no faithful enrolled readout with
the required source reconstruction, variation, sensitivity and observational dependence.
The rational coordinate is used for 0 < s <= 1/100, with 1-s*x != 0 explicit.
The claim uses the literal homomorphism limit and the weakest monotone-selection reading.
Definitions are bind-only encodings consumed by the named mathematical steps.
octic_hasDeriv: proof_shape: bind-only; escape_witness: none; consumers: octic_strictMonoOn.
octic_root_signs: proof_shape: bind-only; escape_witness: none; consumers: max_interval_one,
max_interval_two, max_interval_open_one, max_interval_open_two.
coord_interval_order: proof_shape: bind-only; escape_witness: none; consumers:
maximisers_reversed.
test_point_values: proof_shape: bind-only; escape_witness: none; consumers: max_interval_one,
max_interval_two.
octic_deriv_positive: proof_shape: bind-only; escape_witness: none; consumers:
octic_strictMonoOn.
octic_strictMonoOn: proof_shape: bind-only; escape_witness: none; consumers:
fCoord_strictMono_left, fCoord_strictAnti_right, max_unique_one, max_unique_two.
qCoord_hasDeriv: proof_shape: bind-only; escape_witness: none; consumers: coord_strictMonoOn,
coord_root_of_max.
coord_strictMonoOn: proof_shape: bind-only; escape_witness: none; consumers: weights_of_coord,
maximisers_reversed, max_coord_root_one, max_coord_root_two.
colour_condition_iff: proof_shape: bind-only; escape_witness: none; consumers:
h3_admissible_iff.
h3_admissible_iff: proof_shape: bind-only; escape_witness: none; consumers: density_h3.
sum_fin_fun: proof_shape: bind-only; escape_witness: none; consumers: sum_fin_seven.
h3_fixed_core: proof_shape: bind-only; escape_witness: none; consumers: h3Poly_closed.
sum_fin_seven: proof_shape: bind-only; escape_witness: none; consumers: h3Poly_closed.
h3Poly_closed: proof_shape: bind-only; escape_witness: none; consumers: density_h3.
weights_edge_density: proof_shape: bind-only; escape_witness: none; consumers: xFrom_properties,
density_h3.
xFrom_properties: proof_shape: bind-only; escape_witness: none; consumers: weights_of_coord,
density_xFrom, max_interval_one, max_interval_two, max_unique_one, max_unique_two.
weights_of_coord: proof_shape: bind-only; escape_witness: none; consumers: fCoord_low_bound,
density_coord.
fCoord_eq_rationalF: proof_shape: bind-only; escape_witness: none; consumers: fCoord_hasDeriv.
fNumerator_hasDeriv: proof_shape: bind-only; escape_witness: none; consumers: fCoord_hasDeriv.
fCoord_hasDeriv: proof_shape: bind-only; escape_witness: none; consumers:
fCoord_strictMono_left, fCoord_strictAnti_right, coord_root_of_max.
d3_nonneg_bound: proof_shape: bind-only; escape_witness: none; consumers: fCoord_low_bound.
fCoord_low_bound: proof_shape: bind-only; escape_witness: none; consumers:
coord_interval_for_max.
fCoord_strictMono_left: proof_shape: bind-only; escape_witness: none; consumers:
coord_interval_for_max.
fCoord_strictAnti_right: proof_shape: bind-only; escape_witness: none; consumers:
coord_interval_for_max.
coord_interval_for_max: proof_shape: bind-only; escape_witness: none; consumers:
max_interval_one, max_interval_two.
coord_root_of_max: proof_shape: bind-only; escape_witness: none; consumers: max_coord_root_one,
max_coord_root_two.
rawWeight_eq: proof_shape: bind-only; escape_witness: none; consumers: density_h3.
density_h3: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: density_coord,
density_continuous.
density_coord: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: density_xFrom,
maximise_coord.
density_xFrom: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: maximise_coord.
maximise_coord: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: max_interval_one,
max_interval_two, max_coord_root_one, max_coord_root_two.
max_interval_one: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: maximisers_reversed,
max_coord_root_one, max_interval_open_one.
max_interval_two: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: maximisers_reversed,
max_coord_root_two, max_interval_open_two.
maximisers_reversed: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: result.
density_continuous: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: max_exists.
max_exists: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: unique_max_one,
unique_max_two.
max_coord_root_one: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers:
max_interval_open_one, max_unique_one.
max_coord_root_two: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers:
max_interval_open_two, max_unique_two.
max_interval_open_one: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: max_unique_one.
max_interval_open_two: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: max_unique_two.
max_unique_one: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: unique_max_one.
max_unique_two: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: unique_max_two.
unique_max_one: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: result.
unique_max_two: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound; consumers: result.
result: proof_shape: content; escape_witness: ThreeClassHomomorphismLimit.bad_count_bound;
consumers: external settlement.
-/

import D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
open Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Combinatorics.ExtremalDensity.NagyOptimizerMonotonicity
open D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit
attribute [local instance] Classical.propDecidable

def claim : Prop := ∀ (v : ℕ) (G : SimpleGraph (Fin v)), ∃ qf : ℝ → ℝ,
  (∀ beta ∈ Set.Icc (0 : ℝ) 1, qf beta ∈ Set.Icc (0 : ℝ) 1 ∧
    IsMaxOn (tDens G beta) (Set.Icc 0 1) (qf beta)) ∧
  MonotoneOn qf (Set.Icc 0 1)

private def qCoord (s x : ℝ) : ℝ := x - s*(1-x^2)/(2*(1-s*x))
private def rCoord (s x : ℝ) : ℝ := s^2*(1-x^2)/(2*(1-s*x))
private def d3 (r y b beta : ℝ) : ℝ :=
  r*(r+y)^3 + 3*b*r^3 + y*(r+y)^6 + 2*b*y*r^2*(r+y)^3 + b*r^4*beta

private def fCoord (s x : ℝ) : ℝ :=
  d3 (rCoord s x) (s*x-rCoord s x) (1-s*x) (s^2) / s^5

private def octic (s x : ℝ) : ℝ :=
  28*s^5*x^8 - 104*s^4*x^7 + (27*s^5+132*s^3)*x^6 -
  (74*s^4+48*s^2)*x^5 + (-3*s^5+44*s^3-28*s)*x^4 +
  (28*s^4+12*s^2+20)*x^3 - (7*s^5+16*s^3)*x^2 -
  (2*s^4+12*s^2+12)*x + 3*s^5+12*s

private def octicDeriv (s x : ℝ) : ℝ :=
  224*s^5*x^7 - 728*s^4*x^6 + 6*(27*s^5+132*s^3)*x^5 -
  5*(74*s^4+48*s^2)*x^4 + 4*(-3*s^5+44*s^3-28*s)*x^3 +
  3*(28*s^4+12*s^2+20)*x^2 - 2*(7*s^5+16*s^3)*x -
  (2*s^4+12*s^2+12)

private theorem octic_hasDeriv (s x : ℝ) : HasDerivAt (octic s) (octicDeriv s x) x := by
  unfold octic octicDeriv
  convert! ((((((((((((hasDerivAt_id x).pow 8).const_mul (28*s^5)).sub (((hasDerivAt_id x).pow 7).const_mul (104*s^4))).add (((hasDerivAt_id x).pow 6).const_mul (27*s^5+132*s^3))).sub (((hasDerivAt_id x).pow 5).const_mul (74*s^4+48*s^2))).add (((hasDerivAt_id x).pow 4).const_mul (-3*s^5+44*s^3-28*s))).add (((hasDerivAt_id x).pow 3).const_mul (28*s^4+12*s^2+20))).sub (((hasDerivAt_id x).pow 2).const_mul (7*s^5+16*s^3))).sub ((hasDerivAt_id x).const_mul (2*s^4+12*s^2+12))).add_const (3*s^5)).add_const (12*s)) using 1 <;> norm_num <;> ring

private theorem octic_root_signs :
    octic (1/1000) (77451/100000) < 0 ∧ 0 < octic (1/1000) (77452/100000) ∧
    octic (1/100) (77384/100000) < 0 ∧ 0 < octic (1/100) (77385/100000) := by
  norm_num [octic]

private theorem coord_interval_order :
    (7743/10000 : ℝ) < qCoord (1/1000) (77451/100000) ∧
    qCoord (1/100) (77385/100000) < 7719/10000 := by
  norm_num [qCoord]

private theorem test_point_values :
    (9/100 : ℝ) < fCoord (1/1000) (3/4) ∧
    (9/100 : ℝ) < fCoord (1/100) (3/4) := by
  norm_num [fCoord,d3,rCoord]

private theorem octic_deriv_positive (s x : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hx : x ∈ Set.Icc (1/2 : ℝ) 1) : 0 < octicDeriv s x := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have xp (k : ℕ) : x^k ≤ 1 := pow_le_one₀ hx0 hx.2
  have sp (k : ℕ) : s^k ≤ (1/100 : ℝ)^k := pow_le_pow_left₀ hs.le hs1 k
  have b46 : s^4*x^6 ≤ s^4 := mul_le_of_le_one_right (pow_nonneg hs.le _) (xp 6)
  have b44 : s^4*x^4 ≤ s^4 := mul_le_of_le_one_right (pow_nonneg hs.le _) (xp 4)
  have b24 : s^2*x^4 ≤ s^2 := mul_le_of_le_one_right (pow_nonneg hs.le _) (xp 4)
  have b53 : s^5*x^3 ≤ s^5 := mul_le_of_le_one_right (pow_nonneg hs.le _) (xp 3)
  have b13 : s*x^3 ≤ s := mul_le_of_le_one_right hs.le (xp 3)
  have b51 : s^5*x ≤ s^5 := mul_le_of_le_one_right (pow_nonneg hs.le _) hx.2
  have b31 : s^3*x ≤ s^3 := mul_le_of_le_one_right (pow_nonneg hs.le _) hx.2
  have p57 : 0 ≤ s^5*x^7 := mul_nonneg (pow_nonneg hs.le _) (pow_nonneg hx0 _)
  have p55 : 0 ≤ s^5*x^5 := mul_nonneg (pow_nonneg hs.le _) (pow_nonneg hx0 _)
  have p35 : 0 ≤ s^3*x^5 := mul_nonneg (pow_nonneg hs.le _) (pow_nonneg hx0 _)
  have p33 : 0 ≤ s^3*x^3 := mul_nonneg (pow_nonneg hs.le _) (pow_nonneg hx0 _)
  have p42 : 0 ≤ s^4*x^2 := mul_nonneg (pow_nonneg hs.le _) (pow_nonneg hx0 _)
  have p22 : 0 ≤ s^2*x^2 := mul_nonneg (pow_nonneg hs.le _) (pow_nonneg hx0 _)
  have hx2 : 1/4 ≤ x^2 := by nlinarith [hx.1]
  have hb : 3-112*s-252*s^2-32*s^3-1100*s^4-26*s^5 ≤ octicDeriv s x := by
    dsimp [octicDeriv]
    nlinarith only [b46,b44,b24,b53,b13,b51,b31,p57,p55,p35,p33,p42,p22,hx2]
  have hsp2 := sp 2
  have hsp3 := sp 3
  have hsp4 := sp 4
  have hsp5 := sp 5
  norm_num at hsp2 hsp3 hsp4 hsp5
  linarith

private theorem octic_strictMonoOn (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100) :
    StrictMonoOn (octic s) (Set.Icc (1/2 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold octic; fun_prop)
  intro x hx
  rw [octic_hasDeriv s x |>.deriv]
  exact octic_deriv_positive s x hs hs1 (interior_subset hx)

private theorem qCoord_hasDeriv (s x : ℝ) (h : 1-s*x ≠ 0) :
    HasDerivAt (qCoord s) (((1-s*x)^2+1-s^2)/(2*(1-s*x)^2)) x := by
  unfold qCoord
  have hnum := (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).const_mul s)
  have hden := (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul s)).const_mul 2)
  have hh := (hasDerivAt_id x).sub (hnum.div hden (by exact mul_ne_zero (by norm_num) h))
  convert! hh using 1
  norm_num
  field_simp
  ring

private theorem coord_strictMonoOn (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100) :
    StrictMonoOn (qCoord s) (Set.Icc (0 : ℝ) 1) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < 1-s*x := by nlinarith [hx.1,hx.2]
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro x hx
    exact (qCoord_hasDeriv s x (ne_of_gt (hd x hx))).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    rw [(qCoord_hasDeriv s x (ne_of_gt (hd x hx'))).deriv]
    apply div_pos
    · nlinarith [sq_nonneg (1-s*x)]
    · exact mul_pos (by norm_num) (pow_pos (hd x hx') 2)

private def h3Edge (i j : Fin 7) : Prop :=
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
  (i.val = 0 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 4) ∨
  (i.val = 3 ∧ j.val = 5) ∨ (i.val = 3 ∧ j.val = 6)

private def h3 : SimpleGraph (Fin 7) := SimpleGraph.fromRel h3Edge

private def h3ColourAdmissible (c : Fin 7 → Fin 3) : Prop :=
  (c 0).val + (c 1).val ≤ 2 ∧ (c 1).val + (c 2).val ≤ 2 ∧
  (c 2).val + (c 0).val ≤ 2 ∧ (c 0).val + (c 3).val ≤ 2 ∧
  (c 3).val + (c 4).val ≤ 2 ∧ (c 3).val + (c 5).val ≤ 2 ∧
  (c 3).val + (c 6).val ≤ 2

private theorem colour_condition_iff (a b : Fin 3) :
    independentWeight a + independentWeight b ≤ 1 ↔ a.val + b.val ≤ 2 := by
  fin_cases a <;> fin_cases b <;> norm_num [independentWeight]

private theorem h3_admissible_iff (c : Fin 7 → Fin 3) :
    admissible h3 c ↔ h3ColourAdmissible c := by
  unfold admissible h3ColourAdmissible
  simp_rw [colour_condition_iff]
  constructor
  · intro h
    exact ⟨h 0 1 (by simp [h3,h3Edge]), h 1 2 (by simp [h3,h3Edge]),
      h 2 0 (by simp [h3,h3Edge]), h 0 3 (by simp [h3,h3Edge]),
      h 3 4 (by simp [h3,h3Edge]), h 3 5 (by simp [h3,h3Edge]),
      h 3 6 (by simp [h3,h3Edge])⟩
  · rintro ⟨h01,h12,h20,h03,h34,h35,h36⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [h3,h3Edge] <;> omega

private def rawWeight (r y b : ℝ) (a : Fin 3) : ℝ :=
  if a.val = 0 then r else if a.val = 1 then y else b

private def h3Poly (r y b : ℝ) : ℝ :=
  ∑ c : Fin 7 → Fin 3, if h3ColourAdmissible c then ∏ i, rawWeight r y b (c i) else 0

private theorem sum_fin_fun {n : ℕ} (f : (Fin (n+1) → Fin 3) → ℝ) :
    ∑ c, f c = ∑ a : Fin 3, ∑ t : Fin n → Fin 3, f (Fin.cons a t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 3)).sum_comp f]
  exact Fintype.sum_prod_type _

set_option maxHeartbeats 1000000 in
 private theorem h3_fixed_core (r y b : ℝ) (a bb cc d : Fin 3) :
    (∑ t : Fin 3 → Fin 3,
      if h3ColourAdmissible (Fin.cons a (Fin.cons bb (Fin.cons cc (Fin.cons d t))))
      then ∏ i, rawWeight r y b ((Fin.cons a (Fin.cons bb (Fin.cons cc (Fin.cons d t))) : Fin 7 → Fin 3) i) else 0) =
    if a.val+bb.val ≤ 2 ∧ bb.val+cc.val ≤ 2 ∧ cc.val+a.val ≤ 2 ∧ a.val+d.val ≤ 2
    then rawWeight r y b a * rawWeight r y b bb * rawWeight r y b cc * rawWeight r y b d *
      (if d.val = 0 then r+y+b else if d.val = 1 then r+y else r)^3 else 0 := by
  let C := a.val+bb.val ≤ 2 ∧ bb.val+cc.val ≤ 2 ∧ cc.val+a.val ≤ 2 ∧ a.val+d.val ≤ 2
  let K := rawWeight r y b a * rawWeight r y b bb * rawWeight r y b cc * rawWeight r y b d
  let L := fun u : Fin 3 => if d.val+u.val ≤ 2 then rawWeight r y b u else 0
  have ht (t : Fin 3 → Fin 3) :
      (if h3ColourAdmissible (Fin.cons a (Fin.cons bb (Fin.cons cc (Fin.cons d t))))
      then ∏ i, rawWeight r y b ((Fin.cons a (Fin.cons bb (Fin.cons cc (Fin.cons d t))) : Fin 7 → Fin 3) i) else 0) =
      if C then K * ∏ i, L (t i) else 0 := by
    have hColor : h3ColourAdmissible (Fin.cons a (Fin.cons bb (Fin.cons cc (Fin.cons d t)))) ↔
        C ∧ d.val+(t 0).val ≤ 2 ∧ d.val+(t 1).val ≤ 2 ∧ d.val+(t 2).val ≤ 2 := by
      simp only [h3ColourAdmissible,C,and_assoc]
      rfl
    rw [hColor]
    simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    by_cases hC : C <;> by_cases h0 : d.val+(t 0).val ≤ 2 <;>
      by_cases h1 : d.val+(t 1).val ≤ 2 <;> by_cases h2 : d.val+(t 2).val ≤ 2 <;>
      simp [hC,h0,h1,h2,L,K,Fin.prod_univ_three] <;> ring
  simp_rw [ht]
  by_cases hC : C
  · simp only [hC,if_pos,←Finset.mul_sum]
    rw [← Fintype.prod_sum]
    have hL : ∑ u : Fin 3, L u = if d.val = 0 then r+y+b else if d.val = 1 then r+y else r := by
      fin_cases d <;> simp [L,rawWeight,Fin.sum_univ_three]
    simp_rw [hL]
    simp only [Fin.prod_const]
    simp only [←show C = (a.val+bb.val ≤ 2 ∧ bb.val+cc.val ≤ 2 ∧ cc.val+a.val ≤ 2 ∧ a.val+d.val ≤ 2) from rfl,hC,if_pos]
    rfl
  · simp [←show C = (a.val+bb.val ≤ 2 ∧ bb.val+cc.val ≤ 2 ∧ cc.val+a.val ≤ 2 ∧ a.val+d.val ≤ 2) from rfl,hC]

private theorem sum_fin_seven (f : (Fin 7 → Fin 3) → ℝ) :
    ∑ c, f c = ∑ a : Fin 3, ∑ bb : Fin 3, ∑ cc : Fin 3, ∑ d : Fin 3,
      ∑ t : Fin 3 → Fin 3, f (Fin.cons a (Fin.cons bb (Fin.cons cc (Fin.cons d t)))) := by
  rw [sum_fin_fun]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_fin_fun]
  apply Finset.sum_congr rfl
  intro bb _
  rw [sum_fin_fun]
  apply Finset.sum_congr rfl
  intro cc _
  rw [sum_fin_fun]

set_option maxHeartbeats 3000000 in
 private theorem h3Poly_closed (r y b : ℝ) :
    h3Poly r y b = (r*(r+y)^3+3*b*r^3)*(r+y+b)^3 +
      y*(r+y)^6 + 2*b*y*r^2*(r+y)^3 + b*r^4*((r+y)^2+2*b*r) := by
  unfold h3Poly
  rw [sum_fin_seven]
  simp_rw [h3_fixed_core]
  simp [Fin.sum_univ_three,rawWeight]
  ring

private theorem weights_edge_density (beta q : ℝ) (hb : beta ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) :
    (rW beta q+yW beta q)^2+2*bW beta q*rW beta q = beta := by
  obtain ⟨hy,hr,hb0,hSum⟩ := weights_valid beta q hb hq
  have hq2 : q^2 ≤ 1 := by nlinarith [hq.1,hq.2]
  have hArg : 0 ≤ 1-beta*(1-q^2) := by nlinarith [hb.1,hb.2,sq_nonneg q]
  have hS := Real.sq_sqrt hb.1
  have hR := Real.sq_sqrt hArg
  dsimp [rW,yW,bW]
  nlinarith [hS,hR]

private def xFrom (s q : ℝ) : ℝ := (rW (s^2) q+yW (s^2) q)/s

private theorem xFrom_properties (s q : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hq : q ∈ Set.Icc 0 1) :
    xFrom s q ∈ Set.Icc (0 : ℝ) 1 ∧
    rW (s^2) q = rCoord s (xFrom s q) ∧ qCoord s (xFrom s q) = q := by
  have hb : s^2 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> nlinarith
  have hS : Real.sqrt (s^2) = s := Real.sqrt_sq hs.le
  obtain ⟨hy,hr,hb0,hSum⟩ := weights_valid (s^2) q hb hq
  have he := weights_edge_density (s^2) q hb hq
  have hz0 : 0 ≤ rW (s^2) q+yW (s^2) q := add_nonneg hr hy
  have hz1 : rW (s^2) q+yW (s^2) q ≤ s := by
    nlinarith [mul_nonneg hb0 hr]
  have hx : xFrom s q ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hz0 hs.le
    · exact (div_le_iff₀ hs).mpr (by simpa [xFrom] using hz1)
  have hz : s*xFrom s q = rW (s^2) q+yW (s^2) q := by
    dsimp [xFrom];field_simp
  have hden : 0 < 1-s*xFrom s q := by nlinarith [hx.1,hx.2]
  have heR : rW (s^2) q = rCoord s (xFrom s q) := by
    unfold rCoord
    apply (eq_div_iff (mul_ne_zero (by norm_num) (ne_of_gt hden))).mpr
    nlinarith [he,hSum,hz]
  refine ⟨hx,heR,?_⟩
  unfold qCoord
  have hy' : yW (s^2) q = s*q := by simp [yW,hS]
  have hr' : rW (s^2) q/s = s*(1-xFrom s q^2)/(2*(1-s*xFrom s q)) := by
    rw [heR];dsimp [rCoord];field_simp <;> ring
  rw [←hr']
  nlinarith [hz,hy',div_mul_cancel₀ (rW (s^2) q) (ne_of_gt hs)]

private theorem weights_of_coord (s x : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hq : qCoord s x ∈ Set.Icc (0 : ℝ) 1) :
    rW (s^2) (qCoord s x) = rCoord s x ∧
    yW (s^2) (qCoord s x) = s*x-rCoord s x ∧
    bW (s^2) (qCoord s x) = 1-s*x := by
  obtain ⟨hx',hr',hq'⟩ := xFrom_properties s (qCoord s x) hs hs1 hq
  have heq : xFrom s (qCoord s x) = x :=
    (coord_strictMonoOn s hs hs1).injOn hx' hx hq'
  rw [heq] at hr'
  have hS := Real.sqrt_sq hs.le
  have hy : yW (s^2) (qCoord s x) = s*x-rCoord s x := by
    dsimp [yW,qCoord,rCoord];rw [hS];field_simp <;> ring
  refine ⟨hr',hy,?_⟩
  dsimp [bW,rW,yW] at *
  linarith

private def fNumerator (s x : ℝ) : ℝ :=
  4*s^5*x^10+11*s^5*x^8+8*s^5*x^6-10*s^5*x^4+4*s^5*x^2-s^5-
  20*s^4*x^9-36*s^4*x^7+4*s^4*x^5+4*s^4*x^3+
  32*s^3*x^8+24*s^3*x^6-8*s^3*x^4-14*s^2*x^7+10*s^2*x^5-
  18*s^2*x^3+6*s^2*x-10*s*x^6-2*s*x^4+18*s*x^2-6*s+8*x^5-8*x^3

private def rationalF (s x : ℝ) : ℝ := fNumerator s x / (16*(s*x-1)^3)

private theorem fCoord_eq_rationalF (s x : ℝ) (hs : s ≠ 0) (h : 1-s*x ≠ 0) :
    fCoord s x = rationalF s x := by
  unfold fCoord d3 rCoord rationalF fNumerator
  have h' : s*x-1 ≠ 0 := by intro he; apply h; linarith
  field_simp [hs,h,h']
  ring

private def fNumeratorDeriv (s x : ℝ) : ℝ := (4*s^5)*10*x^9+(11*s^5)*8*x^7+(8*s^5)*6*x^5-(10*s^5)*4*x^3+(4*s^5)*2*x^1-(20*s^4)*9*x^8-(36*s^4)*7*x^6+(4*s^4)*5*x^4+(4*s^4)*3*x^2+(32*s^3)*8*x^7+(24*s^3)*6*x^5-(8*s^3)*4*x^3-(14*s^2)*7*x^6+(10*s^2)*5*x^4-(18*s^2)*3*x^2+(6*s^2)*1*x^0-(10*s)*6*x^5-(2*s)*4*x^3+(18*s)*2*x^1+(8)*5*x^4-(8)*3*x^2

private theorem fNumerator_hasDeriv (s x : ℝ) :
    HasDerivAt (fNumerator s) (fNumeratorDeriv s x) x := by
  unfold fNumerator fNumeratorDeriv
  convert! (((((((((((((((((((((((((hasDerivAt_id x).pow 10).const_mul (4*s^5)).add (((hasDerivAt_id x).pow 8).const_mul (11*s^5))).add (((hasDerivAt_id x).pow 6).const_mul (8*s^5))).sub (((hasDerivAt_id x).pow 4).const_mul (10*s^5))).add (((hasDerivAt_id x).pow 2).const_mul (4*s^5))).sub (hasDerivAt_const x (s^5))).sub (((hasDerivAt_id x).pow 9).const_mul (20*s^4))).sub (((hasDerivAt_id x).pow 7).const_mul (36*s^4))).add (((hasDerivAt_id x).pow 5).const_mul (4*s^4))).add (((hasDerivAt_id x).pow 3).const_mul (4*s^4))).add (((hasDerivAt_id x).pow 8).const_mul (32*s^3))).add (((hasDerivAt_id x).pow 6).const_mul (24*s^3))).sub (((hasDerivAt_id x).pow 4).const_mul (8*s^3))).sub (((hasDerivAt_id x).pow 7).const_mul (14*s^2))).add (((hasDerivAt_id x).pow 5).const_mul (10*s^2))).sub (((hasDerivAt_id x).pow 3).const_mul (18*s^2))).add ((hasDerivAt_id x).const_mul (6*s^2))).sub (((hasDerivAt_id x).pow 6).const_mul (10*s))).sub (((hasDerivAt_id x).pow 4).const_mul (2*s))).add (((hasDerivAt_id x).pow 2).const_mul (18*s))).sub (hasDerivAt_const x (6*s))).add (((hasDerivAt_id x).pow 5).const_mul (8))).sub (((hasDerivAt_id x).pow 3).const_mul (8))) using 1 <;> norm_num <;> ring

private theorem fCoord_hasDeriv (s x : ℝ) (hs : s ≠ 0) (h : 1-s*x ≠ 0) :
    HasDerivAt (fCoord s) ((s*x^2+s-2*x)*octic s x/(16*(s*x-1)^4)) x := by
  have hden := ((((hasDerivAt_id x).const_mul s).sub_const 1).pow 3).const_mul 16
  have hd : 16*(s*x-1)^3 ≠ 0 := by
    have h' : s*x-1 ≠ 0 := by intro he; apply h; linarith
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ h')
  have hr := (fNumerator_hasDeriv s x).div hden hd
  have h' : s*x-1 ≠ 0 := by intro he; apply h; linarith
  have hre : ∀ᶠ t in 𝓝 x, rationalF s t = fCoord s t := by
    have hn : ∀ᶠ t in 𝓝 x, 1-s*t ≠ 0 :=
      (show ContinuousAt (fun t : ℝ => 1-s*t) x by fun_prop).eventually_ne h
    filter_upwards [hn] with t ht using (fCoord_eq_rationalF s t hs ht).symm
  apply HasDerivAt.congr_of_eventuallyEq (f := rationalF s) (f' := (s*x^2+s-2*x)*octic s x/(16*(s*x-1)^4)) ?_ (hre.mono (fun t ht => ht.symm))
  unfold rationalF
  convert! hr using 1
  norm_num
  unfold fNumerator fNumeratorDeriv octic
  field_simp [hs,h,h']
  ring

private theorem d3_nonneg_bound (r y b s : ℝ) (hs : 0 < s)
    (hr : 0 ≤ r) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hr1 : r ≤ 3*s^2/5) (hz : r+y ≤ s/2) (hb1 : b ≤ 1) :
    d3 r y b (s^2) / s^5 ≤
      3/40+(81/125)*s+s^2/128+(9/200)*s^3+(81/625)*s^5 := by
  have hz0 : 0 ≤ r+y := add_nonneg hr hy
  have hy1 : y ≤ s/2 := by linarith
  have pz (k : ℕ) : (r+y)^k ≤ (s/2)^k := pow_le_pow_left₀ hz0 hz k
  have pr (k : ℕ) : r^k ≤ (3*s^2/5)^k := pow_le_pow_left₀ hr hr1 k
  have h1 : r*(r+y)^3 ≤ (3*s^2/5)*(s/2)^3 :=
    mul_le_mul hr1 (pz 3) (pow_nonneg hz0 _) (by positivity)
  have h2 : 3*b*r^3 ≤ 3*(3*s^2/5)^3 := by
    have ht := mul_le_mul hb1 (pr 3) (pow_nonneg hr _) (by norm_num)
    nlinarith only [ht]
  have h3 : y*(r+y)^6 ≤ (s/2)*(s/2)^6 :=
    mul_le_mul hy1 (pz 6) (pow_nonneg hz0 _) (by positivity)
  have h4 : 2*b*y*r^2*(r+y)^3 ≤ 2*(s/2)*(3*s^2/5)^2*(s/2)^3 := by
    have hby : b*y ≤ s/2 := (mul_le_mul hb1 hy1 hy (by norm_num)).trans_eq (one_mul _)
    have hby0 : 0 ≤ b*y := mul_nonneg hb hy
    have ht := mul_le_mul hby (pr 2) (pow_nonneg hr _) (by positivity)
    have ht2 := mul_le_mul ht (pz 3) (pow_nonneg hz0 _) (by positivity)
    nlinarith only [ht2]
  have h5 : b*r^4*s^2 ≤ (3*s^2/5)^4*s^2 := by
    have ht := mul_le_mul hb1 (pr 4) (pow_nonneg hr _) (by norm_num)
    exact mul_le_mul_of_nonneg_right (by simpa using ht) (sq_nonneg s)
  apply (div_le_iff₀ (pow_pos hs 5)).mpr
  unfold d3
  nlinarith only [h1,h2,h3,h4,h5]

private theorem fCoord_low_bound (s x : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hx : x ∈ Set.Icc (0 : ℝ) (1/2)) (hq : qCoord s x ∈ Set.Icc (0 : ℝ) 1) :
    fCoord s x < 83/1000 := by
  have hx1 : x ≤ 1 := by linarith [hx.2]
  have hden : 0 < 1-s*x := by nlinarith [hx.1,hx.2]
  have hrc : 0 ≤ rCoord s x := by
    unfold rCoord
    apply div_nonneg
    · apply mul_nonneg (sq_nonneg s); nlinarith [hx.1,hx.2]
    · positivity
  have hrc1 : rCoord s x ≤ 3*s^2/5 := by
    unfold rCoord
    apply (div_le_iff₀ (mul_pos (by norm_num) hden)).mpr
    have hlow : (9/10 : ℝ) ≤ 1-s*x := by nlinarith [hx.1,hx.2]
    nlinarith [sq_nonneg x,mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hlow)]
  obtain ⟨hr,hy,hb⟩ := weights_of_coord s x hs hs1 ⟨hx.1,hx1⟩ hq
  have hbeta : s^2 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> nlinarith
  obtain ⟨hy0,hr0,hb0,_⟩ := weights_valid (s^2) (qCoord s x) hbeta hq
  rw [hr] at hr0
  rw [hy] at hy0
  rw [hb] at hb0
  have hf := d3_nonneg_bound (rCoord s x) (s*x-rCoord s x) (1-s*x) s hs
    hr0 hy0 hb0 hrc1 (by nlinarith [hx.2]) (by nlinarith [hx.1])
  have sp (k : ℕ) : s^k ≤ (1/100 : ℝ)^k := pow_le_pow_left₀ hs.le hs1 k
  have sp2 := sp 2
  have sp3 := sp 3
  have sp5 := sp 5
  norm_num at sp2 sp3 sp5
  unfold fCoord
  linarith

private theorem fCoord_strictMono_left (s a : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (ha : a ∈ Set.Icc (1/2 : ℝ) 1) (hQ : octic s a < 0) :
    StrictMonoOn (fCoord s) (Set.Icc (1/2 : ℝ) a) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc (1/2 : ℝ) a) : 0 < 1-s*x := by
    have hx1 : x ≤ 1 := hx.2.trans ha.2
    nlinarith [hx.1]
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro x hx
    exact (fCoord_hasDeriv s x (ne_of_gt hs) (ne_of_gt (hd x hx))).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc (1/2 : ℝ) a := interior_subset hx
    have hx1 : x ∈ Set.Icc (1/2 : ℝ) 1 := ⟨hx'.1,hx'.2.trans ha.2⟩
    have hQx : octic s x < 0 :=
      lt_of_le_of_lt ((octic_strictMonoOn s hs hs1).monotoneOn hx1 ha hx'.2) hQ
    have hnum : s*x^2+s-2*x < 0 := by
      have hx0 : 0 ≤ x := by linarith [hx'.1]
      have hx2 : x^2 ≤ 1 := pow_le_one₀ hx0 hx1.2
      nlinarith [hx'.1]
    rw [(fCoord_hasDeriv s x (ne_of_gt hs) (ne_of_gt (hd x hx'))).deriv]
    exact div_pos (mul_pos_of_neg_of_neg hnum hQx)
      (mul_pos (by norm_num) ((show Even (4 : ℕ) by decide).pow_pos (by intro he; have hh := hd x hx'; linarith)))

private theorem fCoord_strictAnti_right (s b : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hb : b ∈ Set.Icc (1/2 : ℝ) 1) (hQ : 0 < octic s b) :
    StrictAntiOn (fCoord s) (Set.Icc b (1 : ℝ)) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc b (1 : ℝ)) : 0 < 1-s*x := by
    have hx0 : (1/2 : ℝ) ≤ x := hb.1.trans hx.1
    nlinarith [hx.2]
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · intro x hx
    exact (fCoord_hasDeriv s x (ne_of_gt hs) (ne_of_gt (hd x hx))).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc b (1 : ℝ) := interior_subset hx
    have hx1 : x ∈ Set.Icc (1/2 : ℝ) 1 := ⟨hb.1.trans hx'.1,hx'.2⟩
    have hQx : 0 < octic s x :=
      lt_of_lt_of_le hQ ((octic_strictMonoOn s hs hs1).monotoneOn hb hx1 hx'.1)
    have hnum : s*x^2+s-2*x < 0 := by
      have hx0 : 0 ≤ x := by linarith [hx1.1]
      have hx2 : x^2 ≤ 1 := pow_le_one₀ hx0 hx1.2
      nlinarith [hx1.1]
    rw [(fCoord_hasDeriv s x (ne_of_gt hs) (ne_of_gt (hd x hx'))).deriv]
    apply div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hnum hQx)
    exact mul_pos (by norm_num) ((show Even (4 : ℕ) by decide).pow_pos (by intro he; have hh := hd x hx'; linarith))

private theorem coord_interval_for_max (s a b x : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (ha : a ∈ Set.Icc (1/2 : ℝ) 1) (hb : b ∈ Set.Icc (1/2 : ℝ) 1)
    (hQa : octic s a < 0) (hQb : 0 < octic s b)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hqx : qCoord s x ∈ Set.Icc (0 : ℝ) 1)
    (hTest : (9/100 : ℝ) < fCoord s (3/4))
    (hmaxT : fCoord s (3/4) ≤ fCoord s x)
    (hmaxA : fCoord s a ≤ fCoord s x) (hmaxB : fCoord s b ≤ fCoord s x) :
    x ∈ Set.Icc a b := by
  have hxhalf : (1/2 : ℝ) < x := by
    by_contra h
    have hx' : x ∈ Set.Icc (0 : ℝ) (1/2) := ⟨hx.1,not_lt.mp h⟩
    have hlow := fCoord_low_bound s x hs hs1 hx' hqx
    linarith
  constructor
  · by_contra h
    have hxa : x < a := not_le.mp h
    have hh := fCoord_strictMono_left s a hs hs1 ha hQa
      ⟨hxhalf.le,hxa.le⟩ ⟨ha.1,le_rfl⟩ hxa
    linarith
  · by_contra h
    have hbx : b < x := not_le.mp h
    have hh := fCoord_strictAnti_right s b hs hs1 hb hQb
      ⟨le_rfl,hb.2⟩ ⟨hbx.le,hx.2⟩ hbx
    linarith

private theorem coord_root_of_max (s x : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hx : x ∈ Set.Ioo (1/2 : ℝ) 1) (hq : qCoord s x ∈ Set.Ioo (0 : ℝ) 1)
    (hmax : ∀ y ∈ Set.Icc (0 : ℝ) 1, qCoord s y ∈ Set.Icc (0 : ℝ) 1 →
      fCoord s y ≤ fCoord s x) : octic s x = 0 := by
  have hden : 0 < 1-s*x := by nlinarith [hx.1,hx.2]
  have hlocal : IsLocalMax (fCoord s) x := by
    change ∀ᶠ y in 𝓝 x, fCoord s y ≤ fCoord s x
    have hNear : ∀ᶠ y in 𝓝 x, y ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhds (by linarith [hx.1]) hx.2
    have hqNear : ∀ᶠ y in 𝓝 x, qCoord s y ∈ Set.Ioo (0 : ℝ) 1 :=
      (qCoord_hasDeriv s x (ne_of_gt hden)).continuousAt.tendsto.eventually
        (Ioo_mem_nhds hq.1 hq.2)
    filter_upwards [hNear,hqNear] with y hy hqy
    exact hmax y ⟨hy.1.le,hy.2.le⟩ ⟨hqy.1.le,hqy.2.le⟩
  have hd := (fCoord_hasDeriv s x (ne_of_gt hs) (ne_of_gt hden)).deriv
  rw [hlocal.deriv_eq_zero] at hd
  have hnum : s*x^2+s-2*x ≠ 0 := by
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hx2 : x^2 ≤ 1 := pow_le_one₀ hx0 hx.2.le
    have hn : s*x^2+s-2*x < 0 := by nlinarith [hx.1]
    exact ne_of_lt hn
  have hden' : 16*(s*x-1)^4 ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    apply pow_ne_zero
    intro h
    linarith
  have hprod : (s*x^2+s-2*x)*octic s x = 0 :=
    (div_eq_zero_iff).mp hd.symm |>.resolve_right hden'
  exact (mul_eq_zero.mp hprod).resolve_left hnum

private theorem rawWeight_eq (beta q : ℝ) (a : Fin 3) :
    colourWeight beta q a = rawWeight (rW beta q) (yW beta q) (bW beta q) a := by
  fin_cases a <;> norm_num [colourWeight,rawWeight,Fin.ext_iff]

private theorem density_h3 (beta q : ℝ) (hb : beta ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    tDens h3 beta q = d3 (rW beta q) (yW beta q) (bW beta q) beta := by
  rw [tDens_eq_weightingSum h3 beta q hb hq]
  unfold weightingSum
  simp_rw [h3_admissible_iff,rawWeight_eq]
  change h3Poly (rW beta q) (yW beta q) (bW beta q) = _
  rw [h3Poly_closed]
  have hSum : rW beta q+yW beta q+bW beta q = 1 := by
    have hh := (weights_valid beta q hb hq).2.2.2
    linarith
  rw [hSum,weights_edge_density beta q hb hq]
  unfold d3
  ring

private theorem density_coord (s x : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hq : qCoord s x ∈ Set.Icc (0 : ℝ) 1) :
    tDens h3 (s^2) (qCoord s x) = s^5*fCoord s x := by
  have hbeta : s^2 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> nlinarith
  rw [density_h3 (s^2) (qCoord s x) hbeta hq]
  obtain ⟨hr,hy,hb⟩ := weights_of_coord s x hs hs1 hx hq
  rw [hr,hy,hb]
  unfold fCoord
  exact (mul_div_cancel₀ _ (pow_ne_zero _ (ne_of_gt hs))).symm

private theorem density_xFrom (s q : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    tDens h3 (s^2) q = s^5*fCoord s (xFrom s q) := by
  obtain ⟨hx,hr,hqq⟩ := xFrom_properties s q hs hs1 hq
  have hq' : qCoord s (xFrom s q) ∈ Set.Icc (0 : ℝ) 1 := by rwa [hqq]
  have h := density_coord s (xFrom s q) hs hs1 hx hq'
  rwa [hqq] at h

private theorem maximise_coord (s q : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/100)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (tDens h3 (s^2)) (Set.Icc 0 1) q) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, qCoord s x ∈ Set.Icc (0 : ℝ) 1 →
      fCoord s x ≤ fCoord s (xFrom s q) := by
  intro x hx hqx
  have hh := hmax hqx
  change tDens h3 (s^2) (qCoord s x) ≤ tDens h3 (s^2) q at hh
  rw [density_coord s x hs hs1 hx hqx,density_xFrom s q hs hs1 hq] at hh
  exact (mul_le_mul_iff_right₀ (pow_pos hs 5)).mp hh

private theorem max_interval_one (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hm : IsMaxOn (tDens h3 ((1/1000 : ℝ)^2)) (Set.Icc 0 1) q) :
    xFrom (1/1000) q ∈ Set.Icc (77451/100000 : ℝ) (77452/100000) := by
  have hx := (xFrom_properties (1/1000) q (by norm_num) (by norm_num) hq).1
  have hqx := (xFrom_properties (1/1000) q (by norm_num) (by norm_num) hq).2.2
  have hphys : qCoord (1/1000) (xFrom (1/1000) q) ∈ Set.Icc (0 : ℝ) 1 := by rwa [hqx]
  have hmax := maximise_coord (1/1000) q (by norm_num) (by norm_num) hq hm
  exact coord_interval_for_max (1/1000) (77451/100000) (77452/100000) _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    octic_root_signs.1 octic_root_signs.2.1 hx hphys test_point_values.1
    (hmax (3/4) (by norm_num) (by norm_num [qCoord]))
    (hmax (77451/100000) (by norm_num) (by norm_num [qCoord]))
    (hmax (77452/100000) (by norm_num) (by norm_num [qCoord]))

private theorem max_interval_two (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hm : IsMaxOn (tDens h3 ((1/100 : ℝ)^2)) (Set.Icc 0 1) q) :
    xFrom (1/100) q ∈ Set.Icc (77384/100000 : ℝ) (77385/100000) := by
  have hx := (xFrom_properties (1/100) q (by norm_num) (by norm_num) hq).1
  have hqx := (xFrom_properties (1/100) q (by norm_num) (by norm_num) hq).2.2
  have hphys : qCoord (1/100) (xFrom (1/100) q) ∈ Set.Icc (0 : ℝ) 1 := by rwa [hqx]
  have hmax := maximise_coord (1/100) q (by norm_num) (by norm_num) hq hm
  exact coord_interval_for_max (1/100) (77384/100000) (77385/100000) _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    octic_root_signs.2.2.1 octic_root_signs.2.2.2 hx hphys test_point_values.2
    (hmax (3/4) (by norm_num) (by norm_num [qCoord]))
    (hmax (77384/100000) (by norm_num) (by norm_num [qCoord]))
    (hmax (77385/100000) (by norm_num) (by norm_num [qCoord]))

private theorem maximisers_reversed (q1 q2 : ℝ) (hq1 : q1 ∈ Set.Icc (0 : ℝ) 1)
    (hq2 : q2 ∈ Set.Icc (0 : ℝ) 1)
    (hm1 : IsMaxOn (tDens h3 ((1/1000 : ℝ)^2)) (Set.Icc 0 1) q1)
    (hm2 : IsMaxOn (tDens h3 ((1/100 : ℝ)^2)) (Set.Icc 0 1) q2) :
    (7743/10000 : ℝ) < q1 ∧ q2 < 7719/10000 := by
  have h1 := max_interval_one q1 hq1 hm1
  have h2 := max_interval_two q2 hq2 hm2
  have hx1 := (xFrom_properties (1/1000) q1 (by norm_num) (by norm_num) hq1).1
  have hx2 := (xFrom_properties (1/100) q2 (by norm_num) (by norm_num) hq2).1
  have heq1 := (xFrom_properties (1/1000) q1 (by norm_num) (by norm_num) hq1).2.2
  have heq2 := (xFrom_properties (1/100) q2 (by norm_num) (by norm_num) hq2).2.2
  have hqlo := (coord_strictMonoOn (1/1000) (by norm_num) (by norm_num)).monotoneOn
    (by norm_num : (77451/100000 : ℝ) ∈ Set.Icc 0 1) hx1 h1.1
  have hqhi := (coord_strictMonoOn (1/100) (by norm_num) (by norm_num)).monotoneOn
    hx2 (by norm_num : (77385/100000 : ℝ) ∈ Set.Icc 0 1) h2.2
  rw [heq1] at hqlo
  rw [heq2] at hqhi
  exact ⟨coord_interval_order.1.trans_le hqlo,hqhi.trans_lt coord_interval_order.2⟩

private theorem density_continuous (beta : ℝ) (hb : beta ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (tDens h3 beta) (Set.Icc (0 : ℝ) 1) := by
  have hh : Continuous (fun q : ℝ => d3 (rW beta q) (yW beta q) (bW beta q) beta) := by
    unfold d3 rW yW bW
    fun_prop
  apply hh.continuousOn.congr
  intro q hq
  exact density_h3 beta q hb hq

private theorem max_exists (beta : ℝ) (hb : beta ∈ Set.Icc (0 : ℝ) 1) :
    ∃ q ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (tDens h3 beta) (Set.Icc 0 1) q :=
  isCompact_Icc.exists_isMaxOn (by exact ⟨0,by norm_num⟩) (density_continuous beta hb)

private theorem max_coord_root_one (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hm : IsMaxOn (tDens h3 ((1/1000 : ℝ)^2)) (Set.Icc 0 1) q) :
    octic (1/1000) (xFrom (1/1000) q) = 0 := by
  have hx := max_interval_one q hq hm
  have hxphys := (xFrom_properties (1/1000) q (by norm_num) (by norm_num) hq).1
  have hqlo := (coord_strictMonoOn (1/1000) (by norm_num) (by norm_num)).monotoneOn
    (by norm_num : (77451/100000 : ℝ) ∈ Set.Icc 0 1) hxphys hx.1
  have hqhi := (coord_strictMonoOn (1/1000) (by norm_num) (by norm_num)).monotoneOn
    hxphys (by norm_num : (77452/100000 : ℝ) ∈ Set.Icc 0 1) hx.2
  apply coord_root_of_max (1/1000) _ (by norm_num) (by norm_num)
  · constructor <;> linarith [hx.1,hx.2]
  · constructor
    · exact lt_of_lt_of_le (by norm_num [qCoord] : (0 : ℝ) < qCoord (1/1000) (77451/100000)) hqlo
    · exact lt_of_le_of_lt hqhi (by norm_num [qCoord] : qCoord (1/1000) (77452/100000) < (1 : ℝ))
  · exact maximise_coord (1/1000) q (by norm_num) (by norm_num) hq hm

private theorem max_coord_root_two (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hm : IsMaxOn (tDens h3 ((1/100 : ℝ)^2)) (Set.Icc 0 1) q) :
    octic (1/100) (xFrom (1/100) q) = 0 := by
  have hx := max_interval_two q hq hm
  have hxphys := (xFrom_properties (1/100) q (by norm_num) (by norm_num) hq).1
  have hqlo := (coord_strictMonoOn (1/100) (by norm_num) (by norm_num)).monotoneOn
    (by norm_num : (77384/100000 : ℝ) ∈ Set.Icc 0 1) hxphys hx.1
  have hqhi := (coord_strictMonoOn (1/100) (by norm_num) (by norm_num)).monotoneOn
    hxphys (by norm_num : (77385/100000 : ℝ) ∈ Set.Icc 0 1) hx.2
  apply coord_root_of_max (1/100) _ (by norm_num) (by norm_num)
  · constructor <;> linarith [hx.1,hx.2]
  · constructor
    · exact lt_of_lt_of_le (by norm_num [qCoord] : (0 : ℝ) < qCoord (1/100) (77384/100000)) hqlo
    · exact lt_of_le_of_lt hqhi (by norm_num [qCoord] : qCoord (1/100) (77385/100000) < (1 : ℝ))
  · exact maximise_coord (1/100) q (by norm_num) (by norm_num) hq hm

private theorem max_interval_open_one (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hm : IsMaxOn (tDens h3 ((1/1000 : ℝ)^2)) (Set.Icc 0 1) q) :
    xFrom (1/1000) q ∈ Set.Ioo (77451/100000 : ℝ) (77452/100000) := by
  have hx := max_interval_one q hq hm
  have hroot := max_coord_root_one q hq hm
  constructor
  · rcases lt_or_eq_of_le hx.1 with h | h
    · exact h
    · rw [← h] at hroot
      linarith [octic_root_signs.1]
  · rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · rw [h] at hroot
      linarith [octic_root_signs.2.1]

private theorem max_interval_open_two (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hm : IsMaxOn (tDens h3 ((1/100 : ℝ)^2)) (Set.Icc 0 1) q) :
    xFrom (1/100) q ∈ Set.Ioo (77384/100000 : ℝ) (77385/100000) := by
  have hx := max_interval_two q hq hm
  have hroot := max_coord_root_two q hq hm
  constructor
  · rcases lt_or_eq_of_le hx.1 with h | h
    · exact h
    · rw [← h] at hroot
      linarith [octic_root_signs.2.2.1]
  · rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · rw [h] at hroot
      linarith [octic_root_signs.2.2.2]

private theorem max_unique_one (q1 q2 : ℝ) (hq1 : q1 ∈ Set.Icc (0 : ℝ) 1)
    (hq2 : q2 ∈ Set.Icc (0 : ℝ) 1)
    (hm1 : IsMaxOn (tDens h3 ((1/1000 : ℝ)^2)) (Set.Icc 0 1) q1)
    (hm2 : IsMaxOn (tDens h3 ((1/1000 : ℝ)^2)) (Set.Icc 0 1) q2) : q1 = q2 := by
  have hx1 := max_interval_open_one q1 hq1 hm1
  have hx2 := max_interval_open_one q2 hq2 hm2
  have hroot1 := max_coord_root_one q1 hq1 hm1
  have hroot2 := max_coord_root_one q2 hq2 hm2
  have hxEq : xFrom (1/1000) q1 = xFrom (1/1000) q2 :=
    (octic_strictMonoOn (1/1000) (by norm_num) (by norm_num)).injOn
      ⟨by linarith [hx1.1],by linarith [hx1.2]⟩
      ⟨by linarith [hx2.1],by linarith [hx2.2]⟩ (hroot1.trans hroot2.symm)
  have h1 := (xFrom_properties (1/1000) q1 (by norm_num) (by norm_num) hq1).2.2
  have h2 := (xFrom_properties (1/1000) q2 (by norm_num) (by norm_num) hq2).2.2
  rw [hxEq] at h1
  exact h1.symm.trans h2

private theorem max_unique_two (q1 q2 : ℝ) (hq1 : q1 ∈ Set.Icc (0 : ℝ) 1)
    (hq2 : q2 ∈ Set.Icc (0 : ℝ) 1)
    (hm1 : IsMaxOn (tDens h3 ((1/100 : ℝ)^2)) (Set.Icc 0 1) q1)
    (hm2 : IsMaxOn (tDens h3 ((1/100 : ℝ)^2)) (Set.Icc 0 1) q2) : q1 = q2 := by
  have hx1 := max_interval_open_two q1 hq1 hm1
  have hx2 := max_interval_open_two q2 hq2 hm2
  have hroot1 := max_coord_root_two q1 hq1 hm1
  have hroot2 := max_coord_root_two q2 hq2 hm2
  have hxEq : xFrom (1/100) q1 = xFrom (1/100) q2 :=
    (octic_strictMonoOn (1/100) (by norm_num) (by norm_num)).injOn
      ⟨by linarith [hx1.1],by linarith [hx1.2]⟩
      ⟨by linarith [hx2.1],by linarith [hx2.2]⟩ (hroot1.trans hroot2.symm)
  have h1 := (xFrom_properties (1/100) q1 (by norm_num) (by norm_num) hq1).2.2
  have h2 := (xFrom_properties (1/100) q2 (by norm_num) (by norm_num) hq2).2.2
  rw [hxEq] at h1
  exact h1.symm.trans h2

private theorem unique_max_one : ∃! q : ℝ,
    q ∈ Set.Icc (0 : ℝ) 1 ∧ IsMaxOn (tDens h3 ((1/1000 : ℝ)^2)) (Set.Icc 0 1) q := by
  obtain ⟨q,hq,hm⟩ := max_exists ((1/1000 : ℝ)^2) (by norm_num)
  refine ⟨q,⟨hq,hm⟩,?_⟩
  intro p hp
  exact max_unique_one p q hp.1 hq hp.2 hm

private theorem unique_max_two : ∃! q : ℝ,
    q ∈ Set.Icc (0 : ℝ) 1 ∧ IsMaxOn (tDens h3 ((1/100 : ℝ)^2)) (Set.Icc 0 1) q := by
  obtain ⟨q,hq,hm⟩ := max_exists ((1/100 : ℝ)^2) (by norm_num)
  refine ⟨q,⟨hq,hm⟩,?_⟩
  intro p hp
  exact max_unique_two p q hp.1 hq hp.2 hm

theorem result : ¬ claim := by
  intro h
  obtain ⟨qf,hopt,hmono⟩ := h 7 h3
  have hb1 : (1/1000 : ℝ)^2 ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hb2 : (1/100 : ℝ)^2 ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  obtain ⟨q1,h1,hu1⟩ := unique_max_one
  obtain ⟨q2,h2,hu2⟩ := unique_max_two
  have heq1 := hu1 (qf ((1/1000 : ℝ)^2)) (hopt _ hb1)
  have heq2 := hu2 (qf ((1/100 : ℝ)^2)) (hopt _ hb2)
  have hle : qf ((1/1000 : ℝ)^2) ≤ qf ((1/100 : ℝ)^2) :=
    hmono hb1 hb2 (by norm_num)
  rw [heq1,heq2] at hle
  obtain ⟨hlo,hhi⟩ := maximisers_reversed q1 q2 h1.1 h2.1 h1.2 h2.2
  linarith

end D5.S3.Combinatorics.ExtremalDensity.NagyOptimizerMonotonicity
