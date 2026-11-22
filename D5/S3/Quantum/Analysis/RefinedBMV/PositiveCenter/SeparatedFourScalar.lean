/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourScalar
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two cleared scalar signs for the central strip at gap four. -/

import D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

/-! # Cleared scalar signs for the central strip at gap four

The value and its partial derivative in the parameter `r` are evaluated at
`r = 1 - u / (4 * E)`, where `E = exp u - 1`.
-/

open Finset Polynomial
open scoped BigOperators Polynomial

namespace RefinedBMV.PositiveCenter

/-- The scalar upper envelope at the lower endpoint of the range of `r`. -/
noncomputable def separatedFourValue (u E : ℝ) : ℝ :=
  let x := u / E
  let b := 1 + 2 / E - E / (2 * (E - u))
  let l := b - 1 / 4
  let r := 1 - x / 4
  l * (-(5 / 16) * r ^ 2 + 2 * r * (1 / 16) * x) +
    (1 / 16) * r ^ 2 + 2 * r * (5 / 16 - 27 / 50) * (1 / 16) * x +
    2 * r * (1 / 32) * x +
    (1 / 872) * ((14 / 11 + 1 / 2 + 3 / 8) * (b + (1 + 14 / 11 + 1 / 4)) + 1 / 16)

/-- The partial derivative of the envelope in `r`, at the same endpoint. -/
noncomputable def separatedFourDerivative (u E : ℝ) : ℝ :=
  let x := u / E
  let b := 1 + 2 / E - E / (2 * (E - u))
  let l := b - 1 / 4
  let r := 1 - x / 4
  2 * r * (1 / 16 - (5 / 16) * l) + 2 * x * ((1 / 16) * (l + 5 / 16 - 27 / 50) + 1 / 32)

private inductive Sign
  | value
  | derivative

private structure ExpTerm where
  rate : ℕ
  power : ℕ
  weight : ℕ

private structure Certificate where
  leading : ℕ
  positive : List ExpTerm
  negative : List ExpTerm

-- Multiplying the cleared expressions by 168819200 and 800 respectively
-- makes every weight integral.
private def certificate : Sign → Certificate
  | .value =>
    ⟨2737700,
      [⟨3, 0, 198410000⟩, ⟨2, 2, 78012935⟩, ⟨1, 2, 68187130⟩,
       ⟨1, 1, 559261676⟩, ⟨1, 0, 617131600⟩],
      [⟨3, 1, 79767708⟩, ⟨2, 1, 159979276⟩, ⟨2, 0, 611656200⟩,
       ⟨1, 3, 14415577⟩, ⟨0, 3, 19875823⟩, ⟨0, 2, 146200065⟩,
       ⟨0, 1, 319514692⟩, ⟨0, 0, 206623100⟩]⟩
  | .derivative =>
    ⟨50,
      [⟨3, 0, 1800⟩, ⟨2, 2, 342⟩, ⟨1, 2, 216⟩, ⟨1, 1, 3799⟩, ⟨1, 0, 5800⟩],
      [⟨3, 1, 667⟩, ⟨2, 1, 899⟩, ⟨2, 0, 5700⟩,
       ⟨0, 2, 558⟩, ⟨0, 1, 2233⟩, ⟨0, 0, 1950⟩]⟩

private def Certificate.lead (c : Certificate) : ExpTerm :=
  ⟨4, 0, c.leading⟩

private noncomputable def ExpTerm.polynomial (t : ExpTerm) (u z : ℝ) : ℝ :=
  (t.weight : ℝ) * u ^ t.power * z ^ t.rate

private noncomputable def Certificate.polynomial (c : Certificate) (u z : ℝ) : ℝ :=
  c.lead.polynomial u z + (c.positive.map (fun t ↦ t.polynomial u z)).sum -
    (c.negative.map (fun t ↦ t.polynomial u z)).sum

private def ExpTerm.coeff (t : ExpTerm) (n : ℕ) : ℚ :=
  if t.power ≤ n then (t.weight : ℚ) * (t.rate : ℚ) ^ (n - t.power) /
    ((n - t.power).factorial : ℚ) else 0

private def coeffSum (ts : List ExpTerm) (n : ℕ) : ℚ :=
  (ts.map (fun t ↦ t.coeff n)).sum

private def Certificate.coeff (c : Certificate) (n : ℕ) : ℚ :=
  c.lead.coeff n + coeffSum c.positive n - coeffSum c.negative n

set_option maxHeartbeats 1000000 in
private theorem value_clear (u E : ℝ) (hE : E ≠ 0) (hEu : E - u ≠ 0) :
    (certificate .value).polynomial u (E + 1) =
      168819200 * (-2 * E ^ 3 * (E - u) * separatedFourValue u E) := by
  norm_num [certificate, Certificate.polynomial, Certificate.lead, ExpTerm.polynomial,
    separatedFourValue] <;> field_simp [hE, hEu] <;> ring

set_option maxHeartbeats 1000000 in
private theorem derivative_clear (u E : ℝ) (hE : E ≠ 0) (hEu : E - u ≠ 0) :
    (certificate .derivative).polynomial u (E + 1) =
      800 * (-2 * E ^ 3 * (E - u) * separatedFourDerivative u E) := by
  norm_num [certificate, Certificate.polynomial, Certificate.lead, ExpTerm.polynomial,
    separatedFourDerivative] <;> field_simp [hE, hEu] <;> ring

private theorem term_hasSum (t : ExpTerm) (u : ℝ) :
    HasSum (fun n ↦ (t.coeff n : ℝ) * u ^ n) (t.polynomial u (Real.exp u)) := by
  rw [ExpTerm.polynomial, ← Real.exp_nat_mul]
  apply (hasSum_nat_add_iff' t.power).1
  have hzero : (∑ n ∈ range t.power, (t.coeff n : ℝ) * u ^ n) = 0 := by
    refine sum_eq_zero fun n hn ↦ ?_
    simp [ExpTerm.coeff, show ¬ t.power ≤ n from Nat.not_le.mpr (mem_range.mp hn)]
  rw [hzero, sub_zero, Real.exp_eq_exp_ℝ]
  refine ((NormedSpace.expSeries_div_hasSum_exp ((t.rate : ℝ) * u)).mul_left
    ((t.weight : ℝ) * u ^ t.power)).congr_fun fun n ↦ ?_
  have hpower : t.power ≤ n + t.power := by omega
  have hsub : n + t.power - t.power = n := by omega
  simp only [ExpTerm.coeff, if_pos hpower, hsub, Rat.cast_natCast, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, mul_pow, pow_add]
  ring

private theorem coeffSum_hasSum (ts : List ExpTerm) (u : ℝ) :
    HasSum (fun n ↦ (coeffSum ts n : ℝ) * u ^ n)
      (ts.map (fun t ↦ t.polynomial u (Real.exp u))).sum := by
  induction ts with
  | nil => simpa [coeffSum] using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
  | cons t ts ih =>
      simpa only [coeffSum, List.map_cons, List.sum_cons, Rat.cast_add, add_mul] using
        (term_hasSum t u).add ih

private theorem certificate_hasSum (c : Certificate) (u : ℝ) :
    HasSum (fun n ↦ (c.coeff n : ℝ) * u ^ n) (c.polynomial u (Real.exp u)) := by
  simpa only [Certificate.coeff, Certificate.polynomial, Rat.cast_add, Rat.cast_sub,
    add_mul, sub_mul] using
    ((term_hasSum c.lead u).add (coeffSum_hasSum c.positive u)).sub
      (coeffSum_hasSum c.negative u)

private theorem term_coeff_nonneg (t : ExpTerm) (n : ℕ) : 0 ≤ (t.coeff n : ℝ) := by
  unfold ExpTerm.coeff
  split <;> push_cast <;> positivity

private theorem coeffSum_nonneg (ts : List ExpTerm) (n : ℕ) :
    0 ≤ (coeffSum ts n : ℝ) := by
  induction ts with
  | nil => simp [coeffSum]
  | cons t ts ih =>
      simp only [coeffSum, List.map_cons, List.sum_cons, Rat.cast_add]
      exact add_nonneg (term_coeff_nonneg t n) ih

private theorem term_coeff_succ (t : ExpTerm) {n : ℕ} (hn : t.power ≤ n) :
    (t.coeff (n + 1) : ℝ) =
      (t.coeff n : ℝ) * ((t.rate : ℝ) / (((n - t.power : ℕ) : ℝ) + 1)) := by
  have hnext : t.power ≤ n + 1 := by omega
  have hsub : n + 1 - t.power = n - t.power + 1 := by omega
  simp only [ExpTerm.coeff, ite_eq_left hn, ite_eq_left hnext, hsub, pow_succ,
    Nat.factorial_succ, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_one,
    Rat.cast_natCast,
    Nat.cast_mul, Nat.cast_succ, div_mul_div_comm]
  ac_rfl

-- At degree n the successive-term ratio is k / (n + 1 - a).
-- For k,a ≤ 3 and n ≥ 26 it is bounded by the leading ratio 4 / (n + 1).
private theorem adverse_step {ts : List ExpTerm} {n : ℕ} (hn : 26 ≤ n)
    (hts : ∀ t ∈ ts, t.rate ≤ 3 ∧ t.power ≤ 3) :
    (coeffSum ts (n + 1) : ℝ) ≤ (coeffSum ts n : ℝ) * (4 / ((n : ℝ) + 1)) := by
  induction ts with
  | nil => simp [coeffSum]
  | cons t ts ih =>
      obtain ⟨hkr, har⟩ := hts t (by simp)
      have ha : t.power ≤ n := by omega
      have hsub : ((n - t.power : ℕ) : ℝ) = (n : ℝ) - (t.power : ℝ) := Nat.cast_sub ha
      have hnR : (26 : ℝ) ≤ n := by exact_mod_cast hn
      have hkR : (t.rate : ℝ) ≤ 3 := by exact_mod_cast hkr
      have haR : (t.power : ℝ) ≤ 3 := by exact_mod_cast har
      have hratio : (t.rate : ℝ) / (((n - t.power : ℕ) : ℝ) + 1) ≤ 4 / ((n : ℝ) + 1) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        rw [hsub]
        calc
          _ ≤ 3 * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hkR (by positivity)
          _ ≤ _ := by linarith
      simp only [coeffSum, List.map_cons, List.sum_cons, Rat.cast_add]
      rw [term_coeff_succ t ha, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hratio (term_coeff_nonneg t n))
        (ih fun t' ht' ↦ hts t' (List.mem_cons_of_mem _ ht'))

private theorem adverse_rates (s : Sign) :
    ∀ t ∈ (certificate s).negative, t.rate ≤ 3 ∧ t.power ≤ 3 := by
  have h : ((certificate s).negative.all
      (fun t ↦ decide (t.rate ≤ 3 ∧ t.power ≤ 3))) = true := by
    cases s <;> decide +kernel
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

private theorem adverse_base (s : Sign) :
    coeffSum (certificate s).negative 26 ≤ (certificate s).lead.coeff 26 := by
  cases s <;> decide +kernel

private theorem adverse_domination (s : Sign) (m : ℕ) :
    (coeffSum (certificate s).negative (m + 26) : ℝ) ≤
      ((certificate s).lead.coeff (m + 26) : ℝ) := by
  induction m with
  | zero => exact_mod_cast adverse_base s
  | succ m ih =>
      rw [show m.succ + 26 = m + 26 + 1 by omega]
      have h := term_coeff_succ (certificate s).lead (n := m + 26)
        (by simp [Certificate.lead])
      rw [h]
      simp only [Certificate.lead, Nat.sub_zero, Nat.cast_ofNat]
      exact (adverse_step (by omega : 26 ≤ m + 26) (adverse_rates s)).trans
        (mul_le_mul_of_nonneg_right ih (by positivity))

private theorem tail_nonneg (s : Sign) {n : ℕ} (hn : 26 ≤ n) :
    0 ≤ ((certificate s).coeff n : ℝ) := by
  have h := adverse_domination s (n - 26)
  rw [Nat.sub_add_cancel hn] at h
  simp only [Certificate.coeff, Rat.cast_add, Rat.cast_sub]
  exact sub_nonneg.mpr (h.trans (le_add_of_nonneg_right (coeffSum_nonneg _ _)))

private theorem coeff_zero (s : Sign) {n : ℕ} (hn : n < 4) :
    (certificate s).coeff n = 0 := by
  cases s <;> interval_cases n <;> decide +kernel

private noncomputable def truncation (s : Sign) (u : ℝ) : ℝ :=
  ∑ j ∈ range 22, ((certificate s).coeff (4 + j) : ℝ) * u ^ j

private theorem truncation_le (s : Sign) {u : ℝ} (hu : 0 ≤ u) :
    u ^ 4 * truncation s u ≤ (certificate s).polynomial u (Real.exp u) := by
  let f (n : ℕ) := ((certificate s).coeff n : ℝ) * u ^ n
  have hs : HasSum f ((certificate s).polynomial u (Real.exp u)) := certificate_hasSum _ _
  have ht := (hasSum_nat_add_iff' 26).2 hs
  have htail : 0 ≤ (certificate s).polynomial u (Real.exp u) - ∑ n ∈ range 26, f n := by
    rw [← ht.tsum_eq]
    exact tsum_nonneg fun n ↦ mul_nonneg (tail_nonneg s (by omega)) (pow_nonneg hu _)
  have hzero : (∑ n ∈ range 4, f n) = 0 := by
    refine sum_eq_zero fun n hn ↦ ?_
    simp [f, coeff_zero s (mem_range.mp hn)]
  have hsplit : (∑ n ∈ range 26, f n) = u ^ 4 * truncation s u := by
    rw [show (26 : ℕ) = 4 + 22 from rfl, sum_range_add f 4 22, hzero, zero_add,
      truncation, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [f, pow_add]
    ring
  rw [← hsplit]
  exact sub_nonneg.mp htail

set_option maxHeartbeats 2000000 in
private theorem derivative_coeff_pos {j : ℕ} (hj : j < 22) :
    0 < (certificate .derivative).coeff (4 + j) := by
  interval_cases j <;> decide +kernel

private theorem derivative_truncation_pos {u : ℝ} (hu : 0 < u) :
    0 < truncation .derivative u := by
  unfold truncation
  apply sum_pos'
  · intro j hj
    exact mul_nonneg (by exact_mod_cast (derivative_coeff_pos (mem_range.mp hj)).le)
      (pow_nonneg hu.le _)
  · refine ⟨0, by simp, ?_⟩
    exact mul_pos (by exact_mod_cast derivative_coeff_pos (j := 0) (by decide)) (pow_pos hu _)

private def rangeSum {R : Type*} [AddMonoid R] (f : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => rangeSum f n + f n

private theorem rangeSum_eq {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    rangeSum f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih => rw [rangeSum, ih, sum_range_succ]

-- Use the falling-factorial formula for the finite binomial computations.
private def choose (n j : ℕ) : ℕ := n.descFactorial j / j.factorial

private theorem choose_eq (n j : ℕ) : choose n j = n.choose j :=
  (Nat.choose_eq_descFactorial_div_factorial n j).symm

private def shiftedCoeff (lo : ℚ) (j : ℕ) : ℚ :=
  rangeSum (fun i ↦ (certificate .value).coeff (4 + i) * (choose i j : ℚ) *
    lo ^ (i - j) * (7 / 4) ^ j) 22

-- The ascending power coefficients on the two affine unit intervals.
-- Each entry is checked against shiftedCoeff below.
private def shiftedTable (right : Bool) : List ℚ :=
  if right then [
      915618507023088336000165087419779570491 / 5776475741678366066286264320000,
      -2839289439503640077143520548455333367 / 117887260034252368699719680000,
      -22797858527240855749595326889933855483 / 35366178010275710609915904000,
      -55292839694685196202290185170895168637 / 75784667164876522735534080000,
      20132215519845397760209330694888030519 / 50523111443251015157022720000,
      1002425745851418693867787641794373920893 / 454708002989259136413204480000,
      205070660873949125587357925836079801441 / 56838500373657392051650560000,
      45309548195754898507931314906049433419 / 11367700074731478410330112000,
      261015646017474762220882124349719396117 / 75784667164876522735534080000,
      297153321207574811249708263834444389709 / 120363883144215653756436480000,
      46816756842267980387210857058309116757 / 31002818385631304755445760000,
      163375913593533383221240978356148260511 / 204618601345166611385942016000,
      149829818705940890932712173347859763767 / 409237202690333222771884032000,
      296804031846040189623768765740478600377 / 2046186013451666113859420160000,
      226476716231057639190344905990696890409 / 4603918530266248756183695360000,
      194390677381123347037329758283909571037 / 13811755590798746268551086080000,
      122600699942736660330469079569391505443 / 36831348242129990049469562880000,
      13980596611807968684041954391051150743 / 22098808945277994029681737728000,
      569292101440071422532118879430909981 / 6138558040354998341578260480000,
      543081018811623232676725106250032123 / 55247022363194985074204344320000,
      222009054687491676135557021086044611 / 331482134179169910445226065920000,
      1989309144913632790725421747442689 / 90404218412500884666879836160000] else [
      4818869002096264548880289441362303523 / 162646825823958319591587840000,
      24218062324196708495923349402696581 / 316125997714204702801920000,
      19931880214138788491186917912596853 / 245875775999936991068160000,
      75752738564499422934420674829095887 / 1896755986285228216811520000,
      -1247134613617788219563610539088809 / 281000886857070846935040000,
      -495816640220450798366085937847893 / 19835356719322648018944000,
      -29980103613616266813689261032077131 / 1264503990856818811207680000,
      -11712711696305353448819375860932847 / 843002660571212540805120000,
      -2684451694015868865633291767438719 / 518770868043823102033920000,
      -54411608534393916316076327434123969 / 121392383122254605875937280000,
      380863540421631451727388952890833 / 334414278573704148418560000,
      2477429508767887542778990947898913 / 2075083472175292408135680000,
      781634525761118104376665310988132161 / 971139064978036847007498240000,
      2435111153780333403979406784297589 / 5533555925800779755028480000,
      91474837787737643549227633569721 / 436859678352693138554880000,
      57964935896962569781183839062639419 / 647426043318691231338332160000,
      24120851941972571216224239264409157 / 690587779539937313427554304000,
      85900389989264689243002089187388987 / 6905877795399373134275543040000,
      245823773843764533982365874015957441 / 62152900158594358208479887360000,
      43759132587925390275973120163771381 / 41435266772396238805653258240000,
      11472041754856991874949924422159593 / 55247022363194985074204344320000,
      1989309144913632790725421747442689 / 90404218412500884666879836160000]

private def leftEndpoint (right : Bool) : ℚ := if right then 9 / 4 else 1 / 2

private def tableCoeff (right : Bool) (j : ℕ) : ℚ := (shiftedTable right).getD j 0

set_option maxHeartbeats 2000000 in
private theorem tableCoeff_eq (right : Bool) {j : ℕ} (hj : j < 22) :
    tableCoeff right j = shiftedCoeff (leftEndpoint right) j := by
  cases right <;> interval_cases j <;> decide +kernel

private def bernsteinCoeff (right : Bool) (i : ℕ) : ℚ :=
  rangeSum (fun j ↦ tableCoeff right j * (choose i j : ℚ) / (choose 21 j : ℚ)) 22

set_option maxHeartbeats 2000000 in
private theorem bernstein_checked (right : Bool) {i : ℕ} (hi : i ≤ 21) :
    (1688192 : ℚ) < bernsteinCoeff right i := by
  cases right <;> interval_cases i <;> decide +kernel

private theorem shifted_eval (lo : ℚ) (t : ℝ) :
    (∑ j ∈ range 22, (shiftedCoeff lo j : ℝ) * t ^ j) =
      truncation .value ((lo : ℝ) + (7 / 4) * t) := by
  simp only [shiftedCoeff, rangeSum_eq, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, choose_eq, truncation, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [add_comm (lo : ℝ), add_pow, mul_sum]
  have hi' : i + 1 ≤ 22 := mem_range.mp hi
  calc
    _ = ∑ j ∈ range (i + 1), ((certificate .value).coeff (4 + i) : ℝ) *
        (i.choose j : ℝ) * (lo : ℝ) ^ (i - j) * (7 / 4) ^ j * t ^ j := by
      symm
      refine sum_subset (range_mono hi') fun j _ hj ↦ ?_
      have hji : i < j := by
        have hn : ¬ j < i + 1 := fun h ↦ hj (mem_range.mpr h)
        omega
      simp [Nat.choose_eq_zero_of_lt hji]
    _ = _ := by
      refine sum_congr rfl fun j _ ↦ ?_
      rw [mul_pow]
      ring

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

private theorem bernstein_weight_eq (n i : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℂ n i).eval (x : ℂ) =
      ((n.choose i : ℝ) * x^i * (1-x)^(n-i) : ℝ) := by
  simp [bernsteinPolynomial]

/-- Lower bounds on the ordinary Bernstein coefficients apply on the whole
real unit interval. -/
private theorem bernstein_eval_re_lower {P : ℂ[X]} {n : ℕ} (hdegree : P.natDegree ≤ n)
    {x lower : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hcoeff : ∀ i ≤ n, lower ≤ (bernsteinCoefficient n i P).re) :
    lower ≤ (P.eval (x : ℂ)).re := by
  let b (i : ℕ) := (n.choose i : ℝ) * x^i * (1-x)^(n-i)
  have hb (i : ℕ) : 0 ≤ b i := by
    unfold b
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx₀ _))
      (pow_nonneg (sub_nonneg.mpr hx₁) _)
  have hweights : ∑ i ∈ range (n+1), b i = 1 := by
    have hs := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
    simpa [b, eval_finsetSum, bernsteinPolynomial] using hs
  have heval : (P.eval (x : ℂ)).re =
      ∑ i ∈ range (n+1), (bernsteinCoefficient n i P).re * b i := by
    have he := congrArg (fun Q : ℂ[X] ↦ (Q.eval (x : ℂ)).re)
      (bernstein_reconstruction P n hdegree)
    simpa only [eval_finsetSum, eval_mul, eval_C, Complex.re_sum, bernstein_weight_eq,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, b] using he.symm
  rw [heval]
  calc
    lower = lower * ∑ i ∈ range (n+1), b i := by rw [hweights, mul_one]
    _ = ∑ i ∈ range (n+1), lower * b i := by rw [mul_sum]
    _ ≤ _ := sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_right (hcoeff i (Nat.lt_succ_iff.mp (mem_range.mp hi))) (hb i)

/-- Bernstein lower bounds for a real polynomial presented as a finite power sum. -/
private theorem bernstein_eval_power_lower (a : ℕ → ℝ) (n : ℕ) {x lower : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (ha : ∀ i ≤ n, lower ≤
      ∑ k ∈ range (n + 1), a k * (i.choose k : ℝ) / (n.choose k : ℝ)) :
    lower ≤ ∑ k ∈ range (n + 1), a k * x ^ k := by
  let P : ℂ[X] := ∑ k ∈ range (n + 1), monomial k (a k : ℂ)
  have hdegree : P.natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    exact fun k hk ↦ (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))
  have hcoeff (k : ℕ) (hk : k ∈ range (n + 1)) : P.coeff k = (a k : ℂ) := by
    simp only [P, finsetSum_coeff, coeff_monomial]
    rw [sum_eq_single_of_mem k hk]
    · simp
    · intro j _ hj
      simp [Ne.symm hj, hj]
  have hbound (i : ℕ) (hi : i ≤ n) : lower ≤ (bernsteinCoefficient n i P).re := by
    unfold bernsteinCoefficient
    rw [Complex.re_sum]
    convert ha i hi using 1
    refine sum_congr rfl fun k hk ↦ ?_
    rw [hcoeff k hk]
    push_cast
    simp
  have h := bernstein_eval_re_lower hdegree hx₀ hx₁ hbound
  simpa only [P, eval_finsetSum, eval_monomial, Complex.re_sum, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re] using h

private theorem value_truncation_lower (right : Bool) {u : ℝ}
    (hlo : (leftEndpoint right : ℝ) ≤ u) (hhi : u ≤ (leftEndpoint right : ℝ) + 7 / 4) :
    (1688192 : ℝ) ≤ truncation .value u := by
  let t := (u - (leftEndpoint right : ℝ)) / (7 / 4)
  have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (by norm_num)
  have ht₁ : t ≤ 1 := (div_le_iff₀ (by norm_num)).2 (by linarith)
  have ht : (leftEndpoint right : ℝ) + (7 / 4) * t = u := by dsimp [t]; ring
  have hcoeff (i : ℕ) (hi : i ≤ 21) :
      (1688192 : ℝ) ≤ ∑ j ∈ range 22, (tableCoeff right j : ℝ) *
        (i.choose j : ℝ) / (Nat.choose 21 j : ℝ) := by
    have h : (1688192 : ℝ) ≤ (bernsteinCoeff right i : ℝ) := by
      exact_mod_cast (bernstein_checked right hi).le
    simpa only [bernsteinCoeff, rangeSum_eq, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, choose_eq] using h
  have h := bernstein_eval_power_lower (fun j ↦ (tableCoeff right j : ℝ)) 21 ht₀ ht₁ hcoeff
  have heval : (∑ j ∈ range 22, (tableCoeff right j : ℝ) * t ^ j) = truncation .value u := by
    rw [← ht, ← shifted_eval]
    exact sum_congr rfl fun j hj ↦ by rw [tableCoeff_eq right (mem_range.mp hj)]
  rw [← heval]
  exact h

/-- The cleared value in the gap-four central-strip certificate is positive. -/
theorem separatedFour_cleared_value_pos {u : ℝ} (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4) :
    let E := Real.exp u - 1
    0 < -2 * E ^ 3 * (E - u) * separatedFourValue u E := by
  intro E
  have hu : 0 < u := by linarith
  have he := Real.add_one_lt_exp hu.ne'
  have hE : E ≠ 0 := by dsimp [E]; linarith
  have hEu : E - u ≠ 0 := by dsimp [E]; linarith
  have hz : E + 1 = Real.exp u := by dsimp [E]; ring
  have htrunc : (1688192 : ℝ) ≤ truncation .value u := by
    by_cases hm : u ≤ 9 / 4
    · apply value_truncation_lower false <;> norm_num [leftEndpoint] <;> linarith
    · apply value_truncation_lower true <;> norm_num [leftEndpoint] <;> linarith
  have hp : 0 < (certificate .value).polynomial u (Real.exp u) :=
    (mul_pos (pow_pos hu _) ((by norm_num : (0 : ℝ) < 1688192).trans_le htrunc)).trans_le
      (truncation_le .value hu.le)
  rw [← hz, value_clear u E hE hEu] at hp
  exact pos_of_mul_pos_right hp (by norm_num)

/-- The cleared partial derivative in the gap-four certificate is positive for positive `u`. -/
theorem separatedFour_cleared_derivative_pos {u : ℝ} (hu : 0 < u) :
    let E := Real.exp u - 1
    0 < -2 * E ^ 3 * (E - u) * separatedFourDerivative u E := by
  intro E
  have he := Real.add_one_lt_exp hu.ne'
  have hE : E ≠ 0 := by dsimp [E]; linarith
  have hEu : E - u ≠ 0 := by dsimp [E]; linarith
  have hz : E + 1 = Real.exp u := by dsimp [E]; ring
  have hp : 0 < (certificate .derivative).polynomial u (Real.exp u) :=
    (mul_pos (pow_pos hu _) (derivative_truncation_pos hu)).trans_le
      (truncation_le .derivative hu.le)
  rw [← hz, derivative_clear u E hE hEu] at hp
  exact pos_of_mul_pos_right hp (by norm_num)

end RefinedBMV.PositiveCenter
