import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometric
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripIntervals
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Box

/-! # A centered certificate for the geometric left-strip scalar -/

namespace RefinedBMV.PositiveCenter

noncomputable section

open private profileSecond profileThird positiveRadical radicalFirst radicalSecond radicalThird
  negativeMarginalFactor marginalFactorFirst geometricGEndpoint
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometric

private theorem radical_product_defect {L M : ℝ} (hL : L ≤ 1) (hM : M ≤ 1) :
    1 - Real.sqrt (1-L)*Real.sqrt (1-M) =
      (L+M-L*M)/(1+Real.sqrt (1-L)*Real.sqrt (1-M)) := by
  let R := Real.sqrt (1-L)*Real.sqrt (1-M)
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hR₂ : R^2 = (1-L)*(1-M) := by
    rw [show R^2 = (Real.sqrt (1-L))^2*(Real.sqrt (1-M))^2 by dsimp [R]; ring,
      Real.sq_sqrt (sub_nonneg.mpr hL), Real.sq_sqrt (sub_nonneg.mpr hM)]
  change 1-R = (L+M-L*M)/(1+R)
  apply (eq_div_iff (show 1+R ≠ 0 by positivity)).2
  nlinarith only [hR₂]

/-- Rationalize the product of both marginal radicals before multiplying it by
the profile derivatives. Both differences in the scalar share the same defect. -/
theorem leftStrip_geometric_scalar_rationalized {h a d : ℝ}
    (hd : upperTailLambda h d ≤ 1) (hv : upperTailLambda h (d+a) ≤ 1) :
    let v := d+a
    let V := negativeMarginalFactor h v
    let A := V - marginalFactorFirst h v
    let b := positiveRadical h
    let L := upperTailLambda h
    let D := (L d+L v-L d*L v)/(1+b d*b v)
    let r := 3+2*h
    let q₂ := 2*profileSlope h d*radicalFirst h d+radicalSecond h d
    let q₃ := 3*profileSecond h 0 d*radicalFirst h d+
      3*profileSlope h d*radicalSecond h d+radicalThird h d
    let B₂ := profileSecond h 0 d*b d+q₂
    leftStripGeometricScalar h a d =
      2*V*(b v*q₃+radicalFirst h v*B₂-profileThird h 0 d*D) +
        A*(b v*q₂-profileSecond h 0 d*D) +
        Real.exp (-(r*d))*(2*V*profileThird h r d+A*profileSecond h r d) +
        upperTailGap h d*Real.exp (-((3+h)*d))*(A-2*(2+h)*V)*geometricGEndpoint h := by
  have hD := radical_product_defect hd hv
  change 1-positiveRadical h d*positiveRadical h (d+a) =
    (upperTailLambda h d+upperTailLambda h (d+a)-upperTailLambda h d*upperTailLambda h (d+a)) /
      (1+positiveRadical h d*positiveRadical h (d+a)) at hD
  dsimp only
  rw [← hD]
  unfold leftStripGeometricScalar
  dsimp only
  ring

open private leftStripS leftStripReflectedSlope leftStrip_small_slope
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripCollision
open private weightedThird leftStrip_logKernel_mixed_lt_of_weighted
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripKernel
open private negativeMarginalFactor_pos f geometricProfile geometricScale
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometric

open private hasDerivAt_negativeMarginal
  from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftLimit

private theorem reflectedSlope_eq_half_logDerivative {p : ℕ} (hp : 0 < p) {v : ℝ}
    (hv : 0 < v) :
    leftStripReflectedSlope p v =
      (deriv (fun t ↦ compositionMoment p 0 (-t)) v / compositionMoment p 0 (-v))/2 := by
  let M (t : ℝ) := compositionMoment p 0 (-t)
  have hm : 0 < M v := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hd := hasDerivAt_negativeMarginal p v
  change leftStripReflectedSlope p v = (deriv M v/M v)/2
  change deriv (fun t ↦ Real.sqrt (M t)) v / Real.sqrt (M v) = _
  rw [((hd.sqrt hm.ne')).deriv, hd.deriv, div_div, div_div, mul_assoc, ← sq, Real.sq_sqrt hm.le,
    mul_comm 2]

/-- A scalar certificate up to seven halves extends to the entire separated
strip above its lower endpoint. The switch to the tail bound occurs at each
point of integration. -/
theorem leftStrip_logKernel_mixed_lt_of_geometric_interval {p : ℕ} (hp : 11 ≤ p)
    {ℓ u v : ℝ} (hℓ : 0 < ℓ) (hu : 0 < u) (humax : u ≤ 1/2) (hd : ℓ ≤ v-u)
    (hscalar : ∀ a d : ℝ, 0 ≤ a → a ≤ 1/2 → ℓ ≤ d → d ≤ 7/2 →
      0 < leftStripGeometricScalar (3/(p : ℝ)) a d) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have huv : u < v := by linarith
  have hv := hu.trans huv
  refine leftStrip_logKernel_mixed_lt_of_weighted hp₀ hu huv
    (leftStrip_small_slope hp hu humax) ?_
  dsimp only
  intro a ha
  have hav := ha.2.trans huv
  have hamax := ha.2.le.trans humax
  rcases le_total (v-a) (7/2) with hmid | hfar
  · have hpos := hscalar a (v-a) ha.1.le hamax
      (hd.trans (sub_le_sub_left ha.2.le _)) hmid
    have hV := negativeMarginalFactor_pos hp₀ hv
    have hfv : 0 < f (3/(p : ℝ)) v := by
      simp only [f, geometricProfile, geometricScale]
      positivity
    have hfw : 0 < f (3/(p : ℝ)) (v-a) := by
      simp only [f, geometricProfile, geometricScale]
      positivity
    exact neg_pos.mp ((mul_pos (div_pos (mul_pos hfv hfw) (mul_pos zero_lt_two hV)) hpos).trans_le
      (leftStrip_geometric_scalar_le hp₀ ha.1.le hav))
  · have hlo := negativeMarginal_logDeriv_ge_seven_halves hp₀ (v := v) (by linarith [ha.1])
    have hhi := negativeMarginal_logDeriv_le hp₀ (v := v) (by linarith [ha.1])
    have hγ := reflectedSlope_eq_half_logDerivative hp₀ hv
    have hγlo : 5/12 ≤ leftStripReflectedSlope p v := by rw [hγ]; linarith
    have hγhi : leftStripReflectedSlope p v ≤ 1 := by rw [hγ]; linarith
    exact (leftStrip_numerator_seven_halves_lt hp ha.1 hamax hfar hγlo hγhi).trans (by norm_num)

#print axioms leftStrip_geometric_scalar_rationalized
#print axioms leftStrip_logKernel_mixed_lt_of_geometric_interval

-- Coefficients are independently rounded. Monomials share the same three
-- normalized coordinates, so additions and products keep their cancellation.
namespace LocalTaylor

open RefinedBMV.PositiveCenter.SmallCorner
open RefinedBMV.PositiveCenter.SmallCorner.RoundedInterval

private abbrev Interval := RoundedInterval

private abbrev Index := ℕ × ℕ × ℕ
private abbrev Coordinates := ℝ × ℝ × ℝ
private abbrev Term := Index × Interval
private abbrev Model := List Term

private def monomial (u : Coordinates) (k : Index) : ℝ :=
  u.1 ^ k.1 * u.2.1 ^ k.2.1 * u.2.2 ^ k.2.2

private def plus (j k : Index) : Index :=
  (j.1+k.1, j.2.1+k.2.1, j.2.2+k.2.2)

private theorem monomial_plus (u : Coordinates) (j k : Index) :
    monomial u (plus j k) = monomial u j * monomial u k := by
  simp only [monomial, plus, pow_add]
  ring

private def unitBox (u : Coordinates) : Prop := |u.1| ≤ 1 ∧ |u.2.1| ≤ 1 ∧ |u.2.2| ≤ 1

private def monomialBox : Interval := interval (-1) 1

private theorem monomial_enclosed {u : Coordinates} (hu : unitBox u) (k : Index) :
    monomialBox.encloses (monomial u k) := by
  have hpow (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) : |x ^ n| ≤ 1 := by
    rw [abs_pow]
    convert pow_le_pow_left₀ (abs_nonneg x) hx n using 1
    simp
  have hm : |monomial u k| ≤ 1 := by
    unfold monomial
    simp only [abs_mul]
    have h1 := hpow _ hu.1 k.1
    have h2 := hpow _ hu.2.1 k.2.1
    have h3 := hpow _ hu.2.2 k.2.2
    have h12 : |u.1 ^ k.1| * |u.2.1 ^ k.2.1| ≤ 1 :=
      (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact (mul_le_mul h12 h3 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact encloses_interval (by simpa using (abs_le.mp hm).1)
    (by simpa using (abs_le.mp hm).2)

private inductive Models (u : Coordinates) : Model → ℝ → Prop
  | nil : Models u [] 0
  | cons {k : Index} {I : Interval} {c : ℝ} {P : Model} {x : ℝ} (hc : I.encloses c) (hx : Models u P x) :
      Models u ((k,I)::P) (c*monomial u k+x)

private def range : Model → Interval
  | [] => point 0
  | (k,I)::P =>
      (if k = (0,0,0) then I else I * monomialBox) + range P

private theorem range_sound {u : Coordinates} {P : Model} {x : ℝ}
    (hu : unitBox u) (hx : Models u P x) : (range P).encloses x := by
  induction hx with
  | nil => simpa only [range, Rat.cast_zero] using encloses_point 0
  | @cons k I c P x hc _ ih =>
    by_cases hk : k = (0,0,0)
    · subst k
      simpa [range, monomial] using encloses_add hc ih
    · simpa only [range, if_neg hk] using encloses_add
        (encloses_mul hc (monomial_enclosed hu k)) ih

private def insert (k : Index) (I : Interval) : Model → Model
  | [] => [(k,I)]
  | (j,J)::P =>
      if k = j then (j,I+J)::P else (j,J)::insert k I P

private theorem insert_sound {u : Coordinates} {k : Index} {I : Interval} {c x : ℝ}
    {P : Model} (hc : I.encloses c) (hx : Models u P x) :
    Models u (insert k I P) (c*monomial u k+x) := by
  induction hx with
  | nil => exact .cons hc .nil
  | @cons j J d P y hd _ ih =>
    by_cases h : k = j
    · subst j
      simp only [insert, if_pos rfl]
      have he : (c+d)*monomial u k+y = c*monomial u k+(d*monomial u k+y) := by ring
      exact he ▸ Models.cons (encloses_add hc hd) ‹Models u P y›
    · simp only [insert, if_neg h]
      convert Models.cons hd ih using 1 <;> ring

private def add (P Q : Model) : Model :=
  match P with
  | [] => Q
  | (k,I)::P => insert k I (add P Q)

private theorem add_sound {u : Coordinates} {P Q : Model} {x y : ℝ}
    (hx : Models u P x) (hy : Models u Q y) : Models u (add P Q) (x+y) := by
  induction hx with
  | nil => simpa only [add, zero_add] using hy
  | @cons k I c P x hc _ ih =>
    simpa only [add, add_assoc] using insert_sound hc ih

private def multiplyTerm (k : Index) (I : Interval) : Model → Model
  | [] => []
  | (j,J)::P =>
      let m := plus k j
      let C := I*J
      if m.1+m.2.1+m.2.2 ≤ 3 then insert m C (multiplyTerm k I P)
      else insert (0,0,0) (C*monomialBox) (multiplyTerm k I P)

private theorem multiplyTerm_sound {u : Coordinates} {k : Index} {I : Interval} {c x : ℝ}
    {P : Model} (hu : unitBox u) (hc : I.encloses c) (hx : Models u P x) :
    Models u (multiplyTerm k I P) ((c*monomial u k)*x) := by
  induction hx with
  | nil => simpa only [multiplyTerm, mul_zero] using Models.nil (u := u)
  | @cons j J d P y hd _ ih =>
    rw [mul_add]
    have he : c*monomial u k*(d*monomial u j) = (c*d)*monomial u (plus k j) := by
      rw [monomial_plus]
      ring
    rw [he]
    simp only [multiplyTerm]
    split
    · exact insert_sound (encloses_mul hc hd) ih
    · simpa only [monomial, pow_zero, mul_one] using
        insert_sound (k := (0,0,0))
          (encloses_mul (encloses_mul hc hd) (monomial_enclosed hu (plus k j))) ih

private def mul (P Q : Model) : Model :=
  match P with
  | [] => []
  | (k,I)::P => add (multiplyTerm k I Q) (mul P Q)

private theorem mul_sound {u : Coordinates} {P Q : Model} {x y : ℝ}
    (hu : unitBox u) (hx : Models u P x) (hy : Models u Q y) :
    Models u (mul P Q) (x*y) := by
  induction hx with
  | nil => simpa only [mul, zero_mul] using Models.nil (u := u)
  | cons hc _ ih => simpa only [mul, add_mul] using add_sound (multiplyTerm_sound hu hc hy) ih

private def ofInterval (I : Interval) : Model := [((0,0,0),I)]

private theorem ofInterval_sound {u : Coordinates} {I : Interval} {x : ℝ} (hx : I.encloses x) :
    Models u (ofInterval I) x := by
  simpa only [ofInterval, monomial, pow_zero, mul_one, add_zero] using
    Models.cons (k := (0,0,0)) hx (Models.nil (u := u))

private def const (q : ℚ) : Model := ofInterval (point q)

private theorem const_sound {u : Coordinates} (q : ℚ) : Models u (const q) (q : ℝ) :=
  ofInterval_sound (encloses_point q)

private def sub (P Q : Model) : Model := add P (mul (const (-1)) Q)

private theorem sub_sound {u : Coordinates} {P Q : Model} {x y : ℝ}
    (hu : unitBox u) (hx : Models u P x) (hy : Models u Q y) :
    Models u (sub P Q) (x-y) := by
  simpa only [sub, Rat.cast_neg, Rat.cast_one, neg_one_mul, sub_eq_add_neg] using
    add_sound hx (mul_sound hu (const_sound (-1)) hy)

private def center : Model → ℚ
  | [] => 0
  | (k,I)::P => if k = (0,0,0) then (I.lower+I.upper)/2 else center P

private def bound (P : Model) : ℚ :=
  max |(range P).lower| |(range P).upper|

private theorem abs_le_bound {u : Coordinates} {P : Model} {x : ℝ}
    (hu : unitBox u) (hx : Models u P x) : |x| ≤ (bound P : ℝ) := by
  have he := range_sound hu hx
  have hl : -((bound P : ℚ) : ℝ) ≤ ((range P).lower : ℝ) := by
    rw [← Rat.cast_neg, Rat.cast_le]
    exact (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
  have hh : ((range P).upper : ℝ) ≤ (bound P : ℝ) := by
    rw [Rat.cast_le]
    exact (le_abs_self _).trans (le_max_right _ _)
  exact abs_le.mpr ⟨hl.trans he.1, he.2.trans hh⟩

private def withError (P : Model) (e : ℚ) : Model :=
  insert (0,0,0) (interval (-e) e) P

private theorem withError_sound {u : Coordinates} {P : Model} {x y : ℝ} {e : ℚ}
    (hx : Models u P x) (he : |y-x| ≤ (e : ℝ)) : Models u (withError P e) y := by
  obtain ⟨hl, hh⟩ := abs_le.mp he
  have hm := insert_sound (k := (0,0,0))
    (encloses_interval (lo := -e) (by simpa only [Rat.cast_neg] using hl) hh) hx
  simpa only [withError, monomial, pow_zero, mul_one, sub_add_cancel] using hm

private def scale (q : ℚ) (P : Model) : Model := mul (const q) P

private theorem scale_sound {u : Coordinates} {P : Model} {x : ℝ}
    (hu : unitBox u) (q : ℚ) (hx : Models u P x) : Models u (scale q P) ((q : ℝ)*x) :=
  mul_sound hu (const_sound _) hx

private def series (coefficient : ℕ → ℚ) (P : Model) : ℕ → Model
  | 0 => []
  | n+1 => add (const (coefficient 0)) (mul (series (coefficient ∘ Nat.succ) P n) P)

open Finset

private theorem series_sound {u : Coordinates} {P : Model} {x : ℝ}
    (hu : unitBox u) (hx : Models u P x) (coefficient : ℕ → ℚ) (n : ℕ) :
    Models u (series coefficient P n) (∑ i ∈ Finset.range n, (coefficient i : ℝ) * x^i) := by
  induction n generalizing coefficient with
  | zero => simpa only [series, Finset.range_zero, sum_empty] using (Models.nil (u := u))
  | succ n ih =>
    rw [sum_range_succ', add_comm (∑ k ∈ Finset.range n, (coefficient (k+1) : ℝ)*x^(k+1))]
    simp only [pow_zero, mul_one, pow_succ, ← mul_assoc, ← Finset.sum_mul]
    exact add_sound (const_sound _) (mul_sound hu (ih _) hx)

private def expCoefficient (j : ℕ) : ℚ := 1 / j.factorial

private def expError (m : ℚ) (n : ℕ) : ℚ :=
  m ^ n * (n.succ / ((n.factorial : ℚ)*n))

private def exp (P : Model) : Option Model :=
  let c := center P
  let Q := sub P (const c)
  let m := bound Q
  if |c| ≤ 256 ∧ m ≤ 1 then
    let e := RefinedBMV.FourSpectrumLift.compactExpBounds c c
    some (mul (ofInterval (interval e.1 e.2)) (withError (series expCoefficient Q 10) (expError m 10)))
  else none

private theorem exp_sound {u : Coordinates} {P Q : Model} {x : ℝ}
    (hu : unitBox u) (hx : Models u P x) (hQ : exp P = some Q) :
    Models u Q (Real.exp x) := by
  let c := center P
  let S := sub P (const c)
  let m := bound S
  have hS : Models u S (x-(c : ℝ)) := sub_sound hu hx (const_sound c)
  have ht := abs_le_bound hu hS
  simp only [exp] at hQ
  split at hQ
  · rename_i h
    obtain ⟨hc, hm⟩ : |c| ≤ 256 ∧ m ≤ 1 := h
    have hm' : (m : ℝ) ≤ 1 := by exact_mod_cast hm
    have he := Real.exp_bound (n := 10) (ht.trans hm') (by decide)
    have hE : |Real.exp (x-(c : ℝ)) -
        ∑ i ∈ Finset.range 10, (expCoefficient i : ℝ)*(x-(c : ℝ))^i| ≤ (expError m 10 : ℝ) := by
      have hs : (∑ i ∈ Finset.range 10, (expCoefficient i : ℝ)*(x-(c : ℝ))^i) =
          ∑ i ∈ Finset.range 10, (x-(c : ℝ))^i/(i.factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        push_cast [expCoefficient]
        ring
      rw [hs]
      unfold expError
      push_cast
      refine he.trans ?_
      norm_num
      gcongr
    have hcenter := RefinedBMV.FourSpectrumLift.compactExpBounds_sound hc hc
      (x := (c : ℝ)) ⟨le_rfl, le_rfl⟩
    injection hQ with hQ
    rw [← hQ, ← show (c : ℝ)+(x-c) = x by ring, Real.exp_add]
    exact mul_sound hu (ofInterval_sound (encloses_interval hcenter.1 hcenter.2))
      (withError_sound (series_sound hu hS expCoefficient 10) hE)
  · cases hQ

private def phi (x : ℝ) : ℝ := if x = 0 then 1 else (1-Real.exp (-x))/x

private def phiCoefficient (j : ℕ) : ℚ := (-1 : ℚ)^j / (j+1).factorial

private theorem phi_error {x : ℝ} (hx : x ≠ 0) {m : ℝ} (hxm : |x| ≤ m) (hm : m ≤ 1) :
    |phi x - ∑ j ∈ Finset.range 9, (phiCoefficient j : ℝ)*x^j| ≤
      m^9 * (11 / ((10 : ℕ).factorial * (10 : ℝ))) := by
  have he := Real.exp_bound (x := -x) (n := 10) (by simpa only [abs_neg] using hxm.trans hm) (by decide)
  have hp : (∑ j ∈ Finset.range 10, (-x)^j/(j.factorial : ℝ)) =
      1-x * (∑ j ∈ Finset.range 9, (phiCoefficient j : ℝ)*x^j) := by
    rw [sum_range_succ']
    norm_num only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, phiCoefficient,
      Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    rw [Finset.mul_sum, sub_eq_add_neg, add_comm 1, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [neg_pow, pow_succ x, pow_succ (-1)]
    ring
  rw [hp, abs_neg] at he
  let T := ∑ j ∈ Finset.range 9, (phiCoefficient j : ℝ)*x^j
  have hcross : phi x - T = -(Real.exp (-x)-(1-x*T))/x := by
    rw [phi, if_neg hx]
    field_simp
    ring
  rw [hcross, abs_div, abs_neg, div_le_iff₀ (abs_pos.mpr hx)]
  refine he.trans ?_
  rw [pow_succ |x| 9]
  norm_num at he ⊢
  calc
    |x| ^ 9 * |x| * (11 / 36288000) =
        |x| ^ 9 * (11 / 36288000) * |x| := by ring
    _ ≤ _ := by gcongr <;> positivity

private def phiModel (P : Model) : Option Model :=
  let m := bound P
  if m ≤ 1 then
    some (withError (series phiCoefficient P 9) (m^9 * (11 / ((10 : ℕ).factorial * (10 : ℚ)))))
  else none

private theorem phiModel_sound {u : Coordinates} {P Q : Model} {x : ℝ}
    (hu : unitBox u) (hx : Models u P x) (hQ : phiModel P = some Q) :
    Models u Q (phi x) := by
  simp only [phiModel] at hQ
  split at hQ
  · rename_i hm
    injection hQ with hQ
    rw [← hQ]
    refine withError_sound (series_sound hu hx phiCoefficient 9) ?_
    by_cases he : x = 0
    · subst x
      have hm₀ : (0 : ℝ) ≤ (bound P : ℝ) :=
        (abs_nonneg (0 : ℝ)).trans (abs_le_bound hu hx)
      norm_num [phi, Finset.sum_range_succ, phiCoefficient, expError, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_div, Rat.cast_natCast]
      positivity
    · simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using
        phi_error he (abs_le_bound hu hx) (by exact_mod_cast hm)
  · cases hQ

private def inverse (P : Model) : Option Model :=
  let lo := (range P).lower
  let c := center P
  if 0 < lo ∧ 0 < c then
    let S := scale (-1 / c) (sub P (const c))
    let B := scale (1/c) (series (fun _ ↦ 1) S 4)
    some (withError B (bound (sub (const 1) (mul P B))/lo))
  else none

private theorem inverse_sound {u : Coordinates} {P Q : Model} {x : ℝ}
    (hu : unitBox u) (hx : Models u P x) (hQ : inverse P = some Q) :
    Models u Q (1/x) := by
  simp only [inverse] at hQ
  split at hQ
  · rename_i h
    have hlo : (0 : ℝ) < (range P).lower := by exact_mod_cast h.1
    have hle := (range_sound hu hx).1
    have hxpos := hlo.trans_le hle
    let c := center P
    let s := ((-1/c : ℚ) : ℝ)*(x-c)
    let b := ((1/c : ℚ) : ℝ) * (∑ i ∈ Finset.range 4, ((1 : ℚ) : ℝ)*s^i)
    have hs := scale_sound hu (-1/c) (sub_sound hu hx (const_sound c))
    have hb := scale_sound hu (1/c) (series_sound hu hs (fun _ ↦ 1) 4)
    change Models u _ b at hb
    have he := abs_le_bound hu (sub_sound hu (const_sound 1) (mul_sound hu hx hb))
    rw [Rat.cast_one] at he
    injection hQ with hQ
    rw [← hQ]
    refine withError_sound hb ?_
    rw [Rat.cast_div, show 1/x-b = (1-x*b)/x by field_simp [hxpos.ne'], abs_div, abs_of_pos hxpos]
    exact (div_le_div_of_nonneg_right he hxpos.le).trans
      (div_le_div_of_nonneg_left ((abs_nonneg _).trans he) hlo hle)
  · cases hQ

open private sqrtFloor grid sqrtFloor_lo grid_pos
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripIntervals

private def sqrtLower (q : ℚ) : ℚ := (sqrtFloor q : ℚ)/grid

private theorem sqrtLower_le {q : ℚ} {x : ℝ} (hq : 0 ≤ q) (h : (q : ℝ) ≤ x) :
    (sqrtLower q : ℝ) ≤ Real.sqrt x := by
  have hs := sqrtFloor_lo hq
  change (sqrtLower q)^2 ≤ q at hs
  apply Real.le_sqrt_of_sq_le
  exact (by exact_mod_cast hs : (sqrtLower q : ℝ)^2 ≤ (q : ℝ)).trans h

private def sqrtCoefficient (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | 1 => 1/2
  | 2 => -1/8
  | _ => 1/16

private def root (P : Model) : Option Model :=
  let lo := (range P).lower
  let c := center P
  let S := scale (1/c) (sub P (const c))
  let B := scale (sqrtLower c) (series sqrtCoefficient S 4)
  let lb := (range B).lower
  if 0 < lo ∧ 0 < lb then
    some (withError B (bound (sub P (mul B B))/(sqrtLower lo+lb)))
  else none

private theorem root_sound {u : Coordinates} {P Q : Model} {x : ℝ}
    (hu : unitBox u) (hx : Models u P x) (hQ : root P = some Q) :
    Models u Q (Real.sqrt x) := by
  let c := center P
  let s := ((1/c : ℚ) : ℝ)*(x-c)
  let b := (sqrtLower c : ℝ) * (∑ i ∈ Finset.range 4, (sqrtCoefficient i : ℝ)*s^i)
  have hs := scale_sound hu (1/c) (sub_sound hu hx (const_sound c))
  have hb := scale_sound hu (sqrtLower c) (series_sound hu hs sqrtCoefficient 4)
  change Models u _ b at hb
  simp only [root] at hQ
  split at hQ
  · rename_i h
    have hlo : (0 : ℝ) < (range P).lower := by exact_mod_cast h.1
    let B := scale (sqrtLower c) (series sqrtCoefficient (scale (1/c) (sub P (const c))) 4)
    have hlb : (0 : ℝ) < (range B).lower := by
      exact_mod_cast h.2
    have hxpos := hlo.trans_le (range_sound hu hx).1
    have hbpos := hlb.trans_le (range_sound hu hb).1
    have hspos := Real.sqrt_pos.mpr hxpos
    have hden := add_pos hspos hbpos
    have hsmall := sqrtLower_le h.1.le (range_sound hu hx).1
    have hcmp := add_le_add hsmall (range_sound hu hb).1
    have hS₀ : 0 ≤ sqrtLower (range P).lower := div_nonneg (Nat.cast_nonneg _) grid_pos.le
    have hp : (0 : ℝ) < (sqrtLower (range P).lower : ℝ) + (range B).lower :=
      add_pos_of_nonneg_of_pos (by exact_mod_cast hS₀) hlb
    have he := abs_le_bound hu (sub_sound hu hx (mul_sound hu hb hb))
    injection hQ with hQ
    rw [← hQ]
    refine withError_sound hb ?_
    have hId : Real.sqrt x-b = (x-b*b)/(Real.sqrt x+b) := by
      apply (eq_div_iff hden.ne').2
      nlinarith only [Real.sq_sqrt hxpos.le]
    rw [hId, abs_div, abs_of_pos hden, Rat.cast_div, Rat.cast_add]
    exact (div_le_div_of_nonneg_right he hden.le).trans
      (div_le_div_of_nonneg_left ((abs_nonneg _).trans he) hp hcmp)
  · cases hQ

private structure Enclosure (u : Coordinates) where
  value : ℝ
  model : Option Model
  sound : ∀ P, model = some P → Models u P value

private def Enclosure.num (u : Coordinates) (q : ℚ) : Enclosure u :=
  ⟨q, some (const q), fun P hP ↦ by cases hP; exact const_sound q⟩

private def Enclosure.liftUnary {u : Coordinates} (f : ℝ → ℝ) (g : Model → Option Model)
    (hg : ∀ {P Q x}, Models u P x → g P = some Q → Models u Q (f x))
    (a : Enclosure u) : Enclosure u where
  value := f a.value
  model := a.model.bind g
  sound := by
    intro P hP
    cases ha : a.model with
    | none => simp [ha] at hP
    | some A => exact hg (a.sound A ha) (by simpa [ha] using hP)

private def Enclosure.liftBinary {u : Coordinates} (f : ℝ → ℝ → ℝ) (g : Model → Model → Model)
    (hg : ∀ {P Q x y}, Models u P x → Models u Q y → Models u (g P Q) (f x y))
    (a b : Enclosure u) : Enclosure u where
  value := f a.value b.value
  model := a.model.bind fun P ↦ b.model.map (g P)
  sound := by
    intro P hP
    cases ha : a.model with
    | none => simp [ha] at hP
    | some A =>
      cases hb : b.model with
      | none => simp [ha, hb] at hP
      | some B =>
        have he : g A B = P := by simpa [ha, hb] using hP
        rw [← he]
        exact hg (a.sound A ha) (b.sound B hb)

private instance {u : Coordinates} : Add (Enclosure u) :=
  ⟨Enclosure.liftBinary (·+·) add (fun h₁ h₂ ↦ add_sound h₁ h₂)⟩

private def Enclosure.sub {u : Coordinates} (hu : unitBox u) :
    Enclosure u → Enclosure u → Enclosure u :=
  Enclosure.liftBinary (·-·) LocalTaylor.sub (fun h₁ h₂ ↦ sub_sound hu h₁ h₂)

private def Enclosure.mul {u : Coordinates} (hu : unitBox u) :
    Enclosure u → Enclosure u → Enclosure u :=
  Enclosure.liftBinary (·*·) LocalTaylor.mul (fun h₁ h₂ ↦ mul_sound hu h₁ h₂)

private def Enclosure.exp {u : Coordinates} (hu : unitBox u) : Enclosure u → Enclosure u :=
  Enclosure.liftUnary Real.exp LocalTaylor.exp (fun h₁ h₂ ↦ exp_sound hu h₁ h₂)

private def Enclosure.phi {u : Coordinates} (hu : unitBox u) : Enclosure u → Enclosure u :=
  Enclosure.liftUnary LocalTaylor.phi phiModel (fun h₁ h₂ ↦ phiModel_sound hu h₁ h₂)

private def Enclosure.root {u : Coordinates} (hu : unitBox u) : Enclosure u → Enclosure u :=
  Enclosure.liftUnary Real.sqrt LocalTaylor.root (fun h₁ h₂ ↦ root_sound hu h₁ h₂)

private def Enclosure.inverse {u : Coordinates} (hu : unitBox u) : Enclosure u → Enclosure u :=
  Enclosure.liftUnary (fun x ↦ 1/x) LocalTaylor.inverse (fun h₁ h₂ ↦ inverse_sound hu h₁ h₂)

private structure Arithmetic (R : Type) where
  num : ℚ → R
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  exp : R → R
  phi : R → R
  root : R → R
  inverse : R → R

private def realArithmetic : Arithmetic ℝ :=
  ⟨(↑), (·+·), (·-·), (·*·), Real.exp, phi, Real.sqrt, fun x ↦ 1/x⟩

private def enclosureArithmetic {u : Coordinates} (hu : unitBox u) :
    Arithmetic (Enclosure u) :=
  ⟨Enclosure.num u, (·+·), Enclosure.sub hu, Enclosure.mul hu, Enclosure.exp hu,
    Enclosure.phi hu, Enclosure.root hu, Enclosure.inverse hu⟩

private def modelArithmetic : Arithmetic (Option Model) :=
  let binary (f : Model → Model → Model) (P Q : Option Model) := P.bind fun p ↦ Q.map (f p)
  ⟨fun q ↦ some (const q), binary add, binary sub, binary mul, (·.bind exp), (·.bind phiModel),
    (·.bind root), (·.bind inverse)⟩

private def Arithmetic.sq {R : Type} (o : Arithmetic R) (a : R) : R := o.mul a a

private def Arithmetic.cube {R : Type} (o : Arithmetic R) (a : R) : R := o.mul (o.sq a) a

private def Arithmetic.neg {R : Type} (o : Arithmetic R) (a : R) : R := o.sub (o.num 0) a

private def Arithmetic.div {R : Type} (o : Arithmetic R) (a b : R) : R :=
  o.mul a (o.inverse b)

private def Arithmetic.decay {R : Type} (o : Arithmetic R) (r t : R) : R :=
  o.exp (o.neg (o.mul r t))

private def Arithmetic.gap {R : Type} (o : Arithmetic R) (h t : R) : R :=
  let ht := o.mul (o.num (1/2)) (o.mul h t)
  o.mul (o.mul (o.mul (o.num (1/2)) t) (o.phi ht)) (o.add (o.num 1) (o.exp (o.neg ht)))

private def Arithmetic.radicalJet {R : Type} (o : Arithmetic R)
    (h c F e E decayTwo decayG : R) : R × R × R × R × R :=
  let j := o.add (o.num 1) h
  let g := o.add (o.num 3) h
  let r := o.add (o.sub (o.mul j F) (o.num 1)) E
  let r₁ := o.mul j (o.sub e E)
  let r₂ := o.mul j (o.add (o.mul (o.neg h) e) (o.mul j E))
  let K := o.mul F r
  let K₁ := o.add (o.mul e r) (o.mul F r₁)
  let K₂ := o.add (o.add (o.mul (o.mul (o.neg h) e) r) (o.mul (o.mul (o.num 2) e) r₁))
    (o.mul F r₂)
  let pref := o.mul (o.mul (o.num 2) c) decayTwo
  let lam := o.add (o.mul (o.add (o.num 1) (o.mul g F)) decayG)
    (o.mul (o.mul c (o.sq F)) decayTwo)
  let b := o.root (o.sub (o.num 1) lam)
  let inv := o.inverse (o.mul (o.num 2) b)
  let b₁ := o.mul (o.mul pref K) inv
  let b₂ := o.mul (o.sub (o.mul pref (o.sub K₁ (o.mul (o.num 2) K))) (o.mul (o.num 2) (o.sq b₁))) inv
  let b₃ := o.mul (o.sub (o.mul pref (o.add (o.sub K₂ (o.mul (o.num 4) K₁)) (o.mul (o.num 4) K)))
    (o.mul (o.mul (o.num 6) b₁) b₂)) inv
  (lam, b, b₁, b₂, b₃)

private def Arithmetic.scalar {R : Type} (o : Arithmetic R) (h a d : R) : R :=
  let v := o.add d a
  let g := o.add (o.num 3) h
  let r := o.add (o.num 3) (o.mul (o.num 2) h)
  let k := o.add (o.num 2) h
  let c := o.div (o.mul g r) (o.num 2)
  let j := o.add (o.num 1) h
  let Fd := o.gap h d
  let Fv := o.gap h v
  let eD := o.decay h d
  let eV := o.decay h v
  let Eg := o.decay g d
  let Jd := o.radicalJet h c Fd eD (o.decay j d) (o.decay (o.num 2) d) Eg
  let Jv := o.radicalJet h c Fv eV (o.decay j v) (o.decay (o.num 2) v) (o.decay g v)
  let (Ld, bd, bd₁, bd₂, bd₃) := Jd
  let (Lv, bv, bv₁, _, _) := Jv
  let L := o.sub (o.inverse Fd) h
  let α := o.sub (o.num 1) L
  let β := o.sub α r
  let q := o.mul L (o.add h L)
  let q₁ := o.mul q (o.add h (o.mul (o.num 2) L))
  let P₂ := o.add (o.sq α) q
  let P₃ := o.sub (o.add (o.cube α) (o.mul (o.mul (o.num 3) α) q)) q₁
  let Q₂ := o.add (o.sq β) q
  let Q₃ := o.sub (o.add (o.cube β) (o.mul (o.mul (o.num 3) β) q)) q₁
  let D := o.div (o.sub (o.add Ld Lv) (o.mul Ld Lv)) (o.add (o.num 1) (o.mul bd bv))
  let q₂ := o.add (o.mul (o.mul (o.num 2) α) bd₁) bd₂
  let q₃ := o.add (o.add (o.mul (o.mul (o.num 3) P₂) bd₁)
    (o.mul (o.mul (o.num 3) α) bd₂)) bd₃
  let B₂ := o.add (o.mul P₂ bd) q₂
  let Δ₂ := o.sub (o.mul bv q₂) (o.mul P₂ D)
  let Δ₃ := o.sub (o.add (o.mul bv q₃) (o.mul bv₁ B₂)) (o.mul P₃ D)
  let En := o.decay r v
  let ec := o.mul c (o.exp (o.neg v))
  let V := o.sub (o.add (o.sub En (o.num 1)) (o.mul r Fv)) (o.mul (o.mul c (o.sq Fv)) (o.exp (o.neg v)))
  let V₁ := o.sub (o.mul r (o.sub eV En)) (o.mul ec (o.sub (o.mul (o.mul (o.num 2) Fv) eV) (o.sq Fv)))
  let A := o.sub V V₁
  let VV := o.mul (o.num 2) V
  let G := o.div (o.mul (o.mul (o.add h (o.num 1)) (o.add h (o.num 2)))
    (o.add (o.mul (o.num 2) h) (o.num 3))) (o.num 2)
  o.add (o.add (o.add (o.mul VV Δ₃) (o.mul A Δ₂))
    (o.mul (o.decay r d) (o.add (o.mul VV Q₃) (o.mul A Q₂))))
    (o.mul (o.mul (o.mul Fd Eg) (o.sub A (o.mul (o.mul (o.num 2) k) V))) G)

private theorem scalar_value {u : Coordinates} (hu : unitBox u) (H A D : Enclosure u) :
    ((enclosureArithmetic hu).scalar H A D).value = realArithmetic.scalar H.value A.value D.value := by
  rfl

private theorem scalar_model {u : Coordinates} (hu : unitBox u) (H A D : Enclosure u) :
    ((enclosureArithmetic hu).scalar H A D).model = modelArithmetic.scalar H.model A.model D.model := by
  rfl

open private radicandJet positive_marginal_eq
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometric

private theorem gap_eq {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    realArithmetic.gap h t = upperTailGap h t := by
  let y : ℝ := h*t/2
  have hy : 0 < y := div_pos (mul_pos hh ht) zero_lt_two
  have hExp : Real.exp (-(h*t)) = Real.exp (-y)*Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [y]
    ring
  simp only [Arithmetic.gap, Arithmetic.neg, realArithmetic, Rat.cast_one, Rat.cast_zero]
  rw [show (↑(1/2 : ℚ) : ℝ)*(h*t) = y by push_cast; dsimp [y]; ring, zero_sub,
    phi, if_neg hy.ne', upperTailGap, hExp]
  dsimp [y] at hy ⊢
  have hht : h*t ≠ 0 := (mul_pos hh ht).ne'
  push_cast
  field_simp [hht, hh.ne', ht.ne']
  <;> ring

private theorem slope_eq {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    1/upperTailGap h t - h = upperTailSlope h t := by
  have hp : 0 < upperTailGap h t := (tail_gap_pos hh ht)
  have he : Real.exp (-(h*t)) = upperTailSlope h t*upperTailGap h t := by
    have h := upperTailGap_logDeriv hh ht
    rw [(hasDerivAt_upperTailGap hh).deriv] at h
    exact (div_eq_iff hp.ne').mp h
  have hf : h*upperTailGap h t = 1-Real.exp (-(h*t)) := by
    unfold upperTailGap
    field_simp [hh.ne']
  apply (sub_eq_iff_eq_add).2
  apply (div_eq_iff hp.ne').2
  nlinarith only [he, hf]

private theorem decay_eq (r t : ℝ) : realArithmetic.decay r t = Real.exp (-(r*t)) := by
  simp [Arithmetic.decay, Arithmetic.neg, realArithmetic]

private theorem radicalJet_eq (h t : ℝ) :
    realArithmetic.radicalJet h (geometricScale h) (upperTailGap h t)
      (Real.exp (-(h*t))) (Real.exp (-((1+h)*t))) (Real.exp (-(2*t))) (Real.exp (-((3+h)*t))) =
    (upperTailLambda h t, positiveRadical h t, radicalFirst h t, radicalSecond h t, radicalThird h t) := by
  simp only [Arithmetic.radicalJet, Arithmetic.sq, Arithmetic.neg, realArithmetic,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, zero_sub, upperTailLambda, positiveRadical,
    radicalFirst, radicalSecond, radicalThird, radicandJet, geometricScale,
    div_eq_mul_inv, one_mul, pow_two]

private theorem radicand_nonneg {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    upperTailLambda (3/(p : ℝ)) t ≤ 1 := by
  have hm := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp ht.ne')
  change 0 < leftStripS p t at hm
  rw [positive_marginal_eq hp ht] at hm
  have hf : 0 < f (3/(p : ℝ)) t := by
    simp only [f, geometricProfile, geometricScale]
    positivity
  have h := pos_of_mul_pos_right hm hf.le
  exact sub_nonneg.mp (Real.sqrt_pos.mp h).le

private theorem real_num (q : ℚ) : realArithmetic.num q = (q : ℝ) := rfl
private theorem real_add (x y : ℝ) : realArithmetic.add x y = x+y := rfl
private theorem real_sub (x y : ℝ) : realArithmetic.sub x y = x-y := rfl
private theorem real_mul (x y : ℝ) : realArithmetic.mul x y = x*y := rfl
private theorem real_exp (x : ℝ) : realArithmetic.exp x = Real.exp x := rfl
private theorem real_inv (x : ℝ) : realArithmetic.inverse x = 1/x := rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 600000 in
private theorem realScalar_eq {p : ℕ} (hp : 0 < p) {a d : ℝ}
    (hd : 0 < d) (hv : 0 < d+a) :
    realArithmetic.scalar (3/(p : ℝ)) a d = leftStripGeometricScalar (3/(p : ℝ)) a d := by
  let h : ℝ := 3/(p : ℝ)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  change realArithmetic.scalar h a d = leftStripGeometricScalar h a d
  rw [leftStrip_geometric_scalar_rationalized (radicand_nonneg hp hd) (radicand_nonneg hp hv)]
  have hc : (3+h)*(3+2*h)*(1/(2 : ℝ)) = geometricScale h := by
    rw [geometricScale, mul_one_div]
  simp only [Arithmetic.scalar, Arithmetic.sq, Arithmetic.cube, Arithmetic.div, Arithmetic.neg,
    decay_eq, real_num, real_add, real_sub, real_mul, real_exp, real_inv,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, zero_sub, hc, gap_eq hh hd, gap_eq hh hv,
    radicalJet_eq, slope_eq hh hd]
  simp only [profileSecond, profileThird, profileCurvature, profileSlope, sub_zero, pow_two,
    pow_succ, pow_one, negativeMarginalFactor, marginalFactorFirst, geometricGEndpoint,
    mul_one_div, div_eq_mul_inv, one_mul, pow_zero]
  simp only [h, div_eq_mul_inv]

private abbrev Endpoints := ℚ × ℚ

private def midpoint (B : Endpoints) : ℚ := (B.1+B.2)/2

private def radius (B : Endpoints) : ℚ := (B.2-B.1)/2

private def inputModel (B : Endpoints) (i : Index) : Model :=
  [(i, point (radius B)), ((0,0,0), point (midpoint B))]

private def unit {B : Endpoints} (x : ℝ) : ℝ := (x-(midpoint B : ℝ))/(radius B : ℝ)

private def InBox (B : Endpoints) (x : ℝ) : Prop := (B.1 : ℝ) ≤ x ∧ x ≤ (B.2 : ℝ)

private theorem radius_pos {B : Endpoints} (hB : B.1 < B.2) : (0 : ℝ) < (radius B : ℝ) := by
  have hb : 0 < radius B := div_pos (sub_pos.mpr hB) (by norm_num)
  exact_mod_cast hb

private theorem unit_abs_le {B : Endpoints} {x : ℝ} (hB : B.1 < B.2) (hx : InBox B x) :
    |unit (B := B) x| ≤ 1 := by
  unfold unit
  rw [abs_div, abs_of_pos (radius_pos hB), div_le_iff₀ (radius_pos hB), one_mul]
  obtain ⟨hl, hh⟩ := hx
  apply abs_le.mpr
  push_cast [midpoint, radius]
  exact ⟨by linarith, by linarith⟩

private theorem input_sound {B : Endpoints} (hB : B.1 < B.2) (x : ℝ)
    {u : Coordinates} {i : Index} (hi : monomial u i = unit (B := B) x) :
    Models u (inputModel B i) x := by
  have hx : (radius B : ℝ)*monomial u i + (midpoint B : ℝ) = x := by
    rw [hi, unit]
    field_simp [(radius_pos hB).ne']
    ring
  rw [← hx]
  exact Models.cons (encloses_point _) (const_sound _)

private abbrev Box := Endpoints × Endpoints × Endpoints

private def check (B : Box) : Bool :=
  match modelArithmetic.scalar (some (inputModel B.1 (1,0,0)))
      (some (inputModel B.2.1 (0,1,0))) (some (inputModel B.2.2 (0,0,1))) with
  | some P => decide (0 < (range P).lower)
  | none => false

private theorem check_sound {B : Box} {p : ℕ} (hp : 0 < p) {a d : ℝ}
    (hd₀ : 0 < d) (hv : 0 < d+a)
    (hH : InBox B.1 (3/(p : ℝ))) (hA : InBox B.2.1 a) (hD : InBox B.2.2 d)
    (hw : B.1.1 < B.1.2 ∧ B.2.1.1 < B.2.1.2 ∧ B.2.2.1 < B.2.2.2)
    (hc : check B = true) : 0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  let h : ℝ := 3/(p : ℝ)
  let u : Coordinates := (unit (B := B.1) h, unit (B := B.2.1) a, unit (B := B.2.2) d)
  have hu : unitBox u := ⟨unit_abs_le hw.1 hH, unit_abs_le hw.2.1 hA, unit_abs_le hw.2.2 hD⟩
  let H : Enclosure u := ⟨h, some (inputModel B.1 (1,0,0)), fun P hP ↦ by
    cases hP
    exact input_sound hw.1 h (by simp [u, monomial])⟩
  let A : Enclosure u := ⟨a, some (inputModel B.2.1 (0,1,0)), fun P hP ↦ by
    cases hP
    exact input_sound hw.2.1 a (by simp [u, monomial])⟩
  let D : Enclosure u := ⟨d, some (inputModel B.2.2 (0,0,1)), fun P hP ↦ by
    cases hP
    exact input_sound hw.2.2 d (by simp [u, monomial])⟩
  let S := (enclosureArithmetic hu).scalar H A D
  have he := scalar_model hu H A D
  change S.model = _ at he
  unfold check at hc
  rw [← show S.model = _ from he] at hc
  cases hS : S.model with
  | none => simp [hS] at hc
  | some P =>
    have hl : (0 : ℚ) < (range P).lower := by simpa [hS] using hc
    have hbound := (range_sound hu (S.sound P hS)).1
    have hc' : (0 : ℝ) < ((range P).lower : ℝ) := by exact_mod_cast hl
    have hs : S.value = _ := (scalar_value hu H A D).trans (realScalar_eq hp hd₀ hv)
    exact hs ▸ hc'.trans_le hbound

private def leftHalf (B : Endpoints) : Endpoints := (B.1, midpoint B)
private def rightHalf (B : Endpoints) : Endpoints := (midpoint B, B.2)

private theorem inHalf {B : Endpoints} {x : ℝ} (hx : InBox B x) :
    InBox (leftHalf B) x ∨ InBox (rightHalf B) x := by
  rcases le_total x (midpoint B : ℝ) with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

private def validWidth (B : Box) : Prop :=
  B.1.1 < B.1.2 ∧ B.2.1.1 < B.2.1.2 ∧ B.2.2.1 < B.2.2.2

private theorem halfWidths {B : Endpoints} (h : B.1 < B.2) :
    (leftHalf B).1 < (leftHalf B).2 ∧ (rightHalf B).1 < (rightHalf B).2 := by
  dsimp [leftHalf, rightHalf, midpoint]
  exact ⟨by linarith, by linarith⟩

private def splitBox (B : Box) : Box × Box :=
  let (H, A, D) := B
  if radius A ≤ 3/2 * radius H ∧ radius D ≤ 3/2 * radius H then
    ((leftHalf H, A, D), (rightHalf H, A, D))
  else if radius D ≤ radius A then
    ((H, leftHalf A, D), (H, rightHalf A, D))
  else
    ((H, A, leftHalf D), (H, A, rightHalf D))

private def contains (B : Box) (h a d : ℝ) : Prop :=
  InBox B.1 h ∧ InBox B.2.1 a ∧ InBox B.2.2 d

private theorem split_sound {B : Box} {h a d : ℝ}
    (hw : validWidth B) (hx : contains B h a d) :
    (validWidth (splitBox B).1 ∧ contains (splitBox B).1 h a d) ∨
    (validWidth (splitBox B).2 ∧ contains (splitBox B).2 h a d) := by
  obtain ⟨H, A, D⟩ := B
  simp only [splitBox]
  split
  · rcases inHalf hx.1 with hl | hr
    · exact Or.inl ⟨⟨(halfWidths hw.1).1, hw.2⟩, ⟨hl, hx.2⟩⟩
    · exact Or.inr ⟨⟨(halfWidths hw.1).2, hw.2⟩, ⟨hr, hx.2⟩⟩
  split
  · rcases inHalf hx.2.1 with hl | hr
    · exact Or.inl ⟨⟨hw.1, (halfWidths hw.2.1).1, hw.2.2⟩, ⟨hx.1, hl, hx.2.2⟩⟩
    · exact Or.inr ⟨⟨hw.1, (halfWidths hw.2.1).2, hw.2.2⟩, ⟨hx.1, hr, hx.2.2⟩⟩
  · rcases inHalf hx.2.2 with hl | hr
    · exact Or.inl ⟨⟨hw.1, hw.2.1, (halfWidths hw.2.2).1⟩, ⟨hx.1, hx.2.1, hl⟩⟩
    · exact Or.inr ⟨⟨hw.1, hw.2.1, (halfWidths hw.2.2).2⟩, ⟨hx.1, hx.2.1, hr⟩⟩

private def checkCover : ℕ → Box → Bool
  | 0, B => check B
  | n+1, B => check B || (checkCover n (splitBox B).1 && checkCover n (splitBox B).2)

private theorem checkCover_sound {p : ℕ} (hp : 0 < p) {a d : ℝ}
    (hd : 0 < d) (hv : 0 < d+a) (n : ℕ) {B : Box} (hw : validWidth B)
    (hx : contains B (3/(p : ℝ)) a d) (hc : checkCover n B = true) :
    0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  induction n generalizing B with
  | zero => exact check_sound hp hd hv hx.1 hx.2.1 hx.2.2 hw hc
  | succ n ih =>
    simp only [checkCover, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨hl, hr⟩
    · exact check_sound hp hd hv hx.1 hx.2.1 hx.2.2 hw hc
    · rcases split_sound hw hx with hl' | hr'
      · exact ih hl'.1 hl'.2 hl
      · exact ih hr'.1 hr'.2 hr

private def band (lo hi : ℚ) : Box := ((0,3/11), (0,1/2), (lo,hi))

private theorem band_sound {p : ℕ} (hp : 11 ≤ p) {a d : ℝ}
    (ha : 0 ≤ a) (hamax : a ≤ 1/2) (hd₀ : 0 < d)
    {lo hi : ℚ} (hw : lo < hi) (hd : (lo : ℝ) ≤ d) (hdmax : d ≤ (hi : ℝ))
    {n : ℕ} (hc : checkCover n (band lo hi) = true) :
    0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : InBox (0,3/11) (3/(p : ℝ)) := by
    constructor
    · push_cast
      positivity
    · norm_num
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have ha' : InBox (0,1/2) a := ⟨by simpa using ha, by simpa using hamax⟩
  exact checkCover_sound hp₀ hd₀ (by linarith) n
    ⟨by norm_num [band], by norm_num [band], hw⟩ ⟨hh, ha', hd, hdmax⟩ hc

/-- The six closed bands for the moderate geometric left strip. -/
def moderateLeftStripCheck (depth : ℕ) : Bool :=
  checkCover depth (band 1 (5/4)) &&
  checkCover depth (band (5/4) (3/2)) &&
  checkCover depth (band (3/2) 2) &&
  checkCover depth (band 2 (5/2)) &&
  checkCover depth (band (5/2) 3) &&
  checkCover depth (band 3 (7/2))

/-- A successful centered enclosure check certifies the exact scalar
throughout the requested real interval. -/
theorem leftStripGeometricScalar_pos_of_check {depth : ℕ}
    (hcheck : moderateLeftStripCheck depth = true) {p : ℕ} (hp : 11 ≤ p)
    {a d : ℝ} (ha : 0 ≤ a) (hamax : a ≤ 1/2) (hd : 1 ≤ d) (hdmax : d ≤ 7/2) :
    0 < leftStripGeometricScalar (3/(p : ℝ)) a d := by
  simp only [moderateLeftStripCheck, Bool.and_eq_true, and_assoc] at hcheck
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hcheck
  have hd₀ : 0 < d := by linarith
  by_cases h₁ : d ≤ 5/4
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using hd)
      (by simpa using h₁) c₁
  by_cases h₂ : d ≤ 3/2
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₁)))
      (by simpa using h₂) c₂
  by_cases h₃ : d ≤ 2
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₂)))
      (by simpa using h₃) c₃
  by_cases h₄ : d ≤ 5/2
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₃)))
      (by simpa using h₄) c₄
  by_cases h₅ : d ≤ 3
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₄)))
      (by simpa using h₅) c₅
  · exact band_sound hp ha hamax hd₀ (by norm_num) (by simpa using (le_of_lt (lt_of_not_ge h₅)))
      (by simpa using hdmax) c₆

end LocalTaylor

/-- A checked moderate strip gives the strict mixed-derivative sign for the
original kernel at every gap at least one. -/
theorem leftStrip_logKernel_mixed_lt_of_certificate {depth : ℕ}
    (hcheck : LocalTaylor.moderateLeftStripCheck depth = true)
    {p : ℕ} (hp : 11 ≤ p) {u v : ℝ} (hu : 0 < u) (humax : u ≤ 1/2) (hd : 1 ≤ v-u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 :=
  leftStrip_logKernel_mixed_lt_of_geometric_interval hp (by norm_num) hu humax hd
    (fun _ _ ↦ LocalTaylor.leftStripGeometricScalar_pos_of_check hcheck hp)

#print axioms LocalTaylor.leftStripGeometricScalar_pos_of_check
#print axioms leftStrip_logKernel_mixed_lt_of_certificate


end

end RefinedBMV.PositiveCenter
