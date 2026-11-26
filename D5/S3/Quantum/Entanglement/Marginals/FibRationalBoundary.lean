/- GID: D5/S3/Quantum/Entanglement/Marginals/FibRationalBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibRationalBoundary
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact arithmetic of rational points on the feasible Fibonacci coupling boundary. -/

import D5.S3.Quantum.Entanglement.Marginals.FibQuadraticCompletion
import Mathlib.Topology.Instances.Rat
import D5.S3.Quantum.AURICOmega.OmegaShadowBridge

/-! Rational boundary points of the two residual disks for coherent Fibonacci data. -/

open Complex
open D5.S3.Quantum.AURICOmega.OmegaShadowBridge
open Omega.Projective.Circle (Coordinates cayleyX cayleyY)
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open scoped ComplexConjugate ComplexOrder
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.Marginals.FibQuadraticCompletion
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank (rational_pivot_of_trace)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary

private def phase (t : ℝ) : ℂ :=
  ⟨(1 - t^2) / (1 + t^2), 2*t / (1 + t^2)⟩

private def fromNat (n : ℕ) : Omega.Nat :=
  n.rec Omega.Nat.zero (fun _ q => q.succ)

/-- Encode a standard integer in Omega arithmetic. -/
def fromInt : ℤ → Omega.Int
  | .ofNat n => .ofNat (fromNat n)
  | .negSucc n => .negSucc (fromNat n)

private theorem to_fromNat (n : ℕ) : toStdNat (fromNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/-- Reading the Omega encoding recovers the standard integer. -/
theorem to_fromInt (n : ℤ) : toStdInt (fromInt n) = n := by
  cases n with
  | ofNat n => exact congrArg Int.ofNat (to_fromNat n)
  | negSucc n => exact congrArg Int.negSucc (to_fromNat n)

private theorem value_read (a : Omega.Int) (d : Omega.Nat) :
    toReal (Omega.IntRatio.value a d) = (toStdInt a : ℝ) / (toStdNat d : ℝ) := by
  induction d using Omega.Nat.rec with
  | zero => simp [toReal, Omega.IntRatio.value, toRat, toStdNat]
  | succ d ih =>
    change (↑((toStdInt a : ℚ) / (Int.ofNat (toStdNat d).succ : ℚ)) : ℝ) =
      (toStdInt a : ℝ) / ((toStdNat d).succ : ℝ)
    norm_cast

private theorem toStd_normSq (p q : Omega.Int) :
    (toStdNat (Omega.Projective.Circle.normSq p q) : ℤ) =
      toStdInt p * toStdInt p + toStdInt q * toStdInt q := by
  have h := (Coordinates.mk p q).normSq_cast
  have hx := Omega.Eq.rec (motive := fun y _ =>
    toStdInt (.ofNat (Omega.Projective.Circle.normSq p q)) = toStdInt y) rfl h
  change (toStdNat (Omega.Projective.Circle.normSq p q) : ℤ) = _ at hx
  simpa only [Omega.Int.square, toStdInt_add, toStdInt_mul] using hx

private theorem phase_normSq (t : ℚ) : normSq (phase t) = 1 := by
  let p := fromInt t.num
  let q := Omega.Int.ofNat (fromNat t.den)
  have hp : toStdInt p = t.num := to_fromInt _
  have hq : toStdInt q = (t.den : ℤ) := congrArg Int.ofNat (to_fromNat _)
  have hden : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  have hq' : Omega.Not (Omega.Eq q Omega.Int.zero) := by
    intro h
    have he := Omega.Eq.rec (motive := fun y _ => toStdInt q = toStdInt y) rfl h
    have hzero : toStdInt Omega.Int.zero = 0 := rfl
    rw [hq, hzero] at he
    exact (t.den_ne_zero (Int.ofNat_eq_zero.mp he)).elim
  have h := D5.S3.Quantum.AURICOmega.OmegaShadowBridge.cayley_circle_unit p q
    (Omega.Or.inr hq')
  have hD : (toStdNat (Omega.Projective.Circle.normSq p q) : ℝ) =
      (t.num : ℝ)^2 + (t.den : ℝ)^2 := by
    have h := congrArg (fun k : ℤ => (k : ℝ)) (toStd_normSq p q)
    simpa only [hp, hq, Int.cast_natCast, Int.cast_add, Int.cast_mul, pow_two] using h
  have hsub (a b : Omega.Int) : toStdInt (a.sub b) = toStdInt a - toStdInt b := by
    change toStdInt (Omega.Int.add a (Omega.Int.neg b)) = _
    rw [toStdInt_add, toStdInt_neg, sub_eq_add_neg]
  simp only [cayleyX, cayleyY, value_read, Omega.Int.square, hsub, toStdInt_add,
    toStdInt_mul, hp, hq, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, hD] at h
  have ht : (t : ℝ) = (t.num : ℝ) / (t.den : ℝ) := Rat.cast_def t
  rw [phase, Complex.normSq_mk]
  change (((1 - (t : ℝ)^2)/(1 + (t : ℝ)^2)) *
    ((1 - (t : ℝ)^2)/(1 + (t : ℝ)^2))) +
    (2*(t : ℝ)/(1 + (t : ℝ)^2)) * (2*(t : ℝ)/(1 + (t : ℝ)^2)) = 1
  rw [ht]
  have hDpos : 0 < (t.num : ℝ)^2 + (t.den : ℝ)^2 := by positivity
  field_simp at h ⊢
  linear_combination h

private theorem phase_continuous : Continuous phase := by
  have hx : Continuous (fun t : ℝ => (1 - t^2) / (1 + t^2)) :=
    (continuous_const.sub (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity)
  have hy : Continuous (fun t : ℝ => 2*t / (1 + t^2)) :=
    (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity)
  have he : (⇑Complex.equivRealProdCLM.symm ∘
      fun t : ℝ => ((1 - t^2) / (1 + t^2), 2*t / (1 + t^2))) = phase := by
    funext t
    rw [Function.comp_apply, Complex.equivRealProdCLM_symm_apply]
    apply Complex.ext <;>
      simp only [phase, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        zero_add, add_zero, sub_self]
  rw [← he]
  exact Complex.equivRealProdCLM.symm.continuous.comp (hx.prodMk hy)

private theorem phase_rat (t : ℚ) : RationalEntry (phase t) := by
  refine ⟨(1-t^2)/(1+t^2), 2*t/(1+t^2), ?_, ?_⟩
  · change (((1-t^2)/(1+t^2) : ℚ) : ℝ) = (1-(t : ℝ)^2)/(1+(t : ℝ)^2)
    push_cast
    rfl
  · change (((2*t)/(1+t^2) : ℚ) : ℝ) = 2*(t : ℝ)/(1+(t : ℝ)^2)
    push_cast
    rfl

private theorem phase_covers {u : ℂ} (hu : normSq u = 1) (hu' : u ≠ -1) :
    ∃ t : ℝ, phase t = u := by
  have hunit : u.re * u.re + u.im * u.im = 1 := by
    simpa only [normSq_apply] using hu
  have hr : 1 + u.re ≠ 0 := by
    intro h
    apply hu'
    apply Complex.ext
    · simp
      linarith
    · simp
      have h' : u.re = -1 := by linarith
      rw [h'] at hunit
      nlinarith
  let t := u.im / (1 + u.re)
  have hden : 1 + t^2 = 2/(1 + u.re) := by
    dsimp [t]
    field_simp
    nlinarith only [hunit]
  have ht : 1 - t^2 = u.re * (1 + t^2) := by
    rw [hden]
    dsimp [t]
    field_simp
    nlinarith only [hunit]
  have hp : 1 + t ^ 2 ≠ 0 := by positivity
  refine ⟨t, Complex.ext ?_ ?_⟩
  · change (1 - t^2) / (1 + t^2) = u.re
    exact (div_eq_iff hp).mpr ht
  · change 2*t / (1 + t^2) = u.im
    rw [hden]
    dsimp [t]
    field_simp

private theorem rational_circle_point (p q a z : ℂ) (s : ℝ)
    (qp : RationalEntry p) (qa : RationalEntry a)
    (hz : normSq (z - p) = normSq a) (hinside : normSq (z - q) < s) :
    ∃ w : ℂ, RationalEntry w ∧ normSq (w - p) = normSq a ∧ normSq (w - q) < s := by
  by_cases ha : a = 0
  · have h : z = p := sub_eq_zero.mp (normSq_eq_zero.mp (by simpa [ha] using hz))
    subst z
    exact ⟨p, qp, by simp [ha], hinside⟩
  let u := (z - p) / a
  have hu : normSq u = 1 := by
    rw [normSq_div, hz, div_self (fun h => ha (normSq_eq_zero.mp h))]
  have hpu : p + a * u = z := by
    dsimp [u]
    field_simp
    ring
  by_cases hu' : u = -1
  · rw [hu', mul_neg, mul_one, ← sub_eq_add_neg] at hpu
    refine ⟨z, hpu ▸ rationalComplex.sub_mem qp qa, hz, hinside⟩
  obtain ⟨t, ht⟩ := phase_covers hu hu'
  let f (v : ℝ) := p + a * phase v
  have hf : Continuous f :=
    continuous_const.add (continuous_const.mul phase_continuous)
  have hnorm : Continuous (fun v : ℝ => normSq (f v - q)) :=
    continuous_normSq.comp (hf.sub continuous_const)
  have hopen : IsOpen {v : ℝ | normSq (f v - q) < s} :=
    isOpen_lt hnorm continuous_const
  have hnonempty : {v : ℝ | normSq (f v - q) < s}.Nonempty := by
    refine ⟨t, ?_⟩
    change normSq (p + a * phase t - q) < s
    rwa [ht, hpu]
  obtain ⟨b, hb⟩ := Rat.denseRange_cast.exists_mem_open hopen hnonempty
  refine ⟨f b, rationalComplex.add_mem qp (rationalComplex.mul_mem qa (phase_rat b)), ?_, hb⟩
  rw [show f b - p = a * phase b by dsimp [f]; ring, normSq_mul, phase_normSq, mul_one]

private theorem circle_pair (p q : ℂ) (r s : ℝ) (hp : RationalEntry p) (hq : RationalEntry q)
    (hr : ∃ x : ℚ, (x : ℝ) = r) (hs : ∃ x : ℚ, (x : ℝ) = s) (h : p ≠ q) :
    let d := normSq (q - p)
    let t := (d + r - s) / (2 * d)
    (∃ z : ℂ, RationalEntry z ∧ normSq (z - p) = r ∧ normSq (z - q) = s) ↔
    ∃ y : ℚ, (y : ℝ)^2 = r/d - t^2 := by
  let v := q - p
  let d := normSq v
  let t := (d + r - s) / (2 * d)
  change (∃ z : ℂ, RationalEntry z ∧ normSq (z - p) = r ∧ normSq (z - q) = s) ↔
    ∃ y : ℚ, (y : ℝ)^2 = r/d - t^2
  have hv : v ≠ 0 := sub_ne_zero.mpr h.symm
  have hd : d ≠ 0 := fun he => hv (normSq_eq_zero.mp he)
  have hleft (z : ℂ) : normSq ((z - p) / v) = normSq (z - p) / d := normSq_div _ _
  have hright (z : ℂ) : normSq ((z-p)/v-1) = normSq (z-q) / d := by
    rw [show (z-p)/v-1 = (z-q)/v by field_simp; dsimp [v]; ring, normSq_div]
  have hdiff (w : ℂ) : normSq w - normSq (w - 1) = 2*w.re - 1 := by
    simp only [normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero]
    ring
  constructor
  · rintro ⟨z, qz, hz, hz'⟩
    let w := (z - p) / v
    have hl : normSq w = r / d := (hleft z).trans (by rw [hz])
    have hr' : normSq (w-1) = s / d := (hright z).trans (by rw [hz'])
    have hw := hdiff w
    rw [hl, hr'] at hw
    have hreal : w.re = t := by
      dsimp [t]
      field_simp
      field_simp at hw
      linarith
    have qr : RationalEntry w := rationalComplex.div_mem (rationalComplex.sub_mem qz hp)
      (rationalComplex.sub_mem hq hp)
    obtain ⟨_, y, _, hy⟩ := qr
    refine ⟨y, ?_⟩
    rw [hy]
    rw [normSq_apply, hreal] at hl
    nlinarith only [hl]
  · rintro ⟨y, hy⟩
    obtain ⟨rQ, hrQ⟩ := hr
    obtain ⟨sQ, hsQ⟩ := hs
    have qv : RationalEntry v := rationalComplex.sub_mem hq hp
    obtain ⟨xQ, yQ, hxQ, hyQ⟩ := qv
    let dQ := xQ*xQ+yQ*yQ
    have hdQ : (dQ : ℝ) = d := by simp [dQ, d, normSq_apply, hxQ, hyQ]
    let tQ := (dQ + rQ - sQ) / (2*dQ)
    have htQ : (tQ : ℝ) = t := by simp [tQ, t, hdQ, hrQ, hsQ]
    let w : ℂ := ⟨t, y⟩
    let z := p + v*w
    have hwl : normSq w = r/d := by
      change t*t + (y : ℝ)*(y : ℝ) = r/d
      nlinarith only [hy]
    have hwr : normSq (w-1) = s/d := by
      have hh := hdiff w
      rw [hwl] at hh
      change r/d - normSq (w-1) = 2*t-1 at hh
      dsimp [t] at hh
      field_simp at hh ⊢
      linarith
    have qw : RationalEntry w := ⟨tQ, y, htQ, rfl⟩
    refine ⟨z, rationalComplex.add_mem hp
      (rationalComplex.mul_mem (rationalComplex.sub_mem hq hp) qw), ?_, ?_⟩
    · rw [show z-p = v*w by dsimp [z]; ring, normSq_mul, hwl]
      exact mul_div_cancel₀ _ hd
    · have hw : (z-p)/v = w := by dsimp [z]; field_simp; ring
      have hz := hright z
      rw [hw, hwr] at hz
      field_simp at hz
      exact hz.symm

/-- Arithmetic alternatives for a rational point on the boundary of a two-disk intersection. -/
def RationalBoundaryCriterion (p q : ℂ) (r s : ℝ) : Prop :=
  ((∃ z : ℂ, normSq (z - p) = r ∧ normSq (z - q) < s) ∧
    ∃ a : ℂ, RationalEntry a ∧ normSq a = r) ∨
  ((∃ z : ℂ, normSq (z - q) = s ∧ normSq (z - p) < r) ∧
    ∃ a : ℂ, RationalEntry a ∧ normSq a = s) ∨
  (p = q ∧ r = s ∧ ∃ a : ℂ, RationalEntry a ∧ normSq a = r) ∨
  (p ≠ q ∧
    let d := normSq (q - p)
    let t := (d + r - s) / (2 * d)
    ∃ y : ℚ, (y : ℝ)^2 = r / d - t^2)

private theorem rational_boundary_iff (p q : ℂ) (r s : ℝ)
    (hp : RationalEntry p) (hq : RationalEntry q) (hr : RationalReal r) (hs : RationalReal s) :
    (∃ z : ℂ, RationalEntry z ∧ normSq (z - p) ≤ r ∧ normSq (z - q) ≤ s ∧
      (normSq (z - p) = r ∨ normSq (z - q) = s)) ↔ RationalBoundaryCriterion p q r s := by
  constructor
  · rintro ⟨z, qz, hl, hh, hboundary⟩
    have qzp := rationalComplex.sub_mem qz hp
    have qzq := rationalComplex.sub_mem qz hq
    have both (he₁ : normSq (z - p) = r) (he₂ : normSq (z - q) = s) :
        RationalBoundaryCriterion p q r s := by
      by_cases hc : p = q
      · have he : r = s := he₁.symm.trans (by simpa [hc] using he₂)
        exact Or.inr (Or.inr (Or.inl ⟨hc, he, z - p, qzp, he₁⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨hc, (circle_pair p q r s hp hq hr hs hc).mp ⟨z, qz, he₁, he₂⟩⟩))
    rcases hboundary with he | he
    · rcases hh.lt_or_eq with hh | hh
      · exact Or.inl ⟨⟨z, he, hh⟩, z - p, qzp, he⟩
      · exact both he hh
    · rcases hl.lt_or_eq with hl | hl
      · exact Or.inr (Or.inl ⟨⟨z, he, hl⟩, z - q, qzq, he⟩)
      · exact both hl he
  · rintro (⟨⟨z, hz, hi⟩, a, qa, ha⟩ | ⟨⟨z, hz, hi⟩, a, qa, ha⟩ |
      ⟨he, hrs, a, qa, ha⟩ | ⟨hc, hsq⟩)
    · obtain ⟨x, qx, hx, hix⟩ := rational_circle_point p q a z s hp qa (hz.trans ha.symm) hi
      rw [ha] at hx
      exact ⟨x, qx, hx.le, hix.le, Or.inl hx⟩
    · obtain ⟨x, qx, hx, hix⟩ := rational_circle_point q p a z r hq qa (hz.trans ha.symm) hi
      rw [ha] at hx
      exact ⟨x, qx, hix.le, hx.le, Or.inr hx⟩
    · have hx : normSq (p + a - p) = r := by simpa using ha
      exact ⟨p+a, rationalComplex.add_mem hp qa, hx.le, by simpa [← he, ← hrs] using hx.le,
        Or.inl hx⟩
    · obtain ⟨z, qz, hl, hh⟩ := (circle_pair p q r s hp hq hr hs hc).mpr hsq
      exact ⟨z, qz, hl.le, hh.le, Or.inl hl⟩

/-- At positive middle occupation, the arithmetic criterion decides whether the compatible
rational edges have a rational rank-at-most-three extension with a boundary coupling. -/
theorem rational_rank_three_boundary_iff (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ)
    (hb : 0 < b) (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (he : CoherentExtendible b L R u v w) :
    let A := edgeDisk b L u v w
    let B := edgeDisk b R u w v
    (∃ (z : ℂ) (ρ : Matrix Word Word ℂ), ρ.PosSemidef ∧
      MatchesCoherentData b L R u v w z ρ ∧ ρ.rank ≤ 3 ∧
      (∀ i j, RationalEntry (ρ i j)) ∧
      (normSq (z - A.1) = A.2 ∨ normSq (z - B.1) = B.2)) ↔
      RationalBoundaryCriterion A.1 B.1 A.2 B.2 := by
  let z₀ := selectedCoupling b L R u v w
  obtain ⟨_, ht, hr, _, hleft, hright⟩ := (extendible_iff_selected b L R u v w).mp he
  have qb : RationalReal b := rreal (z := (b : ℂ)) (rational_pivot_of_trace ht qL)
  have hc : (correction b (middleRow u v w z₀)).PosSemidef := by
    unfold correction
    exact (Matrix.posSemidef_vecMulVec_star_self _).smul (inv_nonneg.mpr hb.le)
  have hL : L.IsHermitian := by
    simpa [z₀] using (hleft.add (partialTraceRight_posSemidef hc)).isHermitian
  have hR : R.IsHermitian := by
    simpa [z₀] using (hright.add (partialTraceLeft_posSemidef hc)).isHermitian
  let A := edgeDisk b L u v w
  let B := edgeDisk b R u w v
  obtain ⟨qA, qr⟩ := edgeDiskRational b L u v w qb qL qu qv qw
  obtain ⟨qB, qs⟩ := edgeDiskRational b R u w v qb qR qu qw qv
  have criterion := rational_boundary_iff A.1 B.1 A.2 B.2 qA qB qr qs
  constructor
  · rintro ⟨z, ρ, hp, hm, _, qρ, hboundary⟩
    have qz : RationalEntry z := by
      rw [← hm.2.2.2]
      exact qρ (.inl 0) (.inr true)
    obtain ⟨T, _, hT, hTL, hTR⟩ := extension_blocks hp hm
    have hX := partialTraceRight_posSemidef hT
    have hY := partialTraceLeft_posSemidef hT
    rw [partialTraceRight_sub, hTL] at hX
    rw [partialTraceLeft_sub, hTR, swapped_trace] at hY
    exact criterion.mp ⟨z, qz, (edgeDisk_spec b L u v w z hb hL).mp hX,
      (edgeDisk_spec b R u w v z hb hR).mp hY, hboundary⟩
  · intro h
    obtain ⟨z, qz, hx, hx', hboundary⟩ := criterion.mpr h
    have hX := (edgeDisk_spec b L u v w z hb hL).mpr hx
    have hY := (edgeDisk_spec b R u w v z hb hR).mpr hx'
    rw [← swapped_trace] at hY
    have hd : (L - partialTraceRight (correction b (middleRow u v w z))).det = 0 ∨
        (R - partialTraceLeft (correction b (middleRow u v w z))).det = 0 := by
      rw [swapped_trace]
      exact hboundary.imp (edge_singular_at_boundary b L u v w z hb hL)
        (edge_singular_at_boundary b R u w v z hb hR)
    obtain ⟨ρ, hp, hm, hRank, qρ⟩ := boundary_state b L R u v w z hb ht hr
      rationalComplex (fun _ h => h) qL qR qu qv qw qz
      (rationalConjugate ⟨z, qz⟩).property hX hY hd
    exact ⟨z, ρ, hp, hm, hRank, qρ, hboundary⟩

end D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary
