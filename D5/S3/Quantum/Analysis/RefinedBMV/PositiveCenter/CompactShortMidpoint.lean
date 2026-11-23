/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortMidpoint
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The joint term of the actual logarithmic kernel as a finite tilted average. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortEvenTails
import Batteries.Tactic.OpenPrivate

/-! The midpoint form of the compact short-gap joint contribution. -/

namespace RefinedBMV.PositiveCenter

open Filter
open scoped Topology

noncomputable section

open private centeredExponent from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenter
open private compositionMoment_marginal_smooth reflectedHalfLogSlope_nonneg from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization
open private short_midpoint_pair from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortEvenTails

private abbrev ShortGap := ℕ × ℕ × ℕ

/-- The uniform average over the last two centered gaps of a composition. -/
def shortJointAverage (p : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ((DimThree.gaps p).map fun g ↦
    f (centeredExponent p g.2.1) (centeredExponent p g.2.2)).sum /
      ((DimThree.gaps p).length : ℝ)

private theorem shortJointAverage_add (p : ℕ) (f g : ℝ → ℝ → ℝ) :
    shortJointAverage p (fun x y ↦ f x y + g x y) =
      shortJointAverage p f + shortJointAverage p g := by
  simp only [shortJointAverage, List.sum_map_add, add_div]

private theorem shortJointAverage_mul (p : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    shortJointAverage p (fun x y ↦ c * f x y) = c * shortJointAverage p f := by
  simp only [shortJointAverage, List.sum_map_mul_left, mul_div_assoc]

private theorem shortJointAverage_le (p : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ k ∈ DimThree.gaps p, f (centeredExponent p k.2.1) (centeredExponent p k.2.2) ≤
      g (centeredExponent p k.2.1) (centeredExponent p k.2.2)) :
    shortJointAverage p f ≤ shortJointAverage p g := by
  unfold shortJointAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  let F (k : ShortGap) := f (centeredExponent p k.2.1) (centeredExponent p k.2.2)
  let G (k : ShortGap) := g (centeredExponent p k.2.1) (centeredExponent p k.2.2)
  change ((DimThree.gaps p).map F).sum ≤ ((DimThree.gaps p).map G).sum
  have hsum (l : List ShortGap) (hl : ∀ k ∈ l, F k ≤ G k) :
      (l.map F).sum ≤ (l.map G).sum := by
    induction l with
    | nil => simp
    | cons k l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hl k (by simp)) (ih fun x hx ↦ hl x (by simp [hx]))
  exact hsum (DimThree.gaps p) h

private theorem shortJointAverage_conditioned (p : ℕ) (f : ℝ → ℝ → ℝ) :
    shortJointAverage p f =
      (∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p + 1 - i),
        f (centeredExponent p j) (centeredExponent p (p - i - j))) /
      ((DimThree.gaps p).length : ℝ) := by
  simp only [shortJointAverage, List.map_map, DimThree.gaps, List.flatMap_def, List.map_flatten,
    List.sum_flatten, Function.comp_def, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

private theorem shortJointAverage_swap (p : ℕ) (f : ℝ → ℝ → ℝ) :
    shortJointAverage p (fun x y ↦ f y x) = shortJointAverage p f := by
  simp only [shortJointAverage_conditioned]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  let n := p + 1 - i
  have hi' := Finset.mem_range.mp hi
  have hn : n - 1 = p - i := by dsimp [n]; omega
  let F j := f (centeredExponent p j) (centeredExponent p (p - i - j))
  change (∑ j ∈ Finset.range n, f (centeredExponent p (p - i - j)) (centeredExponent p j)) =
    ∑ j ∈ Finset.range n, F j
  rw [← Finset.sum_range_reflect F n]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  dsimp only [F]
  rw [hn, show p - i - (p - i - j) = j by omega]

/-- The midpoint pairing retains the signed odd term of the joint average. -/
theorem shortJointAverage_eq_midpoint (p : ℕ) (u v a b : ℝ) :
    let w := (u + v) / 2
    let r := (v - u) / 2
    shortJointAverage p (fun x y ↦ (x - a) * (y - b) * Real.exp (x * u + y * v)) =
      shortJointAverage p (fun x y ↦ Real.exp (w * (x + y)) *
        ((x * y - (a + b) * (x + y) / 2 + a*b) * Real.cosh (r * (y - x)) +
          (b - a) / 2 * (y - x) * Real.sinh (r * (y - x)))) := by
  intro w r
  let F (x y : ℝ) := (x - a) * (y - b) * Real.exp (x * u + y * v)
  change shortJointAverage p F = _
  have hpair (x y : ℝ) : (1 / 2) * (F x y + F y x) =
      Real.exp (w * (x + y)) *
        ((x * y - (a + b) * (x + y) / 2 + a*b) * Real.cosh (r * (y - x)) +
          (b - a) / 2 * (y - x) * Real.sinh (r * (y - x))) := by
    have hx : x * u + y * v = w * (x + y) + r * (y - x) := by dsimp [w, r]; ring
    have hy : y * u + x * v = w * (x + y) + -(r * (y - x)) := by dsimp [w, r]; ring
    dsimp only [F]
    simp only [hx, hy, Real.exp_add]
    linear_combination Real.exp (w * (x + y)) *
      (short_midpoint_pair (X := x) (Y := y) (a := a) (b := b) (r := r))
  simp_rw [← hpair]
  rw [shortJointAverage_mul, shortJointAverage_add, shortJointAverage_swap]
  ring

/-- A power of the sum coordinate in a tilted even separation moment. -/
def shortMidpointMonomial (w : ℝ) (j k : ℕ) (x y : ℝ) : ℝ :=
  Real.exp (w * (x + y)) * (x + y) ^ k * (y - x) ^ (2 * j)

/-- The scalar moments used by the finite midpoint certificate. -/
def shortMidpointMoment (p j k : ℕ) (w : ℝ) : ℝ :=
  shortJointAverage p (shortMidpointMonomial w j k)

/-- Conditioning reduces the tilted even moments to symmetric step-two grid sums. -/
theorem shortMidpointMoment_conditioned {p : ℕ} (hp : 0 < p) (j k : ℕ) (w : ℝ) :
    let h := 3 / (p : ℝ)
    shortMidpointMoment p j k w =
      (∑ i ∈ Finset.range (p + 1), (Real.exp (-(h * i - 1) * w) * (-(h * i - 1)) ^ k) *
        (h ^ (2 * j) * shortGridEvenSum (p + 1 - i) j)) /
        ((DimThree.gaps p).length : ℝ) := by
  intro h
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have htotal : h * (p : ℝ) = 3 := by dsimp only [h]; exact div_mul_cancel₀ _ hpR
  have hexp (i : ℕ) : centeredExponent p i = h * i - 1 := by
    unfold centeredExponent
    dsimp only [h]
    ring
  rw [shortMidpointMoment, shortJointAverage_conditioned]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  let n := p + 1 - i
  have hi' := Finset.mem_range.mp hi
  have hn : (n : ℝ) = (p : ℝ) + 1 - i := by
    dsimp only [n]
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  change (∑ k ∈ Finset.range n, _) =
    (Real.exp (-(h * i - 1) * w) * (-(h * i - 1)) ^ k) *
      (h ^ (2 * j) * shortGridEvenSum n j)
  rw [shortGridEvenSum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hk' := Finset.mem_range.mp hm
  have hcast : (↑(p - i - m) : ℝ) = (p : ℝ) - i - m := by
    rw [Nat.cast_sub (by dsimp [n] at hk'; omega), Nat.cast_sub (by omega)]
  have hsum : centeredExponent p m + centeredExponent p (p - i - m) =
      -(h * i - 1) := by
    rw [hexp, hexp, hcast]
    linear_combination htotal
  have hdiff : centeredExponent p (p - i - m) - centeredExponent p m =
      h * ((n : ℝ) - 1 - 2 * m) := by
    rw [hexp, hexp, hcast, hn]
    ring
  rw [shortMidpointMonomial, hsum, hdiff, mul_pow, mul_comm w]

private theorem hasDerivAt_shortJointAverage (p : ℕ) {t : ℝ}
    {f : ℝ → ℝ → ℝ → ℝ} {df : ℝ → ℝ → ℝ}
    (h : ∀ x y, HasDerivAt (f x y) (df x y) t) :
    HasDerivAt (fun z ↦ shortJointAverage p (fun x y ↦ f x y z)) (shortJointAverage p df) t := by
  let x (g : ShortGap) := centeredExponent p g.2.1
  let y (g : ShortGap) := centeredExponent p g.2.2
  have hsum (l : List ShortGap) :
      HasDerivAt (fun z ↦ (l.map fun g ↦ f (x g) (y g) z).sum)
        ((l.map fun g ↦ df (x g) (y g)).sum) t := by
    induction l with
    | nil => simpa only [List.map_nil, List.sum_nil] using hasDerivAt_const t (0 : ℝ)
    | cons g l ih =>
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using (h (x g) (y g)).add ih
  exact (hsum (DimThree.gaps p)).div_const _

private def shortMomentJet (p : ℕ) (u v : ℝ) : MixedJet ℝ :=
  let E (x y : ℝ) := Real.exp (x * u + y * v)
  ⟨shortJointAverage p E - 1,
    shortJointAverage p (fun x y ↦ x * E x y),
    shortJointAverage p (fun x y ↦ y * E x y),
    shortJointAverage p (fun x y ↦ (x * y) * E x y)⟩

private theorem shortMomentJet_isAt (p : ℕ) (u v : ℝ) :
    MixedJet.IsAt (shortMomentJet p) u v := by
  refine ⟨Eventually.of_forall fun t ↦ ?_, ?_, ?_⟩
  · refine (hasDerivAt_shortJointAverage p
      (f := fun x y z ↦ Real.exp (x * z + y * t))
      (df := fun x y ↦ x * Real.exp (x * u + y * t)) ?_).sub_const 1
    intro x y
    simpa [mul_comm] using (((hasDerivAt_id' u).const_mul x).add_const (y * t)).exp
  · refine (hasDerivAt_shortJointAverage p
      (f := fun x y z ↦ Real.exp (x * u + y * z))
      (df := fun x y ↦ y * Real.exp (x * u + y * v)) ?_).sub_const 1
    intro x y
    simpa [mul_comm, add_comm] using (((hasDerivAt_id' v).const_mul y).const_add (x * u)).exp
  · refine hasDerivAt_shortJointAverage p
      (f := fun x y z ↦ x * Real.exp (x * u + y * z))
      (df := fun x y ↦ x * y * Real.exp (x * u + y * v)) ?_
    intro x y
    have h := ((((hasDerivAt_id' v).const_mul y).const_add (x * u)).exp).const_mul x
    refine h.congr_deriv ?_
    simp only [mul_one, id_eq]
    ring

/-- The finite average with the two normalization slopes gives the joint mixed term exactly. -/
theorem logKernel_mixed_eq_shortJointAverage {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let R := compositionMoment p 0
    let a := reflectedHalfLogSlope R u
    let b := reflectedHalfLogSlope R v
    Real.sqrt (R (-u) * R (-v)) * deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v =
      shortJointAverage p (fun x y ↦ (x - a) * (y - b) * Real.exp (x * u + y * v)) -
        a * b - compactMixedQ p u v := by
  intro R a b
  have h := mixed_normalized_marginal_sub (compositionMoment_marginal_smooth p)
    (fun _ ht ↦ compositionMoment_marginal_pos hp ht) hu huv (shortMomentJet_isAt p u v)
  change Real.sqrt (R (-u) * R (-v)) * deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v = _ at h
  rw [h]
  dsimp only [shortMomentJet, compactMixedQ]
  have hweight (x y : ℝ) :
      (x - a) * (y - b) * Real.exp (x * u + y * v) =
        (x * y) * Real.exp (x * u + y * v) +
          (-b) * (x * Real.exp (x * u + y * v)) +
          (-a) * (y * Real.exp (x * u + y * v)) +
          (a * b) * Real.exp (x * u + y * v) := by ring
  simp_rw [hweight, shortJointAverage_add, shortJointAverage_mul]
  ring

/-- The finite fourth-order comparison bounds the mixed derivative of the original kernel. -/
theorem logKernel_mixed_le_shortMidpointMajorant {p : ℕ} (hp : 0 < p) {u v radius : ℝ}
    (hu : 0 < u) (huv : u < v) (hr : 3 * ((v - u) / 2) ≤ radius)
    (hR : radius ^ 2 / 42 < 1) :
    let R := compositionMoment p 0
    let a := reflectedHalfLogSlope R u
    let b := reflectedHalfLogSlope R v
    Real.sqrt (R (-u) * R (-v)) * deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v ≤
      shortJointAverage p (fun x y ↦ Real.exp (((u + v) / 2) * (x + y)) *
        shortPairMajorant ((v - u) / 2) radius a b x y) - a*b - compactMixedQ p u v := by
  intro R a b
  rw [logKernel_mixed_eq_shortJointAverage hp hu huv, shortJointAverage_eq_midpoint]
  apply sub_le_sub_right
  apply sub_le_sub_right
  apply shortJointAverage_le
  intro g hg
  let x := centeredExponent p g.2.1
  let y := centeredExponent p g.2.2
  have htotalNat := (DimThree.mem_gaps_iff_total p g).mp hg
  let h : ℝ := 3 / (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have htotal : h * p = 3 := by dsimp only [h]; exact div_mul_cancel₀ _ hpR.ne'
  have hx' : x = h * g.2.1 - 1 := by unfold x centeredExponent h; ring
  have hy' : y = h * g.2.2 - 1 := by unfold y centeredExponent h; ring
  have hx : -1 ≤ x := by
    rw [hx']
    linarith only [mul_nonneg hh (Nat.cast_nonneg g.2.1)]
  have hy : -1 ≤ y := by
    rw [hy']
    linarith only [mul_nonneg hh (Nat.cast_nonneg g.2.2)]
  have hsum : x + y ≤ 1 := by
    have hc : (g.2.1 : ℝ) + g.2.2 ≤ p := by
      exact_mod_cast (show g.2.1 + g.2.2 ≤ p by omega)
    rw [hx', hy']
    linarith only [mul_le_mul_of_nonneg_left hc hh, htotal]
  have hw : |y - x| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hhalf : 0 ≤ (v-u)/2 := div_nonneg (sub_nonneg.mpr huv.le) (by norm_num)
  have hz : ((v-u)/2)*|y-x| ≤ radius :=
    (mul_le_mul_of_nonneg_left hw hhalf).trans (by linarith only [hr])
  have hpair := short_midpoint_pair_le_fourth hhalf hz hR (reflectedHalfLogSlope_nonneg hp hu)
    (reflectedHalfLogSlope_nonneg hp (hu.trans huv)) (by linarith) hsum
  exact mul_le_mul_of_nonneg_left hpair (Real.exp_pos _).le

private def shortWeightedMoment (p j : ℕ) (w a b : ℝ) : ℝ :=
  shortMidpointMoment p j 2 w / 4 - shortMidpointMoment p (j + 1) 0 w / 4 -
    (a + b) / 2 * shortMidpointMoment p j 1 w + a * b * shortMidpointMoment p j 0 w

private theorem shortWeightedMoment_eq (p j : ℕ) (w a b : ℝ) :
    shortWeightedMoment p j w a b =
      shortJointAverage p (fun x y ↦
        Real.exp (w * (x + y)) * ((x*y - (a+b)*(x+y)/2 + a*b) * (y-x)^(2*j))) := by
  have heq (x y : ℝ) :
      Real.exp (w * (x + y)) * ((x*y - (a+b)*(x+y)/2 + a*b) * (y-x)^(2*j)) =
      (1/4) * shortMidpointMonomial w j 2 x y + (-1/4) * shortMidpointMonomial w (j+1) 0 x y +
        (-(a+b)/2) * shortMidpointMonomial w j 1 x y +
        (a*b) * shortMidpointMonomial w j 0 x y := by
    simp only [shortMidpointMonomial, Nat.mul_add, Nat.mul_one, pow_add, pow_zero, pow_one]
    ring
  simp_rw [heq, shortJointAverage_add, shortJointAverage_mul]
  unfold shortWeightedMoment shortMidpointMoment
  ring

/-- The fourth-order majorant uses only the first four even separation moments and quadratic weights. -/
theorem shortJointMajorant_eq_moments (p : ℕ) (w r radius a b : ℝ) :
    let c := (b - a) / 2
    let B := fun j ↦ shortWeightedMoment p j w a b
    let A := fun j ↦ shortMidpointMoment p j 0 w
    let tail := (1 + a) * (1 + b) * (r ^ 6 / 720 / (1 - radius ^ 2 / 56)) +
      max 0 c * (r ^ 5 / 120 / (1 - radius ^ 2 / 42))
    shortJointAverage p (fun x y ↦ Real.exp (w * (x + y)) * shortPairMajorant r radius a b x y) =
      B 0 + (r^2/2) * B 1 + (r^4/24) * B 2 +
        (c*r) * A 1 + (c*(r^3/6)) * A 2 + tail * A 3 := by
  intro c B A tail
  let f (j : ℕ) (x y : ℝ) :=
    Real.exp (w * (x + y)) * ((x*y - (a+b)*(x+y)/2 + a*b) * (y-x)^(2*j))
  have hB (j : ℕ) : B j = shortJointAverage p (f j) := shortWeightedMoment_eq p j w a b
  have hA (j : ℕ) : A j = shortJointAverage p (shortMidpointMonomial w j 0) := rfl
  have hx (x y : ℝ) :
      Real.exp (w * (x + y)) * shortPairMajorant r radius a b x y =
      f 0 x y + (r^2/2) * f 1 x y + (r^4/24) * f 2 x y +
        (c*r) * shortMidpointMonomial w 1 0 x y +
        (c*(r^3/6)) * shortMidpointMonomial w 2 0 x y +
        tail * shortMidpointMonomial w 3 0 x y := by
    rw [shortPairMajorant_expanded]
    simp only [f, shortMidpointMonomial, pow_zero, mul_one]
    dsimp only [c, tail]
    ring
  simp_rw [hx, shortJointAverage_add, shortJointAverage_mul, hB, hA]

end

end RefinedBMV.PositiveCenter
