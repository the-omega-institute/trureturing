/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterWeightedTaylorReplay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Horner evaluation of the small-corner marginal jets and continued divided differences. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMarginalTaylor
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMomentPolynomial

/-! # Horner evaluation of the marginal Taylor jets -/

namespace RefinedBMV.PositiveCenter.SmallCorner

open Filter MeasureTheory Set
open scoped BigOperators Topology

set_option autoImplicit false

/-- Ascending coefficient evaluation for real jets and their interval enclosures. -/
def marginalHorner {R : Type*} (add mul : R → R → R) (zero t : R) : List R → R
  | [] => zero
  | c :: cs => add (mul (marginalHorner add mul zero t cs) t) c

structure MarginalHornerResult (R : Type*) where
  atV : R
  atD : R
  prime : R
  firstDifference : R
  secondDifference : R

/-- Evaluate the polynomial at (v,d), its derivative at (v), and the first
and repeated-node divided differences at (v,d). -/
def marginalDifferenceHorner {R : Type*} (add mul : R → R → R) (zero v d : R) :
    List R → MarginalHornerResult R
  | [] => ⟨zero, zero, zero, zero, zero⟩
  | c :: cs =>
    let rest := marginalDifferenceHorner add mul zero v d cs
    ⟨add (mul rest.atV v) c, add (mul rest.atD d) c,
      add (mul rest.prime v) rest.atV,
      add (mul rest.firstDifference v) rest.atD,
      add (mul rest.secondDifference v) rest.firstDifference⟩

noncomputable section

/-- The exact marginal coefficients in the order used by the Horner replay. -/
noncomputable def marginalTaylorMomentCoefficients (p : ℕ) : List ℝ :=
  List.ofFn (n := 23) fun k ↦
    momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (k.val + 2))

private theorem marginalHorner_ofFn (n : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    marginalHorner (· + ·) (· * ·) 0 t (List.ofFn (n := n) fun i ↦ c i) =
      ∑ i ∈ Finset.range n, c i * t ^ i := by
  induction n generalizing c with
  | zero => simp [marginalHorner]
  | succ n ih =>
    rw [List.ofFn_succ, marginalHorner, Finset.sum_range_succ']
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
    rw [ih (fun i ↦ c (i + 1)), Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ, mul_assoc]

private theorem marginalTaylorMoment_eq {p : ℕ} (hp : 0 < p) (k : ℕ) :
    momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (k + 2)) =
      jointTaylorMoment p k 0 / (((k.factorial : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  let x (j : ℕ) : ℝ := 3 * (j : ℝ) / (p : ℝ) - 1
  let norm : ℝ := ((DimThree.gaps p).length : ℝ) * (compositionMarginalVariance p / 2)
  have hcycle := ((DimThree.gaps_cycle_all p).map fun g ↦ x g.2.1 ^ (k + 2)).sum_eq
  simp only [List.map_map, Function.comp_def] at hcycle
  rw [normalized_moment_eval_marginal hp]
  change ((DimThree.gaps p).map fun g ↦ x g.2.2 ^ (k + 2)).sum /
      (norm * ((k + 2).factorial : ℝ)) =
      (((DimThree.gaps p).map fun g ↦ x g.2.1 ^ 2 *
        (x g.2.1 ^ k * x g.2.2 ^ 0)).sum / norm) /
        ((k.factorial : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2))
  rw [hcycle]
  simp only [pow_zero, mul_one, ← pow_add, Nat.add_comm 2 k, div_div]
  rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

/-- Real Horner evaluation of the marginal Taylor polynomial. -/
theorem marginalHorner_taylor {p : ℕ} (hp : 0 < p) (t : ℝ) :
    marginalHorner (· + ·) (· * ·) 0 t (marginalTaylorMomentCoefficients p) =
      marginalTaylorPolynomial p 0 t := by
  rw [marginalTaylorMomentCoefficients, marginalHorner_ofFn 23
    (fun k ↦ momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (k + 2)))]
  simp only [marginalTaylorPolynomial, Nat.sub_zero, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [marginalTaylorMoment_eq hp]
  ring

/-- Constant input in a real Horner evaluation. -/
def marginalScalarJet (c : ℝ) : MixedJet ℝ := ⟨c, 0, 0, 0⟩

/-- The jet of a linear function of the two original gap variables. -/
def marginalAffineInput (a b u v : ℝ) : MixedJet ℝ := ⟨a * u + b * v, a, b, 0⟩

private theorem scalar_isAt (c u v : ℝ) :
    MixedJet.IsAt (fun _ _ ↦ marginalScalarJet c) u v :=
  ⟨Eventually.of_forall (fun _ ↦ hasDerivAt_const u c),
    hasDerivAt_const v c, hasDerivAt_const v (0 : ℝ)⟩

private theorem affine_isAt (a b u v : ℝ) :
    MixedJet.IsAt (marginalAffineInput a b) u v := by
  refine ⟨Eventually.of_forall (fun y ↦ ?_), ?_, hasDerivAt_const v a⟩
  · simpa only [marginalAffineInput, mul_one] using
      ((hasDerivAt_id' u).const_mul a).add_const (b * y)
  · simpa only [marginalAffineInput, mul_one] using
      ((hasDerivAt_id' v).const_mul b).const_add (a * u)

private theorem jet_eq_of_value_eq {f g : ℝ → ℝ → MixedJet ℝ}
    (hf : ∀ u v, MixedJet.IsAt f u v) (hg : ∀ u v, MixedJet.IsAt g u v)
    (heq : ∀ u v, (f u v).value = (g u v).value) (u v : ℝ) :
    f u v = g u v := by
  have hdu (y : ℝ) : (f u y).du = (g u y).du := by
    have h₁ := (hf u y).1.self_of_nhds
    have h₂ := (hg u y).1.self_of_nhds
    rw [show (fun x ↦ (f x y).value) = fun x ↦ (g x y).value from funext (heq · y)] at h₁
    exact h₁.unique h₂
  have hdv : (f u v).dv = (g u v).dv := by
    have h₁ := (hf u v).2.1
    rw [show (fun y ↦ (f u y).value) = fun y ↦ (g u y).value from funext (heq u)] at h₁
    exact h₁.unique (hg u v).2.1
  have hduv : (f u v).duv = (g u v).duv := by
    have h₁ := (hf u v).2.2
    rw [show (fun y ↦ (f u y).du) = fun y ↦ (g u y).du from funext hdu] at h₁
    exact h₁.unique (hg u v).2.2
  have hv := heq u v
  have hu := hdu v
  rcases hF : f u v with ⟨fv, fu, fw, ft⟩
  rcases hG : g u v with ⟨gv, gu, gw, gt⟩
  congr 1
  · simpa only [hF, hG] using hv
  · simpa only [hF, hG] using hu
  · simpa only [hF, hG] using hdv
  · simpa only [hF, hG] using hduv

private theorem marginalHorner_jet_value (cs : List ℝ) (t : MixedJet ℝ) :
    (marginalHorner MixedJet.add MixedJet.mul (marginalScalarJet 0) t
      (cs.map marginalScalarJet)).value =
      marginalHorner (· + ·) (· * ·) 0 t.value cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change (marginalHorner MixedJet.add MixedJet.mul (marginalScalarJet 0) t
      (cs.map marginalScalarJet)).value * t.value + c = _
    rw [ih]
    rfl

private theorem marginalHorner_jet_isAt (cs : List ℝ) {t : ℝ → ℝ → MixedJet ℝ}
    (ht : ∀ u v, MixedJet.IsAt t u v) (u v : ℝ) :
    MixedJet.IsAt (fun x y ↦ marginalHorner MixedJet.add MixedJet.mul (marginalScalarJet 0)
      (t x y) (cs.map marginalScalarJet)) u v := by
  induction cs with
  | nil => exact scalar_isAt 0 u v
  | cons c cs ih => exact (ih.mul (ht u v)).add (scalar_isAt c u v)

/-- Horner replay computes the full mixed jet of the marginal Taylor polynomial
at any linear argument, including the two negative arguments. -/
theorem marginalHorner_affineTaylor {p : ℕ} (hp : 0 < p) (a b u v : ℝ) :
    marginalHorner MixedJet.add MixedJet.mul (marginalScalarJet 0)
      (marginalAffineInput a b u v) ((marginalTaylorMomentCoefficients p).map marginalScalarJet) =
    affineMarginalJet (marginalTaylorPolynomial p) 0 a b u v := by
  apply jet_eq_of_value_eq
    (f := fun x y ↦ marginalHorner MixedJet.add MixedJet.mul (marginalScalarJet 0)
      (marginalAffineInput a b x y) ((marginalTaylorMomentCoefficients p).map marginalScalarJet))
    (g := affineMarginalJet (marginalTaylorPolynomial p) 0 a b) (u := u) (v := v)
  · intro x y
    exact marginalHorner_jet_isAt _ (affine_isAt a b) x y
  · exact affineMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p) 0 a b
  · intro x y
    rw [marginalHorner_jet_value, marginalHorner_taylor hp]
    rfl

#print axioms marginalHorner_affineTaylor

private theorem marginalDifferenceHorner_equations (cs : List ℝ) (v d : ℝ) :
    let r := marginalDifferenceHorner (· + ·) (· * ·) 0 v d cs
    r.atV = marginalHorner (· + ·) (· * ·) 0 v cs ∧
    r.atD = marginalHorner (· + ·) (· * ·) 0 d cs ∧
    (v - d) * r.firstDifference = r.atV - r.atD ∧
    (v - d) * r.secondDifference = r.prime - r.firstDifference := by
  induction cs with
  | nil => simp [marginalDifferenceHorner, marginalHorner]
  | cons c cs ih =>
    obtain ⟨hv, hd, hfirst, hsecond⟩ := ih
    dsimp only [marginalDifferenceHorner, marginalHorner]
    exact ⟨by rw [hv], by rw [hd], by linear_combination v * hfirst,
      by linear_combination v * hsecond + hfirst⟩

private theorem marginalDifferenceHorner_hasDerivAt (cs : List ℝ) (v d : ℝ) :
    HasDerivAt (fun x ↦ marginalHorner (· + ·) (· * ·) 0 x cs)
      (marginalDifferenceHorner (· + ·) (· * ·) 0 v d cs).prime v := by
  induction cs with
  | nil => exact hasDerivAt_const v (0 : ℝ)
  | cons c cs ih =>
    have h := (ih.mul (hasDerivAt_id' v)).add_const c
    simpa only [marginalHorner, marginalDifferenceHorner, Pi.mul_apply, id_eq, mul_one,
      (marginalDifferenceHorner_equations cs v d).1] using h

private def realDifferenceReplay (cs : List ℝ) (u v : ℝ) : MarginalHornerResult (MixedJet ℝ) :=
  marginalDifferenceHorner MixedJet.add MixedJet.mul (marginalScalarJet 0)
    (marginalAffineInput 0 1 u v) (marginalAffineInput (-1) 1 u v) (cs.map marginalScalarJet)

private theorem realDifferenceReplay_isAt (cs : List ℝ) (u v : ℝ) :
    MixedJet.IsAt (fun x y ↦ (realDifferenceReplay cs x y).atV) u v ∧
    MixedJet.IsAt (fun x y ↦ (realDifferenceReplay cs x y).atD) u v ∧
    MixedJet.IsAt (fun x y ↦ (realDifferenceReplay cs x y).prime) u v ∧
    MixedJet.IsAt (fun x y ↦ (realDifferenceReplay cs x y).firstDifference) u v ∧
    MixedJet.IsAt (fun x y ↦ (realDifferenceReplay cs x y).secondDifference) u v := by
  induction cs with
  | nil =>
    have hz := scalar_isAt 0 u v
    exact ⟨hz, hz, hz, hz, hz⟩
  | cons c cs ih =>
    obtain ⟨hv, hd, hprime, hfirst, hsecond⟩ := ih
    have hV := affine_isAt 0 1 u v
    have hD := affine_isAt (-1) 1 u v
    have hc := scalar_isAt c u v
    exact ⟨(hv.mul hV).add hc, (hd.mul hD).add hc, (hprime.mul hV).add hv,
      (hfirst.mul hV).add hd, (hsecond.mul hV).add hfirst⟩

private theorem realDifferenceReplay_values (cs : List ℝ) (u v : ℝ) :
    let j := realDifferenceReplay cs u v
    let r := marginalDifferenceHorner (· + ·) (· * ·) 0 v (v - u) cs
    j.atV.value = r.atV ∧ j.atD.value = r.atD ∧ j.prime.value = r.prime ∧
    j.firstDifference.value = r.firstDifference ∧
    j.secondDifference.value = r.secondDifference := by
  induction cs with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons c cs ih =>
    obtain ⟨hv, hd, hprime, hfirst, hsecond⟩ := ih
    simp only [realDifferenceReplay, List.map_cons, marginalDifferenceHorner, MixedJet.add,
      MixedJet.mul, marginalScalarJet]
    change (realDifferenceReplay cs u v).atV.value * (0*u + 1*v) + c = _ ∧
      (realDifferenceReplay cs u v).atD.value * (-1*u + 1*v) + c = _ ∧
      (realDifferenceReplay cs u v).prime.value * (0*u + 1*v) +
        (realDifferenceReplay cs u v).atV.value = _ ∧
      (realDifferenceReplay cs u v).firstDifference.value * (0*u + 1*v) +
        (realDifferenceReplay cs u v).atD.value = _ ∧
      (realDifferenceReplay cs u v).secondDifference.value * (0*u + 1*v) +
        (realDifferenceReplay cs u v).firstDifference.value = _
    simp only [hv, hd, hprime, hfirst, hsecond, zero_mul, one_mul, zero_add,
      neg_one_mul, ← sub_eq_neg_add, and_self]

private theorem taylorDifference_values_ne_zero {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : u ≠ 0) :
    let j := realDifferenceReplay (marginalTaylorMomentCoefficients p) u v
    j.firstDifference.value =
      (weightedMarginalJet (marginalTaylorPolynomial p) (fun _ ↦ 1) 1 u v).value ∧
    j.secondDifference.value =
      (weightedMarginalJet (marginalTaylorPolynomial p) (fun t ↦ 1 - t) 2 u v).value := by
  let cs := marginalTaylorMomentCoefficients p
  let q := marginalTaylorPolynomial p
  let d := v - u
  let r := marginalDifferenceHorner (· + ·) (· * ·) 0 v d cs
  have hv : r.atV = q 0 v :=
    (marginalDifferenceHorner_equations cs v d).1.trans (marginalHorner_taylor hp v)
  have hd : r.atD = q 0 d :=
    (marginalDifferenceHorner_equations cs v d).2.1.trans (marginalHorner_taylor hp d)
  have hprime : r.prime = q 1 v := by
    have h := marginalDifferenceHorner_hasDerivAt cs v d
    change HasDerivAt _ r.prime v at h
    simp_rw [show ∀ t, marginalHorner (· + ·) (· * ·) 0 t cs = q 0 t from
      marginalHorner_taylor hp] at h
    exact h.unique (hasDerivAt_marginalTaylorPolynomial p 0 v)
  have h₁ : IntervalIntegrable (fun t ↦ q 1 (v - t * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold q marginalTaylorPolynomial
    fun_prop
  have h₂ : IntervalIntegrable (fun t ↦ (1 - t) * q 2 (v - t * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold q marginalTaylorPolynomial
    fun_prop
  obtain ⟨hfirst, hsecond⟩ := divided_differences_eq_integral (g := q 0) (g₁ := q 1) (g₂ := q 2)
    hu (fun t _ ↦ hasDerivAt_marginalTaylorPolynomial p 0 _)
    (fun t _ ↦ hasDerivAt_marginalTaylorPolynomial p 1 _) h₁ h₂
  have hdiff : r.firstDifference = (q 0 v - q 0 d) / u := by
    apply (eq_div_iff hu).2
    have h := (marginalDifferenceHorner_equations cs v d).2.2.1
    rwa [show v - d = u by dsimp [d]; ring, mul_comm u, hv, hd] at h
  have hddiff : r.secondDifference = (q 1 v - r.firstDifference) / u := by
    apply (eq_div_iff hu).2
    have h := (marginalDifferenceHorner_equations cs v d).2.2.2
    rwa [show v - d = u by dsimp [d]; ring, mul_comm u, hprime] at h
  have hj := realDifferenceReplay_values cs u v
  change _ = _ ∧ _ = _
  rw [hj.2.2.2.1, hj.2.2.2.2, hddiff, hdiff]
  simpa only [weightedMarginalJet, weightedMarginalIntegral, pow_zero, mul_one, one_mul,
    Nat.add_zero] using And.intro hfirst hsecond

private theorem taylorDifference_values {p : ℕ} (hp : 0 < p) (u v : ℝ) :
    let j := realDifferenceReplay (marginalTaylorMomentCoefficients p) u v
    j.firstDifference.value =
      (weightedMarginalJet (marginalTaylorPolynomial p) (fun _ ↦ 1) 1 u v).value ∧
    j.secondDifference.value =
      (weightedMarginalJet (marginalTaylorPolynomial p) (fun t ↦ 1 - t) 2 u v).value := by
  let cs := marginalTaylorMomentCoefficients p
  let f₁ (x : ℝ) := (realDifferenceReplay cs x v).firstDifference.value
  let f₂ (x : ℝ) := (realDifferenceReplay cs x v).secondDifference.value
  let g₁ (x : ℝ) := (weightedMarginalJet (marginalTaylorPolynomial p) (fun _ ↦ 1) 1 x v).value
  let g₂ (x : ℝ) := (weightedMarginalJet (marginalTaylorPolynomial p) (fun t ↦ 1 - t) 2 x v).value
  have hf₁ : Continuous f₁ := continuous_iff_continuousAt.mpr fun x ↦
    (realDifferenceReplay_isAt cs x v).2.2.2.1.1.self_of_nhds.continuousAt
  have hf₂ : Continuous f₂ := continuous_iff_continuousAt.mpr fun x ↦
    (realDifferenceReplay_isAt cs x v).2.2.2.2.1.self_of_nhds.continuousAt
  have hg₁ : Continuous g₁ := continuous_iff_continuousAt.mpr fun x ↦
    (weightedMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p)
      (w := fun _ ↦ 1) continuous_const 1 x v).1.self_of_nhds.continuousAt
  have hg₂ : Continuous g₂ := continuous_iff_continuousAt.mpr fun x ↦
    (weightedMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p)
      (continuous_const.sub continuous_id) 2 x v).1.self_of_nhds.continuousAt
  have h₁ : EqOn f₁ g₁ ({0} : Set ℝ)ᶜ := fun x hx ↦ (taylorDifference_values_ne_zero hp hx).1
  have h₂ : EqOn f₂ g₂ ({0} : Set ℝ)ᶜ := fun x hx ↦ (taylorDifference_values_ne_zero hp hx).2
  have hu : u ∈ closure ({0} : Set ℝ)ᶜ := by
    rw [(dense_compl_singleton (0 : ℝ)).closure_eq]
    exact mem_univ u
  exact ⟨h₁.closure hf₁ hg₁ hu, h₂.closure hf₂ hg₂ hu⟩

/-- Horner evaluation yields the two marginal jets on the segment, the
derivative jet at its right endpoint, and both continued divided differences. -/
theorem marginalDifferenceHorner_taylor {p : ℕ} (hp : 0 < p) (u v : ℝ) :
    let j := marginalDifferenceHorner MixedJet.add MixedJet.mul (marginalScalarJet 0)
      (marginalAffineInput 0 1 u v) (marginalAffineInput (-1) 1 u v)
      ((marginalTaylorMomentCoefficients p).map marginalScalarJet)
    j.atV = affineMarginalJet (marginalTaylorPolynomial p) 0 0 1 u v ∧
    j.atD = affineMarginalJet (marginalTaylorPolynomial p) 0 (-1) 1 u v ∧
    j.prime = affineMarginalJet (marginalTaylorPolynomial p) 1 0 1 u v ∧
    j.firstDifference = weightedMarginalJet (marginalTaylorPolynomial p) (fun _ ↦ 1) 1 u v ∧
    j.secondDifference =
      weightedMarginalJet (marginalTaylorPolynomial p) (fun t ↦ 1 - t) 2 u v := by
  let cs := marginalTaylorMomentCoefficients p
  have hv : (realDifferenceReplay cs u v).atV =
      affineMarginalJet (marginalTaylorPolynomial p) 0 0 1 u v := by
    apply jet_eq_of_value_eq (fun x y ↦ (realDifferenceReplay_isAt cs x y).1)
      (affineMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p) 0 0 1)
    intro x y
    rw [(realDifferenceReplay_values cs x y).1, (marginalDifferenceHorner_equations cs y (y-x)).1,
      marginalHorner_taylor hp]
    simp [affineMarginalJet]
  have hd : (realDifferenceReplay cs u v).atD =
      affineMarginalJet (marginalTaylorPolynomial p) 0 (-1) 1 u v := by
    apply jet_eq_of_value_eq (fun x y ↦ (realDifferenceReplay_isAt cs x y).2.1)
      (affineMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p) 0 (-1) 1)
    intro x y
    rw [(realDifferenceReplay_values cs x y).2.1,
      (marginalDifferenceHorner_equations cs y (y-x)).2.1, marginalHorner_taylor hp]
    simp [affineMarginalJet, sub_eq_neg_add]
  have hprime : (realDifferenceReplay cs u v).prime =
      affineMarginalJet (marginalTaylorPolynomial p) 1 0 1 u v := by
    apply jet_eq_of_value_eq (fun x y ↦ (realDifferenceReplay_isAt cs x y).2.2.1)
      (affineMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p) 1 0 1)
    intro x y
    rw [(realDifferenceReplay_values cs x y).2.2.1]
    simp only [affineMarginalJet, zero_mul, zero_add, one_mul]
    have h := marginalDifferenceHorner_hasDerivAt cs y (y-x)
    simp_rw [show ∀ t, marginalHorner (· + ·) (· * ·) 0 t cs = marginalTaylorPolynomial p 0 t from
      marginalHorner_taylor hp] at h
    exact h.unique (hasDerivAt_marginalTaylorPolynomial p 0 y)
  exact ⟨hv, hd, hprime,
    jet_eq_of_value_eq (fun x y ↦ (realDifferenceReplay_isAt cs x y).2.2.2.1)
      (weightedMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p) continuous_const 1)
      (fun x y ↦ (taylorDifference_values hp x y).1) u v,
    jet_eq_of_value_eq (fun x y ↦ (realDifferenceReplay_isAt cs x y).2.2.2.2)
      (weightedMarginalJet_isAt (hasDerivAt_marginalTaylorPolynomial p)
        (continuous_const.sub continuous_id) 2)
      (fun x y ↦ (taylorDifference_values hp x y).2) u v⟩

#print axioms marginalDifferenceHorner_taylor

end

end RefinedBMV.PositiveCenter.SmallCorner
