/- GID: D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Biased trine qubit measurements have the conjectured triplewise threshold. -/

import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence

/-! The biased trine family and its exact eight-outcome compatibility threshold. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
open D5.S3.Quantum.Measurement.FourQubitParentConstruction
open D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence
  (FamilyJointlyMeasurable)
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)

namespace D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold

/-- Index `i : Fin 3` denotes source index `i + 1`; the coordinates are ordered x,y,z. -/
def trineDir (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (![![-1 / 2, 0, Real.sqrt 3 / 2],
    ![-1 / 2, 0, -Real.sqrt 3 / 2], ![1, 0, 0]] i)

/-- The source's first family, with `true` denoting outcome +1 and `false` outcome -1. -/
def trineEffect (b η : ℝ) (k : Fin 3) (x : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • scalarB (1 + sgn x * b) ((η * sgn x) • trineDir k)

/-- A single eight-outcome POVM has all six specified binary marginals. -/
def TriplewiseJointlyMeasurable (b η : ℝ) : Prop :=
  FamilyJointlyMeasurable (trineEffect b η)

/-- The three cases of the conjectured threshold, including both central endpoints. -/
def trineThreshold (b : ℝ) : ℝ :=
  if b < -1 / 3 then 1 + b else if b ≤ 1 / 3 then 2 / 3 else 1 - b

private lemma trine_source (k : Fin 3) :
    trineDir k = WithLp.toLp 2
      ![Real.cos (2 * ((k.val : ℝ) + 1) * Real.pi / 3), 0,
        Real.sin (2 * ((k.val : ℝ) + 1) * Real.pi / 3)] := by
  fin_cases k
  · have he : (2 : ℝ) * (0 + 1) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    dsimp only [trineDir]
    simp only [Nat.cast_zero, he, Real.cos_pi_sub,
      Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    norm_num
  · have he : (2 : ℝ) * (1 + 1) * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    dsimp only [trineDir]
    simp only [Nat.cast_one, he,
      Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_three, Real.sin_pi_div_three]
    ext j
    fin_cases j <;> norm_num; ring
  · have he : (2 : ℝ) * (2 + 1) * Real.pi / 3 = 2 * Real.pi := by ring
    dsimp only [trineDir]
    simp only [Nat.cast_ofNat, he,
      Real.cos_two_pi, Real.sin_two_pi]
    rfl

private lemma trine_norm (k : Fin 3) : ‖trineDir k‖ = 1 := by
  rw [trine_source]
  have hn := norm_sq_coords (WithLp.toLp 2
    ![Real.cos (2 * ((k.val : ℝ) + 1) * Real.pi / 3), 0,
      Real.sin (2 * ((k.val : ℝ) + 1) * Real.pi / 3)])
  norm_num at hn
  rcases hn with hn | hn <;> nlinarith [norm_nonneg (WithLp.toLp 2
    ![Real.cos (2 * ((k.val : ℝ) + 1) * Real.pi / 3), 0,
      Real.sin (2 * ((k.val : ℝ) + 1) * Real.pi / 3)] : EuclideanSpace ℝ (Fin 3))]

private lemma trine_sum : ∑ k : Fin 3, trineDir k = 0 := by
  ext j
  fin_cases j <;> dsimp only [trineDir] <;> norm_num [Fin.sum_univ_three]; ring

private lemma sign_sum_bound (s : Fin 3 → Bool) :
    ‖∑ k : Fin 3, sgn (s k) • trineDir k‖ ≤ 2 := by
  have hz := trine_sum
  rw [Fin.sum_univ_three] at hz
  unfold sgn
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    simp only [Fin.sum_univ_three, h0, h1, h2, Bool.false_eq_true,
      ite_false, ite_true, one_smul, neg_smul] <;>
    first
    | simpa only [← neg_add, hz, neg_zero, norm_zero] using (show (0 : ℝ) ≤ 2 by norm_num)
    | (have he : -trineDir 0 + -trineDir 1 + trineDir 2 = (2 : ℝ) • trineDir 2 := by
         linear_combination (norm := module) -hz
       rw [he, norm_smul, trine_norm]; norm_num)
    | (have he : -trineDir 0 + trineDir 1 + -trineDir 2 = (2 : ℝ) • trineDir 1 := by
         linear_combination (norm := module) -hz
       rw [he, norm_smul, trine_norm]; norm_num)
    | (have he : -trineDir 0 + trineDir 1 + trineDir 2 = (-2 : ℝ) • trineDir 0 := by
         linear_combination (norm := module) hz
       rw [he, norm_smul, trine_norm]; norm_num)
    | (have he : trineDir 0 + -trineDir 1 + -trineDir 2 = (2 : ℝ) • trineDir 0 := by
         linear_combination (norm := module) -hz
       rw [he, norm_smul, trine_norm]; norm_num)
    | (have he : trineDir 0 + -trineDir 1 + trineDir 2 = (-2 : ℝ) • trineDir 1 := by
         linear_combination (norm := module) hz
       rw [he, norm_smul, trine_norm]; norm_num)
    | (have he : trineDir 0 + trineDir 1 + -trineDir 2 = (-2 : ℝ) • trineDir 2 := by
         linear_combination (norm := module) hz
       rw [he, norm_smul, trine_norm]; norm_num)

private lemma scalarB_injective (t u : ℝ) (a v : EuclideanSpace ℝ (Fin 3))
    (h : scalarB t a = scalarB u v) : t = u ∧ a = v := by
  unfold scalarB at h
  have h00 : t + a 2 = u + v 2 := by
    simpa [B_formula, Complex.mul_re, Complex.mul_im] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m 0 0).re) h
  have h11 : t + -a 2 = u + -v 2 := by
    simpa [B_formula, Complex.mul_re, Complex.mul_im] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m 1 1).re) h
  have h01 : a 0 = v 0 := by
    simpa [B_formula, Complex.mul_re, Complex.mul_im] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m 0 1).re) h
  have hi : a 1 = v 1 := by
    simpa [B_formula, Complex.mul_re, Complex.mul_im] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => (m 0 1).im) h
  constructor
  · linarith
  · ext j
    fin_cases j
    · exact h01
    · exact hi
    · change a 2 = v 2
      linarith

private lemma scalarB_one : scalarB 1 (0 : EuclideanSpace ℝ (Fin 3)) = 1 := by
  simp only [scalarB, Complex.ofReal_one, one_smul, B_zero, add_zero]

private lemma effect_coordinates (b η : ℝ) (k : Fin 3) (x : Bool) :
    trineEffect b η k x = scalarB ((1 + sgn x * b) / 2)
      ((η * sgn x / 2) • trineDir k) := by
  unfold trineEffect
  have ht : 2 * ((1 + sgn x * b) / 2) = 1 + sgn x * b := by ring
  have ha : (2 : ℝ) • ((η * sgn x / 2) • trineDir k) =
      (η * sgn x) • trineDir k := by module
  simpa only [ht, ha] using half_scalarB_double ((1 + sgn x * b) / 2)
    ((η * sgn x / 2) • trineDir k)

private lemma parent_coordinates (b η : ℝ)
    (h : TriplewiseJointlyMeasurable b η) :
    ∃ (q : (Fin 3 → Bool) → ℝ) (r : (Fin 3 → Bool) → EuclideanSpace ℝ (Fin 3)),
      (∀ s, ‖r s‖ ≤ q s) ∧ (∑ s, q s) = 1 ∧
      ∀ k, ∑ s, sgn (s k) • r s = η • trineDir k := by
  classical
  obtain ⟨g, hg, hm⟩ := h
  let q := fun s => (Matrix.trace (g s)).re / 2
  let r := fun s => (1 / 2 : ℝ) •
    D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (g s)
  have he : ∀ s, g s = scalarB (q s) (r s) := fun s =>
    hermitian_decomposition (g s) (hg.1 s).isHermitian
  refine ⟨q, r, ?_, ?_, ?_⟩
  · intro s
    exact (scalarB_posSemidef_iff _ _).mp ((he s) ▸ hg.1 s)
  · have ht : scalarB (∑ s, q s) (∑ s, r s) = scalarB 1 0 := by
      rw [scalarB_sum, scalarB_one, ← hg.2]
      exact Finset.sum_congr (by ext s; simp) fun s _ => (he s).symm
    exact (scalarB_injective _ _ _ _ ht).1
  · intro k
    have hx : ∀ x : Bool, (∑ s with s k = x, r s) =
        (η * sgn x / 2) • trineDir k := by
      intro x
      have ht : scalarB (∑ s with s k = x, q s) (∑ s with s k = x, r s) =
          scalarB ((1 + sgn x * b) / 2) ((η * sgn x / 2) • trineDir k) := by
        rw [scalarB_sum, ← effect_coordinates, ← hm k x]
        exact Finset.sum_congr (by ext s; simp) fun s _ => (he s).symm
      exact (scalarB_injective _ _ _ _ ht).2
    have hp := hx true
    have hn := hx false
    have hf : (∑ s, sgn (s k) • r s) =
        (∑ s with s k = true, r s) - ∑ s with s k = false, r s := by
      simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      unfold sgn
      cases s k <;> simp
    rw [hf, hp, hn]
    unfold sgn
    simp only [ite_true, Bool.false_eq_true, ite_false, mul_one, mul_neg_one]
    rw [← sub_smul]
    congr 1
    ring

private lemma necessity_certificate (b η : ℝ)
    (h : TriplewiseJointlyMeasurable b η) : 3 * η ≤ 2 := by
  classical
  obtain ⟨q, r, hq, hsum, hr⟩ := parent_coordinates b η h
  have he : (∑ s, ⟪∑ k : Fin 3, sgn (s k) • trineDir k, r s⟫_ℝ) = 3 * η := by
    simp only [sum_inner, real_inner_smul_left]
    rw [Finset.sum_comm]
    have hk : ∀ k, (∑ s, sgn (s k) * ⟪trineDir k, r s⟫_ℝ) = η := by
      intro k
      calc
        _ = ⟪trineDir k, ∑ s, sgn (s k) • r s⟫_ℝ := by
          simp only [inner_sum, real_inner_smul_right]
        _ = η := by rw [hr k, real_inner_smul_right, real_inner_self_eq_norm_sq, trine_norm]; ring
    simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  calc
    3 * η = _ := he.symm
    _ ≤ ∑ s, 2 * ‖r s‖ := Finset.sum_le_sum fun s _ =>
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (sign_sum_bound s) (norm_nonneg _))
    _ ≤ ∑ s, 2 * q s := Finset.sum_le_sum fun s _ => by linarith [hq s]
    _ = 2 := by rw [← Finset.mul_sum, hsum]; ring

private lemma necessity (b η : ℝ) (hd : |b| ≤ 1 - η)
    (h : TriplewiseJointlyMeasurable b η) : η ≤ trineThreshold b := by
  have hc := necessity_certificate b η h
  unfold trineThreshold
  split_ifs <;> have ha := abs_le.mp (show |b| ≤ 1 - η from hd) <;> linarith

lemma sum_strings {α : Type*} [AddCommMonoid α] (f : (Fin 3 → Bool) → α) :
    (∑ s, f s) = f ![false, false, false] + f ![false, false, true] +
      f ![false, true, false] + f ![false, true, true] +
      f ![true, false, false] + f ![true, false, true] +
      f ![true, true, false] + f ![true, true, true] := by
  classical
  have hu : (Finset.univ : Finset (Fin 3 → Bool)) =
      {![false, false, false], ![false, false, true], ![false, true, false],
       ![false, true, true], ![true, false, false], ![true, false, true],
       ![true, true, false], ![true, true, true]} := by decide
  rw [hu]
  simp
  abel

private def parent (c d u v e f : ℝ) (s : Fin 3 → Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if s 0 then
    if s 1 then
      if s 2 then scalarB e 0 else scalarB c ((-u) • trineDir 2)
    else if s 2 then scalarB c ((-u) • trineDir 1) else scalarB d (v • trineDir 0)
  else if s 1 then
    if s 2 then scalarB c ((-u) • trineDir 0) else scalarB d (v • trineDir 1)
  else if s 2 then scalarB d (v • trineDir 2) else scalarB f 0

private lemma parent_sum (c d u v e f : ℝ) :
    (∑ s, parent c d u v e f s) = scalarB (3 * c + 3 * d + e + f) 0 := by
  rw [sum_strings]
  dsimp only [parent]
  unfold scalarB
  simp only [B_formula]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp only [trineDir] <;> simp <;> ring

private lemma parent_marginal (c d u v e f : ℝ) (k : Fin 3) (x : Bool) :
    (∑ s with s k = x, parent c d u v e f s) =
      if x then scalarB (2 * c + d + e) ((u + v) • trineDir k)
      else scalarB (c + 2 * d + f) ((-(u + v)) • trineDir k) := by
  classical
  rw [Finset.sum_filter, sum_strings]
  fin_cases k <;> cases x <;> dsimp only [parent]
  all_goals
    unfold scalarB
    simp only [B_formula]
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp only [trineDir] <;> simp <;> ring

private lemma parent_valid (b η c d u v e f : ℝ)
    (hc : |u| ≤ c) (hd : |v| ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hp : 2 * c + d + e = (1 + b) / 2)
    (hn : c + 2 * d + f = (1 - b) / 2) (hv : u + v = η / 2) :
    TriplewiseJointlyMeasurable b η := by
  classical
  refine ⟨parent c d u v e f, ⟨?_, ?_⟩, ?_⟩
  · intro s
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
      dsimp only [parent] <;>
      simp only [h0, h1, h2, Bool.false_eq_true, ite_false, ite_true] <;>
      apply (scalarB_posSemidef_iff _ _).mpr <;>
      simp only [norm_smul, trine_norm, Real.norm_eq_abs, abs_neg, mul_one, norm_zero]
    all_goals assumption
  · have hs : (∑ s : Fin 3 → Bool, parent c d u v e f s) = 1 := by
      rw [parent_sum]
      have hnorm : 3 * c + 3 * d + e + f = 1 := by linarith
      rw [hnorm, scalarB_one]
    convert hs using 1
    apply Finset.sum_congr
    · ext s; simp
    · intro s _; rfl
  · intro k x
    have hm : (∑ s : Fin 3 → Bool with s k = x, parent c d u v e f s) =
        trineEffect b η k x := by
      rw [parent_marginal, effect_coordinates]
      unfold sgn
      cases x <;> simp only [Bool.false_eq_true, ite_false, ite_true, hp, hn, hv,
        mul_one, mul_neg_one]
      · congr 1
        · ring
        · congr 1
          ring
      · congr 1
        ring
    convert hm using 1
    apply Finset.sum_congr
    · ext s; simp
    · intro s _; rfl

private lemma parent_central (b η : ℝ) (hb : -(1 / 3 : ℝ) ≤ b)
    (hb1 : b ≤ 1 / 3) (hη : 0 ≤ η) (hη1 : η ≤ 2 / 3) :
    TriplewiseJointlyMeasurable b η := by
  let c := (1 + 3 * b) / 6
  let d := (1 - 3 * b) / 6
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hd : 0 ≤ d := by dsimp [d]; linarith
  apply parent_valid b η c d (c * (3 * η / 2)) (d * (3 * η / 2)) 0 0
  · rw [abs_of_nonneg (mul_nonneg hc (by positivity))]
    nlinarith
  · rw [abs_of_nonneg (mul_nonneg hd (by positivity))]
    nlinarith
  · rfl
  · rfl
  · dsimp [c, d]; ring
  · dsimp [c, d]; ring
  · dsimp [c, d]; ring

private lemma parent_positive (b η : ℝ) (hb : 1 / 3 ≤ b)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 - b) : TriplewiseJointlyMeasurable b η := by
  apply parent_valid b η ((1 - b) / 2) 0 (η / 2) 0 ((3 * b - 1) / 2) 0
  · rw [abs_of_nonneg (by positivity)]; linarith
  · norm_num
  · linarith
  · rfl
  · ring
  · ring
  · ring

private lemma parent_negative (b η : ℝ) (hb1 : b ≤ -(1 / 3 : ℝ))
    (hη : 0 ≤ η) (hη1 : η ≤ 1 + b) : TriplewiseJointlyMeasurable b η := by
  apply parent_valid b η 0 ((1 + b) / 2) 0 (η / 2) 0 ((-1 - 3 * b) / 2)
  · norm_num
  · rw [abs_of_nonneg (by positivity)]; linarith
  · rfl
  · linarith
  · ring
  · ring
  · ring

/-- The exact triplewise joint-measurability threshold on the source parameter domain. -/
theorem result : ∀ b η : ℝ, -1 ≤ b → b ≤ 1 → 0 ≤ η → η ≤ 1 →
    |b| ≤ 1 - η → (TriplewiseJointlyMeasurable b η ↔ η ≤ trineThreshold b) := by
  intro b η _ _ hη _ hd
  constructor
  · exact necessity b η hd
  · intro ht
    unfold trineThreshold at ht
    split_ifs at ht with hn hp
    · exact parent_negative b η (by linarith) hη ht
    · exact parent_central b η (by linarith) hp hη ht
    · exact parent_positive b η (le_of_not_ge hp) hη ht

end D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold
