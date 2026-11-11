/- GID: D5/S3/QuadraticForms/RealThreePathFiniteQueryBoundary
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/RealThreePathFiniteQueryBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth phase-invariant countermodels preserve every finite three-path menu. -/

module

public import D5.S3.QuadraticForms.RealThreePathRepresentation
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Finite exact readout agreement does not certify the universal three-path law. -/

public section
noncomputable section

namespace D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary

open RealThreePathPolar ThreeWayPositiveKernel Polynomial
open scoped BigOperators ContDiff

/-- The arguments actually read by one original recipe, including its baseline. -/
@[expose] def readPoints (r : ℂ × ℂ × ℝ) : Finset ℂ :=
  {0, r.1, r.2.1, r.2.2 • r.1, r.2.2 • r.2.1,
    r.1 + r.2.2 • r.2.1, r.1 + r.2.2 • (omega * r.2.1),
    r.2.2 • (omega * r.1) + r.2.1}

/-- The six signed three-phase images of one original point. -/
@[expose] def orbit (a : ℂ) : Finset ℂ :=
  {a, omega * a, omega ^ 2 * a, -a, -(omega * a), -(omega ^ 2 * a)}

/-- Closure of a finite readout menu under the three phases and negation. -/
@[expose] def phaseClosure (A : Finset ℂ) : Finset ℂ :=
  (insert 0 A).biUnion orbit

/-- The source's squared distance product, with no supplied existence oracle. -/
@[expose] def distanceProduct (S : Finset ℂ) (z : ℂ) : ℝ :=
  ∏ a ∈ S, Complex.normSq (z - a)

/-- The same explicit perturbation is used for every clause of the boundary. -/
@[expose] def perturbedReadout (S : Finset ℂ) (ε : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq z + ε * distanceProduct S z ^ 2

/-- One test uses the original baseline and the uncalibrated scalar readouts. -/
@[expose] def Passes (q : ℂ → ℝ) (r : ℂ × ℂ × ℝ) : Prop :=
  let Q := fun z => q z - q 0
  Q (r.1 + r.2.2 • r.2.1) + Q (r.1 + r.2.2 • (omega * r.2.1)) +
    Q (r.2.2 • (omega * r.1) + r.2.1) =
    2 * Q r.1 + Q r.2.1 + Q (r.2.2 • r.1) + 2 * Q (r.2.2 • r.2.1)

private theorem phase_data : omega ^ 3 = 1 ∧ Complex.normSq omega = 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hs]
  constructor
  · apply Complex.ext <;> simp [omega, pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith [hc]
  · simp [omega, Complex.normSq_apply]; nlinarith

private theorem closure_contains (A : Finset ℂ) : insert 0 A ⊆ phaseClosure A := by
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [orbit]⟩

private theorem closure_neg (A : Finset ℂ) {z : ℂ} (hz : z ∈ phaseClosure A) :
    -z ∈ phaseClosure A := by
  obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
  refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  rcases hz with h | h | h | h | h | h <;> subst z <;> simp

private theorem closure_phase (A : Finset ℂ) {z : ℂ} (hz : z ∈ phaseClosure A) :
    omega * z ∈ phaseClosure A := by
  obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
  refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
  have hc : omega * (omega ^ 2 * a) = a := by
    calc
      _ = omega ^ 3 * a := by ring
      _ = a := by rw [phase_data.1, one_mul]
  have hh : omega * (omega * a) = omega ^ 2 * a := by ring
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  rcases hz with h | h | h | h | h | h <;> subst z <;>
    simp only [mul_neg, hh, hc] <;> tauto

private theorem product_zero {S : Finset ℂ} {a : ℂ} (ha : a ∈ S) :
    distanceProduct S a = 0 := by
  exact Finset.prod_eq_zero ha (by simp)

private theorem product_neg (A : Finset ℂ) (z : ℂ) :
    distanceProduct (phaseClosure A) (-z) = distanceProduct (phaseClosure A) z := by
  unfold distanceProduct
  apply Finset.prod_bij' (fun a _ => -a) (fun a _ => -a)
    (fun _ h => closure_neg A h) (fun _ h => closure_neg A h)
    (by intros; simp) (by intros; simp)
  intro a ha
  rw [show -z - a = -(z - -a) by ring, Complex.normSq_neg]

private theorem product_phase (A : Finset ℂ) (z : ℂ) :
    distanceProduct (phaseClosure A) (omega * z) = distanceProduct (phaseClosure A) z := by
  unfold distanceProduct
  have hc (a : ℂ) : omega * (omega ^ 2 * a) = a := by
    calc
      _ = omega ^ 3 * a := by ring
      _ = a := by rw [phase_data.1, one_mul]
  apply Finset.prod_bij' (fun a _ => omega ^ 2 * a) (fun a _ => omega * a)
    (fun a h => by simpa [pow_two, mul_assoc] using closure_phase A (closure_phase A h))
    (fun _ h => closure_phase A h)
    (by intro a ha; calc
      _ = omega ^ 3 * a := by ring
      _ = a := by rw [phase_data.1, one_mul])
    (by intro a ha; calc
      _ = omega * (omega ^ 2 * a) := by ring
      _ = a := hc a)
  intro a ha
  rw [show omega * z - a = omega * (z - omega ^ 2 * a) by rw [mul_sub, hc],
    Complex.normSq_mul, phase_data.2, one_mul]

private theorem readout_nonneg (S : Finset ℂ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    0 ≤ perturbedReadout S ε z :=
  add_nonneg (Complex.normSq_nonneg _) (mul_nonneg hε.le (sq_nonneg _))

private theorem readout_smooth (S : Finset ℂ) (ε : ℝ) :
    ContDiff ℝ ∞ (perturbedReadout S ε) := by
  have hn : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
    simpa only [Complex.normSq_eq_norm_sq] using (contDiff_norm_sq ℂ (E := ℂ) (n := ∞))
  have hp : ContDiff ℝ ∞ (distanceProduct S) := by
    apply contDiff_prod
    intro a ha
    exact hn.comp (contDiff_id.sub contDiff_const)
  exact hn.add (contDiff_const.mul (hp.pow 2))

private def rayFactor (a : ℂ) : ℝ[X] := (X - C a.re) ^ 2 + C (a.im ^ 2)

private theorem rayFactor_degree (a : ℂ) : (rayFactor a).natDegree = 2 := by
  rw [rayFactor, natDegree_add_C, natDegree_pow, natDegree_X_sub_C]

private theorem rayFactor_monic (a : ℂ) : (rayFactor a).Monic := by
  apply ((monic_X_sub_C a.re).pow 2).add_of_left
  apply lt_of_le_of_lt degree_C_le
  rw [degree_pow, degree_X_sub_C]
  norm_num

private theorem not_balance (S : Finset ℂ) (hzero : 0 ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ¬ Balance (fun z : ℂ => omega * z) (perturbedReadout S ε) := by
  intro hb
  obtain ⟨B, _, _, hd, _⟩ := raw_real_polar _ _ (readout_nonneg S hε) hb
  have hq0 : perturbedReadout S ε 0 = 0 := by
    simp [perturbedReadout, product_zero hzero]
  have hscale (t : ℝ) : perturbedReadout S ε (t : ℂ) = t ^ 2 * perturbedReadout S ε 1 := by
    have ht : (t : ℂ) = t • (1 : ℂ) := by simp
    calc
      _ = B (t • (1 : ℂ)) (t • (1 : ℂ)) := by rw [ht, hd, hq0, zero_add]
      _ = t ^ 2 * B 1 1 := by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [hd 1, hq0, zero_add]
  let R : ℝ[X] := ∏ a ∈ S, rayFactor a
  have heval (t : ℝ) : R.eval t = distanceProduct S (t : ℂ) := by
    simp only [R, Polynomial.eval_prod, rayFactor, eval_add, eval_pow, eval_sub,
      eval_X, eval_C, distanceProduct]
    apply Finset.prod_congr rfl
    intro a ha
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have heq : R ^ 2 = C ((perturbedReadout S ε 1 - 1) / ε) * X ^ 2 := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hall (t : ℝ) : (R ^ 2).eval t =
        (C ((perturbedReadout S ε 1 - 1) / ε) * X ^ 2).eval t := by
      simp only [eval_pow, heval, eval_mul, eval_C, eval_X]
      have hh := hscale t
      rw [show perturbedReadout S ε (t : ℂ) =
        t * t + ε * distanceProduct S (t : ℂ) ^ 2 by
          simp only [perturbedReadout, Complex.normSq_ofReal]] at hh
      field_simp [ne_of_gt hε]
      nlinarith
    simpa only [hall, Set.ofPred_true] using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℝ))
  have hdR : R.natDegree = 2 * S.card := by
    change (∏ a ∈ S, rayFactor a).natDegree = _
    rw [natDegree_prod_of_monic S rayFactor (fun a _ => rayFactor_monic a)]
    simp [rayFactor_degree, Nat.mul_comm]
  have hdeg : (C ((perturbedReadout S ε 1 - 1) / ε) * X ^ 2).natDegree ≤ 2 := by
    calc
      _ ≤ (C ((perturbedReadout S ε 1 - 1) / ε) : ℝ[X]).natDegree + (X ^ 2 : ℝ[X]).natDegree := natDegree_mul_le
      _ = 2 := by simp
  rw [← heq, natDegree_pow, hdR] at hdeg
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨0, hzero⟩
  omega

private theorem standard_balance : Balance (fun z : ℂ => omega * z) Complex.normSq := by
  apply (RealThreePathRepresentation.original_hilbert_characterization.{0, 0, 0} _ _
    Complex.normSq_nonneg).2.1 ℂ (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
  · intro z
    simp [Complex.normSq_eq_norm_sq]
  · intro z
    rfl

/-- Every finite menu admits the explicit smooth, positive and symmetric readout
which agrees with all its original values but fails the global relation. -/
-- proof_shape: content; admission_basis: escape-witness.
-- The orbit-closed product construction is live in every conclusion below.
theorem finite_query_boundary (menu : Finset (ℂ × ℂ × ℝ)) (ε : ℝ) (hε : 0 < ε) :
    let S := phaseClosure (menu.biUnion readPoints)
    ∃ q : ℂ → ℝ, q = perturbedReadout S ε ∧
    (0 ∈ S) ∧ (∀ r ∈ menu, readPoints r ⊆ S) ∧
    ContDiff ℝ ∞ q ∧ (∀ z, 0 ≤ q z) ∧ (∀ z, z ≠ 0 → 0 < q z) ∧
    q 0 = 0 ∧ (∀ z, q (omega * z) = q z) ∧ (∀ z, q (-z) = q z) ∧
    (∀ a ∈ S, q a = Complex.normSq a) ∧
    (∀ r ∈ menu, Passes q r) ∧ ¬ Balance (fun z : ℂ => omega * z) q := by
  classical
  let A := menu.biUnion readPoints
  let S := phaseClosure A
  have hz : 0 ∈ S := closure_contains A (Finset.mem_insert_self _ _)
  have hreads (r) (hr : r ∈ menu) : readPoints r ⊆ S := by
    intro z hzr
    exact closure_contains A (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, hzr⟩))
  have hagree (a) (ha : a ∈ S) : perturbedReadout S ε a = Complex.normSq a := by
    simp [perturbedReadout, product_zero ha]
  have hq0 : perturbedReadout S ε 0 = 0 := by simpa using hagree 0 hz
  refine ⟨perturbedReadout S ε, rfl, hz, hreads, readout_smooth S ε, readout_nonneg S hε, ?_, hq0, ?_, ?_,
    hagree, ?_, not_balance S hz hε⟩
  · intro z hz
    exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hz) (mul_nonneg hε.le (sq_nonneg _))
  · intro z
    simp only [perturbedReadout, Complex.normSq_mul, phase_data.2, one_mul]
    rw [product_phase]
  · intro z
    simp only [perturbedReadout, Complex.normSq_neg]
    rw [product_neg]
  · intro r hr
    have hvalues (a : ℂ) (ha : a ∈ readPoints r) := hagree a (hreads r hr ha)
    have h := standard_balance r.1 r.2.1 r.2.2
    change Passes Complex.normSq r at h
    unfold Passes at h ⊢
    have hv : ∀ a ∈ readPoints r, perturbedReadout S ε a = Complex.normSq a := hvalues
    dsimp only
    simp only [Complex.normSq_zero, sub_zero] at h
    simpa only [hv _ (by simp only [readPoints, Finset.mem_insert, Finset.mem_singleton]; tauto),
      hq0, sub_zero] using h

end D5.S3.QuadraticForms.RealThreePathFiniteQueryBoundary
