/- GID: D5/S3/VertexAlgebra/CollisionAnalytic/FinalLaurentEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CollisionAnalytic/FinalLaurentEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute evaluation of the original final inverse Laurent fibers. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentFiber
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! proof_shape: content
admission_basis: escape-witness
escape_witness: joint inverse-binomial summability precedes regrouping
of the original signed fibers.
The generalized binomial coefficients, geometric sums, and infinite-sum
reindexing are reused from Mathlib (Apache 2.0). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology
namespace D5.S3.VertexAlgebra.FinalLaurentEvaluation
open ThreeFieldFinalLaurentFiber
open StateFieldResidueReconstruction (integerBinomial)
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision

private theorem binomial_succ (m n : ℕ) :
    integerBinomial (-((m + 1 : ℕ) : ℤ)) n =
      (-1 : ℂ)^n * ((n + m).choose m : ℂ) := by
  rw [integerBinomial, Ring.choose_neg,
    show ((m + 1 : ℕ) : ℤ) + n - 1 = ((m + n : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
    Int.cast_negOnePow_natCast, Int.cast_natCast]
  rw [← Nat.choose_symm_add, Nat.add_comm m n]

private theorem binomial_zero (n : ℕ) :
    integerBinomial 0 n = if n = 0 then 1 else 0 := by
  simp [integerBinomial, Ring.choose_zero_ite]

private theorem binomial_hasSum (m : ℕ) (r : ℂ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => integerBinomial (-(m : ℤ)) n * r^n)
      ((1 + r)^m)⁻¹ := by
  cases m with
  | zero =>
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℂ)) using 1
    · funext n
      by_cases hn : n = 0 <;> simp [binomial_zero, hn]
    · simp
  | succ m =>
    convert hasSum_choose_mul_geometric_of_norm_lt_one m
      (show ‖-r‖ < 1 by simpa using hr) using 1
    · funext n
      rw [binomial_succ, neg_pow]
      ring
    · simp

private theorem binomial_norm_summable (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (h : t < 1) :
    Summable (fun n : ℕ => ‖integerBinomial (-(m : ℤ)) n‖ * t^n) := by
  cases m with
  | zero =>
    have he : (fun n : ℕ => ‖integerBinomial 0 n‖ * t^n) =
        fun n : ℕ => if n = 0 then (1 : ℝ) else 0 := by
      funext n
      by_cases hn : n = 0 <;> simp [binomial_zero, hn]
    simpa only [Nat.cast_zero, neg_zero, he] using (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  | succ m =>
    have he (n : ℕ) : ‖integerBinomial (-((m + 1 : ℕ) : ℤ)) n‖ =
        ((n + m).choose m : ℝ) := by
      rw [binomial_succ, norm_mul, norm_pow]
      simp
    simpa only [he] using summable_choose_mul_geometric_of_norm_lt_one m
      (show ‖t‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg ht] using h)

private theorem choose_hasSum (q : ℕ) (r : ℂ) :
    HasSum (fun h : ℕ => (q.choose h : ℂ) * r^h) ((1 + r)^q) := by
  have hs : HasSum (fun h : ℕ => (q.choose h : ℂ) * r^h)
      (∑ h ∈ Finset.range (q + 1), (q.choose h : ℂ) * r^h) :=
    hasSum_sum_of_ne_finset_zero (fun h hh => by
      have hh' : q < h := by
        have hh'' : ¬ h < q + 1 := by simpa only [Finset.mem_range] using hh
        omega
      rw [Nat.choose_eq_zero_of_lt hh', Nat.cast_zero, zero_mul])
  convert hs using 1
  simpa [add_comm, mul_comm] using (add_pow r (1 : ℂ) q)

private theorem choose_norm_sum (q : ℕ) (t : ℝ) :
    HasSum (fun h : ℕ => (q.choose h : ℝ) * t^h) ((1 + t)^q) := by
  have hs : HasSum (fun h : ℕ => (q.choose h : ℝ) * t^h)
      (∑ h ∈ Finset.range (q + 1), (q.choose h : ℝ) * t^h) :=
    hasSum_sum_of_ne_finset_zero (fun h hh => by
      rw [Nat.choose_eq_zero_of_lt (by
        have hh' : ¬ h < q + 1 := by simpa only [Finset.mem_range] using hh
        omega),
        Nat.cast_zero, zero_mul])
  convert hs using 1
  simpa [add_comm, mul_comm] using (add_pow t (1 : ℝ) q)

private def coupled (m : ℕ) (r s : ℂ) (p : ℕ × ℕ) : ℂ :=
  integerBinomial (-(m : ℤ)) p.1 * s^p.1 * (p.1.choose p.2 : ℂ) * r^p.2

private theorem coupled_norm (m : ℕ) (r s : ℂ)
    (h : (1 + ‖r‖) * ‖s‖ < 1) : Summable (fun p => ‖coupled m r s p‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  constructor
  · intro q
    have hc := (choose_norm_sum q ‖r‖).summable.mul_left
      (‖integerBinomial (-(m : ℤ)) q‖ * ‖s‖^q)
    simpa [coupled, norm_mul, norm_pow, mul_assoc] using hc
  · have hb := binomial_norm_summable m ((1 + ‖r‖) * ‖s‖)
      (mul_nonneg (by positivity) (norm_nonneg _)) h
    convert hb using 1
    funext q
    simp only [coupled, norm_mul, norm_pow, Complex.norm_natCast, mul_assoc,
      tsum_mul_left]
    rw [← mul_assoc, (choose_norm_sum q ‖r‖).tsum_eq, mul_pow]
    ring

private theorem coupled_hasSum (m : ℕ) (r s : ℂ)
    (h : (1 + ‖r‖) * ‖s‖ < 1) :
    HasSum (coupled m r s) ((1 + (1 + r) * s)^m)⁻¹ := by
  have ha := (coupled_norm m r s h).of_norm
  have hr : ‖(1 + r) * s‖ < 1 := by
    calc
      ‖(1 + r) * s‖ = ‖1 + r‖ * ‖s‖ := norm_mul _ _
      _ ≤ (1 + ‖r‖) * ‖s‖ := mul_le_mul_of_nonneg_right
        (by simpa using norm_add_le (1 : ℂ) r) (norm_nonneg _)
      _ < 1 := h
  have hf (q : ℕ) : HasSum (fun h => coupled m r s (q,h))
      (integerBinomial (-(m : ℤ)) q * ((1 + r) * s)^q) := by
    convert (choose_hasSum q r).mul_left
      (integerBinomial (-(m : ℤ)) q * s^q) using 1
    · funext h; simp only [coupled]; ring
    · rw [mul_pow]; ring
  exact (ha.hasSum.prod_fiberwise hf).unique
    (binomial_hasSum m ((1 + r) * s) hr) ▸ ha.hasSum

private theorem product_hasSum {α β : Type*} (f : α → ℂ) (g : β → ℂ)
    (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun i => ‖g i‖))
    {u v : ℂ} (hu : HasSum f u) (hv : HasSum g v) :
    HasSum (fun p : α × β => f p.1 * g p.2) (u * v) := by
  have h := (summable_mul_of_summable_norm hf hg).hasSum
  rwa [← tsum_mul_tsum_of_summable_norm hf hg, hu.tsum_eq, hv.tsum_eq] at h

private def splitIndex : LaurentIndex ≃ ℕ × ((ℕ × ℕ) × ℕ) where
  toFun i := (i.1.1, ((i.1.2, i.2.1), i.2.2))
  invFun p := ((p.1,p.2.1.1),(p.2.1.2,p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def kernel (k : ℕ) (a : Fin 3 → ℕ) (r s : ℂ) (i : LaurentIndex) : ℂ :=
  (integerBinomial (-(k : ℤ)) i.1.1 * r^i.1.1) * (coupled (a 0) r s (i.1.2,i.2.1) * (integerBinomial (-(a 1 : ℤ)) i.2.2 * s^i.2.2))

private theorem kernel_evaluation (k : ℕ) (a : Fin 3 → ℕ) (r s : ℂ)
    (hr : ‖r‖ < 1) (h : (1 + ‖r‖) * ‖s‖ < 1) :
    Summable (fun i => ‖kernel k a r s i‖) ∧
    HasSum (kernel k a r s)
      (((1 + r)^k)⁻¹ * (((1 + (1 + r) * s)^(a 0))⁻¹ * ((1 + s)^(a 1))⁻¹)) := by
  have hs : ‖s‖ < 1 := lt_of_le_of_lt (by nlinarith [norm_nonneg r, norm_nonneg s]) h
  have bn (m : ℕ) (t : ℂ) (ht : ‖t‖ < 1) :
      Summable (fun n : ℕ => ‖integerBinomial (-(m : ℤ)) n * t^n‖) := by
    simpa only [norm_mul, norm_pow] using binomial_norm_summable m ‖t‖ (norm_nonneg _) ht
  have hj := bn k r hr
  have hq := coupled_norm (a 0) r s h
  have hl := bn (a 1) s hs
  constructor
  · exact splitIndex.summable_iff.mpr (hj.mul_norm (hq.mul_norm hl))
  · exact splitIndex.hasSum_iff.mpr (product_hasSum _ _ hj (hq.mul_norm hl)
      (binomial_hasSum k r hr) (product_hasSum _ _ hq hl
        (coupled_hasSum (a 0) r s h) (binomial_hasSum (a 1) s hs)))

private def monomial (z : Fin 3 → ℂ) (e : Fin 3 → ℤ) : ℂ := ∏ c, z c ^ e c

private theorem monomial_add (z : Fin 3 → ℂ) (hz : ∀ c, z c ≠ 0)
    (e f : Fin 3 → ℤ) : monomial z (e + f) = monomial z e * monomial z f := by
  simp only [monomial, Pi.add_apply, zpow_add₀ (hz _), Finset.prod_mul_distrib]

private def natExponent (d : Fin 3 →₀ ℕ) : Fin 3 → ℤ := fun c => (d c : ℤ)

private theorem natExponent_injective : Function.Injective natExponent := by
  intro d f h
  ext c
  have hc : (d c : ℤ) = (f c : ℤ) := congrFun h c
  exact_mod_cast hc

private theorem index_natExponent (d : Fin 3 →₀ ℕ) : signedIndex (natExponent d) = d := by
  ext c
  simp [signedIndex, natExponent]

private theorem natExponent_index (n : Fin 3 → ℤ) (hn : ∀ c, 0 ≤ n c) :
    natExponent (signedIndex n) = n := by
  funext c
  simp [natExponent, signedIndex, Int.toNat_of_nonneg (hn c)]

private theorem signed_poly_nat (Q : MvPolynomial (Fin 3) ℂ) (d : Fin 3 →₀ ℕ) :
    signedExtend (Q : MvPowerSeries (Fin 3) ℂ) (natExponent d) = Q.coeff d := by
  rw [signedExtend, if_pos (by intro c; exact Int.natCast_nonneg _), index_natExponent]
  rfl

private def numerator (Q : MvPolynomial (Fin 3) ℂ) (z : Fin 3 → ℂ)
    (n : Fin 3 → ℤ) : ℂ := signedExtend (Q : MvPowerSeries (Fin 3) ℂ) n * monomial z n

private theorem numerator_support (Q : MvPolynomial (Fin 3) ℂ) (z : Fin 3 → ℂ) :
    Function.support (numerator Q z) ⊆ (Q.support.image natExponent : Set (Fin 3 → ℤ)) := by
  classical
  intro n hn
  by_cases hp : ∀ c, 0 ≤ n c
  · have hq : Q.coeff (signedIndex n) ≠ 0 := by
      intro hq
      exact hn (by simp [numerator, signedExtend, hp, show
        (Q : MvPowerSeries (Fin 3) ℂ) (signedIndex n) = Q.coeff (signedIndex n) from rfl, hq])
    exact Finset.mem_image.mpr ⟨signedIndex n, MvPolynomial.mem_support_iff.mpr hq,
      natExponent_index n hp⟩
  · exact (hn (by simp [numerator, signedExtend, hp])).elim

private theorem numerator_evaluation (Q : MvPolynomial (Fin 3) ℂ) (z : Fin 3 → ℂ) :
    Summable (fun n => ‖numerator Q z n‖) ∧ HasSum (numerator Q z) (MvPolynomial.eval z Q) := by
  classical
  have hzero (n : Fin 3 → ℤ) (hn : n ∉ Q.support.image natExponent) : numerator Q z n = 0 := by
    by_contra h
    exact hn (numerator_support Q z h)
  constructor
  · exact (hasSum_sum_of_ne_finset_zero (s := Q.support.image natExponent)
      (fun n hn => by rw [hzero n hn, norm_zero])).summable
  · have hh : HasSum (numerator Q z)
        (∑ n ∈ Q.support.image natExponent, numerator Q z n) :=
      hasSum_sum_of_ne_finset_zero hzero
    convert hh using 1
    rw [Finset.sum_image (fun d _ f _ h => natExponent_injective h)]
    rw [MvPolynomial.eval_eq']
    apply Finset.sum_congr rfl
    intro d _
    simp only [numerator, signed_poly_nat, monomial, natExponent, zpow_natCast]

private def offset (k : ℕ) (a : Fin 3 → ℕ) (i : LaurentIndex) : Fin 3 → ℤ :=
  ![-(k : ℤ) + i.1.1 + i.2.1,
    -2 * (k : ℤ)-i.1.1 + i.1.2-i.2.1 + i.2.2,
    -((a 0 : ℤ) + a 1 + a 2)-i.1.2-i.2.2]

private theorem input_offset (k : ℕ) (a : Fin 3 → ℕ) (n : Fin 3 → ℤ)
    (i : LaurentIndex) : laurentInput k a (n + offset k a i) i = n := by
  funext c
  fin_cases c <;> simp [laurentInput, offset] <;> omega

private def inputEquiv (k : ℕ) (a : Fin 3 → ℕ) :
    ((Fin 3 → ℤ) × LaurentIndex) ≃ ((Fin 3 → ℤ) × LaurentIndex) where
  toFun p := (laurentInput k a p.1 p.2, p.2)
  invFun p := (p.1 + offset k a p.2, p.2)
  left_inv p := by
    refine Prod.ext ?_ rfl
    funext c
    fin_cases c <;> simp [laurentInput, offset] <;> omega
  right_inv p := by simp only [input_offset]

private def prefactor (k : ℕ) (a : Fin 3 → ℕ) (z : Fin 3 → ℂ) : ℂ :=
  z 0 ^ (-(k : ℤ)) * z 1 ^ (-2 * (k : ℤ)) * z 2 ^ (-((a 0 : ℤ) + a 1 + a 2))

private theorem offset_weight (k : ℕ) (a : Fin 3 → ℕ) (z : Fin 3 → ℂ)
    (hz : ∀ c, z c ≠ 0) (i : LaurentIndex) :
    laurentWeight k a i * monomial z (offset k a i) =
      prefactor k a z * kernel k a (z 0 / z 1) (z 1 / z 2) i := by
  simp [monomial, Fin.prod_univ_succ, offset, laurentWeight, prefactor, kernel, coupled,
    zpow_add₀ (hz _), zpow_sub₀ (hz _), div_pow]
  ring

private theorem term_no_conditional (Q : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℤ) (i : LaurentIndex) :
    laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a e i =
      laurentWeight k a i * signedExtend (Q : MvPowerSeries (Fin 3) ℂ)
        (laurentInput k a e i) := by
  by_cases hi : i.2.1 ≤ i.1.2
  · simp [laurentTerm, hi, smul_eq_mul]
  · simp [laurentTerm, hi, laurentWeight, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi)]

private theorem raw_factor (Q : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (a : Fin 3 → ℕ) (z : Fin 3 → ℂ) (hz : ∀ c, z c ≠ 0)
    (n : Fin 3 → ℤ) (i : LaurentIndex) :
    laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a (n + offset k a i) i * monomial z (n + offset k a i) =
    numerator Q z n * (prefactor k a z * kernel k a (z 0 / z 1) (z 1 / z 2) i) := by
  rw [term_no_conditional, input_offset, monomial_add z hz]
  calc
    _ = numerator Q z n * (laurentWeight k a i * monomial z (offset k a i)) := by
      unfold numerator
      ring
    _ = _ := by rw [offset_weight k a z hz]

private theorem raw_evaluation (Q : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (a : Fin 3 → ℕ) (z : Fin 3 → ℂ) (hz : ∀ c, z c ≠ 0)
    (hr : ‖z 0 / z 1‖ < 1) (hc : (1 + ‖z 0 / z 1‖) * ‖z 1 / z 2‖ < 1) :
    Summable (fun p : (Fin 3 → ℤ) × LaurentIndex =>
      ‖laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a p.1 p.2 * monomial z p.1‖) ∧
    HasSum (fun p : (Fin 3 → ℤ) × LaurentIndex =>
      laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a p.1 p.2 * monomial z p.1)
      (MvPolynomial.eval z Q * (prefactor k a z *
        (((1 + z 0 / z 1)^k)⁻¹ *
          (((1 + (1 + z 0 / z 1) * (z 1 / z 2))^(a 0))⁻¹ *
            ((1 + z 1 / z 2)^(a 1))⁻¹)))) := by
  obtain ⟨hn, hv⟩ := numerator_evaluation Q z
  obtain ⟨hk, hs⟩ := kernel_evaluation k a (z 0 / z 1) (z 1 / z 2) hr hc
  have hp : Summable (fun i => ‖prefactor k a z * kernel k a (z 0 / z 1) (z 1 / z 2) i‖) := by
    simpa only [norm_mul] using hk.mul_left ‖prefactor k a z‖
  constructor
  · apply (inputEquiv k a).symm.summable_iff.mp
    simpa only [Function.comp_def, inputEquiv, Equiv.coe_fn_symm_mk, raw_factor Q k a z hz]
      using hn.mul_norm hp
  · apply (inputEquiv k a).symm.hasSum_iff.mp
    simpa only [Function.comp_def, inputEquiv, Equiv.coe_fn_symm_mk, raw_factor Q k a z hz]
      using product_hasSum _ _ hn hp hv (hs.mul_left (prefactor k a z))

private theorem fiber_hasSum (Q : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (a : Fin 3 → ℕ) (z : Fin 3 → ℂ) (e : Fin 3 → ℤ) :
    HasSum (fun i : LaurentIndex =>
      laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a e i * monomial z e)
      (laurentCoefficient (Q : MvPowerSeries (Fin 3) ℂ) k a e * monomial z e) := by
  classical
  have hz (i : LaurentIndex) (hi : i ∉ laurentFiber k a e) :
      laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a e i * monomial z e = 0 := by
    have hi' : ¬ LaurentAdmissible k a e i := by
      simpa only [mem_laurentFiber_iff] using hi
    by_cases hq : i.2.1 ≤ i.1.2
    · have hn : ¬ ∀ c, 0 ≤ laurentInput k a e i c := fun hn => hi' ⟨hq, hn⟩
      simp [laurentTerm, hq, signedExtend, hn]
    · simp [laurentTerm, hq]
  have hs : HasSum (fun i : LaurentIndex =>
      laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a e i * monomial z e)
      (∑ i ∈ laurentFiber k a e,
        laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a e i * monomial z e) :=
    hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  rw [laurentCoefficient_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [laurentTerm, if_pos ((mem_laurentFiber_iff k a e i).1 hi).1]

/-- The original final inverse Laurent coefficient is absolutely summable over
all signed exponents and has its exact rational value. The ungrouped native
term family is absolutely summable as well. -/
theorem final_laurent_absolute_evaluation
    (Q : MvPolynomial (Fin 3) ℂ) (k : ℕ) (a : Fin 3 → ℕ)
    (x y z : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : ‖x‖ < ‖y‖) (hxyz : ‖x‖ + ‖y‖ < ‖z‖) :
    Summable (fun p : (Fin 3 → ℤ) × LaurentIndex =>
      ‖laurentTerm (Q : MvPowerSeries (Fin 3) ℂ) k a p.1 p.2 * (x^p.1 0 * y^p.1 1 * z^p.1 2)‖) ∧
    Summable (fun e : Fin 3 → ℤ =>
      ‖laurentCoefficient (Q : MvPowerSeries (Fin 3) ℂ) k a e * (x^e 0 * y^e 1 * z^e 2)‖) ∧
    HasSum (fun e : Fin 3 → ℤ =>
      laurentCoefficient (Q : MvPowerSeries (Fin 3) ℂ) k a e * (x^e 0 * y^e 1 * z^e 2))
      (MvPolynomial.eval ![x,y,z] Q / (x^k * y^k * (x + y)^k * (x + y + z)^(a 0) * (y + z)^(a 1) * z^(a 2))) := by
  let w : Fin 3 → ℂ := ![x,y,z]
  have hw : ∀ c, w c ≠ 0 := by intro c; fin_cases c <;> assumption
  have hr : ‖x / y‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hy)).2 hxy
  have hc : (1 + ‖x / y‖) * ‖y / z‖ < 1 := by
    rw [norm_div, norm_div]
    have he : (1 + ‖x‖ / ‖y‖) * (‖y‖ / ‖z‖) = (‖x‖ + ‖y‖) / ‖z‖ := by
      field_simp [norm_ne_zero_iff.mpr hy, norm_ne_zero_iff.mpr hz]
      <;> ring
    rw [he]
    exact (div_lt_one (norm_pos_iff.mpr hz)).2 hxyz
  obtain ⟨ha, hs⟩ := raw_evaluation Q k a w hw hr hc
  have hm (e : Fin 3 → ℤ) : monomial w e = x^e 0 * y^e 1 * z^e 2 := by
    simp [monomial, w, Fin.prod_univ_succ, mul_assoc]
  have hf := fiber_hasSum Q k a w
  have hg := hs.prod_fiberwise hf
  have hnorm : Summable (fun e : Fin 3 → ℤ =>
      ‖laurentCoefficient (Q : MvPowerSeries (Fin 3) ℂ) k a e * monomial w e‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun e => ?_) ha.prod
    rw [← (hf e).tsum_eq]
    exact norm_tsum_le_tsum_norm (ha.prod_factor e)
  have hnxy : x + y ≠ 0 := by
    intro he
    have hh : x = -y := eq_neg_of_add_eq_zero_left he
    rw [hh, norm_neg] at hxy
    exact (lt_irrefl _ hxy)
  have hnyz : y + z ≠ 0 := by
    intro he
    have hh : z = -y := eq_neg_of_add_eq_zero_right he
    rw [hh, norm_neg] at hxyz
    linarith [norm_nonneg x]
  have hnxyz : x + y + z ≠ 0 := by
    intro he
    have hh : z = -(x + y) := eq_neg_of_add_eq_zero_right he
    rw [hh, norm_neg] at hxyz
    exact (not_lt_of_ge (norm_add_le x y) hxyz)
  have value : MvPolynomial.eval w Q * (prefactor k a w * (((1 + x / y)^k)⁻¹ * (((1 + (1 + x / y) * (y / z))^(a 0))⁻¹ * ((1 + y / z)^(a 1))⁻¹))) =
      MvPolynomial.eval w Q / (x^k * y^k * (x + y)^k * (x + y + z)^(a 0) * (y + z)^(a 1) * z^(a 2)) := by
    have h1 : 1 + x / y = (x + y) / y := by field_simp [hy] <;> ring
    have h2 : 1 + (1 + x / y) * (y / z) = (x + y + z) / z := by field_simp [hy, hz] <;> ring
    have h3 : 1 + y / z = (y + z) / z := by field_simp [hz] <;> ring
    rw [h2, h1, h3]
    simp only [prefactor, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      show -2 * (k : ℤ) = -((k + k : ℕ) : ℤ) by omega,
      show -((a 0 : ℤ) + a 1 + a 2) = -((a 0 + a 1 + a 2 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, div_pow, inv_div, pow_add, pow_mul]
    field_simp [hx, hy, hz, hnxy, hnyz, hnxyz]
    <;> ring
  refine ⟨by simpa only [hm] using ha, by simpa only [hm] using hnorm, ?_⟩
  convert hg using 1
  · funext e; rw [hm]
  · exact value.symm

#print axioms final_laurent_absolute_evaluation

end D5.S3.VertexAlgebra.FinalLaurentEvaluation
