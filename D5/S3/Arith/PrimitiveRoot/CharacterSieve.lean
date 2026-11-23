/- GID: D5/S3/Arith/PrimitiveRoot/CharacterSieve
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/CharacterSieve
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character sieve bounds for primitive-root weights. -/
import D5.S3.Arith.PrimitiveRoot.CharacterExpansion
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
/-! Exact defect corrections and smoothed bounds for primitive roots. -/
namespace D5.S3.Arith.PrimitiveRoot.CharacterSieve
open scoped BigOperators Classical
open D5.S3.Factorization.Galois.GeneralPowerCharacterLayer (powerSubgroup)
open D5.S3.Arith.PrimitiveRoot.CharacterExpansion
export D5.S3.Arith.PrimitiveRoot.CharacterExpansion
  (theta delta errorCoefficient errorCoefficientAbs)
private lemma powerSubgroup_eq_kernel (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hq : q ∣ p - 1) : powerSubgroup ((ZMod p)ˣ) q =
      (powMonoidHom ((p - 1) / q) : (ZMod p)ˣ →* (ZMod p)ˣ).ker := by
  apply IsCyclic.subgroup_eq_iff_card_eq.mpr; rw [powerSubgroup, IsCyclic.card_powMonoidHom_range,
      IsCyclic.card_powMonoidHom_ker,
    Nat.card_eq_fintype_card, ZMod.card_units, Nat.gcd_eq_right hq,
    Nat.gcd_eq_right (Nat.div_dvd_of_dvd hq)]
private lemma powerSubgroup_mem (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hq : q ∣ p - 1) (a : (ZMod p)ˣ) :
    a ∈ powerSubgroup ((ZMod p)ˣ) q ↔ a ^ ((p - 1) / q) = 1 := by
  rw [powerSubgroup_eq_kernel p hq]; rfl
private lemma sum_units_primitive (p : ℕ) [NeZero p] (W : ZMod p → ℝ) :
    (∑ a : (ZMod p)ˣ, if orderOf a = p - 1 then W a else 0) =
      ∑ a ∈ Finset.univ.filter (fun a : ZMod p => orderOf a = p - 1), W a := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a ha => (a : ZMod p)) ?_ ?_ ?_ ?_
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, orderOf_units] using ha
  · intro a ha b hb hab; exact Units.val_injective hab
  · intro a ha
    have hoa := (Finset.mem_filter.mp ha).2
    have hu : IsUnit a := by
      by_cases hp1 : p = 1
      · subst p
        rw [Subsingleton.elim a 1]
        exact isUnit_one
      · apply IsOfFinOrder.isUnit
        apply orderOf_pos_iff.mp
        rw [hoa]
        have := NeZero.ne p
        omega
    refine ⟨hu.unit, ?_, hu.unit_spec⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← orderOf_units, hu.unit_spec] using hoa
  · intro a ha; rfl
/-- The sieve primes: primes of `T` that divide `p - 1` and do not divide `e`. -/
def sievePrimes (p e : ℕ) (T : Finset ℕ) : Finset ℕ :=
  T.filter (fun t => t.Prime ∧ t ∣ p - 1 ∧ ¬ t ∣ e)
/-- The exact excess of the primitive-root indicator over the linear sieve. -/
noncomputable def defect (p e : ℕ) (T : Finset ℕ) (a : (ZMod p)ˣ) : ℝ :=
  let b := ((sievePrimes p e T).filter
    (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card
  if (∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q) ∧ 2 ≤ b then
    (b : ℝ) - 1 else 0
private lemma pointwise_defect (p : ℕ) [Fact p.Prime] (e : ℕ) (he0 : e ≠ 0)
    (he : ∀ q ∈ e.primeFactors, q ∣ p - 1) (T : Finset ℕ)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T) (a : (ZMod p)ˣ) :
    (if orderOf a = p - 1 then (1 : ℝ) else 0) =
      (if ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q then 1 else 0) *
        (1 - (((sievePrimes p e T).filter
          (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card : ℝ)) + defect p e T a := by
  let U := sievePrimes p e T
  let b := (U.filter (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card
  have hp : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hroot : orderOf a = p - 1 ↔
      (∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q) ∧ b = 0 := by
    constructor
    · intro ho
      have hn (q : ℕ) (hq : q.Prime) (hd : q ∣ p - 1) :
          a ∉ powerSubgroup ((ZMod p)ˣ) q := by
        intro ha
        have hh := orderOf_dvd_of_pow_eq_one ((powerSubgroup_mem p hd a).mp ha)
        rw [ho] at hh
        exact (Nat.not_le_of_lt (Nat.div_lt_self hp hq.one_lt))
          (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hp hd) hq.pos) hh)
      refine ⟨fun q hq => hn q (Nat.prime_of_mem_primeFactors hq) (he q hq), ?_⟩
      apply Finset.card_eq_zero.mpr; apply Finset.filter_eq_empty_iff.mpr
      intro t ht; exact hn t (Finset.mem_filter.mp ht).2.1 (Finset.mem_filter.mp ht).2.2.1
    · rintro ⟨hf, hb⟩
      apply orderOf_eq_of_pow_and_pow_div_prime hp
      · rw [← ZMod.card_units p]; exact pow_card_eq_one
      · intro q hq hd
        apply (not_congr (powerSubgroup_mem p hd a)).mp
        rcases hcover q hq hd with hqe | hqt
        · exact hf q (Nat.mem_primeFactors.mpr ⟨hq, hqe, he0⟩)
        · intro ha
          have hqU : q ∈ U := Finset.mem_filter.mpr ⟨hqt, hq, hd, fun hqe =>
            hf q (Nat.mem_primeFactors.mpr ⟨hq, hqe, he0⟩) ha⟩
          have hpos : 0 < b := Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqU, ha⟩⟩
          omega
  change (if orderOf a = p - 1 then (1 : ℝ) else 0) =
    (if ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q then 1 else 0) *
      (1 - (b : ℝ)) +
      (if (∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q) ∧ 2 ≤ b then
        (b : ℝ) - 1 else 0)
  by_cases hf : ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q
  · by_cases hb : b = 0
    · have ho := hroot.mpr ⟨hf, hb⟩
      simp only [ite_eq_left ho, ite_eq_left hf, hb]; norm_num
    · have ho : orderOf a ≠ p - 1 := fun h => hb (hroot.mp h).2
      by_cases hb2 : 2 ≤ b
      · simp only [ite_eq_right ho, ite_eq_left hf, ite_eq_left (And.intro hf hb2)]
        ring
      · have hb1 : b = 1 := by omega
        simp only [ite_eq_right ho, ite_eq_left hf, hb1]; norm_num
  · have ho : orderOf a ≠ p - 1 := fun h => hf (hroot.mp h).1
    have hn : ¬((∀ q ∈ e.primeFactors,
        a ∉ powerSubgroup ((ZMod p)ˣ) q) ∧ 2 ≤ b) := fun h => hf h.1
    simp only [ite_eq_right ho, ite_eq_right hf, ite_eq_right hn, zero_mul, add_zero]
private lemma primitive_weight_identity (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ)
    (e : ℕ) (T : Finset ℕ) (he : e ≠ 0 ∧ ∀ q ∈ e.primeFactors, q ∣ p - 1)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T) :
    (∑ a ∈ Finset.univ.filter (fun a : ZMod p => orderOf a = p - 1), W a) =
      (∑ a : (ZMod p)ˣ, W a *
        (if ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q then 1 else 0) *
        (1 - (((sievePrimes p e T).filter
          (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card : ℝ))) +
      ∑ a : (ZMod p)ˣ, W a * defect p e T a := by
  rw [← sum_units_primitive p W]
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _
  have hh := congrArg (fun x : ℝ => W a * x) (pointwise_defect p e he.1 he.2 T hcover a)
  simp only [mul_add, ← mul_assoc] at hh
  simpa only [mul_ite, mul_one, mul_zero] using hh

/-- The full defect-corrected absolute error estimate, for every margin. -/
theorem primitive_weight_error_bound (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ) (e : ℕ)
    (T : Finset ℕ) (he : e ≠ 0)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T) (M : ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M) :
    |(∑ a ∈ Finset.univ.filter (fun a : ZMod p => orderOf a = p - 1), W a) -
      (∑ a : (ZMod p)ˣ, W a * defect p (Nat.gcd e (p - 1)) T a) -
      theta (Nat.gcd e (p - 1)) * delta (sievePrimes p e T) * ∑ a : (ZMod p)ˣ, W a| ≤
        theta (Nat.gcd e (p - 1)) *
          errorCoefficientAbs (Nat.gcd e (p - 1)) (sievePrimes p e T) * M := by
  classical
  let f := Nat.gcd e (p - 1)
  have hf0 : f ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero he))
  have hfe : f ∣ e := Nat.gcd_dvd_left _ _
  have hfp : f ∣ p - 1 := Nat.gcd_dvd_right _ _
  have hsub := Nat.primeFactors_mono hfe he
  have hU : sievePrimes p f T = sievePrimes p e T := by
    ext t; simp only [sievePrimes, Finset.mem_filter]
    constructor
    · rintro ⟨ht, hp, hd, hn⟩
      exact ⟨ht, hp, hd, fun he => hn (Nat.dvd_gcd he hd)⟩
    · rintro ⟨ht, hp, hd, hn⟩; exact ⟨ht, hp, hd, fun hf => hn (hf.trans hfe)⟩
  have hR : (∏ q ∈ f.primeFactors, q) ∣ ∏ q ∈ e.primeFactors, q :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hf : ∀ q ∈ f.primeFactors, q ∣ p - 1 :=
    fun q hq => (Nat.dvd_of_mem_primeFactors hq).trans hfp
  have hb := weighted_sieve_error_bound p W f hf (sievePrimes p f T)
    (fun t ht => ⟨(Finset.mem_filter.mp ht).2.1, (Finset.mem_filter.mp ht).2.2.1,
      fun h => (Finset.mem_filter.mp ht).2.2.2 (Nat.dvd_of_mem_primeFactors h)⟩) M (by
      intro χ hχ hs; apply hM χ hχ
      rw [hU] at hs
      exact hs.imp (fun h => h.trans hR) (fun ⟨t, ht, hd⟩ =>
        ⟨t, ht, hd.trans (Nat.mul_dvd_mul_left t hR)⟩))
  rw [primitive_weight_identity p W f T ⟨hf0, hf⟩
    (fun q hq hd => (hcover q hq hd).imp (fun h => Nat.dvd_gcd h hd) id)]
  rw [hU] at hb
  simpa only [hU, f, add_sub_cancel_right] using hb
/-- The full signed-coefficient error estimate when the reduced coefficients agree. -/
theorem primitive_weight_lower_bound (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ) (e : ℕ)
    (T : Finset ℕ) (he : e ≠ 0)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T) (M : ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M) :
    0 ≤ delta (sievePrimes p e T) ∨ (Nat.gcd e (p - 1)).primeFactors = ∅ →
    |(∑ a ∈ Finset.univ.filter (fun a : ZMod p => orderOf a = p - 1), W a) -
      (∑ a : (ZMod p)ˣ, W a * defect p (Nat.gcd e (p - 1)) T a) -
      theta (Nat.gcd e (p - 1)) * delta (sievePrimes p e T) * ∑ a : (ZMod p)ˣ, W a| ≤
        theta (Nat.gcd e (p - 1)) *
          errorCoefficient (Nat.gcd e (p - 1)) (sievePrimes p e T) * M := by
  intro hδ
  rw [← (errorCoefficientAbs_eq (Nat.gcd e (p - 1)) (sievePrimes p e T)).mpr hδ]
  exact primitive_weight_error_bound p W e T he hcover M hM
/-- The von Mangoldt sum smoothed by `1 - m/p`, twisted by a Dirichlet character. -/
noncomputable def smoothedCharacterSum (p : ℕ) (χ : DirichletCharacter ℂ p) : ℂ :=
  ∑ m ∈ Finset.range p, (ArithmeticFunction.vonMangoldt m : ℂ) *
    (1 - (m : ℂ) / p) * χ m
private noncomputable def smoothWeight (p m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m * (1 - (m : ℝ) / p)
private noncomputable def residueWeight (p : ℕ) (a : ZMod p) : ℝ :=
  ∑ m ∈ (Finset.range p).filter (fun m : ℕ => (m : ZMod p) = a), smoothWeight p m
/-- The smoothed primitive-root weight on residue classes. -/
noncomputable def smoothedPrimitiveWeight (p : ℕ) [NeZero p] : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : ZMod p => orderOf a = p - 1), residueWeight p a
/-- The full smoothed defect correction, with the sieve parameter supplied explicitly. -/
noncomputable def smoothedDefect (p : ℕ) [NeZero p] (e : ℕ) (T : Finset ℕ) : ℝ :=
  ∑ a : (ZMod p)ˣ, residueWeight p a * defect p e T a
private lemma smoothWeight_nonneg {p m : ℕ} (hm : m < p) :
    0 ≤ smoothWeight p m := by
  apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg; apply sub_nonneg.mpr
  exact (div_le_one (by exact_mod_cast (Nat.zero_lt_of_lt hm))).mpr
    (by exact_mod_cast hm.le)
private lemma residueWeight_nonneg (p : ℕ) (a : ZMod p) : 0 ≤ residueWeight p a := by
  apply Finset.sum_nonneg; intro m hm
  exact smoothWeight_nonneg (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
private lemma residueWeight_character (p : ℕ) [NeZero p] (χ : DirichletCharacter ℂ p) :
    ∑ a : ZMod p, (residueWeight p a : ℂ) * χ a = smoothedCharacterSum p χ := by
  classical
  unfold residueWeight smoothedCharacterSum; simp only [Complex.ofReal_sum, Finset.sum_mul]; calc
    _ = ∑ a : ZMod p, ∑ m ∈ (Finset.range p).filter
        (fun m : ℕ => (m : ZMod p) = a), (smoothWeight p m : ℂ) * χ m := by
      apply Finset.sum_congr rfl
      intro a ha; apply Finset.sum_congr rfl; intro m hm; rw [(Finset.mem_filter.mp hm).2]
    _ = ∑ m ∈ Finset.range p, (smoothWeight p m : ℂ) * χ m :=
      Finset.sum_fiberwise _ (fun m : ℕ => (m : ZMod p)) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm; simp [smoothWeight]
private lemma residueWeight_principal (p : ℕ) [NeZero p] :
    (smoothedCharacterSum p 1).re = ∑ a : (ZMod p)ˣ, residueWeight p a := by
  rw [← residueWeight_character,
    sum_units_character p (fun a => (residueWeight p a : ℂ))]
  simp [Complex.re_sum, MulChar.one_apply_coe]
private lemma exists_prime_of_residueWeight_pos (p : ℕ) [Fact p.Prime]
    (hpos : 0 < ∑ a ∈ Finset.univ.filter
      (fun a : ZMod p => orderOf a = p - 1), residueWeight p a) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  classical
  obtain ⟨a, ha, hwa⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun a _ => residueWeight_nonneg p a)).mp hpos
  obtain ⟨m, hm, hwm⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun m hm => smoothWeight_nonneg
      (Finset.mem_range.mp (Finset.mem_filter.mp hm).1))).mp hwa
  have hmp : m < p := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hma : (m : ZMod p) = a := (Finset.mem_filter.mp hm).2
  have hlambda : 0 < ArithmeticFunction.vonMangoldt m :=
    (mul_pos_iff.mp hwm).elim (fun h => h.1) (fun h =>
      False.elim (not_lt_of_ge ArithmeticFunction.vonMangoldt_nonneg h.1))
  obtain ⟨q, k, hq, hk, hqm⟩ :=
    (isPrimePow_nat_iff m).mp (ArithmeticFunction.vonMangoldt_pos_iff.mp hlambda)
  have hqp : q < p := (hqm ▸ Nat.le_pow hk).trans_lt hmp
  refine ⟨q, hq, hqp, ?_⟩
  have hord : orderOf ((q : ZMod p) ^ k) = p - 1 := by
    rw [← Nat.cast_pow, hqm, hma]; exact (Finset.mem_filter.mp ha).2
  apply Nat.dvd_antisymm
  · exact ZMod.orderOf_dvd_card_sub_one (by
      intro hz; have hd : p ∣ q := (CharP.cast_eq_zero_iff (ZMod p) p q).mp hz
      exact Nat.not_dvd_of_pos_of_lt hq.pos hqp hd)
  · rw [← hord]
    exact orderOf_pow_dvd k
/-- Gcd reduction preserves the complete smoothed two-sided estimate and defect sign. -/
theorem smoothed_primitive_weight_error_bound (p : ℕ) [Fact p.Prime] (e : ℕ)
    (T : Finset ℕ) (M : ℝ)
    (he : e ≠ 0)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(smoothedCharacterSum p χ).re| ≤ M)
    : 0 ≤ (smoothedCharacterSum p 1).re ∧ 0 ≤ smoothedPrimitiveWeight p ∧
      0 ≤ smoothedDefect p (Nat.gcd e (p - 1)) T ∧
      |smoothedPrimitiveWeight p - smoothedDefect p (Nat.gcd e (p - 1)) T -
        theta (Nat.gcd e (p - 1)) * delta (sievePrimes p e T) *
          (smoothedCharacterSum p 1).re| ≤
        theta (Nat.gcd e (p - 1)) *
          errorCoefficientAbs (Nat.gcd e (p - 1)) (sievePrimes p e T) * M := by
  have hm : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (residueWeight p a : ℂ) * χ a).re| ≤ M := by
    intro χ hχ hs; rw [residueWeight_character]; exact hM χ hχ hs
  have hD : 0 ≤ ∑ a : (ZMod p)ˣ, residueWeight p a * defect p (Nat.gcd e (p - 1)) T a := by
    apply Finset.sum_nonneg; intro a _
    apply mul_nonneg (residueWeight_nonneg p a)
    unfold defect; dsimp only; split_ifs with ha
    · have hh : (2 : ℝ) ≤ (((sievePrimes p (Nat.gcd e (p - 1)) T).filter
        (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card : ℝ) := by
        exact_mod_cast ha.2
      linarith
    · exact le_rfl
  have hS : 0 ≤ (smoothedCharacterSum p 1).re := by
    rw [residueWeight_principal]
    exact Finset.sum_nonneg fun a _ => residueWeight_nonneg p a
  have hP : 0 ≤ smoothedPrimitiveWeight p :=
    Finset.sum_nonneg fun a _ => residueWeight_nonneg p a
  refine ⟨hS, hP, hD, ?_⟩
  rw [residueWeight_principal]
  by_cases hδ : 0 ≤ delta (sievePrimes p e T)
  · rw [(errorCoefficientAbs_eq (Nat.gcd e (p - 1)) (sievePrimes p e T)).mpr (Or.inl hδ)]
    exact primitive_weight_lower_bound p (residueWeight p) e T he hcover M hm (Or.inl hδ)
  · exact primitive_weight_error_bound p (residueWeight p) e T he hcover M hm
/-- A positive defect-corrected margin produces a prime primitive root below `p`. -/
theorem exists_prime_primitiveRoot_of_smoothed (p : ℕ) [Fact p.Prime] (e : ℕ)
    (T : Finset ℕ) (M : ℝ)
    (he : e ≠ 0)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(smoothedCharacterSum p χ).re| ≤ M)
    (hpos : 0 < theta (Nat.gcd e (p - 1)) *
      (delta (sievePrimes p e T) * (smoothedCharacterSum p 1).re -
        errorCoefficientAbs (Nat.gcd e (p - 1)) (sievePrimes p e T) * M) +
      smoothedDefect p (Nat.gcd e (p - 1)) T) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  have hb := (abs_le.mp
    (smoothed_primitive_weight_error_bound p e T M he hcover hM).2.2.2).1
  apply exists_prime_of_residueWeight_pos p
  change 0 < smoothedPrimitiveWeight p
  nlinarith

/-- A strict signed margin is positive and produces a prime primitive root. -/
theorem exists_prime_primitiveRoot_of_smoothed_signed (p : ℕ) [Fact p.Prime] (e : ℕ)
    (T : Finset ℕ) (M : ℝ)
    (he : e ≠ 0)
    (hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(smoothedCharacterSum p χ).re| ≤ M)
    (hpos : errorCoefficient (Nat.gcd e (p - 1)) (sievePrimes p e T) * M <
      delta (sievePrimes p e T) * (smoothedCharacterSum p 1).re) :
    0 < delta (sievePrimes p e T) ∧
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  have hquant := smoothed_primitive_weight_error_bound p e T M he hcover hM
  have hD := hquant.2.2.1
  have hδ : 0 < delta (sievePrimes p e T) := by
    by_contra hn
    have hTn : (sievePrimes p e T).Nonempty := by
      by_contra hnone
      rw [Finset.not_nonempty_iff_eq_empty.mp hnone] at hn
      norm_num [delta] at hn
    obtain ⟨t, ht⟩ := hTn
    have hM0 := bound_nonneg p (fun a => (residueWeight p a : ℂ)) M t (by
      intro χ ho
      rw [Nat.gcd_eq_left (Finset.mem_filter.mp ht).2.2.1] at ho
      rw [residueWeight_character p χ]
      apply hM χ (by
        intro hc; rw [hc, orderOf_one] at ho
        exact (Finset.mem_filter.mp ht).2.1.ne_one ho.symm)
      apply Or.inr; refine ⟨t, ht, ?_⟩
      rw [ho]; exact dvd_mul_right t _)
    have hK := (errorCoefficient_nonneg (Nat.gcd e (p - 1)) (sievePrimes p e T)).mp
      (calc
        _ ≤ ∑ _t ∈ sievePrimes p e T, (2 : ℝ)⁻¹ := Finset.sum_le_sum fun t ht =>
          inv_anti₀ (by norm_num)
            (by exact_mod_cast (Finset.mem_filter.mp ht).2.1.two_le)
        _ = _ := by simp [div_eq_mul_inv])
    have hS := hquant.1
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hS
    have := mul_nonneg hK.2 hM0
    linarith
  refine ⟨hδ, ?_⟩
  apply exists_prime_primitiveRoot_of_smoothed p e T M he hcover hM
  rw [(errorCoefficientAbs_eq (Nat.gcd e (p - 1))
    (sievePrimes p e T)).mpr (Or.inl hδ.le)]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (CharacterExpansion.theta_pos _) (sub_pos.mpr hpos)) hD

end D5.S3.Arith.PrimitiveRoot.CharacterSieve
