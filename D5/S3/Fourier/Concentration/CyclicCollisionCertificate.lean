/- GID: D5/S3/Fourier/Concentration/CyclicCollisionCertificate
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicCollisionCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Certified lattice approximations transfer weighted collisions to cyclic sums. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
import D5.S3.Fourier.FinitePoisson

/-! Weighted collision bounds from certified lattice approximations. -/

set_option autoImplicit false

open Finset
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
  (tailCollisionMass nearCollisionMass monomialWeight_nonneg)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
  (monomialFrequency monomialWeight)

noncomputable section

namespace D5.S3.Fourier.Concentration.CyclicCollisionCertificate

/-- The integral sum of the lattice coordinates with their multiplicities. -/
def latticeFrequency {J : Type*} [Fintype J] (a : J → ℤ) (m : J → ℕ) : ℤ :=
  ∑ j, (m j : ℤ) * a j

/-- The mass of ordered pairs of degree-p vectors whose lattice gap is in the cyclic band. -/
def cyclicCollisionMass {J : Type*} [Fintype J] [DecidableEq J] (q : ℕ)
    (a : J → ℤ) (w : J → ℝ) (p : ℕ) (R : Finset (ZMod q)) : ℝ :=
  ∑ m ∈ piAntidiag univ p, ∑ n ∈ piAntidiag univ p,
    if ((latticeFrequency a m - latticeFrequency a n : ℤ) : ZMod q) ∈ R
      then monomialWeight w m * monomialWeight w n else 0

private theorem signed_gap_error_le {J : Type*} [Fintype J]
    (g : J → ℝ) (a : J → ℤ) (step e : ℝ)
    (happrox : ∀ j, |g j - step * (a j : ℝ)| ≤ e) (he : 0 ≤ e)
    (m n : J → ℕ) (p : ℕ) (hm : (∑ j, m j) = p) (hn : (∑ j, n j) = p) :
    |(monomialFrequency g m - monomialFrequency g n) -
      step * ((latticeFrequency a m - latticeFrequency a n : ℤ) : ℝ)| ≤ 2 * p * e := by
  have hrewrite :
      (monomialFrequency g m - monomialFrequency g n) -
          step * ((latticeFrequency a m - latticeFrequency a n : ℤ) : ℝ) =
        ∑ j, ((m j : ℝ) - n j) * (g j - step * (a j : ℝ)) := by
    unfold monomialFrequency latticeFrequency
    push_cast
    simp only [mul_sub, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun _ _ => ?_
    ring
  have hmR : (∑ j, (m j : ℝ)) = p := by exact_mod_cast hm
  have hnR : (∑ j, (n j : ℝ)) = p := by exact_mod_cast hn
  rw [hrewrite]
  calc
    _ ≤ ∑ j, |((m j : ℝ) - n j) * (g j - step * (a j : ℝ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ((m j : ℝ) + n j) * e := by
      refine sum_le_sum fun j _ => ?_
      rw [abs_mul]
      apply (mul_le_mul_of_nonneg_left (happrox j) (abs_nonneg _)).trans
      refine mul_le_mul_of_nonneg_right ?_ he
      simpa using (abs_sub_le (m j : ℝ) 0 (n j : ℝ))
    _ = 2 * p * e := by rw [← sum_mul, sum_add_distrib, hmR, hnR]; ring

/-- Certified lattice enclosures transfer every closed real near-collision into
the corresponding modular band, counting each residue just once. -/
theorem tailCollisionMass_le_cyclic {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (a : J → ℤ) (hw : ∀ j, 0 ≤ w j) (q p : ℕ)
    {step e η : ℝ} (hstep : 0 < step) (he : 0 ≤ e)
    (happrox : ∀ j, |g j - step * (a j : ℝ)| ≤ e) :
    let H := ⌊(η + 2 * p * e) / step⌋
    tailCollisionMass g w p η ≤ cyclicCollisionMass q a w p
      ((Icc (-H) H).image (fun x : ℤ => (x : ZMod q))) := by
  intro H
  unfold tailCollisionMass nearCollisionMass cyclicCollisionMass
  refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
  let b := latticeFrequency a m - latticeFrequency a n
  let x := monomialFrequency g m - monomialFrequency g n
  by_cases h : |x| ≤ η
  · have herror := signed_gap_error_le g a step e happrox he m n p
      (mem_piAntidiag.mp hm).1 (mem_piAntidiag.mp hn).1
    change |x - step * (b : ℝ)| ≤ 2 * p * e at herror
    have hbound : step * |(b : ℝ)| ≤ η + 2 * p * e := by
      rw [← abs_of_pos hstep, ← abs_mul]
      have hsum := abs_sub x (x - step * (b : ℝ))
      rw [sub_sub_cancel] at hsum
      have hs : |x| + |x - step * (b : ℝ)| ≤ η + 2 * p * e := add_le_add h herror
      simpa only [abs_of_pos hstep] using hsum.trans hs
    have hb : |b| ≤ H := by
      apply Int.le_floor.mpr
      rw [Int.cast_abs, le_div_iff₀ hstep, mul_comm]
      exact hbound
    have hmem : (b : ZMod q) ∈ (Icc (-H) H).image (fun c : ℤ => (c : ZMod q)) :=
      mem_image.mpr ⟨b, mem_Icc.mpr (abs_le.mp hb), rfl⟩
    rw [ite_eq_left h, ite_eq_left hmem]
  · rw [ite_eq_right h]
    split_ifs
    · exact mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n)
    · exact le_rfl

/-- If the spread of the lattice sums leaves room for the target band, no modular
hit can be a wrapped lattice difference. -/
theorem cyclicCollisionMass_le_tail_of_no_wrap {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (a : J → ℤ) (hw : ∀ j, 0 ≤ w j) (q p : ℕ) (H lo hi : ℤ)
    {step e : ℝ} (hstep : 0 ≤ step) (he : 0 ≤ e)
    (happrox : ∀ j, |g j - step * (a j : ℝ)| ≤ e) (ha : ∀ j, a j ∈ Set.Icc lo hi)
    (hwrap : (p : ℤ) * (hi - lo) + H < q) :
    cyclicCollisionMass q a w p ((Icc (-H) H).image (fun x : ℤ => (x : ZMod q))) ≤
      tailCollisionMass g w p (step * (H : ℝ) + 2 * p * e) := by
  have hspan (m : J → ℕ) (hm : (∑ j, m j) = p) :
      latticeFrequency a m ∈ Set.Icc ((p : ℤ) * lo) ((p : ℤ) * hi) := by
    have hsum : (∑ j, (m j : ℤ)) = p := by exact_mod_cast hm
    unfold latticeFrequency
    rw [← hsum, sum_mul, sum_mul]
    exact ⟨sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ha j).1 (Int.natCast_nonneg _),
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ha j).2 (Int.natCast_nonneg _)⟩
  unfold tailCollisionMass nearCollisionMass cyclicCollisionMass
  refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
  let b := latticeFrequency a m - latticeFrequency a n
  let x := monomialFrequency g m - monomialFrequency g n
  let R := (Icc (-H) H).image (fun z : ℤ => (z : ZMod q))
  by_cases h : (b : ZMod q) ∈ R
  · obtain ⟨z, hz, heq⟩ := mem_image.mp h
    have hmp := (mem_piAntidiag.mp hm).1
    have hnp := (mem_piAntidiag.mp hn).1
    have hb : |b| ≤ (p : ℤ) * (hi - lo) := by
      apply abs_le.mpr
      constructor
      · dsimp [b]
        linarith [(hspan m hmp).1, (hspan n hnp).2]
      · dsimp [b]
        linarith [(hspan m hmp).2, (hspan n hnp).1]
    have hzabs : |z| ≤ H := abs_le.mpr (mem_Icc.mp hz)
    have hzb : z = b := by
      have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub z b q).mp heq
      apply (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd ?_)).symm
      exact (abs_sub b z).trans_lt ((add_le_add hb hzabs).trans_lt hwrap)
    have hbabs : |(b : ℝ)| ≤ H := by
      rw [← hzb]
      exact_mod_cast hzabs
    have herror := signed_gap_error_le g a step e happrox he m n p hmp hnp
    change |x - step * (b : ℝ)| ≤ 2 * p * e at herror
    have hx : |x| ≤ step * (H : ℝ) + 2 * p * e := by
      have hadd := abs_add_le (step * (b : ℝ)) (x - step * (b : ℝ))
      rw [add_sub_cancel] at hadd
      rw [abs_mul, abs_of_nonneg hstep] at hadd
      exact hadd.trans (add_le_add (mul_le_mul_of_nonneg_left hbabs hstep) herror)
    rw [ite_eq_left h, ite_eq_left hx]
  · rw [ite_eq_right h]
    split_ifs
    · exact mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n)
    · exact le_rfl

open D5.S3.Fourier.FinitePoisson (character character_apply)

private theorem character_weighted_power {J : Type*} [Fintype J] [DecidableEq J]
    {q : ℕ} (ψ : AddChar (ZMod q) ℂ) (a : J → ℤ) (w : J → ℝ) (p : ℕ) :
    (∑ j, (w j : ℂ) * ψ (a j : ZMod q)) ^ p =
      ∑ m ∈ piAntidiag univ p,
        (monomialWeight w m : ℂ) * ψ (latticeFrequency a m : ZMod q) := by
  have hf (b : J → ZMod q) (s : Finset J) : ψ (∑ j ∈ s, b j) = ∏ j ∈ s, ψ (b j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [sum_insert hj, prod_insert hj, ψ.map_add_eq_mul, ih]
  rw [sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun m _ => ?_
  unfold monomialWeight latticeFrequency
  push_cast
  rw [hf]
  simp_rw [mul_pow, prod_mul_distrib, ← nsmul_eq_mul, ψ.map_nsmul_eq_pow]
  ring

private theorem character_conj {q : ℕ} [NeZero q] (k x : ZMod q) :
    starRingEnd ℂ (character k x) = character k (-x) := by
  rw [character_apply, character_apply, mul_neg,
    AddChar.map_neg_eq_inv (ZMod.stdAddChar : AddChar (ZMod q) ℂ) (k * x),
    ZMod.stdAddChar_apply, ← Circle.coe_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle (k * x))).symm

/-- The cyclic band mass is an exact finite Fourier average of the weighted score. -/
theorem cyclicCollisionMass_fourier {J : Type*} [Fintype J] [DecidableEq J]
    (q : ℕ) [NeZero q] (a : J → ℤ) (w : J → ℝ) (p : ℕ) (R : Finset (ZMod q)) :
    (q : ℂ) * (cyclicCollisionMass q a w p R : ℂ) =
      ∑ k : ZMod q, ((‖∑ j, (w j : ℂ) * character k (a j : ZMod q)‖ ^ (2 * p) : ℝ) : ℂ) *
        ∑ y ∈ R, character k (-y) := by
  classical
  let s := piAntidiag (univ : Finset J) p
  let x (m : J → ℕ) : ZMod q := latticeFrequency a m
  let c (m : J → ℕ) : ℂ := monomialWeight w m
  let A (k : ZMod q) := ∑ j, (w j : ℂ) * character k (a j : ZMod q)
  have horth (d : ZMod q) :
      ∑ k : ZMod q, character k d = if d = 0 then (q : ℂ) else 0 := by
    simpa only [character_apply, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar q)
  have hmoment (k : ZMod q) : ((‖A k‖ ^ (2 * p) : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, c m * c n * character k (x m - x n) := by
    have hpow := character_weighted_power (character k) a w p
    change A k ^ p = ∑ m ∈ s, c m * character k (x m) at hpow
    have hconj : starRingEnd ℂ (A k ^ p) =
        ∑ n ∈ s, c n * character k (-x n) := by
      rw [hpow, map_sum]
      exact sum_congr rfl fun n _ => by
        rw [map_mul, character_conj]
        congr 1
        exact Complex.conj_ofReal _
    rw [pow_mul, Complex.sq_norm, Complex.ofReal_pow, ← Complex.mul_conj, mul_pow, ← map_pow,
      hconj, hpow, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [sub_eq_add_neg, (character k).map_add_eq_mul]
    ring
  have hshift (d : ZMod q) :
      (∑ y ∈ R, ∑ k : ZMod q, character k (d - y)) =
        if d ∈ R then (q : ℂ) else 0 := by
    simp only [horth, sub_eq_zero]
    by_cases hd : d ∈ R
    · rw [ite_eq_left hd, sum_eq_single d]
      · simp
      · intro b _ hne
        rw [ite_eq_right hne.symm]
      · exact fun hn => (hn hd).elim
    · rw [ite_eq_right hd]
      refine sum_eq_zero fun y hy => ite_eq_right ?_
      exact fun h => hd (h.symm ▸ hy)
  symm
  calc
    _ = ∑ k : ZMod q, ∑ m ∈ s, ∑ n ∈ s, ∑ y ∈ R,
        c m * c n * character k (x m - x n - y) := by
      refine sum_congr rfl fun k _ => ?_
      change ((‖A k‖ ^ (2 * p) : ℝ) : ℂ) * _ = _
      rw [hmoment, sum_mul]
      refine sum_congr rfl fun m _ => ?_
      rw [sum_mul]
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun y _ => by
        rw [sub_eq_add_neg (x m - x n) y, (character k).map_add_eq_mul]
        ring
    _ = ∑ m ∈ s, ∑ n ∈ s, c m * c n *
        (if x m - x n ∈ R then (q : ℂ) else 0) := by
      rw [sum_comm]
      refine sum_congr rfl fun m _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun n _ => ?_
      rw [sum_comm]
      simp_rw [← mul_sum, hshift]
    _ = _ := by
      unfold cyclicCollisionMass
      push_cast
      rw [mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      change _ = (q : ℂ) * (↑(if x m - x n ∈ R then monomialWeight w m * monomialWeight w n
        else 0 : ℝ) : ℂ)
      split_ifs <;> simp [c] <;> ring

#print axioms tailCollisionMass_le_cyclic
#print axioms cyclicCollisionMass_le_tail_of_no_wrap
#print axioms cyclicCollisionMass_fourier

end D5.S3.Fourier.Concentration.CyclicCollisionCertificate
