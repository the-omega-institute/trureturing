/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalPrimeExclusion
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalPrimeExclusion
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The algebraic exclusion of spectral primes for the three vertical sections. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSingletNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.FractionRing

/-! The algebraic exclusion of spectral primes for the three vertical sections. -/

open scoped BigOperators
open MvPolynomial

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalPrimeExclusion

noncomputable section

open PeriodicMPSWeightedLineSpecialization

abbrev Roots := MvPolynomial (Fin 4) ℂ

/-- The pairings in order are 01|23, 02|13 and 03|21. -/
def pairing (j : Fin 3) : Equiv.Perm (Fin 4) := Equiv.swap 1 j.succ

private abbrev weight (j : Fin 3) := pairingWeight j.succ

private abbrev root (j : Fin 3) (i : Fin 4) : Roots := X (pairing j i)

private def imbalance (j : Fin 3) : Roots :=
  root j 0 + root j 1 - (root j 2 + root j 3)

/-- The obstruction with the coordinate units omitted. -/
def obstruction (m : ℕ) (j : Fin 3) : Roots :=
  (root j 0 + root j 1) * (root j 2 + root j 3) * imbalance j *
    (root j 0 ^ m - root j 1 ^ m) * (root j 2 ^ m - root j 3 ^ m)

private def binomial (i j : Fin 4) (c : ℂ) : Roots := X i + C c * X j

private abbrev linearCoeff (p : Roots) (i : Fin 4) := p.coeff (Finsupp.single i 1)

private theorem linearCoeff_binomial (i j k : Fin 4) (c : ℂ) :
    linearCoeff (binomial i j c) k = (if i = k then 1 else 0) + (if j = k then c else 0) := by
  simp [linearCoeff, binomial, coeff_X, Finsupp.single_eq_single_iff]

private theorem linearCoeff_imbalance (j : Fin 3) (i : Fin 4) :
    linearCoeff (imbalance j) (pairing j i) = ![(1 : ℂ), 1, -1, -1] i := by
  fin_cases i <;> norm_num [linearCoeff, imbalance, coeff_X,
    Finsupp.single_eq_single_iff, (pairing j).injective.eq_iff]

private theorem linear_irreducible {p : Roots} {i : Fin 4}
    (hh : p.IsHomogeneous 1) (hc : linearCoeff p i = 1) : Irreducible p := by
  have hn : p ≠ 0 := by
    intro h
    simp [linearCoeff, h] at hc
  refine irreducible_of_totalDegree_eq_one (hh.totalDegree hn) ?_
  intro c h
  exact isUnit_iff_dvd_one.mpr (hc ▸ h (Finsupp.single i 1))

private theorem binomial_irreducible {i j : Fin 4} (h : i ≠ j) (c : ℂ) :
    Irreducible (binomial i j c) := by
  refine linear_irreducible (i := i) ?_ ?_
  · exact (isHomogeneous_X ℂ i).add ((isHomogeneous_X ℂ j).C_mul c)
  · rw [linearCoeff_binomial]
    simp [h.symm]

private theorem imbalance_irreducible (j : Fin 3) : Irreducible (imbalance j) := by
  apply linear_irreducible (i := pairing j 0)
  · exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).sub
      ((isHomogeneous_X _ _).add (isHomogeneous_X _ _))
  · rw [linearCoeff_imbalance]
    rfl

private def rootsOfUnity (m : ℕ) : Multiset ℂ :=
  (Polynomial.X ^ m - Polynomial.C (1 : ℂ)).roots

private theorem rootsOfUnity_ne_zero {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : z ∈ rootsOfUnity m) : z ≠ 0 := by
  intro he
  subst z
  rw [rootsOfUnity, Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hm 1),
    Polynomial.IsRoot.def] at hz
  simp [zero_pow hm.ne'] at hz

private theorem pow_sub_pow_factorization (m : ℕ) (hm : 0 < m) (i j : Fin 4) :
    (X i : Roots) ^ m - X j ^ m =
      ((rootsOfUnity m).map (fun z => binomial i j (-z))).prod := by
  let p : Polynomial ℂ := Polynomial.X ^ m - Polynomial.C 1
  have hmonic : p.Monic := Polynomial.monic_X_pow_sub_C 1 hm.ne'
  have hsplit := IsAlgClosed.splits p
  have hprod := hsplit.eq_prod_roots_of_monic hmonic
  have hcard : (rootsOfUnity m).card = m := by
    change p.roots.card = m
    rw [← hsplit.natDegree_eq_card_roots]
    exact Polynomial.natDegree_X_pow_sub_C
  let F := FractionRing Roots
  let ι : Roots →+* F := algebraMap Roots F
  let x : F := ι (X i)
  let y : F := ι (X j)
  have hy : y ≠ 0 := by
    intro h
    apply X_ne_zero (R := ℂ) j
    apply IsFractionRing.injective Roots F
    simpa only [map_zero] using h
  let ev : Polynomial ℂ →+* F := Polynomial.eval₂RingHom (ι.comp C) (x / y)
  have heval := congrArg ev hprod
  change ev p = ev (p.roots.map (fun z => Polynomial.X - Polynomial.C z)).prod at heval
  simp only [map_multiset_prod, Multiset.map_map, Function.comp_apply, p, ev,
    map_sub, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_sub,
    Polynomial.eval₂_C, RingHom.comp_apply, map_one] at heval
  apply IsFractionRing.injective Roots F
  let zs := rootsOfUnity m
  have hscale :
      ∀ l : Multiset ℂ, y ^ l.card * (l.map (fun z => x / y - ι (C z))).prod =
        (l.map (fun z => x - ι (C z) * y)).prod := by
    intro l
    induction l using Multiset.induction_on with
    | empty => simp
    | cons z l ih =>
        simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
        have hz : y * (x / y - ι (C z)) = x - ι (C z) * y := by
          rw [mul_sub, mul_div_cancel₀ _ hy, mul_comm y]
        calc
          _ = (y * (x / y - ι (C z))) *
              (y ^ l.card * (l.map (fun z => x / y - ι (C z))).prod) := by ring
          _ = _ := by rw [hz, ih]
  have hs := hscale zs
  change y ^ (rootsOfUnity m).card * ((rootsOfUnity m).map
    (fun z => x / y - ι (C z))).prod = _ at hs
  rw [hcard] at hs
  change (x / y) ^ m - 1 = ((rootsOfUnity m).map (fun z => x / y - ι (C z))).prod at heval
  rw [← heval, mul_sub, mul_one, div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hy)] at hs
  simpa only [map_sub, map_pow, map_multiset_prod, Multiset.map_map, Function.comp_apply,
    binomial, map_add, map_mul, map_neg, sub_eq_add_neg, neg_mul, x, y] using hs

private inductive Factor (j : Fin 3) : Roots → Prop
  | left (c : ℂ) (hc : c ≠ 0) : Factor j (binomial (pairing j 0) (pairing j 1) c)
  | right (c : ℂ) (hc : c ≠ 0) : Factor j (binomial (pairing j 2) (pairing j 3) c)
  | difference : Factor j (imbalance j)

private theorem Factor.irreducible {j : Fin 3} {g : Roots} (h : Factor j g) :
    Irreducible g := by
  cases h with
  | left c _ => exact binomial_irreducible ((pairing j).injective.ne (by decide)) c
  | right c _ => exact binomial_irreducible ((pairing j).injective.ne (by decide)) c
  | difference => exact imbalance_irreducible j

private theorem prime_dvd_pow_sub_pow {f : Roots} (hf : Prime f) {m : ℕ} (hm : 0 < m)
    (i j : Fin 4) (h : f ∣ (X i : Roots) ^ m - X j ^ m) :
    ∃ c : ℂ, c ≠ 0 ∧ f ∣ binomial i j c := by
  rw [pow_sub_pow_factorization m hm] at h
  have hmember : ∀ factors : Multiset Roots, f ∣ factors.prod →
      ∃ g ∈ factors, f ∣ g := by
    intro factors
    induction factors using Multiset.induction_on with
    | empty =>
        simpa [← isUnit_iff_dvd_one] using hf.not_isUnit
    | cons g factors ih =>
        simp only [Multiset.prod_cons, hf.dvd_mul]
        rintro (hd | hd)
        · exact ⟨g, Multiset.mem_cons_self _ _, hd⟩
        · obtain ⟨g', hg', hd'⟩ := ih hd
          exact ⟨g', Multiset.mem_cons_of_mem hg', hd'⟩
  obtain ⟨g, hg, hd⟩ := hmember _ h
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hg
  exact ⟨-z, neg_ne_zero.mpr (rootsOfUnity_ne_zero hm hz), hd⟩

private theorem associated_factor_of_dvd {m : ℕ} (hm : 0 < m) {j : Fin 3} {f : Roots}
    (hf : Irreducible f) (h : f ∣ obstruction m j) :
    ∃ g, Factor j g ∧ Associated g f := by
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hfactor : ∃ g, Factor j g ∧ f ∣ g := by
    simp only [obstruction, hp.dvd_mul] at h
    rcases h with (((hl | hr) | hd) | hpow) | hpow
    · exact ⟨_, .left 1 one_ne_zero, by simpa [binomial] using hl⟩
    · exact ⟨_, .right 1 one_ne_zero, by simpa [binomial] using hr⟩
    · exact ⟨_, .difference, hd⟩
    · obtain ⟨c, hc, hd⟩ := prime_dvd_pow_sub_pow hp hm _ _ hpow
      exact ⟨_, .left c hc, hd⟩
    · obtain ⟨c, hc, hd⟩ := prime_dvd_pow_sub_pow hp hm _ _ hpow
      exact ⟨_, .right c hc, hd⟩
  obtain ⟨g, hg, hd⟩ := hfactor
  exact ⟨g, hg, (hf.associated_of_dvd hg.irreducible hd).symm⟩

private theorem weight_crosses {j k : Fin 3} (hjk : j ≠ k) :
    weight k (pairing j 0) ≠ weight k (pairing j 1) ∧
      weight k (pairing j 2) ≠ weight k (pairing j 3) := by
  fin_cases j <;> fin_cases k <;> first | contradiction | decide

private theorem width_imbalance (k : Fin 3) :
    weight k 0 ≠ weight k 1 ∨ weight k 0 ≠ weight k 2 := by
  fin_cases k <;> decide

private theorem Factor.width {j k : Fin 3} {g : Roots} (h : Factor j g) (hjk : j ≠ k) :
    ∃ i l, linearCoeff g i ≠ 0 ∧ linearCoeff g l ≠ 0 ∧ weight k i ≠ weight k l := by
  obtain ⟨hl, hr⟩ := weight_crosses hjk
  cases h with
  | left c hc =>
    refine ⟨pairing j 0, pairing j 1, ?_, ?_, hl⟩
    · simp [linearCoeff_binomial, (pairing j).injective.eq_iff]
    · simpa [linearCoeff_binomial, (pairing j).injective.eq_iff] using hc
  | right c hc =>
    refine ⟨pairing j 2, pairing j 3, ?_, ?_, hr⟩
    · simp [linearCoeff_binomial, (pairing j).injective.eq_iff]
    · simpa [linearCoeff_binomial, (pairing j).injective.eq_iff] using hc
  | difference =>
    have hc (i : Fin 4) : linearCoeff (imbalance j) i ≠ 0 := by
      obtain ⟨l, rfl⟩ := (pairing j).surjective i
      rw [linearCoeff_imbalance]
      fin_cases l <;> norm_num
    rcases width_imbalance k with hw | hw
    · exact ⟨0, 1, hc 0, hc 1, hw⟩
    · exact ⟨0, 2, hc 0, hc 2, hw⟩

private theorem scalar_of_associated {g f : Roots} (h : Associated g f) :
    ∃ c : ℂ, c ≠ 0 ∧ f = C c * g := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, hc, he⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  exact ⟨c, hc.ne_zero, by rw [← hu, he, mul_comm]⟩

/-- Two nonzero support coefficients occur in different degrees of the other pairing. -/
theorem obstruction_factor_width {m : ℕ} (hm : 0 < m) {j k : Fin 3} (hjk : j ≠ k)
    {f : Roots} (hf : Irreducible f) (hd : f ∣ obstruction m j) :
    ∃ a b : Fin 4 →₀ ℕ, a ∈ f.support ∧ b ∈ f.support ∧
      Finsupp.weight (weight k) a ≠ Finsupp.weight (weight k) b := by
  obtain ⟨g, hg, hassoc⟩ := associated_factor_of_dvd hm hf hd
  obtain ⟨i, l, hi, hl, hw⟩ := hg.width hjk
  obtain ⟨c, hc, rfl⟩ := scalar_of_associated hassoc
  refine ⟨Finsupp.single i 1, Finsupp.single l 1, ?_, ?_, ?_⟩
  · simpa only [mem_support_iff, coeff_C_mul] using mul_ne_zero hc hi
  · simpa only [mem_support_iff, coeff_C_mul] using mul_ne_zero hc hl
  · simpa only [Finsupp.weight_single, one_nsmul] using hw

private theorem weight_left (j : Fin 3) :
    weight j (pairing j 0) = 1 ∧ weight j (pairing j 1) = 1 := by
  fin_cases j <;> decide

private theorem weight_right (j : Fin 3) :
    weight j (pairing j 2) = 0 ∧ weight j (pairing j 3) = 0 := by
  fin_cases j <;> decide

private theorem binomial_weighted {w : Fin 4 → ℕ} {i j : Fin 4} {d : ℕ}
    (hi : w i = d) (hj : w j = d) (c : ℂ) :
    (binomial i j c).IsWeightedHomogeneous w d := by
  have hi' := isWeightedHomogeneous_X ℂ w i
  have hj' := isWeightedHomogeneous_X ℂ w j
  rw [hi] at hi'
  rw [hj] at hj'
  exact hi'.add (hj'.C_mul c)

private theorem imbalance_not_associated {j k : Fin 3} (hjk : j ≠ k) :
    ¬ Associated (imbalance j) (imbalance k) := by
  intro ha
  obtain ⟨c, _, he⟩ := scalar_of_associated ha
  have atZero (l : Fin 3) : linearCoeff (imbalance l) 0 = 1 := by
    have h : pairing l 0 = 0 := by fin_cases l <;> decide
    rw [← h, linearCoeff_imbalance]
    rfl
  have hc : 1 = c := by
    have h := congrArg (fun p : Roots => linearCoeff p 0) he
    change linearCoeff (imbalance k) 0 = (C c * imbalance j).coeff _ at h
    simpa only [atZero, coeff_C_mul, mul_one] using h
  have hj : linearCoeff (imbalance j) j.succ = 1 := by
    rw [← show pairing j 1 = j.succ from Equiv.swap_apply_left _ _,
      linearCoeff_imbalance]
    rfl
  obtain ⟨i, hi, hki⟩ : ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ pairing k i = j.succ := by
    fin_cases j <;> fin_cases k <;> first
      | contradiction
      | exact ⟨2, Or.inl rfl, by decide⟩
      | exact ⟨3, Or.inr rfl, by decide⟩
  have hk : linearCoeff (imbalance k) j.succ = -1 := by
    rw [← hki, linearCoeff_imbalance]
    rcases hi with rfl | rfl <;> rfl
  have hh := congrArg (fun p : Roots => linearCoeff p j.succ) he
  change linearCoeff (imbalance k) j.succ = (C c * imbalance j).coeff _ at hh
  rw [hk, coeff_C_mul, ← hc, one_mul] at hh
  change (-1 : ℂ) = linearCoeff (imbalance j) j.succ at hh
  rw [hj] at hh
  norm_num at hh

/-- A prime can obstruct at most one of the three sections. -/
theorem no_common_obstruction_factor {m : ℕ} (hm : 0 < m) {j k : Fin 3} (hjk : j ≠ k)
    {f : Roots} (hf : Irreducible f) (hj : f ∣ obstruction m j) (hk : f ∣ obstruction m k) :
    False := by
  have force {a b : Fin 3} (hab : a ≠ b) {g : Roots} (hg : Factor a g)
      (ha : Associated g f) (hb : f ∣ obstruction m b) : g = imbalance a := by
    obtain ⟨u, v, hu, hv, huv⟩ := obstruction_factor_width hm hab.symm hf hb
    obtain ⟨c, _, he⟩ := scalar_of_associated ha
    have impossible {d : ℕ} (hh : g.IsWeightedHomogeneous (weight a) d) : False := by
      have hhf := hh.C_mul c
      rw [← he] at hhf
      exact huv ((hhf (mem_support_iff.mp hu)).trans (hhf (mem_support_iff.mp hv)).symm)
    cases hg with
    | left c hc =>
      exact (impossible (binomial_weighted (weight_left a).1 (weight_left a).2 c)).elim
    | right c hc =>
      exact (impossible (binomial_weighted (weight_right a).1 (weight_right a).2 c)).elim
    | difference => rfl
  obtain ⟨g, hg, ha⟩ := associated_factor_of_dvd hm hf hj
  obtain ⟨g', hg', ha'⟩ := associated_factor_of_dvd hm hf hk
  rw [force hjk hg ha hk] at ha
  rw [force hjk.symm hg' ha' hj] at ha'
  exact imbalance_not_associated hjk (ha.trans ha'.symm)

theorem obstruction_ne_zero {m : ℕ} (hm : 0 < m) (j : Fin 3) : obstruction m j ≠ 0 := by
  have hsum {a b : Fin 4} (h : a ≠ b) : (X a : Roots) + X b ≠ 0 := by
    simpa [binomial] using (binomial_irreducible h 1).ne_zero
  have hpow {a b : Fin 4} (h : a ≠ b) : (X a : Roots) ^ m - X b ^ m ≠ 0 := by
    intro he
    have hc := congrArg (fun p : Roots => p.coeff (Finsupp.single a m)) he
    simp [coeff_X_pow, Finsupp.single_eq_single_iff, hm.ne', h.symm] at hc
  have hl : pairing j 0 ≠ pairing j 1 := (pairing j).injective.ne (by decide)
  have hr : pairing j 2 ≠ pairing j 3 := (pairing j).injective.ne (by decide)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hsum hl) (hsum hr))
    (imbalance_irreducible j).ne_zero) (hpow hl)) (hpow hr)

/-- Pairwise relative primality holds already in the homogeneous polynomial ring. -/
theorem obstruction_isRelPrime {m : ℕ} (hm : 0 < m) {j k : Fin 3} (hjk : j ≠ k) :
    IsRelPrime (obstruction m j) (obstruction m k) := by
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors (obstruction_ne_zero hm j)).mpr
  intro f hj hk hf
  exact no_common_obstruction_factor hm hjk hf.irreducible hj hk

/-- The trace used for projective normalization. -/
def rootSum : Roots := ∑ i : Fin 4, X i

private theorem isRelPrime_localization {S : Type*} [CommRing S] [Algebra Roots S]
    (M : Submonoid Roots) [IsLocalization M S] (hM : M ≤ nonZeroDivisors Roots)
    {a b : Roots} (ha : a ≠ 0) (hab : IsRelPrime a b) :
    IsRelPrime (algebraMap Roots S a) (algebraMap Roots S b) := by
  let ι := algebraMap Roots S
  have hinj : Function.Injective ι := IsLocalization.injective S hM
  have clear {d x : Roots} (h : ι d ∣ ι x) : ∃ s : M, d ∣ x * (s : Roots) := by
    obtain ⟨k, hk⟩ := h
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj M k
    refine ⟨s, n, hinj ?_⟩
    rw [map_mul, map_mul, hk, mul_assoc, hs]
  intro f hfA hfB
  obtain ⟨⟨d, s⟩, hs⟩ := IsLocalization.surj M f
  have hfd : ι d ∣ f := by
    rw [← hs]
    exact (IsLocalization.map_units S s).mul_right_dvd.mpr dvd_rfl
  have hdA := hfd.trans hfA
  have hdB := hfd.trans hfB
  have hunit : ∀ d : Roots, ι d ∣ ι a → ι d ∣ ι b → IsUnit (ι d) := by
    intro d
    induction d using WfDvdMonoid.induction_on_irreducible with
    | zero =>
        intro hd _
        exact (ha (hinj (by simpa using (zero_dvd_iff.mp (by simpa using hd))))).elim
    | unit d hd =>
        exact fun _ _ => hd.map ι
    | mul d q _ hq ih =>
        intro hda hdb
        have hd : ι d ∣ ι (q * d) := by rw [map_mul]; exact dvd_mul_left _ _
        have hq' : ι q ∣ ι (q * d) := by rw [map_mul]; exact dvd_mul_right _ _
        have huD := ih (hd.trans hda) (hd.trans hdb)
        have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
        have huQ : IsUnit (ι q) := by
          by_contra hn
          have pull {x : Roots} (hx : ι q ∣ ι x) : q ∣ x := by
            obtain ⟨t, ht⟩ := clear hx
            rcases hprime.dvd_mul.mp ht with h | h
            · exact h
            · exact (hn (isUnit_of_dvd_unit (map_dvd ι h) (IsLocalization.map_units S t))).elim
          exact hq.not_isUnit (hab (pull (hq'.trans hda)) (pull (hq'.trans hdb)))
        rw [map_mul]
        exact huQ.mul huD
  exact isUnit_of_mul_isUnit_left (hs ▸ hunit d hdA hdB)

/-- Substitute the trace-normalized roots in any localization in which the trace is a unit. -/
def normalizedRoots {S : Type*} [CommRing S] [Algebra Roots S] (trace : Sˣ) :
    Roots →+* S :=
  eval₂Hom ((algebraMap Roots S).comp C) fun i =>
    algebraMap Roots S (X i) * (↑trace⁻¹ : S)

theorem normalizedRoots_rootSum {S : Type*} [CommRing S] [Algebra Roots S]
    (trace : Sˣ) (htrace : (trace : S) = algebraMap Roots S rootSum) :
    normalizedRoots trace rootSum = 1 := by
  rw [rootSum, map_sum]
  simp only [normalizedRoots, eval₂Hom_X', ← Finset.sum_mul]
  rw [← map_sum, ← rootSum, ← htrace, Units.mul_inv]

theorem normalizedRoots_obstruction {S : Type*} [CommRing S] [Algebra Roots S]
    (trace : Sˣ) (m : ℕ) (j : Fin 3) :
    normalizedRoots trace (obstruction m j) =
      algebraMap Roots S (obstruction m j) * ((↑trace⁻¹ : S) ^ (3 + m + m)) := by
  simp only [obstruction, imbalance, map_mul, map_add, map_sub, map_pow,
    normalizedRoots, eval₂Hom_X', mul_pow, ← add_mul, ← sub_mul, pow_add]
  ring

/-- Relative primality persists on the trace-one chart, also after inverting
the coordinates or further nonzero chart denominators. -/
theorem normalized_obstruction_isRelPrime {S : Type*} [CommRing S] [Algebra Roots S]
    (M : Submonoid Roots) [IsLocalization M S] (hM : M ≤ nonZeroDivisors Roots)
    (htrace : rootSum ∈ M) {m : ℕ} (hm : 0 < m) {j k : Fin 3} (hjk : j ≠ k) :
    let trace := (IsLocalization.map_units S (⟨rootSum, htrace⟩ : M)).unit
    IsRelPrime (normalizedRoots trace (obstruction m j)) (normalizedRoots trace (obstruction m k)) := by
  intro trace
  have h := isRelPrime_localization (S := S) M hM (obstruction_ne_zero hm j) (obstruction_isRelPrime hm hjk)
  rw [normalizedRoots_obstruction, normalizedRoots_obstruction]
  intro d hdj hdk
  have hu : IsUnit ((↑trace⁻¹ : S) ^ (3 + m + m)) := trace⁻¹.isUnit.pow _
  rw [mul_comm, hu.dvd_mul_left] at hdj hdk
  exact h hdj hdk

theorem normalized_coordinate_isUnit {S : Type*} [CommRing S] [Algebra Roots S]
    (M : Submonoid Roots) [IsLocalization M S] (trace : Sˣ) {i : Fin 4}
    (hi : (X i : Roots) ∈ M) : IsUnit (normalizedRoots trace (X i)) := by
  rw [normalizedRoots, eval₂Hom_X']
  exact (IsLocalization.map_units S (⟨X i, hi⟩ : M)).mul trace⁻¹.isUnit


section SectionCoefficients

open PeriodicMPSUniformVerticalSection
open PeriodicMPSUniformVerticalBoundaryCoprime (hsymm_isRelPrime_of_boundary_monomial)
open PeriodicMPSUniformVerticalSingletNorm (middlePolynomial hsymm_isRelPrime_middlePolynomial)

abbrev SectionRoots := MvPolynomial (Fin 5) ℂ

private def toSectionPolynomial : SectionRoots ≃ₐ[ℂ] Polynomial Roots :=
  (renameEquiv ℂ (finRotate 5)).trans (finSuccEquiv ℂ 4)

/-- The divided outer determinant in the dimensionless section parameter
`q`, where `p = u + (t-u)q`, with the four roots ordered by the pairing. -/
def outerPolynomial (m : ℕ) (j : Fin 3) : Polynomial Roots :=
  (toSectionPolynomial (outerDividedDet (R := ℂ) m)).map (rename (pairing j)).toRingHom

/-- The actual cubic coefficient of the divided outer determinant. -/
def outerCoefficient (m : ℕ) (j : Fin 3) : Roots := (outerPolynomial m j).coeff 3

private def outerBase (m : ℕ) : Roots :=
  (toSectionPolynomial (outerDividedDet (R := ℂ) m)).coeff 3

private theorem outerCoefficient_eq (m : ℕ) (j : Fin 3) :
    outerCoefficient m j = rename (pairing j) (outerBase m) := by
  simp [outerCoefficient, outerPolynomial, outerBase]

private theorem weight_mapDomain {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin n → ℕ)
    (s : Fin n →₀ ℕ) : Finsupp.weight w (s.mapDomain e) = Finsupp.weight (w ∘ e) s := by
  rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
  symm
  apply Fintype.sum_equiv e
  intro i
  rw [Finsupp.mapDomain_apply_of_injective e.injective]
  rfl

private theorem rename_weighted {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin n → ℕ)
    {p : MvPolynomial (Fin n) ℂ} {d : ℕ} (h : p.IsWeightedHomogeneous (w ∘ e) d) :
    (rename e p).IsWeightedHomogeneous w d := by
  intro s hs
  obtain ⟨t, rfl, ht⟩ := coeff_rename_ne_zero _ _ _ hs
  exact (weight_mapDomain e w t).trans (h ht)

private theorem outerBase_degrees (m : ℕ) {s : Fin 4 →₀ ℕ}
    (hs : (outerBase m).coeff s ≠ 0) :
    s 0 + s 1 = 3 * m + 4 ∧ s 2 + s 3 = 3 * m + 4 := by
  let e := finRotate 5
  change ((finSuccEquiv ℂ 4 (rename e (outerDividedDet (R := ℂ) m))).coeff 3).coeff s ≠ 0 at hs
  rw [finSuccEquiv_coeff_coeff] at hs
  obtain ⟨t, ht, htc⟩ := coeff_rename_ne_zero _ _ _ hs
  have he (i : Fin 4) : e i.castSucc = i.succ := by
    fin_cases i <;> decide
  have hti (i : Fin 4) : t i.castSucc = s i := by
    have h := congrArg (fun a : Fin 5 →₀ ℕ => a (e i.castSucc)) ht
    rwa [Finsupp.mapDomain_apply_of_injective e.injective, he, Finsupp.cons_succ] at h
  have hL := (outerDividedDet_isWeightedHomogeneous (R := ℂ) m 0) htc
  have hR := (outerDividedDet_isWeightedHomogeneous (R := ℂ) m 1) htc
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_five, smul_eq_mul] at hL hR
  change t (0 : Fin 5) * 1 + (t 1 * 1 + (t 2 * 0 + (t 3 * 0 + t 4 * 0))) = _ at hL
  change t (0 : Fin 5) * 0 + t 1 * 0 + t 2 * 1 + t 3 * 1 + t 4 * 0 = _ at hR
  constructor
  · simpa [show t 0 = s 0 from hti 0, show t 1 = s 1 from hti 1] using hL
  · simpa [show t 2 = s 2 from hti 2, show t 3 = s 3 from hti 3] using hR

theorem outerCoefficient_isHomogeneous (m : ℕ) (j : Fin 3) :
    (outerCoefficient m j).IsHomogeneous (6 * m + 8) := by
  rw [outerCoefficient_eq]
  apply IsHomogeneous.rename_isHomogeneous
  intro s hs
  obtain ⟨hl, hr⟩ := outerBase_degrees m hs
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_four, Pi.one_apply, smul_eq_mul, mul_one]
  omega

theorem outerCoefficient_isWeightedHomogeneous (m : ℕ) (j : Fin 3) :
    (outerCoefficient m j).IsWeightedHomogeneous (pairingWeight j.succ) (3 * m + 4) := by
  rw [outerCoefficient_eq]
  apply rename_weighted
  intro s hs
  have hw : weight j ∘ pairing j = ![1, 1, 0, 0] := by
    funext i
    fin_cases i
    · exact (weight_left j).1
    · exact (weight_left j).2
    · exact (weight_right j).1
    · exact (weight_right j).2
  rw [hw, Finsupp.weight_eq_sum, Fin.sum_univ_four]
  simpa using (outerBase_degrees m hs).1

private abbrev Boundary := MvPolynomial (Fin 2) ℂ

private def boundary : Roots →ₐ[ℂ] Boundary := aeval ![X (0 : Fin 2), 0, X 1, 0]

private theorem toSectionPolynomial_X (i : Fin 5) :
    toSectionPolynomial (X i) =
      ![Polynomial.C (X (0 : Fin 4)), Polynomial.C (X 1), Polynomial.C (X 2),
        Polynomial.C (X 3), Polynomial.X] i := by
  simp only [toSectionPolynomial, AlgEquiv.trans_apply, renameEquiv_apply, rename_X]
  fin_cases i
  · exact finSuccEquiv_X_succ (j := (0 : Fin 4))
  · exact finSuccEquiv_X_succ (j := (1 : Fin 4))
  · exact finSuccEquiv_X_succ (j := (2 : Fin 4))
  · exact finSuccEquiv_X_succ (j := (3 : Fin 4))
  · exact finSuccEquiv_X_zero

theorem eval_outerPolynomial (m : ℕ) (j : Fin 3) (q : Roots) :
    (outerPolynomial m j).eval q =
      aeval ![root j 0, root j 1, root j 2, root j 3, q]
        (outerDividedDet (R := ℂ) m) := by
  let ev : Polynomial Roots →ₐ[ℂ] Roots :=
    Polynomial.eval₂AlgHom (rename (pairing j)) q (fun _ => Commute.all _ _)
  have hcomp : ev.comp toSectionPolynomial.toAlgHom =
      aeval ![root j 0, root j 1, root j 2, root j 3, q] := by
    apply algHom_ext
    intro i
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, toSectionPolynomial_X, aeval_X]
    change Polynomial.eval₂ (rename (pairing j)).toRingHom q _ = _
    fin_cases i <;> simp
  rw [outerPolynomial, Polynomial.eval_map]
  exact congrArg (fun f : SectionRoots →ₐ[ℂ] Roots =>
    f (outerDividedDet (R := ℂ) m)) hcomp

private theorem outerBase_boundary (m : ℕ) (hm : 3 ≤ m) :
    boundary (outerBase m) =
      C (-8 * ((m : ℂ) + 2) ^ 2) * (X 0 : Boundary) ^ (3*m+4) * (X 1) ^ (3*m+4) := by
  have hcomp : (Polynomial.mapAlgHom boundary).comp toSectionPolynomial.toAlgHom =
      aeval ![Polynomial.C (X (0 : Fin 2)), 0, Polynomial.C (X 1), 0, Polynomial.X] := by
    apply algHom_ext
    intro i
    fin_cases i <;> simp [toSectionPolynomial_X, boundary]
  have he := congrArg (fun f : SectionRoots →ₐ[ℂ] Polynomial Boundary =>
    f (outerDividedDet (R := ℂ) m)) hcomp
  change (toSectionPolynomial (outerDividedDet (R := ℂ) m)).map boundary.toRingHom =
    aeval ![Polynomial.C (X (0 : Fin 2)), 0, Polynomial.C (X 1), 0, Polynomial.X]
      (outerDividedDet (R := ℂ) m) at he
  rw [outerDividedDet_boundary m hm] at he
  have hc := congrArg (fun p : Polynomial Boundary => p.coeff 3) he
  rw [Polynomial.coeff_map] at hc
  change boundary (outerBase m) = _ at hc
  rw [hc]
  have hq : (Polynomial.X : Polynomial Boundary) * (Polynomial.X - 1) ^ 2 =
      Polynomial.X ^ 3 - Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.X := by
    rw [Polynomial.C_ofNat]
    ring
  rw [mul_assoc _ Polynomial.X, hq]
  let c : Boundary :=
    C (-8 * ((m : ℂ) + 2) ^ 2) * (X 0 : Boundary) ^ (3*m+4) * (X 1) ^ (3*m+4)
  have hconst : Polynomial.C c =
      -8 * ((m : Polynomial Boundary) + 2) ^ 2 *
        (Polynomial.C (X 0) * Polynomial.C (X 1)) ^ (3*m+4) := by
    simp [c, mul_pow, map_ofNat]
    ring
  rw [← hconst, Polynomial.coeff_C_mul]
  change _ = c
  norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X]

private theorem scalar_boundary_ne_zero (m : ℕ) : (-8 : ℂ) * ((m : ℂ) + 2) ^ 2 ≠ 0 := by
  have hm : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hm)

theorem outerCoefficient_ne_zero (m : ℕ) (hm : 3 ≤ m) (j : Fin 3) :
    outerCoefficient m j ≠ 0 := by
  rw [outerCoefficient_eq]
  intro h
  have hb : outerBase m = 0 := rename_injective _ (pairing j).injective (h.trans (map_zero _).symm)
  have hbd := outerBase_boundary m hm
  rw [hb, map_zero] at hbd
  exact (mul_ne_zero (mul_ne_zero
    ((isUnit_iff_ne_zero.mpr (scalar_boundary_ne_zero m)).map C).ne_zero
    (pow_ne_zero _ (X_ne_zero (R := ℂ) (0 : Fin 2))))
    (pow_ne_zero _ (X_ne_zero (R := ℂ) (1 : Fin 2)))) hbd.symm

/-- The complete homogeneous singlet factor on the four roots. -/
def singlet (m : ℕ) : Roots := hsymm (Fin 4) ℂ (m - 2)

/-- The middle factor on the singlet branch, used for `4 ≤ m`. -/
def middle (m : ℕ) : Roots := middlePolynomial ℂ (m - 4)

/-- The same middle polynomial supplies the literal middle factor in each pairing. -/
theorem middle_eq_literal (m : ℕ) (hm : 4 ≤ m) (j : Fin 3) (p : Roots) :
    middle m = PeriodicMPSUniformVerticalMiddle.middleFactor
      (PeriodicMPSUniformVerticalMiddle.sectionB0 (X (pairing j 0)) (X (pairing j 1)))
      (PeriodicMPSUniformVerticalMiddle.sectionB1 (X (pairing j 2)) (X (pairing j 3)) p)
      (m - 2) := by
  have hv : (![root j 0, root j 1, root j 2, root j 3] : Fin 4 → Roots) = X ∘ pairing j := by
    funext i
    fin_cases i <;> rfl
  have h := PeriodicMPSUniformVerticalSingletNorm.aeval_middlePolynomial ℂ
    (root j 0) (root j 1) (root j 2) (root j 3) p (m - 4)
  rw [hv, ← rename_eq_aeval, show m - 4 + 2 = m - 2 by omega] at h
  simpa [middle, middlePolynomial, rename_hsymm] using h

theorem singlet_isRelPrime_middle (m : ℕ) (hm : 4 ≤ m) :
    IsRelPrime (singlet m) (middle m) := hsymm_isRelPrime_middlePolynomial m hm

theorem singlet_three : singlet 3 = rootSum := hsymm_one _ _

theorem singlet_isRelPrime_outerCoefficient (m : ℕ) (hm : 3 ≤ m) (j : Fin 3) :
    IsRelPrime (singlet m) (outerCoefficient m j) := by
  let embed : Roots →ₐ[ℂ] SectionRoots := rename Fin.castSucc
  have hcomp : (aeval ![(X (0 : Fin 2) : Boundary), 0, X 1, 0, 0]).comp embed = boundary := by
    apply algHom_ext
    intro i
    fin_cases i <;> simp [embed, boundary]
  have hrel : IsRelPrime (embed (singlet m)) (embed (outerBase m)) := by
    apply hsymm_isRelPrime_of_boundary_monomial (m - 2) _ 0 _ (scalar_boundary_ne_zero m)
      (3*m+4) (3*m+4)
    simpa only [← AlgHom.comp_apply, hcomp, map_zero] using outerBase_boundary m hm
  have hbase : IsRelPrime (singlet m) (outerBase m) := by
    let project : SectionRoots →ₐ[ℂ] Roots := aeval ![X (0 : Fin 4), X 1, X 2, X 3, 0]
    have hleft : project.comp embed = AlgHom.id ℂ Roots := by
      apply algHom_ext
      intro i
      fin_cases i <;> simp [embed, project]
    intro d hH hA
    have hd := (hrel (map_dvd embed hH) (map_dvd embed hA)).map project
    simpa only [← AlgHom.comp_apply, hleft, AlgHom.id_apply] using hd
  have hrename : rename (pairing j) (singlet m) = singlet m :=
    rename_hsymm (Fin 4) ℂ (m - 2) (pairing j)
  rw [outerCoefficient_eq, ← hrename]
  intro d hH hA
  let back : Roots →ₐ[ℂ] Roots := rename (pairing j).symm
  have hleft : back.comp (rename (pairing j)) = AlgHom.id ℂ Roots := by
    apply algHom_ext
    intro i
    simp [back]
  have hd := hbase
    (by simpa only [← AlgHom.comp_apply, hleft, AlgHom.id_apply] using map_dvd back hH)
    (by simpa only [← AlgHom.comp_apply, hleft, AlgHom.id_apply] using map_dvd back hA)
  have hright : (rename (pairing j)).comp back = AlgHom.id ℂ Roots := by
    apply algHom_ext
    intro i
    simp [back]
  simpa only [← AlgHom.comp_apply, hright, AlgHom.id_apply] using hd.map (rename (pairing j))


private theorem outerCoefficient_dvd {m : ℕ} {j : Fin 3} {f : Roots}
    (h : Polynomial.C f ∣ outerPolynomial m j) : f ∣ outerCoefficient m j := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g.coeff 3, by rw [outerCoefficient, hg, Polynomial.coeff_C_mul]⟩

/-- The implication supplied by section rank failure. For each unobstructed
pairing, the outer determinant vanishes identically modulo `f`, or the
singlet and middle spectral factors both vanish modulo `f` on the branch
`m ≥ 4`. At `m = 3` the singlet factor is the chart unit `rootSum`. -/
def SectionRankImplication (m : ℕ) (f : Roots) : Prop :=
  ∀ j : Fin 3, ¬ f ∣ obstruction m j →
    Polynomial.C f ∣ outerPolynomial m j ∨
      (4 ≤ m ∧ f ∣ singlet m ∧ f ∣ middle m)

theorem not_dvd_singlet_of_sectionRankImplication {m : ℕ} (hm : 3 ≤ m)
    {f : Roots} (hf : Irreducible f) (htrace : ¬ f ∣ rootSum)
    (hrank : SectionRankImplication m f) : ¬ f ∣ singlet m := by
  intro hH
  have hlarge : 4 ≤ m := by
    by_contra h
    obtain rfl : m = 3 := by omega
    exact htrace (singlet_three ▸ hH)
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, ¬ f ∣ obstruction m j := by
    by_cases h : f ∣ obstruction m 0
    · exact ⟨1, no_common_obstruction_factor (by omega) (by decide : (0 : Fin 3) ≠ 1) hf h⟩
    · exact ⟨0, h⟩
  rcases hrank j hj with hout | ⟨_, _, hmid⟩
  · exact hf.not_isUnit (singlet_isRelPrime_outerCoefficient m hm j hH (outerCoefficient_dvd hout))
  · exact hf.not_isUnit (singlet_isRelPrime_middle m hlarge hH hmid)

/-- A prime surviving the section implications is a coordinate prime.
Coordinates are units on the nonzero-root chart. -/
theorem associated_coordinate_of_sectionRankImplication {m : ℕ} (hm : 3 ≤ m)
    {f : Roots} (hf : Irreducible f) (htrace : ¬ f ∣ rootSum)
    (hrank : SectionRankImplication m f) : ∃ i : Fin 4, Associated f (X i) := by
  have hH := not_dvd_singlet_of_sectionRankImplication hm hf htrace hrank
  have hgood (j : Fin 3) (hj : ¬ f ∣ obstruction m j) :
      f ∣ outerCoefficient m j := by
    rcases hrank j hj with h | ⟨_, hd, _⟩
    · exact outerCoefficient_dvd h
    · exact (hH hd).elim
  have hnone (j : Fin 3) : ¬ f ∣ obstruction m j := by
    intro hj
    let k := j + 1
    have hjk : j ≠ k := by fin_cases j <;> decide
    have hk : ¬ f ∣ obstruction m k := no_common_obstruction_factor (by omega) hjk hf hj
    obtain ⟨d, hd⟩ := isWeightedHomogeneous_of_dvd (outerCoefficient_ne_zero m hm k)
      (outerCoefficient_isWeightedHomogeneous m k) (hgood k hk)
    obtain ⟨a, b, ha, hb, hw⟩ := obstruction_factor_width (by omega) hjk hf hj
    exact hw ((hd (mem_support_iff.mp ha)).trans (hd (mem_support_iff.mp hb)).symm)
  have hdata (j : Fin 3) :
      outerCoefficient m j ≠ 0 ∧ (outerCoefficient m j).IsHomogeneous (6 * m + 8) ∧
        (outerCoefficient m j).IsWeightedHomogeneous (pairingWeight j.succ) (3 * m + 4) ∧
        f ∣ outerCoefficient m j := ⟨outerCoefficient_ne_zero m hm j,
    outerCoefficient_isHomogeneous m j, outerCoefficient_isWeightedHomogeneous m j,
    hgood j (hnone j)⟩
  exact associated_X_of_irreducible_common_pairing_dvd hf (hdata 0) (hdata 1) (hdata 2)

theorem no_noncoordinate_prime_of_sectionRankImplication {m : ℕ} (hm : 3 ≤ m)
    {f : Roots} (hf : Irreducible f) (htrace : ¬ f ∣ rootSum)
    (hcoord : ∀ i : Fin 4, ¬ Associated f (X i))
    (hrank : SectionRankImplication m f) : False := by
  obtain ⟨i, hi⟩ := associated_coordinate_of_sectionRankImplication hm hf htrace hrank
  exact hcoord i hi

end SectionCoefficients

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalPrimeExclusion
