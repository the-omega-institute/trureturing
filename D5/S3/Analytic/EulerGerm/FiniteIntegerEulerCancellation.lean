/- GID: D5/S3/Analytic/EulerGerm/FiniteIntegerEulerCancellation
   generality: G
   mirror-B: D5/B/S3/Analytic/EulerGerm/FiniteIntegerEulerCancellation
   mirror-E: none(waiver:symbolic-finite-algebra)
   anchors: []
   utility: none
   digest: Finite integer Euler cancellation with an analytic certificate consumer. -/

import D5.S3.Analytic.EulerGerm.EvaluatedEulerCertificate
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Finite signed monomial extraction and its polynomial-to-analytic certificate bridge. -/

noncomputable section

namespace D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation

open Finset MvPolynomial
open EvaluatedEulerCertificate

variable {J : Type} [Fintype J]

/-- The integer linear polynomial, before analytic parameters are chosen. -/
def linearPolynomial (a : J → ℤ) : MvPolynomial J ℤ :=
  1 + ∑ j, C (a j) * X j

/-- Positive and negative exponents are ordinary natural polynomial powers. -/
def correctionProduct {I : Type} [Fintype I]
    (n : I → J →₀ ℕ) (c : I → ℤ) : MvPolynomial J ℤ :=
  ∏ i, (1 - monomial (n i) 1) ^ (c i).toNat

/-- The finite polynomial error after clearing negative powers. -/
def residual {I : Type} [Fintype I]
    (a : J → ℤ) (n : I → J →₀ ℕ) (c : I → ℤ) : MvPolynomial J ℤ :=
  linearPolynomial a * correctionProduct n c - correctionProduct n (-c)

private theorem square_zero_powers {R : Type*} [CommRing R] (x : R)
    (hx : x * x = 0) (k : ℕ) : (1 - x) ^ k = 1 - (k : R) * x := by
  simpa [Polynomial.derivative_X_pow, sub_eq_add_neg] using
    Polynomial.eval_add_of_sq_eq_zero ((Polynomial.X : Polynomial R) ^ k) 1 (-x)
      (by simpa [pow_two] using hx)

private theorem square_zero_product {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (x : ι → R) (k : ι → ℕ)
    (hx : ∀ i ∈ s, ∀ j ∈ s, x i * x j = 0) :
    (∏ i ∈ s, (1 - x i) ^ k i) = 1 - ∑ i ∈ s, (k i : R) * x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      square_zero_powers _ (hx i (by simp) i (by simp)),
      ih (fun j hj l hl => hx j (by simp [hj]) l (by simp [hl]))]
    have hh : x i * (∑ j ∈ s, (k j : R) * x j) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [mul_left_comm, hx i (by simp) j (by simp [hj]), mul_zero]
    calc
      _ = 1 - ((k i : R) * x i + ∑ j ∈ s, (k j : R) * x j) +
          (k i : R) * (x i * ∑ j ∈ s, (k j : R) * x j) := by ring
      _ = _ := by rw [hh]; ring

omit [Fintype J] in
private theorem cancel_layer (p U V : MvPolynomial J ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hH : p * U - V ∈ idealOfVars J ℤ ^ d)
    (hV : V - 1 ∈ idealOfVars J ℤ) :
    let H := p * U - V
    let s := H.support.filter (fun u => u.degree = d)
    let A := ∏ u ∈ s, (1 - monomial u (1 : ℤ)) ^ (H.coeff u).toNat
    let B := ∏ u ∈ s, (1 - monomial u (1 : ℤ)) ^ (-H.coeff u).toNat
    p * (U * A) - V * B ∈ idealOfVars J ℤ ^ (d + 1) := by
  classical
  dsimp only
  let H := p * U - V
  let s := H.support.filter (fun u => u.degree = d)
  let K := idealOfVars J ℤ ^ (d + 1)
  let q := Ideal.Quotient.mk K
  let x (u : J →₀ ℕ) := q (monomial u 1)
  have hdeg (u) (hu : u ∈ s) : u.degree = d := (Finset.mem_filter.mp hu).2
  have hxmem (u) (hu : u ∈ s) : monomial u (1 : ℤ) ∈ idealOfVars J ℤ ^ d :=
    (monomial_mem_pow_idealOfVars_iff d u (by norm_num)).mpr (hdeg u hu).ge
  have hmul (f g : MvPolynomial J ℤ)
      (hf : f ∈ idealOfVars J ℤ ^ d) (hg : g ∈ idealOfVars J ℤ ^ d) :
      q f * q g = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply (Ideal.pow_le_pow_right (show d + 1 ≤ d + d by omega))
    rw [pow_add]
    exact Ideal.mul_mem_mul hf hg
  have hxx : ∀ u ∈ s, ∀ v ∈ s, x u * x v = 0 :=
    fun u hu v hv => hmul _ _ (hxmem u hu) (hxmem v hv)
  have ha := square_zero_product s x (fun u => (H.coeff u).toNat) hxx
  have hb := square_zero_product s x (fun u => (-H.coeff u).toNat) hxx
  have hc : q (homogeneousComponent d H) =
      ∑ u ∈ s, (H.coeff u : (MvPolynomial J ℤ) ⧸ K) * x u := by
    rw [homogeneousComponent_apply, map_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [show monomial u (H.coeff u) = C (H.coeff u) * monomial u 1 by
      rw [C_mul_monomial, mul_one], map_mul]
    simp [x]
  have hab : (∑ u ∈ s, ((H.coeff u).toNat : (MvPolynomial J ℤ) ⧸ K) * x u) -
      (∑ u ∈ s, ((-H.coeff u).toNat : (MvPolynomial J ℤ) ⧸ K) * x u) =
      q (homogeneousComponent d H) := by
    rw [hc, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← sub_mul]
    congr 1
    have hz : ((H.coeff u).toNat : ℤ) - ((-H.coeff u).toNat : ℤ) = H.coeff u := by omega
    simpa only [Int.cast_sub, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : (MvPolynomial J ℤ) ⧸ K)) hz
  have hHP : q H * (∑ u ∈ s,
      ((H.coeff u).toNat : (MvPolynomial J ℤ) ⧸ K) * x u) = 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro u hu
    rw [mul_left_comm, hmul _ _ hH (hxmem u hu), mul_zero]
  have hVC : (q V - 1) * q (homogeneousComponent d H) = 0 := by
    rw [hc, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro u hu
    rw [mul_left_comm]
    have hz : (q V - 1) * x u = 0 := by
      rw [← map_one q, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      change (V - 1) * monomial u 1 ∈ idealOfVars J ℤ ^ (d + 1)
      rw [show d + 1 = 1 + d by omega, pow_add, pow_one]
      exact Ideal.mul_mem_mul hV (hxmem u hu)
    rw [hz, mul_zero]
  have hrem : q (H - homogeneousComponent d H) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff']
    intro u hu
    rw [coeff_sub, coeff_homogeneousComponent]
    by_cases he : u.degree = d
    · simp [he]
    · simp only [he, ite_false, sub_zero]
      exact (mem_pow_idealOfVars_iff' d H).mp hH u (by omega)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change q (p * (U * _) - V * _) = 0
  simp only [map_sub, map_mul, map_prod, map_pow, map_one]
  change q p * (q U * (∏ u ∈ s, (1 - x u) ^ (H.coeff u).toNat)) -
    q V * (∏ u ∈ s, (1 - x u) ^ (-H.coeff u).toNat) = 0
  rw [ha, hb]
  have hHq : q H = q p * q U - q V := by simp [H]
  rw [map_sub] at hrem
  linear_combination hrem - hHP - hVC - q V * hab -
    (1 - ∑ u ∈ s, ((H.coeff u).toNat : (MvPolynomial J ℤ) ⧸ K) * x u) * hHq

private def finiteProduct (s : Finset (J →₀ ℕ)) (c : (J →₀ ℕ) → ℤ) :
    MvPolynomial J ℤ := ∏ u ∈ s, (1 - monomial u 1) ^ (c u).toNat

omit [Fintype J] in
private theorem product_constant (s : Finset (J →₀ ℕ)) (c : (J →₀ ℕ) → ℤ)
    (hs : ∀ u ∈ s, 1 ≤ u.degree) : constantCoeff (finiteProduct s c) = 1 := by
  classical
  simp only [finiteProduct, map_prod, map_pow, map_sub, map_one]
  apply Finset.prod_eq_one
  intro u hu
  have hu0 : u ≠ 0 := by intro he; simpa [he] using hs u hu
  simp [constantCoeff_monomial, hu0]

omit [Fintype J] in
private theorem constant_one_mem (p : MvPolynomial J ℤ)
    (hp : constantCoeff p = 1) : p - 1 ∈ idealOfVars J ℤ := by
  rw [← pow_one (idealOfVars J ℤ), mem_pow_idealOfVars_iff']
  intro u hu
  have he : u = 0 := (Finsupp.degree_eq_zero_iff u).mp (by omega)
  subst u
  change p.coeff 0 = 1 at hp
  simpa using sub_eq_zero.mpr hp

omit [Fintype J] in
private theorem finite_cancellation (p : MvPolynomial J ℤ)
    (hp : constantCoeff p = 1) (N : ℕ) :
    ∃ (s : Finset (J →₀ ℕ)) (c : (J →₀ ℕ) → ℤ),
      (∀ u ∈ s, 1 ≤ u.degree ∧ u.degree ≤ N) ∧
      p * finiteProduct s c - finiteProduct s (-c) ∈ idealOfVars J ℤ ^ (N + 1) := by
  classical
  induction N with
  | zero =>
    refine ⟨∅, 0, by simp, ?_⟩
    simpa [finiteProduct] using constant_one_mem p hp
  | succ N ih =>
    obtain ⟨s, c, hs, hH⟩ := ih
    let U := finiteProduct s c
    let V := finiteProduct s (-c)
    let H := p * U - V
    let t := H.support.filter (fun u => u.degree = N + 1)
    let c' : (J →₀ ℕ) → ℤ := fun u => if u ∈ s then c u else H.coeff u
    have hst : Disjoint s t := by
      rw [Finset.disjoint_left]
      intro u hus hut
      have := (hs u hus).2
      have := (Finset.mem_filter.mp hut).2
      omega
    have hU : finiteProduct (s ∪ t) c' = U *
        (∏ u ∈ t, (1 - monomial u (1 : ℤ)) ^ (H.coeff u).toNat) := by
      rw [finiteProduct, Finset.prod_union hst]
      congr 1
      · apply Finset.prod_congr rfl
        intro u hu
        simp [c', hu]
      · apply Finset.prod_congr rfl
        intro u hu
        have hn : u ∉ s := fun h => Finset.disjoint_left.mp hst h hu
        simp [c', hn]
    have hV : finiteProduct (s ∪ t) (-c') = V *
        (∏ u ∈ t, (1 - monomial u (1 : ℤ)) ^ (-H.coeff u).toNat) := by
      rw [finiteProduct, Finset.prod_union hst]
      congr 1
      · apply Finset.prod_congr rfl
        intro u hu
        simp [c', hu]
      · apply Finset.prod_congr rfl
        intro u hu
        have hn : u ∉ s := fun h => Finset.disjoint_left.mp hst h hu
        simp [c', hn]
    refine ⟨s ∪ t, c', ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact ⟨(hs u hu).1, (hs u hu).2.trans (Nat.le_succ N)⟩
      · have he := (Finset.mem_filter.mp hu).2
        exact ⟨by omega, he.le⟩
    · rw [hU, hV]
      exact cancel_layer p U V (N + 1) (by omega) hH
        (constant_one_mem V (product_constant s (-c) (fun u hu => (hs u hu).1)))

/-- All positive correction modes through the prescribed total degree. -/
abbrev Mode (J : Type) (N : ℕ) := {u : J →₀ ℕ // 1 ≤ u.degree ∧ u.degree ≤ N}

private def modeSet (N : ℕ) : Finset (J →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le N).subset (fun _ h => h.2) :
    {u : J →₀ ℕ | 1 ≤ u.degree ∧ u.degree ≤ N}.Finite).toFinset

instance (N : ℕ) : Fintype (Mode J N) :=
  Fintype.ofFinset (modeSet N) (by
    intro u
    change u ∈ modeSet N ↔ 1 ≤ u.degree ∧ u.degree ≤ N
    simp [modeSet])

private theorem exact_cancellation (a : J → ℤ) (N : ℕ) :
    ∃ c : Mode J N → ℤ, ∀ u : J →₀ ℕ, u.degree ≤ N →
      (residual a (fun i : Mode J N => i.val) c).coeff u = 0 := by
  classical
  have hp : constantCoeff (linearPolynomial a) = 1 := by simp [linearPolynomial]
  obtain ⟨s, c, hs, hc⟩ := finite_cancellation (linearPolynomial a) hp N
  let c' : (J →₀ ℕ) → ℤ := fun u => if u ∈ s then c u else 0
  have hsub : s ⊆ modeSet N := by
    intro u hu
    simpa only [modeSet, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hs u hu
  have hprod (k : (J →₀ ℕ) → ℤ) (hk : ∀ u ∉ s, k u = 0)
      (hk' : ∀ u ∈ s, k u = c u) :
      correctionProduct (fun i : Mode J N => i.val) (fun i => k i.val) =
        finiteProduct s c := by
    unfold correctionProduct finiteProduct
    simp only
    rw [← Finset.prod_subtype (p := fun u : J →₀ ℕ => 1 ≤ u.degree ∧ u.degree ≤ N)
      (modeSet N) (by intro u; simp [modeSet])
      (fun u => (1 - monomial u (1 : ℤ)) ^ (k u).toNat)]
    calc
      _ = ∏ u ∈ s, (1 - monomial u (1 : ℤ)) ^ (k u).toNat :=
        (Finset.prod_subset hsub (by intro u _ hu; simp [hk u hu])).symm
      _ = _ := Finset.prod_congr rfl (fun u hu => by rw [hk' u hu])
  have hpos := hprod c' (by intro u hu; simp [c', hu]) (by intro u hu; simp [c', hu])
  have hneg : correctionProduct (fun i : Mode J N => i.val) (fun i => -c' i.val) =
      finiteProduct s (-c) := by
    unfold correctionProduct finiteProduct
    simp only
    rw [← Finset.prod_subtype (p := fun u : J →₀ ℕ => 1 ≤ u.degree ∧ u.degree ≤ N)
      (modeSet N) (by intro u; simp [modeSet])
      (fun u => (1 - monomial u (1 : ℤ)) ^ (-c' u).toNat)]
    calc
      _ = ∏ u ∈ s, (1 - monomial u (1 : ℤ)) ^ (-c' u).toNat :=
        (Finset.prod_subset hsub (by intro u _ hu; simp [c', hu])).symm
      _ = _ := Finset.prod_congr rfl (fun u hu => by simp [c', hu])
  refine ⟨fun i => c' i.val, ?_⟩
  intro u hu
  have hh := (mem_pow_idealOfVars_iff' (N + 1)
    (linearPolynomial a * finiteProduct s c - finiteProduct s (-c))).mp hc u (by omega)
  change (linearPolynomial a * correctionProduct (fun i : Mode J N => i.val) (fun i => c' i.val) -
    correctionProduct (fun i : Mode J N => i.val) (fun i => -c' i.val)).coeff u = 0
  rw [hpos, hneg]
  exact hh

/-- The modes in the function-index presentation of the finite cancellation event. -/
abbrev FunctionMode (J : Type) [Fintype J] (N : ℕ) :=
  {u : J → ℕ // 1 ≤ ∑ j, u j ∧ ∑ j, u j ≤ N}

private def modeEquiv (N : ℕ) : Mode J N ≃ FunctionMode J N :=
  Finsupp.equivFunOnFinite.subtypeEquiv (by intro u; simp [Finsupp.degree_eq_sum])

instance (N : ℕ) : Fintype (FunctionMode J N) := Fintype.ofEquiv (Mode J N) (modeEquiv N)

/-- The finite-support index corresponding to an ordinary function on a finite type. -/
def polynomialMode (N : ℕ) (i : FunctionMode J N) : J →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm i.val

private theorem function_cancellation (a : J → ℤ) (N : ℕ) :
    ∃ c : FunctionMode J N → ℤ, ∀ u : J → ℕ, (∑ j, u j) ≤ N →
      (residual a (polynomialMode N) c).coeff (Finsupp.equivFunOnFinite.symm u) = 0 := by
  classical
  obtain ⟨c, hc⟩ := exact_cancellation a N
  let c' : FunctionMode J N → ℤ := fun i => c ((modeEquiv N).symm i)
  have he (k : Mode J N → ℤ) :
      correctionProduct (polynomialMode N) (fun i => k ((modeEquiv N).symm i)) =
        correctionProduct (fun i : Mode J N => i.val) k := by
    unfold correctionProduct
    exact (modeEquiv N).symm.prod_comp
      (fun i => (1 - monomial i.val (1 : ℤ)) ^ (k i).toNat)
  refine ⟨c', ?_⟩
  intro u hu
  have hdeg : (Finsupp.equivFunOnFinite.symm u).degree ≤ N := by
    simpa [Finsupp.degree_eq_sum] using hu
  have hh := hc (Finsupp.equivFunOnFinite.symm u) hdeg
  change (linearPolynomial a * correctionProduct (polynomialMode N) c' -
      correctionProduct (polynomialMode N) (-c')).coeff _ = 0
  rw [he c]
  change (linearPolynomial a * correctionProduct (fun i : Mode J N => i.val) c -
    correctionProduct (polynomialMode N) (fun i => (-c) ((modeEquiv N).symm i))).coeff _ = 0
  rw [he (-c)]
  exact hh

/-- Tail indices are the actual finite support, with no division in evaluation. -/
def tailData {I : Type} [Fintype I]
    (a : J → ℤ) (n : I → J →₀ ℕ) (c : I → ℤ) :
    Data J I (residual a n c).support where
  linear := a
  mode i := n i
  power := c
  tailMode t := t.val
  tailCoeff t := (residual a n c).coeff t.val

private theorem tail_certificate {I : Type} [Fintype I]
    (a : J → ℤ) (n : I → J →₀ ℕ) (c : I → ℤ) :
    (tailData a n c).Certificate := by
  classical
  intro z
  let ev := eval₂Hom (Int.castRingHom ℂ) z
  have hm (u : J →₀ ℕ) : ev (monomial u 1) = monomialValue u z := by
    simp [ev, eval₂_monomial, monomialValue, ← Finsupp.prod_pow]
  have hp (k : I → ℤ) : ev (correctionProduct n k) =
      ∏ i, (1 - monomialValue (n i) z) ^ (k i).toNat := by
    simp [correctionProduct, map_prod, map_pow, map_sub, hm]
  have hl : ev (linearPolynomial a) = 1 + ∑ j, (a j : ℂ) * z j := by
    simp only [linearPolynomial, map_add, map_one, map_sum, map_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [ev, eval₂Hom_C, eval₂Hom_X', Int.coe_castRingHom]
  have ht : ev (residual a n c) = (tailData a n c).tail z := by
    rw [show ev (residual a n c) = (residual a n c).eval₂ (Int.castRingHom ℂ) z from rfl,
      eval₂_eq']
    simp only [Data.tail, tailData, monomialValue]
    exact (Finset.sum_attach _ _).symm
  change (1 + ∑ j, (a j : ℂ) * z j) *
    (∏ i, (1 - monomialValue (n i) z) ^ (c i).toNat) =
    (∏ i, (1 - monomialValue (n i) z) ^ (-c i).toNat) + (tailData a n c).tail z
  rw [← ht]
  have he : ev (residual a n c) =
      ev (linearPolynomial a) * ev (correctionProduct n c) -
        ev (correctionProduct n (-c)) := by simp only [residual, map_sub, map_mul]
  rw [he, hl, hp, hp]
  simp only [Pi.neg_apply]
  ring

/-- Finite integer cancellation, its exact support certificate, and its uniform
analytic consequence. All algebraic choices precede every analytic parameter. -/
theorem finite_integer_euler_cancellation (a : J → ℤ) (N : ℕ) :
    ∃ c : FunctionMode J N → ℤ,
      (∀ u : J → ℕ, (∑ j, u j) ≤ N →
        (residual a (polynomialMode N) c).coeff (Finsupp.equivFunOnFinite.symm u) = 0) ∧
      (tailData a (polynomialMode N) c).Certificate ∧
      (∀ i, 1 ≤ ∑ j, (tailData a (polynomialMode N) c).mode i j ∧
        (∑ j, (tailData a (polynomialMode N) c).mode i j) ≤ N) ∧
      (∀ t, N + 1 ≤ ∑ j, (tailData a (polynomialMode N) c).tailMode t j) ∧
      ∀ (b : J → ℝ) (m ε A : ℝ), 0 < m → (∀ j, m ≤ b j) →
        0 < ε → 0 ≤ A → 2 ≤ (N + 1 : ℝ) * ε * m →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ R : Nat.Primes → ℂ → ℂ,
          (∀ p, AnalyticOnNhd ℂ (R p) {s : ℂ | ε < s.re}) →
          (∀ p s, ε < s.re → ‖R p s‖ ≤ A / (p : ℝ) ^ 2) →
          ∀ p, AnalyticOnNhd ℂ ((tailData a (polynomialMode N) c).corrected b R p)
              {s : ℂ | ε < s.re} ∧
            ∀ s, ε < s.re →
              ‖(tailData a (polynomialMode N) c).corrected b R p s - 1‖ ≤ C / (p : ℝ) ^ 2 := by
  classical
  obtain ⟨c, hc⟩ := function_cancellation a N
  have hcert := tail_certificate a (polynomialMode N) c
  have hmodes (i : FunctionMode J N) :
      1 ≤ ∑ j, (tailData a (polynomialMode N) c).mode i j ∧
      (∑ j, (tailData a (polynomialMode N) c).mode i j) ≤ N := by
    simpa [tailData, polynomialMode] using i.prop
  have ht (t : (residual a (polynomialMode N) c).support) :
      N + 1 ≤ ∑ j, (tailData a (polynomialMode N) c).tailMode t j := by
    by_contra h
    have hle : (∑ j, t.val j) ≤ N := by
      change ¬ N + 1 ≤ ∑ j, t.val j at h
      omega
    have hz := hc t.val hle
    have he : Finsupp.equivFunOnFinite.symm (t.val : J → ℕ) = t.val :=
      Finsupp.equivFunOnFinite.symm_apply_apply t.val
    rw [he] at hz
    exact (mem_support_iff.mp t.prop) hz
  refine ⟨c, hc, hcert, hmodes, ht, ?_⟩
  intro b m ε A hm hb hε hA hcut
  exact evaluated_certificate_uniform (tailData a (polynomialMode N) c) N hcert
    (fun i => (hmodes i).1) ht b m ε A hm hb hε hA hcut

end D5.S3.Analytic.EulerGerm.FiniteIntegerEulerCancellation
