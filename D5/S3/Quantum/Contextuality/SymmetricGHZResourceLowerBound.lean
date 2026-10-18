/- GID: D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Symmetric complete-function lifts require a middle binomial layer of qubits. -/

/-
   result: proof_shape: content; escape_witness: finite_lower_bound
   admission_basis: open-problem-resolution (#16724; Proved)
   Direct frozen dependencies (declaration statement_id):
     D5/S1/Words/AssociatedMersenne/SingleRunDegrees
       D5.S1.Words.AssociatedMersenne.SingleRunDegrees.singleRun
       sha256:9e9db382bf4fee85c608a273c94cf133db308f9d86cd77d828016690795f632e
     D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder
       D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.populationGenerating
       sha256:bf54f64a19821ffb353e4fc3c80dbd9613d01bcfa4524bcf80184ae12ca4fe92
     D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder
       D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.populationGenerating.eq_1
       sha256:db1935dc803e988d2d894d951baf4af478df2a502c98aea31b500fe5376614fc
     D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound
       D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity
       sha256:a7a19c8a4a406f91de04d115dea1061ce40c06361d791db009d98520acb2b6f7

   layer contains the literal Odd-cardinality parity expression; the proof uses
   SparseLiteralParityReadLowerBound.parity through parity_eq_owner.
   Signs use Int.negOnePow at the integer-cast filtered cardinality.
   Threshold inputs use SingleRunDegrees.singleRun, and signed layer generating
   polynomials use LorentzLowDegreeCoefficientRemainder.populationGenerating.
   The definitions layer, csf, ComputesSym, qubits and claim express the source
   model, with no constant term in ComputesSym. Hamming weight uses hammingDist
   against the all-false input. The argument is symbolic and universally quantified.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16852

   Definitions (direct consumers):
   ComputesSym: consumers: claim, claim_of_finiteClaim, finite_lower_bound, middle_layer_obstruction, qubits_pos, result.
   certificate: consumers: certificate_coeff, certificate_generating, certificate_layer, certificate_odd_pairing, certificate_signedLayer, certificate_sum, middle_layer_obstruction.
   claim: consumers: claim_of_finiteClaim, result.
   csf: consumers: ComputesSym, csf_weight, middle_layer_obstruction, qubits_pos.
   layer: consumers: ComputesSym, certificate_layer, layer_signed, middle_layer_obstruction, qubits_pos.
   qubits: consumers: claim, claim_of_finiteClaim, finite_lower_bound, qubits_pos.
   signedLayer: consumers: certificate_layer, certificate_signedLayer, layerPolynomial_coeff, layer_signed, weightPolynomial_coeff.

   Declarations:
   certificate_coeff: proof_shape: bind-only;
     escape_witness: none;
     consumers: certificate_signedLayer;
     Direct frozen dependencies: none.
   certificate_generating: proof_shape: bind-only;
     escape_witness: none;
     consumers: certificate_coeff;
     Direct frozen dependencies: none.
   certificate_layer: proof_shape: bind-only;
     escape_witness: none;
     consumers: middle_layer_obstruction;
     Direct frozen dependencies: singleRun, populationGenerating, eq_1, parity.
   certificate_odd_pairing: proof_shape: bind-only;
     escape_witness: none;
     consumers: middle_layer_obstruction;
     Direct frozen dependencies: none.
   certificate_signedLayer: proof_shape: bind-only;
     escape_witness: none;
     consumers: certificate_layer;
     Direct frozen dependencies: singleRun, populationGenerating, eq_1.
   certificate_sum: proof_shape: bind-only;
     escape_witness: none;
     consumers: certificate_layer;
     Direct frozen dependencies: none.
   character_prod: proof_shape: bind-only;
     escape_witness: none;
     consumers: layerPolynomial_expand;
     Direct frozen dependencies: none.
   choose_le_of_middle: proof_shape: bind-only;
     escape_witness: none;
     consumers: finite_lower_bound;
     Direct frozen dependencies: none.
   choose_power_lower: proof_shape: bind-only;
     escape_witness: none;
     consumers: claim_of_finiteClaim;
     Direct frozen dependencies: none.
   claim_of_finiteClaim: proof_shape: bind-only;
     escape_witness: none;
     consumers: result;
     Direct frozen dependencies: singleRun.
   csf_weight: proof_shape: bind-only;
     escape_witness: none;
     consumers: middle_layer_obstruction, qubits_pos;
     Direct frozen dependencies: none.
   finite_lower_bound: proof_shape: content;
     escape_witness: middle_layer_obstruction;
     consumers: result;
     Direct frozen dependencies: singleRun, populationGenerating, eq_1, parity.
   hammingDist_singleRun: proof_shape: bind-only;
     escape_witness: none;
     consumers: certificate_signedLayer, middle_layer_obstruction, qubits_pos;
     Direct frozen dependencies: singleRun.
   layerPolynomial_coeff: proof_shape: bind-only;
     escape_witness: none;
     consumers: weightPolynomial_coeff;
     Direct frozen dependencies: populationGenerating, eq_1.
   layerPolynomial_expand: proof_shape: bind-only;
     escape_witness: none;
     consumers: layerPolynomial_coeff;
     Direct frozen dependencies: populationGenerating, eq_1.
   layerPolynomial_weight: proof_shape: bind-only;
     escape_witness: none;
     consumers: weightPolynomial_coeff;
     Direct frozen dependencies: populationGenerating.
   layer_signed: proof_shape: bind-only;
     escape_witness: none;
     consumers: certificate_layer;
     Direct frozen dependencies: parity.
   middle_layer_obstruction: proof_shape: content;
     escape_witness: middle_layer_obstruction;
     consumers: finite_lower_bound;
     Direct frozen dependencies: singleRun, populationGenerating, eq_1, parity.
   parity_character: proof_shape: bind-only;
     escape_witness: none;
     consumers: layer_signed;
     Direct frozen dependencies: parity.
   parity_eq_owner: proof_shape: bind-only;
     escape_witness: none;
     consumers: parity_character;
     Direct frozen dependencies: parity.
   qubits_pos: proof_shape: bind-only;
     escape_witness: none;
     consumers: claim_of_finiteClaim;
     Direct frozen dependencies: singleRun.
   result: proof_shape: content;
     escape_witness: finite_lower_bound;
     consumers: none;
     Direct frozen dependencies: singleRun, populationGenerating, eq_1, parity.
   weightPolynomial_coeff: proof_shape: bind-only;
     escape_witness: none;
     consumers: certificate_signedLayer;
     Direct frozen dependencies: populationGenerating, eq_1.
-/

import D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
import D5.S1.Words.AssociatedMersenne.SingleRunDegrees
import D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Words.AssociatedMersenne.SingleRunDegrees
open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

open scoped BigOperators
open Finset Polynomial
namespace D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound
noncomputable section

variable {n : ℕ}

def layer (n i : ℕ) (x : Fin n → Bool) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = i), (if Odd ((S.filter (fun l => x l = true)).card) then (1 : ℤ) else 0)

def csf (n k : ℕ) (x : Fin n → Bool) : ℤ :=
  (((Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => S.card = k ∧ ∀ l ∈ S, x l = true)).card : ℤ) % 2

def ComputesSym (n k : ℕ) (T : Finset ℕ) (a : ℕ → ℝ) : Prop :=
  (∀ i ∈ T, 1 ≤ i ∧ i ≤ n) ∧ ∀ x : Fin n → Bool, ∃ z : ℤ,
    (∑ i ∈ T, a i * (layer n i x : ℝ)) = z ∧ z % 2 = csf n k x

def qubits (n : ℕ) (T : Finset ℕ) : ℕ := ∑ i ∈ T, n.choose i

def claim : Prop := ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
  ∀ n : ℕ, N ≤ n → ∀ (T : Finset ℕ) (a : ℕ → ℝ), ComputesSym n k T a →
    c * (n : ℝ) ^ (((k / 2 : ℕ) : ℤ) - 1) ≤ (qubits n T : ℝ)


open Finset Polynomial

private def signedLayer (n i : ℕ) (x : Fin n → Bool) : ℤ :=
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card = i), (Int.negOnePow ((S.filter (fun l => x l = true)).card : ℤ) : ℤ)

private theorem csf_weight (k : ℕ) (x : Fin n → Bool) :
    csf n k x = (Nat.choose (hammingDist x (fun _ => false)) k : ℤ) % 2 := by
  have h : (univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ ∀ l ∈ S, x l = true) = ((univ : Finset (Fin n)).filter (fun l => x l = true)).powersetCard k := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_iff]
    aesop
  simp only [csf, h, card_powersetCard, hammingDist, Bool.not_eq_false]

private theorem parity_eq_owner {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    (if Odd ((S.filter (fun l => x l = true)).card) then (1 : ℤ) else 0) =
      (D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity
        (fun l => decide (l ∈ S ∧ x l = true))).toNat := by
  have hsum : (∑ l : Fin n, (decide (l ∈ S ∧ x l = true)).toNat) =
      (S.filter (fun l => x l = true)).card := by
    have he : ∀ l : Fin n, (decide (l ∈ S ∧ x l = true)).toNat =
        if l ∈ S ∧ x l = true then 1 else 0 := by
      intro l
      by_cases h : l ∈ S ∧ x l = true <;> simp [h]
    simp only [he, sum_boole]
    apply congrArg Finset.card
    ext l
    simp
  simp only [D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity, hsum]
  by_cases h : Odd ((S.filter (fun l => x l = true)).card)
  · simp [h, Nat.odd_iff.mp h]
  · simp [h, (Nat.odd_iff).not.mp h]

private theorem parity_character (S : Finset (Fin n)) (x : Fin n → Bool) :
    2 * (if Odd ((S.filter (fun l => x l = true)).card) then (1 : ℤ) else 0) = 1 - (Int.negOnePow ((S.filter (fun l => x l = true)).card : ℤ) : ℤ) := by
  rw [parity_eq_owner]
  cases hp : D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity
      (fun l => decide (l ∈ S ∧ x l = true)) with
  | false =>
    have he : Even ((S.filter (fun l => x l = true)).card) := by
      by_contra hn
      have ho := Nat.not_even_iff_odd.mp hn
      have h := parity_eq_owner S x
      rw [hp] at h
      simp [ho] at h
    simp [Int.coe_negOnePow_natCast, he.neg_one_pow]
  | true =>
    have ho : Odd ((S.filter (fun l => x l = true)).card) := by
      by_contra hn
      have h := parity_eq_owner S x
      rw [hp] at h
      simp [hn] at h
    simp [Int.coe_negOnePow_natCast, ho.neg_one_pow]

private theorem layer_signed (i : ℕ) (x : Fin n → Bool) :
    2 * layer n i x = (n.choose i : ℤ) - signedLayer n i x := by
  have h : ((univ : Finset (Fin n)).powersetCard i) =
      (univ : Finset (Finset (Fin n))).filter (fun S => S.card = i) := by
    exact (Finset.univ_filter_card_eq (Fin n) i).symm
  have hc : ((univ : Finset (Finset (Fin n))).filter (fun S => S.card = i)).card =
      n.choose i := by rw [← h, card_powersetCard]; simp
  simp only [layer, signedLayer, mul_sum, parity_character, sum_sub_distrib, sum_const,
    nsmul_eq_mul, mul_one, hc]

private theorem hammingDist_singleRun {w : ℕ} (hw : w ≤ n) : hammingDist (singleRun n w) (fun _ => false) = w := by
  simp only [hammingDist, singleRun, Bool.not_eq_false, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right hw]

private theorem character_prod (S : Finset (Fin n)) (x : Fin n → Bool) :
    (Int.negOnePow ((S.filter (fun l => x l = true)).card : ℤ) : ℤ) = ∏ l ∈ S, (if x l = true then (-1 : ℤ) else 1) := by
  simp [Int.coe_negOnePow_natCast, prod_ite]

private theorem layerPolynomial_expand (x : Fin n → Bool) :
    populationGenerating n (fun l => if x l = true then (-1 : ℝ) else 1) = ∑ S : Finset (Fin n), C ((Int.negOnePow ((S.filter (fun l => x l = true)).card : ℤ) : ℤ) : ℂ) * X ^ S.card := by
  rw [populationGenerating, prod_one_add, powerset_univ]
  apply sum_congr rfl
  intro S _
  rw [prod_mul_distrib, prod_const, ← map_prod, character_prod]
  congr 2
  simp only [Int.cast_prod]
  apply prod_congr rfl
  intro l _
  split_ifs <;> norm_num

private theorem layerPolynomial_weight (x : Fin n → Bool) :
    populationGenerating n (fun l => if x l = true then (-1 : ℝ) else 1) = (1 - X) ^ hammingDist x (fun _ => false) * (1 + X) ^ (n - hammingDist x (fun _ => false)) := by
  have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun l => x l = true)
  simp only [card_univ, Fintype.card_fin] at hc
  have hneg : ((univ : Finset (Fin n)).filter (fun l => ¬ x l = true)).card =
      n - hammingDist x (fun _ => false) := by simp only [hammingDist, Bool.not_eq_false]; omega
  calc
    populationGenerating n (fun l => if x l = true then (-1 : ℝ) else 1) = ∏ l : Fin n, (if x l = true then (1 - X : ℂ[X]) else 1 + X) := by
      unfold populationGenerating
      apply prod_congr rfl
      intro l _
      split_ifs with h <;> simp [h, sub_eq_add_neg]
    _ = _ := by rw [prod_ite, prod_const, prod_const, hneg]; simp only [hammingDist, Bool.not_eq_false]

private theorem layerPolynomial_coeff (i : ℕ) (x : Fin n → Bool) :
    (populationGenerating n (fun l => if x l = true then (-1 : ℝ) else 1)).coeff i = (signedLayer n i x : ℂ) := by
  rw [layerPolynomial_expand]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, signedLayer, sum_filter, eq_comm, Int.cast_sum, Int.cast_ite, Int.cast_zero]

private def certificate (m u : ℕ) : ℤ := (-1) ^ (m - u) * m.choose u

private theorem certificate_sum {m : ℕ} (hm : 1 ≤ m) :
    ∑ u ∈ range (m + 1), certificate m u = 0 := by
  calc
    _ = ∑ u ∈ range (m + 1), (-1 : ℤ) ^ u * m.choose u := by
      rw [← sum_range_reflect (fun u => (-1 : ℤ) ^ u * m.choose u) (m + 1)]
      apply sum_congr rfl
      intro u hu
      simp only [certificate, Nat.add_sub_cancel]
      rw [Nat.choose_symm (by have := mem_range.mp hu; omega)]
    _ = 0 := Int.alternating_sum_range_choose_of_ne (by omega)

private theorem certificate_generating {n m r : ℕ} (hn : 2 * m + r ≤ n) :
    (∑ u ∈ range (m + 1), C (certificate m u : ℂ) * ((1 - X) ^ (2 * u + r) * (1 + X) ^ (n - (2 * u + r)))) =
    C ((-4 : ℂ) ^ m) * (X ^ m * ((1 - X) ^ r * (1 + X) ^ (n - (2 * m + r)))) := by
  have he : ∀ u ∈ range (m + 1), n - (2 * u + r) = 2 * (m - u) + (n - (2 * m + r)) := by
    intro u hu
    have := mem_range.mp hu
    omega
  calc
    _ = ((1 - X) ^ r * (1 + X) ^ (n - (2 * m + r))) *
        ∑ u ∈ range (m + 1), ((1 - X) ^ 2) ^ u * (-((1 + X) ^ 2)) ^ (m - u) *
          (m.choose u : ℂ[X]) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro u hu
      simp only [certificate, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, map_mul, map_pow, map_neg, map_one,
        map_natCast, he u hu, pow_add, pow_mul, neg_pow ((1 + X : ℂ[X]) ^ 2)]
      ring
    _ = _ := by
      rw [← add_pow]
      have hx : ((1 - X) ^ 2 + -((1 + X) ^ 2) : ℂ[X]) = C (-4) * X := by
        simp only [map_neg, map_ofNat]
        ring
      rw [hx, mul_pow, ← map_pow]
      ring

private theorem weightPolynomial_coeff (i : ℕ) (x : Fin n → Bool) :
    ((1 - X : ℂ[X]) ^ hammingDist x (fun _ => false) * (1 + X) ^ (n - hammingDist x (fun _ => false))).coeff i = (signedLayer n i x : ℂ) := by
  rw [← layerPolynomial_coeff, layerPolynomial_weight]

private theorem certificate_coeff {n m r j : ℕ} (hn : 2 * m + r ≤ n)
    (hj : j < m ∨ n - m < j) :
    ∑ u ∈ range (m + 1), (certificate m u : ℂ) * (((1 - X : ℂ[X]) ^ (2 * u + r) * (1 + X) ^ (n - (2 * u + r))).coeff j) = 0 := by
  have h := congrArg (fun p : ℂ[X] => p.coeff j) (certificate_generating hn)
  simp only [finsetSum_coeff, coeff_C_mul] at h
  rw [h]
  rcases hj with hj | hj
  · rw [coeff_X_pow_mul', if_neg (by omega : ¬m ≤ j), mul_zero]
  · have hminus : (1 - X : ℂ[X]).natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    have hplus : (1 + X : ℂ[X]).natDegree ≤ 1 := by
      exact (natDegree_add_le _ _).trans (by simp)
    have hd : (X ^ m * ((1 - X : ℂ[X]) ^ r * (1 + X) ^ (n - (2 * m + r)))).natDegree ≤ n - m := by
      have h1 := natDegree_pow_le_of_le r hminus
      have h2 := natDegree_pow_le_of_le (n - (2 * m + r)) hplus
      have h3 := natDegree_mul_le_of_le h1 h2
      have h4 := natDegree_mul_le_of_le (natDegree_X_pow_le m : (X ^ m : ℂ[X]).natDegree ≤ m) h3
      exact h4.trans (by omega)
    rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt hj), mul_zero]

private theorem certificate_signedLayer {n m r j : ℕ} (hn : 2 * m + r ≤ n)
    (hj : j < m ∨ n - m < j) :
    ∑ u ∈ range (m + 1), certificate m u * signedLayer n j (singleRun n (2 * u + r)) = 0 := by
  have hc := certificate_coeff hn hj
  have he : (∑ u ∈ range (m + 1), (certificate m u : ℂ) *
      (signedLayer n j (singleRun n (2 * u + r)) : ℂ)) = 0 := by
    convert hc using 1
    apply sum_congr rfl
    intro u hu
    have hw : 2 * u + r ≤ n := by have := mem_range.mp hu; omega
    rw [← weightPolynomial_coeff, hammingDist_singleRun hw]
  exact_mod_cast he

private theorem certificate_layer {n m r j : ℕ} (hm : 1 ≤ m) (hn : 2 * m + r ≤ n)
    (hj : j < m ∨ n - m < j) :
    ∑ u ∈ range (m + 1), certificate m u * layer n j (singleRun n (2 * u + r)) = 0 := by
  have hs := certificate_signedLayer hn hj
  have hd := certificate_sum hm
  have he : 2 * (∑ u ∈ range (m + 1), certificate m u *
      layer n j (singleRun n (2 * u + r))) =
      (∑ u ∈ range (m + 1), certificate m u) * (n.choose j : ℤ) -
      ∑ u ∈ range (m + 1), certificate m u * signedLayer n j (singleRun n (2 * u + r)) := by
    rw [mul_sum, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    have h := layer_signed j (singleRun n (2 * u + r))
    linear_combination (certificate m u) * h
  rw [hd, hs] at he
  omega

private theorem certificate_odd_pairing {m : ℕ} (z : ℕ → ℤ)
    (heven : ∀ u ∈ range m, z u % 2 = 0) (hodd : z m % 2 = 1) :
    (∑ u ∈ range (m + 1), certificate m u * z u) % 2 = 1 := by
  have hd : (2 : ℤ) ∣ ∑ u ∈ range m, certificate m u * z u := by
    apply dvd_sum
    intro u hu
    exact dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr (heven u hu)) _
  have hself : certificate m m = 1 := by simp [certificate]
  rw [sum_range_succ, hself, one_mul, Int.add_emod, Int.emod_eq_zero_of_dvd hd,
    zero_add, hodd]
  norm_num

private theorem middle_layer_obstruction {n k : ℕ} {T : Finset ℕ} {a : ℕ → ℝ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (h : ComputesSym n k T a) :
    ∃ j ∈ T, k / 2 ≤ j ∧ j ≤ n - k / 2 := by
  let m := k / 2
  let r := k - 2 * m
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hkr : 2 * m + r = k := by dsimp [r, m]; omega
  have hn : 2 * m + r ≤ n := by
    exact le_of_eq_of_le hkr hkn
  by_contra hmid
  have hout : ∀ j ∈ T, j < m ∨ n - m < j := by
    intro j hj
    by_cases hjm : j < m
    · exact Or.inl hjm
    · right
      by_contra hjn
      apply hmid
      exact ⟨j, hj, by dsimp [m] at *; omega, by dsimp [m] at *; omega⟩
  let z (u : ℕ) : ℤ := Classical.choose (h.2 (singleRun n (2 * u + r)))
  have hz (u : ℕ) : (∑ i ∈ T, a i * (layer n i (singleRun n (2 * u + r)) : ℝ)) =
      (z u : ℝ) := (Classical.choose_spec (h.2 (singleRun n (2 * u + r)))).1
  have hp (u : ℕ) : z u % 2 = csf n k (singleRun n (2 * u + r)) :=
    (Classical.choose_spec (h.2 (singleRun n (2 * u + r)))).2
  have heven : ∀ u ∈ range m, z u % 2 = 0 := by
    intro u hu
    have hu' := mem_range.mp hu
    have hw : 2 * u + r ≤ n := by omega
    have hwk : 2 * u + r < k := by omega
    rw [hp, csf_weight, hammingDist_singleRun hw, Nat.choose_eq_zero_of_lt hwk]
    norm_num
  have hodd : z m % 2 = 1 := by
    rw [hp, hkr, csf_weight, hammingDist_singleRun hkn, Nat.choose_self]
    norm_num
  have hzeroR : (∑ u ∈ range (m + 1), (certificate m u : ℝ) * (z u : ℝ)) = 0 := by
    simp_rw [← hz, mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro j hj
    have hjzero : (∑ u ∈ range (m + 1), (certificate m u : ℝ) *
        (layer n j (singleRun n (2 * u + r)) : ℝ)) = 0 := by
      exact_mod_cast certificate_layer hm hn (hout j hj)
    calc
      (∑ u ∈ range (m + 1), (certificate m u : ℝ) *
          (a j * (layer n j (singleRun n (2 * u + r)) : ℝ))) =
          a j * ∑ u ∈ range (m + 1), (certificate m u : ℝ) *
            (layer n j (singleRun n (2 * u + r)) : ℝ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro u hu
        ring
      _ = 0 := by rw [hjzero, mul_zero]
  have hzero : (∑ u ∈ range (m + 1), certificate m u * z u) = 0 := by
    exact_mod_cast hzeroR
  have hdetect := certificate_odd_pairing z heven hodd
  rw [hzero] at hdetect
  norm_num at hdetect

private theorem choose_le_of_middle {n m j : ℕ} (hmj : m ≤ j) (hjn : j ≤ n - m) :
    n.choose m ≤ n.choose j := by
  have hsmall : ∀ d : ℕ, m + d ≤ n / 2 → n.choose m ≤ n.choose (m + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases hj : j ≤ n / 2
  · simpa only [Nat.add_sub_of_le hmj] using hsmall (j - m) (by omega)
  · have hmn : m ≤ n - j := by omega
    have hnj : j ≤ n := by omega
    rw [← Nat.choose_symm hnj]
    simpa only [Nat.add_sub_of_le hmn] using hsmall (n - j - m) (by omega)

private theorem finite_lower_bound {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (T : Finset ℕ) (a : ℕ → ℝ) (h : ComputesSym n k T a) :
    n.choose (k / 2) ≤ qubits n T := by
  obtain ⟨j, hj, hmj, hjn⟩ := middle_layer_obstruction hk hkn h
  exact (choose_le_of_middle hmj hjn).trans
    (single_le_sum (fun i _ => Nat.zero_le (n.choose i)) hj)

private theorem qubits_pos {n k : ℕ} {T : Finset ℕ} {a : ℕ → ℝ}
    (hk : k ≤ n) (h : ComputesSym n k T a) : 1 ≤ qubits n T := by
  have hT : T.Nonempty := by
    by_contra hn
    have hzero : T = ∅ := not_nonempty_iff_eq_empty.mp hn
    obtain ⟨z, hz, hp⟩ := h.2 (singleRun n k)
    simp only [hzero, sum_empty] at hz
    have hz0 : z = 0 := by exact_mod_cast hz.symm
    subst z
    rw [csf_weight, hammingDist_singleRun hk, Nat.choose_self] at hp
    norm_num at hp
  obtain ⟨j, hj⟩ := hT
  have hjn := (h.1 j hj).2
  calc
    1 ≤ n.choose j := Nat.succ_le_iff.mpr (Nat.choose_pos hjn)
    _ ≤ qubits n T := single_le_sum (fun i _ => Nat.zero_le (n.choose i)) hj

private theorem choose_power_lower {n m : ℕ} (hn : 2 * m ≤ n) :
    (1 / ((2 : ℝ) ^ m * m.factorial)) * (n : ℝ) ^ m ≤ n.choose m := by
  have hhalf : (n : ℝ) / 2 ≤ (n + 1 - m : ℕ) := by
    have hm : m ≤ n + 1 := by omega
    rw [Nat.cast_sub hm, Nat.cast_add, Nat.cast_one]
    have hn' : (2 : ℝ) * m ≤ n := by exact_mod_cast hn
    linarith
  have hc := Nat.pow_le_choose (α := ℝ) m n
  calc
    _ = ((n : ℝ) / 2) ^ m / m.factorial := by rw [div_pow]; ring
    _ ≤ ((n + 1 - m : ℕ) : ℝ) ^ m / m.factorial := by
      gcongr
    _ ≤ _ := hc

private theorem claim_of_finiteClaim (hf : ∀ n k : ℕ, 2 ≤ k → k ≤ n →
    ∀ (T : Finset ℕ) (a : ℕ → ℝ), ComputesSym n k T a →
      n.choose (k / 2) ≤ qubits n T) : claim := by
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    refine ⟨1, by norm_num, 1, ?_⟩
    intro n hn T a h
    have hq : (1 : ℝ) ≤ qubits n T := by exact_mod_cast qubits_pos hn h
    have hn' : (1 : ℝ) ≤ n := by
      exact Nat.one_le_cast.mpr hn
    simp only [Nat.reduceDiv, Nat.cast_zero, zero_sub, zpow_neg_one, one_mul]
    exact (inv_le_one₀ (by positivity)).mpr hn' |>.trans hq
  · let m := k / 2
    refine ⟨1 / ((2 : ℝ) ^ m * m.factorial), by positivity, 2 * k, ?_⟩
    intro n hn T a h
    have hkn : k ≤ n := by omega
    have hmn : 2 * m ≤ n := by dsimp [m]; omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have he : (n : ℝ) ^ ((m : ℤ) - 1) ≤ (n : ℝ) ^ m := by
      simpa only [zpow_natCast] using zpow_le_zpow_right₀ hn1 (show (m : ℤ) - 1 ≤ m by omega)
    calc
      _ ≤ (1 / ((2 : ℝ) ^ m * m.factorial)) * (n : ℝ) ^ m := by
        exact mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ n.choose m := choose_power_lower hmn
      _ ≤ qubits n T := by exact_mod_cast hf n k (by omega) hkn T a h

theorem result : claim :=
  claim_of_finiteClaim (fun n k hk hkn T a h => finite_lower_bound (n := n) (k := k) hk hkn T a h)

end
end D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound
