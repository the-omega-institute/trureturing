/- GID: D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Symmetric complete-function lifts require a middle binomial layer of qubits. -/

/-
   result
   proof_shape: content
   escape_witness: none
   admission_basis: open-problem-resolution (#16724; Proved)
   Direct frozen dependencies: none (all imports are pinned Mathlib).

   The definitions parityBit, layer, csf, ComputesSym, qubits and claim are
   the expressions fixed in https://github.com/the-omega-institute/trureturing/issues/16724.
   ComputesSym has no constant term. The finite bound is a private theorem used by result.
   Hamming weight uses Mathlib.hammingDist against the all-false input; no weight or support
   alias is introduced. Private helpers marked bind-only below are consumed on result’s proof path.
   utility: none applies to this symbolic, universally quantified argument, not a bounded
   enumeration, numerical reduction, checker or certified instance.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16852

   csf_weight: proof_shape: bind-only; escape_witness: none;
     consumers: middle_layer_obstruction, qubits_pos; Direct frozen dependencies: none.
   parity_character: proof_shape: bind-only; escape_witness: none;
     consumers: layer_signed; Direct frozen dependencies: none.
   layer_signed: proof_shape: bind-only; escape_witness: none;
     consumers: certificate_layer; Direct frozen dependencies: none.
   hammingDist_weightInput: proof_shape: bind-only; escape_witness: none;
     consumers: certificate_signedLayer, middle_layer_obstruction, qubits_pos; Direct frozen dependencies: none.
   character_prod: proof_shape: bind-only; escape_witness: none;
     consumers: layerPolynomial_expand; Direct frozen dependencies: none.
   layerPolynomial_expand: proof_shape: bind-only; escape_witness: none;
     consumers: layerPolynomial_coeff; Direct frozen dependencies: none.
   layerPolynomial_weight: proof_shape: bind-only; escape_witness: none;
     consumers: weightPolynomial_coeff; Direct frozen dependencies: none.
   layerPolynomial_coeff: proof_shape: bind-only; escape_witness: none;
     consumers: weightPolynomial_coeff; Direct frozen dependencies: none.
   certificate_sum: proof_shape: bind-only; escape_witness: none;
     consumers: certificate_layer; Direct frozen dependencies: none.
   certificate_generating: proof_shape: bind-only; escape_witness: none;
     consumers: certificate_coeff; Direct frozen dependencies: none.
   weightPolynomial_coeff: proof_shape: bind-only; escape_witness: none;
     consumers: certificate_signedLayer; Direct frozen dependencies: none.
   certificate_coeff: proof_shape: bind-only; escape_witness: none;
     consumers: certificate_signedLayer; Direct frozen dependencies: none.
   certificate_signedLayer: proof_shape: bind-only; escape_witness: none;
     consumers: certificate_layer; Direct frozen dependencies: none.
   certificate_layer: proof_shape: bind-only; escape_witness: none;
     consumers: middle_layer_obstruction; Direct frozen dependencies: none.
   certificate_odd_pairing: proof_shape: bind-only; escape_witness: none;
     consumers: middle_layer_obstruction; Direct frozen dependencies: none.
   middle_layer_obstruction: proof_shape: content; escape_witness: none;
     consumers: finite_lower_bound; Direct frozen dependencies: none.
   choose_le_of_middle: proof_shape: bind-only; escape_witness: none;
     consumers: finite_lower_bound; Direct frozen dependencies: none.
   finite_lower_bound: proof_shape: content; escape_witness: none;
     consumers: claim_of_finiteClaim; Direct frozen dependencies: none.
   qubits_pos: proof_shape: bind-only; escape_witness: none;
     consumers: claim_of_finiteClaim; Direct frozen dependencies: none.
   choose_power_lower: proof_shape: bind-only; escape_witness: none;
     consumers: claim_of_finiteClaim; Direct frozen dependencies: none.
   claim_of_finiteClaim: proof_shape: bind-only; escape_witness: none;
     consumers: result; Direct frozen dependencies: none.
-/

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.InformationTheory.Hamming

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset Polynomial
namespace D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound
noncomputable section

variable {n : ℕ}

def parityBit (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ :=
  if Odd ((S.filter (fun l => x l = true)).card) then 1 else 0

def layer (n i : ℕ) (x : Fin n → Bool) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = i), parityBit S x

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

private def character (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ :=
  (-1) ^ ((S.filter (fun l => x l = true)).card)

private def signedLayer (n i : ℕ) (x : Fin n → Bool) : ℤ :=
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card = i), character S x

private theorem csf_weight (k : ℕ) (x : Fin n → Bool) :
    csf n k x = (Nat.choose (hammingDist x (fun _ => false)) k : ℤ) % 2 := by
  have h : (univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ ∀ l ∈ S, x l = true) = ((univ : Finset (Fin n)).filter (fun l => x l = true)).powersetCard k := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_iff]
    aesop
  simp only [csf, h, card_powersetCard, hammingDist, Bool.not_eq_false]

private theorem parity_character (S : Finset (Fin n)) (x : Fin n → Bool) :
    2 * parityBit S x = 1 - character S x := by
  rcases Nat.even_or_odd ((S.filter (fun l => x l = true)).card) with h | h
  · simp [parityBit, character, h.neg_one_pow, Nat.not_odd_iff_even.mpr h]
  · simp [parityBit, character, h, h.neg_one_pow]

private theorem layer_signed (i : ℕ) (x : Fin n → Bool) :
    2 * layer n i x = (n.choose i : ℤ) - signedLayer n i x := by
  have h : ((univ : Finset (Fin n)).powersetCard i) =
      (univ : Finset (Finset (Fin n))).filter (fun S => S.card = i) := by
    ext S
    simp only [mem_powersetCard, subset_univ, true_and, mem_filter, mem_univ]
  have hc : ((univ : Finset (Finset (Fin n))).filter (fun S => S.card = i)).card =
      n.choose i := by rw [← h, card_powersetCard]; simp
  simp only [layer, signedLayer, mul_sum, parity_character, sum_sub_distrib, sum_const,
    nsmul_eq_mul, mul_one, hc]

private def weightInput (n w : ℕ) : Fin n → Bool := fun l => decide (l.val < w)

private theorem hammingDist_weightInput {w : ℕ} (hw : w ≤ n) : hammingDist (weightInput n w) (fun _ => false) = w := by
  simp only [hammingDist, weightInput, Bool.not_eq_false, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right hw]

private theorem character_prod (S : Finset (Fin n)) (x : Fin n → Bool) :
    character S x = ∏ l ∈ S, (if x l = true then (-1 : ℤ) else 1) := by
  simp [character, prod_ite]

private def layerPolynomial (x : Fin n → Bool) : ℤ[X] :=
  ∏ l : Fin n, (1 + C (if x l = true then (-1 : ℤ) else 1) * X)

private theorem layerPolynomial_expand (x : Fin n → Bool) :
    layerPolynomial x = ∑ S : Finset (Fin n), C (character S x) * X ^ S.card := by
  rw [layerPolynomial, prod_one_add, powerset_univ]
  apply sum_congr rfl
  intro S _
  rw [prod_mul_distrib, prod_const, ← map_prod, ← character_prod]

private theorem layerPolynomial_weight (x : Fin n → Bool) :
    layerPolynomial x = (1 - X) ^ hammingDist x (fun _ => false) * (1 + X) ^ (n - hammingDist x (fun _ => false)) := by
  have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun l => x l = true)
  simp only [card_univ, Fintype.card_fin] at hc
  have hneg : ((univ : Finset (Fin n)).filter (fun l => ¬ x l = true)).card =
      n - hammingDist x (fun _ => false) := by simp only [hammingDist, Bool.not_eq_false]; omega
  calc
    layerPolynomial x = ∏ l : Fin n, (if x l = true then (1 - X : ℤ[X]) else 1 + X) := by
      unfold layerPolynomial
      apply prod_congr rfl
      intro l _
      split_ifs <;> simp [sub_eq_add_neg]
    _ = _ := by rw [prod_ite, prod_const, prod_const, hneg]; simp only [hammingDist, Bool.not_eq_false]

private theorem layerPolynomial_coeff (i : ℕ) (x : Fin n → Bool) :
    (layerPolynomial x).coeff i = signedLayer n i x := by
  rw [layerPolynomial_expand]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, signedLayer, sum_filter, eq_comm]

private def certificate (m u : ℕ) : ℤ := (-1) ^ (m - u) * m.choose u

private def weightPolynomial (n w : ℕ) : ℤ[X] := (1 - X) ^ w * (1 + X) ^ (n - w)

private theorem certificate_sum {m : ℕ} (hm : 1 ≤ m) :
    ∑ u ∈ range (m + 1), certificate m u = 0 := by
  have h := (add_pow (1 : ℤ) (-1) m).symm
  simpa [certificate, zero_pow (by omega : m ≠ 0)] using h

private theorem certificate_generating {n m r : ℕ} (hn : 2 * m + r ≤ n) :
    (∑ u ∈ range (m + 1), C (certificate m u) * weightPolynomial n (2 * u + r)) =
    C ((-4 : ℤ) ^ m) * (X ^ m * ((1 - X) ^ r * (1 + X) ^ (n - (2 * m + r)))) := by
  have he : ∀ u ∈ range (m + 1), n - (2 * u + r) = 2 * (m - u) + (n - (2 * m + r)) := by
    intro u hu
    have := mem_range.mp hu
    omega
  calc
    _ = ((1 - X) ^ r * (1 + X) ^ (n - (2 * m + r))) *
        ∑ u ∈ range (m + 1), ((1 - X) ^ 2) ^ u * (-((1 + X) ^ 2)) ^ (m - u) *
          (m.choose u : ℤ[X]) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro u hu
      simp only [certificate, weightPolynomial, map_mul, map_pow, map_neg, map_one,
        map_natCast, he u hu, pow_add, pow_mul, neg_pow ((1 + X : ℤ[X]) ^ 2)]
      ring
    _ = _ := by
      rw [← add_pow]
      have hx : ((1 - X) ^ 2 + -((1 + X) ^ 2) : ℤ[X]) = C (-4) * X := by norm_num; ring
      rw [hx, mul_pow, ← map_pow]
      ring

private theorem weightPolynomial_coeff (i : ℕ) (x : Fin n → Bool) :
    (weightPolynomial n (hammingDist x (fun _ => false))).coeff i = signedLayer n i x := by
  rw [← layerPolynomial_coeff, layerPolynomial_weight]
  rfl

private theorem certificate_coeff {n m r j : ℕ} (hn : 2 * m + r ≤ n)
    (hj : j < m ∨ n - m < j) :
    ∑ u ∈ range (m + 1), certificate m u * (weightPolynomial n (2 * u + r)).coeff j = 0 := by
  have h := congrArg (fun p : ℤ[X] => p.coeff j) (certificate_generating hn)
  simp only [finsetSum_coeff, coeff_C_mul] at h
  rw [h]
  rcases hj with hj | hj
  · rw [coeff_X_pow_mul', if_neg (by omega : ¬m ≤ j), mul_zero]
  · have hminus : (1 - X : ℤ[X]).natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    have hplus : (1 + X : ℤ[X]).natDegree ≤ 1 := by
      exact (natDegree_add_le _ _).trans (by simp)
    have hd : (X ^ m * ((1 - X : ℤ[X]) ^ r * (1 + X) ^ (n - (2 * m + r)))).natDegree ≤ n - m := by
      have h1 := natDegree_pow_le_of_le r hminus
      have h2 := natDegree_pow_le_of_le (n - (2 * m + r)) hplus
      have h3 := natDegree_mul_le_of_le h1 h2
      have h4 := natDegree_mul_le_of_le (natDegree_X_pow_le m : (X ^ m : ℤ[X]).natDegree ≤ m) h3
      exact h4.trans (by omega)
    rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt hj), mul_zero]

private theorem certificate_signedLayer {n m r j : ℕ} (hn : 2 * m + r ≤ n)
    (hj : j < m ∨ n - m < j) :
    ∑ u ∈ range (m + 1), certificate m u * signedLayer n j (weightInput n (2 * u + r)) = 0 := by
  convert certificate_coeff hn hj using 1
  apply sum_congr rfl
  intro u hu
  have hw : 2 * u + r ≤ n := by have := mem_range.mp hu; omega
  rw [← weightPolynomial_coeff, hammingDist_weightInput hw]

private theorem certificate_layer {n m r j : ℕ} (hm : 1 ≤ m) (hn : 2 * m + r ≤ n)
    (hj : j < m ∨ n - m < j) :
    ∑ u ∈ range (m + 1), certificate m u * layer n j (weightInput n (2 * u + r)) = 0 := by
  have hs := certificate_signedLayer hn hj
  have hd := certificate_sum hm
  have he : 2 * (∑ u ∈ range (m + 1), certificate m u *
      layer n j (weightInput n (2 * u + r))) =
      (∑ u ∈ range (m + 1), certificate m u) * (n.choose j : ℤ) -
      ∑ u ∈ range (m + 1), certificate m u * signedLayer n j (weightInput n (2 * u + r)) := by
    rw [mul_sum, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    have h := layer_signed j (weightInput n (2 * u + r))
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
  have hn : 2 * m + r ≤ n := by omega
  by_contra hmid
  have hout : ∀ j ∈ T, j < m ∨ n - m < j := by
    intro j hj
    by_cases hjm : j < m
    · exact Or.inl hjm
    · right
      by_contra hjn
      apply hmid
      exact ⟨j, hj, by dsimp [m] at *; omega, by dsimp [m] at *; omega⟩
  let z (u : ℕ) : ℤ := Classical.choose (h.2 (weightInput n (2 * u + r)))
  have hz (u : ℕ) : (∑ i ∈ T, a i * (layer n i (weightInput n (2 * u + r)) : ℝ)) =
      (z u : ℝ) := (Classical.choose_spec (h.2 (weightInput n (2 * u + r)))).1
  have hp (u : ℕ) : z u % 2 = csf n k (weightInput n (2 * u + r)) :=
    (Classical.choose_spec (h.2 (weightInput n (2 * u + r)))).2
  have heven : ∀ u ∈ range m, z u % 2 = 0 := by
    intro u hu
    have hu' := mem_range.mp hu
    have hw : 2 * u + r ≤ n := by omega
    have hwk : 2 * u + r < k := by omega
    rw [hp, csf_weight, hammingDist_weightInput hw, Nat.choose_eq_zero_of_lt hwk]
    norm_num
  have hodd : z m % 2 = 1 := by
    rw [hp, hkr, csf_weight, hammingDist_weightInput hkn, Nat.choose_self]
    norm_num
  have hzeroR : (∑ u ∈ range (m + 1), (certificate m u : ℝ) * (z u : ℝ)) = 0 := by
    simp_rw [← hz, mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro j hj
    have hjzero : (∑ u ∈ range (m + 1), (certificate m u : ℝ) *
        (layer n j (weightInput n (2 * u + r)) : ℝ)) = 0 := by
      exact_mod_cast certificate_layer hm hn (hout j hj)
    calc
      (∑ u ∈ range (m + 1), (certificate m u : ℝ) *
          (a j * (layer n j (weightInput n (2 * u + r)) : ℝ))) =
          a j * ∑ u ∈ range (m + 1), (certificate m u : ℝ) *
            (layer n j (weightInput n (2 * u + r)) : ℝ) := by
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
    obtain ⟨z, hz, hp⟩ := h.2 (weightInput n k)
    simp only [hzero, sum_empty] at hz
    have hz0 : z = 0 := by exact_mod_cast hz.symm
    subst z
    rw [csf_weight, hammingDist_weightInput hk, Nat.choose_self] at hp
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
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
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
