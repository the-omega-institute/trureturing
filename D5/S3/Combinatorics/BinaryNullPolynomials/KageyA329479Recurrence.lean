/- GID: D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary null polynomial counts satisfy Kagey's order-eight recurrence. -/

/-
result
proof_shape: content
escape_witness: countEquiv (literal-polynomial/word bijection) and contribution_eq
  (identification of the two polynomial evaluations with transfer acceptance)
admission_basis: open-problem-resolution (#21714; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22573.
Direct frozen dependencies:
D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.weighted_walks_eq_pow
  statement_id: sha256:0a48c821df6269e2755784a5d9d96495b76527600ae4f593396574cd4f512097
D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.wordContribution
  statement_id: sha256:a8e8be6f5bd332924e7f96a4ce42963c84d7e2a05047d3cff103a67b763b5595
D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.wordContribution.congr_simp
  statement_id: sha256:bdec28924a293cc9855e5c5b8f7487660d3d1f538b1a3d2d2932ee121a99fbd5
D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.wordContribution.eq_1
  statement_id: sha256:01f967b969de7e0233a3e59f6b941124a14d29e65863239be5eb0aec720745d6
D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer.wordContribution.eq_2
  statement_id: sha256:46b0d8ed4de1614c076dff25a3d0be1e99945d2d6cee03d9fb2222000ffce62e

Closed source reuse: Complexity.TapeToStacks.fin_three_cases; its owner is not
a frozen member. The ZMod 3 split is its specialization with 2 = -1.

The count a uses the degree-exact integer-polynomial subtype from OEIS A329479.
Interior Boolean coefficients use Bool.toInt and Polynomial.ofFn; the constant
coefficient is zero and the leading coefficient is one.
The proof constructs the coefficient-word correspondence and identifies its two evaluations
with the terminal column of the labelled-word transfer matrix. A finite column identity
propagates linearly to every degree. The only public theorem is result.
-/

import D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer
import D5.S0.Computability.BinaryMachine.TapeToStacks
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.ZMod.Basic

namespace D5.S3.Combinatorics.BinaryNullPolynomials.KageyA329479Recurrence

/-- OEIS A329479: the number of degree-exactly-n integer polynomials with
all nonzero coefficients equal to 1 that vanish modulo 3 at every integer. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {f : Polynomial ℤ //
    f.natDegree = n ∧ f.Monic ∧
    (∀ i : ℕ, f.coeff i = 0 ∨ f.coeff i = 1) ∧
    (∀ k : ℤ, (3 : ℤ) ∣ f.eval k)}

/-- The final conjectured-recurrence line of OEIS A329479, revision 25.
The bound 9 is the first index for which all eight arguments lie in offset 1.
Subtraction of counts takes place in the integers. -/
def claim : Prop :=
  ∀ n : ℕ, 9 ≤ n →
    (a n : ℤ) =
      2 * (a (n - 1) : ℤ) + 2 * (a (n - 2) : ℤ) -
      5 * (a (n - 3) : ℤ) - 2 * (a (n - 4) : ℤ) +
      10 * (a (n - 5) : ℤ) - 4 * (a (n - 6) : ℤ) -
      4 * (a (n - 7) : ℤ) + 8 * (a (n - 8) : ℤ)

open Polynomial
open scoped BigOperators Classical

private noncomputable def encoded {n : ℕ} (w : Fin n → Bool) : Polynomial ℤ :=
  X ^ (n + 1) + X * Polynomial.ofFn n (fun i => Bool.toInt (w i))

private theorem encoded_sum {n : ℕ} (w : Fin n → Bool) :
    encoded w = X ^ (n + 1) +
      ∑ i : Fin n, C (Bool.toInt (w i)) * X ^ (i.val + 1) := by
  rw [encoded, Polynomial.ofFn_eq_sum_monomial, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_succ]
  ring

private theorem coeff_encoded {n : ℕ} (w : Fin n → Bool) (j : ℕ) :
    (encoded w).coeff j =
      if j = n + 1 then 1 else
        if h : 0 < j ∧ j ≤ n then Bool.toInt (w ⟨j - 1, by omega⟩) else 0 := by
  rw [encoded_sum, coeff_add, finsetSum_coeff]
  simp only [coeff_X_pow, coeff_C_mul_X_pow]
  by_cases hn : j = n + 1
  · subst j
    simp only [ite_true]
    have hs : (∑ i : Fin n, if n + 1 = i.val + 1 then Bool.toInt (w i) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro i _
      rw [ite_eq_right (show n + 1 ≠ i.val + 1 by omega)]
    rw [hs, add_zero]
  · simp only [ite_eq_right hn]
    by_cases h : 0 < j ∧ j ≤ n
    · simp only [dite_eq_left h]
      let q : Fin n := ⟨j - 1, by omega⟩
      have hi (i : Fin n) : j = i.val + 1 ↔ i = q := by
        simp only [Fin.ext_iff, q]; omega
      simp_rw [hi]
      simp [q]
    · simp only [dite_eq_right h]
      have hs : (∑ i : Fin n, if j = i.val + 1 then Bool.toInt (w i) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro i _
        rw [ite_eq_right (show j ≠ i.val + 1 by omega)]
      simpa using hs

private theorem encoded_shape {n : ℕ} (w : Fin n → Bool) :
    (encoded w).natDegree = n + 1 ∧ (encoded w).Monic ∧
      (∀ i : ℕ, (encoded w).coeff i = 0 ∨ (encoded w).coeff i = 1) ∧
      (encoded w).coeff 0 = 0 := by
  have high : (encoded w).coeff (n+1) = 1 := by simp [coeff_encoded]
  have deg : (encoded w).natDegree = n+1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      simp [coeff_encoded, show j ≠ n+1 by omega, show ¬ (0<j ∧ j≤n) by omega]
    · rw [high]; decide
  refine ⟨deg, ?_, ?_, ?_⟩
  · rw [Monic.def, leadingCoeff, deg, high]
  · intro i
    rw [coeff_encoded]
    split_ifs <;> simp [Bool.toInt]
  · simp [coeff_encoded]

private theorem residue_cases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 := by
  intro x
  have h := Complexity.TapeToStacks.fin_three_cases x
  change x = (0 : ZMod 3) ∨ x = (1 : ZMod 3) ∨ x = (2 : ZMod 3) at h
  simpa only [show (2 : ZMod 3) = -1 by decide] using h

private theorem null_iff (f : Polynomial ℤ) (hz : f.coeff 0 = 0) :
    (∀ k : ℤ, (3 : ℤ) ∣ f.eval k) ↔
      f.eval₂ (Int.castRingHom (ZMod 3)) 1 = 0 ∧
      f.eval₂ (Int.castRingHom (ZMod 3)) (-1) = 0 := by
  constructor
  · intro h
    constructor
    · have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval 1) 3).mpr (h 1)
      simpa only [map_one] using (eval₂_at_apply (Int.castRingHom (ZMod 3)) 1).trans hh
    · have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (-1)) 3).mpr (h (-1))
      simpa only [map_neg, map_one] using
        (eval₂_at_apply (Int.castRingHom (ZMod 3)) (-1)).trans hh
  · rintro ⟨h1, hm⟩ k
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval k) 3).mp
    change (Int.castRingHom (ZMod 3)) (f.eval k) = 0
    rw [← eval₂_at_apply]
    have hall (x : ZMod 3) : f.eval₂ (Int.castRingHom (ZMod 3)) x = 0 := by
      rcases residue_cases x with rfl | rfl | rfl
      · rw [eval₂_at_zero, hz, map_zero]
      · exact h1
      · exact hm
    exact hall _

private theorem encoded_injective (n : ℕ) : Function.Injective (@encoded n) := by
  intro u v h
  funext i
  have hc := congrArg (fun f : Polynomial ℤ => f.coeff (i.val+1)) h
  have hn : i.val+1 ≠ n+1 := by omega
  have hi : 0 < i.val+1 ∧ i.val+1 ≤ n := by omega
  simp only [coeff_encoded, ite_eq_right hn, dite_eq_left hi, Nat.add_sub_cancel] at hc
  cases hu : u i <;> cases hv : v i <;> simp_all [Bool.toInt]

private theorem reconstruct (n : ℕ) (f : Polynomial ℤ)
    (hd : f.natDegree = n+1) (hm : f.Monic)
    (hb : ∀ j : ℕ, f.coeff j = 0 ∨ f.coeff j = 1) (hz : f.coeff 0 = 0) :
    encoded (fun i : Fin n => decide (f.coeff (i.val+1) = 1)) = f := by
  ext j
  rw [coeff_encoded]
  split_ifs with hn hj
  · subst j
    simpa only [hd] using hm.coeff_natDegree.symm
  · simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : j ≠ 0))]
    rcases hb j with h | h <;> simp [Bool.toInt, h]
  · by_cases h0 : j = 0
    · subst j; exact hz.symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < j)).symm

private theorem zero_constant (f : Polynomial ℤ)
    (hb : f.coeff 0 = 0 ∨ f.coeff 0 = 1)
    (hf : ∀ k : ℤ, (3 : ℤ) ∣ f.eval k) : f.coeff 0 = 0 := by
  rcases hb with h | h
  · exact h
  · have hh := hf 0
    rw [← coeff_zero_eq_eval_zero, h] at hh
    norm_num at hh

private def WordValid {n : ℕ} (w : Fin n → Bool) : Prop :=
  (encoded w).eval₂ (Int.castRingHom (ZMod 3)) 1 = 0 ∧
  (encoded w).eval₂ (Int.castRingHom (ZMod 3)) (-1) = 0

private noncomputable def countEquiv (n : ℕ) :
    {w : Fin n → Bool // WordValid w} ≃
    {f : Polynomial ℤ // f.natDegree = n+1 ∧ f.Monic ∧
      (∀ i : ℕ, f.coeff i = 0 ∨ f.coeff i = 1) ∧
      (∀ k : ℤ, (3 : ℤ) ∣ f.eval k)} := by
  classical
  apply Equiv.ofBijective (fun w => ⟨encoded w.val,
    (encoded_shape w.val).1, (encoded_shape w.val).2.1,
    (encoded_shape w.val).2.2.1,
    (null_iff _ (encoded_shape w.val).2.2.2).mpr w.property⟩)
  constructor
  · intro u v h
    apply Subtype.ext
    exact encoded_injective n (congrArg Subtype.val h)
  · rintro ⟨f, hd, hm, hb, hf⟩
    let w : Fin n → Bool := fun i => decide (f.coeff (i.val+1) = 1)
    have he : encoded w = f := reconstruct n f hd hm hb (zero_constant f (hb 0) hf)
    have hw : WordValid w := by
      unfold WordValid
      rw [he]
      exact (null_iff f (zero_constant f (hb 0) hf)).mp hf
    refine ⟨⟨w, hw⟩, ?_⟩
    exact Subtype.ext he

private theorem count_bridge (n : ℕ) :
    (a (n+1) : ℤ) = ∑ w : Fin n → Bool, if WordValid w then 1 else 0 := by
  classical
  unfold a
  rw [← Nat.card_congr (countEquiv n), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.sum_boole]


private theorem encoded_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    encoded (Fin.cons b w) = X * (C (Bool.toInt b) + encoded w) := by
  rw [encoded_sum, encoded_sum]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, zero_add, pow_one]
  rw [mul_add, mul_add, Finset.mul_sum]
  have hs : (∑ i : Fin n, C (Bool.toInt (w i)) * X ^ (i.val + 1 + 1)) =
      ∑ i : Fin n, X * (C (Bool.toInt (w i)) * X ^ (i.val + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  rw [hs, pow_succ]
  ring

private def back (s : (ZMod 3 × ZMod 3)) (b : Bool) : (ZMod 3 × ZMod 3) :=
  (s.1 - (Bool.toInt b : ZMod 3), -s.2 - (Bool.toInt b : ZMod 3))

private def base : (ZMod 3 × ZMod 3) := (1,-1)

private noncomputable def transfer : Matrix (ZMod 3 × ZMod 3) (ZMod 3 × ZMod 3) ℤ :=
  Matrix.of fun s t => ∑ b : Bool, if back s b = t then 1 else 0

open D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer

private theorem contribution_eq {n : ℕ} (w : Fin n → Bool) (s : (ZMod 3 × ZMod 3)) :
    wordContribution back (fun _ _ => 1) base s (List.ofFn w) =
      if ((encoded w).eval₂ (Int.castRingHom (ZMod 3)) 1,
        (encoded w).eval₂ (Int.castRingHom (ZMod 3)) (-1)) = s then 1 else 0 := by
  induction n generalizing s with
  | zero =>
    simp [wordContribution, encoded, base, eq_comm]
  | succ n ih =>
    obtain ⟨⟨b,w⟩, rfl⟩ := (Fin.consEquiv fun _ : Fin (n+1) => Bool).surjective w
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [List.ofFn_cons, wordContribution, one_mul, ih]
    have hkey :
        ((encoded (Fin.cons b w)).eval₂ (Int.castRingHom (ZMod 3)) 1,
          (encoded (Fin.cons b w)).eval₂ (Int.castRingHom (ZMod 3)) (-1)) = s ↔
        ((encoded w).eval₂ (Int.castRingHom (ZMod 3)) 1,
          (encoded w).eval₂ (Int.castRingHom (ZMod 3)) (-1)) = back s b := by
      rcases s with ⟨s1,s2⟩
      simp only [encoded_cons, eval₂_mul, eval₂_X, eval₂_add, eval₂_C,
        one_mul, neg_one_mul, Prod.mk.injEq, back]
      change ((Bool.toInt b : ZMod 3) + (encoded w).eval₂ (Int.castRingHom (ZMod 3)) 1 = s1 ∧
        -((Bool.toInt b : ZMod 3) + (encoded w).eval₂ (Int.castRingHom (ZMod 3)) (-1)) = s2) ↔ _
      constructor
      · rintro ⟨h1,h2⟩
        constructor
        · linear_combination h1
        · linear_combination -h2
      · rintro ⟨h1,h2⟩
        constructor
        · linear_combination h1
        · linear_combination -h2
    simp only [hkey]

private theorem words_eq_v (n : ℕ) (s : (ZMod 3 × ZMod 3)) :
    (∑ w : Fin n → Bool, wordContribution back (fun _ _ => 1) base s (List.ofFn w)) = ((transfer ^ n) s base) := by
  exact weighted_walks_eq_pow back (fun _ _ => 1) n s base

private theorem a_eq_v (n : ℕ) : (a (n+1) : ℤ) = ((transfer ^ n) (0,0) base) := by
  rw [count_bridge, ← words_eq_v]
  apply Finset.sum_congr rfl
  intro w _
  rw [contribution_eq]
  simp [WordValid, Prod.mk.injEq]

private theorem v_succ (n : ℕ) (s : (ZMod 3 × ZMod 3)) :
    ((transfer ^ (n+1)) s base) = ((transfer ^ n) (back s false) base) + ((transfer ^ n) (back s true) base) := by
  rw [← words_eq_v]
  rw [← (Fin.consEquiv fun _ : Fin (n+1) => Bool).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons,
    wordContribution, one_mul]
  simp_rw [words_eq_v]
  simp [add_comm]

private theorem vector_eight (s : (ZMod 3 × ZMod 3)) :
    ((transfer ^ 8) s base) = 2*((transfer ^ 7) s base) + 2*((transfer ^ 6) s base) - 5*((transfer ^ 5) s base) - 2*((transfer ^ 4) s base) +
      10*((transfer ^ 3) s base) - 4*((transfer ^ 2) s base) - 4*((transfer ^ 1) s base) + 8*((transfer ^ 0) s base) := by
  rcases s with ⟨u,w⟩
  rcases residue_cases u with rfl | rfl | rfl <;>
    rcases residue_cases w with rfl | rfl | rfl <;>
    norm_num [back, base, Bool.toInt] <;> decide

private theorem vector_recurrence (n : ℕ) (s : (ZMod 3 × ZMod 3)) :
    ((transfer ^ (n+8)) s base) = 2*((transfer ^ (n+7)) s base) + 2*((transfer ^ (n+6)) s base) - 5*((transfer ^ (n+5)) s base) - 2*((transfer ^ (n+4)) s base) +
      10*((transfer ^ (n+3)) s base) - 4*((transfer ^ (n+2)) s base) - 4*((transfer ^ (n+1)) s base) + 8*((transfer ^ n) s base) := by
  induction n generalizing s with
  | zero => simpa using vector_eight s
  | succ n ih =>
    change ((transfer ^ ((n+8)+1)) s base) = 2*((transfer ^ ((n+7)+1)) s base) + 2*((transfer ^ ((n+6)+1)) s base) -
      5*((transfer ^ ((n+5)+1)) s base) - 2*((transfer ^ ((n+4)+1)) s base) + 10*((transfer ^ ((n+3)+1)) s base) -
      4*((transfer ^ ((n+2)+1)) s base) - 4*((transfer ^ ((n+1)+1)) s base) + 8*((transfer ^ (n+1)) s base)
    rw [v_succ n, v_succ (n+1), v_succ (n+2), v_succ (n+3), v_succ (n+4),
      v_succ (n+5), v_succ (n+6), v_succ (n+7), v_succ (n+8)]
    rw [ih (back s false), ih (back s true)]
    ring

theorem result : claim := by
  intro n hn
  have h := vector_recurrence (n-9) (0,0)
  have hi (j : ℕ) (hj : j ≤ 8) : n-j = (n-9+(8-j))+1 := by omega
  change (a (n-0) : ℤ) = _
  rw [hi 0 (by omega), hi 1 (by omega), hi 2 (by omega), hi 3 (by omega),
    hi 4 (by omega), hi 5 (by omega), hi 6 (by omega), hi 7 (by omega),
    hi 8 (by omega)]
  simp only [a_eq_v]
  simpa using h

end D5.S3.Combinatorics.BinaryNullPolynomials.KageyA329479Recurrence
