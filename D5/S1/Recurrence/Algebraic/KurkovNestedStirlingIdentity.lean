/- GID: D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Vandermonde]
   utility: none
   digest: Kurkov's full nested rational sum equals the unsigned Stirling number. -/

/-
The proof-local cauchyBinet is adapted from physlib
15d02258f4c017bd63c6f3ece4653aa421ea87c3,
QuantumInfo/ForMathlib/Majorization.lean, lines 147-231.
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0; full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Authors of the upstream supplier: Alex Meiburg.
Modifications: minimal Mathlib imports, proof-local scope and fixed universe.
The mathematical proof body is unchanged. The pinned upstream tree has no NOTICE.
Retirement: replace this local port with direct application when this repository's
own pinned Mathlib contains an equivalent rectangular Cauchy-Binet declaration.
The source assertion and bounded prior-art scope are recorded in
Library/Recurrence/kurkov2026a132393.md and the corresponding Problems dossier.
-/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Vandermonde
import D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod
import Mathlib.Tactic.Cases

open Finset BigOperators Matrix

namespace D5.S1.Recurrence.Algebraic.KurkovNestedStirlingIdentity

/-- Zero-based positions; values are the literal decreasing summation indices. -/
def Chain (n m : ℕ) := {j : Fin m → Fin (n + 1) // Antitone j}

noncomputable instance (n m : ℕ) : Fintype (Chain n m) := by
  classical
  unfold Chain
  infer_instance

/-- The original rational summand, with source positions t = i+1. -/
def sourceTerm {n m : ℕ} (j : Chain n m) : ℚ :=
  (-1 : ℚ) ^ (n * m + ∑ i, (j.val i).val) *
    (∏ q : Fin m, ∏ p ∈ Ioi q,
      (((j.val q).val : ℚ) - (j.val p).val + p.val - q.val) ^ 2) *
    ∏ t : Fin m,
      ((n + t.val).descFactorial (j.val t).val : ℚ) /
        (((n - (j.val t).val + (t.val + 1) : ℕ) : ℚ) ^ (m + 1) *
          ((j.val t).val + m - (t.val + 1)).factorial)

/-- The literal Kurkov right-hand side (no determinant hypothesis). -/
noncomputable def sourceRHS (n m : ℕ) : ℚ :=
  ((n + m).factorial : ℚ) *
    (∏ i : Fin m, ((n + (i.val + 1) : ℕ) : ℚ) ^ (i.val + 1)) *
    ∑ j : Chain n m, sourceTerm j

/-- The literal full Kurkov identity, preregistered in issue 9456. -/
theorem result (n m : ℕ) (_hm : 1 ≤ m) :
    sourceRHS n m = (Nat.stirlingFirst (n + m + 1) (m + 1) : ℚ) := by
  classical
  let NodeSet (n m : ℕ) := {s : Finset (Fin (n + m)) // s.card = m}
  have cauchyBinet {m : ℕ} {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n]
      {R : Type} [CommRing R]
      (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R) :
      (A * B).det = ∑ S : {S : Finset n // S.card = m},
        (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    have h_cauchy_binet : ∀ (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R), Matrix.det (A * B) = ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) := by
      simp [Matrix.det_apply']
      simp [Matrix.mul_apply, Finset.mul_sum]
      intro A B; rw [← Finset.sum_comm]; congr; ext x; simp [mul_comm]
      simp only [prod_sum, sum_mul]
      refine' Finset.sum_bij (fun f _ => fun i => f (x.symm i) (Finset.mem_univ _)) _ _ _ _
      · simp
      · simp only [univ_pi_univ, mem_univ, funext_iff, forall_true_left, forall_const]
        exact fun a₁ a₂ h i => by simpa using h (x i)
      · simp only [mem_univ, univ_pi_univ, exists_const, forall_const]
        exact fun b => ⟨fun i _ => b (x i), by ext i; simp⟩
      · simp only [univ_pi_univ, mem_univ, prod_mul_distrib, prod_attach_univ,
        Equiv.symm_apply_apply, forall_const]
        intro a
        rw [← Equiv.prod_comp x.symm]
        ring_nf
        rw [← Equiv.prod_comp x.symm]
        simp only [mul_comm, mul_assoc]
        conv_rhs => rw [← Equiv.prod_comp x]
        simp [Equiv.symm_apply_apply]
    -- Split the sum into injective and non-injective functions.
    have h_split : ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) = ∑ σ : Fin m → n, if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0 := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      split_ifs with hσ <;> simp_all [Function.Injective]
      obtain ⟨i, j, hij, hne⟩ := hσ
      exact mul_eq_zero_of_right _ (Matrix.det_zero_of_row_eq hne (by ext1; simp only [of_apply, hij]))
    -- Group the sum by the image of the injective functions.
    have h_group : ∑ σ : Fin m → n, (if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) := by
      rw [← Finset.sum_comm, Finset.sum_congr rfl]
      intro σ _
      by_cases hσ : Function.Injective σ
      · simp [hσ]
        rw [Finset.sum_eq_single ⟨Finset.image σ Finset.univ, by simp [Finset.card_image_of_injective _ hσ]⟩]
        · simp
        · grind
        · simp
      · simp [hσ]
    -- For each subset $S$ of size $m$, the inner sum is equal to the product of the determinants of the submatrices of $A$ and $B$ corresponding to $S$.
    have h_inner : ∀ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = Matrix.det (Matrix.submatrix A id (S.val.orderEmbOfFin S.property)) * Matrix.det (Matrix.submatrix B (S.val.orderEmbOfFin S.property) id) := by
      intro S
      have h_inner_sum : ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ τ : Equiv.Perm (Fin m), (∏ i, A i (S.val.orderEmbOfFin S.property (τ i))) * Matrix.det (Matrix.of (fun i j ↦ B (S.val.orderEmbOfFin S.property (τ i)) j)) := by
        have h_inner_sum : Finset.filter (fun σ : Fin m → n => Function.Injective σ ∧ Finset.image σ Finset.univ = S.val) Finset.univ = Finset.image (fun τ : Equiv.Perm (Fin m) => fun i => S.val.orderEmbOfFin S.property (τ i)) Finset.univ := by
          ext σ
          simp [Finset.mem_image]
          constructor
          · intro hσ
            obtain ⟨a, ha⟩ : ∃ a : Fin m → Fin m, ∀ i, σ i = S.val.orderEmbOfFin S.property (a i) := by
              have h_exists_a : ∀ i, ∃ a : Fin m, σ i = S.val.orderEmbOfFin S.property a := by
                intro i
                have h_exists_a : σ i ∈ S.val := by
                  exact hσ.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
                have h_exists_a : Finset.image (fun a : Fin m => S.val.orderEmbOfFin S.property a) Finset.univ = S.val := by
                  refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun a _ => Finset.orderEmbOfFin_mem _ _ _) _
                  rw [Finset.card_image_of_injective _ fun a b h => by simpa [Fin.ext_iff] using h]; simp [S.2]
                grind
              exact ⟨fun i => Classical.choose (h_exists_a i), fun i => Classical.choose_spec (h_exists_a i)⟩
            have ha_inj : Function.Injective a := by
              exact fun i j hij => hσ.1 <| by simp [ha, hij]
            exact ⟨Equiv.ofBijective a ⟨ha_inj, Finite.injective_iff_surjective.mp ha_inj⟩, funext fun i => ha i ▸ rfl⟩
          · rintro ⟨a, rfl⟩
            constructor
            · exact fun i j hij => a.injective <| by simpa using hij
            · refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _) ?_
              rw [Finset.card_image_of_injective _ fun i j hij => by simpa [Fin.ext_iff] using hij]; simp [S.2]
        rw [← Finset.sum_filter, h_inner_sum, Finset.sum_image]
        exact fun τ _ τ' _ h => Equiv.Perm.ext fun i => by simpa using congr_fun h i
      rw [h_inner_sum, Matrix.det_apply', Matrix.det_apply']
      simp [Matrix.det_apply', Finset.sum_mul]
      refine' Finset.sum_bij (fun σ _ => σ⁻¹) _ _ _ _ <;> simp [Equiv.Perm.sign_inv]
      · exact fun b => ⟨b⁻¹, inv_inv b⟩
      · intro σ
        rw [← Equiv.prod_comp σ⁻¹]
        simp [mul_assoc, mul_left_comm, Finset.mul_sum]
        refine' Finset.sum_bij (fun τ _ => σ * τ) _ _ _ _ <;> simp [Equiv.Perm.sign_mul]
        · exact fun b => ⟨σ⁻¹ * b, by simp⟩
        · cases' Int.units_eq_one_or (Equiv.Perm.sign σ) with h h <;> simp [h]
    rw [h_cauchy_binet, h_split, h_group, Finset.sum_congr rfl fun S hS => h_inner S]
  /- The source's map l_t = n-j_t+t, using zero-based nodes l_t-1. -/
  let chainNodes {n m : ℕ} (j : Chain n m) : Fin m ↪o Fin (n + m) :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨n - (j.val i).val + i.val, by have := i.isLt; omega⟩)
      (by
        intro a b hab
        have hj := j.property (le_of_lt hab)
        have ha := (j.val a).isLt
        have hb := (j.val b).isLt
        change n - (j.val a).val + a.val < n - (j.val b).val + b.val
        change (j.val b).val ≤ (j.val a).val at hj
        change a.val < b.val at hab
        omega)
  
  /- Exact finite reindexing, with the inverse n+i-(l_i-1). -/
  let chainEquiv (n m : ℕ) : Chain n m ≃ NodeSet n m := by
    classical
    have gap (l : Fin m ↪o Fin (n + m)) :
        ∀ (a b : ℕ) (ha : a < m) (hb : b < m), a ≤ b →
          (l ⟨a, ha⟩).val + b ≤ (l ⟨b, hb⟩).val + a := by
      intro a b ha hb hab
      induction b, hab using Nat.le_induction with
      | base => omega
      | succ b hab ih =>
        have hbm : b < m := by omega
        have hs := l.strictMono (show (⟨b, hbm⟩ : Fin m) < ⟨b+1, hb⟩ from by
          change b < b + 1; omega)
        have hi := ih hbm
        change (l ⟨b, hbm⟩).val < (l ⟨b+1, hb⟩).val at hs
        omega
    have lower (l : Fin m ↪o Fin (n + m)) (i : Fin m) : i.val ≤ (l i).val := by
      have h := gap l 0 i.val (by have := i.isLt; omega) i.isLt (Nat.zero_le _)
      simp only [Fin.eta] at h
      omega
    have upper (l : Fin m ↪o Fin (n + m)) (i : Fin m) :
        (l i).val ≤ n + i.val := by
      have hm : 0 < m := by have := i.isLt; omega
      have h := gap l i.val (m-1) i.isLt (by omega) (by have := i.isLt; omega)
      simp only [Fin.eta] at h
      have hlast := (l ⟨m-1, by omega⟩).isLt
      omega
    let toSet : Chain n m → NodeSet n m := fun j =>
      ⟨univ.image (chainNodes j), by
        rw [card_image_of_injective _ (chainNodes j).injective]; simp⟩
    let toChain : NodeSet n m → Chain n m := fun s =>
      let l := s.val.orderEmbOfFin s.property
      ⟨fun i => ⟨n + i.val - (l i).val, by have := lower l i; omega⟩, by
        intro a b hab
        have h := gap l a.val b.val a.isLt b.isLt hab
        simp only [Fin.eta] at h
        have ha := upper l a
        have hb := upper l b
        change n + b.val - (l b).val ≤ n + a.val - (l a).val
        omega⟩
    refine ⟨toSet, toChain, ?_, ?_⟩
    · intro j
      have hsort : (toSet j).val.orderEmbOfFin (toSet j).property = chainNodes j :=
        (orderEmbOfFin_unique' _ (fun i => mem_image_of_mem _ (mem_univ i))).symm
      apply Subtype.ext
      funext i
      apply Fin.ext
      change n + i.val -
        ((toSet j).val.orderEmbOfFin (toSet j).property i).val = (j.val i).val
      rw [hsort]
      change n + i.val - (n - (j.val i).val + i.val) = (j.val i).val
      have := (j.val i).isLt
      omega
    · intro s
      have hnodes : chainNodes (toChain s) = s.val.orderEmbOfFin s.property := by
        ext i
        change n - (n + i.val - (s.val.orderEmbOfFin s.property i).val) + i.val =
          (s.val.orderEmbOfFin s.property i).val
        have := lower (s.val.orderEmbOfFin s.property) i
        have := upper (s.val.orderEmbOfFin s.property) i
        omega
      apply Subtype.ext
      change univ.image (chainNodes (toChain s)) = s.val
      rw [hnodes, image_orderEmbOfFin_univ]
  
  let weight (N m k : ℕ) : ℚ :=
    (-1 : ℚ) ^ k * (N.choose (k + 1) : ℚ) / ((k + 1 : ℕ) : ℚ) ^ m
  
  let delta {m : ℕ} (l : Fin m → ℕ) : ℚ :=
    ∏ q : Fin m, ∏ p ∈ Ioi q, ((l p : ℚ) - l q)
  
  /- Source normalization on a single chain, with every sign retained. -/
  have chain_normalization (n m : ℕ) (j : Chain n m) :
      (∏ i : Fin m, ((n + (i.val + 1) : ℕ) : ℚ) ^ (i.val + 1)) *
        sourceTerm j =
      (-1 : ℚ) ^ (m * (m - 1) / 2) *
        delta (fun i => (chainNodes j i).val) ^ 2 *
        ∏ i : Fin m, weight (n + m) m (chainNodes j i).val := by
    have prefactor (n m : ℕ) :
        (∏ i : Fin m, ((n + (i.val + 1) : ℕ) : ℚ) ^ (i.val + 1)) *
          (∏ i : Fin m, ((n + i.val).factorial : ℚ)) =
        ((n + m).factorial : ℚ) ^ m := by
      induction m with
      | zero => simp
      | succ m ih =>
        simp only [Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
        calc
          _ = ((∏ i : Fin m, ((n + (i.val + 1) : ℕ) : ℚ) ^ (i.val + 1)) *
              (∏ i : Fin m, ((n + i.val).factorial : ℚ))) *
              ((n + (m + 1) : ℕ) : ℚ) ^ (m + 1) * (n + m).factorial := by ring
          _ = _ := by
            rw [ih, show n + (m + 1) = (n + m) + 1 by omega, Nat.factorial_succ,
              Nat.cast_mul, mul_pow, pow_succ]
            ring
    have atom (i : Fin m) :
        ((n + i.val).descFactorial (j.val i).val : ℚ) /
          (((n - (j.val i).val + (i.val + 1) : ℕ) : ℚ) ^ (m + 1) *
            ((j.val i).val + m - (i.val + 1)).factorial) =
        ((n + i.val).factorial : ℚ) / (n + m).factorial *
          ((n + m).choose ((chainNodes j i).val + 1) : ℚ) /
            (((chainNodes j i).val + 1 : ℕ) : ℚ) ^ m := by
      have hj := (j.val i).isLt
      have hi := i.isLt
      let k := (chainNodes j i).val
      have hk : k = n - (j.val i).val + i.val := rfl
      have hA : n + i.val - (j.val i).val = k := by omega
      have hC : (j.val i).val + m - (i.val + 1) = n + m - (k + 1) := by omega
      have hL : n - (j.val i).val + (i.val + 1) = k + 1 := by omega
      have hkN : k + 1 ≤ n + m := by omega
      have hdesc : (k.factorial : ℚ) * (n + i.val).descFactorial (j.val i).val =
          (n + i.val).factorial := by
        exact_mod_cast (hA ▸ Nat.factorial_mul_descFactorial (show (j.val i).val ≤ n + i.val by omega))
      have hchoose : ((n + m).choose (k + 1) : ℚ) *
          (k + 1) * k.factorial * (n + m - (k + 1)).factorial =
          (n + m).factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial hkN
        rw [Nat.factorial_succ] at h
        have h' : (n + m).choose (k + 1) * (k + 1) * k.factorial *
            (n + m - (k + 1)).factorial = (n + m).factorial := by
          simpa only [mul_assoc] using h
        exact_mod_cast h'
      have hfac (a : ℕ) : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
      have hkp : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hd : ((n + i.val).descFactorial (j.val i).val : ℚ) =
          (n + i.val).factorial / (k.factorial : ℚ) := by
        apply (eq_div_iff (hfac k)).2
        simpa [mul_comm] using hdesc
      have hc : ((n + m).choose (k + 1) : ℚ) =
          (n + m).factorial /
            (((k + 1 : ℕ) : ℚ) * k.factorial * (n + m - (k + 1)).factorial) := by
        apply (eq_div_iff (mul_ne_zero (mul_ne_zero hkp (hfac k)) (hfac _))).2
        simpa [mul_assoc] using hchoose
      change _ = (n + i.val).factorial / (n + m).factorial *
        ((n + m).choose (k + 1) : ℚ) / ((k + 1 : ℕ) : ℚ) ^ m
      rw [hd, hC, hL, hc, pow_succ]
      field_simp
    have sign : (-1 : ℚ) ^ (n * m + ∑ i, (j.val i).val) =
        (-1 : ℚ) ^ (m * (m - 1) / 2) *
          ∏ i : Fin m, (-1 : ℚ) ^ (chainNodes j i).val := by
      have hs : (∑ i : Fin m, (j.val i).val) +
          (∑ i : Fin m, (chainNodes j i).val) =
          n * m + m * (m - 1) / 2 := by
        rw [← sum_add_distrib]
        calc
          _ = ∑ i : Fin m, (n + i.val) := by
            apply sum_congr rfl
            intro i _
            change (j.val i).val + (n - (j.val i).val + i.val) = n + i.val
            have := (j.val i).isLt
            omega
          _ = _ := by
            simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
            rw [mul_comm m n]
            congr 1
            exact (Fin.sum_univ_eq_sum_range (fun i => i) m).trans (sum_range_id m)
      rw [prod_pow_eq_pow_sum, ← pow_add]
      conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
      conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
      congr 1
      omega
    have vand : (∏ q : Fin m, ∏ p ∈ Ioi q,
        (((j.val q).val : ℚ) - (j.val p).val + p.val - q.val) ^ 2) =
        delta (fun i => (chainNodes j i).val) ^ 2 := by
      unfold delta
      rw [← prod_pow]
      apply prod_congr rfl
      intro q _
      rw [← prod_pow]
      apply prod_congr rfl
      intro p _
      congr 1
      change _ = ((n - (j.val p).val + p.val : ℕ) : ℚ) -
        ((n - (j.val q).val + q.val : ℕ) : ℚ)
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by have := (j.val p).isLt; omega),
        Nat.cast_sub (by have := (j.val q).isLt; omega)]
      ring
    simp only [sourceTerm, atom, sign, vand, weight]
    simp only [prod_div_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    have hF : ((n + m).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+m)
    have hp := prefactor n m
    field_simp
    calc
      _ = ((∏ i : Fin m, ((n + (i.val + 1) : ℕ) : ℚ) ^ (i.val + 1)) *
          (∏ i : Fin m, ((n + i.val).factorial : ℚ))) *
          delta (fun i => (chainNodes j i).val) ^ 2 *
          (∏ i : Fin m, ((n + m).choose ((chainNodes j i).val + 1) : ℚ)) := by ring
      _ = _ := by rw [hp]; ring
  
  /- Integer-indexed signed rational moments. -/
  let moment (N : ℕ) (k : ℤ) : ℚ :=
    ∑ l : Fin N, (-1 : ℚ) ^ l.val * (N.choose (l.val + 1) : ℚ) *
      (((l.val + 1 : ℕ) : ℚ) ^ (-k))
  
  let momentMatrix (n m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
    fun i j => moment (n + m) ((m : ℤ) - (i.val : ℤ) - (j.val : ℤ))
  
  /- The exact source expression reduces to the signed moment determinant.
  This is a bridge only: the determinant evaluation is not assumed or proved here. -/
  have source_to_moment (n m : ℕ) :
      sourceRHS n m = ((n + m).factorial : ℚ) *
        (-1 : ℚ) ^ (m * (m - 1) / 2) * (momentMatrix n m).det := by
    classical
    let A : Matrix (Fin m) (Fin (n + m)) ℚ := fun i l => ((l.val + 1 : ℕ) : ℚ) ^ i.val
    let B : Matrix (Fin (n + m)) (Fin m) ℚ := fun l j =>
      weight (n + m) m l.val * ((l.val + 1 : ℕ) : ℚ) ^ j.val
    have factor : momentMatrix n m = A * B := by
      ext i j
      simp only [momentMatrix, moment, A, B, weight]
      apply sum_congr rfl
      intro l _
      have hl : ((l.val + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [show -((m : ℤ) - i.val - j.val) = (i.val : ℤ) + j.val - m by ring,
        zpow_sub₀ hl, zpow_add₀ hl]
      simp only [zpow_natCast]
      ring
    have minor (s : NodeSet n m) :
        (A.submatrix id (s.val.orderEmbOfFin s.property)).det *
          (B.submatrix (s.val.orderEmbOfFin s.property) id).det =
        delta (fun i => (s.val.orderEmbOfFin s.property i).val) ^ 2 *
          ∏ i : Fin m, weight (n + m) m (s.val.orderEmbOfFin s.property i).val := by
      let l := s.val.orderEmbOfFin s.property
      let v : Fin m → ℚ := fun i => ((l i).val + 1 : ℕ)
      have ha : A.submatrix id l = (Matrix.vandermonde v).transpose := rfl
      have hb : B.submatrix l id =
          Matrix.of (fun i j => weight (n + m) m (l i).val * Matrix.vandermonde v i j) := rfl
      have hv : (Matrix.vandermonde v).det = delta (fun i => (l i).val) := by
        rw [Matrix.det_vandermonde]
        unfold delta
        apply prod_congr rfl
        intro q _
        apply prod_congr rfl
        intro p _
        simp only [v, Nat.cast_add, Nat.cast_one]
        ring
      rw [ha, hb, Matrix.det_transpose, Matrix.det_mul_column, hv]
      ring
    have reindex :
        (∑ j : Chain n m, delta (fun i => (chainNodes j i).val) ^ 2 *
          ∏ i : Fin m, weight (n + m) m (chainNodes j i).val) =
        ∑ s : NodeSet n m, delta (fun i => (s.val.orderEmbOfFin s.property i).val) ^ 2 *
          ∏ i : Fin m, weight (n + m) m (s.val.orderEmbOfFin s.property i).val := by
      apply Fintype.sum_equiv (chainEquiv n m)
      intro j
      have hs : (chainEquiv n m j).val.orderEmbOfFin (chainEquiv n m j).property =
          chainNodes j :=
        (orderEmbOfFin_unique' _ (fun i => mem_image_of_mem _ (mem_univ i))).symm
      rw [hs]
    rw [sourceRHS, factor, cauchyBinet]
    simp_rw [minor]
    rw [← reindex, mul_assoc, mul_assoc, mul_sum]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [chain_normalization]
    ring
  
  /- Includes the zero moment and all required negative moments. -/
  have nonpositive_moments (N r : ℕ) (hr : r < N) :
      moment N (-(r : ℤ)) = if r = 0 then 1 else 0 := by
    have hs := D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion r N
    rw [Nat.stirlingSecond_eq_zero_of_lt hr] at hs
    simp only [Nat.cast_zero, mul_zero] at hs
    have hsQ : (∑ k ∈ range (N + 1), (-1 : ℚ) ^ (N-k) *
        (N.choose k : ℚ) * (k : ℚ) ^ r) = 0 := by exact_mod_cast hs.symm
    have hs' : (∑ k ∈ range (N + 1), (-1 : ℚ) ^ k *
        (N.choose k : ℚ) * (k : ℚ) ^ r) = 0 := by
      have h := congrArg (fun x : ℚ => (-1 : ℚ) ^ N * x) hsQ
      rw [mul_zero, mul_sum] at h
      convert h using 1
      apply sum_congr rfl
      intro k hk
      have hkN : k ≤ N := by simpa using mem_range.mp hk
      have hsign : (-1 : ℚ) ^ k = (-1 : ℚ) ^ N * (-1 : ℚ) ^ (N-k) := by
        rw [← pow_add]
        conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
        conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
        congr 1
        omega
      rw [hsign]
      ring
    rw [sum_range_succ'] at hs'
    simp only [pow_succ, neg_mul, mul_neg, one_mul, mul_one, Nat.cast_zero,
      pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at hs'
    simp only [moment, neg_neg, zpow_natCast]
    rw [Fin.sum_univ_eq_sum_range
      (fun l : ℕ => (-1 : ℚ) ^ l * (N.choose (l+1) : ℚ) * ((l+1 : ℕ) : ℚ) ^ r) N]
    simp only [Nat.cast_add, Nat.cast_one] at hs' ⊢
    rw [sum_neg_distrib] at hs'
    split_ifs with h
    · subst r
      simp only [pow_zero, mul_one] at hs' ⊢
      linarith
    · rw [zero_pow h, add_zero, neg_eq_zero] at hs'
      exact hs'
  
  /- Pascal's identity supplies the complete-homogeneous moment recurrence. -/
  have moment_recurrence (N : ℕ) (k : ℤ) :
      (N + 1 : ℚ) * moment (N + 1) (k + 1) =
        (N + 1 : ℚ) * moment N (k + 1) + moment (N + 1) k := by
    have term (l : ℕ) (hl : l < N + 1) :
        (N + 1 : ℚ) * ((-1 : ℚ) ^ l * ((N+1).choose (l+1) : ℚ) *
          ((l+1 : ℕ) : ℚ) ^ (-(k+1))) -
        ((-1 : ℚ) ^ l * ((N+1).choose (l+1) : ℚ) * ((l+1 : ℕ) : ℚ) ^ (-k)) =
        (N + 1 : ℚ) * ((-1 : ℚ) ^ l * (N.choose (l+1) : ℚ) *
          ((l+1 : ℕ) : ℚ) ^ (-(k+1))) := by
      have hc := congrArg (fun x : ℕ => (x : ℚ)) (Nat.choose_mul_succ_eq N (l+1))
      simp only [Nat.cast_mul, Nat.cast_sub (by omega : l+1 ≤ N+1), Nat.cast_add,
        Nat.cast_one] at hc
      have hp : ((l+1 : ℕ) : ℚ) ^ (-k) =
          ((l+1 : ℕ) : ℚ) * ((l+1 : ℕ) : ℚ) ^ (-(k+1)) := by
        calc
          _ = ((l+1 : ℕ) : ℚ) ^ ((1 : ℤ) + (-(k+1))) := by congr 1; ring
          _ = _ := by rw [zpow_add₀ (by positivity : ((l+1 : ℕ) : ℚ) ≠ 0), zpow_one]
      rw [hp]
      push_cast
      linear_combination -((-1 : ℚ) ^ l * (l+1 : ℚ) ^ (-(k+1))) * hc
    apply sub_eq_iff_eq_add.mp
    unfold moment
    rw [Fin.sum_univ_eq_sum_range
      (fun l : ℕ => (-1 : ℚ) ^ l * ((N+1).choose (l+1) : ℚ) * ((l+1 : ℕ) : ℚ) ^ (-(k+1))) (N+1),
      Fin.sum_univ_eq_sum_range
      (fun l : ℕ => (-1 : ℚ) ^ l * ((N+1).choose (l+1) : ℚ) * ((l+1 : ℕ) : ℚ) ^ (-k)) (N+1),
      Fin.sum_univ_eq_sum_range
      (fun l : ℕ => (-1 : ℚ) ^ l * (N.choose (l+1) : ℚ) * ((l+1 : ℕ) : ℚ) ^ (-(k+1))) N]
    rw [mul_sum, ← sum_sub_distrib]
    rw [sum_congr rfl (fun l hl => term l (mem_range.mp hl))]
    rw [sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N), Nat.cast_zero,
      mul_zero, zero_mul, mul_zero, add_zero, mul_sum]
  
  let hessenberg (N m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
    fun i j => moment N (1 + (i.val : ℤ) - j.val)
  
  have source_to_hessenberg (n m : ℕ) :
      sourceRHS n m = ((n + m).factorial : ℚ) * (hessenberg (n + m) m).det := by
    have hsign : Equiv.Perm.sign (@Fin.revPerm m) = (-1 : ℤˣ) ^ (m * (m-1) / 2) := by
      rw [Equiv.Perm.sign_eq_prod_prod_Iio]
      calc
        _ = ∏ j : Fin m, (-1 : ℤˣ) ^ j.val := by
          apply prod_congr rfl
          intro j _
          calc
            _ = ∏ i ∈ Iio j, (-1 : ℤˣ) := by
              apply prod_congr rfl
              intro i hi
              have hij : i < j := mem_Iio.mp hi
              simp only [Fin.revPerm_apply, Fin.rev_lt_rev, not_lt_of_ge hij.le, ↓reduceIte]
            _ = _ := by rw [prod_const, Fin.card_Iio]
        _ = _ := by
          rw [prod_pow_eq_pow_sum]
          congr 1
          exact (Fin.sum_univ_eq_sum_range (fun i => i) m).trans (sum_range_id m)
    have hrev : hessenberg (n + m) m = (momentMatrix n m).submatrix Fin.revPerm id := by
      ext i j
      simp only [hessenberg, momentMatrix]
      congr 1
      have hi := i.isLt
      simp only [Fin.revPerm_apply, Fin.val_rev, id_eq]
      omega
    rw [source_to_moment, hrev, Matrix.det_permute, hsign]
    simp only [Units.val_pow_eq_pow_val, Int.cast_pow, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one]
    ring
  
  /- A Hessenberg determinant recurrence obtained by a unit triangular column operation. -/
  have hessenberg_recurrence (N d : ℕ) (hd : d + 1 ≤ N + 1) :
      (hessenberg (N+1) (d+1)).det = (hessenberg N (d+1)).det +
        (N+1 : ℚ)⁻¹ * (hessenberg N d).det := by
    classical
    let H := hessenberg (N+1) (d+1)
    let G := hessenberg N (d+1)
    let c : ℚ := (N+1 : ℚ)⁻¹
    let C : Matrix (Fin (d+1)) (Fin (d+1)) ℚ :=
      fun i j => (if i = j then 1 else 0) - (if i.val = j.val + 1 then c else 0)
    have hC : C.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular C]
      · simp only [C, ↓reduceIte, show ∀ i : Fin (d+1), ¬ i.val = i.val + 1 by omega,
          sub_zero, prod_const_one]
      · intro i j hij
        have hij' : i.val < j.val := hij
        have hne : i ≠ j := by intro h; subst j; omega
        simp only [C, if_neg hne, if_neg (by omega : ¬ i.val = j.val + 1), sub_self]
    have hc : (N+1 : ℚ) ≠ 0 := by positivity
    have entry (i j : Fin (d+1)) :
        H i j - c * moment (N+1) ((i.val : ℤ) - j.val) = G i j := by
      have h := moment_recurrence N ((i.val : ℤ) - j.val)
      have he : (i.val : ℤ) - j.val + 1 = 1 + i.val - j.val := by ring
      rw [he] at h
      change moment (N+1) (1 + (i.val : ℤ) - j.val) -
        (N+1 : ℚ)⁻¹ * moment (N+1) ((i.val : ℤ) - j.val) =
        moment N (1 + (i.val : ℤ) - j.val)
      field_simp
      linear_combination h
    have lastmoment (i : Fin (d+1)) :
        moment (N+1) ((i.val : ℤ) - d) = if i = Fin.last d then 1 else 0 := by
      have h := nonpositive_moments (N+1) (d-i.val) (by have := i.isLt; omega)
      have he : (i.val : ℤ) - d = -((d-i.val : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by have := i.isLt; omega)]; ring
      rw [he, h]
      congr 1
      apply propext
      constructor
      · intro h
        apply Fin.ext
        have := i.isLt
        simp only [Fin.val_last]
        omega
      · intro h; subst i; simp
    have product : H * C = Matrix.updateCol G (Fin.last d)
        (fun i => G i (Fin.last d) + c * (if i = Fin.last d then 1 else 0)) := by
      ext i j
      change (∑ k, H i k * C k j) = _
      simp only [C, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
        sum_ite_eq', mem_univ, ↓reduceIte]
      by_cases hj : j = Fin.last d
      · subst j
        have hz : (∑ k : Fin (d+1), if k.val = d+1 then H i k * c else 0) = 0 := by
          apply sum_eq_zero
          intro k _
          rw [if_neg (by have := k.isLt; omega)]
        simp only [Fin.val_last] at *
        rw [hz, sub_zero, Matrix.updateCol_self]
        have he := entry i (Fin.last d)
        simp only [Fin.val_last, lastmoment, mul_ite, mul_one, mul_zero] at he
        linarith
      · have hj' : j.val + 1 < d+1 := by
          have := j.isLt
          have : j.val ≠ d := by intro h; apply hj; exact Fin.ext h
          omega
        let j' : Fin (d+1) := ⟨j.val+1, hj'⟩
        have hz : (∑ k : Fin (d+1), if k.val = j.val+1 then H i k * c else 0) = H i j' * c := by
          rw [sum_eq_single j']
          · simp [j']
          · intro b _ hb
            rw [if_neg (by intro h; apply hb; exact Fin.ext h)]
          · simp
        rw [hz, Matrix.updateCol_ne hj]
        have he := entry i j
        have he' : H i j' = moment (N+1) ((i.val : ℤ) - j.val) := by
          dsimp [H, hessenberg, j']
          congr 1
          ring
        rw [he', mul_comm]
        exact he
    have hdet := congrArg Matrix.det product
    rw [Matrix.det_mul, hC, mul_one] at hdet
    have hcol : (fun i => G i (Fin.last d) + c * (if i = Fin.last d then 1 else 0)) =
        (fun i => G i (Fin.last d)) + c • (Pi.single (Fin.last d) 1) := by
      funext i
      simp [Pi.single_apply]
    rw [hcol, Matrix.det_updateCol_add, Matrix.updateCol_eq_self, Matrix.det_updateCol_smul] at hdet
    rw [hdet]
    congr 2
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp only [Matrix.mulVec_single_one]
    change G.adjugate (Fin.last d) (Fin.last d) = _
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.val_last, pow_add, ← mul_pow, neg_mul_neg, one_mul, one_pow,
      Fin.succAbove_last]
    rfl
  
  /- Too few nodes force the larger moment determinant to vanish. -/
  have hessenberg_rank (N m : ℕ) (hm : N < m) : (hessenberg N m).det = 0 := by
    classical
    let A : Matrix (Fin m) (Fin N) ℚ :=
      fun i l => ((l.val + 1 : ℕ) : ℚ) ^ (-(i.val : ℤ))
    let B : Matrix (Fin N) (Fin m) ℚ :=
      fun l j => (-1 : ℚ) ^ l.val * (N.choose (l.val+1) : ℚ) *
        ((l.val+1 : ℕ) : ℚ) ^ ((j.val : ℤ) - 1)
    have factor : hessenberg N m = A * B := by
      ext i j
      change (∑ l : Fin N, _) = ∑ l : Fin N, _
      apply sum_congr rfl
      intro l _
      dsimp [A, B]
      rw [show -(1 + (i.val : ℤ) - j.val) = -(i.val : ℤ) + ((j.val : ℤ) - 1) by ring,
        zpow_add₀ (by positivity : ((l.val+1 : ℕ) : ℚ) ≠ 0)]
      ring
    rw [factor, cauchyBinet]
    apply sum_eq_zero
    intro s _
    have hc := card_le_univ s.val
    simp only [Fintype.card_fin, s.property] at hc
    omega
  
  /- The scaled determinant follows the unsigned Stirling recurrence. -/
  have hessenberg_stirling (N m : ℕ) :
      (N.factorial : ℚ) * (hessenberg N m).det =
        (Nat.stirlingFirst (N+1) (m+1) : ℚ) := by
    induction N generalizing m with
    | zero =>
      cases m with
      | zero => simp [Matrix.det_fin_zero, Nat.stirlingFirst_self]
      | succ d =>
        rw [hessenberg_rank 0 (d+1) (by omega), mul_zero,
          Nat.stirlingFirst_eq_zero_of_lt (by omega : 0+1 < (d+1)+1)]
        rfl
    | succ N ih =>
      cases m with
      | zero => simp [Matrix.det_fin_zero, Nat.stirlingFirst_one_right]
      | succ d =>
        by_cases hd : d+1 ≤ N+1
        · rw [hessenberg_recurrence N d hd, Nat.factorial_succ,
            Nat.stirlingFirst_succ_succ (N+1) (d+1)]
          push_cast
          have hc : (N+1 : ℚ) ≠ 0 := by positivity
          calc
            _ = (N+1 : ℚ) * ((N.factorial : ℚ) * (hessenberg N (d+1)).det) +
                (N.factorial : ℚ) * (hessenberg N d).det := by field_simp
            _ = _ := by rw [ih (d+1), ih d]
        · rw [hessenberg_rank (N+1) (d+1) (by omega), mul_zero,
            Nat.stirlingFirst_eq_zero_of_lt (by omega : (N+1)+1 < (d+1)+1)]
          rfl
  
  rw [source_to_hessenberg, hessenberg_stirling]

end D5.S1.Recurrence.Algebraic.KurkovNestedStirlingIdentity

