/- GID: D5/S3/ArithSums/LogLaplacianBellNonvanishing
   generality: G
   mirror-B: D5/B/S3/ArithSums/LogLaplacianBellNonvanishing
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Bell values of Rosenzweig-Stanfill Open Problem 1.3 never vanish. -/

/-
proof_shape: result: content; scaledEntry_pos_val: content; scaled_pBell: content
escape_witness: form (1): scaledEntry_pos_val is W1, the strict positive
  valuation of every nonprincipal scaled Bell profile (route v2 of #11490);
  scaled_pBell is W2, the scaled-sum identity linking the paper's defining
  Bell sum to the normalised profile sum (route v2 of #11490).
admission_basis: open-problem-resolution (#11490; Proved)
Direct frozen dependencies: none (pinned Mathlib only). Upstream owners
actually applied: Bernoulli.vonStaudt_clausen, Nat.prod_factorial_dvd_factorial_sum,
Nat.factorization_prod_apply, Nat.factorization_def, Nat.factorial_dvd_factorial,
Finset.sum_lt_sum, padicValNat_factorial_mul, padicValRat.add_eq_of_lt,
padicValRat.min_le_padicValRat_add, padicValRat.mul, padicValRat.div,
padicValRat.pow, padicValRat.zpow, and Fintype.sum_equiv.
Private theorem/lemma declarations: scaledEntry_pos_val (W1) and scaled_pBell
(W2), both genuine content and consumed on result's live proof path. All other
coefficient valuations, factorial-valuation estimates and ultrametric facts
remain local have statements in the proof that consumes each fact.
Private definitions: profileEquiv constructs and verifies the finite-profile
representation of the paper's literal natural-sequence sum.
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.LogLaplacianBellNonvanishing

open scoped BigOperators
open Finset

/-- Natural sequences with the two constraints in the paper's ordinary Bell sum.
The zero-based index i represents the paper's index i+1; n-k is natural subtraction. -/
def BellProfile (n k : ℕ) :=
  {r : Fin (n-k+1) → ℕ // (∑ i, r i) = k ∧ (∑ i, (i.val+1)*r i) = n}

private def bellProfiles (n k : ℕ) : Finset (Fin (n-k+1) → Fin (k+1)) :=
  Finset.univ.filter fun j =>
    (∑ i, (j i : ℕ)) = k ∧ (∑ i, (i.val+1) * (j i : ℕ)) = n

private def profileEquiv (n k : ℕ) :
    {j : Fin (n-k+1) → Fin (k+1) // j ∈ bellProfiles n k} ≃ BellProfile n k where
  toFun j := ⟨fun i => (j.val i).val, (mem_filter.mp j.property).2⟩
  invFun r := ⟨fun i => ⟨r.val i, by
    have hle : r.val i ≤ ∑ j, r.val j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    rw [r.property.1] at hle
    omega⟩, by
      apply mem_filter.mpr
      exact ⟨mem_univ _, r.property⟩⟩
  left_inv j := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv r := by
    apply Subtype.ext
    rfl

private noncomputable instance literalProfileFintype (n k : ℕ) : Fintype (BellProfile n k) :=
  Fintype.ofEquiv {j : Fin (n-k+1) → Fin (k+1) // j ∈ bellProfiles n k} (profileEquiv n k)

/-- The partial ordinary Bell polynomial, with exactly its natural-sequence defining sum. -/
noncomputable def bellOrdinary (n k : ℕ) (s : ℕ → ℚ) : ℚ :=
  ∑ r : BellProfile n k,
    ((k.factorial : ℚ) / ∏ i, ((r.val i).factorial : ℚ)) *
      ∏ i, s (i.val+1)^r.val i

/-- The first defining expression of Definition 1.1 (the Bell-polynomial expression). -/
noncomputable def pBell (n : ℕ) (s : ℕ → ℚ) (t : ℚ) : ℚ :=
  ∑ k ∈ range (n+1), ((-1 : ℚ)^k / (k.factorial : ℚ)) * bellOrdinary n k s * t^k

/-- Equation (1.8), with Mathlib's Bernoulli convention B₁ = -1/2.
The integer exponent makes 1-k signed; k=0 is unused and is assigned the rational value 0. -/
def S1 (k : ℕ) : ℚ :=
  (1-(2 : ℚ)^((1 : ℤ)-(k : ℤ))) * (2 * bernoulli k) / (k : ℚ)

/-- Open Problem 1.3: the paper uses positive natural m. -/
def claim : Prop := ∀ m : ℕ, 1 ≤ m → pBell (2*m) S1 ((1:ℚ)/2-m) ≠ 0

private def aParam (m : ℕ) : ℚ := (2*(m:ℚ)-1)/2

private def bCoeff (m n : ℕ) : ℚ := 24^n * aParam m * S1 (2*n)

private def scaledEntry (m : ℕ) {L : ℕ} (r : Fin L → ℕ) : ℚ :=
  (m.factorial : ℚ) * (∏ i, bCoeff m ((i.val+1)/2) ^ r i) /
    ∏ i, ((r i).factorial : ℚ)

private def rawEntry (m : ℕ) {L : ℕ} (r : Fin L → ℕ) : ℚ :=
  24^m * (m.factorial : ℚ) * (∏ i, (aParam m * S1 (i.val+1)) ^ r i) /
    ∏ i, ((r i).factorial : ℚ)

private def mainProfile (m : ℕ) : Fin (2*m-m+1) → Fin (m+1) :=
  fun i => if i.val = 1 then ⟨m, by omega⟩ else 0

/-- W1: nonprincipal even profiles have strictly positive scaled valuation. -/
private theorem scaledEntry_pos_val {m L : ℕ} (hm : 0 < m) (r : Fin L → ℕ)
    (hw : ∑ i, (i.val + 1) * r i = 2 * m)
    (ho : ∀ i, Odd (i.val + 1) → r i = 0)
    (hex : ∃ i, 2 ≤ (i.val + 1) / 2 ∧ 0 < r i) :
    0 < padicValRat 2 (scaledEntry m r) := by
  have bCoeff_val (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      bCoeff m n ≠ 0 ∧ padicValRat 2 (bCoeff m n) = (n:ℤ)-1-padicValNat 2 n := by
    have val_sum_ge {α : Type} (s : Finset α) (f : α → ℚ) (a : ℤ)
        (h : ∀ i ∈ s, f i ≠ 0 → a ≤ padicValRat 2 (f i))
        (hne : s.sum f ≠ 0) : a ≤ padicValRat 2 (s.sum f) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp at hne
      | @insert i s hi ih =>
        rw [sum_insert hi] at hne ⊢
        by_cases hf : f i = 0
        · simp only [hf, zero_add] at hne ⊢
          exact ih (fun j hj => h j (by simp [hj])) hne
        by_cases hs : s.sum f = 0
        · simpa [hs] using h i (by simp) hf
        exact le_trans (le_min (h i (by simp) hf)
          (ih (fun j hj => h j (by simp [hj])) hs))
          (padicValRat.min_le_padicValRat_add hne)
    have val_add_ne {x y : ℚ} (hx : x ≠ 0)
        (hy : y ≠ 0 → padicValRat 2 x < padicValRat 2 y) : x+y ≠ 0 := by
      intro hz
      have he : y = -x := by linarith
      have hyn : y ≠ 0 := by simp [he, hx]
      have hv := hy hyn
      rw [he, padicValRat.neg] at hv
      exact lt_irrefl _ hv
    have bernoulli_val_two (n : ℕ) (hn : 0 < n) :
        padicValRat 2 (bernoulli (2*n)) = -1 := by
      let s := (range (2*n+2)).filter fun p => p.Prime ∧ (p-1) ∣ 2*n
      have h2 : 2 ∈ s := by simp [s, Nat.prime_two]; omega
      obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen n
      have hr : ∀ p ∈ s.erase 2, 0 ≤ padicValRat 2 ((1:ℚ)/p) := by
        intro p hp
        have hprime : p.Prime := ((mem_filter.mp (mem_of_mem_erase hp)).2).1
        have hp2 : p ≠ 2 := (mem_erase.mp hp).1
        have hd : ¬ 2 ∣ p := fun hd => hp2 ((hprime.dvd_iff_eq (by decide)).mp hd)
        rw [padicValRat.div (by norm_num) (Nat.cast_ne_zero.mpr hprime.ne_zero),
          padicValRat.one, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
        simp
      have hsum : ∑ p ∈ s, (1:ℚ)/p = 1/2 + ∑ p ∈ s.erase 2, (1:ℚ)/p := by
        rw [← sum_erase_add _ _ h2]
        ring
      have he : bernoulli (2*n) = -(1/2 : ℚ) +
          ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) := by
        change (z : ℚ) = bernoulli (2*n) + ∑ p ∈ s, (1:ℚ)/p at hz
        rw [hsum] at hz
        linarith
      have hb : padicValRat 2 (-(1/2 : ℚ)) = -1 := by
        rw [padicValRat.neg, one_div, padicValRat.inv]
        change -padicValRat 2 ((2 : ℕ) : ℚ) = -1
        rw [padicValRat.of_nat, padicValNat_self]
        norm_num
      have hrest : ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) ≠ 0 →
          0 ≤ padicValRat 2 ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) := by
        intro hne
        rw [sub_eq_add_neg] at hne ⊢
        apply le_trans (le_min (by simp [padicValRat.of_int]) ?_)
          (padicValRat.min_le_padicValRat_add hne)
        rw [padicValRat.neg]
        by_cases hs : ∑ p ∈ s.erase 2, (1:ℚ)/p = 0
        · rw [hs]; simp
        exact val_sum_ge _ _ 0 (fun p hp _ => hr p hp) hs
      rw [he]
      by_cases hr0 : (z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p = 0
      · rw [hr0, add_zero]; exact hb
      have hlt : padicValRat 2 (-(1/2 : ℚ)) <
          padicValRat 2 ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) := by
        rw [hb]; exact lt_of_lt_of_le (by norm_num) (hrest hr0)
      exact (padicValRat.add_eq_of_lt (val_add_ne (by norm_num) (fun _ => hlt))
        (by norm_num) hr0 hlt).trans hb
    have val_two : padicValRat 2 (2:ℚ) = 1 := by
      change padicValRat 2 ((2:ℕ):ℚ) = 1
      rw [padicValRat.of_nat, padicValNat_self]
      norm_num
    have S1_even_val (n : ℕ) (hn : 0 < n) :
        S1 (2*n) ≠ 0 ∧ padicValRat 2 (S1 (2*n)) = -2*(n:ℤ) - padicValNat 2 n := by
      have hb := bernoulli_val_two n hn
      have hbn : bernoulli (2*n) ≠ 0 := by intro h; rw [h, padicValRat.zero] at hb; omega
      let e : ℤ := 1-2*(n:ℤ)
      have he : e < 0 := by dsimp [e]; omega
      have hp : padicValRat 2 (-(2 : ℚ)^e) = e := by
        rw [padicValRat.neg, padicValRat.zpow, val_two]
        ring
      have hx : -(2 : ℚ)^e ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero _ (by norm_num))
      have hlt : padicValRat 2 (-(2 : ℚ)^e) < padicValRat 2 (1 : ℚ) := by simpa [hp] using he
      have hnon : -(2 : ℚ)^e + 1 ≠ 0 := val_add_ne hx (fun _ => hlt)
      have hv := padicValRat.add_eq_of_lt hnon hx (by norm_num) hlt
      have hargs : 1-(2 : ℚ)^e = -(2 : ℚ)^e+1 := by ring
      have hv' : padicValRat 2 (1-(2 : ℚ)^e) = e := by
        rw [hargs]
        exact hv.trans hp
      have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have ht : (2*n : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hn'
      have hf : 1-(2 : ℚ)^e ≠ 0 := by
        rw [hargs]
        exact hnon
      have hdef : S1 (2*n) = (1-(2 : ℚ)^e) * (2 * bernoulli (2*n)) / (2*(n:ℚ)) := by
        simp only [S1, Nat.cast_mul, Nat.cast_ofNat, e]
      rw [hdef]
      refine ⟨div_ne_zero (mul_ne_zero hf (mul_ne_zero (by norm_num) hbn)) ht, ?_⟩
      rw [padicValRat.div (mul_ne_zero hf (mul_ne_zero (by norm_num) hbn)) ht,
        padicValRat.mul hf (mul_ne_zero (by norm_num) hbn),
        padicValRat.mul (by norm_num) hbn, padicValRat.mul (by norm_num) hn',
        hv', hb, val_two, padicValRat.of_nat]
      dsimp [e]
      ring
    have aParam_val (m : ℕ) (hm : 0 < m) :
        aParam m ≠ 0 ∧ padicValRat 2 (aParam m) = -1 := by
      have hn : (2*(m:ℚ)-1) ≠ 0 := by
        have h : (1:ℚ) ≤ m := by exact_mod_cast hm
        linarith
      have hv : padicValRat 2 (2*(m:ℚ)-1) = 0 := by
        have he : 2*(m:ℚ)-1 = ((2*(m:ℤ)-1 : ℤ) : ℚ) := by norm_cast
        rw [he, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
        · simp
        · intro h; obtain ⟨z, hz⟩ := h; omega
      refine ⟨div_ne_zero hn (by norm_num), ?_⟩
      rw [aParam, padicValRat.div hn (by norm_num), hv, val_two]
      norm_num
    obtain ⟨han, ha⟩ := aParam_val m hm
    obtain ⟨hsn, hs⟩ := S1_even_val n hn
    have h24 : padicValRat 2 (24:ℚ) = 3 := by
      change padicValRat 2 ((24:ℕ):ℚ) = 3
      rw [padicValRat.of_nat]
      have : padicValNat 2 24 = 3 := by decide +kernel
      norm_num [this]
    refine ⟨mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) han) hsn, ?_⟩
    rw [bCoeff, padicValRat.mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) han) hsn,
      padicValRat.mul (pow_ne_zero _ (by norm_num)) han,
      padicValRat.pow, h24, ha, hs]
    ring
  have bCoeff_nonneg (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      0 ≤ padicValRat 2 (bCoeff m n) := by
    rw [(bCoeff_val m n hm hn).2]
    have h : padicValNat 2 n < n :=
      lt_of_le_of_lt (padicValNat_le_nat_log n) (Nat.log_lt_self 2 hn.ne')
    omega
  have val_prod {α : Type} (s : Finset α) (f : α → ℚ)
      (hf : ∀ i ∈ s, f i ≠ 0) :
      padicValRat 2 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat 2 (f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [prod_insert hi, sum_insert hi,
        padicValRat.mul (hf i (by simp)) (Finset.prod_ne_zero_iff.mpr
          (fun j hj => hf j (by simp [hj]))), ih (fun j hj => hf j (by simp [hj]))]
  have profile_weight {m L : ℕ} (r : Fin L → ℕ)
      (hw : ∑ i, (i.val+1)*r i = 2*m)
      (ho : ∀ i, Odd (i.val+1) → r i = 0) :
      (∑ i, ((i.val+1)/2)*r i) = m := by
    have he : ∀ i, (i.val+1)*r i = 2 * (((i.val+1)/2)*r i) := by
      intro i
      by_cases hz : r i = 0
      · simp [hz]
      have hno : ¬ Odd (i.val+1) := fun h => hz (ho i h)
      have hmod : (i.val+1)%2 = 0 := by
        have := Nat.even_or_odd (i.val+1)
        rcases this with h | h
        · exact Nat.even_iff.mp h
        · exact (hno h).elim
      have hi : i.val+1 = 2*((i.val+1)/2) := by omega
      calc
        _ = (2*((i.val+1)/2))*r i := congrArg (fun x => x*r i) hi
        _ = _ := by ring
    simp_rw [he] at hw
    rw [← Finset.mul_sum] at hw
    omega
  have scaledEntry_val {m L : ℕ} (hm : 0 < m) (r : Fin L → ℕ)
      (ho : ∀ i, Odd (i.val+1) → r i = 0) :
      padicValRat 2 (scaledEntry m r) = (padicValNat 2 m.factorial : ℤ) -
        ∑ i, (padicValNat 2 (r i).factorial : ℤ) +
        ∑ i, (r i : ℤ) * padicValRat 2 (bCoeff m ((i.val+1)/2)) := by
    have hf : ∀ i : Fin L, bCoeff m ((i.val+1)/2)^r i ≠ 0 := by
      intro i
      by_cases hz : r i = 0
      · simp [hz]
      have hw : 0 < (i.val+1)/2 := by
        have hno : ¬ Odd (i.val+1) := fun h => hz (ho i h)
        by_contra h
        have hi : i.val = 0 := by omega
        exact hno (by simp [hi])
      exact pow_ne_zero _ (bCoeff_val m _ hm hw).1
    rw [scaledEntry, padicValRat.div
      (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))),
      padicValRat.mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)),
      padicValRat.of_nat, val_prod _ _ (fun i _ => hf i),
      val_prod _ _ (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    simp_rw [padicValRat.pow, padicValRat.of_nat]
    ring
  rw [scaledEntry_val hm r ho]
  have hmono : ∀ i : Fin L, r i ≤ ((i.val+1)/2)*r i := by
    intro i
    by_cases hz : r i = 0
    · simp [hz]
    have hi : 1 ≤ (i.val+1)/2 := by
      by_contra h
      have he : i.val = 0 := by omega
      exact hz (ho i (by simp [he]))
    simpa using Nat.mul_le_mul_right (r i) hi
  have factorial_val_mono {a b : ℕ} (hab : a ≤ b) :
      padicValNat 2 a.factorial ≤ padicValNat 2 b.factorial := by
    apply (padicValNat_dvd_iff_le (Nat.factorial_ne_zero b)).mp
    exact (show 2 ^ padicValNat 2 a.factorial ∣ a.factorial from
      pow_padicValNat_dvd).trans (Nat.factorial_dvd_factorial hab)
  have hprod : (∑ i : Fin L, padicValNat 2 (((i.val+1)/2)*r i).factorial) ≤
      padicValNat 2 (∑ i : Fin L, ((i.val+1)/2)*r i).factorial := by
    rw [← Nat.factorization_def _ Nat.prime_two]
    simp_rw [← Nat.factorization_def _ Nat.prime_two]
    rw [← Nat.factorization_prod_apply (fun i _ => Nat.factorial_ne_zero _)]
    rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two]
    apply (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp
    exact (show 2 ^ padicValNat 2 (∏ i : Fin L, (((i.val+1)/2)*r i).factorial) ∣
      ∏ i : Fin L, (((i.val+1)/2)*r i).factorial from pow_padicValNat_dvd).trans
      (Nat.prod_factorial_dvd_factorial_sum univ (fun i : Fin L => ((i.val+1)/2)*r i))
  have hstrict : (∑ i : Fin L, padicValNat 2 (r i).factorial) <
      padicValNat 2 (∑ i : Fin L, ((i.val+1)/2)*r i).factorial := by
    apply lt_of_lt_of_le ?_ hprod
    obtain ⟨i, hi, hri⟩ := hex
    apply Finset.sum_lt_sum (fun j _ => factorial_val_mono (hmono j))
    refine ⟨i, mem_univ _, ?_⟩
    have hdouble := factorial_val_mono (Nat.mul_le_mul_right (r i) hi)
    rw [padicValNat_factorial_mul] at hdouble
    omega
  rw [profile_weight r hw ho] at hstrict
  have hstrict' : (∑ i, (padicValNat 2 (r i).factorial : ℤ)) < padicValNat 2 m.factorial := by
    exact_mod_cast hstrict
  have hsum : 0 ≤ ∑ i : Fin L, (r i:ℤ) * padicValRat 2 (bCoeff m ((i.val+1)/2)) := by
    apply sum_nonneg
    intro i _
    by_cases hz : r i = 0
    · simp [hz]
    have hi : 0 < (i.val+1)/2 := by
      by_contra h
      have he : i.val = 0 := by omega
      exact hz (ho i (by simp [he]))
    exact mul_nonneg (Int.natCast_nonneg _) (bCoeff_nonneg m _ hm hi)
  omega

/-- W2: the defining Bell sum equals the scaled finite-profile sum. -/
private theorem scaled_pBell (m : ℕ) :
    24^m * (m.factorial:ℚ) * pBell (2*m) S1 ((1:ℚ)/2-m) =
      ∑ k ∈ range (2*m+1), ∑ j ∈ bellProfiles (2*m) k,
        rawEntry m (fun i => (j i).val) := by
  classical
  have bellOrdinary_bounded (n k : ℕ) (s : ℕ → ℚ) :
      bellOrdinary n k s =
        ∑ j ∈ bellProfiles n k,
          ((k.factorial : ℚ) / ∏ i, ((j i).val.factorial : ℚ)) *
            ∏ i, s (i.val+1)^(j i).val := by
    unfold bellOrdinary
    symm
    rw [← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv (profileEquiv n k)
      (fun j => ((k.factorial : ℚ) / ∏ i, ((j.val i).val.factorial : ℚ)) *
        ∏ i, s (i.val+1)^(j.val i).val)
      (fun r => ((k.factorial : ℚ) / ∏ i, ((r.val i).factorial : ℚ)) *
        ∏ i, s (i.val+1)^r.val i) (fun _ => rfl))
  have scaled_bell_summand (m k : ℕ)
      (j : Fin (2*m-k+1) → Fin (k+1))
      (hc : ∑ i, (j i).val = k) :
      24^m*(m.factorial : ℚ) *
        (((-1:ℚ)^k/(k.factorial:ℚ)) *
          (((k.factorial:ℚ) / ∏ i, ((j i).val.factorial:ℚ)) *
            ∏ i, S1 (i.val+1)^(j i).val) * ((1:ℚ)/2-m)^k) =
        rawEntry m (fun i => (j i).val) := by
    have hp : ∏ i, (aParam m * S1 (i.val+1))^(j i).val =
        (aParam m)^k * ∏ i, S1 (i.val+1)^(j i).val := by
      simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hc]
    have ht : aParam m = (-1:ℚ)*((1:ℚ)/2-m) := by unfold aParam; ring
    unfold rawEntry
    rw [hp, ht, mul_pow]
    have hk : (k.factorial:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  unfold pBell
  simp_rw [bellOrdinary_bounded]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro j hj
  apply scaled_bell_summand
  exact (mem_filter.mp hj).2.1

/-- Every positive natural index satisfies the nonvanishing assertion. -/
theorem result : claim := by
  have val_sum_ge {α : Type} (s : Finset α) (f : α → ℚ) (a : ℤ)
      (h : ∀ i ∈ s, f i ≠ 0 → a ≤ padicValRat 2 (f i))
      (hne : s.sum f ≠ 0) : a ≤ padicValRat 2 (s.sum f) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp at hne
    | @insert i s hi ih =>
      rw [sum_insert hi] at hne ⊢
      by_cases hf : f i = 0
      · simp only [hf, zero_add] at hne ⊢
        exact ih (fun j hj => h j (by simp [hj])) hne
      by_cases hs : s.sum f = 0
      · simpa [hs] using h i (by simp) hf
      exact le_trans (le_min (h i (by simp) hf)
        (ih (fun j hj => h j (by simp [hj])) hs))
        (padicValRat.min_le_padicValRat_add hne)
  have val_add_ne {x y : ℚ} (hx : x ≠ 0)
      (hy : y ≠ 0 → padicValRat 2 x < padicValRat 2 y) : x+y ≠ 0 := by
    intro hz
    have he : y = -x := by linarith
    have hyn : y ≠ 0 := by simp [he, hx]
    have hv := hy hyn
    rw [he, padicValRat.neg] at hv
    exact lt_irrefl _ hv
  have bCoeff_val (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      bCoeff m n ≠ 0 ∧ padicValRat 2 (bCoeff m n) = (n:ℤ)-1-padicValNat 2 n := by
    have bernoulli_val_two (n : ℕ) (hn : 0 < n) :
        padicValRat 2 (bernoulli (2*n)) = -1 := by
      let s := (range (2*n+2)).filter fun p => p.Prime ∧ (p-1) ∣ 2*n
      have h2 : 2 ∈ s := by simp [s, Nat.prime_two]; omega
      obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen n
      have hr : ∀ p ∈ s.erase 2, 0 ≤ padicValRat 2 ((1:ℚ)/p) := by
        intro p hp
        have hprime : p.Prime := ((mem_filter.mp (mem_of_mem_erase hp)).2).1
        have hp2 : p ≠ 2 := (mem_erase.mp hp).1
        have hd : ¬ 2 ∣ p := fun hd => hp2 ((hprime.dvd_iff_eq (by decide)).mp hd)
        rw [padicValRat.div (by norm_num) (Nat.cast_ne_zero.mpr hprime.ne_zero),
          padicValRat.one, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
        simp
      have hsum : ∑ p ∈ s, (1:ℚ)/p = 1/2 + ∑ p ∈ s.erase 2, (1:ℚ)/p := by
        rw [← sum_erase_add _ _ h2]
        ring
      have he : bernoulli (2*n) = -(1/2 : ℚ) +
          ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) := by
        change (z : ℚ) = bernoulli (2*n) + ∑ p ∈ s, (1:ℚ)/p at hz
        rw [hsum] at hz
        linarith
      have hb : padicValRat 2 (-(1/2 : ℚ)) = -1 := by
        rw [padicValRat.neg, one_div, padicValRat.inv]
        change -padicValRat 2 ((2 : ℕ) : ℚ) = -1
        rw [padicValRat.of_nat, padicValNat_self]
        norm_num
      have hrest : ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) ≠ 0 →
          0 ≤ padicValRat 2 ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) := by
        intro hne
        rw [sub_eq_add_neg] at hne ⊢
        apply le_trans (le_min (by simp [padicValRat.of_int]) ?_)
          (padicValRat.min_le_padicValRat_add hne)
        rw [padicValRat.neg]
        by_cases hs : ∑ p ∈ s.erase 2, (1:ℚ)/p = 0
        · rw [hs]; simp
        exact val_sum_ge _ _ 0 (fun p hp _ => hr p hp) hs
      rw [he]
      by_cases hr0 : (z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p = 0
      · rw [hr0, add_zero]; exact hb
      have hlt : padicValRat 2 (-(1/2 : ℚ)) <
          padicValRat 2 ((z : ℚ) - ∑ p ∈ s.erase 2, (1:ℚ)/p) := by
        rw [hb]; exact lt_of_lt_of_le (by norm_num) (hrest hr0)
      exact (padicValRat.add_eq_of_lt (val_add_ne (by norm_num) (fun _ => hlt))
        (by norm_num) hr0 hlt).trans hb
    have val_two : padicValRat 2 (2:ℚ) = 1 := by
      change padicValRat 2 ((2:ℕ):ℚ) = 1
      rw [padicValRat.of_nat, padicValNat_self]
      norm_num
    have S1_even_val (n : ℕ) (hn : 0 < n) :
        S1 (2*n) ≠ 0 ∧ padicValRat 2 (S1 (2*n)) = -2*(n:ℤ) - padicValNat 2 n := by
      have hb := bernoulli_val_two n hn
      have hbn : bernoulli (2*n) ≠ 0 := by intro h; rw [h, padicValRat.zero] at hb; omega
      let e : ℤ := 1-2*(n:ℤ)
      have he : e < 0 := by dsimp [e]; omega
      have hp : padicValRat 2 (-(2 : ℚ)^e) = e := by
        rw [padicValRat.neg, padicValRat.zpow, val_two]
        ring
      have hx : -(2 : ℚ)^e ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero _ (by norm_num))
      have hlt : padicValRat 2 (-(2 : ℚ)^e) < padicValRat 2 (1 : ℚ) := by simpa [hp] using he
      have hnon : -(2 : ℚ)^e + 1 ≠ 0 := val_add_ne hx (fun _ => hlt)
      have hv := padicValRat.add_eq_of_lt hnon hx (by norm_num) hlt
      have hargs : 1-(2 : ℚ)^e = -(2 : ℚ)^e+1 := by ring
      have hv' : padicValRat 2 (1-(2 : ℚ)^e) = e := by
        rw [hargs]
        exact hv.trans hp
      have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have ht : (2*n : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hn'
      have hf : 1-(2 : ℚ)^e ≠ 0 := by
        rw [hargs]
        exact hnon
      have hdef : S1 (2*n) = (1-(2 : ℚ)^e) * (2 * bernoulli (2*n)) / (2*(n:ℚ)) := by
        simp only [S1, Nat.cast_mul, Nat.cast_ofNat, e]
      rw [hdef]
      refine ⟨div_ne_zero (mul_ne_zero hf (mul_ne_zero (by norm_num) hbn)) ht, ?_⟩
      rw [padicValRat.div (mul_ne_zero hf (mul_ne_zero (by norm_num) hbn)) ht,
        padicValRat.mul hf (mul_ne_zero (by norm_num) hbn),
        padicValRat.mul (by norm_num) hbn, padicValRat.mul (by norm_num) hn',
        hv', hb, val_two, padicValRat.of_nat]
      dsimp [e]
      ring
    have aParam_val (m : ℕ) (hm : 0 < m) :
        aParam m ≠ 0 ∧ padicValRat 2 (aParam m) = -1 := by
      have hn : (2*(m:ℚ)-1) ≠ 0 := by
        have h : (1:ℚ) ≤ m := by exact_mod_cast hm
        linarith
      have hv : padicValRat 2 (2*(m:ℚ)-1) = 0 := by
        have he : 2*(m:ℚ)-1 = ((2*(m:ℤ)-1 : ℤ) : ℚ) := by norm_cast
        rw [he, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
        · simp
        · intro h; obtain ⟨z, hz⟩ := h; omega
      refine ⟨div_ne_zero hn (by norm_num), ?_⟩
      rw [aParam, padicValRat.div hn (by norm_num), hv, val_two]
      norm_num
    obtain ⟨han, ha⟩ := aParam_val m hm
    obtain ⟨hsn, hs⟩ := S1_even_val n hn
    have h24 : padicValRat 2 (24:ℚ) = 3 := by
      change padicValRat 2 ((24:ℕ):ℚ) = 3
      rw [padicValRat.of_nat]
      have : padicValNat 2 24 = 3 := by decide +kernel
      norm_num [this]
    refine ⟨mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) han) hsn, ?_⟩
    rw [bCoeff, padicValRat.mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) han) hsn,
      padicValRat.mul (pow_ne_zero _ (by norm_num)) han,
      padicValRat.pow, h24, ha, hs]
    ring
  have scaled_value_unit (m : ℕ) (hm : 0 < m) :
      24^m*(m.factorial:ℚ)*pBell (2*m) S1 ((1:ℚ)/2-m) ≠ 0 ∧
      padicValRat 2 (24^m*(m.factorial:ℚ)*pBell (2*m) S1 ((1:ℚ)/2-m)) = 0 := by
    classical
    have S1_odd (k : ℕ) (hk : Odd k) : S1 k = 0 := by
      by_cases h : k = 1
      · subst k
        norm_num [S1]
      · have h1 : 1 < k := by obtain ⟨r, hr⟩ := hk; omega
        simp [S1, bernoulli_eq_zero_of_odd hk h1]
    have profile_weight {m L : ℕ} (r : Fin L → ℕ)
        (hw : ∑ i, (i.val+1)*r i = 2*m)
        (ho : ∀ i, Odd (i.val+1) → r i = 0) :
        (∑ i, ((i.val+1)/2)*r i) = m := by
      have he : ∀ i, (i.val+1)*r i = 2 * (((i.val+1)/2)*r i) := by
        intro i
        by_cases hz : r i = 0
        · simp [hz]
        have hno : ¬ Odd (i.val+1) := fun h => hz (ho i h)
        have hmod : (i.val+1)%2 = 0 := by
          have := Nat.even_or_odd (i.val+1)
          rcases this with h | h
          · exact Nat.even_iff.mp h
          · exact (hno h).elim
        have hi : i.val+1 = 2*((i.val+1)/2) := by omega
        calc
          _ = (2*((i.val+1)/2))*r i := congrArg (fun x => x*r i) hi
          _ = _ := by ring
      simp_rw [he] at hw
      rw [← Finset.mul_sum] at hw
      omega
    have rawEntry_odd_zero {m L : ℕ} (r : Fin L → ℕ)
        (hne : rawEntry m r ≠ 0) : ∀ i, Odd (i.val+1) → r i = 0 := by
      intro i hi
      have hprod : ∏ i, (aParam m * S1 (i.val+1)) ^ r i ≠ 0 := by
        intro hp
        simp [rawEntry, hp] at hne
      have h := (Finset.prod_ne_zero_iff.mp hprod) i (mem_univ _)
      rw [S1_odd _ hi, mul_zero] at h
      by_contra hr
      simp [zero_pow hr] at h
    have rawEntry_eq_scaledEntry {m L : ℕ} (r : Fin L → ℕ)
        (hw : ∑ i, (i.val+1)*r i = 2*m)
        (ho : ∀ i, Odd (i.val+1) → r i = 0) : rawEntry m r = scaledEntry m r := by
      have hp : ∏ i, bCoeff m ((i.val+1)/2)^r i =
          24^m * ∏ i, (aParam m * S1 (i.val+1))^r i := by
        calc
          _ = ∏ i, (24^((i.val+1)/2) * (aParam m * S1 (i.val+1)))^r i := by
            apply prod_congr rfl
            intro i _
            by_cases hz : r i = 0
            · simp [hz]
            have hmod : (i.val+1)%2 = 0 := by
              rcases Nat.even_or_odd (i.val+1) with h | h
              · exact Nat.even_iff.mp h
              · exact (hz (ho i h)).elim
            have hi : 2*((i.val+1)/2) = i.val+1 := by omega
            simp only [bCoeff, hi]
            rw [mul_assoc]
          _ = (∏ i, (24:ℚ)^(((i.val+1)/2)*r i)) *
              ∏ i, (aParam m * S1 (i.val+1))^r i := by
            simp only [mul_pow, ← pow_mul, prod_mul_distrib]
          _ = _ := by
            rw [Finset.prod_pow_eq_pow_sum, profile_weight r hw ho]
      unfold rawEntry scaledEntry
      rw [hp]
      ring
    have profile_no_large {m L k : ℕ} (r : Fin L → ℕ)
        (hc : ∑ i, r i = k) (hw : ∑ i, (i.val+1)*r i = 2*m)
        (ho : ∀ i, Odd (i.val+1) → r i = 0)
        (hno : ¬ ∃ i, 2 ≤ (i.val+1)/2 ∧ 0 < r i) :
        k = m ∧ ∀ i, i.val ≠ 1 → r i = 0 := by
      have hz : ∀ i : Fin L, i.val ≠ 1 → r i = 0 := by
        intro i hi
        by_contra hr
        have hlo : (i.val+1)/2 < 2 := by
          by_contra h
          exact hno ⟨i, by omega, Nat.pos_of_ne_zero hr⟩
        have hx : i.val = 0 ∨ i.val = 2 := by omega
        rcases hx with hx | hx
        · exact hr (ho i (by simp [hx]))
        · exact hr (ho i (by rw [hx]; exact ⟨1, by omega⟩))
      have he : ∀ i : Fin L, (i.val+1)*r i = 2*r i := by
        intro i
        by_cases hi : i.val = 1
        · simp [hi]
        · simp [hz i hi]
      simp_rw [he] at hw
      rw [← mul_sum, hc] at hw
      exact ⟨by omega, hz⟩
    have mainProfile_mem (m : ℕ) (hm : 0 < m) :
        mainProfile m ∈ bellProfiles (2*m) m := by
      let i1 : Fin (2*m-m+1) := ⟨1, by omega⟩
      have hsum : ∑ i, (mainProfile m i).val = m := by
        rw [Finset.sum_eq_single i1]
        · simp [mainProfile, i1]
        · intro i _ hi
          have hv : i.val ≠ 1 := fun h => hi (Fin.ext (by simpa [i1] using h))
          simp [mainProfile, hv]
        · simp
      have hweight : ∑ i, (i.val+1)*(mainProfile m i).val = 2*m := by
        rw [Finset.sum_eq_single i1]
        · simp [mainProfile, i1]
        · intro i _ hi
          have hv : i.val ≠ 1 := fun h => hi (Fin.ext (by simpa [i1] using h))
          simp [mainProfile, hv]
        · simp
      exact mem_filter.mpr ⟨mem_univ _, hsum, hweight⟩
    have profile_no_large_main {m : ℕ} (hm : 0 < m)
        (j : Fin (2*m-m+1) → Fin (m+1)) (hj : j ∈ bellProfiles (2*m) m)
        (ho : ∀ i, Odd (i.val+1) → (j i).val = 0)
        (hno : ¬ ∃ i, 2 ≤ (i.val+1)/2 ∧ 0 < (j i).val) : j = mainProfile m := by
      obtain ⟨hc, hw⟩ := (mem_filter.mp hj).2
      have hz := (profile_no_large (fun i => (j i).val) hc hw ho hno).2
      let i1 : Fin (2*m-m+1) := ⟨1, by omega⟩
      have hj1 : (j i1).val = m := by
        rw [Finset.sum_eq_single i1] at hc
        · exact hc
        · intro i _ hi
          exact hz i (fun h => hi (Fin.ext (by simpa [i1] using h)))
        · simp
      funext i
      apply Fin.ext
      by_cases hi : i.val = 1
      · have hii : i = i1 := Fin.ext (by simpa [i1] using hi)
        simp [mainProfile, hii, hj1, i1]
      · simp [mainProfile, hi, hz i hi]
    have main_rawEntry (m : ℕ) (hm : 0 < m) :
        rawEntry m (fun i => (mainProfile m i).val) = (bCoeff m 1)^m := by
      have hmemb := mainProfile_mem m hm
      obtain ⟨hc, hw⟩ := (mem_filter.mp hmemb).2
      have ho : ∀ i : Fin (2*m-m+1), Odd (i.val+1) → (mainProfile m i).val = 0 := by
        intro i hi
        have hv : i.val ≠ 1 := by
          intro h
          obtain ⟨r, hr⟩ := hi
          omega
        simp [mainProfile, hv]
      rw [rawEntry_eq_scaledEntry _ hw ho, scaledEntry]
      let i1 : Fin (2*m-m+1) := ⟨1, by omega⟩
      have hprod : ∏ i, bCoeff m ((i.val+1)/2)^(mainProfile m i).val = (bCoeff m 1)^m := by
        rw [Finset.prod_eq_single i1]
        · simp [mainProfile, i1]
        · intro i _ hi
          have hv : i.val ≠ 1 := fun h => hi (Fin.ext (by simpa [i1] using h))
          simp [mainProfile, hv]
        · simp
      have hden : ∏ i, ((mainProfile m i).val.factorial : ℚ) = m.factorial := by
        rw [Finset.prod_eq_single i1]
        · simp [mainProfile, i1]
        · intro i _ hi
          have hv : i.val ≠ 1 := fun h => hi (Fin.ext (by simpa [i1] using h))
          simp [mainProfile, hv]
        · simp
      rw [hprod, hden]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    have other_outer_val (m k : ℕ) (hm : 0 < m) (hkm : k ≠ m)
        (j : Fin (2*m-k+1) → Fin (k+1)) (hj : j ∈ bellProfiles (2*m) k)
        (hne : rawEntry m (fun i => (j i).val) ≠ 0) :
        1 ≤ padicValRat 2 (rawEntry m (fun i => (j i).val)) := by
      obtain ⟨hc, hw⟩ := (mem_filter.mp hj).2
      have ho := rawEntry_odd_zero _ hne
      have he : ∃ i, 2 ≤ (i.val+1)/2 ∧ 0 < (j i).val := by
        by_contra h
        exact hkm (profile_no_large _ hc hw ho h).1
      rw [rawEntry_eq_scaledEntry _ hw ho]
      exact (scaledEntry_pos_val hm _ hw ho he)
    have other_inner_val (m : ℕ) (hm : 0 < m)
        (j : Fin (2*m-m+1) → Fin (m+1)) (hj : j ∈ bellProfiles (2*m) m)
        (hjm : j ≠ mainProfile m) (hne : rawEntry m (fun i => (j i).val) ≠ 0) :
        1 ≤ padicValRat 2 (rawEntry m (fun i => (j i).val)) := by
      obtain ⟨hc, hw⟩ := (mem_filter.mp hj).2
      have ho := rawEntry_odd_zero _ hne
      have he : ∃ i, 2 ≤ (i.val+1)/2 ∧ 0 < (j i).val := by
        by_contra h
        exact hjm (profile_no_large_main hm j hj ho h)
      rw [rawEntry_eq_scaledEntry _ hw ho]
      exact (scaledEntry_pos_val hm _ hw ho he)
    have unit_sum {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℚ)
        (i : α) (hi : i ∈ s) (hfn : f i ≠ 0) (hfv : padicValRat 2 (f i) = 0)
        (hrest : ∀ j ∈ s.erase i, f j ≠ 0 → 1 ≤ padicValRat 2 (f j)) :
        s.sum f ≠ 0 ∧ padicValRat 2 (s.sum f) = 0 := by
      rw [← sum_erase_add _ _ hi, add_comm]
      have hr : (s.erase i).sum f ≠ 0 → 1 ≤ padicValRat 2 ((s.erase i).sum f) :=
        val_sum_ge _ _ 1 hrest
      have hne : f i + (s.erase i).sum f ≠ 0 := val_add_ne hfn (fun h => by rw [hfv]; exact hr h)
      refine ⟨hne, ?_⟩
      by_cases hzero : (s.erase i).sum f = 0
      · simpa only [hzero, add_zero] using hfv
      exact (padicValRat.add_eq_of_lt hne hfn hzero (by rw [hfv]; exact hr hzero)).trans hfv
    have main_inner_unit (m : ℕ) (hm : 0 < m) :
        (∑ j ∈ bellProfiles (2*m) m, rawEntry m (fun i => (j i).val)) ≠ 0 ∧
        padicValRat 2 (∑ j ∈ bellProfiles (2*m) m, rawEntry m (fun i => (j i).val)) = 0 := by
      apply unit_sum _ _ (mainProfile m) (mainProfile_mem m hm)
      · rw [main_rawEntry m hm]
        exact pow_ne_zero _ (bCoeff_val m 1 hm (by omega)).1
      · rw [main_rawEntry m hm, padicValRat.pow, (bCoeff_val m 1 hm (by omega)).2]
        simp
      · intro j hj hn
        exact other_inner_val m hm j (mem_of_mem_erase hj) (mem_erase.mp hj).1 hn
    rw [scaled_pBell]
    obtain ⟨hne, hv⟩ := main_inner_unit m hm
    apply unit_sum (range (2*m+1))
      (fun k : ℕ => ∑ j ∈ bellProfiles (2*m) k, rawEntry m (fun i => (j i).val))
      m (mem_range.mpr (by omega)) hne hv
    intro k hk hkn
    apply val_sum_ge (bellProfiles (2*m) k)
      (fun j => rawEntry m (fun i => (j i).val)) 1 ?_ hkn
    intro j hj hjn
    exact other_outer_val m k hm (mem_erase.mp hk).1 j hj hjn
  intro m hm
  have h := (scaled_value_unit m (by omega)).1
  intro hz
  rw [hz, mul_zero] at h
  exact h rfl

end D5.S3.ArithSums.LogLaplacianBellNonvanishing
