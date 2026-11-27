import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  Stage A support for Nathanson's Problem 15.

  The signed radix lemma is kept independent of the interval construction.  It
  is the modulo-and-cancellation step used to separate the labelled sums.
-/

open scoped BigOperators Pointwise

namespace D5.S3.Arith.NathansonProblem15

/- The powers are indexed by `Fin m`; the hypothesis is exactly the strict
   digit-width condition needed by the first-modulus argument. -/
theorem signed_radix_injective {m : ℕ} {B : ℤ} (hB : 1 < B)
    (d e : Fin m → ℤ)
    (hdiff : ∀ i, (d i - e i).natAbs < B.natAbs)
    (h : (∑ i : Fin m, d i * B ^ i.val) =
      ∑ i : Fin m, e i * B ^ i.val) : d = e := by
  induction m with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      have hsplit (f : Fin (m + 1) → ℤ) :
          (∑ i : Fin (m + 1), f i * B ^ i.val) =
            f 0 + B * ∑ i : Fin m, f i.succ * B ^ i.val := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
        rw [Finset.mul_sum]
        simp [mul_assoc, mul_comm, mul_left_comm]
      have h0 : d 0 = e 0 := by
        have hdvd : B ∣ d 0 - e 0 := by
          have hs := congrArg (fun z : ℤ => z -
              B * ∑ i : Fin m, e i.succ * B ^ i.val) h
          rw [hsplit d, hsplit e] at hs
          exact ⟨∑ i : Fin m, e i.succ * B ^ i.val -
              ∑ i : Fin m, d i.succ * B ^ i.val, by linarith⟩
        by_cases hzero : d 0 - e 0 = 0
        · exact sub_eq_zero.mp hzero
        · have habs : B.natAbs ≤ (d 0 - e 0).natAbs :=
            Nat.le_of_dvd (Int.natAbs_pos.mpr hzero)
              (Int.natAbs_dvd_natAbs.mpr hdvd)
          have hlt := hdiff 0
          exact False.elim ((Nat.not_lt_of_ge habs) hlt)
      have htail :
          (∑ i : Fin m, d i.succ * B ^ i.val) =
            ∑ i : Fin m, e i.succ * B ^ i.val := by
        have hs := congrArg (fun z : ℤ => z - d 0) h
        rw [hsplit d, hsplit e, h0] at hs
        have hBn : (B : ℤ) ≠ 0 := by linarith
        apply (mul_left_cancel₀ hBn)
        linarith
      have htaildiff : ∀ i : Fin m, (d i.succ - e i.succ).natAbs < B.natAbs :=
        fun i => hdiff i.succ
      have hfun := ih (d := fun i => d i.succ) (e := fun i => e i.succ)
        htaildiff htail
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun hfun j

/-- The coefficient of a place in the radix expansion of a labelled sum. -/
def digit {m : ℕ} (h : ℕ) (u v : Fin m → ℕ) (i : Fin m) : ℤ :=
  (u i : ℤ) - ((h : ℤ) - 1) * (v i : ℤ)

private theorem zero_off_of_sum_eq {m : ℕ} (f : Fin m → ℕ) (i : Fin m)
    (hi : (∑ j, f j) = f i) {j : Fin m} (hj : j ≠ i) : f j = 0 := by
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [hi] at hsplit
  have hrest : ∑ k ∈ Finset.univ.erase i, f k = 0 := by omega
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le (f k))).mp hrest j
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)

/-- A collision between distinct multiplicity pairs of total weight `h` has zero digits. -/
theorem digit_eq_zero_of_collision {m h : ℕ} (hh : 2 ≤ h)
    {u v u' v' : Fin m → ℕ}
    (huv : (∑ i, (u i + v i)) = h)
    (huv' : (∑ i, (u' i + v' i)) = h)
    (heq : digit h u v = digit h u' v') (hne : (u, v) ≠ (u', v')) :
    digit h u v = 0 := by
  have hz {a b c d : Fin m → ℕ} (hcd : (∑ i, (c i + d i)) = h)
      (hsame : digit h a b = digit h c d) (i : Fin m) (hlt : b i < d i) :
      digit h c d = 0 := by
    have hgap : (b i : ℤ) + 1 ≤ (d i : ℤ) := by omega
    have hcoef : 0 ≤ (h : ℤ) - 1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hgap hcoef
    have hdigit := congrFun hsame i
    unfold digit at hdigit
    have hc : (h : ℤ) - 1 ≤ (c i : ℤ) := by
      rw [mul_add, mul_one] at hmul
      linarith [Int.natCast_nonneg (a i)]
    have hlocal : c i + d i ≤ h := by
      rw [← hcd]
      exact Finset.single_le_sum (f := fun j => c j + d j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hc' : c i = h - 1 := by omega
    have hd' : d i = 1 := by omega
    have hfull : (∑ j, (c j + d j)) = c i + d i := by omega
    funext j
    change digit h c d j = 0
    by_cases hj : j = i
    · subst j
      simp [digit, hd', show (c i : ℤ) = (h : ℤ) - 1 by omega]
    · have hoff := zero_off_of_sum_eq (fun k => c k + d k) i hfull hj
      simp [digit, show c j = 0 by omega, show d j = 0 by omega]
  have hv : v ≠ v' := by
    intro hv
    apply hne
    refine Prod.ext ?_ hv
    change u = u'
    funext i
    have hi := congrFun heq i
    rw [← hv] at hi
    unfold digit at hi
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact heq.trans (hz huv' heq i hlt)
  · exact hz huv heq.symm i hgt

/-- Zero digits use all terms at one index, with one term of the second kind. -/
theorem digit_eq_zero_iff {m h : ℕ} (hh : 2 ≤ h) {u v : Fin m → ℕ}
    (huv : (∑ i, (u i + v i)) = h) :
    digit h u v = 0 ↔ ∃ j : Fin m, ∀ i,
      u i = (if i = j then h - 1 else 0) ∧ v i = (if i = j then 1 else 0) := by
  constructor
  · intro hz
    have hpoint (i : Fin m) : (u i : ℤ) = ((h : ℤ) - 1) * (v i : ℤ) := by
      have hi : digit h u v i = 0 := congrFun hz i
      exact sub_eq_zero.mp hi
    have hlocal (i : Fin m) : u i + v i = h * v i := by
      have hi : (u i : ℤ) + (v i : ℤ) = (h : ℤ) * (v i : ℤ) := by
        rw [hpoint i, sub_mul, one_mul]
        ring
      exact_mod_cast hi
    have htotal : h * (∑ i, v i) = h * 1 := by
      rw [Finset.mul_sum, mul_one]
      exact (Finset.sum_congr rfl (fun i _ => (hlocal i).symm)).trans huv
    have hv : (∑ i, v i) = 1 := mul_left_cancel₀ (by omega : h ≠ 0) htotal
    have hpos : 0 < ∑ i, v i := by rw [hv]; decide
    obtain ⟨j, _, hj⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun i _ => Nat.zero_le (v i))).mp hpos
    have hjle : v j ≤ ∑ i, v i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (v i)) (Finset.mem_univ j)
    have hjone : v j = 1 := by omega
    refine ⟨j, fun i => ?_⟩
    by_cases hi : i = j
    · subst i
      have hloc := hlocal j
      simp [hjone] at hloc
      simp [hjone, show u j = h - 1 by omega]
    · have hvi := zero_off_of_sum_eq v j (hv.trans hjone.symm) hi
      have hui : u i = 0 := by simpa [hvi] using hlocal i
      simp [hi, hui, hvi]
  · rintro ⟨j, hj⟩
    funext i
    change digit h u v i = 0
    obtain ⟨hu, hv⟩ := hj i
    by_cases hi : i = j
    · subst i
      simp at hu hv
      simp [digit, hv, show (u j : ℤ) = (h : ℤ) - 1 by omega]
    · simp [hi] at hu hv
      simp [digit, hu, hv]

/-- The signed radix code with base one more than the width of the digit interval. -/
def radixCode {m : ℕ} (h : ℕ) (u v : Fin m → ℕ) : ℤ :=
  ∑ i, digit h u v i * ((h : ℤ) ^ 2 + 1) ^ i.val

private theorem digit_bounds {m h : ℕ} (hh : 2 ≤ h) {u v : Fin m → ℕ}
    (huv : (∑ i, (u i + v i)) = h) (i : Fin m) :
    -((h : ℤ) - 1) * h ≤ digit h u v i ∧ digit h u v i ≤ h := by
  have hlocal : u i + v i ≤ h := by
    rw [← huv]
    exact Finset.single_le_sum (f := fun j => u j + v j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hu : (u i : ℤ) ≤ h := by omega
  have hv : (v i : ℤ) ≤ h := by omega
  have hcoef : 0 ≤ (h : ℤ) - 1 := by omega
  unfold digit
  constructor
  · linarith [mul_le_mul_of_nonneg_left hv hcoef, Int.natCast_nonneg (u i)]
  · linarith [mul_nonneg hcoef (Int.natCast_nonneg (v i))]

private theorem natAbs_lt_of_digit_bounds {h : ℕ} {x y : ℤ}
    (hx : -((h : ℤ) - 1) * h ≤ x ∧ x ≤ h)
    (hy : -((h : ℤ) - 1) * h ≤ y ∧ y ≤ h) :
    (x - y).natAbs < ((h : ℤ) ^ 2 + 1).natAbs := by
  have hB : 0 ≤ (h : ℤ) ^ 2 + 1 := by positivity
  have hcast : ((x - y).natAbs : ℤ) < (((h : ℤ) ^ 2 + 1).natAbs : ℤ) := by
    rw [Int.ofNat_natAbs_of_nonneg hB]
    rcases le_total 0 (x - y) with hp | hn
    · rw [Int.ofNat_natAbs_of_nonneg hp]
      linarith [hx.2, hy.1]
    · rw [Int.ofNat_natAbs_of_nonpos hn]
      linarith [hy.2, hx.1]
  exact_mod_cast hcast

/-- For multiplicities of weight `h`, equality of codes is equality of digit vectors. -/
theorem radixCode_eq_iff {m h : ℕ} (hh : 2 ≤ h) {u v u' v' : Fin m → ℕ}
    (huv : (∑ i, (u i + v i)) = h) (huv' : (∑ i, (u' i + v' i)) = h) :
    radixCode h u v = radixCode h u' v' ↔ digit h u v = digit h u' v' := by
  have hB : 1 < (h : ℤ) ^ 2 + 1 := by
    have hh' : 0 < (h : ℤ) := by omega
    have hsq : 0 < (h : ℤ) ^ 2 := pow_pos hh' _
    omega
  constructor
  · exact signed_radix_injective hB _ _ (fun i =>
      natAbs_lt_of_digit_bounds (digit_bounds hh huv i) (digit_bounds hh huv' i))
  · intro heq
    simp only [radixCode, heq]

/-- The zero radix code occurs exactly for the multiplicities of a prescribed point. -/
theorem radixCode_eq_zero_iff {m h : ℕ} (hh : 2 ≤ h) {u v : Fin m → ℕ}
    (huv : (∑ i, (u i + v i)) = h) :
    radixCode h u v = 0 ↔ ∃ j : Fin m, ∀ i,
      u i = (if i = j then h - 1 else 0) ∧ v i = (if i = j then 1 else 0) := by
  rw [← digit_eq_zero_iff hh huv]
  have hh' : 0 < (h : ℤ) := by omega
  have hB : 1 < (h : ℤ) ^ 2 + 1 := by
    have hsq : 0 < (h : ℤ) ^ 2 := pow_pos hh' _
    omega
  have hz : -((h : ℤ) - 1) * h ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ h := by
    constructor
    · have hcoef : 0 ≤ (h : ℤ) - 1 := by omega
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoef) hh'.le
    · exact hh'.le
  constructor
  · intro hc
    apply signed_radix_injective hB (digit h u v) (0 : Fin m → ℤ)
      (fun i => natAbs_lt_of_digit_bounds (digit_bounds hh huv i) hz)
    simpa [radixCode] using hc
  · intro hd
    simp [radixCode, hd]

private theorem mem_nsmul_range_iff_counts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℤ) {h : ℕ} {z : ℤ} :
    z ∈ h • Set.range g ↔
      ∃ c : ι → ℕ, (∑ i, c i) = h ∧ (∑ i, c i • g i) = z := by
  have eval (s : Multiset ι) : (s.map g).sum = ∑ i, s.count i • g i := by
    rw [Finset.sum_multiset_map_count]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Multiset.count_eq_zero_of_notMem (mt Multiset.mem_toFinset.mpr hi), zero_nsmul]
  constructor
  · intro hz
    obtain ⟨f, hf, hsum⟩ := Set.mem_nsmul_iff_sum.mp hz
    choose w hw using hf
    let s : Multiset ι := (Finset.univ : Finset (Fin h)).val.map w
    have hcard : s.card = h := by
      simp [s]
    refine ⟨s.count, ?_, ?_⟩
    · exact (Multiset.sum_count_eq_card (s := Finset.univ)
        (fun i _ => Finset.mem_univ i)).trans hcard
    · rw [← eval]
      simpa only [s, Multiset.map_map, Function.comp_def, hw, ← Finset.sum_eq_multiset_sum]
        using hsum
  · rintro ⟨c, hc, hsum⟩
    let s : Multiset ι := ∑ i, Multiset.replicate (c i) i
    have hcard : s.card = h := by simpa only [s, Multiset.card_sum, Multiset.card_replicate] using hc
    have hcount (i : ι) : s.count i = c i := by
      simp [s, Multiset.count_sum', Multiset.count_replicate, eq_comm]
    have hm := Set.multiset_sum_mem_multiset_sum s (fun _ => Set.range g) g
      (fun i _ => ⟨i, rfl⟩)
    simpa only [eval, hcount, hsum, Multiset.map_const', Multiset.sum_replicate, hcard] using hm

/-- Membership in the iterated sum of two labelled families is equivalent to a budgeted
sum of their multiplicities. Labels may have equal values. -/
theorem mem_labelled_sum_iff {m h : ℕ} {z : ℤ} (a b : Fin m → ℤ) :
    z ∈ h • Set.range (Sum.elim a b) ↔
      ∃ u v : Fin m → ℕ, (∑ i, (u i + v i)) = h ∧
        (∑ i, ((u i : ℤ) * a i + (v i : ℤ) * b i)) = z := by
  rw [mem_nsmul_range_iff_counts]
  constructor
  · rintro ⟨c, hc, hs⟩
    refine ⟨c ∘ Sum.inl, c ∘ Sum.inr, ?_, ?_⟩
    · simpa [Fintype.sum_sum_type, Finset.sum_add_distrib, Function.comp_def] using hc
    · simpa [Fintype.sum_sum_type, Finset.sum_add_distrib, Function.comp_def, nsmul_eq_mul] using hs
  · rintro ⟨u, v, hc, hs⟩
    refine ⟨Sum.elim u v, ?_, ?_⟩
    · simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using hc
    · simpa [Fintype.sum_sum_type, Finset.sum_add_distrib, nsmul_eq_mul] using hs

/-- The two generators for each prescribed point, kept distinct as labels. -/
def radixGenerators {m : ℕ} (h : ℕ) (M : ℤ) (t : Fin m → ℤ) : Fin m ⊕ Fin m → ℤ :=
  let a (i : Fin m) := M * ((h : ℤ) ^ 2 + 1) ^ i.val
  Sum.elim a (fun i => t i - ((h : ℤ) - 1) * a i)

/-- A sum of radix generators has a signed code and a remainder from the second labels. -/
theorem mem_radixGenerators_iff {m h : ℕ} {M z : ℤ} (t : Fin m → ℤ) :
    z ∈ h • Set.range (radixGenerators h M t) ↔
      ∃ u v : Fin m → ℕ, (∑ i, (u i + v i)) = h ∧
        M * radixCode h u v + (∑ i, (v i : ℤ) * t i) = z := by
  unfold radixGenerators
  dsimp only
  rw [mem_labelled_sum_iff]
  have heval (u v : Fin m → ℕ) :
      (∑ i, ((u i : ℤ) * (M * ((h : ℤ) ^ 2 + 1) ^ i.val) +
        (v i : ℤ) * (t i - ((h : ℤ) - 1) * (M * ((h : ℤ) ^ 2 + 1) ^ i.val)))) =
      M * radixCode h u v + ∑ i, (v i : ℤ) * t i := by
    rw [radixCode, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold digit
    ring
  simp only [heval]

/-- The values represented by zero-code multiplicities are exactly the prescribed points. -/
theorem mem_range_iff_zero_code_sum {m h : ℕ} (hh : 2 ≤ h) (t : Fin m → ℤ) (z : ℤ) :
    z ∈ Set.range t ↔
      ∃ u v : Fin m → ℕ, (∑ i, (u i + v i)) = h ∧
        radixCode h u v = 0 ∧ (∑ i, (v i : ℤ) * t i) = z := by
  constructor
  · rintro ⟨j, rfl⟩
    let u (i : Fin m) := if i = j then h - 1 else 0
    let v (i : Fin m) := if i = j then 1 else 0
    have huv : (∑ i, (u i + v i)) = h := by
      rw [Finset.sum_eq_single j]
      · have hj : h - 1 + 1 = h := by omega
        simpa [u, v] using hj
      · intro i _ hi
        simp [u, v, hi]
      · simp
    refine ⟨u, v, huv, (radixCode_eq_zero_iff hh huv).mpr ⟨j, fun _ => ⟨rfl, rfl⟩⟩, ?_⟩
    simp [v, apply_ite]
  · rintro ⟨u, v, huv, hzero, hsum⟩
    obtain ⟨j, hj⟩ := (radixCode_eq_zero_iff hh huv).mp hzero
    refine ⟨j, ?_⟩
    have hv (i : Fin m) := (hj i).2
    simpa [hv, apply_ite] using hsum

end D5.S3.Arith.NathansonProblem15
