/- GID: D5/S3/Arith/Additive/NathansonProblem15
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/NathansonProblem15
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Constructs iterated integer sumsets with prescribed intervals and controls the number of generators. -/

/-
admission_basis: open-problem-resolution (#34976; Proved)
Direct frozen dependencies: none for every declaration.

Definitions and live consumers:
  digit -> digit_eq_zero_of_collision, digit_eq_zero_iff, radixCode
  radixCode -> radixCode_eq_iff, radixCode_eq_zero_iff, mem_radixGenerators_iff
  radixGenerators -> mem_radixGenerators_iff, adjacent_mem_range, nathanson_problem15

Declaration                             proof_shape  escape_witness / live consumer
signed_radix_injective                  content      Modulo the radix, the first digits agree under the strict width bound.
zero_off_of_sum_eq                      bind-only    none / digit_eq_zero_of_collision
digit_eq_zero_of_collision              content      A changed second multiplicity spends the entire budget at one index.
digit_eq_zero_iff                       content      Zero digits convert total weight h to h times the second-label weight, forcing that weight to be one.
digit_bounds                            content      The weight budget confines each signed digit to [-(h - 1)h, h].
natAbs_lt_of_digit_bounds               bind-only    Normalizes the two given intervals / radixCode_eq_iff, radixCode_eq_zero_iff
radixCode_eq_iff                        content      Inlines the signed_radix_injective induction to recover equal digit vectors.
radixCode_eq_zero_iff                   content      Applies signed_radix_injective directly against the zero vector, then digit_eq_zero_iff recovers the multiplicities.
mem_nsmul_range_iff_counts              bind-only    Sym.equivNatSumOfFintype supplies exact-size counts / mem_labelled_sum_iff
mem_labelled_sum_iff                    bind-only    none / mem_radixGenerators_iff
mem_radixGenerators_iff                 bind-only    none / adjacent_mem_range, nathanson_problem15
mem_range_iff_zero_code_sum             content      Constructs weight-h multiplicities supported on the index of each prescribed point.
abs_remainder_le                        content      The second-label weight bound controls the full remainder by hU.
separated_values                        content      The radix scale dominates both remainders by at least two.
adjacent_mem_range                      content      Adjacent values force equal codes and then a zero-digit collision.
interval_equivalences                   content      An adjacent pair cannot straddle the gap between prescribed intervals.
nathanson_problem15                     content      Constructs the finite generator set and obtains both exact interval laws.

Four-slot audit: the Reg mirror binds the sumset readout in the prescribed-start
equivalence of nathanson_problem15.
Tracking: https://github.com/the-omega-institute/trureturing/issues/34976.

Utility is none. The conclusion quantifies over arbitrary admissible parameters.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
  Nathanson's Problem 15 on prescribed intervals in iterated integer sumsets.

  The signed radix code separates sums with different codes by at least two.
  Adjacent sums have code zero, whose values are exactly the prescribed points.
-/

compile_only_with_mathlib

open scoped BigOperators Pointwise

namespace D5.S3.Arith.NathansonProblem15

/- The powers are indexed by `Fin m`; the hypothesis is exactly the strict
   digit-width condition needed by the first-modulus argument. -/
private theorem signed_radix_injective {m : ℕ} {B : ℤ} (hB : 1 < B)
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
private theorem digit_eq_zero_of_collision {m h : ℕ} (hh : 2 ≤ h)
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
private theorem digit_eq_zero_iff {m h : ℕ} (hh : 2 ≤ h) {u v : Fin m → ℕ}
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
    obtain ⟨j, hj⟩ := (Finsupp.sum_eq_one_iff (Finsupp.equivFunOnFinite.symm v)).mp
      ((Finsupp.equivFunOnFinite_symm_sum v).trans hv)
    have hsingle (i : Fin m) : v i = (if i = j then 1 else 0) := by
      simpa [Finsupp.single_apply, eq_comm] using congrArg (fun f : Fin m →₀ ℕ => f i) hj
    refine ⟨j, fun i => ?_⟩
    by_cases hi : i = j
    · subst i
      have hjone : v j = 1 := by simpa using hsingle j
      have hloc := hlocal j
      simp [hjone] at hloc
      simp [hjone, show u j = h - 1 by omega]
    · have hvi : v i = 0 := by simpa [hi] using hsingle i
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
private theorem radixCode_eq_iff {m h : ℕ} (hh : 2 ≤ h) {u v u' v' : Fin m → ℕ}
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
private theorem radixCode_eq_zero_iff {m h : ℕ} (hh : 2 ≤ h) {u v : Fin m → ℕ}
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
    let counts : ι → ℕ :=
      (Sym.equivNatSumOfFintype ι h ⟨s, hcard⟩ : ι → ℕ)
    have hcounts (i : ι) : counts i = s.count i := by
      exact (Sym.coe_equivNatSumOfFintype_apply_apply (α := ι) (n := h) ⟨s, hcard⟩ i)
    refine ⟨counts, ?_, ?_⟩
    · exact (Sym.equivNatSumOfFintype ι h ⟨s, hcard⟩).property
    ·
      have hsumcounts : (∑ i, counts i • g i) = ∑ i, s.count i • g i :=
        Finset.sum_congr rfl (fun i _ => by rw [hcounts])
      calc
        _ = ∑ i, s.count i • g i := hsumcounts
        _ = (s.map g).sum := eval s |>.symm
        _ = ∑ i, f i := by
          simp only [s, Multiset.map_map, Function.comp_def, hw,
            ← Finset.sum_eq_multiset_sum]
        _ = z := hsum
  · rintro ⟨c, hc, hsum⟩
    let s : Sym ι h := (Sym.equivNatSumOfFintype ι h).symm ⟨c, hc⟩
    have hcard : (s : Multiset ι).card = h := s.property
    have hs : (Sym.equivNatSumOfFintype ι h) s = ⟨c, hc⟩ :=
      (Sym.equivNatSumOfFintype ι h).apply_symm_apply ⟨c, hc⟩
    have hcount (i : ι) : (s : Multiset ι).count i = c i := by
      calc
        _ = (Sym.equivNatSumOfFintype ι h s).val i :=
          (Sym.coe_equivNatSumOfFintype_apply_apply (α := ι) (n := h) s i).symm
        _ = c i := by rw [hs]
    have hm := Set.multiset_sum_mem_multiset_sum (s : Multiset ι) (fun _ => Set.range g) g
      (fun i _ => ⟨i, rfl⟩)
    simpa only [eval, hcount, hsum, Multiset.map_const', Multiset.sum_replicate, hcard] using hm

/-- Membership in the iterated sum of two labelled families is equivalent to a budgeted
sum of their multiplicities. Labels may have equal values. -/
private theorem mem_labelled_sum_iff {m h : ℕ} {z : ℤ} (a b : Fin m → ℤ) :
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
private theorem mem_radixGenerators_iff {m h : ℕ} {M z : ℤ} (t : Fin m → ℤ) :
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
private theorem mem_range_iff_zero_code_sum {m h : ℕ} (hh : 2 ≤ h) (t : Fin m → ℤ) (z : ℤ) :
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

private theorem abs_remainder_le {m h : ℕ} {U : ℤ} (hU : 0 ≤ U)
    (t : Fin m → ℤ) (ht : ∀ i, |t i| ≤ U) {u v : Fin m → ℕ}
    (huv : (∑ i, (u i + v i)) = h) :
    |∑ i, (v i : ℤ) * t i| ≤ (h : ℤ) * U := by
  have hv : (∑ i, v i) ≤ h := by
    rw [← huv]
    exact Finset.sum_le_sum (fun i _ => Nat.le_add_left _ _)
  have hv' : (∑ i, (v i : ℤ)) ≤ (h : ℤ) := by exact_mod_cast hv
  calc
    _ ≤ ∑ i, |(v i : ℤ) * t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (v i : ℤ) * U := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (ht i) (Int.natCast_nonneg _)
    _ = (∑ i, (v i : ℤ)) * U := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hv' hU

private theorem separated_values {H d e r s : ℤ}
    (hH : 0 ≤ H) (hr : |r| ≤ H) (hs : |s| ≤ H) (hd : d ≠ e) :
    let M := 2 * H + 2
    2 ≤ |(M * d + r) - (M * e + s)| := by
  let M : ℤ := 2 * H + 2
  change 2 ≤ |(M * d + r) - (M * e + s)|
  have hM : 0 ≤ M := by dsimp [M]; omega
  obtain ⟨hrLower, hrUpper⟩ := abs_le.mp hr
  obtain ⟨hsLower, hsUpper⟩ := abs_le.mp hs
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · have hgap : 1 ≤ e - d := by omega
    have hscaled : M ≤ M * e - M * d := by
      simpa only [mul_one, mul_sub] using mul_le_mul_of_nonneg_left hgap hM
    have hbound : M = 2 * H + 2 := rfl
    have hle : 2 ≤ -((M * d + r) - (M * e + s)) := by omega
    exact hle.trans (neg_le_abs _)
  · have hgap : 1 ≤ d - e := by omega
    have hscaled : M ≤ M * d - M * e := by
      simpa only [mul_one, mul_sub] using mul_le_mul_of_nonneg_left hgap hM
    have hbound : M = 2 * H + 2 := rfl
    have hle : 2 ≤ (M * d + r) - (M * e + s) := by omega
    exact hle.trans (le_abs_self _)

private theorem adjacent_mem_range {m h : ℕ} (hh : 2 ≤ h)
    {U : ℤ} (hU : 0 ≤ U) (t : Fin m → ℤ) (ht : ∀ i, |t i| ≤ U) {x : ℤ}
    (hx : x ∈ h • Set.range (radixGenerators h (2 * ((h : ℤ) * U) + 2) t))
    (hx' : x + 1 ∈ h • Set.range (radixGenerators h (2 * ((h : ℤ) * U) + 2) t)) :
    x ∈ Set.range t ∧ x + 1 ∈ Set.range t := by
  obtain ⟨u, v, huv, heval⟩ := (mem_radixGenerators_iff t).mp hx
  obtain ⟨u', v', huv', heval'⟩ := (mem_radixGenerators_iff t).mp hx'
  have hcode : radixCode h u v = radixCode h u' v' := by
    by_contra hne
    have hsep := separated_values (mul_nonneg (Int.natCast_nonneg h) hU)
      (abs_remainder_le hU t ht huv) (abs_remainder_le hU t ht huv') hne
    dsimp at hsep
    rw [heval, heval'] at hsep
    have hdiff : x - (x + 1) = -1 := by omega
    rw [hdiff, show |(-1 : ℤ)| = 1 by decide] at hsep
    omega
  have hpairs : (u, v) ≠ (u', v') := by
    intro heq
    obtain ⟨hu, hv⟩ := Prod.mk.inj heq
    rw [← hu, ← hv, heval] at heval'
    omega
  have hdigit := digit_eq_zero_of_collision hh huv huv'
    ((radixCode_eq_iff hh huv huv').mp hcode) hpairs
  have hz : radixCode h u v = 0 := by simp [radixCode, hdigit]
  have hz' : radixCode h u' v' = 0 := hcode.symm.trans hz
  exact ⟨(mem_range_iff_zero_code_sum hh t x).mpr
      ⟨u, v, huv, hz, by simpa [hz] using heval⟩,
    (mem_range_iff_zero_code_sum hh t (x + 1)).mpr
      ⟨u', v', huv', hz', by simpa [hz'] using heval'⟩⟩

private theorem interval_equivalences {q : ℕ} {n : ℤ} (hn : 1 ≤ n)
    (c : Fin q → ℤ) (S : Set ℤ)
    (hgap : ∀ i j : Fin q, i < j → c i + n + 2 ≤ c j)
    (hcover : ∀ i, Set.Icc (c i) (c i + n) ⊆ S)
    (hpoints : ∀ x : ℤ, x ∈ S → x + 1 ∈ S →
      (∃ i : Fin q, x ∈ Set.Icc (c i) (c i + n)) ∧
        (∃ j : Fin q, x + 1 ∈ Set.Icc (c j) (c j + n))) :
    (∀ x : ℤ, Set.Icc x (x + n) ⊆ S ↔ ∃ i, x = c i) ∧
      (∀ x : ℤ, Set.Icc x (x + 1) ⊆ S ↔ ∃ i,
        Set.Icc x (x + 1) ⊆ Set.Icc (c i) (c i + n) ∧
          Set.Icc (c i) (c i + n) ⊆ S) := by
  have same_interval {i j : Fin q} {x : ℤ}
      (hi : x ∈ Set.Icc (c i) (c i + n)) (hj : x + 1 ∈ Set.Icc (c j) (c j + n)) :
      i = j := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have hsep := hgap i j hij
      have hiUpper := hi.2
      have hjLower := hj.1
      omega
    · exact hij
    · have hsep := hgap j i hji
      have hiLower := hi.1
      have hjUpper := hj.2
      omega
  have hadj (x : ℤ) (hx : x ∈ S) (hx' : x + 1 ∈ S) :
      ∃ i, c i ≤ x ∧ x + 1 ≤ c i + n := by
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hpoints x hx hx'
    rw [← same_interval hi hj] at hj
    exact ⟨i, hi.1, hj.2⟩
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hleft, hright⟩ := hadj x
        (hx (Set.left_mem_Icc.mpr (by omega))) (hx ⟨by omega, by omega⟩)
      have hbound : x + n ≤ c i + n := by
        by_contra! hover
        obtain ⟨j, hjleft, hjright⟩ := hadj (c i + n)
          (hx ⟨by omega, by omega⟩) (hx ⟨by omega, by omega⟩)
        have hij : i = j := same_interval
          (Set.right_mem_Icc.mpr (by omega)) ⟨by omega, hjright⟩
        subst j
        omega
      exact ⟨i, by omega⟩
    · rintro ⟨i, rfl⟩
      exact hcover i
  · intro x
    have horder : x ≤ x + 1 := by omega
    constructor
    · intro hx
      obtain ⟨i, hleft, hright⟩ :=
        hadj x (hx (Set.left_mem_Icc.mpr horder)) (hx (Set.right_mem_Icc.mpr horder))
      exact ⟨i, Set.Icc_subset_Icc hleft hright, hcover i⟩
    · rintro ⟨i, hi, hcoveri⟩
      exact hi.trans hcoveri

/-- Both prescribed-interval equivalences hold for a set of at most two generators
per prescribed point. The sumset uses exactly `h` summands with repetition. -/
theorem nathanson_problem15 (h q n : ℕ) (N : ℤ)
    (hh : 2 ≤ h) (hq : 2 ≤ q) (hn : 1 ≤ n)
    (hN : (n : ℤ) + 2 ≤ N) (c : Fin q → ℤ)
    (hgap : ∀ i j : Fin q, j.val = i.val + 1 → N ≤ c j - c i) :
    ∃ A : Finset ℤ,
      A.card ≤ 2 * q * (n + 1) ∧
      (∀ x : ℤ, Set.Icc x (x + (n : ℤ)) ⊆ h • (A : Set ℤ) ↔
        ∃ i : Fin q, x = c i) ∧
      (∀ x : ℤ, Set.Icc x (x + 1) ⊆ h • (A : Set ℤ) ↔
        ∃ i : Fin q,
          Set.Icc x (x + 1) ⊆ Set.Icc (c i) (c i + (n : ℤ)) ∧
            Set.Icc (c i) (c i + (n : ℤ)) ⊆ h • (A : Set ℤ)) := by
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hgapAll : ∀ i j : Fin q, i < j → c i + (n : ℤ) + 2 ≤ c j := by
    cases q with
    | zero => omega
    | succ k =>
      let transGap : IsTrans ℤ (fun a b => a + (n : ℤ) + 2 ≤ b) := ⟨by
        intro a b d hab hbd
        omega⟩
      have hsucc (i : Fin k) : c i.castSucc + (n : ℤ) + 2 ≤ c i.succ := by
        have h := hgap i.castSucc i.succ rfl
        omega
      exact (Fin.liftFun_iff_succ (fun a b : ℤ => a + (n : ℤ) + 2 ≤ b) (f := c)).mpr hsucc
  let t (j : Fin (q * (n + 1))) : ℤ :=
    c (finProdFinEquiv.symm j).1 + (finProdFinEquiv.symm j).2.val
  have htarget (x : ℤ) : x ∈ Set.range t ↔
      ∃ i : Fin q, x ∈ Set.Icc (c i) (c i + (n : ℤ)) := by
    constructor
    · rintro ⟨j, rfl⟩
      let p := finProdFinEquiv.symm j
      refine ⟨p.1, Set.mem_Icc.mpr ?_⟩
      have hk := p.2.isLt
      change c p.1 ≤ c p.1 + (p.2.val : ℤ) ∧
        c p.1 + (p.2.val : ℤ) ≤ c p.1 + (n : ℤ)
      omega
    · rintro ⟨i, hxi⟩
      obtain ⟨hleft, hright⟩ := Set.mem_Icc.mp hxi
      let k : Fin (n + 1) := ⟨(x - c i).toNat, by omega⟩
      refine ⟨finProdFinEquiv (i, k), ?_⟩
      simp only [t, Equiv.symm_apply_apply, k]
      omega
  let U : ℤ := (Finset.univ.sup fun j => (t j).natAbs : ℕ)
  have hU : 0 ≤ U := Int.natCast_nonneg _
  have ht (j : Fin (q * (n + 1))) : |t j| ≤ U := by
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le.mpr (Finset.le_sup (f := fun j => (t j).natAbs) (Finset.mem_univ j))
  let M : ℤ := 2 * ((h : ℤ) * U) + 2
  let g := radixGenerators h M t
  let A := Finset.univ.image g
  refine ⟨A, ?_, ?_⟩
  · calc
      A.card ≤ (Finset.univ : Finset (Fin (q * (n + 1)) ⊕ Fin (q * (n + 1)))).card :=
        Finset.card_image_le
      _ = 2 * q * (n + 1) := by
        simp [Fintype.card_sum, Nat.mul_assoc, two_mul, Nat.add_mul]
  · have hA : (A : Set ℤ) = Set.range g := by simp [A, Finset.coe_image]
    rw [hA]
    refine interval_equivalences hn' c _ hgapAll (fun i x hx => ?_) (fun x hx hx' => ?_)
    · have hrange := (htarget x).mpr ⟨i, hx⟩
      obtain ⟨u, v, huv, hzero, hsum⟩ := (mem_range_iff_zero_code_sum hh t x).mp hrange
      exact (mem_radixGenerators_iff t).mpr ⟨u, v, huv, by simp [hzero, hsum]⟩
    · obtain ⟨hr, hr'⟩ := adjacent_mem_range hh hU t ht hx hx'
      exact ⟨(htarget x).mp hr, (htarget (x + 1)).mp hr'⟩

end D5.S3.Arith.NathansonProblem15
