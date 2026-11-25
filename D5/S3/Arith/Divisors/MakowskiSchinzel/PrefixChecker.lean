/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/PrefixChecker
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix00.prefix00_checked
   digest: Exact prefix products and rank comparison for prime support exclusion. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Tactic

/-! Exact finite comparisons for deletion inequalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.Certificate

/-- Unreduced numerator of the reciprocal geometric sum. -/
def geomNum (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => r * geomNum r k + 1

/-- Unreduced numerator of a list of factors `(q-1)/q`. -/
def prodNum (bs : List ℕ) : ℕ := (bs.map (· - 1)).prod

/-- Unreduced denominator of a list of factors `(q-1)/q`. -/
def prodDen (bs : List ℕ) : ℕ := bs.prod

/-- Rational product used in the deletion inequality. -/
def lowerProduct (bs : List ℕ) : ℚ :=
  (bs.map fun q : ℕ => ((q : ℚ) - 1) / (q : ℚ)).prod

/-- Check one complete prefix by natural-number cross multiplication. -/
def checkRow (r : ℕ) (bs : List ℕ) : Bool :=
  decide (r ^ bs.length * prodDen bs ≤ geomNum r bs.length * prodNum bs)

/-- Check all prefixes; positive denominators are checked explicitly. -/
def checkPrefixes (r : ℕ) (bs : List ℕ) : Bool :=
  decide (2 ≤ r) && bs.all (fun q => decide (2 ≤ q)) &&
    (List.range (bs.length + 1)).all (fun k => checkRow r (bs.take k))

private theorem geomNum_cast {r : ℕ} (hr : 0 < r) (k : ℕ) :
    (geomNum r k : ℚ) = geom r k * (r : ℚ) ^ k := by
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  induction k with
  | zero => simp [geomNum, geom]
  | succ k ih =>
    simp only [geomNum, Nat.cast_add, Nat.cast_mul, Nat.cast_one, ih]
    have hrec : geom r (k + 1) = geom r k + (r : ℚ)⁻¹ ^ (k + 1) := by
      unfold geom
      rw [Finset.sum_range_succ]
    rw [hrec]
    change (r : ℚ) * (geom r k * (r : ℚ) ^ k) + 1 =
      (geom r k + (r : ℚ)⁻¹ ^ (k + 1)) * (r : ℚ) ^ (k + 1)
    rw [add_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hr0)]
    rw [pow_succ]
    ring

private theorem lowerProduct_eq (bs : List ℕ) (hb : ∀ q ∈ bs, 1 ≤ q) :
    lowerProduct bs = (prodNum bs : ℚ) / prodDen bs := by
  induction bs with
  | nil => simp [lowerProduct, prodNum, prodDen]
  | cons q bs ih =>
    have hq := hb q (by simp)
    have ht : ∀ x ∈ bs, 1 ≤ x := fun x hx => hb x (by simp [hx])
    simp only [lowerProduct, List.map_cons, List.prod_cons]
    change ((q : ℚ) - 1) / q * lowerProduct bs = _
    rw [ih ht]
    simp only [prodNum, prodDen, List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [Nat.cast_sub hq, Nat.cast_one, mul_div_mul_comm]

/-- The integer check implies the required geometric deletion bound. -/
theorem checkRow_sound {r : ℕ} {bs : List ℕ} (hr : 0 < r)
    (hb : ∀ q ∈ bs, 1 ≤ q) :
    checkRow r bs = true ↔ 1 ≤ geom r bs.length * lowerProduct bs := by
  have hd : 0 < prodDen bs := List.prod_pos (fun q hq => by have := hb q hq; omega)
  have hdq : (0 : ℚ) < prodDen bs := by exact_mod_cast hd
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  constructor
  · intro hc
    have hx : (r : ℚ) ^ bs.length * (prodDen bs : ℚ) ≤
        (geomNum r bs.length : ℚ) * (prodNum bs : ℚ) := by
      exact_mod_cast (of_decide_eq_true hc : _)
    rw [geomNum_cast hr] at hx
    rw [lowerProduct_eq bs hb]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hdq).2
    apply (mul_le_mul_iff_right₀ (pow_pos hrq bs.length)).mp
    convert hx using 1 <;> ring
  · intro hc
    apply decide_eq_true_eq.mpr
    have hh : (prodDen bs : ℚ) ≤ geom r bs.length * (prodNum bs : ℚ) := by
      have h : (1 : ℚ) ≤ (geom r bs.length * (prodNum bs : ℚ)) / prodDen bs := by
        simpa only [lowerProduct_eq bs hb, ← mul_div_assoc] using hc
      simpa only [one_mul] using (le_div_iff₀ hdq).mp h
    have hx : (r : ℚ) ^ bs.length * (prodDen bs : ℚ) ≤
        (geomNum r bs.length : ℚ) * (prodNum bs : ℚ) := by
      rw [geomNum_cast hr]
      have h := mul_le_mul_of_nonneg_right hh (pow_nonneg hrq.le bs.length)
      convert h using 1 <;> ring
    exact_mod_cast hx

private theorem factor_nonneg (q : ℕ) : 0 ≤ ((q : ℚ) - 1) / q := by
  by_cases hq : q = 0
  · simp [hq]
  · have h : (1 : ℚ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)

private theorem factor_mono {a b : ℕ} (hab : a ≤ b) :
    ((a : ℚ) - 1) / a ≤ ((b : ℚ) - 1) / b := by
  by_cases ha : a = 0
  · simpa [ha] using factor_nonneg b
  have ha' : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb' : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  rw [div_le_div_iff₀ ha' hb']
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  nlinarith

/-- Coordinatewise lower ranks give a lower bound, including entries equal to zero. -/
theorem lowerProduct_mono {as bs : List ℕ} (h : List.Forall₂ (· ≤ ·) as bs) :
    lowerProduct as ≤ lowerProduct bs := by
  induction h with
  | nil => rfl
  | @cons a b as bs hab ht ih =>
    change ((a : ℚ) - 1) / a * lowerProduct as ≤
      ((b : ℚ) - 1) / b * lowerProduct bs
    apply mul_le_mul (factor_mono hab) ih
    · unfold lowerProduct
      apply List.prod_nonneg
      intro x hx
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      exact factor_nonneg q
    · exact factor_nonneg b

/-- Every checked table supplies its geometric product bound for every prefix length. -/
theorem checkPrefixes_sound {r k : ℕ} {bs : List ℕ}
    (hc : checkPrefixes r bs = true) :
    1 ≤ geom r k * lowerProduct (bs.take k) := by
  have hprefix (i : ℕ) (hi : i ≤ bs.length) :
      1 ≤ geom r i * lowerProduct (bs.take i) := by
    have hc' := hc
    simp only [checkPrefixes, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range] at hc'
    have h := (checkRow_sound (by omega : 0 < r)
      (fun q hq => le_trans (by omega : 1 ≤ 2)
        (hc'.1.2 q (List.mem_of_mem_take hq)))).mp (hc'.2 i (by omega))
    simpa only [List.length_take, Nat.min_eq_left hi] using h
  by_cases hk : k ≤ bs.length
  · exact hprefix k hk
  · have hlen : bs.length ≤ k := by omega
    have hg : geom r bs.length ≤ geom r k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro i _ _
      exact pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r)) i
    have hp : 0 ≤ lowerProduct bs := by
      unfold lowerProduct
      apply List.prod_nonneg
      intro x hx
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      exact factor_nonneg q
    have h := (hprefix bs.length le_rfl).trans (by
      simpa using mul_le_mul_of_nonneg_right hg hp)
    simpa only [List.take_of_length_le hlen, List.take_length] using h

/-- A checked table excludes every rank-dominated actual list, of any prime size. -/
theorem exclude_of_prefix {r : ℕ} {table actual : List ℕ}
    (hc : checkPrefixes r table = true)
    (hrank : List.Forall₂ (· ≤ ·) (table.take actual.length) actual) :
    ¬geom r actual.length * lowerProduct actual < 1 := by
  have hbound := checkPrefixes_sound (k := actual.length) hc
  have hmono := lowerProduct_mono hrank
  have hgeom : 0 ≤ geom r actual.length := by
    apply Finset.sum_nonneg
    intro i hi
    exact pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r)) _
  exact not_lt_of_ge (hbound.trans (mul_le_mul_of_nonneg_left hmono hgeom))

/-- Saturation below every table entry implies coordinatewise rank bounds. -/
theorem ranks_of_saturated {table actual : List ℕ}
    (ht : table.Pairwise (· ≤ ·)) (ha : actual.Pairwise (· < ·))
    (hlen : actual.length ≤ table.length)
    (hcover : ∀ q ∈ actual, (∃ b ∈ table, q < b) → q ∈ table) :
    List.Forall₂ (· ≤ ·) (table.take actual.length) actual := by
  induction actual generalizing table with
  | nil => simp
  | cons a actual ih =>
    cases table with
    | nil => simp at hlen
    | cons b table =>
      rw [List.pairwise_cons] at ht ha
      have hba : b ≤ a := by
        by_contra hn
        have hm := hcover a (by simp) ⟨b, by simp, by omega⟩
        rcases List.mem_cons.mp hm with hm | hm
        · omega
        · have := ht.1 a hm
          omega
      have htcover : ∀ q ∈ actual, (∃ c ∈ table, q < c) → q ∈ table := by
        intro q hq hw
        have hm := hcover q (by simp [hq]) (by
          obtain ⟨c, hc, hqc⟩ := hw
          exact ⟨c, by simp [hc], hqc⟩)
        rcases List.mem_cons.mp hm with hm | hm
        · have := ha.1 q hq
          omega
        · exact hm
      simp only [List.length_cons, List.take_succ_cons]
      exact List.Forall₂.cons hba (ih ht.2 ha.2 (by simpa using hlen) htcover)

/-- A proper factor disproves primality without a primality oracle. -/
def properFactor (q d : ℕ) : Bool :=
  decide (2 ≤ d) && decide (d < q) && decide (q % d = 0)

/-- Cover each progression position by the table, an exclusion, or a proper factor. -/
def checkCover (r : ℕ) (forbidden table factors : List ℕ) : Bool :=
  (List.range factors.length).all fun k =>
    let q := 2 * r * k + 1
    table.contains q || forbidden.any (fun s => decide (s ∣ q - 1)) ||
      decide (q < 2) || properFactor q (factors[k]!)

/-- A table's entries lie below the first unchecked progression position. -/
def checkTableBound (r : ℕ) (table factors : List ℕ) : Bool :=
  table.all fun b => decide (b ≤ 2 * r * factors.length + 1)

private theorem properFactor_not_prime {q d : ℕ} (h : properFactor q d = true) :
    ¬q.Prime := by
  simp only [properFactor, Bool.and_eq_true, decide_eq_true_eq] at h
  intro hp
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h.2) with hd | hd
  · omega
  · omega

/-- Every admissible prime in the checked progression is in the table. -/
theorem checkCover_sound {r k : ℕ} {forbidden table factors : List ℕ}
    (hc : checkCover r forbidden table factors = true) (hk : k < factors.length)
    (hp : (2 * r * k + 1).Prime)
    (hf : ∀ s ∈ forbidden, ¬s ∣ 2 * r * k) : 2 * r * k + 1 ∈ table := by
  simp only [checkCover, List.all_eq_true, List.mem_range] at hc
  have h := hc k hk
  simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h with ((ht | ⟨s, hs, hd⟩) | hsmall) | hfactor
  · exact ht
  · exact False.elim (hf s hs (by simpa using hd))
  · have := hp.two_le
    omega
  · exact False.elim (properFactor_not_prime hfactor hp)

/-- Certified finite progression coverage bounds ranks of an unbounded prime list. -/
theorem ranks_of_cover {r : ℕ} {forbidden table factors actual : List ℕ}
    (hc : checkCover r forbidden table factors = true)
    (hb : checkTableBound r table factors = true)
    (ht : table.Pairwise (· ≤ ·)) (ha : actual.Pairwise (· < ·))
    (hlen : actual.length ≤ table.length)
    (hp : ∀ q ∈ actual, q.Prime)
    (hf : ∀ q ∈ actual, ∀ s ∈ forbidden, ¬s ∣ q - 1)
    (hprog : ∀ q ∈ actual, ∃ k, q = 2 * r * k + 1) :
    List.Forall₂ (· ≤ ·) (table.take actual.length) actual := by
  apply ranks_of_saturated ht ha hlen
  intro q hq hw
  obtain ⟨b, hbt, hqb⟩ := hw
  obtain ⟨k, rfl⟩ := hprog q hq
  have hbound : b ≤ 2 * r * factors.length + 1 := by
    simp only [checkTableBound, List.all_eq_true, decide_eq_true_eq] at hb
    exact hb b hbt
  have hk : k < factors.length := by nlinarith
  exact checkCover_sound hc hk (hp _ hq) (by simpa using hf _ hq)

#print axioms checkRow_sound
#print axioms checkPrefixes_sound
#print axioms lowerProduct_mono
#print axioms exclude_of_prefix
#print axioms ranks_of_saturated
#print axioms checkCover_sound
#print axioms ranks_of_cover



/-- Finite data certifying lower ranks, including a composite witness at each omitted slot. -/
structure PrefixCertificate where
  r : ℕ
  forbidden : List ℕ
  table : List ℕ
  factors : List ℕ
  deriving Inhabited

/-- Every semantic requirement is covered by an executable Boolean check. -/
def PrefixCertificate.check (c : PrefixCertificate) : Bool :=
  checkPrefixes c.r c.table && checkCover c.r c.forbidden c.table c.factors &&
    checkTableBound c.r c.table c.factors && decide (c.table.Pairwise (· ≤ ·))

/-- A checked collection supplies the full check for each of its member certificates. -/
theorem checked_member {cs : List PrefixCertificate} (hc : cs.all (·.check) = true)
    {c : PrefixCertificate} (hmem : c ∈ cs) : c.check = true := by
  exact List.all_eq_true.mp hc c hmem

#print axioms checked_member




/-- Natural-number thresholds rule out joint deletion inequalities under a total budget. -/
def checkThreshold (T : ℕ) (only5 only11 both : List ℕ) (w uMin vMin : ℕ) : Bool :=
  decide (T < uMin + vMin + w) &&
    (List.range uMin).all (fun u => checkRow 5 (only5.take u ++ both.take w)) &&
    (List.range vMin).all (fun v => checkRow 11 (only11.take v ++ both.take w))

/-- A threshold certificate covers every triple, without assuming disjoint optima coexist. -/
theorem checkThreshold_sound {T u v w uMin vMin : ℕ}
    {only5 only11 both : List ℕ}
    (hc : checkThreshold T only5 only11 both w uMin vMin = true)
    (h5 : ∀ q ∈ only5, 1 ≤ q) (h11 : ∀ q ∈ only11, 1 ≤ q)
    (hb : ∀ q ∈ both, 1 ≤ q) (hbudget : u + v + w ≤ T) :
    ¬(geom 5 (u + w) * lowerProduct (only5.take u ++ both.take w) < 1 ∧
      geom 11 (v + w) * lowerProduct (only11.take v ++ both.take w) < 1) := by
  simp only [checkThreshold, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hc
  intro hbad
  have hpos {as bs : List ℕ} {i j : ℕ}
      (ha : ∀ q ∈ as, 1 ≤ q) (hb : ∀ q ∈ bs, 1 ≤ q) :
      ∀ q ∈ as.take i ++ bs.take j, 1 ≤ q := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ha q (List.mem_of_mem_take hq)
    · exact hb q (List.mem_of_mem_take hq)
  have hraise (r k : ℕ) (bs : List ℕ) (hlen : bs.length ≤ k)
      (h : 1 ≤ geom r bs.length * lowerProduct bs) :
      1 ≤ geom r k * lowerProduct bs := by
    apply h.trans
    apply mul_le_mul_of_nonneg_right
    · unfold geom
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hlen))
      intro i _ _
      exact pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r)) i
    · unfold lowerProduct
      apply List.prod_nonneg
      intro x hx
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      exact factor_nonneg q
  by_cases huMin : u < uMin
  · have h := (checkRow_sound (by decide : 0 < 5) (hpos h5 hb)).mp (hc.1.2 u huMin)
    have hh := hraise 5 (u + w) _ (by
      simp only [List.length_append, List.length_take]
      omega) h
    exact (not_lt_of_ge hh) hbad.1
  · have hvMin : v < vMin := by omega
    have h := (checkRow_sound (by decide : 0 < 11) (hpos h11 hb)).mp (hc.2 v hvMin)
    have hh := hraise 11 (v + w) _ (by
      simp only [List.length_append, List.length_take]
      omega) h
    exact (not_lt_of_ge hh) hbad.2

/-- Check one threshold row for every shared-class count within the budget. -/
def checkJoint (T : ℕ) (only5 only11 both : List ℕ)
    (thresholds : List (ℕ × ℕ)) : Bool :=
  (List.range (T + 1)).all fun w =>
    checkThreshold T only5 only11 both w (thresholds[w]!).1 (thresholds[w]!).2

/-- The finite threshold table rules out all joint count triples in the budget. -/
theorem checkJoint_sound {T u v w : ℕ} {only5 only11 both : List ℕ}
    {thresholds : List (ℕ × ℕ)}
    (hc : checkJoint T only5 only11 both thresholds = true)
    (h5 : ∀ q ∈ only5, 1 ≤ q) (h11 : ∀ q ∈ only11, 1 ≤ q)
    (hb : ∀ q ∈ both, 1 ≤ q)
    (hbudget : u + v + w ≤ T) :
    ¬(geom 5 (u + w) * lowerProduct (only5.take u ++ both.take w) < 1 ∧
      geom 11 (v + w) * lowerProduct (only11.take v ++ both.take w) < 1) := by
  simp only [checkJoint, List.all_eq_true, List.mem_range] at hc
  exact checkThreshold_sound (hc w (by omega)) h5 h11 hb hbudget

#print axioms checkThreshold_sound
#print axioms checkJoint_sound


end D5.S3.Arith.MakowskiSchinzel.Certificate
