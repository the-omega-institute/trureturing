/- GID: D5/S3/PrimeGaps/IntegerAverages
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the integer-average machinery and the assignment-family cardinality bound. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.AssignmentStructure

namespace LongGapsBetweenPrimes

noncomputable section

/-- The average of `f` over the integers in `[0, T)`. -/
def integerAverage (T : ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ Finset.range T, f n) / T

/-- Expand a function of residues as a sum of residue indicators. -/
lemma residue_expansion {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (n : ℕ) :
    g ⟨n % m, Nat.mod_lt n hm⟩ = ∑ a : Fin m, g a * residueIndicator m a.val n := by
  simpa [residueIndicator, Fin.ext_iff, mul_ite] using
    (Fintype.sum_ite_eq (⟨n % m, Nat.mod_lt n hm⟩ : Fin m) g).symm

/-- Express a periodic average using the frequencies of its residue classes. -/
lemma integerAverage_residue_expansion {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (T : ℕ) :
    integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) =
      ∑ a : Fin m, g a * ((∑ n ∈ Finset.range T, residueIndicator m a.val n) / T) := by
  classical
  unfold integerAverage
  simp_rw [residue_expansion hm g]
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [← Finset.mul_sum, mul_div_assoc]

/-- A bounded function of one residue class has interval-average error at most m/T. -/
theorem residue_average_bounded_error {m T : ℕ} (hm : 0 < m) (hT : 0 < T)
    (g : Fin m → ℝ) (hg : ∀ a, |g a| ≤ 1) :
    |integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) - Finset.expect Finset.univ g| ≤
      (m : ℝ) / T := by
  rw [integerAverage_residue_expansion hm, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, div_eq_mul_one_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Fin m, |g a * ((∑ n ∈ Finset.range T, residueIndicator m a.val n) / T) -
        g a * (1 / (m : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin m, 1 / (T : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul]
      have h := mul_le_mul (hg a) (residue_average_error a.isLt hT)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using h
    _ = (m : ℝ) / T := by simp; ring

/-- Averaging over complete periods equals the uniform average over residues. -/
lemma integerAverage_complete_residues {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hmq : m ∣ q) (g : Fin m → ℝ) :
    integerAverage q (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) = Finset.expect Finset.univ g := by
  rw [integerAverage_residue_expansion hm, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have hcount : ((Finset.range q).filter fun n => n % m = a.val).card = q / m := by
    simpa [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt a.isLt,
      Nat.mod_eq_zero_of_dvd hmq] using Nat.count_modEq_card q hm a.val
  simp only [residueIndicator, Finset.sum_boole, hcount,
    Nat.cast_div hmq (by positivity : (m : ℝ) ≠ 0)]
  field_simp

/-- The interval average of a bounded periodic function has error at most `m / T`. -/
lemma integerAverage_period_error {m q T : ℕ} (hm : 0 < m) (hq : 0 < q) (hT : 0 < T)
    (hmq : m ∣ q) (f : ℕ → ℝ) (hperiod : ∀ n, f (n % m) = f n) (hf : ∀ n, |f n| ≤ 1) :
    |integerAverage T f - integerAverage q f| ≤ (m : ℝ) / T := by
  simpa only [← integerAverage_complete_residues hm hq hmq, hperiod] using
    residue_average_bounded_error hm hT (fun a => f a) (fun a => hf a)

/-- Expand the average of a squared weighted sum into pairwise averages. -/
lemma integerAverage_weight_sq {ι : Type*} [Fintype ι] (T : ℕ) (c : ι → ℝ) (f : ι → ℕ → ℝ) :
    integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) =
      ∑ i, ∑ j, c i * c j * integerAverage T (fun n => f i n * f j n) := by
  simp only [integerAverage, pow_two, Finset.sum_mul_sum, mul_mul_mul_comm]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range T), ← Finset.mul_sum]
  simp only [Finset.sum_div, mul_div_assoc]

/-- Pairwise average errors give a quadratic error bound for a squared weighted sum. -/
lemma integerAverage_weight_error {ι : Type*} [Fintype ι] (q T : ℕ)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ) (E : ℝ)
    (hpair : ∀ i j, |integerAverage T (fun n => f i n * f j n) -
      integerAverage q (fun n => f i n * f j n)| ≤ E) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤ (Fintype.card ι : ℝ) ^ 2 * E := by
  simp only [integerAverage_weight_sq, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ i, ∑ j, E := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      calc
        _ ≤ 1 * 1 * |integerAverage T (fun n => f i n * f j n) -
            integerAverage q (fun n => f i n * f j n)| := by
          gcongr <;> apply hc
        _ ≤ E := by simpa using hpair i j
    _ = _ := by simp [pow_two, mul_assoc]

/-- The primes in the support of an assignment. -/
def assignmentPrimes {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) : Finset ℕ :=
  (assignmentSupport σ).image Subtype.val

/-- Every assigned prime divides `P`. -/
lemma assignmentPrimes_subset {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentPrimes σ ⊆ P.primeFactors := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
  exact q.property

/-- A prime belongs to the assigned set exactly when its assignment is nonempty. -/
lemma mem_assignmentPrimes {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) :
    p.val ∈ assignmentPrimes σ ↔ (σ p).isSome := by
  classical
  simp [assignmentPrimes, assignmentSupport]

/-- Every element of the assigned prime set is prime. -/
lemma assignmentPrimes_prime {P k : ℕ} (σ : PrimeIndex P → Option (Fin k))
    {p : ℕ} (hp : p ∈ assignmentPrimes σ) : p.Prime :=
  (Nat.mem_primeFactors.mp (assignmentPrimes_subset σ hp)).1

/-- The product of the assigned primes equals the assignment product. -/
lemma assignmentPrimes_product {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (∏ p ∈ assignmentPrimes σ, p) = assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  classical
  exact Finset.prod_image Subtype.val_injective.injOn

/-- The product of the assigned primes is positive. -/
lemma assignmentProduct_pos {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    0 < assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  exact Finset.prod_pos fun p _ => (Nat.prime_of_mem_primeFactors p.property).pos

/-- The product of the assigned primes divides `P`. -/
lemma assignmentProduct_dvd {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentProduct (fun p : PrimeIndex P => p.val) σ ∣ P := by
  rw [← assignmentPrimes_product]
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (assignmentPrimes_subset σ)).trans
    (Nat.prod_primeFactors_dvd P)

/-- The prime factors of the assignment product are exactly the assigned primes. -/
lemma assignmentProduct_primeFactors {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (assignmentProduct (fun p : PrimeIndex P => p.val) σ).primeFactors = assignmentPrimes σ := by
  rw [← assignmentPrimes_product]
  exact Nat.primeFactors_prod (fun p hp => assignmentPrimes_prime σ hp)

/-- The root selected by an assignment, with zero at unused primes. -/
def assignedRoot {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) : Fin p.val :=
  match σ p with
  | none => ⟨0, (Nat.mem_primeFactors.mp p.property).1.pos⟩
  | some i => root p i

/-- The Chinese remainder theorem realizes all assigned roots in one residue. -/
lemma exists_assignment_residue {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) :
    ∃ a : ℕ, a < assignmentProduct (fun p : PrimeIndex P => p.val) σ ∧
      ∀ p : PrimeIndex P, (σ p).isSome → a % p.val = (assignedRoot root σ p).val := by
  classical
  have hcop : (↑(assignmentSupport σ) : Set (PrimeIndex P)).Pairwise
      (fun p q => Nat.Coprime p.val q.val) := by
    intro p _ q _ hpq
    exact (Nat.coprime_primes (Nat.mem_primeFactors.mp p.property).1
      (Nat.mem_primeFactors.mp q.property).1).mpr (fun h => hpq (Subtype.ext h))
  let a := Nat.chineseRemainderOfFinset (fun p => (assignedRoot root σ p).val)
    (fun p : PrimeIndex P => p.val) (assignmentSupport σ)
    (fun p _ => (Nat.mem_primeFactors.mp p.property).1.ne_zero) hcop
  refine ⟨a.val, Nat.chineseRemainderOfFinset_lt_prod _ _ _ _, ?_⟩
  intro p hp
  have h := a.property p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (assignedRoot root σ p).isLt] using h

/-- A residue encoding the roots selected by an assignment. -/
def assignmentCode {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) : ℕ := Classical.choose (exists_assignment_residue root σ)

/-- The assignment code is smaller than its modulus. -/
lemma assignmentCode_lt {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) :
    assignmentCode root σ < assignmentProduct (fun p : PrimeIndex P => p.val) σ :=
  (Classical.choose_spec (exists_assignment_residue root σ)).1

/-- The assignment code has the prescribed residue at each assigned prime. -/
lemma assignmentCode_mod {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) (hp : (σ p).isSome) :
    assignmentCode root σ % p.val = (assignedRoot root σ p).val :=
  (Classical.choose_spec (exists_assignment_residue root σ)).2 p hp

/-- Distinct local roots make the modulus and residue code determine the assignment. -/
lemma assignmentCode_determines {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (hroot : ∀ p, Function.Injective (root p)) (σ τ : PrimeIndex P → Option (Fin k))
    (hn : assignmentProduct (fun p : PrimeIndex P => p.val) σ =
      assignmentProduct (fun p : PrimeIndex P => p.val) τ)
    (ha : assignmentCode root σ = assignmentCode root τ) : σ = τ := by
  funext p
  have hsupp : assignmentPrimes σ = assignmentPrimes τ := by
    rw [← assignmentProduct_primeFactors σ, hn, assignmentProduct_primeFactors]
  have hp : (σ p).isSome ↔ (τ p).isSome := by
    rw [← mem_assignmentPrimes, ← mem_assignmentPrimes, hsupp]
  cases hσ : σ p <;> cases hτ : τ p
  · rfl
  · simp [hσ, hτ] at hp
  · simp [hσ, hτ] at hp
  · congr 1
    apply hroot p
    apply Fin.ext
    have hs := assignmentCode_mod root σ p (by simp [hσ])
    have ht := assignmentCode_mod root τ p (by simp [hτ])
    simpa [assignedRoot, hσ, hτ] using
      hs.symm.trans ((congrArg (· % p.val) ha).trans ht)

/-- Encoding an assignment by its modulus and one CRT residue bounds its count. -/
theorem card_assignment_family_le {P k : ℕ} {ι : Type*} [Fintype ι]
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → PrimeIndex P → Option (Fin k)) (hσ : Function.Injective σ)
    {D : ℝ} (hD : 1 ≤ D)
    (hcut : ∀ i, (assignmentProduct (fun p : PrimeIndex P => p.val) (σ i) : ℝ) ≤ D) :
    (Fintype.card ι : ℝ) ≤ 4 * D ^ 2 := by
  let f (i : ι) : Fin (⌊D⌋₊ + 1) × Fin (⌊D⌋₊ + 1) :=
    (⟨assignmentProduct (fun p : PrimeIndex P => p.val) (σ i),
      Nat.lt_succ_of_le (Nat.le_floor (hcut i))⟩,
     ⟨assignmentCode root (σ i), (assignmentCode_lt root (σ i)).trans
      (Nat.lt_succ_of_le (Nat.le_floor (hcut i)))⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply hσ
    exact assignmentCode_determines root hroot (σ i) (σ j)
      (congrArg (fun x => x.1.val) hij) (congrArg (fun x => x.2.val) hij)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin, ← pow_two] at hcard
  calc
    (Fintype.card ι : ℝ) ≤ ((⌊D⌋₊ : ℝ) + 1) ^ 2 := by
      exact_mod_cast hcard
    _ ≤ (2 * D) ^ 2 := by
      gcongr
      linarith [Nat.floor_le (show 0 ≤ D by linarith)]
    _ = 4 * D ^ 2 := by ring

/-- The truncated tuple region has at most `4 * D ^ 2` elements. -/
lemma tupleRegion_card_le {P k : ℕ} (hP : Squarefree P) {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p)) :
    (Fintype.card (tupleRegion P k D) : ℝ) ≤ 4 * D ^ 2 := by
  apply card_assignment_family_le root hroot
    (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D) hD
  intro r
  rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
  exact (Finset.mem_filter.mp r.property).2.2

/-- Invariance modulo `m` implies invariance modulo every multiple of `m`. -/
lemma mod_invariant_of_dvd {m n : ℕ} (hmn : m ∣ n) (f : ℕ → ℝ)
    (hf : ∀ a, f (a % m) = f a) : ∀ a, f (a % n) = f a := by
  intro a
  rw [← hf (a % n), Nat.mod_mod_of_dvd a hmn, hf]

/-- Bound the second-moment averaging error using the periods and number of summands. -/
lemma integerAverage_bounded_periodic_weight {ι : Type*} [Fintype ι]
    {q T : ℕ} (hq : 0 < q) (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D)
    (period : ι → ℕ) (hperiod_pos : ∀ i, 0 < period i) (hperiod_q : ∀ i, period i ∣ q)
    (hperiod_D : ∀ i, (period i : ℝ) ≤ D)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ)
    (hf : ∀ i n, |f i n| ≤ 1) (hmod : ∀ i n, f i (n % period i) = f i n) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤
        (Fintype.card ι : ℝ) ^ 2 * (D ^ 2 / T) := by
  apply integerAverage_weight_error q T c hc
  intro i j
  have hbound : (Nat.lcm (period i) (period j) : ℝ) ≤ D ^ 2 := by
    calc
      _ ≤ (period i : ℝ) * period j := by
        exact_mod_cast Nat.lcm_le_mul (hperiod_pos i) (hperiod_pos j)
      _ ≤ D * D := mul_le_mul (hperiod_D i) (hperiod_D j) (Nat.cast_nonneg _) hD
      _ = D ^ 2 := (pow_two D).symm
  refine (integerAverage_period_error
    (Nat.lcm_pos (hperiod_pos i) (hperiod_pos j)) hq hT
    (Nat.lcm_dvd (hperiod_q i) (hperiod_q j))
    (fun n => f i n * f j n) ?_ ?_).trans
      (div_le_div_of_nonneg_right hbound (Nat.cast_nonneg T))
  · intro n
    rw [mod_invariant_of_dvd (Nat.dvd_lcm_left _ _) (f i) (hmod i),
      mod_invariant_of_dvd (Nat.dvd_lcm_right _ _) (f j) (hmod j)]
  · intro n
    rw [abs_mul]
    exact mul_le_one₀ (hf i n) (abs_nonneg _) (hf j n)

/-- The residues of `n` modulo the prime divisors of `P`. -/
def residueVector (P n : ℕ) : (p : PrimeIndex P) → Fin p.val :=
  fun p => ⟨n % p.val, Nat.mod_lt n (Nat.mem_primeFactors.mp p.property).1.pos⟩

open scoped Fin.CommRing in
/-- The Chinese remainder theorem identifies a full-period average with a product average. -/
lemma integerAverage_residues {P : ℕ} (hP : Squarefree P)
    (f : ((p : PrimeIndex P) → Fin p.val) → ℝ) :
    integerAverage P (fun n => f (residueVector P n)) = Finset.expect Finset.univ f := by
  classical
  let : NeZero P := ⟨hP.ne_zero⟩
  let (p : PrimeIndex P) : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : PrimeIndex P => Nat.Coprime p.val q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.property)
      (Nat.prime_of_mem_primeFactors q.property)).mpr (fun h => hpq (Subtype.ext h))
  have hprod : (∏ p : PrimeIndex P, p.val) = P :=
    (Finset.prod_subtype (F := inferInstanceAs (Fintype (PrimeIndex P)))
      P.primeFactors (fun _ => Iff.rfl) id).symm.trans (Nat.prod_primeFactors_of_squarefree hP)
  let e : Fin P ≃+* ((p : PrimeIndex P) → Fin p.val) :=
    (ZMod.finEquiv P).trans <| (ZMod.ringEquivCongr hprod.symm).trans <|
      (ZMod.prodEquivPi (fun p : PrimeIndex P => p.val) hcop).trans <|
        RingEquiv.piCongrRight (fun p => (ZMod.finEquiv p.val).symm)
  have he (n : Fin P) : e n = residueVector P n.val := by
    calc
      e n = e (Nat.cast n.val : Fin P) := congrArg e (Fin.cast_val_eq_self n).symm
      _ = (Nat.cast n.val : (p : PrimeIndex P) → Fin p.val) := map_natCast e n.val
      _ = residueVector P n.val := rfl
  have h := Fintype.expect_equiv e.toEquiv
    (fun n : Fin P => f (residueVector P n.val)) f (fun n => congrArg f (he n).symm)
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin] at h
  rw [Fin.sum_univ_eq_sum_range (fun n => f (residueVector P n)) P] at h
  simpa only [integerAverage, Fintype.expect_eq_sum_div_card] using h

/-- Every residue factor has absolute value at most one. -/
lemma abs_residueFactor_le_one {p : ℕ} (hp : 1 < p) (a t : Fin p) :
    |residueFactor a t| ≤ 1 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp
  unfold residueFactor
  split_ifs
  · norm_num
  · rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    exact (div_le_one (by linarith)).mpr (by linarith)

/-- Every unnormalized local basis value has absolute value at most one. -/
lemma abs_rawLocalBasis_le_one {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (i : Option (Fin k)) (t : Fin p) : |rawLocalBasis root i t| ≤ 1 := by
  cases i with
  | none => simp [rawLocalBasis]
  | some j => exact abs_residueFactor_le_one hp _ _

/-- A product of local basis values bounded by one is bounded by one. -/
lemma abs_productBasis_le_one {α : Type*} [Fintype α] {Ω J : α → Type*}
    (f : (p : α) → J p → Ω p → ℝ) (hf : ∀ p i t, |f p i t| ≤ 1)
    (σ : (p : α) → J p) (t : (p : α) → Ω p) : |productBasis f σ t| ≤ 1 := by
  rw [productBasis, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => hf p _ _)

/-- Coefficients bounded by one give tuple amplitudes bounded by one. -/
lemma tupleAmplitude_abs_le {P k : ℕ}
    (h : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (r : DivisorTuple P k) :
    |tupleAmplitude r| ≤ 1 := by
  rw [tupleAmplitude, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
    (fun i _ => h _ (r i).property)

/-- Every assigned prime divides the assignment product. -/
lemma prime_dvd_assignmentProduct {P k : ℕ} (σ : PrimeIndex P → Option (Fin k))
    (p : PrimeIndex P) (hp : (σ p).isSome) :
    p.val ∣ assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)

/-- A product basis function depends only on the residue modulo its assignment product. -/
lemma basisProduct_mod_invariant {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (σ : PrimeIndex P → Option (Fin k)) (n : ℕ) :
    productBasis f σ (residueVector P (n % assignmentProduct (fun p : PrimeIndex P => p.val) σ)) =
      productBasis f σ (residueVector P n) := by
  unfold productBasis
  apply Finset.prod_congr rfl
  intro p _
  cases hσ : σ p with
  | none => simp only [hf]
  | some i =>
      congr 1
      exact Fin.ext (Nat.mod_mod_of_dvd n
        (prime_dvd_assignmentProduct σ p (by simp [hσ])))

/-- The truncated tuple sum formed from an arbitrary family of local basis functions. -/
def basisWeight (P k : ℕ) (D : ℝ)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D, tupleAmplitude r.val * productBasis f (tupleAssignment r.val) t

/-- A D^6/T error is sufficient after taking κ = 1/8 in the final parameter choice. -/
theorem basisWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hfnone : ∀ p t, f p none t = 1) (hf : ∀ p i t, |f p i t| ≤ 1) :
    |integerAverage T (fun n => basisWeight P k D f (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => basisWeight P k D f t ^ 2)| ≤ 16 * D ^ 6 / T := by
  rw [← integerAverage_residues hP (fun t => basisWeight P k D f t ^ 2)]
  have hcut (r : tupleRegion P k D) :
      (assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r.val) : ℝ) ≤ D := by
    rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
    exact (Finset.mem_filter.mp r.property).2.2
  calc
    _ ≤ (Fintype.card (tupleRegion P k D) : ℝ) ^ 2 * (D ^ 2 / T) :=
      integerAverage_bounded_periodic_weight (Nat.pos_of_ne_zero hP.ne_zero) hT
        (zero_le_one.trans hD)
        (fun r : tupleRegion P k D =>
          assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r.val))
        (fun r => assignmentProduct_pos _) (fun r => assignmentProduct_dvd _) hcut
        (fun r => tupleAmplitude r.val) (fun r => tupleAmplitude_abs_le hcoeff r.val)
        (fun r n => productBasis f (tupleAssignment r.val) (residueVector P n))
        (fun r n => abs_productBasis_le_one f hf _ _)
        (fun r n => basisProduct_mod_invariant f hfnone _ _)
    _ ≤ (4 * D ^ 2) ^ 2 * (D ^ 2 / T) := by
      gcongr
      exact tupleRegion_card_le hP hD root hroot
    _ = 16 * D ^ 6 / T := by ring

/-- The residue weight's second-moment averaging error is at most `16 * D ^ 6 / T`. -/
lemma residueWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    |integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2)| ≤ 16 * D ^ 6 / T :=
  basisWeight_interval_error hP hT hD root hroot hcoeff (fun p => rawLocalBasis (root p))
    (fun _ _ => rfl) (fun p i t =>
      abs_rawLocalBasis_le_one (Nat.mem_primeFactors.mp p.property).1.one_lt _ i t)


/-- Every divisor tuple has positive product. -/
lemma tupleProduct_pos {P k : ℕ} (r : DivisorTuple P k) : 0 < tupleProduct r := by
  exact Finset.prod_pos fun i _ => Nat.pos_of_mem_divisors (r i).property

/-- Inserting a divisor multiplies the tuple product by that divisor. -/
lemma tupleProduct_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) : tupleProduct (i.insertNth d r) = d.val * tupleProduct r := by
  unfold tupleProduct
  rw [Fin.prod_univ_succAbove _ i]
  simp

/-- Insertion preserves pairwise coprimality iff the new divisor is coprime to the rest. -/
lemma tuplePairwise_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) :
    (∀ j l, j ≠ l →
      Nat.Coprime (i.insertNth (α := fun _ => DivisorIndex P) d r j).val
        (i.insertNth (α := fun _ => DivisorIndex P) d r l).val) ↔
      (∀ j l, j ≠ l → Nat.Coprime (r j).val (r l).val) ∧ d.val.Coprime (tupleProduct r) := by
  simp [Fin.forall_iff_succAbove i, tupleProduct, Nat.coprime_prod_right_iff,
    Nat.coprime_comm, forall_and, and_comm]

/-- Characterize truncated-region membership after inserting one divisor. -/
lemma tupleRegion_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) (D : ℝ) :
    i.insertNth d r ∈ tupleRegion P (k + 1) D ↔
      r ∈ tupleRegion P k D ∧ (d.val : ℝ) ≤ D / tupleProduct r ∧
        d.val.Coprime (tupleProduct r) := by
  classical
  have hr : 0 < (tupleProduct r : ℝ) := by exact_mod_cast tupleProduct_pos r
  have hd : (1 : ℝ) ≤ d.val := by exact_mod_cast Nat.pos_of_mem_divisors d.property
  simp only [tupleRegion, Finset.mem_filter, Finset.mem_univ, true_and,
    tuplePairwise_insertNth, tupleProduct_insertNth, Nat.cast_mul, le_div_iff₀ hr]
  constructor
  · rintro ⟨⟨hpair, hcop⟩, hD⟩
    exact ⟨⟨hpair, (le_mul_of_one_le_left hr.le hd).trans hD⟩, hD, hcop⟩
  · rintro ⟨⟨hpair, _⟩, hD, hcop⟩
    exact ⟨⟨hpair, hcop⟩, hD⟩

/-- Split a truncated tuple sum by one coordinate. -/
lemma tupleSum_split {P k : ℕ} (i : Fin (k + 1)) (D : ℝ)
    (G : Fin (k + 1) → DivisorIndex P → ℝ) :
    (∑ r ∈ tupleRegion P (k + 1) D, ∏ j, G j (r j)) =
      ∑ r ∈ tupleRegion P k D,
        (∑ d : DivisorIndex P,
          if (d.val : ℝ) ≤ D / tupleProduct r ∧ d.val.Coprime (tupleProduct r) then G i d else 0) *
          ∏ j, G (i.succAbove j) (r j) := by
  classical
  let f (r : DivisorTuple P (k + 1)) : ℝ :=
    if r ∈ tupleRegion P (k + 1) D then ∏ j, G j (r j) else 0
  have h := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => DivisorIndex P) i)
    (fun dr => f (i.insertNth dr.1 dr.2)) f (fun _ => rfl)
  rw [Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa [f, tupleRegion_insertNth, Fin.prod_univ_succAbove _ i,
    ite_and, Finset.sum_mul, ite_mul] using h.symm

end

end LongGapsBetweenPrimes
