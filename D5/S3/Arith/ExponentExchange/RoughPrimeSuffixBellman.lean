/- GID: D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman
   generality: G
   mirror-B: D5/B/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: [mathlib/module/Mathlib.NumberTheory.PrimeCounting]
   utility: none
   digest: Exact suffix decomposition for products of consecutive prime powers. -/

import D5.S3.Arith.RobinExponentSwap
import D5.S3.Arith.ExponentExchange.IntegerSwap
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

namespace D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman

open D5.S3.Arith.RobinExponentSwap

noncomputable section

/-- The `i`-th prime strictly above the cutoff `y`. -/
def prime (y i : ℕ) : ℕ := Nat.nth Nat.Prime (Nat.primeCounting y + i)

/-- The integer represented by a consecutive prime-exponent suffix. -/
def suffixNumber (y : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 1
  | i, a :: t => prime y i ^ a * suffixNumber y (i + 1) t

/-- The normalized divisor-sum product of a consecutive prime-exponent suffix. -/
def suffixWeight (y : ℕ) : ℕ → List ℕ → ℝ
  | _, [] => 1
  | i, a :: t => reciprocalGeomSum (prime y i) a * suffixWeight y (i + 1) t

/-- A positive exponent starts the suffix; zero terminates it. -/
def Ordered : ℕ → List ℕ → Prop
  | _, [] => True
  | h, a :: t => 0 < a ∧ a ≤ h ∧ Ordered a t

/-- Actual list feasibility at a suffix state. -/
def Feasible (y i b h : ℕ) (t : List ℕ) : Prop :=
  Ordered h t ∧ suffixNumber y i t ≤ b

/-- The integer budget bounds the length of every actual feasible suffix,
so a state has only finitely many exponent lists. -/
theorem feasible_finite (y i b h : ℕ) :
    {t : List ℕ | Feasible y i b h t}.Finite := by
  have number_length (i h : ℕ) (t : List ℕ) (ht : Ordered h t) :
      t.length < suffixNumber y i t := by
    induction t generalizing i h with
    | nil => simp [suffixNumber]
    | cons a t ih =>
        obtain ⟨ha, _, htail⟩ := ht
        have ha0 : a ≠ 0 := by omega
        have hq : 2 ≤ prime y i ^ a :=
          Nat.succ_le_iff.mpr (one_lt_pow' (Nat.prime_nth_prime _).one_lt ha0)
        have htailnum := ih (i + 1) a htail
        have hmul : 2 * suffixNumber y (i + 1) t ≤
            prime y i ^ a * suffixNumber y (i + 1) t :=
          Nat.mul_le_mul_right _ hq
        simp only [suffixNumber, List.length_cons]
        omega
  have all_le (h : ℕ) (t : List ℕ) (ht : Ordered h t) :
      ∀ a ∈ t, a ≤ h := by
    induction t generalizing h with
    | nil => simp
    | cons a t ih =>
        obtain ⟨_, hah, htail⟩ := ht
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hah
        · exact (ih a htail x hx).trans hah
  let lift (a : ℕ) : Fin (h + 1) :=
    ⟨a % (h + 1), Nat.mod_lt _ (by omega)⟩
  have hfinite :
      {t : List ℕ | t.length ≤ b ∧ ∀ a ∈ t, a ≤ h}.Finite := by
    have hf := (List.finite_length_le (Fin (h + 1)) b).image
      (fun t : List (Fin (h + 1)) => t.map Fin.val)
    apply hf.subset
    intro t ht
    refine ⟨t.map lift, ?_, ?_⟩
    · simpa using ht.1
    · simp only [List.map_map]
      calc
        List.map (Fin.val ∘ lift) t = List.map id t := by
          apply List.map_congr_left
          intro a ha
          exact Nat.mod_eq_of_lt (by have := ht.2 a ha; omega)
        _ = t := List.map_id t
  apply hfinite.subset
  intro t ht
  exact ⟨(number_length i h t ht.1).le.trans ht.2, all_le h t ht.1⟩

/-- The semantic maximum over actual feasible prime-exponent lists. -/
noncomputable def V (y i b h : ℕ) : ℝ :=
  if hb : 1 ≤ b then
    suffixWeight y i (Classical.choose
      (Set.exists_max_image _ (suffixWeight y i) (feasible_finite y i b h)
        ⟨[], by simp [Feasible, Ordered, suffixNumber, hb]⟩))
  else 0

/-- All prime factors of the integer are strictly above the cutoff. -/
def Rough (y n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → y < p

/-- The actual maximum of sigma(n)/n over rough integers in `[1, B]`. -/
noncomputable def U (y B : ℕ) : ℝ := by
  classical
  exact if hB : 1 ≤ B then
    let s := (Finset.Icc 1 B).filter (Rough y)
    let values := s.image (fun n => (ArithmeticFunction.sigma 1 n : ℝ) / n)
    values.max' (by
      have h1 : 1 ∈ s := by
        simp only [s, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨le_rfl, hB⟩, ?_⟩
        intro p hp hpd
        exact (hp.ne_one (Nat.dvd_one.mp hpd)).elim
      exact ⟨_, Finset.mem_image.mpr ⟨1, h1, rfl⟩⟩)
  else 0

/-- The largest exponent of the first allowed prime that fits the root budget. -/
def rootCap (y B : ℕ) : ℕ := Nat.log (prime y 0) B

/-- The terminal value together with every allowed positive-exponent branch. -/
noncomputable def branchValues (y i b h : ℕ) : Finset ℝ := by
  classical
  exact insert 1 (((Finset.Icc 1 h).filter (fun a => prime y i ^ a ≤ b)).image
    (fun a => reciprocalGeomSum (prime y i) a * V y (i + 1) (b / prime y i ^ a) a))

/-- The exact finite Bellman equation, upper bound, attaining suffix, and
strict budget descent for every nonempty branch. -/
theorem bellman_complete (y i b h : ℕ) (hb : 1 ≤ b) :
    V y i b h = (branchValues y i b h).max' (by
      classical
      exact ⟨1, Finset.mem_insert_self _ _⟩) ∧
    (∀ t : List ℕ, Feasible y i b h t → suffixWeight y i t ≤ V y i b h) ∧
    (∃ t : List ℕ, Feasible y i b h t ∧ suffixWeight y i t = V y i b h) ∧
    (∀ a : ℕ, 1 ≤ a → prime y i ^ a ≤ b → b / prime y i ^ a < b) := by
  classical
  have split (j c k a : ℕ) (u : List ℕ) :
      Feasible y j c k (a :: u) ↔
        1 ≤ a ∧ a ≤ k ∧ prime y j ^ a ≤ c ∧
          Feasible y (j + 1) (c / prime y j ^ a) a u := by
    have hu : 0 < suffixNumber y (j + 1) u := by
      induction u generalizing j with
      | nil => simp [suffixNumber]
      | cons d u ih =>
          simp only [suffixNumber]
          exact Nat.mul_pos (pow_pos (Nat.prime_nth_prime _).pos _) (ih (j + 1))
    have hp : 0 < prime y j ^ a := pow_pos (Nat.prime_nth_prime _).pos _
    constructor
    · rintro ⟨⟨ha, hak, htail⟩, hbudget⟩
      refine ⟨ha, hak, ?_, htail, ?_⟩
      · simp only [suffixNumber] at hbudget
        nlinarith
      · simp only [suffixNumber] at hbudget
        exact (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hbudget)
    · rintro ⟨ha, hak, _, htail, hbudget⟩
      refine ⟨⟨ha, hak, htail⟩, ?_⟩
      simp only [suffixNumber]
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).1 hbudget
  have spec (j c k : ℕ) (hc : 1 ≤ c) :
      ∃ t : List ℕ, Feasible y j c k t ∧
        suffixWeight y j t = V y j c k ∧
        ∀ u : List ℕ, Feasible y j c k u →
          suffixWeight y j u ≤ V y j c k := by
    let exists_max := Set.exists_max_image _ (suffixWeight y j)
      (feasible_finite y j c k)
      ⟨[], by simp [Feasible, Ordered, suffixNumber, hc]⟩
    let t := Classical.choose exists_max
    have ht := Classical.choose_spec exists_max
    refine ⟨t, ht.1, ?_, ?_⟩
    · simp only [V, dif_pos hc]
      rfl
    · intro u hu
      simpa only [V, dif_pos hc] using ht.2 u hu
  obtain ⟨t, ht, htV, htupper⟩ := spec i b h hb
  have hbase : 1 ∈ branchValues y i b h := Finset.mem_insert_self _ _
  have hG (a : ℕ) : 0 ≤ reciprocalGeomSum (prime y i) a := by
    unfold reciprocalGeomSum
    positivity
  have hbranch (a : ℕ) (ha : 1 ≤ a) (hah : a ≤ h)
      (hab : prime y i ^ a ≤ b) :
      reciprocalGeomSum (prime y i) a * V y (i + 1) (b / prime y i ^ a) a ∈
        branchValues y i b h := by
    unfold branchValues
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, hah⟩, hab⟩, rfl⟩
  have hbranch_le (a : ℕ) (ha : 1 ≤ a) (hah : a ≤ h)
      (hab : prime y i ^ a ≤ b) :
      reciprocalGeomSum (prime y i) a * V y (i + 1) (b / prime y i ^ a) a ≤
        V y i b h := by
    have hpow : 0 < prime y i ^ a := pow_pos (Nat.prime_nth_prime _).pos _
    have hc : 1 ≤ b / prime y i ^ a := Nat.div_pos hab hpow
    obtain ⟨u, hu, huV, _⟩ := spec (i + 1) (b / prime y i ^ a) a hc
    have hjoin : Feasible y i b h (a :: u) :=
      (split i b h a u).2 ⟨ha, hah, hab, hu⟩
    calc
      reciprocalGeomSum (prime y i) a * V y (i + 1) (b / prime y i ^ a) a =
          suffixWeight y i (a :: u) := by simp [suffixWeight, huV]
      _ ≤ V y i b h := htupper _ hjoin
  have hmax_le : (branchValues y i b h).max' ⟨1, hbase⟩ ≤ V y i b h := by
    apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simpa [suffixWeight] using htupper [] (by simp [Feasible, Ordered, suffixNumber, hb])
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨haa, hab⟩ := Finset.mem_filter.mp ha
      obtain ⟨haa, hah⟩ := Finset.mem_Icc.mp haa
      exact hbranch_le a haa hah hab
  have hV_le : V y i b h ≤ (branchValues y i b h).max' ⟨1, hbase⟩ := by
    cases t with
    | nil =>
        rw [← htV]
        simpa [suffixWeight] using
          (Finset.le_max' (s := branchValues y i b h) 1 hbase)
    | cons a u =>
        obtain ⟨ha, hah, hab, hu⟩ := (split i b h a u).1 ht
        have hpow : 0 < prime y i ^ a := pow_pos (Nat.prime_nth_prime _).pos _
        have hc : 1 ≤ b / prime y i ^ a := Nat.div_pos hab hpow
        obtain ⟨_, _, _, huupper⟩ := spec (i + 1) (b / prime y i ^ a) a hc
        rw [← htV]
        calc
          suffixWeight y i (a :: u) =
              reciprocalGeomSum (prime y i) a * suffixWeight y (i + 1) u := rfl
          _ ≤ reciprocalGeomSum (prime y i) a * V y (i + 1) (b / prime y i ^ a) a :=
            mul_le_mul_of_nonneg_left (huupper u hu) (hG a)
          _ ≤ (branchValues y i b h).max' ⟨1, hbase⟩ :=
            Finset.le_max' (s := branchValues y i b h) _ (hbranch a ha hah hab)
  refine ⟨le_antisymm hV_le hmax_le, htupper, ⟨t, ht, htV⟩, ?_⟩
  intro a ha hab
  have hq : 2 ≤ prime y i ^ a :=
    Nat.succ_le_iff.mpr (one_lt_pow' (Nat.prime_nth_prime _).one_lt (by omega))
  have hdiv : b / prime y i ^ a ≤ b / 2 := Nat.div_le_div_left hq (by omega)
  omega

/-- Every prime divisor of an actual suffix product occurs at an index of its list. -/
theorem suffix_prime_factors (y i : ℕ) (t : List ℕ) :
    0 < suffixNumber y i t ∧
      (∀ p : ℕ, p.Prime → p ∣ suffixNumber y i t →
        ∃ j : ℕ, j < t.length ∧ p = prime y (i + j)) ∧
      Rough y (suffixNumber y i t) := by
  have above (j : ℕ) : y < prime y j := by
    have hc : Nat.count Nat.Prime (y + 1) ≤ Nat.primeCounting y + j := by
      change Nat.count Nat.Prime (y + 1) ≤ Nat.count Nat.Prime (y + 1) + j
      omega
    have h := (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp hc
    exact Nat.lt_of_succ_le (by simpa [prime] using h)
  induction t generalizing i with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · simp [suffixNumber]
      · intro p hp hpd
        have : p = 1 := Nat.dvd_one.mp (by simpa [suffixNumber] using hpd)
        exact (hp.ne_one this).elim
      · intro p hp hpd
        have : p = 1 := Nat.dvd_one.mp (by simpa [suffixNumber] using hpd)
        exact (hp.ne_one this).elim
  | cons a t ih =>
      obtain ⟨htpos, htprime, _⟩ := ih (i + 1)
      have hsupport : ∀ p : ℕ, p.Prime → p ∣ suffixNumber y i (a :: t) →
          ∃ j : ℕ, j < (a :: t).length ∧ p = prime y (i + j) := by
        intro p hp hpd
        have hprod : p ∣ prime y i ^ a * suffixNumber y (i + 1) t := hpd
        rcases (hp.dvd_mul).mp hprod with hhead | htail
        · have hpq : p = prime y i :=
            (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_nth_prime _)).mp
              (hp.dvd_of_dvd_pow hhead)
          exact ⟨0, by simp, by simpa using hpq⟩
        · obtain ⟨j, hj, hpj⟩ := htprime p hp htail
          refine ⟨j + 1, by simp; omega, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpj
      refine ⟨?_, hsupport, ?_⟩
      · exact Nat.mul_pos (pow_pos (Nat.prime_nth_prime _).pos _) htpos
      · intro p hp hpd
        obtain ⟨j, _, hpj⟩ := hsupport p hp hpd
        rw [hpj]
        exact above (i + j)

/-- The all-state finite recurrence represents the exact maximum over all rough
integers, with consecutive-prime enumeration and an actual attaining suffix. -/
theorem rough_prime_suffix_complete (y B : ℕ) (_hy : 1 ≤ y) (hB : 1 ≤ B) :
    (∀ i b h : ℕ, 1 ≤ b →
      V y i b h = (branchValues y i b h).max' (by
        classical
        exact ⟨1, Finset.mem_insert_self _ _⟩) ∧
      (∀ t : List ℕ, Feasible y i b h t → suffixWeight y i t ≤ V y i b h) ∧
      (∃ t : List ℕ, Feasible y i b h t ∧ suffixWeight y i t = V y i b h) ∧
      (∀ a : ℕ, 1 ≤ a → prime y i ^ a ≤ b → b / prime y i ^ a < b)) ∧
    (∀ p : ℕ, p.Prime ∧ y < p ↔ ∃ i : ℕ, p = prime y i) ∧
    (∀ a : ℕ, a ≤ rootCap y B ↔ prime y 0 ^ a ≤ B) ∧
    (∀ (i : ℕ) (t : List ℕ),
      (ArithmeticFunction.sigma 1 (suffixNumber y i t) : ℝ) /
        suffixNumber y i t = suffixWeight y i t) ∧
    (∃ (n : ℕ) (t : List ℕ), 1 ≤ n ∧ n ≤ B ∧ Rough y n ∧
      Feasible y 0 B (rootCap y B) t ∧ suffixNumber y 0 t = n ∧
      suffixWeight y 0 t = U y B) ∧
    U y B = V y 0 B (rootCap y B) := by
  classical
  have hmono : StrictMono (prime y) := by
    intro i j hij
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
  have habove (i : ℕ) : y < prime y i := by
    apply Nat.lt_of_succ_le
    exact (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp
      (show Nat.count Nat.Prime (y + 1) ≤ Nat.primeCounting y + i by
        change Nat.count Nat.Prime (y + 1) ≤ Nat.count Nat.Prime (y + 1) + i
        omega)
  have henumerate (p : ℕ) (hp : p.Prime) (hyp : y < p) :
      ∃ i : ℕ, p = prime y i := by
    have hc : Nat.primeCounting y ≤ Nat.count Nat.Prime p :=
      Nat.count_monotone Nat.Prime (by omega)
    refine ⟨Nat.count Nat.Prime p - Nat.primeCounting y, ?_⟩
    unfold prime
    rw [Nat.add_sub_of_le hc, Nat.nth_count hp]
  have hsigma (i : ℕ) (t : List ℕ) :
      (ArithmeticFunction.sigma 1 (suffixNumber y i t) : ℝ) /
        suffixNumber y i t = suffixWeight y i t := by
    induction t generalizing i with
    | nil => simp [suffixNumber, suffixWeight]
    | cons a t ih =>
        have hp : (prime y i).Prime := Nat.prime_nth_prime _
        have hcop : (prime y i).Coprime (suffixNumber y (i + 1) t) := by
          apply hp.coprime_iff_not_dvd.mpr
          intro hd
          obtain ⟨j, _, heq⟩ := (suffix_prime_factors y (i + 1) t).2.1 _ hp hd
          exact (hmono (show i < i + 1 + j by omega)).ne heq
        simp only [suffixNumber, suffixWeight]
        rw [IntegerSwap.normalized_sigma_mul (hcop.pow_left a),
          IntegerSwap.normalized_sigma_prime_pow hp, ih]
  have hmaximizer : ∃ n : ℕ, 1 ≤ n ∧ n ≤ B ∧ Rough y n ∧
      (ArithmeticFunction.sigma 1 n : ℝ) / n = U y B ∧
      ∀ p q : ℕ, p.Prime → q.Prime → y < p → p < q →
        n.factorization q ≤ n.factorization p := by
    let s := (Finset.Icc 1 B).filter (Rough y)
    let f : ℕ → ℝ := fun n => (ArithmeticFunction.sigma 1 n : ℝ) / n
    have hs : s.Nonempty := by
      refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hB⟩, ?_⟩⟩
      intro p hp hpd
      exact (hp.ne_one (Nat.dvd_one.mp hpd)).elim
    obtain ⟨n, hn, hnmax⟩ := Finset.exists_max_image s f hs
    obtain ⟨hnrange, hnrough⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnB⟩ := Finset.mem_Icc.mp hnrange
    have hnU : f n = U y B := by
      have hne : (s.image f).Nonempty := hs.image f
      simp only [U, dif_pos hB]
      change f n = (s.image f).max' hne
      apply le_antisymm
      · exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
      · apply Finset.max'_le
        intro x hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        exact hnmax m hm
    refine ⟨n, hn1, hnB, hnrough, hnU, ?_⟩
    intro p q hp hq hyp hpq
    by_contra horder
    have hab : n.factorization p < n.factorization q := Nat.lt_of_not_ge horder
    let a := n.factorization p
    let b := n.factorization q
    let t := n / (p ^ a * q ^ b)
    let n' := t * p ^ b * q ^ a
    have hswap := IntegerSwap.prime_exponent_swap hn1 hp hq hpq hab
    change 1 ≤ t ∧ Nat.gcd t (p * q) = 1 ∧ n = t * p ^ a * q ^ b ∧
      (0 < n' ∧ n' < n) ∧ f n < f n' at hswap
    obtain ⟨_, _, hfactor, ⟨hn'1, hn'lt⟩, hgain⟩ := hswap
    have htdvd : t ∣ n := by
      rw [hfactor]
      exact ⟨p ^ a * q ^ b, by simp [Nat.mul_assoc]⟩
    have hn'rough : Rough y n' := by
      intro r hr hrd
      have hrd' : r ∣ t * p ^ b * q ^ a := hrd
      rcases (hr.dvd_mul).mp hrd' with hleft | hqpow
      · rcases (hr.dvd_mul).mp hleft with ht | hppow
        · exact hnrough r hr (dvd_trans ht htdvd)
        · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp
            (hr.dvd_of_dvd_pow hppow)
          exact hrp ▸ hyp
      · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp
          (hr.dvd_of_dvd_pow hqpow)
        exact hrq ▸ (hyp.trans hpq)
    have hn'mem : n' ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn'1, hn'lt.le.trans hnB⟩,
        hn'rough⟩
    exact (not_lt_of_ge (hnmax n' hn'mem)) hgain
  obtain ⟨n, hn1, hnB, hnrough, hnU, hnorder⟩ := hmaximizer
  have hn0 : n ≠ 0 := by omega
  let f : ℕ → ℕ := fun i => n.factorization (prime y i)
  have hf : Antitone f := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact hnorder _ _ (Nat.prime_nth_prime _) (Nat.prime_nth_prime _)
        (habove i) (hmono hij)
  have hcover : n.factorization.support ⊆
      (Finset.range (Nat.primeCounting n)).image (prime y) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨i, hi⟩ := henumerate p hpp (hnrough p hpp hpd)
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_range.mpr ?_, hi.symm⟩
    have hcount : Nat.count Nat.Prime p < Nat.primeCounting n := by
      have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpd
      have hc := Nat.count_monotone Nat.Prime (Nat.succ_le_succ hpn)
      rw [Nat.count_succ, if_pos hpp] at hc
      change Nat.count Nat.Prime p + 1 ≤ Nat.primeCounting n at hc
      omega
    have hindex : Nat.primeCounting y + i = Nat.count Nat.Prime p := by
      rw [hi]
      exact (Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime _).symm
    omega
  have hprod : (∏ j ∈ Finset.range (Nat.primeCounting n), prime y j ^ f j) = n := by
    calc
      _ = n.factorization.prod (fun p a => p ^ a) := by
        rw [Finsupp.prod_of_support_subset _ hcover (fun p a => p ^ a)
          (by intros; simp)]
        rw [Finset.prod_image (by intros a ha b hb hab; exact hmono.injective hab)]
      _ = n := Nat.prod_factorization_pow_eq_self hn0
  -- Zero valuations form a tail; stop at the first zero while reconstructing the product.
  have hbuild (k i h : ℕ) (hhead : f i ≤ h) :
      ∃ t : List ℕ, Ordered h t ∧ suffixNumber y i t =
        ∏ j ∈ Finset.range k, prime y (i + j) ^ f (i + j) := by
    induction k generalizing i h with
    | zero => exact ⟨[], trivial, by simp [suffixNumber]⟩
    | succ k ih =>
        by_cases hz : f i = 0
        · refine ⟨[], trivial, ?_⟩
          simp only [suffixNumber]
          symm
          apply Finset.prod_eq_one
          intro j hj
          have hzero : f (i + j) = 0 := by have := hf (show i ≤ i + j by omega); omega
          rw [hzero, pow_zero]
        · obtain ⟨t, ht, htn⟩ := ih (i + 1) (f i) (hf (by omega))
          refine ⟨f i :: t, ⟨by omega, hhead, ht⟩, ?_⟩
          rw [suffixNumber, htn, Finset.prod_range_succ']
          simp only [Nat.add_zero]
          rw [Nat.mul_comm]
          congr 1
          apply Finset.prod_congr rfl
          intro j hj
          congr 2 <;> omega
  have hcap : f 0 ≤ rootCap y B := by
    apply Nat.le_log_of_pow_le (Nat.prime_nth_prime _).one_lt
    exact (Nat.le_of_dvd (by omega)
      (((Nat.prime_nth_prime _).pow_dvd_iff_le_factorization hn0).mpr le_rfl)).trans hnB
  obtain ⟨t, htorder, htn⟩ := hbuild (Nat.primeCounting n) 0 (rootCap y B) hcap
  have htn' : suffixNumber y 0 t = n := by
    simp only [Nat.zero_add] at htn
    exact htn.trans hprod
  have htfeasible : Feasible y 0 B (rootCap y B) t := ⟨htorder, htn' ▸ hnB⟩
  have htweight : suffixWeight y 0 t = U y B := by
    rw [← hsigma, htn', hnU]
  have hUV : U y B ≤ V y 0 B (rootCap y B) := by
    rw [← htweight]
    exact (bellman_complete y 0 B (rootCap y B) hB).2.1 t htfeasible
  have hVU : V y 0 B (rootCap y B) ≤ U y B := by
    obtain ⟨u, hu, huV⟩ := (bellman_complete y 0 B (rootCap y B) hB).2.2.1
    obtain ⟨hupos, _, hurough⟩ := suffix_prime_factors y 0 u
    rw [← huV, ← hsigma]
    simp only [U, dif_pos hB]
    apply Finset.le_max'
    apply Finset.mem_image.mpr
    exact ⟨suffixNumber y 0 u,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hupos, hu.2⟩, hurough⟩, rfl⟩
  refine ⟨fun i b h hb => bellman_complete y i b h hb, ?_, ?_, hsigma,
    ⟨n, t, hn1, hnB, hnrough, htfeasible, htn', htweight⟩, le_antisymm hUV hVU⟩
  · intro p
    constructor
    · rintro ⟨hp, hyp⟩
      exact henumerate p hp hyp
    · rintro ⟨i, rfl⟩
      exact ⟨Nat.prime_nth_prime _, habove i⟩
  · intro a
    exact Nat.le_log_iff_pow_le (Nat.prime_nth_prime _).one_lt (by omega)

#print axioms rough_prime_suffix_complete
#print axioms IntegerSwap.normalized_sigma_prime_pow
#print axioms IntegerSwap.normalized_sigma_mul
#print axioms bellman_complete
#print axioms feasible_finite
#print axioms suffix_prime_factors

end

end D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
