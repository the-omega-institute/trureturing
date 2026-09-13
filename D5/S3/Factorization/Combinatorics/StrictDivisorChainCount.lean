/- GID: D5/S3/Factorization/Combinatorics/StrictDivisorChainCount
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/StrictDivisorChainCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict divisor-chain counts equal the signed binomial transform of prime-exponent composition counts. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace D5.S3.Factorization.Combinatorics.StrictDivisorChainCount

/-- A chain from one to `n` with `k` strict divisibility steps, allowing arbitrary jumps. -/
def Chain (n k : ℕ) := {d : Fin (k + 1) → Fin (n + 1) //
  (d 0).val = 1 ∧ (d (Fin.last k)).val = n ∧
  ∀ i : Fin k, (d i.castSucc).val ∣ (d i.succ).val ∧ d i.castSucc < d i.succ}

/-- A chain from one to `n` whose divisibility steps may repeat an endpoint. -/
def WeakChain (n k : ℕ) := {d : Fin (k + 1) → Fin (n + 1) //
  (d 0).val = 1 ∧ (d (Fin.last k)).val = n ∧
  ∀ i : Fin k, (d i.castSucc).val ∣ (d i.succ).val ∧ d i.castSucc ≤ d i.succ}

/-- The product of the prime-exponent composition counts, with zero at length zero. -/
def weakCount (n j : ℕ) : ℕ :=
  if j = 0 then 0 else ∏ p ∈ n.primeFactors,
    (n.factorization p + j - 1).choose (n.factorization p)

/-- Strict chains form a finite type because all their endpoints are bounded. -/
instance chainFintype (n k : ℕ) : Fintype (Chain n k) :=
  inferInstanceAs (Fintype {_d : Fin (k + 1) → Fin (n + 1) // _})

/-- Weak chains form a finite type because all their endpoints are bounded. -/
instance weakChainFintype (n k : ℕ) : Fintype (WeakChain n k) :=
  inferInstanceAs (Fintype {_d : Fin (k + 1) → Fin (n + 1) // _})

/-- Positive factors indexed by a finite type, with prescribed product. -/
def FactorTuple (n : ℕ) (ι : Type*) [Fintype ι] :=
  {u : ι → ℕ // (∀ i, 0 < u i) ∧ ∏ i, u i = n}

/-- A weak composition of every prime exponent among the given positions. -/
def PrimeAllocation (n : ℕ) (ι : Type*) [Fintype ι] :=
  (p : n.primeFactors) → {a : ι → ℕ // ∑ i, a i = n.factorization p}

/-- Factorization assigns each prime exponent to its factor position. -/
noncomputable def factorTupleEquivAllocation (n : ℕ) (hn : n ≠ 0)
    (ι : Type*) [Fintype ι] : FactorTuple n ι ≃ PrimeAllocation n ι := by
  classical
  let encode : FactorTuple n ι → PrimeAllocation n ι := fun u p =>
    ⟨fun i => (u.val i).factorization p.val, by
      rw [← Nat.factorization_prod_apply (fun i _ => (u.prop.1 i).ne'), u.prop.2]⟩
  let value : PrimeAllocation n ι → ι → ℕ := fun a i =>
    ∏ p : n.primeFactors, p.val ^ (a p).val i
  have value_pos : ∀ a i, 0 < value a i := by
    intro a i
    apply Finset.prod_pos
    intro p _
    exact pow_pos (Nat.prime_of_mem_primeFactors p.prop).pos _
  have value_factorization : ∀ a i (p : n.primeFactors),
      (value a i).factorization p.val = (a p).val i := by
    intro a i p
    change (∏ q : n.primeFactors, q.val ^ (a q).val i).factorization p.val = (a p).val i
    rw [Nat.factorization_prod_apply (fun q _ =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors q.prop).ne_zero)]
    calc
      _ = ∑ q : n.primeFactors, if q = p then (a q).val i else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        rw [(Nat.prime_of_mem_primeFactors q.prop).factorization_pow, Finsupp.single_apply]
        simp only [Subtype.ext_iff]
      _ = _ := by simp
  have value_prod : ∀ a, ∏ i, value a i = n := by
    intro a
    dsimp [value]
    rw [Finset.prod_comm]
    simp_rw [Finset.prod_pow_eq_pow_sum, (a _).prop]
    exact (Nat.prod_primeFactors_coe_pow_factorization hn).symm
  let decode : PrimeAllocation n ι → FactorTuple n ι := fun a =>
    ⟨value a, value_pos a, value_prod a⟩
  refine ⟨encode, decode, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    funext i
    apply Nat.eq_of_factorization_eq (value_pos (encode u) i).ne' (u.prop.1 i).ne'
    intro p
    by_cases hp : p ∈ n.primeFactors
    · exact value_factorization (encode u) i ⟨p, hp⟩
    · have hzero : n.factorization p = 0 := by
        simpa using (Finsupp.notMem_support_iff.mp hp)
      have hule : (u.val i).factorization ≤ n.factorization := by
        apply (Nat.factorization_le_iff_dvd (u.prop.1 i).ne' hn).mpr
        exact (Finset.dvd_prod_of_mem u.val (Finset.mem_univ i)).trans
          (dvd_of_eq u.prop.2)
      have hvle : (value (encode u) i).factorization ≤ n.factorization := by
        apply (Nat.factorization_le_iff_dvd (value_pos _ _).ne' hn).mpr
        exact value_prod (encode u) ▸
          Finset.dvd_prod_of_mem (value (encode u)) (Finset.mem_univ i)
      exact (Nat.eq_zero_of_le_zero (by simpa only [hzero] using hvle p)).trans
        (Nat.eq_zero_of_le_zero (by simpa only [hzero] using hule p)).symm
  · intro a
    funext p
    apply Subtype.ext
    funext i
    exact value_factorization a i p

/-- Successive quotients and prefix products identify weak chains with positive factor tuples. -/
noncomputable def weakChainEquivFactors (n k : ℕ) (hn : n ≠ 0) :
    WeakChain n k ≃ FactorTuple n (Fin k) := by
  classical
  let partialProducts : (Fin k → ℕ) → Fin (k + 1) → ℕ := fun u i =>
    ∏ j ∈ Finset.univ.filter (fun j : Fin k => j.val < i.val), u j
  have prefix_zero : ∀ u, partialProducts u 0 = 1 := by intro u; simp [partialProducts]
  have prefix_last : ∀ u, partialProducts u (Fin.last k) = ∏ j, u j := by
    intro u
    simp [partialProducts, Fin.is_lt]
  have prefix_step : ∀ u (i : Fin k),
      partialProducts u i.succ = partialProducts u i.castSucc * u i := by
    intro u i
    have hf : Finset.univ.filter (fun j : Fin k => j.val < i.succ.val) =
        insert i (Finset.univ.filter (fun j : Fin k => j.val < i.castSucc.val)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
      omega
    change (∏ j ∈ Finset.univ.filter (fun j : Fin k => j.val < i.succ.val), u j) = _
    rw [hf, Finset.prod_insert (by simp)]
    exact mul_comm _ _
  have positive : ∀ d : WeakChain n k, ∀ i, 0 < (d.val i).val := by
    intro d i
    have hmono : Monotone d.val := Fin.monotone_iff_le_succ.mpr fun j => (d.prop.2.2 j).2
    have hi := hmono (Fin.zero_le i)
    have hz := d.prop.1
    change (d.val 0).val ≤ (d.val i).val at hi
    omega
  let quotient : WeakChain n k → Fin k → ℕ := fun d i =>
    (d.val i.succ).val / (d.val i.castSucc).val
  have quotient_pos : ∀ d i, 0 < quotient d i := by
    intro d i
    exact Nat.div_pos (d.prop.2.2 i).2 (positive d i.castSucc)
  have prefix_quotient : ∀ d i, partialProducts (quotient d) i = (d.val i).val := by
    intro d i
    induction i using Fin.induction with
    | zero => exact (prefix_zero _).trans d.prop.1.symm
    | succ i ih =>
      rw [prefix_step, ih]
      exact Nat.mul_div_cancel' (d.prop.2.2 i).1
  let encode : WeakChain n k → FactorTuple n (Fin k) := fun d =>
    ⟨quotient d, quotient_pos d, by
      rw [← prefix_last, prefix_quotient]
      exact d.prop.2.1⟩
  have prefix_pos : ∀ u : FactorTuple n (Fin k), ∀ i, 0 < partialProducts u.val i := by
    intro u i
    exact Finset.prod_pos fun j _ => u.prop.1 j
  have prefix_bound : ∀ u : FactorTuple n (Fin k), ∀ i, partialProducts u.val i ≤ n := by
    intro u i
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    exact (Finset.prod_dvd_prod_of_subset _ _ u.val (Finset.filter_subset _ _)).trans
      (dvd_of_eq u.prop.2)
  let decode : FactorTuple n (Fin k) → WeakChain n k := fun u =>
    ⟨fun i => ⟨partialProducts u.val i, Nat.lt_succ_of_le (prefix_bound u i)⟩,
      prefix_zero _, (prefix_last _).trans u.prop.2, by
        intro i
        change partialProducts u.val i.castSucc ∣ partialProducts u.val i.succ ∧
          partialProducts u.val i.castSucc ≤ partialProducts u.val i.succ
        rw [prefix_step]
        exact ⟨dvd_mul_right _ _, Nat.le_mul_of_pos_right _ (u.prop.1 i)⟩⟩
  refine ⟨encode, decode, ?_, ?_⟩
  · intro d
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact prefix_quotient d i
  · intro u
    apply Subtype.ext
    funext i
    change partialProducts u.val i.succ / partialProducts u.val i.castSucc = u.val i
    rw [prefix_step, Nat.mul_div_cancel_left _ (prefix_pos u i.castSucc)]

/-- Strict steps correspond to the absence of unit factors in the quotient tuple. -/
noncomputable def strictChainEquivFactors (n k : ℕ) (hn : n ≠ 0) :
    Chain n k ≃ {u : FactorTuple n (Fin k) // ∀ i, u.val i ≠ 1} := by
  classical
  let strict : WeakChain n k → Prop := fun d => ∀ i : Fin k, d.val i.castSucc < d.val i.succ
  let e : Chain n k ≃ {d : WeakChain n k // strict d} :=
    { toFun := fun d => ⟨⟨d.val, d.prop.1, d.prop.2.1,
        fun i => ⟨(d.prop.2.2 i).1, (d.prop.2.2 i).2.le⟩⟩,
        fun i => (d.prop.2.2 i).2⟩
      invFun := fun d => ⟨d.val.val, d.val.prop.1, d.val.prop.2.1,
        fun i => ⟨(d.val.prop.2.2 i).1, d.prop i⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine e.trans ((weakChainEquivFactors n k hn).subtypeEquiv ?_)
  intro d
  change (∀ i : Fin k, d.val i.castSucc < d.val i.succ) ↔
    ∀ i : Fin k, (d.val i.succ).val / (d.val i.castSucc).val ≠ 1
  have hmono : Monotone d.val := Fin.monotone_iff_le_succ.mpr fun i => (d.prop.2.2 i).2
  have hpos : ∀ i, 0 < (d.val i).val := by
    intro i
    have h := hmono (Fin.zero_le i)
    change (d.val 0).val ≤ (d.val i).val at h
    have hz := d.prop.1
    omega
  constructor
  · intro h i heq
    have he := Nat.eq_of_dvd_of_div_eq_one (d.prop.2.2 i).1 heq
    have hi := h i
    change (d.val i.castSucc).val < (d.val i.succ).val at hi
    omega
  · intro h i
    have hle := (d.prop.2.2 i).2
    change (d.val i.castSucc).val < (d.val i.succ).val
    change (d.val i.castSucc).val ≤ (d.val i.succ).val at hle
    apply lt_of_le_of_ne hle
    intro he
    apply h i
    rw [← he, Nat.div_self (hpos _)]

/-- Deleting prescribed unit positions leaves exactly a tuple on the retained positions. -/
noncomputable def factorTupleRestrictEquiv (n : ℕ) (ι : Type*) [Fintype ι]
    (s : Finset ι) :
    {u : FactorTuple n ι // ∀ i, i ∉ s → u.val i = 1} ≃ FactorTuple n s := by
  classical
  let encode : {u : FactorTuple n ι // ∀ i, i ∉ s → u.val i = 1} →
      FactorTuple n s := fun u =>
    ⟨fun i => u.val.val i.val, fun i => u.val.prop.1 i.val, by
      rw [Finset.prod_coe_sort]
      exact (Finset.prod_subset (Finset.subset_univ s) (fun i _ hi => u.prop i hi)).trans
        u.val.prop.2⟩
  let extend : FactorTuple n s → ι → ℕ := fun u i => if hi : i ∈ s then u.val ⟨i, hi⟩ else 1
  have extend_prod : ∀ u, ∏ i, extend u i = n := by
    intro u
    calc
      _ = ∏ i ∈ s, extend u i :=
        (Finset.prod_subset (Finset.subset_univ s) (by
          intro i _ hi
          simp [extend, hi])).symm
      _ = ∏ i : s, u.val i := by
        rw [← Finset.prod_coe_sort]
        apply Finset.prod_congr rfl
        intro i _
        simp [extend]
      _ = n := u.prop.2
  let decode : FactorTuple n s → {u : FactorTuple n ι // ∀ i, i ∉ s → u.val i = 1} := fun u =>
    ⟨⟨extend u, by intro i; dsimp [extend]; split <;> simp [u.prop.1], extend_prod u⟩,
      by intro i hi; simp [extend, hi]⟩
  refine ⟨encode, decode, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change extend (encode u) i = u.val.val i
    by_cases hi : i ∈ s
    · simp [extend, hi, encode]
    · simp [extend, hi, u.prop i hi]
  · intro u
    apply Subtype.ext
    funext i
    change extend u i.val = u.val i
    simp [extend, i.prop]

/-- The strict-chain count is the signed binomial transform of the weak-chain counting function. -/
theorem strict_divisor_chain_count (n k : ℕ) (hn : 1 < n) (_hk : 1 ≤ k)
    (_hkr : k ≤ ArithmeticFunction.cardFactors n) :
    (Nat.card (Chain n k) : ℤ) =
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * weakCount n j := by
  classical
  have hn0 : n ≠ 0 := by omega
  have count_factors : ∀ (ι : Type) [Fintype ι],
      Nat.card (FactorTuple n ι) = weakCount n (Fintype.card ι) := by
    intro ι inst
    by_cases hi : Fintype.card ι = 0
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hi
      have : IsEmpty (FactorTuple n ι) := ⟨by
        intro u
        have hu := u.prop.2
        simp only [Finset.univ_eq_empty, Finset.prod_empty] at hu
        omega⟩
      simp [weakCount]
    · let e := (factorTupleEquivAllocation n hn0 ι).trans
        (Equiv.piCongrRight fun p =>
          (Sym.equivNatSumOfFintype ι (n.factorization p)).symm)
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
      simp only [Sym.card_sym_eq_choose, weakCount, if_neg hi]
      simpa only [Nat.add_comm] using
        (Finset.prod_coe_sort n.primeFactors (fun p =>
          (n.factorization p + Fintype.card ι - 1).choose (n.factorization p)))
  let U := FactorTuple n (Fin k)
  let e := (factorTupleEquivAllocation n hn0 (Fin k)).trans
    (Equiv.piCongrRight fun p => (Sym.equivNatSumOfFintype (Fin k) (n.factorization p)).symm)
  let : Fintype U := Fintype.ofEquiv _ e.symm
  let B : Fin k → Finset U := fun i => Finset.univ.filter (fun u => u.val i = 1)
  have strict_card : Nat.card (Chain n k) =
      ((Finset.univ : Finset (Fin k)).inf (fun i => (B i)ᶜ)).card := by
    rw [Nat.card_congr (strictChainEquivFactors n k hn0), Nat.card_eq_fintype_card]
    apply Fintype.card_of_subtype
    intro u
    simp [Finset.mem_inf, B]
  have intersection_card : ∀ s : Finset (Fin k),
      (s.inf B).card = weakCount n (k - s.card) := by
    intro s
    have hcard : (s.inf B).card =
        Nat.card {u : U // ∀ i, i ∉ sᶜ → u.val i = 1} := by
      rw [Nat.card_eq_fintype_card]
      symm
      apply Fintype.card_of_subtype
      intro u
      simp [Finset.mem_inf, B]
    rw [hcard, Nat.card_congr (factorTupleRestrictEquiv n (Fin k) sᶜ), count_factors]
    simp
  have hIE := Finset.inclusion_exclusion_card_inf_compl (Finset.univ : Finset (Fin k)) B
  rw [← strict_card] at hIE
  simp_rw [intersection_card] at hIE
  rw [Finset.sum_powerset] at hIE
  simp_rw [Finset.sum_powersetCard (f := fun m =>
    (-1 : ℤ) ^ m * (weakCount n (k - m) : ℤ))] at hIE
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hIE
  rw [hIE]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa using Finset.mem_range.mp hj
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hjk, Nat.choose_symm hjk]
  ring

#print axioms strict_divisor_chain_count

end D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
