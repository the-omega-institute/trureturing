/- GID: D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences
   generality: I
   mirror-B: D5/B/S3/Arith/Factorization/OeisA343825KageyPowerSequences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime-power sequence minima eventually equal the rational-relation minimum. -/
/-
proof_shape: bind-only (result; finite threshold selection and minimum comparisons).
escape_witness: none
admission_basis: open-problem-resolution (#18687; Proved)
Direct frozen dependencies: D5/S3/Factorization/Embeddings/RationalValuationRecovery.
  rational_finite_valuation_kernel
  declaration statement_id: sha256:3961205c906d9af154530a8dc120be7f32d5f1f74bb6ea63fc3452c9fec4a93c
The five public definitions have exactly the mathematical bodies in #18687.
All helper theorems have proof_shape: bind-only and escape_witness: none.
  clear_den: consumers separator.
  clear_den_on: consumers relation_of_mem_span.
  rat_one_of_val: consumers vec_relation.
  val_prod: consumers vec_relation.
  vec_relation: consumers relation_of_mem_span, relation_exists.
  relation_of_mem_span: consumers separator.
  separator: consumers lower_valid.
  repList_count: consumers repList_mem, repList_prod, upper_valid.
  repList_mem: consumers repList_prod, upper_valid.
  repList_sorted: consumers upper_valid.
  repList_prod: consumers upper_valid.
  list_endpoints: consumers upper_valid.
  residue_pow: consumers upper_valid.
  int_root: consumers upper_valid.
  upper_valid: consumers result.
  valid_bounds: consumers lower_valid, result.
  lower_valid: consumers result.
  relation_exists: consumers result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19920
The private vec and repList definitions supply finite coordinates and sorted multiplicities.
The uniform existence and nonexistence arguments contain no finite computational certificate.
-/

import D5.S3.Factorization.Embeddings.RationalValuationRecovery
import Mathlib.RingTheory.Polynomial.RationalRoot

set_option autoImplicit false

namespace D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences

/-- A sequence `k = b_1 <= b_2 <= ... <= b_t = m` (as a list) such that no term appears `n` or more
times and the product of the sequence is of the form `c^n`, where `c` is an integer. -/
def Valid (n k m : ℕ) (b : List ℕ) : Prop :=
  b.head? = some k ∧ b.getLast? = some m ∧ b.Pairwise (· ≤ ·) ∧ (∀ x ∈ b, b.count x < n) ∧
    ∃ c : ℤ, ((b.prod : ℕ) : ℤ) = c ^ n

open Classical in
/-- A343825: `T(n, k)` is the least `m` such that there exists such a sequence (`0` if there is
none). -/
noncomputable def T (n k : ℕ) : ℕ := if h : ∃ m b, Valid n k m b then Nat.find h else 0

/-- `n^(k_n) * (n+1)^(k_(n+1)) * ... * m^(k_m) = 1` for integers `k_n, ..., k_m` with `k_n` nonzero
(here with `k` in place of `n`). -/
def Relation (k m : ℕ) : Prop :=
  ∃ e : ℕ → ℤ, e k ≠ 0 ∧ ∏ j ∈ Finset.Icc k m, ((j : ℚ) ^ e j) = 1

open Classical in
/-- A071537: the least integer `m >= n` such that there exist integers `k_n, ..., k_m` with nonzero
`k_n` for which `n^(k_n) * (n+1)^(k_(n+1)) * ... * m^(k_m) = 1` (`0` if there is none). -/
noncomputable def A071537 (k : ℕ) : ℕ := if h : ∃ m, k ≤ m ∧ Relation k m then Nat.find h else 0

/-- A343825 ("Conjecture: T(p,k) = A071537(k) for fixed k and sufficiently large prime p."), for the
`k ≥ 1` where A071537 is defined. -/
def claim : Prop := ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p → T p k = A071537 k

open scoped BigOperators
open Finset

private theorem clear_den {ι : Type*} [Fintype ι] (a : ι → ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ z : ι → ℤ, ∀ i, (z i : ℚ) = D * a i := by
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) a
  choose z hz using hD
  refine ⟨D, nonZeroDivisors.coe_ne_zero D, z, ?_⟩
  intro i
  simpa [Algebra.smul_def] using hz i

private theorem clear_den_on (s : Finset ℕ) (a : ℕ → ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ z : ℕ → ℤ, ∀ i ∈ s, (z i : ℚ) = D * a i := by
  classical
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) s a
  choose! z hz using hD
  refine ⟨D, nonZeroDivisors.coe_ne_zero D, z, ?_⟩
  intro i hi
  simpa [Algebra.smul_def] using hz i hi

private theorem rat_one_of_val (a : ℚ) (ha : 0 < a)
    (h : ∀ q : ℕ, q.Prime → padicValRat q a = 0) : a = 1 := by
  have hh := D5.S3.Factorization.Embeddings.RationalValuationRecovery.rational_finite_valuation_kernel
    ha.ne' (one_ne_zero : (1 : ℚ) ≠ 0) (fun q hq => by simpa using h q hq)
  rcases hh with hh | hh
  · exact hh
  · linarith

private theorem val_prod (q : ℕ) (hq : q.Prime) (s : Finset ℕ) (a : ℕ → ℚ)
    (ha : ∀ j ∈ s, a j ≠ 0) :
    padicValRat q (∏ j ∈ s, a j) = ∑ j ∈ s, padicValRat q (a j) := by
  let : Fact q.Prime := ⟨hq⟩
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj, padicValRat.mul (ha j (mem_insert_self _ _))
      (prod_ne_zero_iff.mpr (fun x hx => ha x (mem_insert_of_mem hx))),
      ih (fun x hx => ha x (mem_insert_of_mem hx))]

private noncomputable def vec (d n : ℕ) : Fin (d + 1) → ℚ := fun q => n.factorization q

private theorem vec_relation (d k m : ℕ) (hk : 1 ≤ k) (hm : m ≤ d) (e : ℕ → ℤ)
    (he : ∑ j ∈ Icc k m, (e j : ℚ) • vec d j = 0) :
    ∏ j ∈ Icc k m, (j : ℚ) ^ e j = 1 := by
  apply rat_one_of_val
  · exact prod_pos (fun j hj => zpow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hk.trans (mem_Icc.mp hj).1))) _)
  intro q hq
  let : Fact q.Prime := ⟨hq⟩
  rw [val_prod q hq _ _ (fun j hj => zpow_ne_zero _ (by exact_mod_cast
    (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hk.trans (mem_Icc.mp hj).1)))))]
  simp only [padicValRat.zpow, padicValRat.of_nat, ← Nat.factorization_def _ hq]
  by_cases hqd : q ≤ d
  · have hh := congrFun he ⟨q, by omega⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vec, Pi.zero_apply] at hh
    exact_mod_cast hh
  · apply sum_eq_zero
    intro j hj
    rw [Nat.factorization_eq_zero_of_lt (by have := (mem_Icc.mp hj).2; omega)]
    simp

private theorem relation_of_mem_span (d k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (hm : m ≤ d)
    (h : vec d k ∈ Submodule.span ℚ (vec d '' (Ioc k m : Set ℕ))) : Relation k m := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := ℚ) (s := Ioc k m)).mp h
  obtain ⟨D, hD, z, hz⟩ := clear_den_on (Ioc k m) a
  let e : ℕ → ℤ := fun j => if j = k then D else -z j
  refine ⟨e, by simpa [e] using hD, vec_relation d k m hk hm e ?_⟩
  rw [Icc_eq_cons_Ioc hkm, sum_cons]
  simp only [e, ite_eq_left rfl]
  have hs : ∑ j ∈ Ioc k m, ((if j = k then D else -z j : ℤ) : ℚ) • vec d j =
      -(D : ℚ) • vec d k := by
    calc
      _ = ∑ j ∈ Ioc k m, (-(D : ℚ) * a j) • vec d j := by
        apply sum_congr rfl
        intro j hj
        rw [ite_eq_right (ne_of_gt (mem_Ioc.mp hj).1), Int.cast_neg, hz j hj, neg_mul]
      _ = -(D : ℚ) • (∑ j ∈ Ioc k m, a j • vec d j) := by
        simp [Finset.smul_sum, mul_smul]
      _ = _ := by rw [ha]
  rw [hs, neg_smul, add_neg_cancel]

private theorem separator (d k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (hm : m ≤ d)
    (hn : ¬Relation k m) :
    ∃ z : Fin (d + 1) → ℤ,
      (∑ q, z q * (k.factorization q : ℤ)) ≠ 0 ∧
      ∀ j ∈ Ioc k m, (∑ q, z q * (j.factorization q : ℤ)) = 0 := by
  classical
  have hv : vec d k ∉ Submodule.span ℚ (vec d '' (Ioc k m : Set ℕ)) :=
    fun h => hn (relation_of_mem_span d k m hk hkm hm h)
  obtain ⟨f, hfk, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  obtain ⟨D, hD, z, hz⟩ := clear_den
    (fun i : Fin (d + 1) => f (fun j => if i = j then 1 else 0))
  have hd (n : ℕ) : ((∑ q, z q * (n.factorization q : ℤ) : ℤ) : ℚ) = D * f (vec d n) := by
    push_cast
    simp_rw [hz]
    rw [LinearMap.pi_apply_eq_sum_univ f (vec d n)]
    simp only [vec, smul_eq_mul, mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  refine ⟨z, ?_, ?_⟩
  · intro he
    have he' := hd k
    rw [he, Int.cast_zero] at he'
    exact (mul_ne_zero (Int.cast_ne_zero.mpr hD) hfk) he'.symm
  · intro j hj
    have hfj : f (vec d j) = 0 := by
      have hj' : vec d j ∈ Submodule.span ℚ (vec d '' (Ioc k m : Set ℕ)) :=
        Submodule.subset_span ⟨j, hj, rfl⟩
      have hfj' := Submodule.mem_map_of_mem (f := f) hj'
      rw [hf, Submodule.mem_bot] at hfj'
      exact hfj'
    have hdj := hd j
    rw [hfj, mul_zero] at hdj
    exact_mod_cast hdj

private noncomputable def repList (s : Finset ℕ) (c : ℕ → ℕ) : List ℕ :=
  (s.toList.flatMap (fun j => List.replicate (c j) j)).mergeSort (· ≤ ·)

private theorem repList_count (s : Finset ℕ) (c : ℕ → ℕ) (x : ℕ) :
    (repList s c).count x = if x ∈ s then c x else 0 := by
  classical
  unfold repList
  rw [(List.mergeSort_perm _ _).count_eq, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate]
  rw [Finset.sum_map_toList]
  simp only [beq_iff_eq, sum_ite_eq']

private theorem repList_mem (s : Finset ℕ) (c : ℕ → ℕ) (x : ℕ) (hx : x ∈ repList s c) : x ∈ s := by
  classical
  have hc : 0 < (repList s c).count x := List.count_pos_iff.mpr hx
  rw [repList_count] at hc
  by_contra hs
  simp [hs] at hc

private theorem repList_sorted (s : Finset ℕ) (c : ℕ → ℕ) : (repList s c).Pairwise (· ≤ ·) :=
  by
  exact List.pairwise_mergeSort' _ _

private theorem repList_prod (s : Finset ℕ) (c : ℕ → ℕ) :
    (repList s c).prod = ∏ j ∈ s, j ^ c j := by
  classical
  rw [Finset.prod_list_count_of_subset (repList s c) s
    (fun j hj => repList_mem s c j (List.mem_toFinset.mp hj))]
  apply prod_congr rfl
  intro j hj
  rw [repList_count, ite_eq_left hj]

private theorem list_endpoints (k m : ℕ) (b : List ℕ) (hs : b.Pairwise (· ≤ ·))
    (hb : ∀ j ∈ b, j ∈ Icc k m) (hk : k ∈ b) :
    ∃ l, l ≤ m ∧ b.head? = some k ∧ b.getLast? = some l := by
  have hne : b ≠ [] := List.ne_nil_of_mem hk
  refine ⟨b.getLast hne, (mem_Icc.mp (hb _ (List.getLast_mem hne))).2, ?_,
    List.getLast?_eq_some_getLast hne⟩
  cases b with
  | nil => simp at hk
  | cons a t =>
    have hka := (mem_Icc.mp (hb a (by simp))).1
    have hak : a ≤ k := hs.rel_head hk
    have : a = k := le_antisymm hak hka
    simp [this]

private theorem residue_pow (k m p : ℕ) (hk : 1 ≤ k) (hp : 0 < p) (e : ℕ → ℤ)
    (he : ∏ j ∈ Icc k m, (j : ℚ) ^ e j = 1) :
    ∃ r : ℚ, ((∏ j ∈ Icc k m, j ^ (e j % (p : ℤ)).toNat : ℕ) : ℚ) = r ^ p := by
  let s := Icc k m
  let a : ℕ → ℚ := fun j => (j : ℚ) ^ (-(e j / (p : ℤ)))
  refine ⟨∏ j ∈ s, a j, ?_⟩
  have hterm (j : ℕ) (hj : j ∈ s) :
      (j : ℚ) ^ (e j % (p : ℤ)).toNat = (j : ℚ) ^ e j * (a j) ^ p := by
    have hj0 : (j : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hk.trans (mem_Icc.mp hj).1)))
    have hc : ((e j % (p : ℤ)).toNat : ℤ) = e j + (-(e j / (p : ℤ))) * p := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
      have hh := Int.emod_add_mul_ediv (e j) (p : ℤ)
      nlinarith [hh]
    rw [← zpow_natCast, hc, zpow_add₀ hj0, zpow_mul, zpow_natCast]
  push_cast
  change (∏ j ∈ s, (j : ℚ) ^ (e j % (p : ℤ)).toNat) = _
  rw [prod_congr rfl hterm, prod_mul_distrib]
  have he' : (∏ j ∈ s, (j : ℚ) ^ e j) = 1 := he
  rw [he', one_mul, prod_pow]

private theorem int_root (a : ℕ) (r : ℚ) (p : ℕ) (hp : 0 < p) (h : (a : ℚ) = r ^ p) :
    ∃ c : ℤ, (a : ℤ) = c ^ p := by
  have hi : IsIntegral ℤ (r ^ p) := by
    rw [← h]
    exact isIntegral_natCast a
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := ℤ) hp hi
  change (c : ℚ) = r at hc
  refine ⟨c, ?_⟩
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_natCast, Int.cast_pow, hc] using h

private theorem upper_valid (k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (h : Relation k m) :
    ∃ N, ∀ p : ℕ, p.Prime → N ≤ p → ∃ l, l ≤ m ∧ ∃ b, Valid p k l b := by
  classical
  obtain ⟨e, hek, he⟩ := h
  refine ⟨(e k).natAbs + 1, ?_⟩
  intro p hp hNp
  let c : ℕ → ℕ := fun j => (e j % (p : ℤ)).toNat
  have hc (j : ℕ) : c j < p := by
    have h0 := Int.emod_nonneg (e j) (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
    have hlt := Int.emod_lt_of_pos (e j) (show (0 : ℤ) < p by exact_mod_cast hp.pos)
    exact_mod_cast (show ((c j : ℕ) : ℤ) < p by simpa [c, Int.toNat_of_nonneg h0] using hlt)
  have hck : c k ≠ 0 := by
    intro hh
    have hemod : e k % (p : ℤ) = 0 := by
      have hn := Int.emod_nonneg (e k) (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
      simpa [c, Int.toNat_of_nonneg hn] using (congrArg (fun n : ℕ => (n : ℤ)) hh)
    have hdvd : (p : ℤ) ∣ e k := Int.dvd_of_emod_eq_zero hemod
    have hlt : (e k).natAbs < (p : ℤ).natAbs := Nat.lt_of_succ_le hNp
    exact hek (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt)
  let b := repList (Icc k m) c
  have hb : k ∈ b := by
    apply List.count_pos_iff.mp
    simp only [b, repList_count, mem_Icc, le_refl, hkm, and_self, ite_true]
    exact Nat.pos_of_ne_zero hck
  obtain ⟨l, hl, hhead, hlast⟩ := list_endpoints k m b (repList_sorted _ _)
    (fun j hj => repList_mem _ _ _ hj) hb
  refine ⟨l, hl, b, hhead, hlast, repList_sorted _ _, ?_, ?_⟩
  · intro x hx
    rw [show b = repList (Icc k m) c from rfl, repList_count,
      ite_eq_left (repList_mem _ _ _ hx)]
    exact hc x
  · obtain ⟨r, hr⟩ := residue_pow k m p hk hp.pos e he
    rw [← repList_prod] at hr
    exact int_root b.prod r p hp.pos hr


private theorem valid_bounds (p k m : ℕ) (b : List ℕ) (h : Valid p k m b) :
    k ≤ m ∧ ∀ j ∈ b, j ∈ Icc k m := by
  obtain ⟨hh, hl, hs, hc, hp⟩ := h
  have hlo : ∀ j ∈ b, k ≤ j := by
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hh
    intro j hj
    exact hs.rel_head hj
  have hhi : ∀ j ∈ b, j ≤ m := by
    obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    intro j hj
    simpa using hs.rel_getLast hj
  refine ⟨hlo m (List.mem_of_getLast? hl), ?_⟩
  intro j hj
  exact mem_Icc.mpr ⟨hlo j hj, hhi j hj⟩

private theorem lower_valid (k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (hn : ¬Relation k m) :
    ∃ N, ∀ p : ℕ, p.Prime → N ≤ p → ∀ b, ¬Valid p k m b := by
  classical
  obtain ⟨z, hzk, hzj⟩ := separator m k m hk hkm le_rfl hn
  let w : ℕ → ℤ := fun n => ∑ q : Fin (m + 1), z q * (n.factorization q : ℤ)
  refine ⟨(w k).natAbs + 1, ?_⟩
  intro p hp hNp b hb
  have hbsub := (valid_bounds p k m b hb).2
  obtain ⟨c, hc⟩ := hb.2.2.2.2
  let a := c.natAbs
  have hprod : b.prod = a ^ p := by
    have hh := congrArg Int.natAbs hc
    simpa only [Int.natAbs_natCast, Int.natAbs_pow] using hh
  have hcoords (q : Fin (m + 1)) :
      ∑ j ∈ Icc k m, b.count j * j.factorization q = p * a.factorization q := by
    rw [Finset.prod_list_count_of_subset b (Icc k m)
      (fun j hj => hbsub j (List.mem_toFinset.mp hj))] at hprod
    have hh := congrArg (fun n : ℕ => n.factorization q) hprod
    rw [Nat.factorization_prod_apply (fun j hj => pow_ne_zero _
      (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hk.trans (mem_Icc.mp hj).1))))] at hh
    simpa only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] using hh
  have hcoordsI (q : Fin (m + 1)) :
      ∑ j ∈ Icc k m, (b.count j : ℤ) * (j.factorization q : ℤ) =
      (p : ℤ) * (a.factorization q : ℤ) := by exact_mod_cast hcoords q
  have hsum : ∑ j ∈ Icc k m, (b.count j : ℤ) * w j = (p : ℤ) * w a := by
    calc
      _ = ∑ q : Fin (m + 1), z q * (∑ j ∈ Icc k m,
          (b.count j : ℤ) * (j.factorization q : ℤ)) := by
        simp only [w, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro q hq
        apply sum_congr rfl
        intro j hj
        ring
      _ = ∑ q : Fin (m + 1), z q * ((p : ℤ) * (a.factorization q : ℤ)) := by
        simp_rw [hcoordsI]
      _ = _ := by
        simp only [w, mul_sum]
        apply sum_congr rfl
        intro q hq
        ring
  rw [Icc_eq_cons_Ioc hkm, sum_cons] at hsum
  have hzero : ∑ j ∈ Ioc k m, (b.count j : ℤ) * w j = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [show w j = 0 from hzj j hj, mul_zero]
  rw [hzero, add_zero] at hsum
  have hdiv : (p : ℤ) ∣ (b.count k : ℤ) * w k := ⟨w a, hsum⟩
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hprime.dvd_or_dvd hdiv with hdc | hdw
  · have hdc' : p ∣ b.count k := Int.natCast_dvd_natCast.mp hdc
    have hcount := hb.2.2.2.1 k (List.mem_of_head? hb.1)
    have hcountpos : 0 < b.count k := List.count_pos_iff.mpr (List.mem_of_head? hb.1)
    have := Nat.le_of_dvd hcountpos hdc'
    omega
  · have hlt : (w k).natAbs < (p : ℤ).natAbs := Nat.lt_of_succ_le hNp
    exact hzk (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdw hlt)


private theorem relation_exists (k : ℕ) (hk : 1 ≤ k) : ∃ m, k ≤ m ∧ Relation k m := by
  classical
  let m := k * (k + 1)
  have hmk : k < m := by
    exact lt_mul_of_one_lt_right (lt_of_lt_of_le Nat.zero_lt_one hk) (Nat.lt_succ_of_le hk)
  have hmk1 : k + 1 ≤ m := Nat.le_mul_of_pos_left (k + 1) hk
  let e : ℕ → ℤ := fun j => (if j = k then 1 else 0) +
    (if j = k + 1 then 1 else 0) - (if j = m then 1 else 0)
  refine ⟨m, hmk.le, e, ?_, vec_relation m k m hk le_rfl e ?_⟩
  · simp [e, ne_of_lt hmk]
  · have hmul : vec m m = vec m k + vec m (k + 1) := by
      funext q
      simp only [vec, m, Nat.factorization_mul (Nat.ne_zero_of_lt hk : k ≠ 0)
        (Nat.succ_ne_zero k : k + 1 ≠ 0), Finsupp.add_apply, Nat.cast_add, Pi.add_apply]
    simp only [e, Int.cast_sub, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
      add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_smul,
      one_smul, zero_smul]
    simp only [sum_ite_eq', mem_Icc, le_refl, hmk.le, hmk1, Nat.le_succ, and_self,
      ite_true]
    rw [hmul, sub_self]

theorem result : D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.claim := by
  classical
  intro k hk
  have hex := relation_exists k hk
  have hA : k ≤ A071537 k ∧ Relation k (A071537 k) := by
    unfold A071537
    rw [dite_eq_left hex]
    exact Nat.find_spec hex
  obtain ⟨Nu, hNu⟩ := upper_valid k (A071537 k) hk hA.1 hA.2
  have hlow : ∀ m ∈ Ico k (A071537 k),
      ∃ N, ∀ p : ℕ, p.Prime → N ≤ p → ∀ b, ¬Valid p k m b := by
    intro m hm
    have hn : ¬Relation k m := by
      intro hr
      have hnot := Nat.find_min hex (show m < Nat.find hex from by
        have hlt := (mem_Ico.mp hm).2
        simpa only [A071537, dite_eq_left hex] using hlt)
      exact hnot ⟨(mem_Ico.mp hm).1, hr⟩
    exact lower_valid k m hk (mem_Ico.mp hm).1 hn
  choose! N hN using hlow
  refine ⟨max Nu ((Ico k (A071537 k)).sup N), ?_⟩
  intro p hp hNp
  obtain ⟨l, hl, b, hb⟩ := hNu p hp (le_trans (le_max_left _ _) hNp)
  have hexp : ∃ m b, Valid p k m b := ⟨l, b, hb⟩
  have hT : T p k = Nat.find hexp := by simp only [T, dite_eq_left hexp]
  rw [hT]
  have hle : Nat.find hexp ≤ A071537 k := (Nat.find_le ⟨b, hb⟩).trans hl
  apply le_antisymm hle
  by_contra hge
  have hlt : Nat.find hexp < A071537 k := Nat.lt_of_not_ge hge
  obtain ⟨b', hb'⟩ := Nat.find_spec hexp
  have hm : Nat.find hexp ∈ Ico k (A071537 k) :=
    mem_Ico.mpr ⟨(valid_bounds p k (Nat.find hexp) b' hb').1, hlt⟩
  have hpN : N (Nat.find hexp) ≤ p := le_trans
    (le_trans (Finset.le_sup hm) (le_max_right _ _)) hNp
  exact hN (Nat.find hexp) hm p hp hpN b' hb'

end D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences
