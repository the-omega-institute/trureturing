/- GID: D5/S3/Combinatorics/Partitions/ShlykConvexityIndex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/ShlykConvexityIndex
   mirror-E: none(waiver:symbolic-exact-partition-index)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Defs]
   utility: none
   digest: Every convexity index at least two occurs at all sufficiently large partition totals. -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! An exact convexity-index construction in literal partition multiplicities. -/

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace D5.S3.Combinatorics.Partitions.ShlykConvexityIndex

-- At the anchor the congruence and pair equations force both auxiliary
-- coordinates to be 1.
private abbrev Pair (k : ℕ) := Fin k ⊕ Fin k
private abbrev Col (k : ℕ) := Pair k × Bool
private abbrev Row (k : ℕ) := Option (Pair k ⊕ Fin k)

private def a {k : ℕ} (i : Fin k) : Col k := (.inl i, false)
private def b {k : ℕ} (i : Fin k) : Col k := (.inl i, true)
private def u {k : ℕ} (i : Fin k) : Col k := (.inr i, false)
private def v {k : ℕ} (i : Fin k) : Col k := (.inr i, true)

private def sumRow {k : ℕ} : Row k := none
private def pairRow {k : ℕ} (p : Pair k) : Row k := some (.inl p)
private def modRow {k : ℕ} (i : Fin k) : Row k := some (.inr i)

private def matrix {k : ℕ} (o : Fin k) (r : Row k) (c : Col k) : ℕ :=
  match r with
  | none => if ∃ i, c = a i then 1 else 0
  | some (.inl p) => if c.1 = p then 1 else 0
  | some (.inr i) => if c = a i ∨ c = b o then 1 else if c = v i then k else 0

private def evalRow {k : ℕ} (o : Fin k) (z : Col k → ℕ) (r : Row k) : ℕ :=
  ∑ c, matrix o r c * z c

private theorem sum_cols {k : ℕ} {R : Type*} [AddCommMonoid R] (f : Col k → R) :
    ∑ c, f c = (∑ i, (f (a i) + f (b i))) + ∑ i, (f (u i) + f (v i)) := by
  simp [Fintype.sum_prod_type, Fintype.sum_sum_type, a, b, u, v, add_comm]

private theorem eval_sumRow {k : ℕ} (o : Fin k) (z : Col k → ℕ) :
    evalRow o z sumRow = ∑ i, z (a i) := by
  simp [evalRow, sum_cols, matrix, sumRow, a, b, u, v]

private theorem eval_pairRow {k : ℕ} (o : Fin k) (z : Col k → ℕ) (p : Pair k) :
    evalRow o z (pairRow p) = z (p, false) + z (p, true) := by
  cases p <;> simp [evalRow, sum_cols, matrix, pairRow, a, b, u, v,
    sum_add_distrib]

private theorem eval_modRow {k : ℕ} (o : Fin k) (z : Col k → ℕ) (i : Fin k) :
    evalRow o z (modRow i) = z (a i) + z (b o) + k * z (v i) := by
  simp [evalRow, sum_cols, matrix, modRow, a, b, u, v,
    sum_add_distrib, add_assoc]

private def center {k : ℕ} : Col k → ℕ
  | (.inl _, true) => k - 1
  | _ => 1

private def indicator {k : ℕ} (j i : Fin k) : ℕ := if j = i then 1 else 0

private def alt {k : ℕ} (o j : Fin k) : Col k → ℕ
  | (.inl i, false) => if i = j then k else 0
  | (.inl i, true) => k - (if i = j then k else 0)
  | (.inr i, false) => 1 + indicator j i - indicator j o
  | (.inr i, true) => 1 + indicator j o - indicator j i

private theorem center_pos {k : ℕ} (hk : 2 ≤ k) (c : Col k) : 0 < center c := by
  rcases c with ⟨p, t⟩
  cases p <;> cases t <;> simp [center] <;> omega

private def rhs {k : ℕ} : Row k → ℕ
  | none => k
  | some (.inl (.inl _)) => k
  | some (.inl (.inr _)) => 2
  | some (.inr _) => 2 * k

private theorem center_eval {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (r : Row k) :
    evalRow o center r = rhs r := by
  rcases r with _ | (_ | i)
  · change evalRow o center sumRow = k
    rw [eval_sumRow]
    simp [center, a]
  · rename_i p
    change evalRow o center (pairRow p) = rhs (pairRow p)
    rw [eval_pairRow]
    cases p <;> simp [center, rhs, pairRow] <;> omega
  · change evalRow o center (modRow i) = 2 * k
    rw [eval_modRow]
    simp [center, a, b, v]
    omega

private theorem alt_eval {k : ℕ} (o j : Fin k) (r : Row k) :
    evalRow o (alt o j) r = rhs r := by
  rcases r with _ | (p | i)
  · change evalRow o (alt o j) sumRow = k
    rw [eval_sumRow]
    simp [alt, a]
  · change evalRow o (alt o j) (pairRow p) = rhs (pairRow p)
    rw [eval_pairRow]
    cases p with
    | inl i => by_cases hij : i = j <;> simp [alt, rhs, pairRow, hij]
    | inr i => by_cases hji : j = i <;> by_cases hjo : j = o <;>
        simp [alt, indicator, rhs, pairRow, hji, hjo] <;> split <;> omega
  · change evalRow o (alt o j) (modRow i) = 2 * k
    rw [eval_modRow]
    by_cases hi : i = j <;> by_cases ho : o = j <;>
      simp [alt, a, b, v, indicator, hi, ho, eq_comm (a := j)] <;> omega

private theorem same_a {k : ℕ} (hk : 2 ≤ k) (o : Fin k) {z z' : Col k → ℕ}
    (hz : ∀ r, evalRow o z r = rhs r) (hz' : ∀ r, evalRow o z' r = rhs r)
    (ha : ∀ i, z (a i) = z' (a i)) : z = z' := by
  have hb (i : Fin k) : z (b i) = z' (b i) := by
    have h := hz (pairRow (.inl i))
    have h' := hz' (pairRow (.inl i))
    rw [eval_pairRow] at h h'
    change z (a i) + z (b i) = k at h
    change z' (a i) + z' (b i) = k at h'
    have := ha i
    omega
  have hv (i : Fin k) : z (v i) = z' (v i) := by
    have h := hz (modRow i)
    have h' := hz' (modRow i)
    rw [eval_modRow] at h h'
    have hm : k * z (v i) = k * z' (v i) := by
      rw [ha i, hb o] at h
      omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hm
  have hu (i : Fin k) : z (u i) = z' (u i) := by
    have h := hz (pairRow (.inr i))
    have h' := hz' (pairRow (.inr i))
    rw [eval_pairRow] at h h'
    change z (u i) + z (v i) = 2 at h
    change z' (u i) + z' (v i) = 2 at h'
    have := hv i
    omega
  funext c
  rcases c with ⟨p, t⟩
  cases p with
  | inl i =>
    cases t
    · exact ha i
    · exact hb i
  | inr i =>
    cases t
    · exact hu i
    · exact hv i

private theorem equation_fiber {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (z : Col k → ℕ) :
    (∀ r, evalRow o z r = rhs r) ↔ z = center ∨ ∃ j, z = alt o j := by
  constructor
  · intro hz
    have hs : ∑ i, z (a i) = k := by
      have h := hz sumRow
      rw [eval_sumRow] at h
      exact h
    have hp (i : Fin k) : z (a i) + z (b i) = k := by
      have h := hz (pairRow (Sum.inl i))
      rw [eval_pairRow] at h
      exact h
    have hle (i : Fin k) : z (a i) ≤ k := by have := hp i; omega
    have hm (i : Fin k) : z (a i) % k = z (a o) % k := by
      have h := hz (modRow i)
      rw [eval_modRow] at h
      change z (a i) + z (b o) + k * z (v i) = 2 * k at h
      have hp0 := hp o
      have he : z (a i) + k * z (v i) = z (a o) + k := by omega
      have hd := congrArg (fun q : ℕ => q % k) he
      simpa [Nat.add_mod] using hd
    by_cases hzero : z (a o) % k = 0
    · have hcases (i : Fin k) : z (a i) = 0 ∨ z (a i) = k := by
        by_cases h : z (a i) < k
        · left
          simpa [Nat.mod_eq_of_lt h, hzero] using hm i
        · right
          have := hle i
          omega
      have hex : ∃ j, z (a j) ≠ 0 := by
        by_contra! h
        simp [h] at hs
        omega
      obtain ⟨j, hj⟩ := hex
      have hjk := (hcases j).resolve_left hj
      right
      refine ⟨j, same_a hk o hz (alt_eval o j) (fun i => ?_)⟩
      by_cases hij : i = j
      · subst i
        simpa [alt, a] using hjk
      · have hsum : z (a i) + z (a j) ≤ ∑ l, z (a l) := by
          simpa [Finset.sum_pair hij] using
            (Finset.sum_le_sum_of_subset (f := fun l : Fin k => z (a l))
              (show {i, j} ⊆ Finset.univ from Finset.subset_univ _))
        have hi0 : z (a i) = 0 := by omega
        simpa [alt, a, hij] using hi0
    · have hlt (i : Fin k) : z (a i) < k := by
        have hh := hle i
        by_contra! hn
        have he : z (a i) = k := by omega
        exact hzero (by simpa only [he, Nat.mod_self] using (hm i).symm)
      have he (i : Fin k) : z (a i) = z (a o) % k := by
        simpa [Nat.mod_eq_of_lt (hlt i)] using hm i
      have hsum : k * (z (a o) % k) = k * 1 := by
        calc
          k * (z (a o) % k) = ∑ _i : Fin k, z (a o) % k := by simp [Nat.mul_comm]
          _ = ∑ i, z (a i) := sum_congr rfl (fun i _ => (he i).symm)
          _ = k * 1 := by simpa only [mul_one] using hs
      have hres := Nat.eq_of_mul_eq_mul_left (by omega) hsum
      left
      exact same_a hk o hz (center_eval hk o) (fun i => by rw [he i, hres]; rfl)
  · rintro (rfl | ⟨j, rfl⟩)
    · exact center_eval hk o
    · exact alt_eval o j

-- Little-endian digits encode row equations. The leading digit bounds the
-- multiplicity sum before any digit of a putative solution is recovered.
section Radix

variable {C R : Type*} [Fintype C]

private def numeral (B : ℕ) (rows : List R) (f : R → ℕ) (lead : ℕ) : ℕ :=
  Nat.ofDigits B (rows.map f ++ [lead])

private theorem numeral_eq (B : ℕ) (rows : List R) (f : R → ℕ) (lead : ℕ) :
    numeral B rows f lead = Nat.ofDigits B (rows.map f) + B ^ rows.length * lead := by
  simp [numeral, Nat.ofDigits_append]

private theorem numeral_linear (B : ℕ) (rows : List R) (A : R → C → ℕ) (z : C → ℕ) :
    ∑ c, numeral B rows (fun r => A r c) 1 * z c =
      numeral B rows (fun r => ∑ c, A r c * z c) (∑ c, z c) := by
  induction rows with
  | nil => simp [numeral]
  | cons r rows ih =>
    simp only [numeral, List.map_cons, List.cons_append, Nat.ofDigits_cons] at ih ⊢
    simp_rw [add_mul, sum_add_distrib, mul_assoc, ← mul_sum, ih]

private theorem numeral_inj (B : ℕ) (hb : 1 < B) (rows : List R) {f g : R → ℕ} {t t' : ℕ}
    (hf : ∀ r ∈ rows, f r < B) (hg : ∀ r ∈ rows, g r < B)
    (ht : t < B) (ht' : t' < B)
    (h : numeral B rows f t = numeral B rows g t') :
    (∀ r ∈ rows, f r = g r) ∧ t = t' := by
  have bound (j : R → ℕ) (b : ℕ) (hj : ∀ r ∈ rows, j r < B) (hjb : b < B) :
      ∀ q ∈ rows.map j ++ [b], q < B := by
    intro q hq
    rcases List.mem_append.mp hq with hmap | hlast
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmap
      exact hj r hr
    · simpa using (List.mem_singleton.mp hlast) ▸ hjb
  have hd := Nat.ofDigits_inj_of_len_eq hb (by simp)
    (bound f t hf ht) (bound g t' hg ht') h
  obtain ⟨hm, hl⟩ := List.append_inj hd (by simp)
  exact ⟨List.map_inj_left.mp hm, by simpa using hl⟩

private theorem numeral_fiber (B K T : ℕ) (hb : 1 < B) (hKT : K * T < B) (hT : T < B)
    (rows : List R) (allRows : ∀ r : R, r ∈ rows)
    (A : R → C → ℕ) (d : R → ℕ) (hA : ∀ r c, A r c ≤ K) (hd : ∀ r, d r < B)
    (z : C → ℕ) :
    (∑ c, numeral B rows (fun r => A r c) 1 * z c = numeral B rows d T) ↔
      (∀ r, ∑ c, A r c * z c = d r) ∧ ∑ c, z c = T := by
  constructor
  · intro h
    have htarget : numeral B rows d T < B ^ rows.length * (T + 1) := by
      have hlow : Nat.ofDigits B (rows.map d) < B ^ rows.length := by
        simpa only [List.length_map] using
          Nat.ofDigits_lt_base_pow_length hb (l := rows.map d) (fun q hq => by
            obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
            exact hd r)
      rw [numeral_eq, mul_add, mul_one]
      omega
    have hlower : B ^ rows.length * (∑ c, z c) ≤ numeral B rows d T := by
      rw [mul_sum, ← h]
      apply sum_le_sum
      intro c _
      apply Nat.mul_le_mul_right
      simp [numeral_eq]
    have hcounts : ∑ c, z c ≤ T := by
      by_contra! hn
      have hcontra := Nat.mul_le_mul_left (B ^ rows.length) (show T + 1 ≤ ∑ c, z c by omega)
      omega
    have hrow (r : R) : ∑ c, A r c * z c < B := by
      calc
        ∑ c, A r c * z c ≤ ∑ c, K * z c :=
          sum_le_sum (fun c _ => Nat.mul_le_mul_right _ (hA r c))
        _ = K * (∑ c, z c) := (mul_sum ..).symm
        _ ≤ K * T := Nat.mul_le_mul_left _ hcounts
        _ < B := hKT
    rw [numeral_linear] at h
    obtain ⟨hr, ht⟩ := numeral_inj B hb rows (fun r _ => hrow r) (fun r _ => hd r)
      (lt_of_le_of_lt hcounts hT) hT h
    exact ⟨fun r => hr r (allRows r), ht⟩
  · rintro ⟨hr, ht⟩
    rw [numeral_linear, ht, funext hr]

end Radix

private noncomputable def rowList (k : ℕ) : List (Row k) := (Finset.univ : Finset (Row k)).toList

private theorem mem_rowList {k : ℕ} (r : Row k) : r ∈ rowList k := by simp [rowList]

private def count (k : ℕ) : ℕ := k * (k + 2)
private def base (k : ℕ) : ℕ := (count k + 1) * (2 * k + 1)

private theorem base_bounds {k : ℕ} (hk : 2 ≤ k) :
    1 < base k ∧ count k < base k ∧ k * count k < base k ∧ 2 * k < base k := by
  have hn : 0 ≤ count k := Nat.zero_le _
  unfold base
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem matrix_le {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (r : Row k) (c : Col k) :
    matrix o r c ≤ k := by
  rcases r with _ | (p | i)
  · simp only [matrix]
    split <;> omega
  · simp only [matrix]
    split <;> omega
  · simp only [matrix]
    split <;> [omega; split <;> omega]

private theorem rhs_le {k : ℕ} (hk : 2 ≤ k) (r : Row k) : rhs r ≤ 2 * k := by
  rcases r with _ | ((i | i) | i) <;> simp [rhs] <;> omega

private theorem matrix_injective {k : ℕ} (hk : 2 ≤ k) (o : Fin k) :
    Function.Injective (fun c : Col k => fun r => matrix o r c) := by
  rintro ⟨p, t⟩ ⟨q, s⟩ he
  have hpq : p = q := by
    have h := congrFun he (pairRow p)
    by_contra hn
    simp [matrix, pairRow, Ne.symm hn] at h
  subst q
  suffices t = s by subst s; rfl
  cases t <;> cases s
  · rfl
  · cases p with
    | inl i =>
      have h := congrFun he sumRow
      simp [matrix, sumRow, a] at h
    | inr i =>
      have h := congrFun he (modRow i)
      have hk0 : k ≠ 0 := by omega
      simp [matrix, modRow, a, b, v, hk0, eq_comm] at h
  · cases p with
    | inl i =>
      have h := congrFun he sumRow
      simp [matrix, sumRow, a] at h
    | inr i =>
      have h := congrFun he (modRow i)
      have hk0 : k ≠ 0 := by omega
      simp [matrix, modRow, a, b, v, hk0] at h
  · rfl

private noncomputable def size {k : ℕ} (o : Fin k) (c : Col k) : ℕ :=
  numeral (base k) (rowList k) (fun r => matrix o r c) 1

private noncomputable def total (k : ℕ) : ℕ :=
  numeral (base k) (rowList k) rhs (count k)

private theorem size_pos {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (c : Col k) : 0 < size o c := by
  have h := (base_bounds hk).1
  simp only [size, numeral_eq, mul_one]
  have hpow : 0 < base k ^ (rowList k).length := pow_pos (by omega) _
  omega

private theorem size_injective {k : ℕ} (hk : 2 ≤ k) (o : Fin k) : Function.Injective (size o) := by
  have ⟨hb, _, _, hkB⟩ := base_bounds hk
  intro c c' h
  have hbound (r : Row k) (j : Col k) : matrix o r j < base k := by
    have := matrix_le hk o r j
    omega
  obtain ⟨hr, _⟩ := numeral_inj (base k) hb (rowList k)
    (fun r _ => hbound r c) (fun r _ => hbound r c') hb hb h
  exact matrix_injective hk o (funext (fun r => hr r (mem_rowList r)))

private theorem eval_count {k : ℕ} (o : Fin k) (z : Col k → ℕ)
    (h : ∀ r, evalRow o z r = rhs r) : ∑ c, z c = count k := by
  have h1 (i : Fin k) : z (a i) + z (b i) = k := by
    have hi := h (pairRow (.inl i))
    rw [eval_pairRow] at hi
    exact hi
  have h2 (i : Fin k) : z (u i) + z (v i) = 2 := by
    have hi := h (pairRow (.inr i))
    rw [eval_pairRow] at hi
    exact hi
  simp [sum_cols, h1, h2, count, mul_add]

private theorem partition_fiber {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (z : Col k → ℕ) :
    (∑ c, size o c * z c = total k) ↔ z = center ∨ ∃ j, z = alt o j := by
  have ⟨hb, hT, hKT, hd⟩ := base_bounds hk
  rw [← equation_fiber hk o z]
  exact (numeral_fiber (base k) k (count k) hb hKT hT (rowList k) mem_rowList
    (matrix o) rhs (matrix_le hk o) (fun r => lt_of_le_of_lt (rhs_le hk r) hd) z).trans
    ⟨And.left, fun h => ⟨h, eval_count o z h⟩⟩

private theorem size_le_total {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (c : Col k) :
    size o c ≤ total k := by
  rw [← (partition_fiber hk o center).2 (Or.inl rfl)]
  calc
    size o c ≤ size o c * center c := by
      have hp := center_pos hk c
      simpa only [mul_one] using (Nat.mul_le_mul_left (size o c) (show 1 ≤ center c by omega))
    _ ≤ ∑ j, size o j * center j := Finset.single_le_sum (f := fun j => size o j * center j)
      (fun _ _ => Nat.zero_le _) (mem_univ c)

private noncomputable def embedVector {α β : Type*} (e : α ↪ β) (z : α → ℕ) : β → ℕ :=
  Function.extend e z (fun _ => 0)

@[local simp] private theorem embedVector_apply {α β : Type*} (e : α ↪ β) (z : α → ℕ) (i : α) :
    embedVector e z (e i) = z i :=
  e.injective.extend_apply _ _ _

private theorem embedVector_off {α β : Type*} (e : α ↪ β) (z : α → ℕ) (j : β)
    (hj : j ∉ Set.range e) : embedVector e z j = 0 :=
  Function.extend_apply' _ _ _ hj

private theorem embedVector_injective {α β : Type*} (e : α ↪ β) :
    Function.Injective (embedVector e) := by
  intro z w h
  funext i
  simpa only [embedVector_apply] using congrFun h (e i)

private theorem embedVector_restrict {α β : Type*} (e : α ↪ β) (x : β → ℕ)
    (h : ∀ j, j ∉ Set.range e → x j = 0) :
    embedVector e (fun i => x (e i)) = x := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp
  · rw [embedVector_off _ _ _ hj, h j hj]

private theorem sum_embedVector {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (z : α → ℕ) (w : β → ℕ) :
    ∑ j, w j * embedVector e z j = ∑ i, w (e i) * z i := by
  classical
  calc
    ∑ j, w j * embedVector e z j =
        ∑ j ∈ Finset.univ.map e, w j * embedVector e z j := by
      symm
      apply sum_subset (subset_univ _)
      intro j _ hj
      rw [embedVector_off _ _ _ (fun ⟨i, hi⟩ => hj (mem_map.mpr ⟨i, mem_univ _, hi⟩)), mul_zero]
    _ = ∑ i, w (e i) * z i := by rw [sum_map]; simp

private abbrev Vector (n : ℕ) := Fin n → ℕ

private def weight {n : ℕ} (x : Vector n) : ℕ := ∑ s, (s.val + 1) * x s

private def IsPartition {n : ℕ} (x : Vector n) : Prop := weight x = n

private noncomputable def partEmbedding {k : ℕ} (hk : 2 ≤ k) (o : Fin k) :
    Col k ↪ Fin (total k) where
  toFun c := ⟨size o c - 1, by
    have := size_pos hk o c
    have := size_le_total hk o c
    omega⟩
  inj' := by
    intro c d h
    have he := congrArg Fin.val h
    change size o c - 1 = size o d - 1 at he
    apply size_injective hk o
    have := size_pos hk o c
    have := size_pos hk o d
    omega

private theorem partEmbedding_val {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (c : Col k) :
    (partEmbedding hk o c).val + 1 = size o c := by
  change size o c - 1 + 1 = size o c
  have := size_pos hk o c
  omega

private theorem weight_of_columns {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (z : Col k → ℕ) :
    weight (embedVector (partEmbedding hk o) z) = ∑ c, size o c * z c := by
  unfold weight
  rw [sum_embedVector]
  simp only [partEmbedding_val]

private theorem supported_partition_fiber {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (x : Vector (total k))
    (hs : ∀ s, s ∉ Set.range (partEmbedding hk o) → x s = 0) :
    IsPartition x ↔
      x = embedVector (partEmbedding hk o) center ∨
        ∃ j, x = embedVector (partEmbedding hk o) (alt o j) := by
  have h := embedVector_restrict (partEmbedding hk o) x hs
  constructor
  · intro hp
    have hw : ∑ c, size o c * x (partEmbedding hk o c) = total k := by
      rw [← weight_of_columns hk o, h]
      exact hp
    rcases (partition_fiber hk o _).mp hw with hc | ⟨j, hj⟩
    · left
      rw [← hc, h]
    · right
      exact ⟨j, by rw [← hj, h]⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · unfold IsPartition
      rw [weight_of_columns]
      exact (partition_fiber hk o _).2 (Or.inl rfl)
    · unfold IsPartition
      rw [weight_of_columns]
      exact (partition_fiber hk o _).2 (Or.inr ⟨j, rfl⟩)

private structure Representation {n r : ℕ} (x : Vector n) (y : Fin r → Vector n)
    (weights : Fin r → ℝ) : Prop where
  distinct : Function.Injective y
  other : ∀ j, y j ≠ x
  partition : ∀ j, IsPartition (y j)
  positive : ∀ j, 0 < weights j
  normalized : ∑ j, weights j = 1
  coordinate : ∀ s, (x s : ℝ) = ∑ j, weights j * (y j s : ℝ)

private def Index (k : ℕ) {n : ℕ} (x : Vector n) : Prop :=
  (∃ (y : Fin k → Vector n) (weights : Fin k → ℝ), Representation x y weights) ∧
    ∀ (r : ℕ) (y : Fin r → Vector n) (weights : Fin r → ℝ), Representation x y weights → k ≤ r

private theorem Representation.zero_coordinate {n r : ℕ} {x : Vector n} {y : Fin r → Vector n}
    {weights : Fin r → ℝ} (h : Representation x y weights) {s : Fin n} (hx : x s = 0)
    (j : Fin r) : y j s = 0 := by
  have hsum : ∑ i, weights i * (y i s : ℝ) = 0 := by simpa [hx] using (h.coordinate s).symm
  have hnn (i : Fin r) (_ : i ∈ (Finset.univ : Finset (Fin r))) :
      0 ≤ weights i * (y i s : ℝ) :=
    mul_nonneg (h.positive i).le (Nat.cast_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (mem_univ _)
  exact_mod_cast (mul_eq_zero.mp hz).resolve_left (h.positive j).ne'

private theorem Representation.exists_pos {n r : ℕ} {x : Vector n} {y : Fin r → Vector n}
    {weights : Fin r → ℝ} (h : Representation x y weights) {s : Fin n} (hx : 0 < x s) :
    ∃ j, 0 < y j s := by
  by_contra! hn
  have hz (j : Fin r) : y j s = 0 := by have := hn j; omega
  have he : (x s : ℝ) = 0 := by simpa [hz] using h.coordinate s
  exact (Nat.cast_pos.mpr hx : (0 : ℝ) < x s).ne' he

private theorem alt_a {k : ℕ} (o j i : Fin k) : alt o j (a i) = if i = j then k else 0 := rfl

private theorem alt_injective {k : ℕ} (hk : 2 ≤ k) (o : Fin k) :
    Function.Injective (alt o) := by
  intro j l h
  have h' := congrFun h (a j)
  by_contra hjl
  simp [alt_a, hjl] at h'
  omega

private theorem alt_ne_center {k : ℕ} (hk : 2 ≤ k) (o j : Fin k) : alt o j ≠ center := by
  intro h
  have h' := congrFun h (a j)
  rw [alt_a, ite_eq_left rfl] at h'
  change k = 1 at h'
  omega

private theorem sum_alt_a {k : ℕ} (o i : Fin k) : ∑ j, (alt o j (a i) : ℝ) = k := by
  classical
  simp [alt_a, Nat.cast_ite, eq_comm (a := i)]

private theorem sum_indicator {k : ℕ} (i : Fin k) : ∑ j, (indicator j i : ℝ) = 1 := by
  classical
  simp [indicator, Nat.cast_ite]

private theorem indicator_le {k : ℕ} (j i : Fin k) : indicator j i ≤ 1 := by
  unfold indicator
  split <;> omega

private theorem sum_alt_col {k : ℕ} (hk : 2 ≤ k) (o : Fin k) (c : Col k) :
    ∑ j, (alt o j c : ℝ) = (k : ℝ) * (center c : ℝ) := by
  rcases c with ⟨p, t⟩
  cases p with
  | inl i =>
    cases t
    · change (∑ j, (alt o j (a i) : ℝ)) = (k : ℝ) * ((1 : ℕ) : ℝ)
      rw [sum_alt_a, Nat.cast_one, mul_one]
    · have h (j : Fin k) : (alt o j (b i) : ℝ) = (k : ℝ) - (alt o j (a i) : ℝ) := by
        change ((k - (if i = j then k else 0) : ℕ) : ℝ) =
          (k : ℝ) - ((if i = j then k else 0 : ℕ) : ℝ)
        rw [Nat.cast_sub (by split <;> omega)]
      change (∑ j, (alt o j (b i) : ℝ)) = (k : ℝ) * ((k - 1 : ℕ) : ℝ)
      simp_rw [h]
      rw [sum_sub_distrib, sum_alt_a, Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      simp
      ring
  | inr i =>
    have hsum (l m : Fin k) :
        ∑ j : Fin k, ((1 + indicator j l - indicator j m : ℕ) : ℝ) = k := by
      have h (j : Fin k) : ((1 + indicator j l - indicator j m : ℕ) : ℝ) =
          1 + (indicator j l : ℝ) - (indicator j m : ℝ) := by
        rw [Nat.cast_sub (le_trans (indicator_le j m) (by omega)), Nat.cast_add, Nat.cast_one]
      simp_rw [h]
      rw [sum_sub_distrib, sum_add_distrib, sum_indicator, sum_indicator]
      simp
    cases t
    · change (∑ j : Fin k, ((1 + indicator j i - indicator j o : ℕ) : ℝ)) = (k : ℝ) * ((1 : ℕ) : ℝ)
      rw [hsum, Nat.cast_one, mul_one]
    · change (∑ j : Fin k, ((1 + indicator j o - indicator j i : ℕ) : ℝ)) = (k : ℝ) * ((1 : ℕ) : ℝ)
      rw [hsum, Nat.cast_one, mul_one]

private theorem center_partition {k : ℕ} (hk : 2 ≤ k) (o : Fin k) :
    IsPartition (embedVector (partEmbedding hk o) center) := by
  unfold IsPartition
  rw [weight_of_columns]
  exact (partition_fiber hk o _).2 (Or.inl rfl)

private theorem alt_partition {k : ℕ} (hk : 2 ≤ k) (o j : Fin k) :
    IsPartition (embedVector (partEmbedding hk o) (alt o j)) := by
  unfold IsPartition
  rw [weight_of_columns]
  exact (partition_fiber hk o _).2 (Or.inr ⟨j, rfl⟩)

private theorem minimum_terms {k r : ℕ} (hk : 2 ≤ k) (o : Fin k)
    (y : Fin r → Vector (total k)) (weights : Fin r → ℝ)
    (h : Representation (embedVector (partEmbedding hk o) center) y weights) : k ≤ r := by
  let e := partEmbedding hk o
  have hs (j : Fin r) (s : Fin (total k)) (hout : s ∉ Set.range e) : y j s = 0 :=
    h.zero_coordinate (embedVector_off e center s hout) j
  have hy (j : Fin r) : ∃ l, y j = embedVector e (alt o l) := by
    rcases (supported_partition_fiber hk o (y j) (hs j)).1 (h.partition j) with hc | ha
    · exact ((h.other j) hc).elim
    · exact ha
  have hall (i : Fin k) : ∃ j, y j = embedVector e (alt o i) := by
    have hp : 0 < embedVector e center (e (a i)) := by
      rw [embedVector_apply]
      exact center_pos hk _
    obtain ⟨j, hj⟩ := h.exists_pos hp
    obtain ⟨l, hl⟩ := hy j
    rw [hl, embedVector_apply, alt_a] at hj
    have hil : i = l := by
      by_contra hn
      simp [hn] at hj
    exact ⟨j, hil ▸ hl⟩
  choose j hj using hall
  have hinj : Function.Injective j := by
    intro i l h'
    apply alt_injective hk o
    apply embedVector_injective e
    rw [← hj i, ← hj l, h']
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective j hinj

private theorem equal_weight_representation {k : ℕ} (hk : 2 ≤ k) (o : Fin k) :
    Representation (embedVector (partEmbedding hk o) center)
      (fun j => embedVector (partEmbedding hk o) (alt o j)) (fun _ : Fin k => (k : ℝ)⁻¹) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  refine ⟨(embedVector_injective _).comp (alt_injective hk o),
    (fun j h => alt_ne_center hk o j (embedVector_injective _ h)), alt_partition hk o,
    (fun _ => inv_pos.mpr (Nat.cast_pos.mpr (by omega))), ?_, ?_⟩
  · simpa [nsmul_eq_mul] using mul_inv_cancel₀ hk0
  · intro s
    by_cases hs : s ∈ Set.range (partEmbedding hk o)
    · obtain ⟨c, hc⟩ := hs
      rw [← hc]
      simp only [embedVector_apply]
      rw [← mul_sum, sum_alt_col hk o, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
    · simp [embedVector_off (partEmbedding hk o) _ _ hs]

private theorem center_index {k : ℕ} (hk : 2 ≤ k) (o : Fin k) :
    Index k (embedVector (partEmbedding hk o) center) :=
  ⟨⟨_, _, equal_weight_representation hk o⟩, fun _ => minimum_terms hk o⟩

private def smallParts {m n : ℕ} (h : 2 * m < n) : Fin m ↪ Fin n where
  toFun i := ⟨i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j he
    exact Fin.ext (congrArg (fun t : Fin n => t.val) he)

private def newPart {m n : ℕ} (h : 2 * m < n) : Fin n :=
  ⟨n - m - 1, by omega⟩

private theorem newPart_weight {m n : ℕ} (h : 2 * m < n) : (newPart h).val + 1 = n - m := by
  change n - m - 1 + 1 = n - m
  omega

private theorem newPart_off {m n : ℕ} (h : 2 * m < n) : newPart h ∉ Set.range (smallParts h) := by
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change i.val = n - m - 1 at he
  have := i.isLt
  omega

private noncomputable def pad {m n : ℕ} (h : 2 * m < n) (x : Vector m) : Vector n :=
  fun s => embedVector (smallParts h) x s + if s = newPart h then 1 else 0

@[local simp] private theorem pad_at_small {m n : ℕ} (h : 2 * m < n) (x : Vector m) (i : Fin m) :
    pad h x (smallParts h i) = x i := by
  have hi : smallParts h i ≠ newPart h := fun he => newPart_off h ⟨i, he⟩
  simp [pad, hi]

@[local simp] private theorem pad_at_new {m n : ℕ} (h : 2 * m < n) (x : Vector m) :
    pad h x (newPart h) = 1 := by
  simp [pad, embedVector_off _ _ _ (newPart_off h)]

private theorem pad_off {m n : ℕ} (h : 2 * m < n) (x : Vector m) (s : Fin n)
    (hs : s ∉ Set.range (smallParts h)) (hp : s ≠ newPart h) : pad h x s = 0 := by
  simp [pad, embedVector_off _ _ _ hs, hp]

private theorem pad_injective {m n : ℕ} (h : 2 * m < n) : Function.Injective (pad h) := by
  intro x y he
  funext i
  simpa only [pad_at_small] using congrFun he (smallParts h i)

private theorem weight_pad {m n : ℕ} (h : 2 * m < n) (x : Vector m) :
    weight (pad h x) = weight x + (n - m) := by
  classical
  simp only [weight, pad, mul_add, sum_add_distrib, sum_embedVector]
  have he : (∑ s : Fin n, (s.val + 1) * (if s = newPart h then 1 else 0)) =
      (newPart h).val + 1 := by simp [mul_ite]
  rw [he, newPart_weight]
  rfl

private theorem partition_pad_iff {m n : ℕ} (h : 2 * m < n) (x : Vector m) :
    IsPartition (pad h x) ↔ IsPartition x := by
  unfold IsPartition
  rw [weight_pad]
  omega

private theorem count_new_le_one {m n : ℕ} (h : 2 * m < n) (z : Vector n)
    (hz : IsPartition z) : z (newPart h) ≤ 1 := by
  have hle : ((newPart h).val + 1) * z (newPart h) ≤ n := by
    calc
      _ ≤ weight z := Finset.single_le_sum (f := fun s : Fin n => (s.val + 1) * z s)
        (fun _ _ => Nat.zero_le _) (mem_univ _)
      _ = n := hz
  rw [newPart_weight] at hle
  by_contra! hn
  have hbad := Nat.mul_le_mul_left (n - m) (show 2 ≤ z (newPart h) by omega)
  omega

private theorem representation_pad_iff {m n r : ℕ} (h : 2 * m < n) (x : Vector m)
    (y : Fin r → Vector m) (weights : Fin r → ℝ) :
    Representation (pad h x) (fun j => pad h (y j)) weights ↔ Representation x y weights := by
  constructor
  · intro hp
    refine ⟨fun i j he => hp.distinct (congrArg (pad h) he),
      (fun j he => hp.other j (congrArg (pad h) he)),
      (fun j => (partition_pad_iff h _).1 (hp.partition j)), hp.positive, hp.normalized, ?_⟩
    intro i
    simpa only [pad_at_small] using hp.coordinate (smallParts h i)
  · intro hp
    refine ⟨(pad_injective h).comp hp.distinct,
      (fun j he => hp.other j (pad_injective h he)),
      (fun j => (partition_pad_iff h _).2 (hp.partition j)), hp.positive, hp.normalized, ?_⟩
    intro s
    by_cases hs : s ∈ Set.range (smallParts h)
    · obtain ⟨i, rfl⟩ := hs
      simpa only [pad_at_small] using hp.coordinate i
    · by_cases hn : s = newPart h
      · subst s
        simp [hp.normalized]
      · simp [pad_off h _ _ hs hn]

-- Positivity first forces one copy of the new part in every summand.
-- It also excludes every size outside the old range and the new part.
private theorem unpad_representation {m n r : ℕ} (h : 2 * m < n) (x : Vector m)
    (Y : Fin r → Vector n) (weights : Fin r → ℝ) (hp : Representation (pad h x) Y weights) :
    ∃ y : Fin r → Vector m, Y = (fun j => pad h (y j)) ∧ Representation x y weights := by
  let p := newPart h
  have hnonneg (j : Fin r) (_ : j ∈ (Finset.univ : Finset (Fin r))) :
      0 ≤ weights j * (1 - (Y j p : ℝ)) := by
    have hle : (Y j p : ℝ) ≤ 1 := by exact_mod_cast count_new_le_one h _ (hp.partition j)
    exact mul_nonneg (hp.positive j).le (sub_nonneg.mpr hle)
  have hsum : ∑ j, weights j * (1 - (Y j p : ℝ)) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib, hp.normalized, ← hp.coordinate p]
    simp [p]
  have hone (j : Fin r) : Y j p = 1 := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum j (mem_univ _)
    have hz' := (mul_eq_zero.mp hz).resolve_left (hp.positive j).ne'
    have he : (Y j p : ℝ) = 1 := by linarith
    exact_mod_cast he
  let y : Fin r → Vector m := fun j i => Y j (smallParts h i)
  have hre : Y = (fun j => pad h (y j)) := by
    funext j s
    by_cases hs : s ∈ Set.range (smallParts h)
    · obtain ⟨i, rfl⟩ := hs
      simp [y]
    · by_cases hn : s = p
      · subst s
        exact (hone j).trans (pad_at_new h _).symm
      · have hzero : pad h x s = 0 := pad_off h x s hs hn
        rw [hp.zero_coordinate hzero j, pad_off h _ _ hs hn]
  refine ⟨y, hre, (representation_pad_iff h x y weights).1 ?_⟩
  rwa [← hre]

private theorem pad_index {k m n : ℕ} (h : 2 * m < n) (x : Vector m) :
    Index k (pad h x) ↔ Index k x := by
  constructor
  · rintro ⟨⟨Y, weights, hp⟩, hmin⟩
    obtain ⟨y, _, hy⟩ := unpad_representation h x Y weights hp
    exact ⟨⟨y, weights, hy⟩,
      fun r z μ hz => hmin r (fun j => pad h (z j)) μ ((representation_pad_iff h x z μ).2 hz)⟩
  · rintro ⟨⟨y, weights, hp⟩, hmin⟩
    refine ⟨⟨_, weights, (representation_pad_iff h x y weights).2 hp⟩, ?_⟩
    intro r Z μ hz
    obtain ⟨z, _, hz'⟩ := unpad_representation h x Z μ hz
    exact hmin r z μ hz'

/-- Every convexity index at least two occurs at every total above a threshold. -/
theorem shlyk_eventual_convexity_index :
    ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∃ x : Fin n → ℕ,
        (∑ s, (s.val + 1) * x s) = n ∧
        (∃ (y : Fin k → Fin n → ℕ) (weights : Fin k → ℝ),
          Function.Injective y ∧ (∀ j, y j ≠ x) ∧
          (∀ j, (∑ s, (s.val + 1) * y j s) = n) ∧
          (∀ j, 0 < weights j) ∧ (∑ j, weights j) = 1 ∧
          (∀ s, (x s : ℝ) = ∑ j, weights j * (y j s : ℝ))) ∧
        ∀ (r : ℕ) (y : Fin r → Fin n → ℕ) (weights : Fin r → ℝ),
          Function.Injective y → (∀ j, y j ≠ x) →
          (∀ j, (∑ s, (s.val + 1) * y j s) = n) →
          (∀ j, 0 < weights j) → (∑ j, weights j) = 1 →
          (∀ s, (x s : ℝ) = ∑ j, weights j * (y j s : ℝ)) → k ≤ r := by
  intro k hk
  let o : Fin k := ⟨0, by omega⟩
  let x₀ := embedVector (partEmbedding hk o) center
  refine ⟨2 * total k, fun n hn => ⟨pad hn x₀, ?_, ?_⟩⟩
  · exact (partition_pad_iff hn x₀).2 (center_partition hk o)
  · obtain ⟨⟨y, weights, hy⟩, hmin⟩ := (pad_index hn x₀).2 (center_index hk o)
    refine ⟨⟨y, weights, hy.distinct, hy.other, hy.partition, hy.positive, hy.normalized,
      hy.coordinate⟩, ?_⟩
    intro r z μ hd ho hp hpos hnorm hcoord
    exact hmin r z μ ⟨hd, ho, hp, hpos, hnorm, hcoord⟩

end D5.S3.Combinatorics.Partitions.ShlykConvexityIndex
