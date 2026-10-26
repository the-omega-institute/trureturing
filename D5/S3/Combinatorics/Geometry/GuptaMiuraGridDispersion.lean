/- GID: D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer grid Lipschitz functions satisfy Gupta's dispersion bound. -/

/-
result:
  proof_shape: content (sorting with a missing-level induction, then centered FKG comparison)
  escape_witness: sorted_step (a unit-gap integer chain has no missing sorted level;
    consumed through sorted_chain_lip and the row/column Lipschitz estimates)
  admission_basis: open-problem-resolution (#19839; Proved)
  Direct frozen dependencies: D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.grid sha256:d245f43debb535edb6005b8a5de97c6ebc0f5c2cd6a8d833de4cb3bc2b556ca8.
The public definitions and claim use the source expressions. The proof uses
Mathlib's Tuple.sort, fkg and SignType.sign; rational signs are casts of that owner.
The grid expression remains literal in IsLipschitz; lipschitz_owner uses the existing
LeeLiuThreeRowIntegerDomination.grid in the proof instead of adding another grid declaration.
The origami distance reductions and Conjecture 4.6 are outside this statement.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21178.
-/


import D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Basic.Sign.Defs

/-! Binding conventions for C. Gupta, "Height functions on the m × n Miura-ori flip graph: degree sequence and
diameter", arXiv:2606.22614v2, Section 4: the `ℓ₁` median-dispersion "disp(ϕ) = min_{K∈ℤ} Σ_v |ϕ(v) − K|" of an integer
function on the grid `G_{m,n}`, the quantity "D(m, n) = min_{K∈ℤ} Σ_{i=1}^m Σ_{j=1}^n |(i + j) − K|", and inequality (4):
no integer 1-Lipschitz function on `G_{m,n}`, realisable or not, has dispersion exceeding `D(m, n)`. The grid is
`pathGraph m □ pathGraph n`, with cell `(i, j)` of the source at `(i - 1, j - 1)`. -/

namespace D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion

open SimpleGraph


/-- `ϕ` is integer 1-Lipschitz on `G_{m,n}`: adjacent cells differ by at most one. -/
def IsLipschitz {m n : ℕ} (ϕ : Fin m × Fin n → ℤ) : Prop :=
  ∀ u v, (pathGraph m □ pathGraph n).Adj u v → |ϕ u - ϕ v| ≤ 1

/-- The `ℓ₁` median-dispersion `disp(ϕ) = min_{K∈ℤ} Σ_v |ϕ(v) − K|`. -/
noncomputable def disp {m n : ℕ} (ϕ : Fin m × Fin n → ℤ) : ℕ :=
  sInf (Set.range fun K : ℤ => ∑ v, (ϕ v - K).natAbs)

/-- `D(m, n) = min_{K∈ℤ} Σ_{i=1}^m Σ_{j=1}^n |(i + j) − K|`. -/
noncomputable def D (m n : ℕ) : ℕ :=
  sInf (Set.range fun K : ℤ => ∑ i : Fin m, ∑ j : Fin n, (((i : ℤ) + 1) + ((j : ℤ) + 1) - K).natAbs)

/-- Inequality (4): every integer 1-Lipschitz function on `G_{m,n}` has dispersion at most `D(m, n)`. -/
def claim : Prop :=
  ∀ (m n : ℕ) (ϕ : Fin m × Fin n → ℤ), IsLipschitz ϕ → disp ϕ ≤ D m n

end D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion


open Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion

/-- Signed FKG for the uniform measure on a finite distributive lattice. -/
private theorem uniform_covariance {α : Type*} [Fintype α] [DistribLattice α]
    (f g : α → ℚ) (hf : Monotone f) (hg : Monotone g) :
    (∑ x, f x) * (∑ x, g x) ≤ (Fintype.card α : ℚ) * ∑ x, f x * g x := by
  classical
  by_cases he : Nonempty α
  · let _ := he
    obtain ⟨a, ha⟩ := Finset.exists_min_image univ f (univ_nonempty)
    obtain ⟨b, hb⟩ := Finset.exists_min_image univ g (univ_nonempty)
    have h := fkg (μ := fun _ : α => (1 : ℚ))
      (f := fun x => f x - f a) (g := fun x => g x - g b)
      (by intro x; norm_num)
      (by intro x; exact sub_nonneg.mpr (ha.2 x (mem_univ x)))
      (by intro x; exact sub_nonneg.mpr (hb.2 x (mem_univ x)))
      (fun _ _ h => sub_le_sub_right (hf h) _) (fun _ _ h => sub_le_sub_right (hg h) _) (by intro x y; norm_num)
    simp only [one_mul, sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ] at h
    simp only [sub_mul, mul_sub, sum_sub_distrib, ← sum_mul, ← mul_sum,
      sum_const, nsmul_eq_mul, card_univ] at h
    nlinarith [h]
  · have : IsEmpty α := not_nonempty_iff.mp he
    simp


private theorem sgn_monotone : Monotone (fun x : ℚ => (SignType.sign x : ℚ)) := by
  intro x y h
  simp only [sign_apply]
  split_ifs <;> norm_num <;> linarith

private theorem abs_subgradient (x y : ℚ) :
    |x| + (SignType.sign x : ℚ) * (y - x) ≤ |y| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp only [sign_neg hx, SignType.coe_neg_one, abs_of_neg hx]
    linarith [neg_le_abs y]
  · simp
  · simp only [sign_pos hx, SignType.coe_one, abs_of_pos hx]
    linarith [le_abs_self y]

/-- Comparison for centered monotone functions with monotone remainder. -/
private theorem centered_abs_comparison {α : Type*} [Fintype α] [DistribLattice α]
    (f a : α → ℚ) (hf : Monotone f) (hr : Monotone (fun x => a x - f x)) :
    (∑ x, |f x - (∑ y, f y) / Fintype.card α|) ≤
      ∑ x, |a x - (∑ y, a y) / Fintype.card α| := by
  classical
  by_cases hn : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    simp
  · have hnq : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast hn
    let ef : ℚ := (∑ y, f y) / Fintype.card α
    let ea : ℚ := (∑ y, a y) / Fintype.card α
    let s : α → ℚ := fun x => (fun x : ℚ => (SignType.sign x : ℚ)) (f x - ef)
    have hs : Monotone s := sgn_monotone.comp (fun _ _ h => sub_le_sub_right (hf h) ef)
    have hc := uniform_covariance s (fun x => a x - f x) hs hr
    have hp := sum_le_sum (s := univ) (fun x _ =>
      abs_subgradient (f x - ef) (a x - ea))
    have hz : 0 ≤ ∑ x, s x * ((a x - ea) - (f x - ef)) := by
      have hform : (∑ x, s x * ((a x - ea) - (f x - ef))) =
          (∑ x, s x * (a x - f x)) - (∑ x, s x) * (ea - ef) := by
        simp only [sub_sub_sub_comm, mul_sub, sum_sub_distrib, ← sum_mul]
      rw [hform, sub_nonneg]
      have he : ea - ef = ((∑ x, a x) - ∑ x, f x) / Fintype.card α := by
        dsimp [ea, ef]; ring
      rw [he, ← mul_div_assoc]
      have hnpos : (0 : ℚ) < Fintype.card α := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      apply (div_le_iff₀ hnpos).mpr
      simpa only [sum_sub_distrib, mul_comm] using hc
    simp only [sum_add_distrib] at hp
    change (∑ x, |f x - ef|) ≤ ∑ x, |a x - ea|
    linarith

end D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion


open Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion
private noncomputable def sorted {n : ℕ} (f : Fin n → ℤ) : Fin n → ℤ := f ∘ Tuple.sort f

private theorem card_filter_perm {α : Type*} [Fintype α] (e : Equiv.Perm α) (p : α → Prop) [DecidablePred p] :
    #{x | p (e x)} = #{x | p x} := by
  classical
  simpa using Equiv.sum_comp e (fun x => if p x then (1 : ℕ) else 0)

private theorem sorted_le {n : ℕ} (f g : Fin n → ℤ) (h : ∀ i, f i ≤ g i) :
    ∀ i, sorted f i ≤ sorted g i := by
  classical
  intro i
  apply (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort f)).mp
  change i.val < #{k | f (Tuple.sort f k) ≤ sorted g i}
  rw [card_filter_perm (Tuple.sort f) (fun k => f k ≤ sorted g i)]
  have hg := (Tuple.lt_card_le_iff_apply_le_of_monotone
    (Tuple.monotone_sort g) (j := i) (a := sorted g i)).mpr le_rfl
  change i.val < #{k | g (Tuple.sort g k) ≤ sorted g i} at hg
  rw [card_filter_perm (Tuple.sort g) (fun k => g k ≤ sorted g i)] at hg
  apply lt_of_lt_of_le hg
  exact card_le_card (fun k hk => mem_filter.mpr
    ⟨mem_univ k, (h k).trans (mem_filter.mp hk).2⟩)

private theorem sorted_add_const {n : ℕ} (f : Fin n → ℤ) (c : ℤ) :
    sorted (fun i => f i + c) = fun i => sorted f i + c := by
  have h := Tuple.unique_monotone (f := fun i => f i + c)
    (σ := Tuple.sort (fun i => f i + c)) (τ := Tuple.sort f)
    (Tuple.monotone_sort _) ((Tuple.monotone_sort f).add_const c)
  exact h

private theorem sorted_close {n : ℕ} (f g : Fin n → ℤ) (h : ∀ i, |f i - g i| ≤ 1) :
    ∀ i, |sorted f i - sorted g i| ≤ 1 := by
  intro i
  have hfg := sorted_le f (fun k => g k + 1) (by intro k; have := (abs_le.mp (h k)).2; omega) i
  have hgf := sorted_le g (fun k => f k + 1) (by intro k; have := (abs_le.mp (h k)).1; omega) i
  rw [sorted_add_const] at hfg hgf
  dsimp only at hfg hgf
  exact abs_le.mpr ⟨by omega, by omega⟩

private theorem sorted_step {n : ℕ} (f : Fin (n + 1) → ℤ)
    (hf : ∀ i : Fin n, |f i.succ - f i.castSucc| ≤ 1) :
    ∀ i : Fin n, sorted f i.succ - sorted f i.castSucc ≤ 1 := by
  classical
  intro i
  by_contra! hbad
  let t := sorted f i.castSucc
  have hno : ∀ k, f k ≤ t ∨ t + 2 ≤ f k := by
    intro k
    let l := (Tuple.sort f).symm k
    have hk : sorted f l = f k := by simp [sorted, l]
    by_cases hl : l ≤ i.castSucc
    · left
      have hh := (Tuple.monotone_sort f) hl
      change sorted f l ≤ t at hh
      rwa [hk] at hh
    · right
      have hli : i.succ ≤ l := by change i.val + 1 ≤ l.val; change ¬ l.val ≤ i.val at hl; omega
      have hh := (Tuple.monotone_sort f) hli
      change sorted f i.succ ≤ sorted f l at hh
      rw [hk] at hh
      change 1 < sorted f i.succ - t at hbad
      omega
  have hstep : ∀ j : Fin n, f j.castSucc ≤ t ↔ f j.succ ≤ t := by
    intro j
    have h := abs_le.mp (hf j)
    rcases hno j.castSucc with h0 | h0 <;> rcases hno j.succ with h1 | h1 <;> omega
  have hconst : ∀ k : Fin (n + 1), f k ≤ t ↔ f 0 ≤ t := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ j ih => exact (hstep j).symm.trans ih
  have hlow : f 0 ≤ t := (hconst (Tuple.sort f i.castSucc)).mp le_rfl
  have hhigh := (hconst (Tuple.sort f i.succ)).mpr hlow
  change sorted f i.succ ≤ t at hhigh
  change 1 < sorted f i.succ - t at hbad
  omega

end D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion

namespace D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion

private def ChainLip {n : ℕ} (f : Fin n → ℤ) : Prop :=
  ∀ i j, i.val + 1 = j.val → |f j - f i| ≤ 1

private theorem sorted_chain_lip {n : ℕ} (f : Fin n → ℤ) (hf : ChainLip f) :
    ChainLip (sorted f) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    intro i j hij
    have hi : i.val < n := by omega
    let k : Fin n := ⟨i.val, hi⟩
    have h0 : k.castSucc = i := by ext; rfl
    have h1 : k.succ = j := by ext; simp [k]; omega
    have hs := sorted_step f (fun k => hf k.castSucc k.succ (by simp)) k
    have hm := Tuple.monotone_sort f (show i ≤ j by change i.val ≤ j.val; omega)
    change sorted f i ≤ sorted f j at hm
    rw [h0, h1] at hs
    exact abs_le.mpr ⟨by omega, hs⟩

private theorem index_remainder_monotone {n : ℕ} (f : Fin n → ℤ) (hf : ChainLip f) :
    Monotone (fun i : Fin n => (i : ℤ) - f i) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have h := (abs_le.mp (hf i.castSucc i.succ (by simp))).2
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    omega

private def GridLip {m n : ℕ} (f : Fin m × Fin n → ℤ) : Prop :=
  (∀ j, ChainLip (fun i => f (i, j))) ∧ (∀ i, ChainLip (fun j => f (i, j)))

private noncomputable def rows {m n : ℕ} (f : Fin m × Fin n → ℤ) : Fin m × Fin n → ℤ :=
  fun p => sorted (fun j => f (p.1, j)) p.2

private noncomputable def cols {m n : ℕ} (f : Fin m × Fin n → ℤ) : Fin m × Fin n → ℤ :=
  fun p => sorted (fun i => f (i, p.2)) p.1

private noncomputable def rearranged {m n : ℕ} (f : Fin m × Fin n → ℤ) := cols (rows f)

private theorem rows_grid_lip {m n : ℕ} (f : Fin m × Fin n → ℤ) (hf : GridLip f) :
    GridLip (rows f) := by
  constructor
  · intro j i k hik
    change |sorted (fun j => f (k, j)) j - sorted (fun j => f (i, j)) j| ≤ 1
    exact sorted_close (fun j => f (k, j)) (fun j => f (i, j))
      (fun j => hf.1 j i k hik) j
  · intro i
    change ChainLip (sorted (fun j => f (i, j)))
    exact sorted_chain_lip _ (hf.2 i)

private theorem cols_grid_lip {m n : ℕ} (f : Fin m × Fin n → ℤ) (hf : GridLip f) :
    GridLip (cols f) := by
  constructor
  · intro j
    change ChainLip (sorted (fun i => f (i, j)))
    exact sorted_chain_lip _ (hf.1 j)
  · intro i j k hjk
    change |sorted (fun i => f (i, k)) i - sorted (fun i => f (i, j)) i| ≤ 1
    exact sorted_close (fun i => f (i, k)) (fun i => f (i, j))
      (fun i => hf.2 i j k hjk) i

private theorem grid_monotone {m n : ℕ} (f : Fin m × Fin n → ℤ)
    (hc : ∀ j, Monotone (fun i => f (i, j)))
    (hr : ∀ i, Monotone (fun j => f (i, j))) : Monotone f := by
  exact monotone_prod_iff.mpr ⟨hr, hc⟩

private theorem rearranged_monotone {m n : ℕ} (f : Fin m × Fin n → ℤ) :
    Monotone (rearranged f) := by
  apply grid_monotone
  · intro j
    exact Tuple.monotone_sort (fun i => rows f (i, j))
  · intro i j k hjk
    exact sorted_le _ _ (fun a => Tuple.monotone_sort (fun b => f (a, b)) hjk) i

private theorem grid_remainder_monotone {m n : ℕ} (f : Fin m × Fin n → ℤ) (hf : GridLip f) :
    Monotone (fun p : Fin m × Fin n => (p.1 : ℤ) + (p.2 : ℤ) - f p) := by
  apply grid_monotone
  · intro j i k hik
    have h := index_remainder_monotone (fun i => f (i, j)) (hf.1 j) hik
    dsimp at h ⊢
    omega
  · intro i j k hjk
    have h := index_remainder_monotone (fun j => f (i, j)) (hf.2 i) hjk
    dsimp at h ⊢
    omega

private theorem rearranged_sum {m n : ℕ} (f : Fin m × Fin n → ℤ)
    {β : Type*} [AddCommMonoid β] (h : ℤ → β) :
    (∑ p, h (rearranged f p)) = ∑ p, h (f p) := by
  classical
  have roweq : ∀ g : Fin m × Fin n → ℤ,
      (∑ p, h (rows g p)) = ∑ p, h (g p) := by
    intro g
    simp only [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    exact Equiv.sum_comp (Tuple.sort (fun j => g (i, j))) (fun j => h (g (i, j)))
  have coleq : ∀ g : Fin m × Fin n → ℤ,
      (∑ p, h (cols g p)) = ∑ p, h (g p) := by
    intro g
    simp only [Fintype.sum_prod_type]
    rw [sum_comm, sum_comm (f := fun i j => h (g (i, j)))]
    apply sum_congr rfl
    intro j _
    exact Equiv.sum_comp (Tuple.sort (fun i => g (i, j))) (fun i => h (g (i, j)))
  exact (coleq (rows f)).trans (roweq f)

end D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion


open Finset
open scoped BigOperators
namespace D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion

private def costQ {α : Type*} [Fintype α] (f : α → ℤ) (c : ℚ) : ℚ :=
  ∑ x, |(f x : ℚ) - c|

/-- Integer-valued data have an integer center no worse than any rational center. -/
private theorem integer_center {α : Type*} [Fintype α] (f : α → ℤ) (c : ℚ) :
    ∃ k : ℤ, costQ f k ≤ costQ f c := by
  classical
  let k : ℤ := ⌊c⌋
  let t : ℚ := c - k
  have hk : (k : ℚ) ≤ c := Int.floor_le c
  have hk1 : c ≤ (k : ℚ) + 1 := (Int.lt_floor_add_one c).le
  have ht0 : 0 ≤ t := sub_nonneg.mpr hk
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hp : ∀ x, |(f x : ℚ) - c| =
      (1 - t) * |(f x : ℚ) - k| + t * |(f x : ℚ) - ((k : ℚ) + 1)| := by
    intro x
    by_cases h : f x ≤ k
    · have hq : (f x : ℚ) ≤ k := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      dsimp [t]; ring
    · have hq : (k : ℚ) + 1 ≤ f x := by exact_mod_cast (show k + 1 ≤ f x by omega)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      dsimp [t]; ring
  have hs : costQ f c = (1 - t) * costQ f k + t * costQ f (k + 1) := by
    unfold costQ
    simp only [hp, sum_add_distrib, ← mul_sum]
  by_cases h : costQ f k ≤ costQ f c
  · exact ⟨k, h⟩
  · refine ⟨k + 1, ?_⟩
    simp only [Int.cast_add, Int.cast_one]
    by_contra! hbad
    have hlow : costQ f c < costQ f k := lt_of_not_ge h
    by_cases ht : t = 0
    · simp only [ht, sub_zero, one_mul, zero_mul, add_zero] at hs
      linarith
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      have h0 := mul_le_mul_of_nonneg_left hlow.le (sub_nonneg.mpr ht1)
      have h1 := mul_lt_mul_of_pos_left hbad htpos
      nlinarith

/-- A symmetric finite sample is minimized at its center. -/
private theorem symmetric_center_min {α : Type*} [Fintype α] (a : α → ℚ)
    (e : Equiv.Perm α) (c : ℚ) (hsym : ∀ x, a (e x) = 2 * c - a x) (k : ℚ) :
    ∑ x, |a x - c| ≤ ∑ x, |a x - k| := by
  classical
  have hp : ∀ x, 2 * |a x - c| ≤ |a x - k| + |a (e x) - k| := by
    intro x
    have ht := abs_sub_le (a x) k (a (e x))
    rw [abs_sub_comm k (a (e x))] at ht
    rw [hsym] at ht
    have he : a x - (2 * c - a x) = 2 * (a x - c) := by ring
    rw [he, abs_mul] at ht
    norm_num at ht
    simpa only [hsym] using ht
  have hs := sum_le_sum (s := univ) (fun x _ => hp x)
  simp only [sum_add_distrib, ← mul_sum] at hs
  rw [Equiv.sum_comp e (fun x => |a x - k|)] at hs
  linarith

/-- The mean of a nonempty symmetric finite sample is its center. -/
private theorem symmetric_mean {α : Type*} [Fintype α] (hn : Fintype.card α ≠ 0)
    (a : α → ℚ) (e : Equiv.Perm α) (c : ℚ)
    (hsym : ∀ x, a (e x) = 2 * c - a x) :
    (∑ x, a x) / Fintype.card α = c := by
  have h := Equiv.sum_comp e a
  simp_rw [hsym, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at h
  have hnq : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast hn
  apply (div_eq_iff hnq).mpr
  linarith

end D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion

namespace D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion
open Finset

private theorem lipschitz_owner {m n : ℕ} (f : Fin m × Fin n → ℤ) :
    IsLipschitz f ↔ ∀ u v,
      (D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination.grid m n).Adj u v →
        |f u - f v| ≤ 1 := Iff.rfl

private theorem lipschitz_grid_lip {m n : ℕ} (f : Fin m × Fin n → ℤ) (hf : IsLipschitz f) :
    GridLip f := by
  have hf := (lipschitz_owner f).mp hf
  constructor
  · intro j i k hik
    have h := hf (i, j) (k, j)
      (SimpleGraph.boxProd_adj_left.mpr (SimpleGraph.pathGraph_adj.mpr (Or.inl hik)))
    simpa only [abs_sub_comm] using h
  · intro i j k hjk
    have h := hf (i, j) (i, k)
      (SimpleGraph.boxProd_adj_right.mpr (SimpleGraph.pathGraph_adj.mpr (Or.inl hjk)))
    simpa only [abs_sub_comm] using h

private theorem disp_rearranged {m n : ℕ} (f : Fin m × Fin n → ℤ) :
    disp (rearranged f) = disp f := by
  have hc : (fun k : ℤ => ∑ p, (rearranged f p - k).natAbs) =
      (fun k : ℤ => ∑ p, (f p - k).natAbs) :=
    funext (fun k => rearranged_sum f (fun z => (z - k).natAbs))
  unfold disp
  rw [hc]

private theorem disp_le_rational_cost {m n : ℕ} (f : Fin m × Fin n → ℤ) (c : ℚ) :
    (disp f : ℚ) ≤ costQ f c := by
  obtain ⟨k, hk⟩ := integer_center f c
  have hd : disp f ≤ ∑ p, (f p - k).natAbs := csInf_le' ⟨k, rfl⟩
  have hq : (disp f : ℚ) ≤ ∑ p, ((f p - k).natAbs : ℚ) := by exact_mod_cast hd
  have he : (∑ p, ((f p - k).natAbs : ℚ)) = costQ f k := by
    simp only [costQ, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  exact (hq.trans_eq he).trans hk

theorem result : claim := by
  intro m n f hf
  classical
  by_cases hn : Fintype.card (Fin m × Fin n) = 0
  · have : IsEmpty (Fin m × Fin n) := Fintype.card_eq_zero_iff.mp hn
    have hd : disp f = 0 := by simp [disp]
    rw [hd]
    exact Nat.zero_le _
  · let F := rearranged f
    have hF := rearranged_monotone f
    have hL := cols_grid_lip (rows f) (rows_grid_lip f (lipschitz_grid_lip f hf))
    have hR := grid_remainder_monotone F hL
    let a : Fin m × Fin n → ℚ := fun p => (p.1.val : ℚ) + (p.2.val : ℚ) + 2
    let c : ℚ := ((m : ℚ) + n + 2) / 2
    let e : Equiv.Perm (Fin m × Fin n) := Equiv.prodCongr Fin.revPerm Fin.revPerm
    have hsym : ∀ p, a (e p) = 2 * c - a p := by
      intro p
      have hm : p.1.rev.val + p.1.val + 1 = m := by simp only [Fin.val_rev]; omega
      have hnn : p.2.rev.val + p.2.val + 1 = n := by simp only [Fin.val_rev]; omega
      have hmq : (p.1.rev : ℚ) + (p.1 : ℚ) + 1 = m := by exact_mod_cast hm
      have hnq : (p.2.rev : ℚ) + (p.2 : ℚ) + 1 = n := by exact_mod_cast hnn
      change (p.1.rev.val : ℚ) + (p.2.rev.val : ℚ) + 2 =
        2 * (((m : ℚ) + n + 2) / 2) - ((p.1.val : ℚ) + (p.2.val : ℚ) + 2)
      linarith
    have hmean := symmetric_mean hn a e c hsym
    have hcomp := centered_abs_comparison (fun p => (F p : ℚ)) a
      (fun p q hpq => by
        change (F p : ℚ) ≤ (F q : ℚ)
        exact_mod_cast (show F p ≤ F q from hF hpq))
      (fun p q hpq => by
        have h := hR hpq
        dsimp [a]
        exact_mod_cast (show (p.1 : ℤ) + (p.2 : ℤ) + 2 - F p ≤
          (q.1 : ℤ) + (q.2 : ℤ) + 2 - F q by dsimp at h; omega))
    rw [hmean] at hcomp
    have hdisp : (disp f : ℚ) ≤ ∑ p, |a p - c| := by
      rw [← disp_rearranged f]
      exact (disp_le_rational_cost F _).trans hcomp
    apply le_csInf (Set.range_nonempty _)
    rintro z ⟨k, rfl⟩
    have hd := hdisp.trans (symmetric_center_min a e c hsym k)
    have he : (∑ p, |a p - (k : ℚ)|) =
        ((∑ i : Fin m, ∑ j : Fin n,
          (((i : ℤ) + 1) + ((j : ℤ) + 1) - k).natAbs : ℕ) : ℚ) := by
      simp only [a, Fintype.sum_prod_type, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs,
        Int.cast_sub, Int.cast_add, Int.cast_natCast]
      congr 1
      ext i
      congr 1
      ext j
      congr 1
      ring
    rw [he] at hd
    exact_mod_cast hd

end D5.S3.Combinatorics.Geometry.GuptaMiuraGridDispersion
