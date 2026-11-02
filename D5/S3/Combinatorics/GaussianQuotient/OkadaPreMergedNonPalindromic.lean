/- GID: D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-three pre-merged Gaussian determinants are not almost palindromic. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuGaussian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Okada's width-three pre-merged determinant conjecture. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic

open Polynomial
open scoped BigOperators
open D5.S3.Combinatorics.CylindricPartition.LiUncuDefs (gauss)

private noncomputable def qFactorial (n : ℕ) : ℤ[X] :=
  ∏ h ∈ Finset.range n, (1 - X ^ (h + 1))

private theorem qFactorial_succ (n : ℕ) :
    qFactorial (n + 1) = qFactorial n * (1 - X ^ (n + 1)) := by
  simp [qFactorial, Finset.prod_range_succ, mul_comm]

private theorem gauss_diagonal (n : ℕ) : gauss n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [gauss, D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt n (n + 1) (by omega),
        Nat.sub_self]
      simpa using ih

private theorem gauss_coeff_zero (n k : ℕ) (hkn : k ≤ n) :
    (gauss n k).coeff 0 = 1 := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp [gauss]
  | succ n ih =>
      cases k with
      | zero => simp [gauss]
      | succ k =>
          by_cases hk : k = n
          · subst k
            rw [gauss, D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt n (n + 1)
              (by omega), gauss_diagonal]
            simp
          · have hkn' : k + 1 ≤ n := by omega
            have hnk : 0 < n - k := by omega
            rw [gauss]
            rw [coeff_add, ih (k + 1) hkn']
            rw [coeff_X_pow_mul']
            simp [hnk.ne']

private theorem gauss_coeff_one (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (gauss n k).coeff 1 = 1 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hkn' : k + 1 ≤ n := by omega
          rw [gauss, coeff_add]
          by_cases hdiag : k + 1 = n
          · subst n
            rw [gauss_diagonal, coeff_one, coeff_X_pow_mul']
            simp [gauss_coeff_zero]
          · have hlt : k + 1 < n := by omega
            rw [ih (k + 1) (by omega) hlt, coeff_X_pow_mul']
            have hpow : 1 < n - k := by omega
            have hnot : ¬ n ≤ 1 + k := by omega
            simp [hnot]

def IsAlmostPalindromic (f : ℤ[X]) : Prop :=
  ((f.support.sort (· ≤ ·)).map f.coeff).reverse =
    (f.support.sort (· ≤ ·)).map f.coeff

noncomputable def preMerged {μ : ℕ} (a b : Fin μ → ℕ) : ℤ[X] :=
  (∏ i, gauss (b i) (a i)) - ∏ i, gauss (b i) (a (Fin.rev i))

def claim : Prop :=
  ∀ (μ : ℕ) (a b : Fin μ → ℕ),
    3 ≤ μ → StrictMono a → StrictMono b → (∀ i j, a i ≤ b j) →
      ¬ IsAlmostPalindromic (preMerged a b)

private theorem factorial_identity
    (n k : ℕ) (hkn : k ≤ n) :
    gauss n k * qFactorial k * qFactorial (n - k) = qFactorial n := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst hk
      simp [qFactorial, gauss]
  | succ n ih =>
      by_cases hk : k = 0
      · subst k
        simp [qFactorial, gauss]
      by_cases hkn' : k = n + 1
      · subst k
        rw [qFactorial_succ]
        rw [gauss, D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt n (n + 1) (by omega),
          gauss_diagonal]
        simp [qFactorial]
      have hkn'' : k ≤ n := by omega
      have hkpos : 0 < k := by omega
      have hsub : n + 1 - k = n - k + 1 := by omega
      have hhook :
          (1 - X ^ (n + 1 - k)) * gauss (n + 1) k =
            (1 - X ^ (n + 1)) * gauss n k := by
        simpa using
          D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_hook (n + 1) k (by omega)
      rw [hsub, qFactorial_succ (n - k)]
      calc
        gauss (n + 1) k * qFactorial k *
            (qFactorial (n - k) * (1 - X ^ (n - k + 1))) =
            qFactorial k * qFactorial (n - k) *
              ((1 - X ^ (n + 1 - k)) * gauss (n + 1) k) := by
          rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
          ring
        _ = qFactorial k * qFactorial (n - k) *
              ((1 - X ^ (n + 1)) * gauss n k) := by rw [hhook]
        _ = qFactorial (n + 1) := by
          calc
            qFactorial k * qFactorial (n - k) *
                ((1 - X ^ (n + 1)) * gauss n k) =
                gauss n k * qFactorial k * qFactorial (n - k) *
                  (1 - X ^ (n + 1)) := by ring
            _ = qFactorial n * (1 - X ^ (n + 1)) := by rw [ih k hkn'']
            _ = qFactorial (n + 1) := (qFactorial_succ n).symm

private theorem index_bounds
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 3 ≤ μ) (ha : StrictMono a)
    (hb : StrictMono b) (hcross : ∀ i j, a i ≤ b j) :
    let t := b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩
    (∀ i, t + 2 ≤ b i - a i) ∧
      b ⟨0, by omega⟩ - a (⟨μ - 1, by omega⟩) = t ∧
      (∀ i : Fin μ, 0 < i.val → t + 2 ≤ b i - a (Fin.rev i)) := by
  dsimp only
  let z : Fin μ := ⟨0, by omega⟩
  let u : Fin μ := ⟨1, by omega⟩
  let v : Fin μ := ⟨μ - 1, by omega⟩
  have hazu := ha (show z < u by change 0 < 1; omega)
  have hauv := ha (show u < v by change 1 < μ - 1; omega)
  have hbzu := hb (show z < u by change 0 < 1; omega)
  have hbuv := hb (show u < v by change 1 < μ - 1; omega)
  have hbase := hcross v z
  change (∀ i, b z - a v + 2 ≤ b i - a i) ∧ _ ∧ _
  refine ⟨?_, rfl, ?_⟩
  · intro i
    by_cases hiz : i = z
    · subst i
      omega
    by_cases hiv : i = v
    · subst i
      omega
    have hbi := hb (show z < i by
      change 0 < i.val
      have : i.val ≠ 0 := fun h => hiz (Fin.ext h)
      omega)
    have hai := ha (show i < v by
      change i.val < μ - 1
      have : i.val ≠ μ - 1 := fun h => hiv (Fin.ext h)
      omega)
    omega
  · intro i hi
    have hbi := hb (show z < i from hi)
    have hai := ha (show Fin.rev i < v by
      change (Fin.rev i).val < μ - 1
      simp only [Fin.val_rev]
      omega)
    change b z - a v + 2 ≤ b i - a (Fin.rev i)
    omega

private theorem low_end
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 3 ≤ μ) (ha : StrictMono a)
    (hb : StrictMono b) (hcross : ∀ i j, a i ≤ b j) :
    let p := preMerged a b
    let t := b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩
    let c := if 0 < a ⟨0, by omega⟩ then μ else μ - 1
    p.coeff (t + 1) = 1 ∧ p.coeff (t + 2) = c + 1 ∧
      (∀ n, n < t + 1 → p.coeff n = 0) := by
  sorry

private theorem high_end
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 3 ≤ μ) (ha : StrictMono a)
    (hb : StrictMono b) (hcross : ∀ i j, a i ≤ b j) :
    let p := preMerged a b
    let d := ∑ i, a i * (b i - a i)
    let c := if 0 < a ⟨0, by omega⟩ then μ else μ - 1
    p.natDegree = d ∧ p.coeff d = 1 ∧ p.coeff (d - 1) = c ∧
      d ≥ b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩ + 4 := by
  sorry

private theorem palindrome_contradiction
    (p : ℤ[X]) (r d c : ℕ)
    (hfirst : p.coeff r = 1 ∧ p.coeff (r + 1) = c + 1)
    (hlast : p.natDegree = d ∧ p.coeff d = 1 ∧ p.coeff (d - 1) = c)
    (hbelow : ∀ n, n < r → p.coeff n = 0) (hcpos : 0 < c)
    (hgap : r + 1 < d - 1) (hc : c + 1 ≠ c)
    (hpal : IsAlmostPalindromic p) : False := by
  let l := p.support.sort (· ≤ ·)
  have hsorted : l.SortedLT := p.support.sortedLT_sort
  have hmem (n : ℕ) : n ∈ l ↔ p.coeff n ≠ 0 := by
    simp [l]
  have hr : r ∈ l := (hmem r).2 (by rw [hfirst.1]; norm_num)
  have hs : r + 1 ∈ l := (hmem (r + 1)).2 (by rw [hfirst.2]; positivity)
  have ht : d - 1 ∈ l := (hmem (d - 1)).2 (by
    rw [hlast.2.2]
    exact_mod_cast hcpos.ne')
  have hd : d ∈ l := (hmem d).2 (by rw [hlast.2.1]; norm_num)
  have hb (n : ℕ) (hn : n ∈ l) : r ≤ n ∧ n ≤ d := by
    refine ⟨?_, ?_⟩
    · by_contra h
      exact (hmem n).1 hn (hbelow n (by omega))
    · rw [← hlast.1]
      exact le_natDegree_of_ne_zero ((hmem n).1 hn)
  obtain ⟨ir, hir, her⟩ := List.mem_iff_getElem.1 hr
  obtain ⟨is, his, hes⟩ := List.mem_iff_getElem.1 hs
  obtain ⟨it, hit, het⟩ := List.mem_iff_getElem.1 ht
  obtain ⟨id, hid, hed⟩ := List.mem_iff_getElem.1 hd
  have hn : 0 < l.length := by omega
  have hz : l[0] = r := by
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le
      (hi := hn) (hj := hir) (Nat.zero_le ir)
    have hge := (hb l[0] (List.getElem_mem hn)).1
    omega
  have hspos : 0 < is := by
    have hlt : l[0] < l[is] := by omega
    exact hsorted.getElem_lt_getElem_iff.1 hlt
  have hn2 : 1 < l.length := by omega
  have hsecond : l[1] = r + 1 := by
    have hlt := hsorted.getElem_lt_getElem_of_lt (hi := hn) (hj := hn2) (by omega : 0 < 1)
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le
      (hi := hn2) (hj := his) (by omega : 1 ≤ is)
    omega
  have htop : l[l.length - 1] = d := by
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le (hi := hid)
      (hj := (by omega : l.length - 1 < l.length)) (by omega : id ≤ l.length - 1)
    have hge := (hb l[l.length - 1] (List.getElem_mem (by omega))).2
    omega
  have htlt : it < l.length - 1 := by
    apply hsorted.getElem_lt_getElem_iff.1
    omega
  have hpenult : l[l.length - 2] = d - 1 := by
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le (hi := hit)
      (hj := (by omega : l.length - 2 < l.length)) (by omega : it ≤ l.length - 2)
    have hlt := hsorted.getElem_lt_getElem_of_lt
      (hi := (by omega : l.length - 2 < l.length))
      (hj := (by omega : l.length - 1 < l.length)) (by omega : l.length - 2 < l.length - 1)
    omega
  change (l.map p.coeff).reverse = l.map p.coeff at hpal
  have heq := congrArg (fun xs : List ℤ => xs[1]?) hpal
  have hidx : l.length - 1 - 1 = l.length - 2 := by omega
  rw [List.getElem?_reverse (l := l.map p.coeff) (i := 1) (by simpa using hn2)] at heq
  simp only [List.length_map, hidx,
    List.getElem?_map, List.getElem?_eq_getElem (by omega : l.length - 2 < l.length),
    List.getElem?_eq_getElem hn2, Option.map_some, hpenult, hsecond,
    hlast.2.2, hfirst.2, Option.some.injEq] at heq
  exact hc (by exact_mod_cast heq.symm)

theorem result : claim := by
  intro μ a b hμ ha hb hcross
  let t := b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩
  let r := t + 1
  let c := if 0 < a ⟨0, by omega⟩ then μ else μ - 1
  have hlo := low_end μ a b hμ ha hb hcross
  have hhi := high_end μ a b hμ ha hb hcross
  intro hpal
  apply palindrome_contradiction (preMerged a b) r (∑ i, a i * (b i - a i)) c
  · simpa [r, t, c] using And.intro hlo.1 hlo.2.1
  · simpa [c] using And.intro hhi.1 (And.intro hhi.2.1 hhi.2.2.1)
  · simpa [r, t] using hlo.2.2
  · dsimp [c]
    split <;> omega
  · dsimp [r, t]
    omega
  · dsimp [c]
    omega
  · exact hpal

end D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
