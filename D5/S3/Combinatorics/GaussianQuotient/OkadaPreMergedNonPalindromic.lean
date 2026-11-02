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
        simpa using D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_hook (n + 1) k (by omega)
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
  sorry

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
    (hgap : r + 1 < d - 1) (hc : c + 1 ≠ c)
    (hpal : IsAlmostPalindromic p) : False := by
  sorry

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
  · dsimp [r, t]
    omega
  · dsimp [c]
    omega
  · exact hpal

end D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
