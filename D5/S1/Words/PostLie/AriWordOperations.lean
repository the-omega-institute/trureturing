/- GID: D5/S1/Words/PostLie/AriWordOperations
   generality: I
   mirror-B: D5/B/S1/Words/PostLie/AriWordOperations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite rational ari letter actions, weight, and pure-word projections. -/


import D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
import Mathlib.Algebra.FreeMonoid.Count
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Finite word presentations of the original rational ari operations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false


noncomputable section

namespace D5.S1.Words.PostLie.AriWordOperations

open scoped BigOperators TensorProduct
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra

abbrev Word := FreeMonoid ℕ
abbrev H := RationalWordPolynomial ℕ

/-- The ordinary concatenation-word basis, with coefficient one. -/
def wordBasis : Module.Basis Word ℚ H := MonoidAlgebra.basis Word ℚ

/-- The letter `v_s`, including `v_0`. -/
def letter (s : ℕ) : H := wordBasis (FreeMonoid.of s)

/-- The original strictly positive letter weight. -/
def gamma (s : ℕ) : ℕ := if s = 0 then 1 else s

/-- Total original weight, including weight zero for the empty word. -/
def weight (w : Word) : ℕ := (w.toList.map gamma).sum

/-- The number of letters different from the fixed generator. -/
def level (k : ℕ) (w : Word) : ℕ := w.countP' (· ≠ k)

/-- A coordinate support submodule in the ordinary word basis. -/
def supportSpace (S : Set Word) : Submodule ℚ H where
  carrier := {p | ∀ w, p.coeff w ≠ 0 → w ∈ S}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq w hw
    by_cases h : p.coeff w = 0
    · exact hq w (by simpa [h] using hw)
    · exact hp w h
  smul_mem' := by
    intro c p hp w hw
    exact hp w (by intro h; apply hw; simp [h])

/-- Homogeneous polynomials, with zero allowed in every degree. -/
def homogeneous (n : ℕ) : Submodule ℚ H := supportSpace {w | weight w = n}

/-- Polynomials supported in words of level at least `n`. -/
def above (k n : ℕ) : Submodule ℚ H := supportSpace {w | n ≤ level k w}

/-- Definition 4.2's extended binomial coefficient, with literal zero boundaries. -/
def beta : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | a + 1, l + 1 => a.choose l

/-- All coordinatewise bounded index choices; each tuple occurs once. -/
def lowerIndices (A : Word) : Finset (Fin A.toList.length → ℕ) :=
  Fintype.piFinset fun i => Finset.range (A.toList.get i + 1)

/-- The exact signed original ari multiplicity. -/
def multiplicity (A : Word) (l : Fin A.toList.length → ℕ) : ℚ :=
  (-1) ^ ((∑ i, A.toList.get i) + ∑ i, l i) *
    ∏ i, (beta (A.toList.get i) (l i) : ℚ)

/-- Ordinary associative commutator. -/
def commutator (p q : H) : H := p * q - q * p

/-- Left-nested commutator, in the displayed list order. -/
def nestedBracket (p : H) : List ℕ → H
  | [] => p
  | l :: ls => nestedBracket (commutator p (letter l)) ls

/-- Proposition 4.19's finite letter-action presentation, from its proof.
The empty word acts identically, whereas a nonempty word acts by zero on `v_0`. -/
def letterAction (A : Word) (s : ℕ) : H := by
  classical
  exact if A = 1 then letter s else if s = 0 then 0 else
    ∑ l ∈ lowerIndices A, multiplicity A l •
      nestedBracket (letter (s + ∑ i, (A.toList.get i - l i))) (List.ofFn l)

/-- The concatenation algebra projection `v_k ↦ X`, `v_i ↦ 0` for `i ≠ k`. -/
def pureProjection (k : ℕ) : H →ₐ[ℚ] Polynomial ℚ :=
  MonoidAlgebra.lift ℚ (Polynomial ℚ) Word
    (FreeMonoid.lift fun s => if s = k then Polynomial.X else 0)

@[simp] theorem weight_one : weight (1 : Word) = 0 := rfl

@[simp] theorem weight_mul (u v : Word) : weight (u * v) = weight u + weight v := by
  simp [weight, FreeMonoid.toList_mul]

@[simp] theorem weight_of (s : ℕ) : weight (FreeMonoid.of s) = gamma s := by
  simp [weight]

@[simp] theorem level_one (k : ℕ) : level k (1 : Word) = 0 := rfl

@[simp] theorem level_mul (k : ℕ) (u v : Word) :
    level k (u * v) = level k u + level k v :=
  FreeMonoid.countP'_mul _ _ _

@[simp] theorem level_of (k s : ℕ) : level k (FreeMonoid.of s) = if s = k then 0 else 1 := by
  simp [level, FreeMonoid.countP']

private theorem basis_mem (S : Set Word) (w : Word) (hw : w ∈ S) :
    wordBasis w ∈ supportSpace S := by
  intro v hv
  by_cases h : w = v
  · simpa [← h] using hw
  · exact False.elim (hv (by simp [wordBasis, MonoidAlgebra.coeff_single, h]))

private theorem support_mul (S T U : Set Word) (p q : H)
    (hp : p ∈ supportSpace S) (hq : q ∈ supportSpace T)
    (h : ∀ u ∈ S, ∀ v ∈ T, u * v ∈ U) : p * q ∈ supportSpace U := by
  classical
  intro w hw
  have hm := MonoidAlgebra.support_coeff_mul_subset p q (Finsupp.mem_support_iff.mpr hw)
  rcases Finset.mem_mul.mp hm with ⟨u, hu, v, hv, rfl⟩
  exact h u (hp u (Finsupp.mem_support_iff.mp hu)) v (hq v (Finsupp.mem_support_iff.mp hv))

theorem homogeneous_basis (w : Word) : wordBasis w ∈ homogeneous (weight w) :=
  basis_mem _ _ rfl

theorem above_basis (k : ℕ) (w : Word) : wordBasis w ∈ above k (level k w) :=
  basis_mem _ _ (show level k w ≤ level k w from le_refl _)

theorem homogeneous_mul (p q : H) (a b : ℕ)
    (hp : p ∈ homogeneous a) (hq : q ∈ homogeneous b) :
    p * q ∈ homogeneous (a + b) := by
  apply support_mul _ _ _ p q hp hq
  intro u hu v hv
  change weight (u * v) = a + b
  simp_all

theorem above_mul (k : ℕ) (p q : H) (a b : ℕ)
    (hp : p ∈ above k a) (hq : q ∈ above k b) : p * q ∈ above k (a + b) := by
  apply support_mul _ _ _ p q hp hq
  intro u hu v hv
  change a + b ≤ level k (u * v)
  rw [level_mul]
  exact Nat.add_le_add hu hv

private theorem homogeneous_commutator (p q : H) (a b : ℕ)
    (hp : p ∈ homogeneous a) (hq : q ∈ homogeneous b) :
    commutator p q ∈ homogeneous (a + b) := by
  apply (homogeneous (a + b)).sub_mem (homogeneous_mul p q a b hp hq)
  simpa [Nat.add_comm] using homogeneous_mul q p b a hq hp

private theorem nested_homogeneous (ls : List ℕ) (p : H) (n : ℕ)
    (hp : p ∈ homogeneous n) :
    nestedBracket p ls ∈ homogeneous (n + (ls.map gamma).sum) := by
  induction ls generalizing p n with
  | nil => simpa [nestedBracket] using hp
  | cons l ls ih =>
    simpa [nestedBracket, List.map_cons, List.sum_cons, Nat.add_assoc] using
      ih (commutator p (letter l)) (n + gamma l)
        (homogeneous_commutator p (letter l) n (gamma l) hp
          (by simpa [letter] using homogeneous_basis (FreeMonoid.of l)))

private theorem beta_zero_iff (a l : ℕ) (h : beta a l ≠ 0) : a = 0 ↔ l = 0 := by
  cases a <;> cases l <;> simp_all [beta]

private theorem beta_bound (a l : ℕ) (hb : beta a l ≠ 0) : l ≤ a := by
  cases a with
  | zero => cases l <;> simp_all [beta]
  | succ a =>
    cases l with
    | zero => omega
    | succ l =>
      by_contra hn
      have hl : a < l := by omega
      exact hb (Nat.choose_eq_zero_of_lt hl)

private theorem gamma_split (a l : ℕ) (hb : beta a l ≠ 0) :
    gamma a = gamma l + (a - l) := by
  have hle := beta_bound a l hb
  have hz := beta_zero_iff a l hb
  by_cases ha : a = 0
  · simp_all [gamma]
  · have hl : l ≠ 0 := by simpa [ha] using hz.symm
    simp [gamma, ha, hl]
    omega

private theorem multiplicity_beta (A : Word) (l : Fin A.toList.length → ℕ)
    (h : multiplicity A l ≠ 0) (i : Fin A.toList.length) : beta (A.toList.get i) (l i) ≠ 0 := by
  have hp : (∏ j, (beta (A.toList.get j) (l j) : ℚ)) ≠ 0 :=
    (mul_ne_zero_iff.mp h).2
  have := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  exact_mod_cast this

theorem letterAction_homogeneous (A : Word) (s : ℕ) :
    letterAction A s ∈ homogeneous (weight A + gamma s) := by
  classical
  unfold letterAction
  split_ifs with ha hs
  · subst A
    simpa [letter] using homogeneous_basis (FreeMonoid.of s)
  · exact (homogeneous _).zero_mem
  · apply (homogeneous _).sum_mem
    intro l hl
    by_cases hm : multiplicity A l = 0
    · simp [hm]
    apply (homogeneous _).smul_mem
    have hw : weight A = (∑ i, gamma (l i)) + ∑ i, (A.toList.get i - l i) := by
      have he : ∑ i, gamma (A.toList.get i) =
          ∑ i, (gamma (l i) + (A.toList.get i - l i)) :=
        Finset.sum_congr rfl fun i _ => gamma_split _ _ (multiplicity_beta A l hm i)
      rw [Finset.sum_add_distrib] at he
      have hsum : weight A = ∑ i : Fin A.toList.length, gamma (A.toList.get i) := by
        rw [← List.sum_ofFn]
        change (A.toList.map gamma).sum = (List.ofFn (gamma ∘ A.toList.get)).sum
        rw [← List.map_ofFn, List.ofFn_get]
      exact hsum.trans he
    have hpos : s + ∑ i, (A.toList.get i - l i) ≠ 0 := by omega
    have hh := nested_homogeneous (List.ofFn l)
      (letter (s + ∑ i, (A.toList.get i - l i)))
      (gamma (s + ∑ i, (A.toList.get i - l i)))
      (by simpa [letter] using homogeneous_basis (FreeMonoid.of (s + ∑ i, (A.toList.get i - l i))))
    simpa [List.map_ofFn, List.sum_ofFn, gamma, hs, hpos, hw, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hh

end D5.S1.Words.PostLie.AriWordOperations
