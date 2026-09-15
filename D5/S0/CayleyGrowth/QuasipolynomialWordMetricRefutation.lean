/- GID: D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation
   generality: G
   mirror-B: D5/B/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The word metric of a closed-form transposition family is not eventually quasipolynomial. -/

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Linarith

/-!
The square indicator cannot eventually be quasipolynomial, even without a degree bound.
In residue zero modulo a proposed period, squares and nearby nonsquares give two infinite
sets of roots forcing the same constituent polynomial to be both one and zero.

For the symmetric group on `Fin n`, use all transpositions and mark `(0 1)` precisely
when `n ≥ 2` is square. The resulting word distance refutes Conjecture 2 of Chervov et al.,
"CayleyPy Growth", arXiv:2509.19162v2. Polynomial-time constructibility is outside this
formal statement; the square test and the marked permutation are given by explicit definitions.
-/

namespace CayleyGrowth

/-- Eventual agreement with one rational polynomial per residue class, with no degree bound. -/
def IsEventuallyQuasipolynomial (f : ℕ → ℚ) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∃ P : ℕ → Polynomial ℚ, ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → f n = (P (n % p)).eval (n : ℚ)

/-- Any function eventually equal to the square indicator fails eventual quasipolynomiality. -/
theorem not_eventuallyQuasipolynomial_of_eventually_squareIndicator
    (f : ℕ → ℚ) (M : ℕ)
    (hsq : ∀ n, M ≤ n → IsSquare n → f n = 1)
    (hns : ∀ n, M ≤ n → ¬ IsSquare n → f n = 0) :
    ¬ IsEventuallyQuasipolynomial f := by
  rintro ⟨p, hp, P, N, hP⟩
  -- Shifting the index clears both thresholds without removing a finite initial segment.
  let b (t : ℕ) := p * (t + M + N + 1)
  let u (t : ℕ) := (b t) ^ 2
  let v (t : ℕ) := u t + p
  have hb (t : ℕ) : M + N + 1 ≤ b t := by
    have h := Nat.le_mul_of_pos_left (t + M + N + 1) hp
    dsimp only [b]
    omega
  have hu_bounds (t : ℕ) : M ≤ u t ∧ N ≤ u t := by
    have h := hb t
    have hbu : b t ≤ u t := by
      simpa only [u, pow_two] using
        Nat.le_mul_of_pos_left (b t) (by omega : 0 < b t)
    omega
  have hu_mod (t : ℕ) : u t % p = 0 := by
    simp [u, b, Nat.pow_mod]
  have hv_mod (t : ℕ) : v t % p = 0 := by
    simpa only [v, Nat.add_mod_right] using hu_mod t
  have hu_inj : Function.Injective u := by
    intro s t h
    have hbst : b s = b t :=
      Nat.mul_self_inj.mp (by simpa only [u, pow_two] using h)
    have hst := Nat.eq_of_mul_eq_mul_left hp hbst
    omega
  -- The second subsequence lies strictly between successive squares.
  have hbetween (t : ℕ) : (b t) ^ 2 < v t ∧ v t < (b t + 1) ^ 2 := by
    have hpb : p ≤ b t := by
      have h := Nat.le_mul_of_pos_left p (by omega : 0 < t + M + N + 1)
      simpa only [b, Nat.mul_comm] using h
    dsimp only [v, u]
    constructor <;> nlinarith
  have hv_nonsquare (t : ℕ) : ¬ IsSquare (v t) := by
    rintro ⟨r, hr⟩
    have hlo : b t < r := Nat.mul_self_lt_mul_self_iff.mp (by
      simpa only [pow_two, hr] using (hbetween t).1)
    have hhi : r < b t + 1 := Nat.mul_self_lt_mul_self_iff.mp (by
      simpa only [pow_two, hr] using (hbetween t).2)
    omega
  have hQ_one : P 0 - 1 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem
      (f := fun t : ℕ => (u t : ℚ)) ?_ ?_
    · intro s t h
      exact hu_inj (Nat.cast_injective h)
    · intro t
      change (P 0 - 1).eval (u t : ℚ) = 0
      have h := hP (u t) (hu_bounds t).2
      rw [hu_mod t] at h
      have hsquare : IsSquare (u t) := ⟨b t, by simp only [u, pow_two]⟩
      rw [Polynomial.eval_sub, Polynomial.eval_one, ← h,
        hsq (u t) (hu_bounds t).1 hsquare, sub_self]
  have hQ_zero : P 0 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem
      (f := fun t : ℕ => (v t : ℚ)) ?_ ?_
    · intro s t h
      have hnat : v s = v t := Nat.cast_injective h
      apply hu_inj
      dsimp only [v] at hnat
      omega
    · intro t
      have hbnd := hu_bounds t
      have hM : M ≤ v t := by dsimp only [v]; omega
      have hN : N ≤ v t := by dsimp only [v]; omega
      change (P 0).eval (v t : ℚ) = 0
      have h := hP (v t) hN
      rw [hv_mod t] at h
      exact h.symm.trans (hns (v t) hM (hv_nonsquare t))
  have hQ : P 0 = 1 := sub_eq_zero.mp hQ_one
  exact one_ne_zero (hQ.symm.trans hQ_zero)

/-- The generating set consisting of every transposition of `Fin n`. -/
def allTranspositions (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {σ | σ.IsSwap}

/-- The transposition of indices zero and one at square sizes at least two; identity otherwise. -/
def squareMarkedElement (n : ℕ) : Equiv.Perm (Fin n) :=
  if h : 2 ≤ n ∧ IsSquare n then
    Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  else 1

/-- Distance from identity to the marked element in the all-transpositions Cayley graph. -/
noncomputable def squareMarkedWordDistance (n : ℕ) : ℚ :=
  ((SimpleGraph.mulCayley (allTranspositions n)).dist 1 (squareMarkedElement n) : ℚ)

/-- Counterexample to Conjecture 2 of Chervov et al., "CayleyPy Growth", arXiv:2509.19162v2.
The conjecture asserts that for any polynomial-time constructible generators of `S n` together
with marked elements `g n`, the distance from the identity to `g n` is eventually a quadratic or
linear quasipolynomial in `n`. Here the generators are all transpositions and the marked element
is `(0 1)` exactly at square sizes, so the distance is the indicator of the squares, which is not
eventually quasipolynomial of any degree. -/
theorem cayleyPy_conjecture2_refuted :
    ¬ IsEventuallyQuasipolynomial squareMarkedWordDistance := by
  apply not_eventuallyQuasipolynomial_of_eventually_squareIndicator squareMarkedWordDistance 2
  · intro n hn hsq
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hval := congrArg Fin.val h
      change (0 : ℕ) = 1 at hval
      omega
    have hcond : 2 ≤ n ∧ IsSquare n := ⟨hn, hsq⟩
    have hmark : squareMarkedElement n = Equiv.swap a b := by
      simp only [squareMarkedElement, dif_pos hcond, a, b]
    have hne : (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap a b := by
      intro h
      apply hab
      have happ := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) h
      simpa only [Equiv.Perm.one_apply, Equiv.swap_apply_left] using happ
    have hadj : (SimpleGraph.mulCayley (allTranspositions n)).Adj 1 (Equiv.swap a b) := by
      apply (SimpleGraph.mulCayley_adj (allTranspositions n) 1 (Equiv.swap a b)).mpr
      refine ⟨hne, Or.inl ?_⟩
      simpa only [inv_one, one_mul, allTranspositions, Set.mem_ofPred_eq] using
        (show (Equiv.swap a b).IsSwap from ⟨a, b, hab, rfl⟩)
    have hdist := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    simp only [squareMarkedWordDistance, hmark, hdist, Nat.cast_one]
  · intro n _ hns
    have hcond : ¬ (2 ≤ n ∧ IsSquare n) := fun h => hns h.2
    have hmark : squareMarkedElement n = 1 := by
      simp only [squareMarkedElement, dif_neg hcond]
    simp only [squareMarkedWordDistance, hmark, SimpleGraph.dist_self, Nat.cast_zero]

end CayleyGrowth
