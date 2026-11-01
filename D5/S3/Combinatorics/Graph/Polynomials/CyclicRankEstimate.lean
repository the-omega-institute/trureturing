import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-! GID: D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff,
     mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: The signed rank-state coefficient splits into forest and cyclic states,
     and the cyclic count controls the coefficient error uniformly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate

open scoped BigOperators Polynomial

/-! The exponent is defined from the actual integer rank/nullity expression and
    is converted to `Nat` only under an explicit nonnegativity proof. -/

def stateExponentInteger (v : ℕ) (q : ℕ) (s : ℕ) : ℤ :=
  (v : ℤ) - 1 + (s : ℤ) - 2 * (q : ℤ)

def stateExponent (v : ℕ) (q : ℕ) (s : ℕ)
    (h : 0 ≤ stateExponentInteger v q s) : ℕ :=
  (stateExponentInteger v q s).toNat

theorem stateExponent_cast_eq_integer {v q s : ℕ}
    (h : 0 ≤ stateExponentInteger v q s) :
    (stateExponent v q s h : ℤ) = stateExponentInteger v q s := by
  unfold stateExponent
  exact Int.toNat_of_nonneg h

def stateTerm {E : Type*} [DecidableEq E]
    (v : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (S : Finset E) : ℤ[X] :=
  Polynomial.C ((-1 : ℤ) ^ S.card) * Polynomial.X ^ q S *
    (1 + Polynomial.X) ^ stateExponent v (q S) S.card (hExp S)

def statePolynomial {E : Type*} [Fintype E] [DecidableEq E]
    (v : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) : ℤ[X] :=
  ∑ S : Finset E, stateTerm v q hExp S

def forestStates {E : Type*} [Fintype E] [DecidableEq E]
    (q : Finset E → ℕ) : Finset (Finset E) :=
  Finset.univ.filter (fun S => q S = S.card)

def cyclicStates {E : Type*} [Fintype E] [DecidableEq E]
    (q : Finset E → ℕ) : Finset (Finset E) :=
  Finset.univ.filter (fun S => q S < S.card)

def termCoefficient {E : Type*} [DecidableEq E]
    (v k : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (S : Finset E) : ℤ :=
  if q S ≤ k then
    (-1 : ℤ) ^ S.card *
      (stateExponent v (q S) S.card (hExp S)).choose (k - q S)
  else 0

def idealCoefficient (b k : ℕ) : ℤ :=
  Ring.choose (-(b : ℤ)) k

theorem idealCoefficient_formula (b k : ℕ) :
    idealCoefficient b k = (-1 : ℤ) ^ k * (b + k - 1).choose k := by
  by_cases hzero : b = 0 ∧ k = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [idealCoefficient]
  · unfold idealCoefficient
    rw [Ring.choose_neg]
    have h : 1 ≤ b + k := by
      by_contra hnot
      have : b + k = 0 := by omega
      have hb : b = 0 := by omega
      have hk : k = 0 := by omega
      exact hzero ⟨hb, hk⟩
    rw [show (↑b + ↑k - 1 : ℤ) = ((b + k - 1 : ℕ) : ℤ) by
      norm_num [Nat.cast_sub h]]
    rw [Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.coe_negOnePow_natCast,
      Int.cast_natCast]

theorem coeff_stateTerm {E : Type*} [DecidableEq E]
    {v k : ℕ} {q : Finset E → ℕ}
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (S : Finset E) :
    (stateTerm v q hExp S).coeff k = termCoefficient v k q hExp S := by
  unfold stateTerm termCoefficient
  by_cases hq : q S ≤ k
  · simp only [hq, ↓reduceIte]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    rw [Polynomial.coeff_one_add_X_pow]
    simp [hq]
  · simp only [hq, ↓reduceIte]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    simp [hq]

theorem coeff_statePolynomial {E : Type*} [Fintype E] [DecidableEq E]
    {v k : ℕ} {q : Finset E → ℕ}
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) :
    (statePolynomial v q hExp).coeff k =
      ∑ S : Finset E, termCoefficient v k q hExp S := by
  unfold statePolynomial
  rw [Polynomial.finsetSum_coeff]
  simp_rw [coeff_stateTerm hExp]

def forestCoefficient {E : Type*} [Fintype E] [DecidableEq E]
    (v k : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) : ℤ :=
  Finset.sum (forestStates q) (fun S => termCoefficient v k q hExp S)

def cyclicCoefficient {E : Type*} [Fintype E] [DecidableEq E]
    (v k : ℕ) (q : Finset E → ℕ)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) : ℤ :=
  Finset.sum (cyclicStates q) (fun S => termCoefficient v k q hExp S)

theorem coeff_split {E : Type*} [Fintype E] [DecidableEq E]
    {v k : ℕ} {q : Finset E → ℕ}
    (hRank : ∀ S : Finset E, q S ≤ S.card)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card) :
    (statePolynomial v q hExp).coeff k =
      forestCoefficient v k q hExp + cyclicCoefficient v k q hExp := by
  rw [coeff_statePolynomial hExp]
  unfold forestCoefficient cyclicCoefficient forestStates cyclicStates
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset E))
    (fun S => q S = S.card)]
  have hcyc : Finset.filter (fun S : Finset E => ¬ q S = S.card) Finset.univ =
      cyclicStates q := by
    ext S
    simp only [cyclicStates, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hn
      exact (Nat.lt_or_eq_of_le (hRank S)).resolve_right hn
    · intro hlt heq
      omega
  rw [hcyc]
  congr 1

theorem natAbs_cyclicCoefficient_le {E : Type*} [Fintype E] [DecidableEq E]
    {v k : ℕ} {q : Finset E → ℕ} {B : ℕ}
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (hterm : ∀ S ∈ cyclicStates q, (termCoefficient v k q hExp S).natAbs ≤ B) :
    (cyclicCoefficient v k q hExp).natAbs ≤ (cyclicStates q).card * B := by
  unfold cyclicCoefficient
  calc
    (Finset.sum (cyclicStates q) (fun S => termCoefficient v k q hExp S)).natAbs ≤
        Finset.sum (cyclicStates q) (fun S => (termCoefficient v k q hExp S).natAbs) := by
      exact Int.natAbs_sum_le _ _
    _ ≤ Finset.sum (cyclicStates q) (fun _S => B) := by
      exact Finset.sum_le_sum (fun S hS => hterm S hS)
    _ = (cyclicStates q).card * B := by simp

theorem signed_tutte_coefficient_estimate
    {E : Type*} [Fintype E] [DecidableEq E]
    {v k b A B : ℕ} {q : Finset E → ℕ}
    (hRank : ∀ S : Finset E, q S ≤ S.card)
    (hExp : ∀ S : Finset E, 0 ≤ stateExponentInteger v (q S) S.card)
    (hForest : forestCoefficient v k q hExp = idealCoefficient b k)
    (hCount : (cyclicStates q).card ≤ A * (Fintype.card E + 1) ^ (k - 1))
    (hTerm : ∀ S ∈ cyclicStates q, (termCoefficient v k q hExp S).natAbs ≤ B) :
    ((statePolynomial v q hExp).coeff k - idealCoefficient b k).natAbs ≤
      A * B * (Fintype.card E + 1) ^ (k - 1) := by
  rw [coeff_split hRank hExp]
  have hdiff :
      forestCoefficient v k q hExp + cyclicCoefficient v k q hExp - idealCoefficient b k =
        cyclicCoefficient v k q hExp := by
    rw [hForest]
    abel
  rw [hdiff]
  have hcyc := natAbs_cyclicCoefficient_le hExp hTerm
  calc
    (cyclicCoefficient v k q hExp).natAbs ≤ (cyclicStates q).card * B := hcyc
    _ ≤ (A * (Fintype.card E + 1) ^ (k - 1)) * B :=
      Nat.mul_le_mul_right B hCount
    _ = A * B * (Fintype.card E + 1) ^ (k - 1) := by ac_rfl

/-! The graph wrapper uses the actual connected-component rank.  The
    coefficient theorem above is intentionally parameterized by the two rank
    inequalities; the graph-specific cyclic embedding/counting argument is
    the next layer and cannot be replaced by a polynomial alias. -/

def graphEdgePredicate {n : ℕ} (G : SimpleGraph (Fin n)) :
    Sym2 (Fin n) → Prop :=
  Sym2.lift ⟨fun u v => G.Adj u v, fun u v => propext (G.adj_comm u v)⟩

def graphEdge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  {e : Sym2 (Fin n) // graphEdgePredicate G e}

noncomputable def graphRank {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (graphEdge G)) : ℕ :=
  by
    classical
    let E := S.image (fun e : graphEdge G => e.1)
    exact n - Nat.card (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).ConnectedComponent

noncomputable def graphStatePolynomial {n : ℕ} (G : SimpleGraph (Fin n))
    (hExp : ∀ S : Finset (graphEdge G),
      0 ≤ stateExponentInteger n (graphRank G S) S.card) : ℤ[X] := by
  classical
  letI : Finite (graphEdge G) :=
    Finite.of_injective (fun e : graphEdge G => e.1) Subtype.val_injective
  letI : Fintype (graphEdge G) := Fintype.ofFinite _
  exact statePolynomial n (graphRank G) hExp

end D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate
