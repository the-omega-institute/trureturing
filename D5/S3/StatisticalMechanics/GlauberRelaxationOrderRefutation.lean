/- GID: D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.claim; result=D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.result; claim=D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.claim
   digest: A four-state Glauber annealing run refutes relaxation-time rate order. -/

import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Multiset.Sort
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation

open scoped BigOperators

/-! Glauber transitions use the Gibbs ratio in Eq. (32) of arXiv:2311.10424v1.
The partial-swap side of (50) is eliminated using Proposition 2: its rate m has
spectral gap m. The gap comparison avoids interpreting a zero denominator as a
finite relaxation time. Characteristic roots retain algebraic multiplicity. -/

def probability {N : ℕ} (p : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

def regularNeighborhood {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A] : Prop :=
  1 ≤ n ∧
  (∀ i j, A i j → A j i) ∧
  (∀ i, ¬ A i i) ∧
  (∀ j, (Finset.univ.filter (fun i => A i j)).card = n)

noncomputable def gibbs {N : ℕ}
    (E : Fin N → ℝ) (b : ℝ) : Fin N → ℝ :=
  fun i =>
    Real.exp (-b * E i) /
      ∑ j, Real.exp (-b * E j)

noncomputable def edgeWeight {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (b : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if A i j then
      gibbs E b i /
        ((n : ℝ) * (gibbs E b i + gibbs E b j))
    else
      0

noncomputable def glauber {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (b : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if i = j then
      1 - ∑ l, edgeWeight n A E b l j
    else
      edgeWeight n A E b i j

def isSARun {N : ℕ} (n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (β : ℕ → ℝ)
    (p : ℕ → Fin N → ℝ) : Prop :=
  (∀ t, probability (p t)) ∧
  p 0 = gibbs E (β 0) ∧
  (∀ t,
    p (t + 1) =
      (glauber n A E (β (t + 1))).mulVec (p t))

noncomputable def meanEnergy {N : ℕ}
    (E p : Fin N → ℝ) : ℝ :=
  ∑ i, E i * p i

noncomputable def energyRate {N : ℕ}
    (E : Fin N → ℝ) (β : ℕ → ℝ)
    (p : ℕ → Fin N → ℝ) (k : ℕ) : ℝ :=
  (meanEnergy E (p (k + 1)) - meanEnergy E (p k)) /
    (meanEnergy E (gibbs E (β (k + 1))) -
      meanEnergy E (p k))

noncomputable def lambda2 {N : ℕ}
    (P : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ((Matrix.charpoly P).roots.sort
    (fun x y : ℝ => y ≤ x)).getD 1 0

def claim : Prop :=
  ∀ (N n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ)
    (β : ℕ → ℝ)
    (p : ℕ → Fin N → ℝ)
    (k : ℕ) (m : ℝ),
    2 ≤ N →
    regularNeighborhood n A →
    (∀ t, 0 < β t) →
    StrictMono β →
    isSARun n A E β p →
    (glauber n A E (β (k + 1))).charpoly.Splits →
    0 < m →
    m ≤ 1 →
    meanEnergy E (p (k + 1)) ≤ meanEnergy E (p k) →
    meanEnergy E (gibbs E (β k)) ≤ meanEnergy E (p k) →
    meanEnergy E (gibbs E (β (k + 1))) ≤
      meanEnergy E (gibbs E (β k)) →
    meanEnergy E (gibbs E (β (k + 1))) ≠
      meanEnergy E (p k) →
    m ≤ 1 - lambda2 (glauber n A E (β (k + 1))) →
    m ≤ energyRate E β p k

private def adj4 (i j : Fin 4) : Prop :=
  (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val

private instance adj4Decidable : DecidableRel adj4 :=
  fun i j =>
    show Decidable
      ((i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val) from inferInstance

private noncomputable def E4 : Fin 4 → ℝ := ![0, 1, 1, 2]

private noncomputable def q4 (k : ℕ) : ℝ :=
  if k = 0 then 2 else (k : ℝ) + 31

private noncomputable def beta4 (k : ℕ) : ℝ := Real.log (q4 k)

private noncomputable def Pq (q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q / (2 * (q + 1)) + q^2 / (2 * (q^2 + 1)),
       q / (2 * (q + 1)), 0, q^2 / (2 * (q^2 + 1));
     1 / (2 * (q + 1)), 1 / 4 + 1 / (2 * (q + 1)), 1 / 4, 0;
     0, 1 / 4, 1 / 4 + q / (2 * (q + 1)), q / (2 * (q + 1));
     1 / (2 * (q^2 + 1)), 0, 1 / (2 * (q + 1)),
       1 / (2 * (q + 1)) + 1 / (2 * (q^2 + 1))]

private noncomputable def run : ℕ → Fin 4 → ℝ :=
  Nat.rec (gibbs E4 (beta4 0))
    (fun k v => (glauber 2 adj4 E4 (beta4 (k + 1))).mulVec v)

private noncomputable def s : ℝ := Real.sqrt ((64 : ℝ) / 545)

private theorem adj4_regular : regularNeighborhood 2 adj4 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro i j h
    exact h.elim Or.inr Or.inl
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases j <;> decide

private theorem q4_spec : (∀ k, 1 < q4 k) ∧ StrictMono q4 := by
  constructor
  · intro k
    unfold q4
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  · intro i j hij
    have hj : j ≠ 0 := by omega
    by_cases hi : i = 0
    · subst i
      simp only [q4, ite_true, if_neg hj]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    · simp only [q4, if_neg hi, if_neg hj]
      have hc : (i : ℝ) < j := Nat.cast_lt.mpr hij
      linarith

private theorem beta4_spec : (∀ k, 0 < beta4 k) ∧ StrictMono beta4 := by
  refine ⟨fun k => Real.log_pos (q4_spec.1 k), ?_⟩
  intro i j hij
  exact Real.log_lt_log (lt_trans zero_lt_one (q4_spec.1 i)) (q4_spec.2 hij)

private theorem weights_log (q : ℝ) (hq : 0 < q) :
    (fun i : Fin 4 => Real.exp (-Real.log q * E4 i)) =
      ![1, q⁻¹, q⁻¹, (q⁻¹)^2] := by
  have h1 : Real.exp (-Real.log q) = q⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hq]
  have h2 : Real.exp (-Real.log q * 2) = (q⁻¹)^2 := by
    rw [mul_two, Real.exp_add, h1, pow_two]
  funext i
  fin_cases i <;> dsimp [E4]
  · simp
  · simpa only [mul_one] using h1
  · simpa only [mul_one] using h1
  · exact h2

private theorem gibbs_log (q : ℝ) (hq : 0 < q) :
    gibbs E4 (Real.log q) =
      ![q^2 / (q + 1)^2, q / (q + 1)^2, q / (q + 1)^2, 1 / (q + 1)^2] := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hq1 : q + 1 ≠ 0 := by positivity
  have hw := weights_log q hq
  change (fun i => (fun j : Fin 4 => Real.exp (-Real.log q * E4 j)) i /
    ∑ j, (fun l : Fin 4 => Real.exp (-Real.log q * E4 l)) j) = _
  rw [hw]
  funext i
  fin_cases i <;> simp [Fin.sum_univ_succ] <;> field_simp <;> ring

end D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
