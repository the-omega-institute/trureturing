/- GID: D5/S3/Quantum/Entanglement/TriangleEJMGramInterface
   generality: I
   mirror-B: none(waiver:interface-module)
   mirror-E: none(waiver:interface-module)
   anchors: [D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation]
   utility: kind=finite-exact-interface
   digest: Exact EJM tetrahedral Gram probabilities and an eight-term independent-source noise map. -/

/-
This file formalizes only finite rational identities. It does not assert that
the EJM table is triangle-local, and it does not contain an inflation
certificate. The imported IsTriangleLocal predicate is the existing
classical anchor for later soundness theorems.
-/

import D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation
import D5.S3.Arith.Congruence.ConditionalComparison.FiniteProbability
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.TriangleEJMGramInterface

abbrev Outcome := Fin 4

/-- A three-party finite output table with exact rational entries. -/
abbrev Table := Outcome → Outcome → Outcome → ℚ

/-- The regular-tetrahedron Gram entry: one on the diagonal and minus one third
off the diagonal. -/
def tetrahedralGram (i j : Outcome) : ℚ :=
  if i = j then 1 else -(1 / 3)

/-- The pairwise Gram sum appearing in the EJM expression. -/
def pairGramSum (a b c : Outcome) : ℚ :=
  tetrahedralGram a b + tetrahedralGram b c + tetrahedralGram c a

/-- The symmetric cycle-sensitive quadratic Gram invariant. -/
def cycleGramTerm (a b c : Outcome) : ℚ :=
  tetrahedralGram a b * tetrahedralGram b c +
    tetrahedralGram b c * tetrahedralGram c a +
    tetrahedralGram c a * tetrahedralGram a b

/-- Exact EJM probability in the tetrahedral Gram coordinates. -/
def ejmGramProbability (a b c : Outcome) : ℚ :=
  (4 + pairGramSum a b c + 6 * cycleGramTerm a b c) / 256

theorem ejmGramProbability_formula (a b c : Outcome) :
    ejmGramProbability a b c =
      (4 + (tetrahedralGram a b + tetrahedralGram b c + tetrahedralGram c a) +
        6 * (tetrahedralGram a b * tetrahedralGram b c +
          tetrahedralGram b c * tetrahedralGram c a +
          tetrahedralGram c a * tetrahedralGram a b)) / 256 := by
  rfl

/-- The three exact EJM output classes. This is the finite table obtained by
substituting the regular-tetrahedron Gram entries. -/
theorem ejmGramProbability_table (a b c : Outcome) :
    ejmGramProbability a b c =
      if a = b ∧ b = c then 25 / 256
      else if a = b ∨ b = c ∨ a = c then 1 / 256
      else 5 / 256 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [ejmGramProbability, pairGramSum, cycleGramTerm, tetrahedralGram]

theorem ejmGramProbability_nonnegative (a b c : Outcome) :
    0 ≤ ejmGramProbability a b c := by
  rw [ejmGramProbability_table]
  split_ifs <;> norm_num

/-- The 64 entries form a normalized finite probability table. -/
theorem ejmGramProbability_mass :
    ∑ a : Outcome, ∑ b : Outcome, ∑ c : Outcome, ejmGramProbability a b c = 1 := by
  simp only [Fin.sum_univ_four]
  norm_num [ejmGramProbability, pairGramSum, cycleGramTerm, tetrahedralGram]

/-- The exact EJM table as an instance of the repository's finite rational
probability carrier. -/
def ejmFiniteLaw : Erdos7.FiniteLaw (Outcome × Outcome × Outcome) where
  weight t := ejmGramProbability t.1 t.2.1 t.2.2
  weight_nonneg t := ejmGramProbability_nonnegative t.1 t.2.1 t.2.2
  weight_sum := by
    change ∑ t : Outcome × Outcome × Outcome,
      ejmGramProbability t.1 t.2.1 t.2.2 = 1
    simpa only [Fintype.sum_prod_type] using ejmGramProbability_mass

/-- The eight coefficients of independent source visibilities. The index is
the binary ideal/noisy choice for the three edges, in the order
alpha beta gamma = 000,100,010,110,001,101,011,111. -/
def sourceNoiseWeight (wα wβ wγ : ℚ) (i : Fin 8) : ℚ :=
  if i = 0 then (1 - wα) * (1 - wβ) * (1 - wγ)
  else if i = 1 then wα * (1 - wβ) * (1 - wγ)
  else if i = 2 then (1 - wα) * wβ * (1 - wγ)
  else if i = 3 then wα * wβ * (1 - wγ)
  else if i = 4 then (1 - wα) * (1 - wβ) * wγ
  else if i = 5 then wα * (1 - wβ) * wγ
  else if i = 6 then (1 - wα) * wβ * wγ
  else wα * wβ * wγ

/-- The exact finite independent-source noise map. P i is the component
table with ideal/noisy source choice i. -/
def independentSourceNoise (wα wβ wγ : ℚ) (P : Fin 8 → Table) : Table :=
  fun a b c => ∑ i : Fin 8, sourceNoiseWeight wα wβ wγ i * P i a b c

theorem sourceNoiseWeight_mass (wα wβ wγ : ℚ) :
    ∑ i : Fin 8, sourceNoiseWeight wα wβ wγ i = 1 := by
  norm_num [sourceNoiseWeight, Fin.sum_univ_succ]
  ring

/-- The source-product noise map is the explicit eight-term multi-affine
polynomial from the theory supplement. -/
theorem independentSourceNoise_eight_terms
    (wα wβ wγ : ℚ) (P : Fin 8 → Table) (a b c : Outcome) :
    independentSourceNoise wα wβ wγ P a b c =
      (1 - wα) * (1 - wβ) * (1 - wγ) * P 0 a b c +
      wα * (1 - wβ) * (1 - wγ) * P 1 a b c +
      (1 - wα) * wβ * (1 - wγ) * P 2 a b c +
      wα * wβ * (1 - wγ) * P 3 a b c +
      (1 - wα) * (1 - wβ) * wγ * P 4 a b c +
      wα * (1 - wβ) * wγ * P 5 a b c +
      (1 - wα) * wβ * wγ * P 6 a b c +
      wα * wβ * wγ * P 7 a b c := by
  unfold independentSourceNoise
  norm_num [sourceNoiseWeight, Fin.sum_univ_succ]

/-- The independent-source map is affine in each edge visibility. This is a
polynomial identity, not a locality or nonlocality statement. -/
theorem independentSourceNoise_affine_alpha
    (wα wβ wγ : ℚ) (P : Fin 8 → Table) (a b c : Outcome) :
    independentSourceNoise wα wβ wγ P a b c =
      (1 - wα) * independentSourceNoise 0 wβ wγ P a b c +
        wα * independentSourceNoise 1 wβ wγ P a b c := by
  rw [independentSourceNoise_eight_terms,
    independentSourceNoise_eight_terms,
    independentSourceNoise_eight_terms]
  ring

end D5.S3.Quantum.Entanglement.TriangleEJMGramInterface
