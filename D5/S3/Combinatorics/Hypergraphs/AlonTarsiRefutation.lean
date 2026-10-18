/- GID: D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.claim; result=D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.result; claim=D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.claim
   digest: A jointly admissible characteristic-three multihypergraph refutes Conjectures 4 and 28 of Alon-Tarsi for Hypergraphs. -/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
A counterexample to Conjectures 4 and 28 in Anholcer et al.,
"Alon-Tarsi for hypergraphs", arXiv:2501.00157v2.
The source permits multiple edges and arbitrary base fields.
-/

open MvPolynomial
namespace D5.S3.Combinatorics.Hypergraphs.AlonTarsiRefutation
noncomputable section

abbrev F := ZMod 3
abbrev P := MvPolynomial (Fin 3) F

def edge : Fin 3 → Finset (Fin 3) := fun _ => Finset.univ

def edgeCount {n m : ℕ} (H : Fin m → Finset (Fin n)) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun e => H e ⊆ S).card

/-- The source's maximum over nonempty vertex subsets, counting edge multiplicities. -/
def density {n m : ℕ} [NeZero n] (H : Fin m → Finset (Fin n)) : ℚ :=
  (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty).sup'
    (by refine ⟨Finset.univ, ?_⟩; simp) (fun S : Finset (Fin n) =>
    (edgeCount H S : ℚ) / (S.card : ℚ))

/-- The bound AT(p) ≤ k using exactly the source's maximum-total-degree convention. -/
def ATAtMost {K : Type*} [CommSemiring K] {n : ℕ} (p : MvPolynomial (Fin n) K) (k : ℕ) : Prop :=
  ∃ d : Fin n →₀ ℕ, p.coeff d ≠ 0 ∧ (d.sum fun _ e => e) = p.totalDegree ∧ ∀ i, d i < k

/-- Each index is an edge occurrence, so equal vertex sets retain multiplicity. -/
def edgePolynomial {K : Type*} [CommSemiring K] {n m : ℕ}
    (H : Fin m → Finset (Fin n)) (a : Fin m → Fin n → K) : MvPolynomial (Fin n) K :=
  ∏ e, ∑ v ∈ H e, C (a e v) * X v

/-- Conjecture 4, for arbitrary fields and occurrence-dependent incident coefficients. -/
def Conjecture4 : Prop :=
  ∀ (K : Type) [Field K] (n m : ℕ) [NeZero n]
    (H : Fin m → Finset (Fin n)) (a : Fin m → Fin n → K),
    (∀ e, 2 ≤ (H e).card) → (∀ e v, v ∈ H e → a e v ≠ 0) →
    ATAtMost (edgePolynomial H a) (2 * ⌈density H⌉₊ + 1)

/-- Conjecture 28 adds full unbalance to the same fixed-polynomial assertion. -/
def Conjecture28 : Prop :=
  ∀ (K : Type) [Field K] (n m : ℕ) [NeZero n]
    (H : Fin m → Finset (Fin n)) (a : Fin m → Fin n → K),
    (∀ e, 2 ≤ (H e).card) → (∀ e v, v ∈ H e → a e v ≠ 0) →
    (∀ e, ∃ u ∈ H e, ∃ v ∈ H e, a e u ≠ a e v) →
    ATAtMost (edgePolynomial H a) (2 * ⌈density H⌉₊ + 1)

/-- At least one of the two printed universal statements holds. -/
def claim : Prop := Conjecture4 ∨ Conjecture28

def coefficient (v : Fin 3) : F := if v = 2 then -1 else 1

def polynomial : P := (X 0 + X 1 - X 2)^3

theorem admissible_edges : ∀ e, 2 ≤ (edge e).card := by
  intro e
  norm_num [edge]

theorem density_one : density edge = 1 := by
  unfold density
  apply le_antisymm
  · exact Finset.sup'_le _ _ (by
      intro S _
      by_cases hS : S = Finset.univ
      · subst S
        norm_num [edgeCount, edge]
      · have hn : ¬ Finset.univ ⊆ S := by simpa using hS
        simp [edgeCount, edge, hn])
  · exact Finset.le_sup'_of_le _ (b := (Finset.univ : Finset (Fin 3)))
      (by simp) (by norm_num [edgeCount, edge])

theorem coefficients_nonzero : ∀ v, coefficient v ≠ 0 := by
  intro v
  fin_cases v <;> decide

theorem fully_unbalanced : ∀ e : Fin 3,
    ∃ u ∈ edge e, ∃ v ∈ edge e, coefficient u ≠ coefficient v := by
  intro e
  refine ⟨0, Finset.mem_univ _, 2, Finset.mem_univ _, ?_⟩
  decide

theorem polynomial_from_edges :
    polynomial = ∏ e : Fin 3, ∑ v ∈ edge e, (C (coefficient v) * X v : P) := by
  simp [polynomial, edge, coefficient, Fin.sum_univ_succ]
  ring

theorem frobenius_identity : polynomial = X 0 ^ 3 + X 1 ^ 3 - X 2 ^ 3 := by
  unfold polynomial
  rw [sub_pow_char, add_pow_char]

theorem small_coeff_zero (d : Fin 3 →₀ ℕ) (hd : ∀ i, d i ≤ 2) :
    polynomial.coeff d = 0 := by
  have h (i : Fin 3) : Finsupp.single i 3 ≠ d := by
    intro he
    have hi := hd i
    rw [← he, Finsupp.single_eq_same] at hi
    omega
  simp [frobenius_identity, coeff_X_pow, h]

theorem coefficient_three : polynomial.coeff (Finsupp.single 0 3) = 1 := by
  simp [frobenius_identity, coeff_X_pow, Finsupp.single_eq_single_iff]

theorem totalDegree_three : polynomial.totalDegree = 3 := by
  apply le_antisymm
  · rw [frobenius_identity]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      simp
    · simp
  · have hm : Finsupp.single (0 : Fin 3) 3 ∈ polynomial.support := by
      rw [mem_support_iff, coefficient_three]
      exact one_ne_zero
    simpa using (le_totalDegree hm)

theorem exact_AT_bound (k : ℕ) : ATAtMost polynomial k ↔ 4 ≤ k := by
  constructor
  · rintro ⟨d, hd, _, hb⟩
    by_contra hk
    have hs : ∀ i, d i ≤ 2 := by
      intro i
      have hi := hb i
      omega
    exact hd (small_coeff_zero d hs)
  · intro hk
    refine ⟨Finsupp.single 0 3, ?_, ?_, ?_⟩
    · rw [coefficient_three]
      exact one_ne_zero
    · simp [totalDegree_three]
    · intro i
      by_cases hi : i = 0
      · subst i
        simp only [Finsupp.single_eq_same]
        omega
      · simp [hi]
        omega

/-- One native certificate joins the exact polynomial with every source premise. -/
theorem source_counterexample :
    (∀ e, 2 ≤ (edge e).card) ∧
    (∀ v, coefficient v ≠ 0) ∧
    (∀ e : Fin 3, ∃ u ∈ edge e, ∃ v ∈ edge e, coefficient u ≠ coefficient v) ∧
    (polynomial = ∏ e : Fin 3, ∑ v ∈ edge e, (C (coefficient v) * X v : P)) ∧
    density edge = 1 ∧ polynomial.totalDegree = 3 ∧
    (∀ k, ATAtMost polynomial k ↔ 4 ≤ k) ∧
    ¬ ATAtMost polynomial (2 * (⌈density edge⌉₊) + 1) := by
  refine ⟨admissible_edges, coefficients_nonzero, fully_unbalanced, polynomial_from_edges,
    density_one, totalDegree_three, exact_AT_bound, ?_⟩
  rw [density_one]
  norm_num [exact_AT_bound]

/-- Both printed conjectures fail, using the same jointly admissible witness. -/
theorem result : ¬ claim := by
  obtain ⟨hsize, hnz, hunbalanced, hproduct, _, _, _, hfail⟩ := source_counterexample
  have hfail' : ¬ ATAtMost (edgePolynomial edge (fun _ => coefficient))
      (2 * ⌈density edge⌉₊ + 1) := by
    simpa only [edgePolynomial, ← hproduct] using hfail
  rintro (h4 | h28)
  · exact hfail' (h4 F 3 3 edge (fun _ => coefficient) hsize (fun _ v _ => hnz v))
  · exact hfail' (h28 F 3 3 edge (fun _ => coefficient) hsize
      (fun _ v _ => hnz v) hunbalanced)

end
end D5.S3.Combinatorics.Hypergraphs.AlonTarsiRefutation
