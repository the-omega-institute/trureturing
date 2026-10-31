/- GID: D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both full Ev averages of actual ordinary Specht traces transport to the existing HSW coefficient sums. -/

import D5.S3.Combinatorics.Partitions.SpechtHSWComparison
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2
import Mathlib.Tactic.FinCases

/-!
The ordinary character below is a trace of the independently constructed complex
polytabloid module. Its definition contains no Frobenius coefficient. Full cycle
partitions retain fixed points. Ev is the original occurrence list, including
repeated outcomes; attaching membership proofs does not deduplicate that list.
The rational reciprocal centralizer weight is cast to the complex numbers only
after its reciprocal is formed. The rectangular shape has no parity restriction.

These declarations supply the ordinary operands and their transport into both
coefficient averages. The binomial evaluation belongs to the existing weighted
coefficient supplier, not to the transport theorem.
Escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary

noncomputable section
open scoped BigOperators
open Equiv
open D5.S3.Combinatorics.Partitions.SpechtPolytabloid.TauCeti


/-- A representative of the full cycle partition, including all parts equal to one. -/
def cycleRepresentative {n : ℕ} (ρ : n.Partition) : Perm (Fin n) :=
  Classical.choose (partitionEquivConjClasses n ρ).exists_rep

private theorem cycleRepresentative_parts {n : ℕ} (ρ : n.Partition) :
    (cycleRepresentative ρ).partition.parts = ρ.parts := by
  have h := parts_partitionEquivConjClasses_symm_mk n (cycleRepresentative ρ)
  rw [show ConjClasses.mk (cycleRepresentative ρ) = partitionEquivConjClasses n ρ from
    Classical.choose_spec (partitionEquivConjClasses n ρ).exists_rep,
    Equiv.symm_apply_apply] at h
  exact h.symm

/-- The actual ordinary complex character of the same literal Specht partition. -/
def ordinaryCharacter {n : ℕ} (μ ρ : n.Partition) : ℂ :=
  LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ (cycleRepresentative ρ))

/-- The value is independent of the chosen representative of the full partition. -/
theorem ordinaryCharacter_eq_trace {n : ℕ} (μ ρ : n.Partition)
    (π : Perm (Fin n)) (hπ : π.partition.parts = ρ.parts) :
    ordinaryCharacter μ ρ = LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) := by
  obtain ⟨_, _, htrace⟩ := (spechtCharValue_ordinaryTrace μ ρ).2
  exact (htrace _ (cycleRepresentative_parts ρ)).trans (htrace π hπ).symm

/-- Every occurrence has positive parts and exactly twice the input size. -/
theorem evTypes_spec (l : List ℕ) :
    (∀ a ∈ l, 0 < a) → ∀ {τ : List ℕ}, τ ∈ HemmerStraubWestrem.evTypes l →
      τ.sum = 2 * l.sum ∧ ∀ a ∈ τ, 0 < a := by
  induction l with
  | nil =>
    intro hl τ hτ
    have hτ' : τ = [] := by simpa [HemmerStraubWestrem.evTypes] using hτ
    subst τ
    simp
  | cons a l ih =>
    intro hl τ hτ
    have ha : 0 < a := hl a (by simp)
    have hl' : ∀ b ∈ l, 0 < b := fun b hb => hl b (by simp [hb])
    simp only [HemmerStraubWestrem.evTypes, List.mem_append, List.mem_map] at hτ
    rcases hτ with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
    · obtain ⟨hsum, hpos⟩ := ih hl' hσ
      refine ⟨by simp only [List.sum_cons]; omega, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · exact hpos b hb
    · obtain ⟨hsum, hpos⟩ := ih hl' hσ
      refine ⟨by simp only [List.sum_cons]; omega, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hpos b hb

/-- The full positive cycle partition associated with a particular Ev occurrence. -/
def evPartition {n : ℕ} (lam : n.Partition)
    (τ : {τ : List ℕ // τ ∈ HemmerStraubWestrem.evTypes lam.parts.toList}) : (2 * n).Partition where
  parts := (τ.val : Multiset ℕ)
  parts_pos := by
    intro a ha
    exact (evTypes_spec lam.parts.toList
      (fun b hb => lam.parts_pos (by simpa using hb)) τ.property).2 a (by simpa using ha)
  parts_sum := by
    have h := (evTypes_spec lam.parts.toList
      (fun b hb => lam.parts_pos (by simpa using hb)) τ.property).1
    simpa [lam.parts_sum] using h

private theorem r3_antitone {m : ℕ} {a : Fin 3 → ℕ} (ha : a ∈ HemmerStraubWestrem.R3 m) :
    Antitone a := by
  have h := (Finset.mem_filter.mp ha).2
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

private theorem r3_sum {m : ℕ} {a : Fin 3 → ℕ} (ha : a ∈ HemmerStraubWestrem.R3 m) :
    ∑ i, a i = m :=
  Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp ha).1

private theorem rectangle_antitone (n : ℕ) : Antitone (![n, n, 0] : Fin 3 → ℕ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

private theorem rectangle_sum (n : ℕ) : ∑ i : Fin 3, (![n, n, 0] : Fin 3 → ℕ) i = 2 * n := by
  simp [Fin.sum_univ_three, two_mul]

/-- The signed even-shape Ev sum of ordinary traces for one input partition. -/
def leftTerm {n : ℕ} (lam : n.Partition) : ℂ :=
  ((HemmerStraubWestrem.evTypes lam.parts.toList).attach.map fun τ =>
    ∑ a ∈ (HemmerStraubWestrem.R3 (2 * n)).attach, (-1 : ℂ) ^ τ.val.length *
      ordinaryCharacter (triplePartition a.val (r3_antitone a.property) (r3_sum a.property))
        (evPartition lam τ)).sum

/-- The rectangular Ev sum of ordinary traces for one input partition, for every n. -/
def rightTerm {n : ℕ} (lam : n.Partition) : ℂ :=
  ((HemmerStraubWestrem.evTypes lam.parts.toList).attach.map fun τ =>
    ordinaryCharacter (triplePartition ![n, n, 0] (rectangle_antitone n) (rectangle_sum n))
      (evPartition lam τ)).sum

private theorem ordinaryCharacter_triple_eq_coefficient {n : ℕ}
    (a : Fin 3 → ℕ) (ha : Antitone a) (hsum : ∑ i, a i = n)
    (ρ : n.Partition) {τ : List ℕ} (hτ : (τ : Multiset ℕ) = ρ.parts) :
    ordinaryCharacter (triplePartition a ha hsum) ρ = (HemmerStraubWestrem.frobChar a τ : ℂ) := by
  obtain ⟨π, hπ, _⟩ := (spechtCharValue_ordinaryTrace (triplePartition a ha hsum) ρ).2
  rw [ordinaryCharacter_eq_trace _ _ π hπ]
  exact spechtTrace_triplePartition_eq_hsw_frobChar a ha hsum ρ π hπ hτ

/-- Both signs and every even shape are transported; no Ev occurrence is removed. -/
theorem leftTerm_eq_frobenius {n : ℕ} (lam : n.Partition) :
    leftTerm lam =
      ((((HemmerStraubWestrem.evTypes lam.parts.toList).map fun τ =>
        ∑ a ∈ HemmerStraubWestrem.R3 (2 * n), (-1 : ℤ) ^ τ.length * HemmerStraubWestrem.frobChar a τ).sum : ℤ) : ℂ) := by
  classical
  unfold leftTerm
  have hterm (τ : {τ : List ℕ // τ ∈ HemmerStraubWestrem.evTypes lam.parts.toList}) :
      (∑ a ∈ (HemmerStraubWestrem.R3 (2 * n)).attach, (-1 : ℂ) ^ τ.val.length *
        ordinaryCharacter (triplePartition a.val (r3_antitone a.property) (r3_sum a.property))
          (evPartition lam τ)) =
      ((∑ a ∈ HemmerStraubWestrem.R3 (2 * n), (-1 : ℤ) ^ τ.val.length * HemmerStraubWestrem.frobChar a τ.val : ℤ) : ℂ) := by
    simp_rw [ordinaryCharacter_triple_eq_coefficient _ _ _ _ (τ := τ.val) rfl]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    exact Finset.sum_attach _ _
  simp_rw [hterm]
  rw [List.attach_map_val]
  exact (map_list_sum (Int.castAddHom ℂ) _).symm

/-- The same literal rectangle is used in odd and even degree. -/
theorem rightTerm_eq_frobenius {n : ℕ} (lam : n.Partition) :
    rightTerm lam =
      ((((HemmerStraubWestrem.evTypes lam.parts.toList).map fun τ => HemmerStraubWestrem.frobChar ![n, n, 0] τ).sum : ℤ) : ℂ) := by
  unfold rightTerm
  have hterm (τ : {τ : List ℕ // τ ∈ HemmerStraubWestrem.evTypes lam.parts.toList}) :
      ordinaryCharacter (triplePartition ![n, n, 0] (rectangle_antitone n) (rectangle_sum n))
        (evPartition lam τ) = (HemmerStraubWestrem.frobChar ![n, n, 0] τ.val : ℂ) :=
    ordinaryCharacter_triple_eq_coefficient _ _ _ _ (τ := τ.val) rfl
  simp_rw [hterm]
  rw [List.attach_map_val]
  exact (map_list_sum (Int.castAddHom ℂ) _).symm

/-- The first equality of the original weighted statement holds already for each input
partition, with actual ordinary characters on both sides. -/
theorem pointwise_identity (n : ℕ) (hn : 1 ≤ n) (lam : n.Partition) :
    leftTerm lam = rightTerm lam := by
  rw [leftTerm_eq_frobenius, rightTerm_eq_frobenius, HemmerStraubWestrem.result n hn lam]

/-- The signed even-shape average with the exact rational reciprocal z weight. -/
def leftAverage (n : ℕ) : ℂ :=
  ∑ lam : n.Partition, ((_root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ : ℂ) * leftTerm lam

/-- The rectangular average with the same rational reciprocal z weight. -/
def rightAverage (n : ℕ) : ℂ :=
  ∑ lam : n.Partition, ((_root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ : ℂ) * rightTerm lam

/-- Exact integer-to-rational-to-complex transport of BOTH original averages. -/
theorem averages_eq_frobenius (n : ℕ) :
    leftAverage n =
      ((∑ lam : n.Partition, (_root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ *
        ((((HemmerStraubWestrem.evTypes lam.parts.toList).map fun τ =>
          ∑ a ∈ HemmerStraubWestrem.R3 (2 * n), (-1 : ℤ) ^ τ.length * HemmerStraubWestrem.frobChar a τ).sum : ℤ) : ℚ)) : ℂ) ∧
    rightAverage n =
      ((∑ lam : n.Partition, (_root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ *
        ((((HemmerStraubWestrem.evTypes lam.parts.toList).map fun τ => HemmerStraubWestrem.frobChar ![n, n, 0] τ).sum : ℤ) : ℚ)) : ℂ) := by
  classical
  constructor
  · unfold leftAverage
    push_cast
    apply Finset.sum_congr rfl
    intro lam _
    rw [leftTerm_eq_frobenius]
  · unfold rightAverage
    push_cast
    apply Finset.sum_congr rfl
    intro lam _
    rw [rightTerm_eq_frobenius]

/-- The two ORIGINAL ordinary-character averages agree for every positive n. -/
theorem weighted_identity (n : ℕ) (hn : 1 ≤ n) : leftAverage n = rightAverage n := by
  classical
  unfold leftAverage rightAverage
  apply Finset.sum_congr rfl
  intro lam _
  rw [pointwise_identity n hn lam]

end
end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
