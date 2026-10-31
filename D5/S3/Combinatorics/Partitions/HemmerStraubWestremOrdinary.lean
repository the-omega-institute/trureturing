/- GID: D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both original ordinary Specht trace averages have the full HSW parity-dependent binomial value. -/

import D5.S3.Combinatorics.Partitions.SpechtHSWComparison
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
The ordinary character below is a trace of the independently constructed complex
polytabloid module. Its definition contains no Frobenius coefficient. Full cycle
partitions retain fixed points. Ev is the original occurrence list, including
repeated outcomes; attaching membership proofs does not deduplicate that list.
The rational reciprocal centralizer weight is cast to the complex numbers only
after its reciprocal is formed. The rectangular shape has no parity restriction.

The live weighted derivation below reuses the necessary proof components from
HemmerStraubWestremWeightedAverage at published revision
69f68474a0566d6f465a14259b74f28b58e293f3. It retains no standalone coefficient
owner, coefficient claim or final-application module. The rectangular suppliers
and centralizer formula are called at their existing owners; the formal ODE
step directly applies LatticeHalfFockChargedCoefficients.solution_unique over
the Laurent polynomial rational algebra, with its torsion-free premise supplied
by HasUniqueDiv.of_module_rat. No ODE uniqueness proof is duplicated.

All inherited and new ordinary/Specht sources are UNCOMPILED. Source composition
and source import closure do not establish elaboration, axiom closure or native
liveness. The external full-problem endpoint is the only unconsumed conclusion;
its individual section 3.2 basis is the original preregistration #21960,
open-problem-resolution, with conservative proof_shape: bind-only. Every other
bind-only theorem below is a consumed helper, not an independent result.
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

private def rightCoefficientAverage (n : ℕ) : ℚ :=
  ∑ lam : n.Partition,
    (_root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ *
      ((((HemmerStraubWestrem.evTypes lam.parts.toList).map fun τ =>
        HemmerStraubWestrem.frobChar ![n, n, 0] τ).sum : ℤ) : ℚ)

private theorem rightAverage_eq_frobenius (n : ℕ) :
    rightAverage n = (rightCoefficientAverage n : ℂ) := by
  classical
  unfold rightAverage rightCoefficientAverage
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
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
private theorem rectangular_sum_coefficient (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) :
    ((evTypes p.parts.toList).map fun τ => frobChar ![n, n, 0] τ).sum =
      (2 : ℤ) ^ p.parts.card *
        ((triProd p.parts.toList).coeff n - (triProd p.parts.toList).coeff (n + 1)) := by
  have hsum : p.parts.toList.sum = n := by simpa using p.parts_sum
  have hpos : ∀ a ∈ p.parts.toList, 0 < a := by
    intro a ha
    exact p.parts_pos (by simpa using ha)
  have h := right_coefficient p.parts.toList (by omega) hpos
  rw [← ev_right] at h
  simpa only [hsum, Multiset.length_toList] using h
end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

private theorem partition_exponent_count {n : ℕ} (p : Nat.Partition n)
    (k : ℕ) (hk : 0 < k) : partitionExponent p (k - 1) = p.parts.count k := by
  have h := congrArg (Multiset.count k) (exponentParts_partitionExponent p)
  rw [exponentParts, show k = Nat.succ (k - 1) by omega,
    Multiset.count_map_eq_count' Nat.succ _ Nat.succ_injective,
    Finsupp.count_toMultiset] at h
  simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using h

private theorem z_partition_cons {n m k : ℕ}
    (p : Nat.Partition n) (q : Nat.Partition m)
    (hk : 0 < k) (hp : p.parts = k ::ₘ q.parts) :
    zPartition p = k * (q.parts.count k + 1) * zPartition q := by
  have he : partitionExponent p = partitionExponent q + Finsupp.single (k - 1) 1 := by
    simp only [partitionExponent, hp, Multiset.map_cons]
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton]
    exact add_comm _ _
  rw [zPartition, he, zExponent_add_single, partition_exponent_count q k hk]
  congr 2
  omega

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private def cycleTerm (a : ℕ → R) {n : ℕ} (p : Nat.Partition n) : R :=
  (zPartition p : ℚ)⁻¹ • (p.parts.map a).prod

private def cycleAverage (a : ℕ → R) (n : ℕ) : R :=
  ∑ p : Nat.Partition n, cycleTerm a p

private theorem cycle_term_cons (a : ℕ → R) {n m k : ℕ}
    (p : Nat.Partition n) (q : Nat.Partition m)
    (hk : 0 < k) (hp : p.parts = k ::ₘ q.parts) :
    ((k : ℚ) * (q.parts.count k + 1)) • cycleTerm a p = a k * cycleTerm a q := by
  have hz : (zPartition q : ℚ) ≠ 0 := by
    exact_mod_cast (zExponent_pos (partitionExponent q)).ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hc : (q.parts.count k + 1 : ℚ) ≠ 0 := by positivity
  have hs : ((k : ℚ) * (q.parts.count k + 1)) * (zPartition p : ℚ)⁻¹ =
      (zPartition q : ℚ)⁻¹ := by
    rw [z_partition_cons p q hk hp]
    push_cast
    field_simp
  simp only [cycleTerm, hp, Multiset.map_cons, Multiset.prod_cons, smul_smul, hs]
  exact (mul_smul_comm _ _ _).symm


private theorem marked_cycle_sum (a : ℕ → R) (n k : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    (∑ p : Nat.Partition n, ((k : ℚ) * p.parts.count k) • cycleTerm a p) =
      a k * cycleAverage a (n - k) := by
  let e := Nat.Partition.partitionWithPartEquiv hk hkn
  calc
    _ = ∑ p : {p : Nat.Partition n // k ∈ p.parts},
        ((k : ℚ) * p.val.parts.count k) • cycleTerm a p.val := by
      apply Finset.sum_congr_set {p : Nat.Partition n | k ∈ p.parts}
      · intro p hp
        rfl
      · intro p hp
        simp [Multiset.count_eq_zero_of_notMem hp]
    _ = ∑ q : Nat.Partition (n - k), a k * cycleTerm a q := by
      apply Fintype.sum_equiv e
      intro p
      have hp : p.val.parts = k ::ₘ (e p).parts := by
        dsimp [e]
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
        exact (Multiset.cons_erase p.property).symm
      have hc : p.val.parts.count k = (e p).parts.count k + 1 := by
        rw [hp]
        simp
      rw [hc, Nat.cast_add, Nat.cast_one]
      exact cycle_term_cons a p.val (e p) hk hp
    _ = _ := by rw [cycleAverage, Finset.mul_sum]

private theorem cycle_average_recursion (a : ℕ → R) (n : ℕ) :
    (n : ℚ) • cycleAverage a n =
      ∑ k ∈ Finset.Icc 1 n, a k * cycleAverage a (n - k) := by
  have hdeg (p : Nat.Partition n) :
      (∑ k ∈ Finset.Icc 1 n, k * p.parts.count k) = n := by
    calc
      _ = ∑ k ∈ p.parts.toFinset, p.parts.count k * k := by
        symm
        calc
          _ = ∑ k ∈ p.parts.toFinset, k * p.parts.count k := by
            apply Finset.sum_congr rfl
            intro k _
            exact mul_comm _ _
          _ = _ := by
            apply Finset.sum_subset
            · intro k hk
              have hk' := Multiset.mem_toFinset.mp hk
              exact Finset.mem_Icc.mpr ⟨p.parts_pos hk', p.le_of_mem_parts hk'⟩
            · intro k hk hnot
              simp [Multiset.count_eq_zero_of_notMem (by simpa using hnot)]
      _ = n := by
        simpa only [nsmul_eq_mul, id_eq, Multiset.map_id, Multiset.map_id', Nat.cast_id,
          p.parts_sum] using
          (Finset.sum_multiset_map_count p.parts id).symm
  calc
    _ = ∑ p : Nat.Partition n, ∑ k ∈ Finset.Icc 1 n,
        ((k : ℚ) * p.parts.count k) • cycleTerm a p := by
      rw [cycleAverage, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_smul]
      congr 1
      exact_mod_cast (hdeg p).symm
    _ = ∑ k ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n,
        ((k : ℚ) * p.parts.count k) • cycleTerm a p := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hk, hkn⟩ := Finset.mem_Icc.mp hk
      exact marked_cycle_sum a n k hk hkn

private theorem cycle_average_zero (a : ℕ → R) : cycleAverage a 0 = 1 := by
  simp [cycleAverage, cycleTerm, zPartition, partitionExponent, zExponent]

private theorem cycle_average_derivative (a : ℕ → R) :
    PowerSeries.derivative (PowerSeries.mk (cycleAverage a)) =
      (PowerSeries.mk fun k => a (k + 1)) * PowerSeries.mk (cycleAverage a) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  rw [show cycleAverage a (n + 1) * (n + 1 : R) =
      ((n + 1 : ℕ) : ℚ) • cycleAverage a (n + 1) by simp [Algebra.smul_def, mul_comm]]
  rw [cycle_average_recursion]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2 <;> omega

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open PowerSeries

private theorem square_series :
    (PowerSeries.mk fun n => (n + 1 : ℚ) ^ 2) =
      2 * (invOneSubPow ℚ 3).val - (invOneSubPow ℚ 2).val := by
  ext n
  simp only [invOneSubPow, coeff_mk, map_sub, mul_comm (2 : PowerSeries ℚ),
    coeff_mul_ofNat]
  simp only [Nat.cast_choose_two, Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem consecutive_series :
    (PowerSeries.mk fun n => (n + 1 : ℚ) * (n + 2 : ℚ)) =
      2 * (invOneSubPow ℚ 3).val := by
  ext n
  simp only [invOneSubPow, coeff_mk, mul_comm (2 : PowerSeries ℚ), coeff_mul_ofNat]
  simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem constant_term_cancellation :
    (invOneSubPow ℚ 2).val *
      ((expand 2 (by decide) (PowerSeries.mk fun n => (n + 1 : ℚ) ^ 2)) -
        X * (expand 2 (by decide)
          (PowerSeries.mk fun n => (n + 1 : ℚ) * (n + 2 : ℚ)))) =
      expand 2 (by decide) (invOneSubPow ℚ 3).val := by
  have hrel : (1 - X : PowerSeries ℚ) * (invOneSubPow ℚ 3).val =
      (invOneSubPow ℚ 2).val := by
    simpa using one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ 2 1
  have he := congrArg (expand 2 (by decide)) hrel
  simp only [map_mul, map_sub, map_one, expand_X] at he
  rw [square_series, consecutive_series, map_sub, map_mul, map_ofNat]
  calc
    _ = (invOneSubPow ℚ 2).val *
        ((1 - X) ^ 2 * expand 2 (by decide) (invOneSubPow ℚ 3).val) := by
      rw [← he]
      ring
    _ = _ := by
      rw [← mul_assoc, show (invOneSubPow ℚ 2).val * (1 - X) ^ 2 = 1 from (invOneSubPow ℚ
        2).val_inv, one_mul]

private theorem coefficient_even_cube (n : ℕ) :
    (expand 2 (by decide) (invOneSubPow ℚ 3).val).coeff n =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  rw [coeff_expand]
  simp only [invOneSubPow, coeff_mk, Nat.add_comm 2, even_iff_two_dvd]

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open PowerSeries
variable {R : Type*} [CommRing R]



private theorem geometric_square (r : R) : (rescale r (invOneSubPow _ 1).val) ^ 2 = (rescale r
  (invOneSubPow _ 2).val) := by
  rw [← map_pow]
  congr 1
  simpa [pow_two, invOneSubPow_add, Units.val_mul] using
    (congrArg Units.val (invOneSubPow_add R 1 1)).symm

private theorem coeff_geometric (r : R) (n : ℕ) : coeff n ((rescale r (invOneSubPow _ 1).val)) =
  r ^ n := by
  simp [coeff_rescale, invOneSubPow]

private theorem coeff_geometricSquare (r : R) (n : ℕ) :
    coeff n ((rescale r (invOneSubPow _ 2).val)) = r ^ n * (n + 1) := by
  simp [coeff_rescale, invOneSubPow, Nat.add_comm]

private theorem geometric_derivative (r : R) :
    derivative ((rescale r (invOneSubPow _ 1).val)) = C r * (rescale r (invOneSubPow _ 2).val)
      := by
  ext n
  simp only [coeff_derivative, coeff_geometric, coeff_C_mul, coeff_geometricSquare,
    pow_succ]
  ring

private theorem geometricSquare_derivative (r : R) :
    derivative ((rescale r (invOneSubPow _ 2).val)) =
      (rescale r (invOneSubPow _ 2).val) * (C (2 * r) * (rescale r (invOneSubPow _ 1).val)) := by
  rw [← geometric_square, derivative_pow, geometric_derivative, ← geometric_square]
  norm_num
  simp only [map_ofNat]
  ring

private theorem three_square_derivative (r s t : R) :
    derivative ((rescale r (invOneSubPow _ 2).val) * (rescale s (invOneSubPow _ 2).val) *
      (rescale t (invOneSubPow _ 2).val)) =
      ((rescale r (invOneSubPow _ 2).val) * (rescale s (invOneSubPow _ 2).val) * (rescale t
        (invOneSubPow _ 2).val)) *
        PowerSeries.mk (fun k => 2 * (r ^ (k + 1) + s ^ (k + 1) + t ^ (k + 1))) := by
  have he : PowerSeries.mk (fun k => 2 * (r ^ (k + 1) + s ^ (k + 1) + t ^ (k + 1))) =
      C (2 * r) * (rescale r (invOneSubPow _ 1).val) + C (2 * s) * (rescale s (invOneSubPow _
        1).val) + C (2 * t) * (rescale t (invOneSubPow _ 1).val) := by
    ext n
    simp only [coeff_mk, map_add, coeff_C_mul, coeff_geometric, pow_succ]
    ring
  rw [he, derivative.leibniz, derivative.leibniz]
  simp only [smul_eq_mul, geometricSquare_derivative]
  ring

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open PowerSeries


private def constantTermSeries (f : PowerSeries (LaurentPolynomial ℚ)) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv
    ℚ).toLinearMap) (PowerSeries.coeff n f)

private theorem constantTerm_C_mul (a : ℚ) (f : (LaurentPolynomial ℚ)) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
      (LaurentPolynomial.C a * f) = a * ((Finsupp.lapply (R := ℚ) 0).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) f := by
  exact AddMonoidAlgebra.coeff_single_zero_mul f a 0

private theorem constantTermSeries_sub (f g : PowerSeries (LaurentPolynomial ℚ)) :
    constantTermSeries (f - g) = constantTermSeries f - constantTermSeries g := by
  ext n
  simp [constantTermSeries]

private theorem constantTermSeries_map_mul (f : PowerSeries ℚ) (g : PowerSeries
  (LaurentPolynomial ℚ)) :
    constantTermSeries ((PowerSeries.map LaurentPolynomial.C f) * g) =
      f * constantTermSeries g := by
  ext n
  simp only [constantTermSeries, coeff_mk, coeff_mul, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact constantTerm_C_mul _ _

private theorem constantTerm_shift (f : (LaurentPolynomial ℚ)) (k : ℤ) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
      (LaurentPolynomial.T k * f) = f.coeff (-k) := by
  change (LaurentPolynomial.T k * f).coeff 0 = _
  simpa only [zero_sub, add_zero, one_mul, LaurentPolynomial.T] using
    AddMonoidAlgebra.coeff_single_mul_apply f (1 : ℚ) k (0 : ℤ)


private theorem laurent_geometric_pair_term (i j : ℕ) :
    (LaurentPolynomial.T (1 : ℤ) ^ i * (i + 1 : (LaurentPolynomial ℚ))) *
      (LaurentPolynomial.T (-1 : ℤ) ^ j * (j + 1 : (LaurentPolynomial ℚ))) =
      LaurentPolynomial.C ((i + 1 : ℚ) * (j + 1 : ℚ)) *
        LaurentPolynomial.T ((i : ℤ) - j) := by
  simp only [LaurentPolynomial.T_pow, mul_one, mul_neg_one]
  rw [map_mul]
  have hi : (i + 1 : (LaurentPolynomial ℚ)) = LaurentPolynomial.C (i + 1 : ℚ) := by simp
  have hj : (j + 1 : (LaurentPolynomial ℚ)) = LaurentPolynomial.C (j + 1 : ℚ) := by simp
  rw [hi, hj, sub_eq_add_neg, LaurentPolynomial.T_add]
  ring

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open PowerSeries

private theorem pair_coefficient (n : ℕ) (e : ℤ) :
    (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val))).coeff e =
      ∑ i ∈ Finset.range (n + 1),
        if (i : ℤ) - (n - i : ℕ) = e then
          (i + 1 : ℚ) * (((n - i : ℕ) : ℚ) + 1) else 0 := by
  let c : (LaurentPolynomial ℚ) →ₗ[ℚ] ℚ := {
    toFun := fun p => p.coeff e
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  change c _ = _
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_geometricSquare, coeff_geometricSquare, laurent_geometric_pair_term]
  change (LaurentPolynomial.C _ * LaurentPolynomial.T _).coeff e = _
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

private theorem pair_coefficient_zero (n : ℕ) :
    (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val))).coeff 0 =
      if Even n then (((n / 2 : ℕ) : ℚ) + 1) ^ 2 else 0 := by
  rw [pair_coefficient]
  split_ifs with hn
  · have he : n % 2 = 0 := Nat.even_iff.mp hn
    rw [Finset.sum_eq_single (n / 2)]
    · have hnat : n - n / 2 = n / 2 := by omega
      simp [hnat, pow_two]
    · intro b hb hne
      have hb' := Finset.mem_range.mp hb
      have hne' : (b : ℤ) - (n - b : ℕ) ≠ 0 := by omega
      simp [hne']
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hn
    have hne : (i : ℤ) - (n - i : ℕ) ≠ 0 := by omega
    simp [hne]

private theorem pair_coefficient_one (n : ℕ) :
    (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val))).coeff 1 =
      if Even n then 0 else (((n / 2 : ℕ) : ℚ) + 1) * (((n / 2 : ℕ) : ℚ) + 2) := by
  rw [pair_coefficient]
  split_ifs with hn
  · apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : n % 2 = 0 := Nat.even_iff.mp hn
    have hne : (i : ℤ) - (n - i : ℕ) ≠ 1 := by omega
    simp [hne]
  · have he : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hn
    rw [Finset.sum_eq_single (n / 2 + 1)]
    · have hnat : n - (n / 2 + 1) = n / 2 := by omega
      have heq : ((n / 2 + 1 : ℕ) : ℤ) - (n - (n / 2 + 1) : ℕ) = 1 := by omega
      rw [ite_eq_left heq, hnat]
      push_cast
      ring
    · intro b hb hne
      have hb' := Finset.mem_range.mp hb
      have hne' : (b : ℤ) - (n - b : ℕ) ≠ 1 := by omega
      simp [hne']
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

private theorem constantTerm_pair :
    constantTermSeries ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ))
      (invOneSubPow _ 2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val)) =
      expand 2 (by decide) (mk fun j => (j + 1 : ℚ) ^ 2) := by
  ext n
  simp only [constantTermSeries, coeff_mk]
  change (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow
    _ 2).val) *
    (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
      2).val))).coeff 0 = _
  simpa only [coeff_expand, coeff_mk, ← even_iff_two_dvd] using pair_coefficient_zero n

private theorem constantTerm_shift_pair :
    constantTermSeries (C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) *
      ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val))) =
      X * expand 2 (by decide) (mk fun j => (j + 1 : ℚ) * (j + 2 : ℚ)) := by
  ext n
  simp only [constantTermSeries, coeff_mk, coeff_C_mul, constantTerm_shift, neg_neg]
  rw [pair_coefficient_one]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_expand, coeff_mk]
    by_cases he : Even n
    · have ho : ¬ Even (n + 1) := by rw [Nat.even_iff] at he ⊢; omega
      have hdiv : (n + 1) / 2 = n / 2 := by have := Nat.even_iff.mp he; omega
      simp [he, ho, hdiv, ← even_iff_two_dvd]
    · have ho : Even (n + 1) := Nat.even_add_one.mpr he
      simp [he, ho, ← even_iff_two_dvd]

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open PowerSeries

private def cycleInput (k : ℕ) : (LaurentPolynomial ℚ) :=
  2 * (LaurentPolynomial.T k + 1 + LaurentPolynomial.T (-(k : ℤ)))

private theorem cycle_generating_series :
    PowerSeries.mk (cycleAverage cycleInput) =
      (rescale (1 : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val)
          := by
  letI : HasUniqueDiv (LaurentPolynomial ℚ) :=
    HasUniqueDiv.of_module_rat (LaurentPolynomial ℚ)
  apply D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.solution_unique
    _ _ (PowerSeries.mk fun k => cycleInput (k + 1))
  · simpa only [mul_comm] using cycle_average_derivative cycleInput
  · have h := three_square_derivative (1 : (LaurentPolynomial ℚ))
      (LaurentPolynomial.T (1 : ℤ)) (LaurentPolynomial.T (-1 : ℤ))
    simpa only [cycleInput, one_pow, LaurentPolynomial.T_pow, mul_one, mul_neg_one,
      add_comm, add_left_comm, Nat.cast_add, Nat.cast_one] using h
  · simp only [coeff_zero_eq_constantCoeff, constantCoeff_mk, cycle_average_zero, map_mul]
    simp [← coeff_zero_eq_constantCoeff, invOneSubPow]

private theorem geometricSquare_one :
    (rescale (1 : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) =
      PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val := by
  ext n
  simp [invOneSubPow, Nat.add_comm]

private theorem weighted_constant_term_series :
    constantTermSeries ((1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ))) *
      PowerSeries.mk (cycleAverage cycleInput)) =
      expand 2 (by decide) (invOneSubPow ℚ 3).val := by
  rw [cycle_generating_series, geometricSquare_one]
  have he :
      (1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ))) *
        (PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val *
          (rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
          (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
            2).val)) =
      PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val *
        (((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
          (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
            2).val)) -
          C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) *
            ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
              2).val) *
              (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
                2).val))) := by ring
  rw [he, constantTermSeries_map_mul, constantTermSeries_sub,
    constantTerm_pair, constantTerm_shift_pair]
  exact constant_term_cancellation

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
open PowerSeries
open D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

private theorem laurent_coefficient_nat (P : Polynomial ℚ) (n : ℕ) :
    P.toLaurent.coeff (n : ℤ) = P.coeff n := by
  exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => Int.natCast_inj.mp h)
    P.toFinsupp.coeff n

private theorem constantTerm_polynomial_shift (P : Polynomial ℚ) (n : ℕ) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
      (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))) = P.coeff n := by
  change (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))).coeff 0 = _
  simpa only [LaurentPolynomial.T, zero_sub, neg_neg, zero_add, mul_one,
    laurent_coefficient_nat] using
    AddMonoidAlgebra.coeff_mul_single_apply P.toLaurent (1 : ℚ) (-(n : ℤ)) (0 : ℤ)


private theorem constantTerm_polynomial_difference (P : Polynomial ℚ) (n : ℕ) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ((1 -
      LaurentPolynomial.T (-1 : ℤ)) *
      (P.toLaurent * LaurentPolynomial.T (-(n : ℤ)))) =
      P.coeff n - P.coeff (n + 1) := by
  rw [sub_mul, one_mul, map_sub, constantTerm_polynomial_shift]
  have he : LaurentPolynomial.T (-1 : ℤ) *
      (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))) =
      P.toLaurent * LaurentPolynomial.T (-((n + 1 : ℕ) : ℤ)) := by
    rw [mul_left_comm, ← LaurentPolynomial.T_add]
    congr 2
    push_cast
    ring
  rw [he, constantTerm_polynomial_shift]

private theorem laurent_trinomial (a : ℕ) :
    Polynomial.toLaurent (Polynomial.X ^ (2 * a) + Polynomial.X ^ a + 1 : Polynomial ℚ) *
      LaurentPolynomial.T (-(a : ℤ)) =
      LaurentPolynomial.T (a : ℤ) + 1 + LaurentPolynomial.T (-(a : ℤ)) := by
  simp only [map_add, Polynomial.toLaurent_X_pow, map_one, add_mul, one_mul,
    ← LaurentPolynomial.T_add]
  have h2 : (2 : ℤ) * a + -(a : ℤ) = (a : ℤ) := by omega
  simp only [Nat.cast_mul, Nat.cast_ofNat, h2, add_neg_cancel, LaurentPolynomial.T_zero]

private theorem laurent_product (l : List ℕ) :
    (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) + 1 +
      LaurentPolynomial.T (-(a : ℤ)) : List (LaurentPolynomial ℚ)).prod =
      ((triProd l).map (Int.castRingHom ℚ)).toLaurent *
        LaurentPolynomial.T (-((l.sum : ℕ) : ℤ)) := by
  induction l with
  | nil => simp [triProd]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, triProd, Polynomial.map_mul, map_mul,
      Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      Nat.cast_add, neg_add] at ih ⊢
    rw [← laurent_trinomial a, ih, LaurentPolynomial.T_add]
    ring

private theorem cycleInput_product (l : List ℕ) :
    (l.map cycleInput).prod =
      LaurentPolynomial.C ((2 : ℚ) ^ l.length) *
        (((triProd l).map (Int.castRingHom ℚ)).toLaurent *
          LaurentPolynomial.T (-((l.sum : ℕ) : ℤ))) := by
  have he : (l.map cycleInput).prod =
      (2 : (LaurentPolynomial ℚ)) ^ l.length * (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) +
        1 +
        LaurentPolynomial.T (-(a : ℤ))).prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, cycleInput, ih, pow_succ]
      ring
  rw [he, laurent_product]
  congr 1
  exact (map_pow LaurentPolynomial.C (2 : ℚ) l.length).trans (by simp only [map_ofNat]) |>.symm

private theorem character_constantTerm (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) :
    ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ((1 -
      LaurentPolynomial.T (-1 : ℤ)) *
      (p.parts.map cycleInput).prod) =
      ((((evTypes p.parts.toList).map fun τ => frobChar ![n, n, 0] τ).sum : ℤ) : ℚ) := by
  have he := cycleInput_product p.parts.toList
  have hsum : p.parts.toList.sum = n := by simpa using p.parts_sum
  rw [Multiset.prod_map_toList, hsum, Multiset.length_toList] at he
  rw [he, mul_left_comm, constantTerm_C_mul, constantTerm_polynomial_difference,
    rectangular_sum_coefficient n hn p]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub, Polynomial.coeff_map,
    Int.coe_castRingHom]

private theorem rightCoefficientAverage_constantTerm (n : ℕ) (hn : 1 ≤ n) :
    rightCoefficientAverage n = ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv
      ℚ).toLinearMap) ((1 - LaurentPolynomial.T (-1 : ℤ)) * cycleAverage cycleInput n) := by
  simp only [rightCoefficientAverage, cycleAverage, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [cycleTerm, mul_smul_comm, map_smul, character_constantTerm n hn p]
  rfl

private theorem rightCoefficientAverage_closed (n : ℕ) (hn : 1 ≤ n) :
    rightCoefficientAverage n = if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  rw [rightCoefficientAverage_constantTerm n hn]
  have he := congrArg (coeff n) weighted_constant_term_series
  simp only [constantTermSeries, coeff_mk] at he
  have hc : (1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) : PowerSeries
    (LaurentPolynomial ℚ)) =
      C (1 - LaurentPolynomial.T (-1 : ℤ)) := by simp
  rw [hc, coeff_C_mul, coeff_mk, coefficient_even_cube] at he
  exact he


/-- Conjecture 6.1 / journal Conjecture 17 with actual same-partition ordinary
complex polytabloid traces, both averages and both parity values, for all n ≥ 1.
The literal rectangle (n,n,0) is used also for odd n. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    leftAverage n = rightAverage n ∧
      leftAverage n = (if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℂ) else 0) ∧
      rightAverage n = (if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℂ) else 0) := by
  have equal := weighted_identity n hn
  have value : rightAverage n =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℂ) else 0 := by
    rw [rightAverage_eq_frobenius]
    have h := congrArg (fun q : ℚ => (q : ℂ)) (rightCoefficientAverage_closed n hn)
    split_ifs with he
    · simpa only [if_pos he, Rat.cast_natCast] using h
    · simpa only [if_neg he, Rat.cast_zero] using h
  exact ⟨equal, equal.trans value, value⟩

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
