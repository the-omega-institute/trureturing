/- GID: D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtThreeRowCauchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual three-row Specht trace and both evaluated HSW ordinary averages. -/

/-
The full ordinary HSW averages use the independently constructed complex Specht trace.
The finite Cauchy kernel calculation is supplied by SpechtThreeRowCauchyKernel.
Unfinished public-declaration audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchyKernel
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

open private solution_unique
  from D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open private right_coefficient ev_right triProd
  from D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti.ThreeRowGram
open _root_.Equiv _root_.Equiv.Perm Finset

/-- The independently defined actual complex polytabloid trace of the literal
sort/delete-zero three-row partition equals the existing HSW alternant coefficient. -/
theorem ordinaryTrace_eq_frobChar {n : ℕ} (r : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1)
    (ρ : n.Partition) {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {τ : List ℕ}
    (hτ : (τ : Multiset ℕ) = ρ.parts) :
    LinearMap.trace ℂ _ ((spechtModuleℂ (tripleShape r hr)).ρ π) =
      (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ : ℂ) := by
  apply ordinaryTrace_eq_frobChar_of_selfGram r hr h01 h12 _ ρ hπ hτ
  simpa using signedContingencyGram_eq_delta r r hr h01 h12 h01 h12

/-- Class values of the unchanged actual Specht module, for use in finite sums. -/
theorem spechtCharValue_eq_frobChar {n : ℕ} (r : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1)
    (ρ : n.Partition) {τ : List ℕ} (hτ : (τ : Multiset ℕ) = ρ.parts) :
    spechtCharValue (tripleShape r hr) ρ =
      D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ := by
  obtain ⟨π, hπ⟩ := (partitionEquivConjClasses n ρ).exists_rep
  have h := ordinaryTrace_eq_frobChar r hr h01 h12 ρ hπ hτ
  change (spechtModuleℂ (tripleShape r hr)).character π = _ at h
  rw [character_spechtModuleℂ_intCast,
    ← spechtCharValue_eq_spechtChar _ _ hπ] at h
  exact_mod_cast h

private theorem evTypes_parts {n : ℕ} (lam : n.Partition) {τ : List ℕ}
    (hτ : τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList) :
    τ.sum = 2*n ∧ ∀ a ∈ τ, 0 < a := by
  have hgeneral (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
      ∀ τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes l,
        τ.sum = 2*l.sum ∧ ∀ a ∈ τ, 0 < a := by
    induction l with
    | nil => simp [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes]
    | cons a l ih =>
      intro τ ht
      have ha := hl a (by simp)
      have hrest := ih (fun b hb => hl b (by simp [hb]))
      simp only [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes,
        List.mem_append, List.mem_map] at ht
      rcases ht with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · obtain ⟨hs, hp⟩ := hrest v hv
        constructor
        · simp only [List.sum_cons]; omega
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro (by omega : 0 < 2*a) hp
      · obtain ⟨hs, hp⟩ := hrest v hv
        constructor
        · simp only [List.sum_cons]; omega
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro ha (And.intro ha hp)
  simpa [lam.parts_sum] using hgeneral lam.parts.toList (fun a ha => lam.parts_pos (by simpa using ha)) τ hτ

/-- The complete Ev list defines a partition of 2n, including every one-cycle. -/
def evPartition {n : ℕ} (lam : n.Partition)
    (τ : {τ // τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList}) :
    (2*n).Partition where
  parts := τ.val
  parts_pos := by
    intro a ha
    exact (evTypes_parts lam τ.property).2 a (by simpa using ha)
  parts_sum := by simpa using (evTypes_parts lam τ.property).1

private theorem rows_total {m : ℕ} {r : Fin 3 → ℕ}
    (hr : r ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 m) : ∑ i, r i = m :=
  Finset.Nat.mem_antidiagonalTuple.mp (mem_filter.mp hr).1

/-- The signed even-row sum of actual ordinary character values, with Ev multiplicity. -/
def signedEvSpechtSum {n : ℕ} (lam : n.Partition) : ℤ :=
  ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList).attach.map
    fun τ => ∑ r ∈ (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 (2*n)).attach,
      (-1 : ℤ)^τ.val.length *
        spechtCharValue (tripleShape r.val (rows_total r.property)) (evPartition lam τ)).sum

/-- The rectangle sum of actual ordinary character values; odd n is included. -/
def rectangleEvSpechtSum {n : ℕ} (lam : n.Partition) : ℤ :=
  ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList).attach.map
    fun τ => spechtCharValue (tripleShape ![n,n,0] (by simp [Fin.sum_univ_three]; omega))
      (evPartition lam τ)).sum

/-- Both original inner Ev sums consume the actual same-partition trace bridge. -/
theorem evSpechtSums_eq_coefficients {n : ℕ} (lam : n.Partition) :
    signedEvSpechtSum lam =
      ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList).map
        fun τ => ∑ r ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 (2*n),
          (-1 : ℤ)^τ.length *
            D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ).sum ∧
    rectangleEvSpechtSum lam =
      ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList).map
        fun τ => D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar ![n,n,0] τ).sum := by
  have hrow (τ : {τ // τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList})
      (r : {r // r ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 (2*n)}) :
      spechtCharValue (tripleShape r.val (rows_total r.property)) (evPartition lam τ) =
        D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r.val τ.val :=
    spechtCharValue_eq_frobChar r.val (rows_total r.property)
      (mem_filter.mp r.property).2.1 (mem_filter.mp r.property).2.2.1 _ rfl
  have hrect (τ : {τ // τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes lam.parts.toList}) :
      spechtCharValue (tripleShape ![n,n,0] (by simp [Fin.sum_univ_three]; omega))
        (evPartition lam τ) =
        D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar ![n,n,0] τ.val :=
    spechtCharValue_eq_frobChar ![n,n,0] _ (by simp) (by simp) _ rfl
  constructor
  · simp only [signedEvSpechtSum, hrow]
    simp
    congr 1
    apply List.map_congr_left
    intro τ hτ
    exact Finset.sum_attach _ (fun r =>
      (-1 : ℤ)^τ.length *
        D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ)
  · simp only [rectangleEvSpechtSum, hrect]
    simp

/-- Actual ordinary characters satisfy the original per-partition Ev identity.
Its weighted consumers below evaluate both reciprocal-centralizer averages. -/
theorem ordinaryEv_identity {n : ℕ} (hn : 1 ≤ n) (lam : n.Partition) :
    signedEvSpechtSum lam = rectangleEvSpechtSum lam := by
  rw [(evSpechtSums_eq_coefficients lam).1, (evSpechtSums_eq_coefficients lam).2]
  exact D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.result n hn lam

/-- The two reciprocal-centralizer weighted averages of actual ordinary characters
are equal; the evaluated consumers below give their common value. -/
theorem ordinaryWeightedEv_identity (n : ℕ) (hn : 1 ≤ n) :
    (∑ lam : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ *
        (signedEvSpechtSum lam : ℚ)) =
    ∑ lam : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ *
        (rectangleEvSpechtSum lam : ℚ) := by
  apply sum_congr rfl
  intro lam _
  rw [ordinaryEv_identity hn lam]

open PowerSeries
open D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The rectangular ordinary average in the full original HSW conjecture.
The partition sum, Laurent series and coefficient maps below are local to this
consumer. ODE uniqueness and the rectangular coefficient identity are reused
from their existing owners, with no new coefficient-character definition. -/
theorem ordinaryWeightedRectangleEv_evaluated (n : ℕ) (hn : 1 ≤ n) :
    (∑ lam : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ *
        (rectangleEvSpechtSum lam : ℚ)) =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  classical
  let cycleWeight (k : ℕ) : LaurentPolynomial ℚ :=
    2 * (LaurentPolynomial.T (k : ℤ) + 1 + LaurentPolynomial.T (-(k : ℤ)))
  let term {d : ℕ} (lam : d.Partition) : LaurentPolynomial ℚ :=
    (zPartition lam : ℚ)⁻¹ • (lam.parts.map cycleWeight).prod
  let A (d : ℕ) : LaurentPolynomial ℚ := ∑ lam : d.Partition, term lam

  have partition_exponent_count {n : ℕ} (p : Nat.Partition n)
      (k : ℕ) (hk : 0 < k) : partitionExponent p (k - 1) = p.parts.count k := by
    have h := congrArg (Multiset.count k) (exponentParts_partitionExponent p)
    rw [exponentParts, show k = Nat.succ (k - 1) by omega,
      Multiset.count_map_eq_count' Nat.succ _ Nat.succ_injective,
      Finsupp.count_toMultiset] at h
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using h

  have z_partition_cons {n m k : ℕ}
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

  have cycle_term_cons {n m k : ℕ}
      (p : Nat.Partition n) (q : Nat.Partition m)
      (hk : 0 < k) (hp : p.parts = k ::ₘ q.parts) :
      ((k : ℚ) * (q.parts.count k + 1)) • term p = cycleWeight k * term q := by
    have hz : (zPartition q : ℚ) ≠ 0 := by
      exact_mod_cast (zExponent_pos (partitionExponent q)).ne'
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    have hc : (q.parts.count k + 1 : ℚ) ≠ 0 := by positivity
    have hs : ((k : ℚ) * (q.parts.count k + 1)) * (zPartition p : ℚ)⁻¹ =
        (zPartition q : ℚ)⁻¹ := by
      rw [z_partition_cons p q hk hp]
      push_cast
      field_simp
    simp only [term, hp, Multiset.map_cons, Multiset.prod_cons, smul_smul, hs]
    exact (mul_smul_comm _ _ _).symm

  have marked_cycle_sum (n k : ℕ)
      (hk : 0 < k) (hkn : k ≤ n) :
      (∑ p : Nat.Partition n, ((k : ℚ) * p.parts.count k) • term p) =
        cycleWeight k * A (n - k) := by
    let e := Nat.Partition.partitionWithPartEquiv hk hkn
    calc
      _ = ∑ p : {p : Nat.Partition n // k ∈ p.parts},
          ((k : ℚ) * p.val.parts.count k) • term p.val := by
        apply Finset.sum_congr_set {p : Nat.Partition n | k ∈ p.parts}
        · intro p hp
          rfl
        · intro p hp
          simp [Multiset.count_eq_zero_of_notMem hp]
      _ = ∑ q : Nat.Partition (n - k), cycleWeight k * term q := by
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
        exact cycle_term_cons p.val (e p) hk hp
      _ = _ := by dsimp only [A]; rw [Finset.mul_sum]

  have cycle_average_recursion (n : ℕ) :
      (n : ℚ) • A n =
        ∑ k ∈ Finset.Icc 1 n, cycleWeight k * A (n - k) := by
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
          ((k : ℚ) * p.parts.count k) • term p := by
        dsimp only [A]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.sum_smul]
        congr 1
        exact_mod_cast (hdeg p).symm
      _ = ∑ k ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n,
          ((k : ℚ) * p.parts.count k) • term p := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hk, hkn⟩ := Finset.mem_Icc.mp hk
        exact marked_cycle_sum n k hk hkn

  have cycle_average_zero : A 0 = 1 := by
    simp [A, term, zPartition, partitionExponent, zExponent]

  have cycle_average_derivative :
      PowerSeries.derivative (PowerSeries.mk (A)) =
        (PowerSeries.mk fun k => cycleWeight (k + 1)) * PowerSeries.mk (A) := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
    rw [show A (n + 1) * (n + 1 : LaurentPolynomial ℚ) =
        ((n + 1 : ℕ) : ℚ) • A (n + 1) by simp [Algebra.smul_def, mul_comm]]
    rw [cycle_average_recursion]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i hi
    congr 2 <;> omega

  have square_series :
      (PowerSeries.mk fun n => (n + 1 : ℚ) ^ 2) =
        2 * (invOneSubPow ℚ 3).val - (invOneSubPow ℚ 2).val := by
    ext n
    simp only [invOneSubPow, coeff_mk, map_sub, mul_comm (2 : PowerSeries ℚ),
      coeff_mul_ofNat]
    simp only [Nat.cast_choose_two, Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat]
    ring

  have consecutive_series :
      (PowerSeries.mk fun n => (n + 1 : ℚ) * (n + 2 : ℚ)) =
        2 * (invOneSubPow ℚ 3).val := by
    ext n
    simp only [invOneSubPow, coeff_mk, mul_comm (2 : PowerSeries ℚ), coeff_mul_ofNat]
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
    ring

  have constant_term_cancellation :
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

  have coefficient_even_cube (n : ℕ) :
      (expand 2 (by decide) (invOneSubPow ℚ 3).val).coeff n =
        if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
    rw [coeff_expand]
    simp only [invOneSubPow, coeff_mk, Nat.add_comm 2, even_iff_two_dvd]

  have geometric_square (r : LaurentPolynomial ℚ) : (rescale r (invOneSubPow _ 1).val) ^ 2 = (rescale r
    (invOneSubPow _ 2).val) := by
    rw [← map_pow]
    congr 1
    simpa [pow_two, invOneSubPow_add, Units.val_mul] using
      (congrArg Units.val (invOneSubPow_add (LaurentPolynomial ℚ) 1 1)).symm

  have coeff_geometric (r : LaurentPolynomial ℚ) (n : ℕ) : coeff n ((rescale r (invOneSubPow _ 1).val)) =
    r ^ n := by
    simp [coeff_rescale, invOneSubPow]

  have coeff_geometricSquare (r : LaurentPolynomial ℚ) (n : ℕ) :
      coeff n ((rescale r (invOneSubPow _ 2).val)) = r ^ n * (n + 1) := by
    simp [coeff_rescale, invOneSubPow, Nat.add_comm]

  have geometric_derivative (r : LaurentPolynomial ℚ) :
      derivative ((rescale r (invOneSubPow _ 1).val)) = C r * (rescale r (invOneSubPow _ 2).val)
        := by
    ext n
    simp only [coeff_derivative, coeff_geometric, coeff_C_mul, coeff_geometricSquare,
      pow_succ]
    ring

  have geometricSquare_derivative (r : LaurentPolynomial ℚ) :
      derivative ((rescale r (invOneSubPow _ 2).val)) =
        (rescale r (invOneSubPow _ 2).val) * (C (2 * r) * (rescale r (invOneSubPow _ 1).val)) := by
    rw [← geometric_square, derivative_pow, geometric_derivative, ← geometric_square]
    norm_num
    simp only [map_ofNat]
    ring

  have three_square_derivative (r s t : LaurentPolynomial ℚ) :
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

  let constantTermSeries (f : PowerSeries (LaurentPolynomial ℚ)) : PowerSeries ℚ :=
    PowerSeries.mk fun n => ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv
      ℚ).toLinearMap) (PowerSeries.coeff n f)

  have constantTerm_C_mul (a : ℚ) (f : (LaurentPolynomial ℚ)) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
        (LaurentPolynomial.C a * f) = a * ((Finsupp.lapply (R := ℚ) 0).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) f := by
    exact AddMonoidAlgebra.coeff_single_zero_mul f a 0

  have constantTermSeries_sub (f g : PowerSeries (LaurentPolynomial ℚ)) :
      constantTermSeries (f - g) = constantTermSeries f - constantTermSeries g := by
    ext n
    simp [constantTermSeries]

  have constantTermSeries_map_mul (f : PowerSeries ℚ) (g : PowerSeries
    (LaurentPolynomial ℚ)) :
      constantTermSeries ((PowerSeries.map LaurentPolynomial.C f) * g) =
        f * constantTermSeries g := by
    ext n
    simp only [constantTermSeries, coeff_mk, coeff_mul, coeff_map, map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact constantTerm_C_mul _ _

  have constantTerm_shift (f : (LaurentPolynomial ℚ)) (k : ℤ) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
        (LaurentPolynomial.T k * f) = f.coeff (-k) := by
    change (LaurentPolynomial.T k * f).coeff 0 = _
    simpa only [zero_sub, add_zero, one_mul, LaurentPolynomial.T] using
      AddMonoidAlgebra.coeff_single_mul_apply f (1 : ℚ) k (0 : ℤ)

  have laurent_geometric_pair_term (i j : ℕ) :
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

  have pair_coefficient (n : ℕ) (e : ℤ) :
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

  have pair_coefficient_zero (n : ℕ) :
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

  have pair_coefficient_one (n : ℕ) :
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

  have constantTerm_pair :
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

  have constantTerm_shift_pair :
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

  -- Both differential equations use the same literal positive-cycle driver.
  have hseries : PowerSeries.mk A =
      (rescale (1 : LaurentPolynomial ℚ) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℚ)
          (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℚ)
          (invOneSubPow _ 2).val) := by
    letI : HasUniqueDiv (LaurentPolynomial ℚ) := .of_module_rat _
    apply solution_unique
      (PowerSeries.mk A) _ (PowerSeries.mk fun k => cycleWeight (k + 1))
    · simpa only [mul_comm] using cycle_average_derivative
    · have h := three_square_derivative (1 : LaurentPolynomial ℚ)
        (LaurentPolynomial.T (1 : ℤ)) (LaurentPolynomial.T (-1 : ℤ))
      simpa only [cycleWeight, one_pow, LaurentPolynomial.T_pow, mul_one, mul_neg_one,
        add_comm, add_left_comm, Nat.cast_add, Nat.cast_one] using h
    · simp only [coeff_mk, cycle_average_zero]
      simp [coeff_mul, coeff_geometricSquare, invOneSubPow]

  have geometricSquare_one :
      (rescale (1 : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) =
        PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val := by
    ext n
    simp [invOneSubPow, Nat.add_comm]

  have weighted_constant_term_series :
      constantTermSeries ((1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ))) *
        PowerSeries.mk A) =
        expand 2 (by decide) (invOneSubPow ℚ 3).val := by
    rw [hseries, geometricSquare_one]
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

  have laurent_coefficient_nat (P : Polynomial ℚ) (n : ℕ) :
      P.toLaurent.coeff (n : ℤ) = P.coeff n := by
    exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => Int.natCast_inj.mp h)
      P.toFinsupp.coeff n

  have constantTerm_polynomial_shift (P : Polynomial ℚ) (n : ℕ) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
        (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))) = P.coeff n := by
    change (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))).coeff 0 = _
    simpa only [LaurentPolynomial.T, zero_sub, neg_neg, zero_add, mul_one,
      laurent_coefficient_nat] using
      AddMonoidAlgebra.coeff_mul_single_apply P.toLaurent (1 : ℚ) (-(n : ℤ)) (0 : ℤ)

  have constantTerm_polynomial_difference (P : Polynomial ℚ) (n : ℕ) :
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

  have laurent_trinomial (a : ℕ) :
      Polynomial.toLaurent (Polynomial.X ^ (2 * a) + Polynomial.X ^ a + 1 : Polynomial ℚ) *
        LaurentPolynomial.T (-(a : ℤ)) =
        LaurentPolynomial.T (a : ℤ) + 1 + LaurentPolynomial.T (-(a : ℤ)) := by
    simp only [map_add, Polynomial.toLaurent_X_pow, map_one, add_mul, one_mul,
      ← LaurentPolynomial.T_add]
    have h2 : (2 : ℤ) * a + -(a : ℤ) = (a : ℤ) := by omega
    simp only [Nat.cast_mul, Nat.cast_ofNat, h2, add_neg_cancel, LaurentPolynomial.T_zero]

  have laurent_product (l : List ℕ) :
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

  have input_product (l : List ℕ) :
      (l.map cycleWeight).prod =
        LaurentPolynomial.C ((2 : ℚ) ^ l.length) *
          (((triProd l).map (Int.castRingHom ℚ)).toLaurent *
            LaurentPolynomial.T (-((l.sum : ℕ) : ℤ))) := by
    have he : (l.map cycleWeight).prod =
        (2 : (LaurentPolynomial ℚ)) ^ l.length * (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) +
          1 +
          LaurentPolynomial.T (-(a : ℤ))).prod := by
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.prod_cons, List.length_cons, cycleWeight, ih, pow_succ]
        ring
    rw [he, laurent_product]
    congr 1
    exact (map_pow LaurentPolynomial.C (2 : ℚ) l.length).trans (by simp only [map_ofNat]) |>.symm

  have character_constantTerm (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ((1 -
        LaurentPolynomial.T (-1 : ℤ)) *
        (p.parts.map cycleWeight).prod) =
        (rectangleEvSpechtSum p : ℚ) := by
    have he := input_product p.parts.toList
    have hsum : p.parts.toList.sum = n := by simpa using p.parts_sum
    rw [Multiset.prod_map_toList, hsum, Multiset.length_toList] at he
    rw [(evSpechtSums_eq_coefficients p).2]
    have hpos : ∀ b ∈ p.parts.toList, 0 < b := by
      intro b hb
      exact p.parts_pos (by simpa using hb)
    have hrect := right_coefficient p.parts.toList (by omega : 1 ≤ p.parts.toList.sum) hpos
    rw [← ev_right] at hrect
    rw [he, mul_left_comm, constantTerm_C_mul, constantTerm_polynomial_difference,
      show ((evTypes p.parts.toList).map fun τ => frobChar ![n,n,0] τ).sum =
        (2 : ℤ)^p.parts.card *
          ((triProd p.parts.toList).coeff n - (triProd p.parts.toList).coeff (n+1)) by
        simpa only [hsum, Multiset.length_toList] using hrect]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub, Polynomial.coeff_map,
      Int.coe_castRingHom]

  have haverage :
      (∑ lam : n.Partition, (zPartition lam : ℚ)⁻¹ * (rectangleEvSpechtSum lam : ℚ)) =
      ((Finsupp.lapply (R := ℚ) 0).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
          ((1 - LaurentPolynomial.T (-1 : ℤ)) * A n) := by
    simp only [A, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro lam _
    dsimp only [term]
    rw [mul_smul_comm, map_smul, character_constantTerm n hn lam]
    rfl
  rw [haverage]
  have he := congrArg (coeff n) weighted_constant_term_series
  simp only [constantTermSeries, coeff_mk] at he
  have hc : (1 - C (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℚ) :
      PowerSeries (LaurentPolynomial ℚ)) =
      C (1 - LaurentPolynomial.T (-1 : ℤ)) := by simp
  rw [hc, coeff_C_mul, coeff_mk, coefficient_even_cube] at he
  exact he

/-- The signed ordinary average has the same evaluated value, with all even
three-row shapes and all occurrence-wise Ev outcomes retained. -/
theorem ordinaryWeightedSignedEv_evaluated (n : ℕ) (hn : 1 ≤ n) :
    (∑ lam : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition lam : ℚ)⁻¹ *
        (signedEvSpechtSum lam : ℚ)) =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  rw [ordinaryWeightedEv_identity n hn]
  exact ordinaryWeightedRectangleEv_evaluated n hn

end TauCeti.ThreeRowGram
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
