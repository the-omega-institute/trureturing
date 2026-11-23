/- GID: D5/S3/Combinatorics/Partitions/DesignatedSummands
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/DesignatedSummands
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.GenFun]
   utility: none
   digest: Ordered tuples of partitions with designated summands have an Euler product. -/

import D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct
import Mathlib.Combinatorics.Enumerative.Partition.GenFun

/-! Definition 2.1 and Proposition 2.2 of Yaqubi and Mirzavaziri (arXiv:2611.05623v1). For each positive multiplicity, a finite index records the chosen occurrence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace D5.S3.Combinatorics.Partitions.DesignatedSummands

open Filter Finset PowerSeries D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct
open scoped PowerSeries.WithPiTopology

/-- A partition with a designated occurrence for each distinct part size. -/
def MarkedPartition (n : ℕ) :=
  Σ p : n.Partition, (i : p.parts.toFinset) → Fin (p.parts.count i.1)

noncomputable instance markedPartitionFintype (n : ℕ) : Fintype (MarkedPartition n) := by
  classical
  unfold MarkedPartition
  infer_instance

/-- Ordered components indexed by a degree assignment of total size `n`. Components of
degree zero are allowed. -/
def MarkedTuple (k n : ℕ) :=
  Σ l : (Finset.range k).finsuppAntidiag n,
    (i : Finset.range k) → MarkedPartition (l.1 i.1)

noncomputable instance markedTupleFintype (k n : ℕ) : Fintype (MarkedTuple k n) := by
  classical
  unfold MarkedTuple
  infer_instance

noncomputable def markedCount (k n : ℕ) := Fintype.card (MarkedTuple k n)

private noncomputable def markedSeries : PowerSeries ℕ :=
  Nat.Partition.genFun (fun _ j => j)

private theorem marked_partition_count (n : ℕ) :
    Fintype.card (MarkedPartition n) = coeff n markedSeries := by
  classical
  rw [markedSeries, Nat.Partition.coeff_genFun]
  unfold MarkedPartition
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Fintype.card_pi, Fintype.card_fin, Finsupp.prod,
    Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  exact Finset.prod_coe_sort p.parts.toFinset (fun i => p.parts.count i)

private theorem marked_count_coeff_nat (k n : ℕ) : markedCount k n = coeff n (markedSeries ^ k) := by
  classical
  rw [coeff_pow, markedCount]
  unfold MarkedTuple
  rw [Fintype.card_sigma]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fintype.card_pi, marked_partition_count]
  exact Finset.prod_coe_sort (Finset.range k) (fun i => coeff (l.1 i) markedSeries)

private noncomputable def geom {R : Type*} [Semiring R] : PowerSeries R :=
  PowerSeries.mk fun _ => 1

private theorem geom_mul {R : Type*} [CommRing R] :
    (1 - PowerSeries.X : PowerSeries R) * geom = 1 := by
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, geom]
  | succ n =>
    rw [sub_mul, one_mul, map_sub]
    rw [show (PowerSeries.X : PowerSeries R) * geom = PowerSeries.X ^ 1 * geom by rw [pow_one]]
    rw [coeff_X_pow_mul]
    simp [geom]

private theorem coeff_geom_sq {R : Type*} [CommRing R] (n : ℕ) :
    coeff n ((geom : PowerSeries R) ^ 2) = (n : R) + 1 := by
  rw [pow_two, coeff_mul]
  simp [geom, Nat.card_antidiagonal, Nat.cast_succ]

private noncomputable def markedFactor {R : Type*} [CommRing R] :
    PowerSeries R := 1 + PowerSeries.X * geom ^ 2

private theorem markedFactor_identity {R : Type*} [CommRing R] :
    (markedFactor : PowerSeries R) * ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) *
      (1 - PowerSeries.X ^ 3)) = 1 - PowerSeries.X ^ 6 := by
  have h : (markedFactor : PowerSeries R) * (1 - PowerSeries.X) ^ 2 =
      1 - PowerSeries.X + PowerSeries.X ^ 2 := by
    unfold markedFactor
    calc
      _ = (1 - PowerSeries.X) ^ 2 +
          (PowerSeries.X : PowerSeries R) * (((1 - PowerSeries.X) * geom) ^ 2) := by ring
      _ = _ := by rw [geom_mul]; ring
  calc
    _ = ((markedFactor : PowerSeries R) * (1 - PowerSeries.X) ^ 2) *
        ((1 + PowerSeries.X) * (1 - PowerSeries.X ^ 3)) := by ring
    _ = _ := by rw [h]; ring

noncomputable def F {R : Type*} [CommRing R] : PowerSeries R :=
  euler 6 (by decide) * invOne (euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide))

theorem F_const {R : Type*} [CommRing R] : constantCoeff (F : PowerSeries R) = 1 := by
  simp [F, invOne, constantCoeff_invOfUnit, euler_const]

private local instance : TopologicalSpace ℤ := ⊥
private local instance : DiscreteTopology ℤ := ⟨rfl⟩
private local instance : TopologicalSpace ℕ := ⊥
private local instance : DiscreteTopology ℕ := ⟨rfl⟩

private theorem markedFactor_hasSum (d : ℕ) (hd : d ≠ 0) :
    HasSum (fun j : ℕ => ((j : ℤ) + 1) • (PowerSeries.X : PowerSeries ℤ) ^ (d * (j + 1)))
      (expand d hd ((markedFactor : PowerSeries ℤ) - 1)) := by
  have h := ((geom : PowerSeries ℤ)^2).hasSum_of_monomials_self
  have hc : Continuous (fun p : PowerSeries ℤ => PowerSeries.X * p) :=
    continuous_const.mul continuous_id
  have hx := h.map
    ({ toFun := fun p => PowerSeries.X * p
       map_zero' := mul_zero _
       map_add' := mul_add _ } : PowerSeries ℤ →+ PowerSeries ℤ) hc
  have hy := hx.map (expand d hd).toAddMonoidHom (tendsto_expand_discrete d hd)
  convert hy using 1
  · funext j
    simp [markedFactor, coeff_geom_sq, monomial_eq_C_mul_X_pow, mul_left_comm,
      ← pow_succ', PowerSeries.smul_eq_C_mul, expand_C, ← pow_mul]
  · simp [markedFactor]

private theorem marked_series_eq_F :
    markedSeries.map (Nat.castRingHom ℤ) = F := by
  let G : PowerSeries ℤ := markedSeries.map (Nat.castRingHom ℤ)
  let g : ℕ → ℕ → ℤ := fun _ j => j
  have hm : G = Nat.Partition.genFun g := by
    ext n
    simp [G, markedSeries, g, Finsupp.prod]
  have hG := (Nat.Partition.hasProd_genFun g).tendsto_prod_nat
  have hf (i : ℕ) :
      (1 + ∑' j, g (i + 1) (j + 1) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) =
        expand (i + 1) (Nat.succ_ne_zero _) markedFactor := by
    unfold g
    simp only [Nat.cast_add, Nat.cast_one]
    rw [(markedFactor_hasSum _ (Nat.succ_ne_zero _)).tsum_eq, map_sub, map_one]
    abel
  change Tendsto (fun N => ∏ i ∈ range N,
    (1 + ∑' j, g (i + 1) (j + 1) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))))
    atTop (nhds (Nat.Partition.genFun g)) at hG
  simp_rw [hf] at hG
  change Tendsto (fun N => ∏ i ∈ range N, expand (i + 1) (Nat.succ_ne_zero _) markedFactor)
    atTop (nhds (Nat.Partition.genFun g)) at hG
  rw [← hm] at hG
  have hp := (((hG.mul (euler_tendsto (R := ℤ) 1 (by decide))).mul
    (euler_tendsto 2 (by decide))).mul (euler_tendsto 3 (by decide)))
  have hN (N : ℕ) :
      (∏ i ∈ range N, expand (i + 1) (Nat.succ_ne_zero _) (markedFactor : PowerSeries ℤ)) *
      (∏ i ∈ range N, (1 - PowerSeries.X ^ (1 * (i + 1)))) *
      (∏ i ∈ range N, (1 - PowerSeries.X ^ (2 * (i + 1)))) *
      (∏ i ∈ range N, (1 - PowerSeries.X ^ (3 * (i + 1)))) =
      ∏ i ∈ range N, (1 - PowerSeries.X ^ (6 * (i + 1))) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have h := congrArg (expand (i + 1) (Nat.succ_ne_zero _))
      (markedFactor_identity (R := ℤ))
    simpa only [map_mul, map_sub, map_one, map_pow, expand_X, ← pow_mul,
      Nat.mul_comm (i + 1), mul_assoc, one_mul] using h
  change Tendsto (fun N =>
    (∏ i ∈ range N, expand (i + 1) (Nat.succ_ne_zero _) markedFactor) *
    (∏ i ∈ range N, (1 - PowerSeries.X ^ (1 * (i + 1)))) *
    (∏ i ∈ range N, (1 - PowerSeries.X ^ (2 * (i + 1)))) *
    (∏ i ∈ range N, (1 - PowerSeries.X ^ (3 * (i + 1)))))
    atTop (nhds (G * euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide))) at hp
  simp_rw [hN] at hp
  have he := tendsto_nhds_unique hp (euler_tendsto 6 (by decide))
  let D : PowerSeries ℤ := euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide)
  have hu : D * invOne D = 1 := mul_invOne (by simp [D, euler_const])
  have hGD : G * D = euler 6 (by decide) := by simpa [D, mul_assoc] using he
  change G = euler 6 (by decide) * invOne D
  rw [← hGD, mul_assoc, hu, mul_one]

theorem marked_count_coeff (k n : ℕ) :
    (markedCount k n : ℤ) = coeff n ((F : PowerSeries ℤ)^k) := by
  rw [← marked_series_eq_F, ← map_pow, coeff_map, marked_count_coeff_nat]
  rfl

end D5.S3.Combinatorics.Partitions.DesignatedSummands
