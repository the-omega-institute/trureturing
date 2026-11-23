/- GID: D5/S3/Combinatorics/Partitions/DesignatedSummands
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/DesignatedSummands
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.GenFun]
   utility: none
   digest: Ordered tuples of partitions with designated summands have an Euler product. -/

/-
admission_basis: escape-witness through marked_count_coeff and the weighted finite-product comparison
F_const proof_shape: bind-only
  escape_witness: none
  Consumers: coeff_seven_period, coefficient_formula_three
marked_count_coeff proof_shape: content
  escape_witness: the cardinalities of dependent marking choices and the weighted Euler-product comparison
tendsto_expand_discrete proof_shape: bind-only
  Consumers: euler_tendsto, hasSum_dilate
euler_tendsto proof_shape: bind-only
  Consumers: marked_series_eq_F, U_product, phi_product, psi_product, euler_pair_odd
euler_const proof_shape: bind-only
  Consumers: etaUnit, F_const, F_eq_unit, F_mul_den, coefficient_formula_three, exceptional_sharp
map_eta proof_shape: bind-only
  Consumers: H_dissection
expand_eta proof_shape: bind-only
  Consumers: H_dissection_rat, H_norm, W_factor
Escape registration: unfinished. See https://github.com/the-omega-institute/trureturing/issues/33480.

Direct frozen dependencies:
  none
-/

import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Section 2 and Definition 2.1 of Yaqubi and Mirzavaziri (arXiv:2611.05623v1). For each positive multiplicity, a finite index records the chosen occurrence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct

open Filter Finset _root_.PowerSeries
open scoped PowerSeries.WithPiTopology

theorem tendsto_expand_discrete {R : Type*} [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] (d : ℕ) (hd : d ≠ 0) :
    Continuous (expand d hd (R := R)) := by
  rename_i t _
  have ht : t = (⊥ : TopologicalSpace R) := DiscreteTopology.eq_bot
  subst t
  let : UniformSpace R := ⊥
  let : DiscreteUniformity R := ⟨rfl⟩
  simpa only [PowerSeries.expand, MvPowerSeries.expand, MvPowerSeries.coe_substAlgHom] using
    (MvPowerSeries.continuous_subst (R := R)
      (MvPowerSeries.HasSubst.X_pow (σ := Unit) (S := R) hd))

noncomputable def euler {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) : PowerSeries R :=
  expand d hd (PowerSeries.pentagonalSeries R)

theorem euler_tendsto {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (d : ℕ) (hd : d ≠ 0) :
    Tendsto (fun N => ∏ i ∈ Finset.range N, (1 - PowerSeries.X ^ (d * (i + 1)) : PowerSeries R))
      atTop (nhds (euler d hd)) := by
  have h := (tendsto_expand_discrete (R := R) d hd).continuousAt.tendsto.comp
    (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow R).tendsto_prod_nat
  simpa only [Function.comp_def, map_prod, map_sub, map_one, map_pow, expand_X,
    ← pow_mul, euler, Nat.mul_comm] using h

theorem euler_const {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) :
    constantCoeff (euler d hd : PowerSeries R) = 1 := by
  rw [euler, constantCoeff_expand, ← coeff_zero_eq_constantCoeff]
  conv_lhs => rw [← show pentagonal 0 = 0 by decide]
  rw [coeff_pentagonalSeries_pentagonal]
  simp

noncomputable def etaUnit {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) :
    (PowerSeries R)ˣ where
  val := euler d hd
  inv := invOfUnit (euler d hd) 1
  val_inv := mul_invOfUnit _ 1 (euler_const _ _)
  inv_val := by rw [mul_comm]; exact mul_invOfUnit _ 1 (euler_const _ _)

private theorem map_euler {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (d : ℕ) (hd : d ≠ 0) : (euler d hd).map g = euler d hd := by
  rw [euler, euler, map_expand]
  congr 1
  ext n
  classical
  simp only [coeff_map, pentagonalSeries, coeff_mk]
  split_ifs with h
  · simp only [Int.coe_negOnePow, map_pow, map_neg, map_one]
  · simp

theorem map_eta {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (d : ℕ) (hd : d ≠ 0) :
    Units.map (PowerSeries.map g).toMonoidHom (etaUnit d hd) = etaUnit d hd := by
  apply Units.ext
  exact map_euler g d hd

theorem expand_eta {R : Type*} [CommRing R] (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Units.map (expand a ha (R := R)).toMonoidHom (etaUnit b hb) =
      etaUnit (a*b) (Nat.mul_ne_zero ha hb) := by
  apply Units.ext
  exact (expand_mul a ha b hb _).symm

end D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct

namespace D5.S3.Combinatorics.Partitions.DesignatedSummands

open Filter Finset _root_.PowerSeries D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct
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

private theorem coeff_geom_sq {R : Type*} [CommRing R] (n : ℕ) :
    coeff n (invUnitsSub (1 : Rˣ) ^ 2) = (n : R) + 1 := by
  rw [pow_two, coeff_mul]
  simp [Nat.card_antidiagonal, Nat.cast_succ]

private noncomputable def markedFactor {R : Type*} [CommRing R] :
    PowerSeries R := 1 + PowerSeries.X * invUnitsSub (1 : Rˣ) ^ 2

private theorem markedFactor_identity {R : Type*} [CommRing R] :
    (markedFactor : PowerSeries R) * ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) *
      (1 - PowerSeries.X ^ 3)) = 1 - PowerSeries.X ^ 6 := by
  have hgeom : (1 - PowerSeries.X : PowerSeries R) * invUnitsSub (1 : Rˣ) = 1 := by
    simpa only [Units.val_one, map_one, mul_comm] using
      invUnitsSub_mul_sub (1 : Rˣ)
  have h : (markedFactor : PowerSeries R) * (1 - PowerSeries.X) ^ 2 =
      1 - PowerSeries.X + PowerSeries.X ^ 2 := by
    unfold markedFactor
    calc
      _ = (1 - PowerSeries.X) ^ 2 +
          (PowerSeries.X : PowerSeries R) * (((1 - PowerSeries.X) * invUnitsSub (1 : Rˣ)) ^ 2) := by ring
      _ = _ := by rw [hgeom]; ring
  calc
    _ = ((markedFactor : PowerSeries R) * (1 - PowerSeries.X) ^ 2) *
        ((1 + PowerSeries.X) * (1 - PowerSeries.X ^ 3)) := by ring
    _ = _ := by rw [h]; ring

noncomputable def F {R : Type*} [CommRing R] : PowerSeries R :=
  euler 6 (by decide) * invOfUnit (euler 1 (by decide) * euler 2 (by decide) * euler 3 (by decide)) 1

theorem F_const {R : Type*} [CommRing R] : constantCoeff (F : PowerSeries R) = 1 := by
  simp [F, constantCoeff_invOfUnit, euler_const]

private local instance : TopologicalSpace ℤ := ⊥
private local instance : DiscreteTopology ℤ := ⟨rfl⟩
private local instance : TopologicalSpace ℕ := ⊥
private local instance : DiscreteTopology ℕ := ⟨rfl⟩

private theorem markedFactor_hasSum (d : ℕ) (hd : d ≠ 0) :
    HasSum (fun j : ℕ => ((j : ℤ) + 1) • (PowerSeries.X : PowerSeries ℤ) ^ (d * (j + 1)))
      (expand d hd ((markedFactor : PowerSeries ℤ) - 1)) := by
  have h := (invUnitsSub (1 : ℤˣ) ^ 2).hasSum_of_monomials_self
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
  have hu : D * invOfUnit D 1 = 1 := mul_invOfUnit D 1 (by simp [D, euler_const])
  have hGD : G * D = euler 6 (by decide) := by simpa [D, mul_assoc] using he
  change G = euler 6 (by decide) * invOfUnit D 1
  rw [← hGD, mul_assoc, hu, mul_one]

theorem marked_count_coeff (k n : ℕ) :
    (markedCount k n : ℤ) = coeff n ((F : PowerSeries ℤ)^k) := by
  rw [← marked_series_eq_F, ← map_pow, coeff_map, marked_count_coeff_nat]
  rfl

end D5.S3.Combinatorics.Partitions.DesignatedSummands
