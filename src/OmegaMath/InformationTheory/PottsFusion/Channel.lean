module

public import OmegaMath.InformationTheory.PottsFusion.Mixture
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Omega original.

Actual finite-channel bridge for the Potts fusion estimate.  A channel carries
its row-stochastic table together with an actual homomorphism from input
permutations to output permutations.  The posterior uses the uniform fallback
on a zero output column, so all displayed identities retain singular columns.

The local subadditivity conclusion is the finite-output form of Gu and
Polyanskiy, arXiv:2303.14688v2, Lemma 20. It uses the conditionally independent
outputs of one common uniform input.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace Omega.InformationTheory.PottsFusion

/-- A finite real channel with an actual fully-symmetric permutation action. -/
structure FMSChannel (I Y : Type*) [Fintype I] [Fintype Y] where
  table : I → Y → ℝ
  nonnegative : ∀ i y, 0 ≤ table i y
  row_stochastic : ∀ i, ∑ y, table i y = 1
  action : Equiv.Perm I →* Equiv.Perm Y
  action_preserves : ∀ σ i y, table (σ i) ((action σ) y) = table i y

namespace FMSChannel

variable {I Y Z : Type*} [Fintype I] [Fintype Y] [Fintype Z]

/-- The simultaneous product action on two output alphabets. -/
def productAction
    (a : Equiv.Perm I →* Equiv.Perm Y)
    (b : Equiv.Perm I →* Equiv.Perm Z) :
    Equiv.Perm I →* Equiv.Perm (Y × Z) :=
  { toFun := fun σ => (a σ).prodCongr (b σ)
    map_one' := by
      ext yz <;> simp
    map_mul' := by
      intro σ τ
      ext yz <;> simp [map_mul] }

/-- Product of two channels using conditionally independent outputs. -/
def star (P : FMSChannel I Y) (Q : FMSChannel I Z) : FMSChannel I (Y × Z) where
  table i yz := P.table i yz.1 * Q.table i yz.2
  nonnegative i yz := mul_nonneg (P.nonnegative i yz.1) (Q.nonnegative i yz.2)
  row_stochastic i := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, Q.row_stochastic,
      P.row_stochastic]
  action := productAction P.action Q.action
  action_preserves σ i yz := by
    simp [productAction, P.action_preserves, Q.action_preserves]

end FMSChannel

variable {I Y Z : Type*} [Fintype I] [Nonempty I] [Fintype Y] [Fintype Z]

/-- The uniform output margin of a finite channel column. -/
def channelMargin (P : I → Y → ℝ) (y : Y) : ℝ :=
  (∑ i, P i y) / (Fintype.card I : ℝ)

/-- The posterior at an output, with a uniform value on a zero-mass column. -/
def channelPosterior (P : I → Y → ℝ) (y : Y) (i : I) : ℝ :=
  if channelMargin P y = 0 then
    1 / (Fintype.card I : ℝ)
  else P i y / ((Fintype.card I : ℝ) * channelMargin P y)

/-- Ordinary finite chi-square capacity, with real division's `0 / 0 = 0`. -/
def channelCapacity (P : I → Y → ℝ) : ℝ :=
  (1 / (Fintype.card I : ℝ)) *
      (∑ y, (∑ i, (P i y) ^ 2) / channelMargin P y) - 1

/-- The capacity attached to an actual finite symmetric channel. -/
def FMSChannel.capacity (P : FMSChannel I Y) : ℝ := channelCapacity P.table

private lemma input_card_pos : 0 < (Fintype.card I : ℝ) := by
  exact_mod_cast Fintype.card_pos

private lemma input_card_ne : (Fintype.card I : ℝ) ≠ 0 :=
  ne_of_gt input_card_pos

omit [Nonempty I] in
private lemma sum_column_nonneg (P : FMSChannel I Y) (y : Y) :
    0 ≤ ∑ i, P.table i y :=
  Finset.sum_nonneg (fun i _ => P.nonnegative i y)

private lemma margin_nonneg (P : FMSChannel I Y) (y : Y) :
    0 ≤ channelMargin P.table y := by
  unfold channelMargin
  exact div_nonneg (sum_column_nonneg P y) input_card_pos.le

private lemma margin_sum_one (P : FMSChannel I Y) :
    ∑ y, channelMargin P.table y = 1 := by
  unfold channelMargin
  rw [← Finset.sum_div]
  rw [← Finset.sum_comm]
  simp only [P.row_stochastic, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  field_simp [input_card_ne]

private lemma zero_column_entry (P : FMSChannel I Y) (y : Y)
    (hy : channelMargin P.table y = 0) (i : I) : P.table i y = 0 := by
  have hsum : (∑ j, P.table j y) = 0 := by
    unfold channelMargin at hy
    exact (div_eq_zero_iff.mp hy).resolve_right input_card_ne
  have hle : P.table i y ≤ ∑ j, P.table j y :=
    Finset.single_le_sum (fun j _ => P.nonnegative j y) (Finset.mem_univ i)
  exact le_antisymm (by linarith [hle, hsum]) (P.nonnegative i y)

private lemma posterior_nonnegative (P : FMSChannel I Y) (y : Y) (i : I) :
    0 ≤ channelPosterior P.table y i := by
  unfold channelPosterior
  split
  · exact div_nonneg (by norm_num) input_card_pos.le
  · exact div_nonneg (P.nonnegative i y)
      (mul_nonneg input_card_pos.le (margin_nonneg P y))

private lemma posterior_sum_one (P : FMSChannel I Y) (y : Y) :
    ∑ i, channelPosterior P.table y i = 1 := by
  unfold channelPosterior
  by_cases hy : channelMargin P.table y = 0
  · simp [hy, input_card_ne]
  · simp only [hy, ↓reduceIte]
    rw [← Finset.sum_div]
    have hm : (∑ i, P.table i y) =
        (Fintype.card I : ℝ) * channelMargin P.table y := by
      unfold channelMargin
      field_simp
    rw [hm]
    field_simp [hy, input_card_ne]

private lemma weighted_posterior_capacity (P : FMSChannel I Y) (y : Y) :
    channelMargin P.table y * posteriorCapacity (channelPosterior P.table y) =
      (1 / (Fintype.card I : ℝ)) *
          ((∑ i, (P.table i y) ^ 2) / channelMargin P.table y) -
        channelMargin P.table y := by
  by_cases hy : channelMargin P.table y = 0
  · have hzero (i : I) := zero_column_entry P y hy i
    simp only [hy, div_zero, mul_zero, sub_zero]
    simp [hzero]
  · have hn := input_card_ne (I := I)
    unfold channelPosterior posteriorCapacity
    simp only [hy, ↓reduceIte]
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    field_simp [hy, hn] <;> ring

/-- Exact ordinary capacity equals the posterior-mixture capacity. -/
theorem capacity_eq_mixtureCapacity (P : FMSChannel I Y) :
    P.capacity =
      mixtureCapacity (channelMargin P.table)
        (channelPosterior P.table) := by
  unfold FMSChannel.capacity channelCapacity mixtureCapacity
  have hterm := fun y => weighted_posterior_capacity P y
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [margin_sum_one P]

/-- A raw product overlap, before posterior normalization. -/
def rawOverlap (P : FMSChannel I Y) (Q : FMSChannel I Z)
    (σ : Equiv.Perm I) (y : Y) (z : Z) : ℝ :=
  ∑ i, P.table i y * Q.table (σ i) z

/-- The corresponding raw squared overlap. -/
def rawOverlapSq (P : FMSChannel I Y) (Q : FMSChannel I Z)
    (σ : Equiv.Perm I) (y : Y) (z : Z) : ℝ :=
  ∑ i, (P.table i y * Q.table (σ i) z) ^ 2

private def rawRatio (P : FMSChannel I Y) (Q : FMSChannel I Z)
    (σ : Equiv.Perm I) (y : Y) (z : Z) : ℝ :=
  rawOverlapSq P Q σ y z / rawOverlap P Q σ y z

omit [Nonempty I] in
private lemma raw_ratio_reindex (P : FMSChannel I Y) (Q : FMSChannel I Z)
    (σ : Equiv.Perm I) :
    ∑ yz : Y × Z, rawRatio P Q σ yz.1 yz.2 =
      ∑ yz : Y × Z, rawRatio P Q 1 yz.1 yz.2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  have hz := Equiv.sum_comp (Q.action σ)
      (fun z => rawRatio P Q σ y z)
  calc
    ∑ z, rawRatio P Q σ y z =
        ∑ z, rawRatio P Q σ y ((Q.action σ) z) := by
          symm
          exact hz
    _ = ∑ z, rawRatio P Q 1 y z := by
      apply Finset.sum_congr rfl
      intro z _
      unfold rawRatio rawOverlap rawOverlapSq
      have hnum :
          (∑ i, (P.table i y * Q.table (σ i) ((Q.action σ) z)) ^ 2) =
            ∑ i, (P.table i y * Q.table i z) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Q.action_preserves σ i z]
      have hden :
          (∑ i, P.table i y * Q.table (σ i) ((Q.action σ) z)) =
            ∑ i, P.table i y * Q.table i z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Q.action_preserves σ i z]
      rw [hnum, hden]
      rfl

private lemma ratio_div_scale (a b k : ℝ) (hk : k ≠ 0) :
    (a / k ^ 2) / (b / k) = (a / b) / k := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [hb, hk] <;> ring

private lemma weighted_orbitFusion_raw (P : FMSChannel I Y) (Q : FMSChannel I Z)
    (y : Y) (z : Z) :
    channelMargin P.table y * channelMargin Q.table z *
        orbitFusion (channelPosterior P.table y)
          (channelPosterior Q.table z) =
      (𝔼 σ : Equiv.Perm I, rawRatio P Q σ y z) -
        channelMargin P.table y * channelMargin Q.table z := by
  by_cases hy : channelMargin P.table y = 0
  · have hp (i : I) := zero_column_entry P y hy i
    simp only [hy, zero_mul, sub_zero]
    symm
    apply Finset.expect_eq_zero
    intro σ _
    simp [rawRatio, rawOverlap, rawOverlapSq, hp]
  · by_cases hz : channelMargin Q.table z = 0
    · have hq (i : I) := zero_column_entry Q z hz i
      simp only [hz, mul_zero, zero_mul, sub_zero]
      symm
      apply Finset.expect_eq_zero
      intro σ _
      simp [rawRatio, rawOverlap, rawOverlapSq, hq]
    · let n : ℝ := Fintype.card I
      let a : ℝ := channelMargin P.table y
      let b : ℝ := channelMargin Q.table z
      let k : ℝ := (n * a) * (n * b)
      have hk : k ≠ 0 := mul_ne_zero
        (mul_ne_zero input_card_ne hy) (mul_ne_zero input_card_ne hz)
      have hcoefficient : a * b * n ^ 2 / k = 1 := by
        have h : a * b * n ^ 2 = k := by dsimp [k]; ring
        rw [h, div_self hk]
      have hpoint (σ : Equiv.Perm I) :
          a * b * (n ^ 2 *
            ((∑ i, (channelPosterior P.table y i *
                channelPosterior Q.table z (σ i)) ^ 2) /
              (∑ i, channelPosterior P.table y i *
                channelPosterior Q.table z (σ i))) - 1) =
            rawRatio P Q σ y z - a * b := by
        have hden : (∑ i, channelPosterior P.table y i *
            channelPosterior Q.table z (σ i)) = rawOverlap P Q σ y z / k := by
          simp only [channelPosterior, if_neg hy, if_neg hz]
          simp_rw [div_mul_div_comm]
          exact (Finset.sum_div _ _ _).symm
        have hnum : (∑ i, (channelPosterior P.table y i *
            channelPosterior Q.table z (σ i)) ^ 2) = rawOverlapSq P Q σ y z / k ^ 2 := by
          simp only [channelPosterior, if_neg hy, if_neg hz]
          simp_rw [div_mul_div_comm, div_pow]
          exact (Finset.sum_div _ _ _).symm
        rw [hnum, hden, ratio_div_scale _ _ _ hk]
        change a * b * (n ^ 2 * (rawRatio P Q σ y z / k) - 1) =
          rawRatio P Q σ y z - a * b
        calc
          _ = (a * b * n ^ 2 / k) * rawRatio P Q σ y z - a * b := by ring
          _ = _ := by rw [hcoefficient, one_mul]
      have hpointAvg := Finset.expect_congr (s := Finset.univ) rfl
        (fun σ _ => hpoint σ)
      change a * b * (n ^ 2 *
          (𝔼 σ : Equiv.Perm I,
            (∑ i, (channelPosterior P.table y i *
                channelPosterior Q.table z (σ i)) ^ 2) /
              (∑ i, channelPosterior P.table y i *
                channelPosterior Q.table z (σ i))) - 1) =
        (𝔼 σ : Equiv.Perm I, rawRatio P Q σ y z) - a * b
      simpa only [Finset.expect_sub_distrib, ← Finset.mul_expect,
        Fintype.expect_const] using hpointAvg

/-- Exact capacity of the product channel equals the orbit-mixture fusion. -/
theorem star_capacity_eq_mixtureFusion
    (P : FMSChannel I Y) (Q : FMSChannel I Z) :
    (P.star Q).capacity =
      mixtureFusion (channelMargin P.table) (channelPosterior P.table)
        (channelMargin Q.table) (channelPosterior Q.table) := by
  have hmargin (yz : Y × Z) :
      channelMargin (P.star Q).table yz =
        rawOverlap P Q 1 yz.1 yz.2 / (Fintype.card I : ℝ) := by
    unfold channelMargin rawOverlap FMSChannel.star
    simp only [Equiv.Perm.coe_one, id_eq]
  have hratio (yz : Y × Z) :
      (1 / (Fintype.card I : ℝ)) *
          (rawOverlapSq P Q 1 yz.1 yz.2 /
            channelMargin (P.star Q).table yz) =
        rawRatio P Q 1 yz.1 yz.2 := by
    rw [hmargin]
    unfold rawRatio
    by_cases hraw : rawOverlap P Q 1 yz.1 yz.2 = 0
    · simp [hraw]
    · field_simp [hraw, input_card_ne]
    
  have hcapacity_raw :
      (P.star Q).capacity =
        ∑ yz : Y × Z, rawRatio P Q 1 yz.1 yz.2 - 1 := by
    unfold FMSChannel.capacity channelCapacity
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun yz _ => hratio yz)

  have hmix :
      mixtureFusion (channelMargin P.table) (channelPosterior P.table)
          (channelMargin Q.table) (channelPosterior Q.table) =
        ∑ yz : Y × Z,
          ((𝔼 σ : Equiv.Perm I, rawRatio P Q σ yz.1 yz.2) -
            channelMargin P.table yz.1 * channelMargin Q.table yz.2) := by
    unfold mixtureFusion
    calc
      _ = ∑ z, ∑ y, channelMargin Q.table z *
            (channelMargin P.table y *
              orbitFusion (channelPosterior P.table y)
                (channelPosterior Q.table z)) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ y, ∑ z, channelMargin Q.table z *
            (channelMargin P.table y *
              orbitFusion (channelPosterior P.table y)
                (channelPosterior Q.table z)) := by
        rw [Finset.sum_comm]
      _ = ∑ yz : Y × Z, channelMargin Q.table yz.2 *
            (channelMargin P.table yz.1 *
              orbitFusion (channelPosterior P.table yz.1)
                (channelPosterior Q.table yz.2)) := by
        rw [Fintype.sum_prod_type]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro yz _
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          weighted_orbitFusion_raw P Q yz.1 yz.2

  rw [hmix]
  rw [Finset.sum_sub_distrib]
  have hexpect :
      (∑ yz : Y × Z, (𝔼 σ : Equiv.Perm I,
        rawRatio P Q σ yz.1 yz.2)) =
        ∑ yz : Y × Z, rawRatio P Q 1 yz.1 yz.2 := by
    rw [← Finset.expect_sum_comm]
    simp_rw [raw_ratio_reindex P Q]
    exact Fintype.expect_const _
  rw [hexpect]
  have hweights :
      (∑ y, channelMargin P.table y) *
          (∑ z, channelMargin Q.table z) = 1 := by
    rw [margin_sum_one P, margin_sum_one Q, one_mul]
  have hpair :
      (∑ yz : Y × Z,
          channelMargin P.table yz.1 * channelMargin Q.table yz.2) = 1 := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, hweights]
  rw [hpair]
  exact hcapacity_raw

/-- The actual finite-channel local estimate, with coefficient `8 q⁴ + q`. -/
theorem star_capacity_local_subadditivity
    (P : FMSChannel I Y) (Q : FMSChannel I Z) (ε : ℝ)
    (hε0 : 0 < ε) (hε : P.capacity ≤ ε) :
    (P.star Q).capacity ≤
      (1 + (8 * (Fintype.card I : ℝ) ^ 4 + (Fintype.card I : ℝ)) *
          Real.rpow ε (1 / 5)) * (P.capacity + Q.capacity) := by
  rw [star_capacity_eq_mixtureFusion, capacity_eq_mixtureCapacity P,
    capacity_eq_mixtureCapacity Q]
  apply mixture_fusion_local_subadditivity
    (w := channelMargin P.table) (p := channelPosterior P.table)
    (v := channelMargin Q.table) (r := channelPosterior Q.table) ε
  · intro y
    exact margin_nonneg P y
  · exact margin_sum_one P
  · intro z
    exact margin_nonneg Q z
  · exact margin_sum_one Q
  · intro y i
    exact posterior_nonnegative P y i
  · intro y
    exact posterior_sum_one P y
  · intro z i
    exact posterior_nonnegative Q z i
  · intro z
    exact posterior_sum_one Q z
  · exact hε0
  · simpa only [capacity_eq_mixtureCapacity] using hε

end Omega.InformationTheory.PottsFusion
