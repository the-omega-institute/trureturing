/- GID: D5/S3/Estimation/TimeArrow/ParityAffinityPerron
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ParityAffinityPerron
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity affinities give a unique scalar root and an explicit positive eigenvector. -/

import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.ParityAffinityPerron

open Finset Set
open D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates

/-- The vertices with prescribed real parity sign. -/
noncomputable def parityClass {d : ℕ} (p : ℝ) : Finset (Fin d → ℤˣ) :=
  Finset.univ.filter fun x => parity x = p

/-- The normalized cross product of the two square-root vectors on one parity class. -/
noncomputable def classAffinity {d : ℕ} (b : (Fin d → ℤˣ) → ℝ) (p : ℝ) : ℝ :=
  (∑ x ∈ parityClass p, √(1 - b x ^ 2)) / (2 : ℝ) ^ (d - 1)

/-- The positive-square-root vector supported on one parity class. -/
noncomputable def classU {d : ℕ} (b : (Fin d → ℤˣ) → ℝ) (p : ℝ)
    (x : Fin d → ℤˣ) : ℝ :=
  if parity x = p then √(1 + b x) else 0

/-- The negative-square-root vector supported on one parity class. -/
noncomputable def classV {d : ℕ} (b : (Fin d → ℤˣ) → ℝ) (p : ℝ)
    (x : Fin d → ℤˣ) : ℝ :=
  if parity x = p then √(1 - b x) else 0

/-- The geometric symmetrization of the parity kernel with profile `x ↦ parity x * b x`. -/
noncomputable def affinityKernel {d : ℕ} (b : (Fin d → ℤˣ) → ℝ)
    (x y : Fin d → ℤˣ) : ℝ :=
  √(parityKernel (fun w => parity w * b w) x y *
    parityKernel (fun w => parity w * b w) y x)

/-- The explicit four-vector Perron candidate associated with a positive scalar root. -/
noncomputable def affinityPerronVector {d : ℕ} (b : (Fin d → ℤˣ) → ℝ)
    (etaPlus etaMinus z : ℝ) (x : Fin d → ℤˣ) : ℝ :=
  (etaPlus * (etaMinus ^ 2 + z) / z) * classU b 1 x +
    (etaMinus * (z * (1 + z)) / z) * classU b (-1) x +
      (etaMinus ^ 2 + z) * classV b 1 x +
        (z * (1 + z)) * classV b (-1) x

/-- Positive affinities at most one determine one root in `(0,1]`, and no other positive root. -/
theorem affinityEquation_unique_root {etaPlus etaMinus : ℝ}
    (hetaPlus0 : 0 < etaPlus) (hetaPlus1 : etaPlus ≤ 1)
    (hetaMinus0 : 0 < etaMinus) (hetaMinus1 : etaMinus ≤ 1) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧
      z ^ 2 * (1 + z) ^ 2 = (z + etaPlus ^ 2) * (z + etaMinus ^ 2) ∧
      ∀ w : ℝ, 0 < w →
        w ^ 2 * (1 + w) ^ 2 = (w + etaPlus ^ 2) * (w + etaMinus ^ 2) → w = z := by
  let g : ℝ → ℝ := fun t =>
    t ^ 2 * (1 + t) ^ 2 - (t + etaPlus ^ 2) * (t + etaMinus ^ 2)
  have hetaPlusSq : 0 < etaPlus ^ 2 := sq_pos_of_pos hetaPlus0
  have hetaMinusSq : 0 < etaMinus ^ 2 := sq_pos_of_pos hetaMinus0
  have hetaPlusSqOne : etaPlus ^ 2 ≤ 1 := by nlinarith
  have hetaMinusSqOne : etaMinus ^ 2 ≤ 1 := by nlinarith
  have hg0 : g 0 < 0 := by
    dsimp [g]
    nlinarith [mul_pos hetaPlusSq hetaMinusSq]
  have hg1 : 0 ≤ g 1 := by
    dsimp [g]
    nlinarith [mul_nonneg (sub_nonneg.mpr hetaPlusSqOne) (sub_nonneg.mpr hetaMinusSqOne)]
  have hgContinuous : Continuous g := by
    dsimp [g]
    fun_prop
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hgContinuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (g 0) (g 1) from ⟨hg0.le, hg1⟩)
  obtain ⟨z, hzIcc, hgz⟩ := himage
  have hz0 : 0 < z := by
    by_contra hz
    have : z = 0 := le_antisymm (not_lt.mp hz) hzIcc.1
    subst z
    exact hg0.ne hgz
  have hzroot : z ^ 2 * (1 + z) ^ 2 =
      (z + etaPlus ^ 2) * (z + etaMinus ^ 2) := by
    exact sub_eq_zero.mp (by simpa [g] using hgz)
  let f : ℝ → ℝ := fun t =>
    t ^ 2 * (1 + t) ^ 2 / ((t + etaPlus ^ 2) * (t + etaMinus ^ 2))
  have hfactor : ∀ t : ℝ, 0 < t →
      f t = (t / (t + etaPlus ^ 2)) * (t / (t + etaMinus ^ 2)) * (1 + t) ^ 2 := by
    intro t ht
    have hp : t + etaPlus ^ 2 ≠ 0 := ne_of_gt (add_pos ht hetaPlusSq)
    have hm : t + etaMinus ^ 2 ≠ 0 := ne_of_gt (add_pos ht hetaMinusSq)
    dsimp [f]
    field_simp
  have hfStrict : StrictMonoOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hxp : 0 < x + etaPlus ^ 2 := add_pos hx hetaPlusSq
    have hyp : 0 < y + etaPlus ^ 2 := add_pos hy hetaPlusSq
    have hxm : 0 < x + etaMinus ^ 2 := add_pos hx hetaMinusSq
    have hym : 0 < y + etaMinus ^ 2 := add_pos hy hetaMinusSq
    have hp : x / (x + etaPlus ^ 2) < y / (y + etaPlus ^ 2) := by
      rw [div_lt_div_iff₀ hxp hyp]
      nlinarith
    have hm : x / (x + etaMinus ^ 2) < y / (y + etaMinus ^ 2) := by
      rw [div_lt_div_iff₀ hxm hym]
      nlinarith
    have hq : (1 + x) ^ 2 < (1 + y) ^ 2 := by nlinarith
    have hpx : 0 < x / (x + etaPlus ^ 2) := div_pos hx hxp
    have hpy : 0 < y / (y + etaPlus ^ 2) := div_pos hy hyp
    have hmx : 0 < x / (x + etaMinus ^ 2) := div_pos hx hxm
    have hmy : 0 < y / (y + etaMinus ^ 2) := div_pos hy hym
    have hqx : 0 < (1 + x) ^ 2 := sq_pos_of_pos (by linarith)
    have hqy : 0 < (1 + y) ^ 2 := sq_pos_of_pos (by linarith)
    rw [hfactor x hx, hfactor y hy]
    calc
      x / (x + etaPlus ^ 2) * (x / (x + etaMinus ^ 2)) * (1 + x) ^ 2 <
          y / (y + etaPlus ^ 2) * (x / (x + etaMinus ^ 2)) * (1 + x) ^ 2 := by
            exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hp hmx) hqx
      _ < y / (y + etaPlus ^ 2) * (y / (y + etaMinus ^ 2)) * (1 + x) ^ 2 := by
            exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hm hpy) hqx
      _ < y / (y + etaPlus ^ 2) * (y / (y + etaMinus ^ 2)) * (1 + y) ^ 2 := by
            exact mul_lt_mul_of_pos_left hq (mul_pos hpy hmy)
  have hfz : f z = 1 := by
    dsimp [f]
    rw [hzroot]
    exact div_self (mul_ne_zero (ne_of_gt (add_pos hz0 hetaPlusSq))
      (ne_of_gt (add_pos hz0 hetaMinusSq)))
  refine ⟨z, hz0, hzIcc.2, hzroot, ?_⟩
  intro w hw hwroot
  have hfw : f w = 1 := by
    dsimp [f]
    rw [hwroot]
    exact div_self (mul_ne_zero (ne_of_gt (add_pos hw hetaPlusSq))
      (ne_of_gt (add_pos hw hetaMinusSq)))
  exact hfStrict.injOn (by simpa) (by simpa) (hfw.trans hfz.symm)

#print axioms affinityEquation_unique_root

set_option maxHeartbeats 400000 in
-- The rank-four evaluation and the coefficient identities require extra elaboration work.
/-- The four-vector built from a positive affinity root is positive and is an eigenvector of the
geometrically symmetrized parity kernel. -/
theorem affinity_perronVector {d : ℕ} (hd : 1 ≤ d) (b : (Fin d → ℤˣ) → ℝ)
    (hb : ∀ x, |b x| < 1)
    (hzeroPlus : ∑ x ∈ parityClass 1, b x = 0)
    (hzeroMinus : ∑ x ∈ parityClass (-1), b x = 0)
    (etaPlus etaMinus z : ℝ)
    (hetaPlus : etaPlus = classAffinity b 1)
    (hetaMinus : etaMinus = classAffinity b (-1))
    (hz0 : 0 < z)
    (hzroot : z ^ 2 * (1 + z) ^ 2 =
      (z + etaPlus ^ 2) * (z + etaMinus ^ 2)) :
    (∀ x, 0 < affinityPerronVector b etaPlus etaMinus z x) ∧
      ∀ x, ∑ y, affinityKernel b x y *
          affinityPerronVector b etaPlus etaMinus z y =
        ((1 + z) / 2) * affinityPerronVector b etaPlus etaMinus z x := by
  classical
  have hparity : ∀ x : Fin d → ℤˣ, parity x = 1 ∨ parity x = -1 := by
    intro x
    unfold parity
    rcases Int.units_eq_one_or (∏ j, x j) with h | h <;> simp [h]
  have hrecord := subcoordinateLaw_eq (d := d) (fun _ => (1 : ℝ))
    (∅ : Finset (Fin d)) (by
      intro h
      let j : Fin d := ⟨0, hd⟩
      have : j ∈ (∅ : Finset (Fin d)) := h ▸ Finset.mem_univ _
      simp at this) 1 (fun _ _ => (1 : ℤˣ))
  unfold subcoordinateLaw at hrecord
  rw [← (Fin.snocEquiv (fun _ : Fin 2 => Fin d → ℤˣ)).sum_comp,
    Fintype.sum_prod_type] at hrecord
  simp [parityKernel] at hrecord
  have hone : (1 : Fin 2) = Fin.last 1 := rfl
  rw [hone] at hrecord
  simp only [Fin.snoc_last] at hrecord
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hrecord
  simp [Fintype.card_fin, Fintype.card_units_int] at hrecord
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hrecord
  have hcard : Fintype.card (Fin d → ℤˣ) = 2 ^ d := by
    simp [Fintype.card_fin, Fintype.card_units_int]
  rw [hcard] at hrecord
  have hpow : (2 : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow] at hrecord
  have hcast : ((2 ^ d : ℕ) : ℝ) = (2 : ℝ) ^ d := by norm_num
  rw [hcast] at hrecord
  have hParitySum : ∑ x : Fin d → ℤˣ, parity x = 0 := by linarith
  have hUnion : parityClass (d := d) 1 ∪ parityClass (-1) = Finset.univ := by
    ext x
    simp only [parityClass, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    exact hparity x
  have hDisjoint : Disjoint (parityClass (d := d) 1) (parityClass (-1)) := by
    rw [Finset.disjoint_left]
    intro x hx hxm
    have hp : parity x = 1 := by simpa [parityClass] using hx
    have hm : parity x = -1 := by simpa [parityClass] using hxm
    linarith
  have hSumPlus : ∑ x ∈ parityClass (d := d) 1, parity x =
      ((parityClass (d := d) 1).card : ℝ) := by
    calc
      _ = ∑ _x ∈ parityClass (d := d) 1, (1 : ℝ) := by
        exact Finset.sum_congr rfl fun x hx => by simpa [parityClass] using hx
      _ = _ := by simp
  have hSumMinus : ∑ x ∈ parityClass (d := d) (-1), parity x =
      -((parityClass (d := d) (-1)).card : ℝ) := by
    calc
      _ = ∑ _x ∈ parityClass (d := d) (-1), (-1 : ℝ) := by
        exact Finset.sum_congr rfl fun x hx => by simpa [parityClass] using hx
      _ = _ := by simp
  have hCardDifference : ((parityClass (d := d) 1).card : ℝ) -
      ((parityClass (d := d) (-1)).card : ℝ) = 0 := by
    have h := hParitySum
    rw [← hUnion, Finset.sum_union hDisjoint, hSumPlus, hSumMinus] at h
    exact h
  have hCardCube : Fintype.card (Fin d → ℤˣ) = 2 ^ d := by
    simp [Fintype.card_fin, Fintype.card_units_int]
  have hCardTotalNat : (parityClass (d := d) 1).card +
      (parityClass (d := d) (-1)).card = 2 ^ d := by
    rw [← Finset.card_union_of_disjoint hDisjoint, hUnion, Finset.card_univ, hCardCube]
  have hCardTotal : ((parityClass (d := d) 1).card : ℝ) +
      ((parityClass (d := d) (-1)).card : ℝ) = (2 : ℝ) ^ d := by
    exact_mod_cast hCardTotalNat
  have hPower : (2 : ℝ) ^ d = 2 * (2 : ℝ) ^ (d - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp [pow_succ]
    ring
  have hCardPlus : ((parityClass (d := d) 1).card : ℝ) = (2 : ℝ) ^ (d - 1) := by
    rw [hPower] at hCardTotal
    linarith
  have hCardMinus : ((parityClass (d := d) (-1)).card : ℝ) = (2 : ℝ) ^ (d - 1) := by
    rw [hPower] at hCardTotal
    linarith
  have hMne : (2 : ℝ) ^ (d - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  -- the class affinities are positive: each class is nonempty and every square root is positive
  have hetaPos : ∀ p : ℝ, ((parityClass (d := d) p).card : ℝ) = (2 : ℝ) ^ (d - 1) →
      0 < classAffinity b p := by
    intro p hp
    have hne : (parityClass (d := d) p).Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < ((parityClass (d := d) p).card : ℝ) := by rw [hp]; positivity
      exact_mod_cast this
    unfold classAffinity
    refine div_pos (Finset.sum_pos (fun x _ => Real.sqrt_pos.2 ?_) hne) (by positivity)
    have hx := abs_lt.mp (hb x)
    nlinarith
  have hetaPlus0 : 0 < etaPlus := hetaPlus ▸ hetaPos 1 hCardPlus
  have hetaMinus0 : 0 < etaMinus := hetaMinus ▸ hetaPos (-1) hCardMinus
  have hClassIdentities : ∀ p : ℝ,
      ((parityClass (d := d) p).card : ℝ) = (2 : ℝ) ^ (d - 1) →
      (∑ x ∈ parityClass p, b x = 0) →
      (∑ x, classU b p x * classU b p x = (2 : ℝ) ^ (d - 1)) ∧
        (∑ x, classV b p x * classV b p x = (2 : ℝ) ^ (d - 1)) ∧
        (∑ x, classU b p x * classV b p x =
          (2 : ℝ) ^ (d - 1) * classAffinity b p) := by
    intro p hCard hzero
    have hPlus : ∑ x ∈ parityClass p, (1 + b x) = (2 : ℝ) ^ (d - 1) := by
      rw [Finset.sum_add_distrib, hzero]
      simp [hCard]
    have hMinus : ∑ x ∈ parityClass p, (1 - b x) = (2 : ℝ) ^ (d - 1) := by
      rw [Finset.sum_sub_distrib, hzero]
      simp [hCard]
    have hSqrt : ∀ x, √(1 + b x) * √(1 - b x) = √(1 - b x ^ 2) := by
      intro x
      have hx := abs_lt.mp (hb x)
      rw [← Real.sqrt_mul (by linarith : 0 ≤ 1 + b x)]
      congr 1
      ring
    have hUU : ∑ x, classU b p x * classU b p x =
        ∑ x ∈ parityClass p, (1 + b x) := by
      unfold classU parityClass
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs
      · rw [Real.mul_self_sqrt]
        exact (by have := abs_lt.mp (hb x); linarith : 0 ≤ 1 + b x)
      · ring
    have hVV : ∑ x, classV b p x * classV b p x =
        ∑ x ∈ parityClass p, (1 - b x) := by
      unfold classV parityClass
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs
      · rw [Real.mul_self_sqrt]
        exact (by have := abs_lt.mp (hb x); linarith : 0 ≤ 1 - b x)
      · ring
    have hUV : ∑ x, classU b p x * classV b p x =
        ∑ x ∈ parityClass p, √(1 - b x ^ 2) := by
      unfold classU classV parityClass
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs
      · exact hSqrt x
      · ring
    refine ⟨hUU.trans hPlus, hVV.trans hMinus, hUV.trans ?_⟩
    unfold classAffinity
    field_simp [hMne]
  obtain ⟨hUUPlus, hVVPlus, hUVPlus⟩ :=
    hClassIdentities 1 hCardPlus hzeroPlus
  obtain ⟨hUUMinus, hVVMinus, hUVMinus⟩ :=
    hClassIdentities (-1) hCardMinus hzeroMinus
  rw [← hetaPlus] at hUVPlus
  rw [← hetaMinus] at hUVMinus
  have hVUPlus : ∑ x, classV b 1 x * classU b 1 x =
      (2 : ℝ) ^ (d - 1) * etaPlus := by
    simpa [mul_comm] using hUVPlus
  have hVUMinus : ∑ x, classV b (-1) x * classU b (-1) x =
      (2 : ℝ) ^ (d - 1) * etaMinus := by
    simpa [mul_comm] using hUVMinus
  have hKernel : ∀ x y, affinityKernel b x y =
      (classU b 1 x * classU b 1 y + classU b (-1) x * classU b (-1) y +
        classV b 1 x * classV b (-1) y + classV b (-1) x * classV b 1 y) /
        (2 : ℝ) ^ d := by
    intro x y
    rcases hparity x with hx | hx <;> rcases hparity y with hy | hy
    all_goals
      have hxp : 0 < 1 + b x := by have := abs_lt.mp (hb x); linarith
      have hxm : 0 < 1 - b x := by have := abs_lt.mp (hb x); linarith
      have hyp : 0 < 1 + b y := by have := abs_lt.mp (hb y); linarith
      have hym : 0 < 1 - b y := by have := abs_lt.mp (hb y); linarith
      have hden : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) _
    · simp only [affinityKernel, parityKernel, classU, classV, hx, hy, if_pos, if_neg,
        one_mul, neg_one_mul, mul_one, mul_neg, neg_neg]
      norm_num
      rw [show (1 + b x) / 2 ^ d * ((1 + b y) / 2 ^ d) =
          ((1 + b x) * (1 + b y)) / ((2 : ℝ) ^ d) ^ 2 by field_simp,
        Real.sqrt_div (mul_nonneg hxp.le hyp.le), Real.sqrt_sq_eq_abs,
        abs_of_pos hden, Real.sqrt_mul hxp.le]
    · simp only [affinityKernel, parityKernel, classU, classV, hx, hy, if_pos, if_neg,
        one_mul, neg_one_mul, mul_one, mul_neg, neg_neg]
      norm_num
      change √((1 - b x) / 2 ^ d * ((1 - b y) / 2 ^ d)) =
        √(1 - b x) * √(1 - b y) / 2 ^ d
      rw [show (1 - b x) / 2 ^ d * ((1 - b y) / 2 ^ d) =
          ((1 - b x) * (1 - b y)) / ((2 : ℝ) ^ d) ^ 2 by field_simp,
        Real.sqrt_div (mul_nonneg hxm.le hym.le), Real.sqrt_sq_eq_abs,
        abs_of_pos hden, Real.sqrt_mul hxm.le]
    · simp only [affinityKernel, parityKernel, classU, classV, hx, hy, if_pos, if_neg,
        one_mul, neg_one_mul, mul_one, mul_neg, neg_neg]
      norm_num
      change √((1 - b x) / 2 ^ d * ((1 - b y) / 2 ^ d)) =
        √(1 - b x) * √(1 - b y) / 2 ^ d
      rw [show (1 - b x) / 2 ^ d * ((1 - b y) / 2 ^ d) =
          ((1 - b x) * (1 - b y)) / ((2 : ℝ) ^ d) ^ 2 by field_simp,
        Real.sqrt_div (mul_nonneg hxm.le hym.le), Real.sqrt_sq_eq_abs,
        abs_of_pos hden, Real.sqrt_mul hxm.le]
    · simp only [affinityKernel, parityKernel, classU, classV, hx, hy, if_pos, if_neg,
        one_mul, neg_one_mul, mul_one, mul_neg, neg_neg]
      norm_num
      rw [show (1 + b x) / 2 ^ d * ((1 + b y) / 2 ^ d) =
          ((1 + b x) * (1 + b y)) / ((2 : ℝ) ^ d) ^ 2 by field_simp,
        Real.sqrt_div (mul_nonneg hxp.le hyp.le), Real.sqrt_sq_eq_abs,
        abs_of_pos hden, Real.sqrt_mul hxp.le]
  let aPlus := etaPlus * (etaMinus ^ 2 + z) / z
  let aMinus := etaMinus * (z * (1 + z)) / z
  let cPlus := etaMinus ^ 2 + z
  let cMinus := z * (1 + z)
  have hVector : ∀ x, affinityPerronVector b etaPlus etaMinus z x =
      aPlus * classU b 1 x + aMinus * classU b (-1) x +
        cPlus * classV b 1 x + cMinus * classV b (-1) x := by
    intro x
    rfl
  have hProduct : ∀ x y, affinityKernel b x y *
      affinityPerronVector b etaPlus etaMinus z y =
      ((((classU b 1 y * classU b 1 y) * aPlus +
          (classU b 1 y * classV b 1 y) * cPlus) * classU b 1 x +
        ((classU b (-1) y * classU b (-1) y) * aMinus +
          (classU b (-1) y * classV b (-1) y) * cMinus) * classU b (-1) x) +
        ((classV b (-1) y * classU b (-1) y) * aMinus +
          (classV b (-1) y * classV b (-1) y) * cMinus) * classV b 1 x +
        ((classV b 1 y * classU b 1 y) * aPlus +
          (classV b 1 y * classV b 1 y) * cPlus) * classV b (-1) x) /
        (2 : ℝ) ^ d := by
    intro x y
    rw [hKernel x y, hVector y]
    rcases hparity y with hy | hy
    · have huPlus : classU b 1 y = √(1 + b y) := by simp [classU, hy] <;> norm_num
      have huMinus : classU b (-1) y = 0 := by simp [classU, hy] <;> norm_num
      have hvPlus : classV b 1 y = √(1 - b y) := by simp [classV, hy] <;> norm_num
      have hvMinus : classV b (-1) y = 0 := by simp [classV, hy] <;> norm_num
      rw [huPlus, huMinus, hvPlus, hvMinus]
      ring
    · have huPlus : classU b 1 y = 0 := by simp [classU, hy] <;> norm_num
      have huMinus : classU b (-1) y = √(1 + b y) := by simp [classU, hy] <;> norm_num
      have hvPlus : classV b 1 y = 0 := by simp [classV, hy] <;> norm_num
      have hvMinus : classV b (-1) y = √(1 - b y) := by simp [classV, hy] <;> norm_num
      rw [huPlus, huMinus, hvPlus, hvMinus]
      ring
  have hAction : ∀ x, ∑ y, affinityKernel b x y *
      affinityPerronVector b etaPlus etaMinus z y =
      (1 / 2 : ℝ) *
        ((aPlus + etaPlus * cPlus) * classU b 1 x +
          (aMinus + etaMinus * cMinus) * classU b (-1) x +
          (etaMinus * aMinus + cMinus) * classV b 1 x +
          (etaPlus * aPlus + cPlus) * classV b (-1) x) := by
    intro x
    simp_rw [hProduct]
    rw [← Finset.sum_div]
    simp only [Finset.sum_add_distrib]
    simp_rw [← Finset.sum_mul]
    simp only [Finset.sum_add_distrib]
    simp_rw [← Finset.sum_mul]
    rw [hUUPlus, hUVPlus, hUUMinus, hUVMinus, hVUMinus, hVVMinus,
      hVUPlus, hVVPlus, hPower]
    field_simp [hMne]
  have hzNe : z ≠ 0 := ne_of_gt hz0
  have hCoeffAPlus : z * aPlus = etaPlus * cPlus := by
    dsimp [aPlus, cPlus]
    field_simp [hzNe]
  have hCoeffAMinus : z * aMinus = etaMinus * cMinus := by
    dsimp [aMinus, cMinus]
    field_simp [hzNe]
  have hCoeffCPlus : (1 + z) * cPlus = etaMinus * aMinus + cMinus := by
    dsimp [aMinus, cPlus, cMinus]
    field_simp [hzNe]
  have hCoeffCMinus : (1 + z) * cMinus = etaPlus * aPlus + cPlus := by
    dsimp [aPlus, cPlus, cMinus]
    field_simp [hzNe]
    linear_combination hzroot
  have hcPlus0 : 0 < cPlus := by
    dsimp [cPlus]
    nlinarith [sq_nonneg etaMinus]
  have hcMinus0 : 0 < cMinus := by
    dsimp [cMinus]
    positivity
  have haPlus0 : 0 < aPlus := by
    dsimp [aPlus]
    positivity
  have haMinus0 : 0 < aMinus := by
    dsimp [aMinus]
    positivity
  refine ⟨?_, ?_⟩
  · intro x
    rw [hVector x]
    rcases hparity x with hx | hx
    · simp [classU, classV, hx]
      have hsqrtPlus : 0 < √(1 + b x) := Real.sqrt_pos.2 (by
        have := abs_lt.mp (hb x); linarith)
      have hsqrtMinus : 0 < √(1 - b x) := Real.sqrt_pos.2 (by
        have := abs_lt.mp (hb x); linarith)
      positivity
    · simp [classU, classV, hx]
      have hsqrtPlus : 0 < √(1 + b x) := Real.sqrt_pos.2 (by
        have := abs_lt.mp (hb x); linarith)
      have hsqrtMinus : 0 < √(1 - b x) := Real.sqrt_pos.2 (by
        have := abs_lt.mp (hb x); linarith)
      positivity
  · intro x
    rw [hAction x, hVector x]
    rw [← hCoeffAPlus, ← hCoeffAMinus, ← hCoeffCPlus, ← hCoeffCMinus]
    ring

#print axioms affinity_perronVector

end D5.S3.Estimation.TimeArrow.ParityAffinityPerron
