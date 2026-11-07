/- GID: D5/S3/ArithUnits/MercaQuarticMoments
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MercaQuarticMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral odd coordinates of the actual normalized quartic-character first moment. -/

import D5.S3.ArithUnits.MercaQuarticCharacter
import D5.S3.ArithUnits.MercaPrimeCharacterMoment
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Prod

/-!
Least representatives of units are positive. Sums here are integer sums of
those representatives, on the actual four ordered kernel cosets. No class
number is defined by a norm or finite sum in this module.
-/

set_option autoImplicit false
open scoped BigOperators Pointwise
noncomputable section

namespace D5.S3.ArithUnits.MercaQuarticMoments

open MercaQuarticCharacter MercaCosetFiberLift MercaPrimeCharacterMoment

/-- The unit represented by two, independently of its multiplicative order. -/
def twoUnit (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : (ZMod r)ˣ :=
  Units.mk0 2 (Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega)))

/-- The literal integer sum of least-positive representatives in `c K`. -/
def sumRep (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) (c : (ZMod r)ˣ) : ℤ :=
  ∑ u ∈ cosetFinset (kernel r hr) c, ((u : ZMod r).val : ℤ)

/-- The quotient is exact at conductors greater than five, as proved below. -/
def coordinate (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) (c : (ZMod r)ˣ) : ℤ :=
  2 * (sumRep r hr c / (r : ℤ)) - ((r - 1) / 4 : ℕ)

/-- Real coordinate, with the source orientation `chi(2)=i`. -/
def realCoordinate (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : ℤ :=
  coordinate r hr 1

/-- Imaginary coordinate, belonging to the coset `2 K`. -/
def imagCoordinate (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : ℤ :=
  coordinate r hr (twoUnit r hr)

/-- The actual first generalized Bernoulli value, on native unit representatives. -/
def bernoulli (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : ℂ :=
  characterMoment r (character r hr) / (r : ℂ)

private lemma coset_card (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (c : (ZMod r)ˣ) : (cosetFinset (kernel r hr) c).card = (r - 1) / 4 := by
  classical
  let e : cosetFinset (kernel r hr) c ≃
      (c • (kernel r hr : Set (ZMod r)ˣ) : Set (ZMod r)ˣ) :=
    Equiv.subtypeEquivRight (fun u => by simp [cosetFinset, mem_leftCoset_iff])
  have h := Nat.card_congr (e.trans (Subgroup.leftCosetEquivSubgroup c))
  rw [(kernel_structure r hr).2.2.2.2.2.1] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

private lemma representative_pos (r : ℕ) [Fact r.Prime] (_hr : r % 8 = 5)
    (u : (ZMod r)ˣ) : 0 < (u : ZMod r).val := by
  have hu : (u : ZMod r) ≠ 0 := Units.ne_zero u
  have hv : (u : ZMod r).val ≠ 0 := by
    intro h
    apply hu
    rw [← ZMod.natCast_zmod_val (u : ZMod r), h, Nat.cast_zero]
  omega

private lemma sumRep_dvd (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) (c : (ZMod r)ˣ) : (r : ℤ) ∣ sumRep r hr c := by
  classical
  let K := kernel r hr
  let C := cosetFinset K c
  have hcard : 1 < Nat.card K := by
    rw [show Nat.card K = (r - 1) / 4 from (kernel_structure r hr).2.2.2.2.2.1]
    omega
  have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨v, hv⟩ := exists_ne (1 : K)
  have hv' : (v : (ZMod r)ˣ) ≠ 1 := by
    intro h
    exact hv (Subtype.ext h)
  have hmem (u : (ZMod r)ˣ) : u ∈ C ↔ (v : (ZMod r)ˣ) * u ∈ C := by
    simp only [C, cosetFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show c⁻¹ * ((v : (ZMod r)ˣ) * u) =
      (v : (ZMod r)ˣ) * (c⁻¹ * u) by ac_rfl]
    exact (K.mul_mem_cancel_left v.property).symm
  let S : ZMod r := ∑ u ∈ C, (u : ZMod r)
  have hmul : (v.val : ZMod r) * S = S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    exact Finset.sum_equiv (Equiv.mulLeft (v : (ZMod r)ˣ)) hmem
      (fun _ _ => rfl)
  have hzero : S = 0 := by
    have hp : ((v.val : ZMod r) - 1) * S = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    rcases mul_eq_zero.mp hp with h | h
    · exact (hv' (Units.ext (sub_eq_zero.mp h))).elim
    · exact h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa [sumRep, S, C, Int.cast_sum, Int.cast_natCast,
    ZMod.natCast_zmod_val] using hzero

private lemma sumRep_neg (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (c : (ZMod r)ˣ) :
    sumRep r hr (-c) = (r : ℤ) * ((r - 1) / 4 : ℕ) - sumRep r hr c := by
  classical
  have hmem (u : (ZMod r)ˣ) :
      u ∈ cosetFinset (kernel r hr) c ↔ -u ∈ cosetFinset (kernel r hr) (-c) := by
    simp [cosetFinset]
  have heq : (∑ u ∈ cosetFinset (kernel r hr) c,
      (((-u : (ZMod r)ˣ) : ZMod r).val : ℤ)) = sumRep r hr (-c) :=
    Finset.sum_equiv (Equiv.neg (ZMod r)ˣ) hmem (fun _ _ => rfl)
  rw [← heq]
  calc
    _ = ∑ u ∈ cosetFinset (kernel r hr) c, ((r : ℤ) - (u : ZMod r).val) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Units.val_neg, ZMod.neg_val, ite_eq_right (Units.ne_zero u),
        Nat.cast_sub (ZMod.val_le _)]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, coset_card]
      dsimp [sumRep]
      ring

/-- Exact divisibility and complementation for every coset, and odd nonzero
integral coordinates. Divisibility uses a nonidentity element of the actual
kernel, which is available precisely after excluding conductor five. -/
theorem representative_properties (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) :
    (∀ u : (ZMod r)ˣ, 0 < (u : ZMod r).val ∧ (u : ZMod r).val < r) ∧
    ∀ c : (ZMod r)ˣ,
      (r : ℤ) ∣ sumRep r hr c ∧
      sumRep r hr (-c) = (r : ℤ) * ((r - 1) / 4 : ℕ) - sumRep r hr c ∧
      Odd (coordinate r hr c) ∧ coordinate r hr c ≠ 0 := by
  refine ⟨fun u => ⟨representative_pos r hr u, ZMod.val_lt _⟩, ?_⟩
  intro c
  have hm : (r - 1) / 4 % 2 = 1 := by omega
  have hc : Odd (coordinate r hr c) := by
    rw [Int.odd_iff]
    dsimp [coordinate]
    omega
  refine ⟨sumRep_dvd r hr hr5 c, sumRep_neg r hr c, hc, ?_⟩
  intro hz
  rw [hz, Int.odd_iff] at hc
  norm_num at hc

private lemma mem_coset_iff (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (c u : (ZMod r)ˣ) :
    u ∈ cosetFinset (kernel r hr) c ↔ character r hr u = character r hr c := by
  classical
  simp only [cosetFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    kernel, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
    Units.ext_iff, MulChar.coe_toUnitHom]
  exact eq_comm

private lemma fourth_values (z : ℂ) (hz : z ^ 4 = 1) :
    z = 1 ∨ z = Complex.I ∨ z = -1 ∨ z = -Complex.I := by
  have hs : z ^ 2 = 1 ∨ z ^ 2 = -1 :=
    sq_eq_one_iff.mp (by simpa only [← pow_mul] using hz)
  rcases hs with h | h
  · rcases sq_eq_one_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans Complex.I_sq.symm) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

private lemma moment_four_cosets (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    characterMoment r (character r hr) =
      (sumRep r hr 1 : ℂ) + Complex.I * (sumRep r hr (twoUnit r hr) : ℂ) -
      (sumRep r hr (-1) : ℂ) - Complex.I * (sumRep r hr (-twoUnit r hr) : ℂ) := by
  classical
  let f (c u : (ZMod r)ˣ) : ℂ :=
    if u ∈ cosetFinset (kernel r hr) c then ((u : ZMod r).val : ℂ) else 0
  have hf (c : (ZMod r)ˣ) : (∑ u, f c u) = (sumRep r hr c : ℂ) := by
    simp [f, sumRep]
  obtain ⟨horder, htwo, _, hodd, _, _, _, _⟩ := kernel_structure r hr
  have hfour : character r hr ^ 4 = 1 := horder ▸ pow_orderOf_eq_one _
  have htwoU : character r hr (twoUnit r hr) = Complex.I := by
    simpa only [twoUnit, Units.val_mk0] using htwo
  have hnegone : character r hr (-1 : ZMod r) = -1 := hodd
  have hnegtwo : character r hr (-(twoUnit r hr : ZMod r)) =
      -Complex.I := by
    rw [hodd.eval_neg, htwoU]
  calc
    _ = ∑ u : (ZMod r)ˣ,
        (f 1 u + Complex.I * f (twoUnit r hr) u - f (-1) u -
          Complex.I * f (-twoUnit r hr) u) := by
      apply Finset.sum_congr rfl
      intro u _
      have hu : character r hr u ^ 4 = 1 := by
        rw [← MulChar.pow_apply_coe, hfour, MulChar.one_apply_coe]
      rcases fourth_values _ hu with h | h | h | h <;>
        norm_num [f, mem_coset_iff, Units.val_neg, htwoU, hnegone, hnegtwo, h,
          Complex.ext_iff]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hf]

private lemma coordinate_scaled (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) (c : (ZMod r)ˣ) :
    (r : ℤ) * coordinate r hr c =
      2 * sumRep r hr c - (r : ℤ) * ((r - 1) / 4 : ℕ) := by
  dsimp only [coordinate]
  calc
    _ = 2 * (sumRep r hr c / (r : ℤ) * r) - (r : ℤ) * ((r - 1) / 4 : ℕ) := by ring
    _ = _ := by rw [Int.ediv_mul_cancel (sumRep_dvd r hr hr5 c)]

private lemma bernoulli_interval (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    bernoulli r hr =
      (∑ a ∈ Finset.Icc 1 (r - 1), (a : ℂ) * character r hr (a : ZMod r)) / r := by
  classical
  rw [bernoulli, character_moment_eq_zmod_sum]
  congr 1
  have hsum : (∑ a : ZMod r, (a.val : ℂ) * character r hr a) =
      ∑ a ∈ Finset.range r, (a : ℂ) * character r hr (a : ZMod r) := by
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro a _ b _ hab
      exact ZMod.val_injective r hab
    · intro a ha
      refine ⟨(a : ZMod r), Finset.mem_univ _, ?_⟩
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
    · intro a _
      rw [ZMod.natCast_zmod_val]
  rw [hsum]
  have hset : Finset.range r = insert 0 (Finset.Icc 1 (r - 1)) := by
    ext a
    have hp := (Fact.out : r.Prime).pos
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp

/-- The actual Bernoulli value has odd nonzero integer coordinates in the
ordered cosets `K, 2K, -K, -2K`. The interval expression and the analytic
L-value use the same actual character, not a supplied scalar. -/
theorem bernoulli_coordinates (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) :
    let k := realCoordinate r hr
    let t := imagCoordinate r hr
    bernoulli r hr = (k : ℂ) + (t : ℂ) * Complex.I ∧
    Odd k ∧ Odd t ∧ k ≠ 0 ∧ t ≠ 0 ∧
    (k : ℚ) = 2 * (sumRep r hr 1 : ℚ) / r - ((r - 1) / 4 : ℕ) ∧
    (t : ℚ) = 2 * (sumRep r hr (twoUnit r hr) : ℚ) / r - ((r - 1) / 4 : ℕ) ∧
    bernoulli r hr =
      (∑ a ∈ Finset.Icc 1 (r - 1), (a : ℂ) * character r hr (a : ZMod r)) / r ∧
    DirichletCharacter.LFunction (character r hr) 0 = -bernoulli r hr := by
  have hprops := representative_properties r hr hr5
  have hk := coordinate_scaled r hr hr5 1
  have ht := coordinate_scaled r hr hr5 (twoUnit r hr)
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
  have hB : bernoulli r hr =
      (realCoordinate r hr : ℂ) + (imagCoordinate r hr : ℂ) * Complex.I := by
    apply (div_eq_iff hr0).mpr
    rw [moment_four_cosets, sumRep_neg, sumRep_neg]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    have hkC : (r : ℂ) * (realCoordinate r hr : ℂ) =
        2 * (sumRep r hr 1 : ℂ) - (r : ℂ) * ((r - 1) / 4 : ℕ) := by
      have hc := congrArg (fun z : ℤ => (z : ℂ)) hk
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
        realCoordinate] using hc
    have htC : (r : ℂ) * (imagCoordinate r hr : ℂ) =
        2 * (sumRep r hr (twoUnit r hr) : ℂ) - (r : ℂ) * ((r - 1) / 4 : ℕ) := by
      have hc := congrArg (fun z : ℤ => (z : ℂ)) ht
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
        imagCoordinate] using hc
    calc
      _ = (2 * (sumRep r hr 1 : ℂ) - r * ((r - 1) / 4 : ℕ)) +
          Complex.I * (2 * (sumRep r hr (twoUnit r hr) : ℂ) - r * ((r - 1) / 4 : ℕ)) := by ring
      _ = _ := by rw [← hkC, ← htC]; ring
  have hquot (c : (ZMod r)ˣ) : (coordinate r hr c : ℚ) =
      2 * (sumRep r hr c : ℚ) / r - ((r - 1) / 4 : ℕ) := by
    have hs : (r : ℚ) * (coordinate r hr c : ℚ) =
        2 * (sumRep r hr c : ℚ) - (r : ℚ) * ((r - 1) / 4 : ℕ) := by
      have hc := congrArg (fun z : ℤ => (z : ℚ)) (coordinate_scaled r hr hr5 c)
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast] using hc
    have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff hrQ).mpr
    nlinarith [hs]
  have hχne : character r hr ≠ 1 := by
    intro h
    have ho := (kernel_structure r hr).1
    rw [h, orderOf_one] at ho
    norm_num at ho
  refine ⟨hB, (hprops.2 1).2.2.1, (hprops.2 (twoUnit r hr)).2.2.1,
    (hprops.2 1).2.2.2, (hprops.2 (twoUnit r hr)).2.2.2,
    hquot 1, hquot (twoUnit r hr), bernoulli_interval r hr, ?_⟩
  rw [D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum
      r (character r hr) hχne, ← character_moment_eq_zmod_sum]
  simp only [bernoulli, neg_div]

/-- The actual reduction preimage of the normalized character kernel. -/
def liftedKernel (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) (q : ℕ) :
    Subgroup (ZMod (r * q))ˣ :=
  (kernel r hr).comap (reduceUnits r q)

private def crtUnits (r q : ℕ) (h : Nat.Coprime r q) :
    (ZMod (r * q))ˣ ≃* (ZMod r)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

private lemma crtUnits_fst (r q : ℕ) (h : Nat.Coprime r q)
    (u : (ZMod (r * q))ˣ) : (crtUnits r q h u).1 = reduceUnits r q u := by
  apply Units.ext
  change (ZMod.cast (u : ZMod (r * q)) : ZMod r × ZMod q).1 = _
  rw [Prod.fst_zmod_cast]
  rfl

/-- The actual CRT identification of H with the kernel times the full second
unit group, with the first coordinate equal to reduction modulo r. -/
def liftedKernelEquiv (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (q : ℕ) (h : Nat.Coprime r q) :
    liftedKernel r hr q ≃* (kernel r hr) × (ZMod q)ˣ := by
  let E := crtUnits r q h
  have hfst (u : (ZMod (r * q))ˣ) : (E u).1 = reduceUnits r q u :=
    crtUnits_fst r q h u
  exact {
    toFun := fun u => (⟨(E u.val).1, by rw [hfst]; exact u.property⟩, (E u.val).2)
    invFun := fun v => ⟨E.symm (v.1.val, v.2), by
      change reduceUnits r q (E.symm (v.1.val, v.2)) ∈ kernel r hr
      rw [← hfst, E.apply_symm_apply]
      exact v.1.property⟩
    left_inv := fun u => by
      apply Subtype.ext
      exact E.symm_apply_apply u.val
    right_inv := fun v => by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst (E.apply_symm_apply (v.1.val, v.2))
      · change (E (E.symm (v.1.val, v.2))).2 = v.2
        exact congrArg Prod.snd (E.apply_symm_apply (v.1.val, v.2))
    map_mul' := fun u v => by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst (E.map_mul u.val v.val)
      · change (E (u.val * v.val)).2 = (E u.val).2 * (E v.val).2
        exact congrArg Prod.snd (E.map_mul u.val v.val) }

/-- The complete MMZ structural domain: cyclicity is exactly the coprimality
condition, and H has index four and omits minus one. -/
theorem lifted_structure (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (q : ℕ) [Fact q.Prime] (hqr : q ≠ r) :
    (IsCyclic (liftedKernel r hr q) ↔ Nat.Coprime ((r - 1) / 4) (q - 1)) ∧
    (liftedKernel r hr q).index = 4 ∧
    (-1 : (ZMod (r * q))ˣ) ∉ liftedKernel r hr q := by
  have hcop : Nat.Coprime q r := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (fun h => hqr ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : r.Prime)).mp h))
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  have hcyc := (liftedKernelEquiv r hr q hcop.symm).isCyclic
  rw [Group.isCyclic_prod_iff, (kernel_structure r hr).2.2.2.2.2.1, hcard] at hcyc
  have hcyc' : IsCyclic (liftedKernel r hr q) ↔ Nat.Coprime ((r - 1) / 4) (q - 1) := by
    simpa only [show IsCyclic (kernel r hr) from inferInstance,
      show IsCyclic (ZMod q)ˣ from inferInstance, true_and] using hcyc
  refine ⟨hcyc', ?_, ?_⟩
  · change ((kernel r hr).comap (reduceUnits r q)).index = 4
    rw [Subgroup.index_comap_of_surjective]
    · exact (kernel_structure r hr).2.2.2.2.2.2.1
    · exact ZMod.unitsMap_surjective _
  · intro hneg
    have hreduce : reduceUnits r q (-1 : (ZMod (r * q))ˣ) = -1 := by
      apply Units.ext
      change (ZMod.castHom (show r ∣ r * q from ⟨q, rfl⟩) (ZMod r)) (-1) = -1
      simp only [map_neg, map_one]
    have h : (-1 : (ZMod r)ˣ) ∈ kernel r hr := by
      change reduceUnits r q (-1) ∈ kernel r hr at hneg
      rwa [hreduce] at hneg
    exact (kernel_structure r hr).2.2.2.2.2.2.2 h

/-- The literal centered first moment of the subgroup itself. -/
def centered (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (q : ℕ) [Fact q.Prime] : Prop :=
  2 * (∑ u ∈ cosetFinset (liftedKernel r hr q) 1,
    ((u : ZMod (r * q)).val : ℤ)) =
    (r : ℤ) * q * (((r - 1) / 4 : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ)

private lemma sumRep_eq_of_character_eq (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (a b : (ZMod r)ˣ) (h : character r hr a = character r hr b) :
    sumRep r hr a = sumRep r hr b := by
  have hsets : cosetFinset (kernel r hr) a = cosetFinset (kernel r hr) b := by
    ext u
    rw [mem_coset_iff, mem_coset_iff, h]
  simp only [sumRep, hsets]

/-- The centered condition for the actual preimage subgroup, in the normalized
coordinates. This finite-character step works for every distinct prime q;
cyclic-generator eligibility imposes the additional MMZ hypotheses separately.
In particular no q>3 or q>r boundary is introduced. -/
theorem centered_coordinates (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) (q : ℕ) [Fact q.Prime] (hqr : q ≠ r) :
    Nat.card (liftedKernel r hr q) = (r - 1) / 4 * (q - 1) ∧
    (∀ u : (ZMod (r * q))ˣ,
      0 < (u : ZMod (r * q)).val ∧ (u : ZMod (r * q)).val < r * q) ∧
    (centered r hr q ↔ character r hr (q : ZMod r) = 1 ∨
      (realCoordinate r hr = imagCoordinate r hr ∧
        character r hr (q : ZMod r) = -Complex.I) ∨
      (realCoordinate r hr = -imagCoordinate r hr ∧
        character r hr (q : ZMod r) = Complex.I)) := by
  classical
  haveI : Fact (1 < r * q) := ⟨by nlinarith [(Fact.out : r.Prime).two_le,
    (Fact.out : q.Prime).two_le]⟩
  have hcop : Nat.Coprime q r := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (fun h => hqr ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : r.Prime)).mp h))
  let e : (ZMod r)ˣ := ZMod.unitOfCoprime q hcop
  have he : character r hr (e : ZMod r) = character r hr (q : ZMod r) := by
    simp [e]
  have hL : liftedFinset r q (cosetFinset (kernel r hr) 1) =
      cosetFinset (liftedKernel r hr q) 1 := by
    ext u
    simp [liftedFinset, cosetFinset, liftedKernel]
  have hlift := MercaCosetFiberLift.result r q (by omega)
    (Fact.out : q.Prime) hcop (kernel r hr) 1
  dsimp only at hlift
  have hc : Nat.card (liftedKernel r hr q) = (r - 1) / 4 * (q - 1) := by
    simpa only [liftedKernel, (kernel_structure r hr).2.2.2.2.2.1] using hlift.1
  have hcen : centered r hr q ↔ sumRep r hr 1 = sumRep r hr e⁻¹ := by
    have hdev := hlift.2.2.2.2.2
    change deviation (r * q) (liftedKernel r hr q)
      (liftedFinset r q (cosetFinset (kernel r hr) 1)) =
      (q : ℚ) * (moment r (cosetFinset (kernel r hr) 1) -
        moment r (cosetFinset (kernel r hr) (e⁻¹ * 1))) at hdev
    rw [hL, mul_one] at hdev
    have hsum (c : (ZMod r)ˣ) :
        moment r (cosetFinset (kernel r hr) c) = (sumRep r hr c : ℚ) := by
      simp [moment, sumRep]
    simp only [hsum] at hdev
    have hzero : centered r hr q ↔
        deviation (r * q) (liftedKernel r hr q)
          (cosetFinset (liftedKernel r hr q) 1) = 0 := by
      dsimp only [centered, deviation, moment]
      rw [hc]
      simp only [Nat.cast_mul]
      constructor
      · intro h
        have hh := congrArg (fun z : ℤ => (z : ℚ)) h
        simp only [Int.cast_mul, Int.cast_sum, Int.cast_natCast, Int.cast_ofNat] at hh
        linarith
      · intro h
        have hh : ((2 * (∑ u ∈ cosetFinset (liftedKernel r hr q) 1,
            ((u : ZMod (r * q)).val : ℤ))) : ℚ) =
            (((r : ℤ) * q * (((r - 1) / 4 : ℕ) : ℤ) *
              ((q - 1 : ℕ) : ℤ)) : ℚ) := by
          simp only [Int.cast_mul, Int.cast_sum, Int.cast_natCast, Int.cast_ofNat]
          linarith
        exact_mod_cast hh
    rw [hzero, hdev, mul_eq_zero]
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    simp only [hq0, false_or, sub_eq_zero, Int.cast_inj]
  have hchar : character r hr (e⁻¹ : (ZMod r)ˣ) *
      character r hr (q : ZMod r) = 1 := by
    have h := congrArg (fun u : (ZMod r)ˣ => character r hr (u : ZMod r))
      (inv_mul_cancel e)
    simpa only [Units.val_mul, map_mul, Units.val_one, map_one, he] using h
  have hs (c : (ZMod r)ˣ) : sumRep r hr 1 = sumRep r hr c ↔
      realCoordinate r hr = coordinate r hr c := by
    have h1 := coordinate_scaled r hr hr5 1
    have h2 := coordinate_scaled r hr hr5 c
    have hp : (0 : ℤ) < r := Nat.cast_pos.mpr (Fact.out : r.Prime).pos
    change sumRep r hr 1 = sumRep r hr c ↔
      coordinate r hr 1 = coordinate r hr c
    constructor
    · intro h
      dsimp only [coordinate]
      rw [h]
    · intro h
      rw [h] at h1
      linarith
  have hneg (c : (ZMod r)ˣ) : coordinate r hr (-c) = -coordinate r hr c := by
    have h1 := coordinate_scaled r hr hr5 (-c)
    have h2 := coordinate_scaled r hr hr5 c
    rw [sumRep_neg] at h1
    have hp : (0 : ℤ) < r := Nat.cast_pos.mpr (Fact.out : r.Prime).pos
    nlinarith
  obtain ⟨horder, htwo, _, hodd, _, _, _, _⟩ := kernel_structure r hr
  have hfour : character r hr ^ 4 = 1 := horder ▸ pow_orderOf_eq_one _
  have hqfour : character r hr (q : ZMod r) ^ 4 = 1 := by
    rw [← he, ← MulChar.pow_apply_coe, hfour, MulChar.one_apply_coe]
  have htwoU : character r hr (twoUnit r hr) = Complex.I := by
    simpa [twoUnit] using htwo
  have hminus : character r hr (-1 : ZMod r) = -1 := hodd
  have hminusTwo : character r hr (-twoUnit r hr : (ZMod r)ˣ) = -Complex.I := by
    simp only [Units.val_neg, hodd.eval_neg, htwoU]
  refine ⟨hc, ?_, ?_⟩
  · intro u
    have hu : (u : ZMod (r * q)).val ≠ 0 := by
      intro h
      exact Units.ne_zero u (by rw [← ZMod.natCast_zmod_val (u : ZMod (r * q)), h, Nat.cast_zero])
    exact ⟨by omega, ZMod.val_lt _⟩
  · rw [hcen]
    rcases fourth_values _ hqfour with h | h | h | h
    · have hei : character r hr (e⁻¹ : (ZMod r)ˣ) =
          character r hr (1 : (ZMod r)ˣ) := by
        rw [h, mul_one] at hchar
        simpa only [Units.val_one, map_one] using hchar
      have hsum := sumRep_eq_of_character_eq r hr e⁻¹ 1 hei
      simp only [h, hsum, true_or]
    · have hei : character r hr (e⁻¹ : (ZMod r)ˣ) =
          character r hr (-twoUnit r hr : (ZMod r)ˣ) := by
        rw [h] at hchar
        rw [hminusTwo]
        apply (mul_right_injective₀ Complex.I_ne_zero)
        change _ * _ = _ * _
        rw [mul_comm Complex.I, hchar]
        norm_num
      have hsum := sumRep_eq_of_character_eq r hr e⁻¹ (-twoUnit r hr) hei
      rw [hsum, hs, hneg]
      norm_num [h, Complex.ext_iff, imagCoordinate]
    · have hei : character r hr (e⁻¹ : (ZMod r)ˣ) =
          character r hr (-1 : (ZMod r)ˣ) := by
        rw [h] at hchar
        rw [show character r hr (-1 : (ZMod r)ˣ) = -1 from hminus]
        linear_combination -hchar
      have hsum := sumRep_eq_of_character_eq r hr e⁻¹ (-1) hei
      rw [hsum, hs, hneg]
      have hk := (bernoulli_coordinates r hr hr5).2.2.2.1
      have hne : realCoordinate r hr ≠ -realCoordinate r hr := by
        intro heq
        exact hk (by omega)
      norm_num [h, Complex.ext_iff]
      exact hne
    · have hei : character r hr (e⁻¹ : (ZMod r)ˣ) =
          character r hr (twoUnit r hr) := by
        rw [h] at hchar
        rw [htwoU]
        apply (mul_right_injective₀ (neg_ne_zero.mpr Complex.I_ne_zero))
        change _ * _ = _ * _
        rw [mul_comm (-Complex.I), hchar]
        norm_num
      have hsum := sumRep_eq_of_character_eq r hr e⁻¹ (twoUnit r hr) hei
      rw [hsum, hs]
      norm_num [h, imagCoordinate, Complex.ext_iff]

/-- Every generator on the eligible MMZ domain has representative a with
`gcd(a-1,r*q)=1`. Both local projection groups are genuinely nontrivial. -/
theorem generator_eligible (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) (q : ℕ) [Fact q.Prime] (hq2 : 2 < q) (hqr : q ≠ r)
    (a : liftedKernel r hr q) (hgen : ∀ x, x ∈ Subgroup.zpowers a) :
    Nat.Coprime ((a.val : ZMod (r * q)).val - 1) (r * q) := by
  haveI : Fact (1 < r * q) := ⟨by nlinarith⟩
  have hcop : Nat.Coprime q r := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (fun h => hqr ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : r.Prime)).mp h))
  let E := liftedKernelEquiv r hr q hcop.symm
  haveI : Nontrivial (kernel r hr) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [(kernel_structure r hr).2.2.2.2.2.1]; omega)
  haveI : Nontrivial (ZMod q)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]; omega)
  have projection_ne {G : Type} [Group G] [Nontrivial G]
      (f : liftedKernel r hr q →* G) (hf : Function.Surjective f) : f a ≠ 1 := by
    intro ha
    obtain ⟨b, hb⟩ := exists_ne (1 : G)
    obtain ⟨x, hx⟩ := hf b
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
    have h := congrArg f hj
    rw [map_zpow, ha, one_zpow, hx] at h
    exact hb h.symm
  have hfirst := projection_ne ((MonoidHom.fst _ _).comp E.toMonoidHom)
    (Prod.fst_surjective.comp E.surjective)
  have hsecond := projection_ne ((MonoidHom.snd _ _).comp E.toMonoidHom)
    (Prod.snd_surjective.comp E.surjective)
  let A := (a.val : ZMod (r * q)).val
  have hA : 1 ≤ A := ZMod.val_pos.mpr (Units.ne_zero a.val)
  have hAr : (A : ZMod r) ≠ 1 := by
    intro heq
    apply hfirst
    apply Subtype.ext
    apply Units.ext
    change ((crtUnits r q hcop.symm a.val).1 : ZMod r) = 1
    rw [crtUnits_fst]
    simpa only [reduceUnits, ZMod.unitsMap_val, ZMod.cast_eq_val] using heq
  have hAq : (A : ZMod q) ≠ 1 := by
    intro heq
    apply hsecond
    apply Units.ext
    change (ZMod.cast (a.val : ZMod (r * q)) : ZMod r × ZMod q).2 = 1
    rw [Prod.snd_zmod_cast, ZMod.cast_eq_val]
    exact heq
  have hru : IsUnit ((A - 1 : ℕ) : ZMod r) := by
    rw [Nat.cast_sub hA, Nat.cast_one]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hAr)
  have hqu : IsUnit ((A - 1 : ℕ) : ZMod q) := by
    rw [Nat.cast_sub hA, Nat.cast_one]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hAq)
  exact ((ZMod.isUnit_iff_coprime _ _).mp hru).mul_right
    ((ZMod.isUnit_iff_coprime _ _).mp hqu)

/-- Conjugation keeps the literal kernel and real coordinate, negates the
imaginary coordinate, and reverses the two nonreal centered branches. The
ordered cosets retain their representatives; their values become 1,-i,-1,i. -/
theorem conjugate_coordinates (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) :
    let χminus := star (character r hr)
    orderOf χminus = 4 ∧ χminus 2 = -Complex.I ∧
    χminus.toUnitHom.ker = kernel r hr ∧
    χminus (-1 : ZMod r) = -1 ∧
    χminus (-twoUnit r hr : (ZMod r)ˣ) = Complex.I ∧
    characterMoment r χminus / (r : ℂ) =
      (realCoordinate r hr : ℂ) + (-imagCoordinate r hr : ℤ) * Complex.I ∧
    ∀ (q : ℕ) [Fact q.Prime], q ≠ r →
      (centered r hr q ↔ χminus (q : ZMod r) = 1 ∨
        (realCoordinate r hr = imagCoordinate r hr ∧ χminus (q : ZMod r) = Complex.I) ∨
        (realCoordinate r hr = -imagCoordinate r hr ∧ χminus (q : ZMod r) = -Complex.I)) := by
  dsimp only
  obtain ⟨ho, ht, _, hodd, _, _, _, _⟩ := kernel_structure r hr
  have hker : (star (character r hr)).toUnitHom.ker = kernel r hr := by
    ext u
    simp only [kernel, MonoidHom.mem_ker, Units.ext_iff,
      MulChar.coe_toUnitHom, Units.val_one, MulChar.star_apply]
    exact ⟨fun h => by simpa only [star_star, star_one] using congrArg star h,
      fun h => by rw [h, star_one]⟩
  have hmoment : characterMoment r (star (character r hr)) / (r : ℂ) =
      star (bernoulli r hr) := by
    simp only [bernoulli, characterMoment, star_div₀, star_sum, star_mul,
      star_natCast, MulChar.star_apply, mul_comm]
  have hB := (bernoulli_coordinates r hr hr5).1
  have htwo : character r hr (twoUnit r hr) = Complex.I := by simpa [twoUnit] using ht
  refine ⟨?_, ?_, hker, ?_, ?_, ?_, ?_⟩
  · rw [MulChar.star_eq_inv, orderOf_inv, ho]
  · rw [MulChar.star_apply, ht]
    exact Complex.conj_I
  · rw [MulChar.star_apply, hodd]
    simp only [star_neg, star_one]
  · rw [MulChar.star_apply, Units.val_neg, hodd.eval_neg, htwo]
    simp
  · rw [hmoment, hB]
    simp only [star_add, star_mul, star_intCast, RCLike.star_def, Complex.conj_I,
      Int.cast_neg]
    ring
  · intro q _ hqr
    have h := (centered_coordinates r hr hr5 q hqr).2.2
    have hval (z : ℂ) : (star (character r hr)) (q : ZMod r) = star z ↔
        character r hr (q : ZMod r) = z := by
      rw [MulChar.star_apply]
      exact star_injective.eq_iff
    rw [← hval 1, ← hval (-Complex.I), ← hval Complex.I] at h
    simpa only [star_one, star_neg, RCLike.star_def, Complex.conj_I, neg_neg] using h

end D5.S3.ArithUnits.MercaQuarticMoments
