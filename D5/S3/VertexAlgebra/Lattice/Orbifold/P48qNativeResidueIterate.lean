/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeResidueIterate
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fractional residue iteration and its negative-current, charged-ground case. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct
import D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate

/-! Fractional transport of the ordinary residue iterate on the threefold cover. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
open OrdinaryResidueIterate (residue_iterate alternating_iterate_weight)
open BinomialKernelDelta (chooseSign)
open StateFieldResidueReconstruction (epsilon)
open LatticeHalfFockGroundRightCurrentTransport.Calculus (R Z Valid)

noncomputable section
private def chooseAt (a : ℂ) (j : ℤ) : ℂ :=
  if 0 ≤ j then Ring.choose a j.toNat else 0

private def signedAt (a : ℂ) (j : ℤ) : ℂ :=
  (-1 : ℂ) ^ j * chooseAt a j
private theorem chooseAt_nat (a : ℂ) (j : ℕ) :
    chooseAt a (j : ℤ) = Ring.choose a j := by simp [chooseAt]
private theorem signedAt_nat (a : ℂ) (j : ℕ) :
    signedAt a (j : ℤ) = (-1 : ℂ)^j * Ring.choose a j := by
  rw [signedAt, chooseAt_nat, zpow_natCast]

private theorem signedAt_int_nat (m : ℤ) (j : ℕ) :
    signedAt (m : ℂ) (j : ℤ) = chooseSign m j := by
  rw [signedAt_nat, chooseSign]
  congr 1
  exact (Ring.map_choose (Int.castRingHom ℂ) m j).symm

private theorem signedAt_reflect (a : ℂ) (j : ℤ) :
    signedAt a j = chooseAt ((j : ℂ) - a - 1) j := by
  by_cases hj : 0 ≤ j
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [signedAt_nat, chooseAt_nat, Int.cast_natCast,
      show (n : ℂ) - a - 1 = - (a - n + 1) by ring, Ring.choose_neg,
      Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_eq_mul,
      show a - (n : ℂ) + 1 + n - 1 = a by ring]
  · simp [signedAt, chooseAt, hj]

private theorem translatedVandermonde (a : ℂ) (k : ℕ) (j : ℤ) :
    (∑ p ∈ Finset.range (k + 1), (k.choose p : ℂ) * chooseAt a (j + p)) =
      chooseAt (a + k) (j + k) := by
  by_cases hj : 0 ≤ j + (k : ℤ)
  · let r := (j + (k : ℤ)).toNat
    have hr : (r : ℤ) = j + k := Int.toNat_of_nonneg hj
    rw [← hr, chooseAt_nat, add_comm a, Ring.add_choose_eq r (Commute.all _ _),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Finset.sum_range_reflect]
    let f (p : ℕ) := (k.choose p : ℂ) * chooseAt a ((r : ℤ) - p)
    calc
      _ = ∑ p ∈ Finset.range (k+1), f p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' : p ≤ k := by simpa [Finset.mem_range] using hp
        simp only [Nat.add_sub_cancel, f, Nat.choose_symm hp', Int.natCast_sub hp']
        congr 2
        omega
      _ = ∑ p ∈ Finset.range (max k r + 1), f p := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro p _ hp
        simp [f, Nat.choose_eq_zero_of_lt (by simpa [Finset.mem_range] using hp : k < p)]
      _ = ∑ p ∈ Finset.range (r+1), f p := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro p _ hp
        have hpr : ¬ 0 ≤ (r : ℤ) - p := by simp only [Finset.mem_range] at hp; omega
        change (k.choose p : ℂ) * chooseAt a ((r : ℤ) - p) = 0
        rw [chooseAt, ite_eq_right hpr, mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpr : p ≤ r := by simpa [Finset.mem_range] using hp
        change (k.choose p : ℂ) * chooseAt a ((r : ℤ) - p) = _
        rw [Ring.choose_natCast, ← Int.natCast_sub hpr, chooseAt_nat]
  · rw [chooseAt, ite_eq_right hj]
    exact Finset.sum_eq_zero fun p hp => by
      have h : ¬ 0 ≤ j + (p : ℤ) := by simp only [Finset.mem_range] at hp; omega
      simp [chooseAt, h]

/-- The first ordered term, with zero extension for negative binomial indices. -/
private theorem forwardKernel (a : ℂ) (k : ℕ) (j : ℤ) :
    (∑ p ∈ Finset.range (k + 1), (k.choose p : ℂ) * signedAt (a + p) (j + p)) =
      signedAt a (j + k) := by
  simp_rw [signedAt_reflect]
  push_cast
  have h (p : ℕ) : (j : ℂ) + p - (a + p) - 1 = (j : ℂ) - a - 1 := by ring
  simp_rw [h]
  rw [translatedVandermonde]
  congr 1
  ring

/-- The second ordered term, including its zero extension below the shift. -/
private theorem reverseKernel (a : ℂ) (k : ℕ) (j : ℕ) :
    (∑ p ∈ Finset.range (k + 1),
      ((-1 : ℂ)^p * (k.choose p : ℂ)) * Ring.choose (a+p) j) =
      (-1 : ℂ)^k * chooseAt a ((j : ℤ) - k) := by
  rw [alternating_iterate_weight, chooseAt]
  simp only [show 0 ≤ (j : ℤ) - k ↔ k ≤ j by omega,
    show ((j : ℤ) - k).toNat = j-k by omega]

private def leftWeight (a b : ℂ) (d p : ℕ) : ℂ :=
  Ring.choose a p * Ring.choose (a + b - p) (d - p)
private def rightWeight (a b : ℂ) (d k : ℕ) : ℂ :=
  Ring.choose a k * Ring.choose b (d - k)

private theorem leftWeight_expand (a b : ℂ) {d p : ℕ} (hp : p ≤ d) :
    leftWeight a b d p =
      ∑ k ∈ Finset.Ico p (d+1), rightWeight a b d k * (k.choose p : ℂ) := by
  rw [leftWeight, show a + b - p = (a - p) + b by ring,
    Ring.add_choose_eq (d-p) (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum,
    Finset.sum_Ico_eq_sum_range, show d+1-p = d-p+1 by omega]
  apply Finset.sum_congr rfl
  intro i hi
  have hip : p ≤ p+i := Nat.le_add_right _ _
  have ha := Ring.choose_smul_choose a hip
  simp only [nsmul_eq_mul, Nat.add_sub_cancel_left] at ha
  change Ring.choose a p * (Ring.choose (a-p) i * Ring.choose b (d-p-i)) = _
  rw [rightWeight, show d - (p+i) = d-p-i by omega, ← mul_assoc, ← ha]
  ring

/-- Change from the two left strip shifts to the two right strip shifts at degree d. -/
private theorem changeWeight {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (a b : ℂ) (d : ℕ) (f : ℕ → M) :
    (∑ p ∈ Finset.range (d+1), leftWeight a b d p • f p) =
      ∑ k ∈ Finset.range (d+1), rightWeight a b d k •
        ∑ p ∈ Finset.range (k+1), (k.choose p : ℂ) • f p := by
  rw [← Nat.Ico_zero_eq_range]
  calc
    _ = ∑ p ∈ Finset.Ico 0 (d+1), ∑ k ∈ Finset.Ico p (d+1),
          rightWeight a b d k • ((k.choose p : ℂ) • f p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [leftWeight_expand a b (by simpa using (Finset.mem_Ico.mp hp).2), Finset.sum_smul]
      simp only [smul_smul]
    _ = _ := by
      rw [Finset.sum_Ico_Ico_comm]
      simp only [Nat.Ico_zero_eq_range, Finset.smul_sum]

private theorem sum_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (D K : ℕ) (h : ∀ j < D, f j = 0) :
    (∑ j ∈ Finset.range (K-D), f (D+j)) = ∑ j ∈ Finset.range K, f j := by
  rw [← Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  · intro j hj hj'
    exact h j (by simp only [Finset.mem_range] at hj; simp only [Finset.mem_Ico] at hj'; omega)

private theorem signedAt_neg (a : ℂ) {j : ℤ} (hj : j < 0) : signedAt a j = 0 := by
  rw [signedAt, chooseAt, ite_eq_right (by omega), mul_zero]

private theorem weighted_forward {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (a b : ℂ) (m : ℤ) (d K : ℕ) (F : ℕ → M) :
    (∑ p ∈ Finset.range (d+1), leftWeight a b d p •
      ∑ j ∈ Finset.range (K-(d-p)), chooseSign (m+p) j • F (d-p+j)) =
    ∑ k ∈ Finset.range (d+1), rightWeight a b d k •
      ∑ i ∈ Finset.range (K-(d-k)), chooseSign m i • F (d-k+i) := by
  have pad (r : ℤ) (p : ℕ) (hp : p ≤ d) :
      (∑ j ∈ Finset.range (K-(d-p)), chooseSign r j • F (d-p+j)) =
      ∑ l ∈ Finset.range K, signedAt (r : ℂ) ((l : ℤ)-d+p) • F l := by
    rw [← sum_shift _ (d-p) K]
    · apply Finset.sum_congr rfl
      intro j _
      rw [show (((d-p+j : ℕ) : ℤ)-d+p) = j by rw [Nat.cast_add, Int.natCast_sub hp]; omega,
        signedAt_int_nat]
    · intro l hl
      rw [signedAt_neg _ (by omega), zero_smul]
  calc
    _ = ∑ p ∈ Finset.range (d+1), leftWeight a b d p •
        ∑ l ∈ Finset.range K, signedAt ((m : ℂ)+p) ((l : ℤ)-d+p) • F l := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pad (m+p) p (by simpa using hp), Int.cast_add, Int.cast_natCast]
    _ = _ := by
      rw [changeWeight]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      rw [pad m k (by simpa using hk)]
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_smul, forwardKernel]

private theorem reverse_signed_left (m : ℤ) (p j : ℕ) :
    -epsilon (m+p) * chooseSign (m+p) j =
      (-epsilon m * (-1 : ℂ)^j) * ((-1 : ℂ)^p * Ring.choose ((m : ℂ)+p) j) := by
  rw [← signedAt_int_nat, signedAt_nat]
  simp only [epsilon, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast,
    Int.cast_add, Int.cast_natCast]
  ring

private theorem weighted_reverse {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (a b : ℂ) (m : ℤ) (d L : ℕ) (F : ℕ → M) :
    (∑ p ∈ Finset.range (d+1), leftWeight a b d p •
      ∑ j ∈ Finset.range L, (-epsilon (m+p) * chooseSign (m+p) j) • F j) =
    ∑ k ∈ Finset.range (d+1), rightWeight a b d k •
      ∑ i ∈ Finset.range (L-k), (-epsilon m * chooseSign m i) • F (k+i) := by
  rw [changeWeight]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp_rw [reverse_signed_left, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have he (j : ℕ) : (∑ p ∈ Finset.range (k+1),
      (k.choose p : ℂ) * ((-epsilon m * (-1 : ℂ)^j) *
        ((-1 : ℂ)^p * Ring.choose ((m : ℂ)+p) j))) =
      (-epsilon m * (-1 : ℂ)^j) * ((-1 : ℂ)^k * chooseAt (m : ℂ) ((j : ℤ)-k)) := by
    rw [← reverseKernel, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  simp_rw [← Finset.sum_smul, he]
  let g (j : ℕ) := ((-epsilon m * (-1 : ℂ)^j) *
    ((-1 : ℂ)^k * chooseAt (m : ℂ) ((j : ℤ)-k))) • F j
  change (∑ j ∈ Finset.range L, g j) = _
  rw [← sum_shift g k L]
  · apply Finset.sum_congr rfl
    intro i _
    dsimp only [g]
    congr 1
    simp only [Nat.cast_add, add_sub_cancel_left, chooseAt_nat, ← signedAt_int_nat, signedAt_nat,
      pow_add]
    have hh : (-1 : ℂ)^k * (-1 : ℂ)^k = 1 := by rw [← mul_pow]; norm_num
    linear_combination ((-epsilon m) * (-1 : ℂ)^i * Ring.choose (m : ℂ) i) * hh
  · intro j hj
    dsimp only [g]
    rw [chooseAt, ite_eq_right (by omega), mul_zero, mul_zero, zero_smul]

open FieldNormalProductLocality (delta)
open SignedFieldNormalProductLocality (signedComm)
open P48qNativeCurrentLocality (Field InResidue CoverLocal coverDelta coverComm stripResidue
  restoreResidue coverDelta_comm_eq_zero_iff)
open P48qNativeResidueProduct (adjustedResidue adjustedResidue_coeff clearedResidue)
open private Z_smul Z_sum Z_Z Z_zero from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange
open private R_sum R_smul R_Z R_zero from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private R_sub_first R_smul_first residue_vanishes sum_range_change from
  D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem residue_iterate_degree (J A B : VertexOperator ℂ V) (a b : ℂ)
    (m n : ℤ) (K L d : ℕ)
    (hAB : delta^[K] (signedComm 1 A B) = 0)
    (hJB : delta^[L] (signedComm 1 J B) = 0) :
    (∑ p ∈ Finset.range (d+1), leftWeight a b d p •
      R (R J A (m+p)) B (n+(d-p : ℕ))) =
    (∑ k ∈ Finset.range (d+1), rightWeight a b d k •
      ∑ i ∈ Finset.range (((K : ℤ)-n).toNat-(d-k)),
        chooseSign m i • R J (R A B (n+i+(d-k : ℕ))) (m-i+k)) +
    (∑ k ∈ Finset.range (d+1), rightWeight a b d k •
      ∑ i ∈ Finset.range (L-k),
        (-epsilon m * chooseSign m i) • R A (R J B ((k : ℤ)+i))
          (m+n-i+(d-k : ℕ))) := by
  have expand (p : ℕ) := residue_iterate J A B K L hAB hJB (m+p) (n+(d-p : ℕ))
  simp_rw [expand, smul_add, Finset.sum_add_distrib]
  congr 1
  · let F (l : ℕ) := R J (R A B (n+l)) (m+(d : ℤ)-l)
    have he (k i : ℕ) (hk : k ≤ d) : n+(i : ℤ)+(d-k : ℕ) = n+(d-k+i : ℕ) := by
      push_cast; omega
    calc
      _ = ∑ p ∈ Finset.range (d+1), leftWeight a b d p •
          ∑ i ∈ Finset.range (((K : ℤ)-n).toNat-(d-p)),
            chooseSign (m+p) i • F (d-p+i) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' : p ≤ d := by simpa using hp
        rw [show ((K : ℤ)-(n+(d-p : ℕ))).toNat = ((K : ℤ)-n).toNat-(d-p) by omega]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp only [F, Nat.cast_add]
        rw [Int.natCast_sub hp']
        rw [show n + ((d : ℤ) - p) + i = n + ((d : ℤ) - p + i) by omega,
          show m + (p : ℤ) - i = m + (d : ℤ) - ((d : ℤ) - p + i) by omega]
      _ = _ := by
        rw [weighted_forward]
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have hk' : k ≤ d := by simpa using hk
        rw [he k i hk']
        simp only [F, Nat.cast_add]
        rw [Int.natCast_sub hk']
        congr 2
        omega
  · let F (j : ℕ) := R A (R J B (j : ℤ)) (m+n+d-j)
    calc
      _ = ∑ p ∈ Finset.range (d+1), leftWeight a b d p •
          ∑ j ∈ Finset.range L, (-epsilon (m+p) * chooseSign (m+p) j) • F j := by
        apply Finset.sum_congr rfl
        intro p hp
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        have hp' : p ≤ d := by simpa using hp
        simp only [F]
        rw [Int.natCast_sub hp']
        congr 2
        omega
      _ = _ := by
        rw [weighted_reverse]
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have hk' : k ≤ d := by simpa using hk
        simp only [F, Nat.cast_add]
        rw [Int.natCast_sub hk']
        congr 2
        omega

private theorem triangle {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (D : ℕ) :
    (∑ p ∈ Finset.range D, ∑ q ∈ Finset.range (D-p), f p q) =
      ∑ d ∈ Finset.range D, ∑ p ∈ Finset.range (d+1), f p (d-p) := by
  calc
    _ = ∑ p ∈ Finset.Ico 0 D, ∑ d ∈ Finset.Ico p D, f p (d-p) := by
      rw [Nat.Ico_zero_eq_range]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
    _ = _ := by
      rw [Finset.sum_Ico_Ico_comm]
      simp only [Nat.Ico_zero_eq_range]

private theorem signedComm_one (X Y : VertexOperator ℂ V) :
    signedComm 1 X Y = FieldNormalProductLocality.commutator X Y := by
  funext i j
  simp [signedComm, FieldNormalProductLocality.commutator]

private theorem stripLocality (s t : ℤ) (A B : Field) (K : ℕ)
    (hA : InResidue s A) (hB : InResidue t B)
    (h : coverDelta^[K] (coverComm A B) = 0) :
    delta^[K] (signedComm 1 (stripResidue s A) (stripResidue t B)) = 0 := by
  rw [signedComm_one]
  exact (coverDelta_comm_eq_zero_iff s t A B hA hB K).mp h

private theorem restore_sum_smul {ι : Type*} (s : ℤ) (S : Finset ι) (c : ι → ℂ)
    (f : ι → Field) :
    restoreResidue s (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i • restoreResidue s (f i) := by
  apply HVertexOperator.coeff_inj
  funext l
  simp only [P48qNativeCurrentLocality.restoreResidue_coeff, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply]
  split_ifs <;> simp

/-- At a fixed total strip degree the two integer ordered sums, restored in a
single cover residue, agree with the weighted nested ordinary residue. -/
theorem adjustedResidue_iterate_degree (J A B : Field) (s t u m n : ℤ) (K L d : ℕ)
    (hJ : InResidue s J) (hA : InResidue t A) (hB : InResidue u B)
    (hAB : coverDelta^[K] (coverComm A B) = 0)
    (hJB : coverDelta^[L] (coverComm J B) = 0) :
    let j := stripResidue s J
    let a := stripResidue t A
    let b := stripResidue u B
    let α := (s : ℂ) / 3
    let β := (t : ℂ) / 3
    let lift := restoreResidue (s+t+u-3*d)
    (∑ p ∈ Finset.range (d+1), leftWeight α β d p •
      lift (R (R j a (m+p)) b (n+(d-p : ℕ)))) =
    (∑ k ∈ Finset.range (d+1), rightWeight α β d k •
      ∑ i ∈ Finset.range (((K : ℤ)-n).toNat-(d-k)),
        chooseSign m i • lift (R j (R a b (n+i+(d-k : ℕ))) (m-i+k))) +
    (∑ k ∈ Finset.range (d+1), rightWeight α β d k •
      ∑ i ∈ Finset.range (L-k),
        (-epsilon m * chooseSign m i) • lift (R a (R j b ((k : ℤ)+i))
          (m+n-i+(d-k : ℕ)))) := by
  dsimp only
  have hadd (r : ℤ) (X Y : Field) : restoreResidue r (X+Y) =
      restoreResidue r X + restoreResidue r Y := by
    apply HVertexOperator.coeff_inj
    funext l
    simp only [P48qNativeCurrentLocality.restoreResidue_coeff, map_add, Pi.add_apply]
    split_ifs <;> simp
  have e := congrArg (restoreResidue (s+t+u-3*d))
    (residue_iterate_degree (stripResidue s J) (stripResidue t A) (stripResidue u B)
      ((s : ℂ)/3) ((t : ℂ)/3) m n K L d
      (stripLocality t u A B K hA hB hAB) (stripLocality s u J B L hJ hB hJB))
  simpa only [hadd, restore_sum_smul] using e

#print axioms adjustedResidue_iterate_degree

open P48qNativeCurrentLocality (restoreResidue_stripResidue stripResidue_restoreResidue
  stripResidue_coeff restoreResidue_coeff)
open private restoreResidue_inResidue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open P48qNativeResidueProduct (clearedResidue_zero_of_locality)
open private integralAdjusted strip_adjusted adjusted_inResidue adjusted_coverLocal
  adjusted_strip_representatives valid_of_coverLocality adjusted_at_valid_cutoffs from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct
open private deltaCoverEnd coverOrder_mono restore_local strip_local from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open private coverLocal_symm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private ext_modes Z_mode from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

private theorem restore_add (s : ℤ) (X Y : Field) :
    restoreResidue s (X+Y) = restoreResidue s X + restoreResidue s Y := by
  apply HVertexOperator.coeff_inj
  funext l
  simp only [restoreResidue_coeff, map_add, Pi.add_apply]
  split_ifs <;> simp

private theorem restore_sum {ι : Type*} (s : ℤ) (S : Finset ι) (f : ι → Field) :
    restoreResidue s (∑ i ∈ S, f i) = ∑ i ∈ S, restoreResidue s (f i) := by
  apply HVertexOperator.coeff_inj
  funext l
  simp only [restoreResidue_coeff, map_sum, Finset.sum_apply]
  split_ifs <;> simp

private theorem strip_sum_smul {ι : Type*} (s : ℤ) (S : Finset ι) (c : ι → ℂ)
    (f : ι → Field) :
    stripResidue s (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i • stripResidue s (f i) := by
  apply HVertexOperator.coeff_inj
  funext l
  simp only [stripResidue_coeff, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]

private theorem R_zero_first (B : VertexOperator ℂ V) (n : ℤ) : R 0 B n = 0 := by
  have h := R_smul_first B B n 0
  simpa only [zero_smul] using h
private theorem R_add_first (X Y B : VertexOperator ℂ V) (n : ℤ) :
    R (X+Y) B n = R X B n + R Y B n := by
  rw [← sub_neg_eq_add, R_sub_first, ← neg_one_smul ℂ Y, R_smul_first, neg_one_smul,
    sub_neg_eq_add]

private theorem R_sum_first {ι : Type*} (S : Finset ι) (f : ι → VertexOperator ℂ V)
    (B : VertexOperator ℂ V) (n : ℤ) :
    R (∑ i ∈ S, f i) B n = ∑ i ∈ S, R (f i) B n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [R_zero_first]
  | insert i S hi ih => rw [Finset.sum_insert hi, R_add_first, ih, Finset.sum_insert hi]

private theorem adjusted_first_sum {ι : Type*} (s t : ℤ) (S : Finset ι) (c : ι → ℂ)
    (X : ι → Field) (B : Field) (N : ℕ) (n : ℤ) :
    adjustedResidue s t (∑ i ∈ S, c i • X i) B N n =
      ∑ i ∈ S, c i • adjustedResidue s t (X i) B N n := by
  have form (A : Field) : adjustedResidue s t A B N n =
      restoreResidue (s+t)
        (integralAdjusted ((s:ℂ)/3) (stripResidue s A) (stripResidue t B) N n) := by
    rw [← strip_adjusted, restoreResidue_stripResidue _ _ (adjusted_inResidue _ _ _ _ _ _)]
  simp only [form, strip_sum_smul, integralAdjusted, R_sum_first, R_smul_first, Z_sum, Z_smul]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  rw [restore_sum]
  simp only [restore_sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- Recover the cover expansion by applying the fixed-index coefficient formula
before restoring the individual integral residues. -/
private theorem adjusted_expand (s t : ℤ) (A B : Field) (N : ℕ) (n : ℤ) :
    adjustedResidue s t A B N n =
      ∑ p ∈ Finset.range ((N : ℤ)-n).toNat, Ring.choose ((s : ℂ)/3) p •
        restoreResidue (s+t-3*p) (R (stripResidue s A) (stripResidue t B) (n+p)) := by
  apply HVertexOperator.coeff_inj
  funext l
  let k := l - 3*n
  have hk : k + 3*n = l := by dsimp [k]; omega
  conv_lhs => rw [← hk, adjustedResidue_coeff]
  simp only [P48qNativeResidueProduct.binomialTail, clearedResidue, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, ← OrdinaryResidueIterate.ordinary_residue]
  apply Finset.sum_congr rfl
  intro p _
  rw [restoreResidue_coeff, restoreResidue_coeff,
    show (k+3*(n+(p:ℤ))) % 3 = l % 3 by dsimp [k]; omega,
    show (s+t-3*(p:ℤ)) % 3 = (s+t) % 3 by omega,
    show k+3*(n+(p:ℤ))-(s+t) = l-(s+t-3*(p:ℤ)) by dsimp [k]; omega]

private theorem cover_mono {A B : Field} {N M : ℕ} (hNM : N ≤ M)
    (hN : coverDelta^[N] (coverComm A B) = 0) :
    coverDelta^[M] (coverComm A B) = 0 := by
  have hN' : (deltaCoverEnd ^ N) (coverComm A B) = 0 := by rwa [Module.End.pow_apply]
  have hM := coverOrder_mono hNM hN'
  rwa [Module.End.pow_apply] at hM

private theorem sum_pad_triangle {M : Type*} [AddCommMonoid M] (P D : ℕ) (Q : ℕ → ℕ)
    (F : ℕ → ℕ → M) (hp : ∀ p ≥ P, ∀ q, F p q = 0)
    (hq : ∀ p q, Q p ≤ q → F p q = 0) (hd : ∀ p q, D ≤ p + q → F p q = 0) :
    (∑ p ∈ Finset.range P, ∑ q ∈ Finset.range (Q p), F p q) =
      ∑ d ∈ Finset.range D, ∑ p ∈ Finset.range (d+1), F p (d-p) := by
  rw [← triangle]
  have hinner (p : ℕ) : (∑ q ∈ Finset.range (Q p), F p q) =
      ∑ q ∈ Finset.range (D-p), F p q :=
    sum_range_change _ _ _ (hq p) (fun q h => hd p q (by omega))
  simp_rw [hinner]
  exact sum_range_change _ _ _
    (fun p h => Finset.sum_eq_zero fun q _ => hp p h q)
    (fun p h => by simp [show D-p = 0 by omega])

private theorem ordinary_coverLocal (s t u : ℤ) (J A B : Field)
    (hB : InResidue u B) (hJB : CoverLocal J B) (hAB : CoverLocal A B)
    (hJA : CoverLocal J A) (v r : ℤ) :
    CoverLocal (restoreResidue v (R (stripResidue s J) (stripResidue t A) r)) B := by
  apply restore_local _ u _ B hB
  rw [OrdinaryResidueIterate.ordinary_residue]
  have h := SignedFieldResidueLocality.residue_locality 1 1 1
    (stripResidue s J) (stripResidue t A) (stripResidue u B)
  simp only [mul_one, signedComm_one] at h
  exact h (strip_local s u J B hJB) (strip_local t u A B hAB) (strip_local s t J A hJA) r

/-- One order clears the nested adjusted left product and every retained
ordinary left summand, in each summand's own strip representative. -/
theorem adjustedResidue_iterate_left_locality (J A B : Field) (s t u m : ℤ) (I : ℕ)
    (hB : InResidue u B) (hJA : CoverLocal J A) (hJB : CoverLocal J B)
    (hAB : CoverLocal A B) :
    ∃ O : ℕ, coverDelta^[O] (coverComm (adjustedResidue s t J A I m) B) = 0 ∧
      ∀ p : ℕ, p < ((I : ℤ)-m).toNat →
        coverDelta^[O] (coverComm
          (restoreResidue (s+t-3*p) (R (stripResidue s J) (stripResidue t A) (m+p))) B) = 0 := by
  obtain ⟨N, hN⟩ := adjusted_coverLocal s t u J A B I m hB hJB hAB hJA
  choose order horder using fun p : ℕ =>
    ordinary_coverLocal s t u J A B hB hJB hAB hJA (s+t-3*p) (m+p)
  let O := max N ((Finset.range ((I : ℤ)-m).toNat).sup order)
  refine ⟨O, cover_mono (le_max_left _ _) hN, ?_⟩
  intro p hp
  exact cover_mono (le_trans (Finset.le_sup (f := order) (Finset.mem_range.mpr hp))
    (le_max_right _ _)) (horder p)

private theorem strip_restore_offset (s : ℤ) (d : ℕ) (A : Field) :
    stripResidue s (restoreResidue (s-3*d) A) = Z (d : ℤ) A := by
  apply ext_modes
  intro q
  rw [Z_mode]
  simp only [VertexOperator.ncoeff_apply, stripResidue_coeff, restoreResidue_coeff]
  rw [ite_eq_left (by omega), show (3*(-q-1)+s-(s-3*(d:ℤ)))/3 = -(q-d)-1 by omega]

private theorem adjusted_left_triangle (J A B : Field) (s t u m n : ℤ) (I O D : ℕ)
    (hJ : InResidue s J) (hA : InResidue t A) (hB : InResidue u B)
    (hJA : coverDelta^[I] (coverComm J A) = 0)
    (hO : ∀ p : ℕ, p < ((I : ℤ)-m).toNat →
        coverDelta^[O] (coverComm
          (restoreResidue (s+t-3*p) (R (stripResidue s J) (stripResidue t A) (m+p))) B) = 0)
    (hD : ((I : ℤ)-m).toNat + ((O : ℤ)-n).toNat ≤ D) :
    stripResidue (s+t+u)
        (adjustedResidue (s+t) u (adjustedResidue s t J A I m) B O n) =
      ∑ d ∈ Finset.range D, Z (d : ℤ)
        (∑ p ∈ Finset.range (d+1),
          leftWeight ((s : ℂ)/3) ((t : ℂ)/3) d p •
            R (R (stripResidue s J) (stripResidue t A) (m+p))
              (stripResidue u B) (n+(d-p : ℕ))) := by
  let X (p : ℕ) := R (stripResidue s J) (stripResidue t A) (m+p)
  let F (p q : ℕ) :=
    (Ring.choose ((s : ℂ)/3) p * Ring.choose ((s : ℂ)/3 + (t : ℂ)/3-p) q) •
      Z ((p : ℤ)+q) (R (X p) (stripResidue u B) (n+q))
  have expand : adjustedResidue s t J A I m =
      ∑ p ∈ Finset.range ((I : ℤ)-m).toNat, Ring.choose ((s : ℂ)/3) p •
        restoreResidue (s+t-3*p) (X p) := adjusted_expand s t J A I m
  rw [expand, adjusted_first_sum, strip_sum_smul]
  calc
    _ = ∑ p ∈ Finset.range ((I : ℤ)-m).toNat, ∑ q ∈ Finset.range ((O : ℤ)-n).toNat,
        F p q := by
      apply Finset.sum_congr rfl
      intro p hp
      have hs := adjusted_strip_representatives (s+t) (s+t-3*p) u u
        (restoreResidue (s+t-3*p) (X p)) B O n (by omega) rfl
        (fun l hl => restoreResidue_inResidue (s+t-3*p) (X p) l
          (by simpa only [show (s+t-3*(p:ℤ)) % 3 = (s+t) % 3 by omega] using hl))
        hB (hO p (Finset.mem_range.mp hp))
      rw [hs, adjusted_expand, strip_sum_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [show s+t-3*(p:ℤ)+u-3*(q:ℤ) = (s+t+u)-3*((p+q : ℕ):ℤ) by push_cast; ring,
        strip_restore_offset, stripResidue_restoreResidue]
      have hcast : (((s+t-3*(p:ℤ) : ℤ) : ℂ)/3) = (s:ℂ)/3+(t:ℂ)/3-p := by
        push_cast
        ring
      simp only [F, hcast, smul_smul, Nat.cast_add]
    _ = ∑ d ∈ Finset.range D, ∑ p ∈ Finset.range (d+1), F p (d-p) := by
      have hp (p : ℕ) (h : ((I : ℤ)-m).toNat ≤ p) (q : ℕ) : F p q = 0 := by
        have hzero := residue_vanishes _ _ I (stripLocality s t J A I hJ hA hJA)
          (m+p) (by omega)
        simp only [F, X, hzero, R_zero_first, Z_zero, smul_zero]
      have hq (p q : ℕ) (h : ((O : ℤ)-n).toNat ≤ q) : F p q = 0 := by
        by_cases hP : p < ((I : ℤ)-m).toNat
        · have hvalid := valid_of_coverLocality (s+t-3*p) u
            (restoreResidue (s+t-3*p) (X p)) B O (restoreResidue_inResidue _ _) hB (hO p hP)
          rw [stripResidue_restoreResidue] at hvalid
          simp only [F, hvalid (n+q) (by omega), Z_zero, smul_zero]
        · exact hp p (by omega) q
      exact sum_pad_triangle _ D _ F hp hq (fun p q hd => by
        by_cases hP : ((I : ℤ)-m).toNat ≤ p
        · exact hp p hP q
        · exact hq p q (by omega))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Z_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Z_smul]
      simp only [F, leftWeight, Int.natCast_sub (by simpa using hp : p ≤ d)]
      rw [show (p : ℤ)+((d : ℤ)-p) = d by omega]

/-- One order clears a right-nested adjusted product and the ordinary right
summands used in its strip-degree expansion. -/
theorem adjustedResidue_iterate_right_locality (J A B : Field) (s t u q : ℤ) (I : ℕ)
    (hJ : InResidue s J) (hJA : CoverLocal J A) (hJB : CoverLocal J B)
    (hAB : CoverLocal A B) :
    ∃ O : ℕ, coverDelta^[O] (coverComm J (adjustedResidue t u A B I q)) = 0 ∧
      ∀ p : ℕ, p < ((I : ℤ)-q).toNat →
        Valid (stripResidue s J)
          (R (stripResidue t A) (stripResidue u B) (q+p)) O := by
  obtain ⟨N, hN⟩ := coverLocal_symm (adjusted_coverLocal t u s A B J I q hJ
    (coverLocal_symm hJA) (coverLocal_symm hJB) hAB)
  let X (p : ℕ) := restoreResidue (t+u) (R (stripResidue t A) (stripResidue u B) (q+p))
  choose order horder using fun p : ℕ =>
    coverLocal_symm (ordinary_coverLocal t u s A B J hJ (coverLocal_symm hJA)
      (coverLocal_symm hJB) hAB (t+u) (q+p))
  let O := max N ((Finset.range ((I : ℤ)-q).toNat).sup order)
  refine ⟨O, cover_mono (le_max_left _ _) hN, ?_⟩
  intro p hp
  have hloc : coverDelta^[O] (coverComm J (X p)) = 0 :=
    cover_mono (le_trans (Finset.le_sup (f := order) (Finset.mem_range.mpr hp))
      (le_max_right _ _)) (horder p)
  simpa only [X, stripResidue_restoreResidue] using
    valid_of_coverLocality s (t+u) J (X p) O hJ (restoreResidue_inResidue _ _) hloc

private theorem adjusted_right_triangle (J A B : Field) (s t u : ℤ) (I P D : ℕ)
    (O : ℕ → ℕ) (q r : ℕ → ℤ) (w : ℕ → ℂ)
    (hD : ∀ i < P, ((I : ℤ)-q i).toNat + ((O i : ℤ)-r i).toNat ≤ D)
    (hO : ∀ i < P, ∀ p < ((I : ℤ)-q i).toNat,
      Valid (stripResidue s J) (R (stripResidue t A) (stripResidue u B) (q i + p)) (O i)) :
    (∑ i ∈ Finset.range P, w i • stripResidue (s+(t+u))
      (adjustedResidue s (t+u) J (adjustedResidue t u A B I (q i)) (O i) (r i))) =
    ∑ d ∈ Finset.range D, Z (d : ℤ)
      (∑ p ∈ Finset.range (d+1),
        (Ring.choose ((t:ℂ)/3) p * Ring.choose ((s:ℂ)/3) (d-p)) •
        ∑ i ∈ Finset.range P, if p < ((I : ℤ)-q i).toNat then
          w i • R (stripResidue s J) (R (stripResidue t A) (stripResidue u B) (q i+p))
            (r i+(d-p : ℕ)) else 0) := by
  let X (i p : ℕ) := R (stripResidue t A) (stripResidue u B) (q i+p)
  let F (i p l : ℕ) := if p < ((I : ℤ)-q i).toNat then
    (Ring.choose ((t:ℂ)/3) p * Ring.choose ((s:ℂ)/3) l) •
      R (stripResidue s J) (X i p) (r i+l) else 0
  have expand (i : ℕ) (hi : i < P) :
      stripResidue (s+(t+u))
          (adjustedResidue s (t+u) J (adjustedResidue t u A B I (q i)) (O i) (r i)) =
        ∑ d ∈ Finset.range D, ∑ p ∈ Finset.range (d+1), Z (d : ℤ) (F i p (d-p)) := by
    rw [strip_adjusted, strip_adjusted]
    simp only [integralAdjusted, R_sum, R_smul, R_Z, Z_sum, Z_smul, Z_Z]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ p ∈ Finset.range ((I : ℤ)-q i).toNat,
          ∑ l ∈ Finset.range ((O i : ℤ)-r i).toNat, Z ((p : ℤ)+l) (F i p l) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro l _
        simp only [F, X, ite_eq_left (Finset.mem_range.mp hp), Z_smul]
        rw [mul_comm (Ring.choose ((s:ℂ)/3) l), add_comm (p : ℤ)]
      _ = _ := by
        have hp (p : ℕ) (hh : ((I : ℤ)-q i).toNat ≤ p) (l : ℕ) :
            Z ((p:ℤ)+l) (F i p l) = 0 := by
          simp only [F, ite_eq_right (not_lt.mpr hh), Z_zero]
        have hl (p l : ℕ) (hh : ((O i : ℤ)-r i).toNat ≤ l) :
            Z ((p:ℤ)+l) (F i p l) = 0 := by
          by_cases hP : p < ((I : ℤ)-q i).toNat
          · simp only [F, X, ite_eq_left hP, hO i hi p hP (r i+l) (by omega),
              smul_zero, Z_zero]
          · exact hp p (by omega) l
        have hd (p l : ℕ) (hh : D ≤ p+l) : Z ((p:ℤ)+l) (F i p l) = 0 := by
          by_cases hP : ((I : ℤ)-q i).toNat ≤ p
          · exact hp p hP l
          · exact hl p l (by have := hD i hi; omega)
        rw [sum_pad_triangle _ D _ (fun p l => Z ((p:ℤ)+l) (F i p l)) hp hl hd]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro p hp'
        rw [Int.natCast_sub (by simpa using hp' : p ≤ d), add_sub_cancel]
  calc
    _ = ∑ i ∈ Finset.range P, w i •
        ∑ d ∈ Finset.range D, ∑ p ∈ Finset.range (d+1), Z (d : ℤ) (F i p (d-p)) := by
      exact Finset.sum_congr rfl fun i hi =>
        congrArg (fun x => w i • x) (expand i (Finset.mem_range.mp hi))
    _ = _ := by
      simp_rw [Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm, Z_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Z_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Z_smul]
      congr 1
      by_cases hp : p < ((I : ℤ)-q i).toNat
      · simp only [F, X, ite_eq_left hp]
        exact smul_comm _ _ _
      · simp only [F, ite_eq_right hp, smul_zero]

private theorem sum_range_if_lt {M : Type*} [AddCommMonoid M] (P Q : ℕ) (hPQ : Q ≤ P)
    (f : ℕ → M) :
    (∑ i ∈ Finset.range P, if i < Q then f i else 0) = ∑ i ∈ Finset.range Q, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem adjusted_forward_triangle (J A B : Field) (s t u m n : ℤ) (K D : ℕ)
    (P : ℕ → ℕ)
    (hD : ∀ i < ((K : ℤ) - n).toNat, ((K : ℤ) - (n + i)).toNat + ((P i : ℤ) - (m - i)).toNat ≤ D)
    (hP : ∀ i < ((K : ℤ) - n).toNat, ∀ p < ((K : ℤ) - (n + i)).toNat,
      Valid (stripResidue s J) (R (stripResidue t A) (stripResidue u B) (n+i+p)) (P i)) :
    (∑ i ∈ Finset.range ((K : ℤ)-n).toNat, chooseSign m i • stripResidue (s+(t+u))
      (adjustedResidue s (t+u) J (adjustedResidue t u A B K (n+i)) (P i) (m-i))) =
    ∑ d ∈ Finset.range D, Z (d : ℤ)
      (∑ k ∈ Finset.range (d+1), rightWeight ((s:ℂ)/3) ((t:ℂ)/3) d k •
        ∑ i ∈ Finset.range (((K : ℤ)-n).toNat-(d-k)), chooseSign m i •
          R (stripResidue s J) (R (stripResidue t A) (stripResidue u B) (n+i+(d-k : ℕ)))
            (m-i+k)) := by
  rw [adjusted_right_triangle J A B s t u K _ D P (fun i => n+i) (fun i => m-i)
    (chooseSign m) hD hP]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [← Finset.sum_range_reflect _ (d+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := by simpa using hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk', rightWeight,
    mul_comm (Ring.choose ((t:ℂ)/3) (d-k))]
  congr 1
  have ht (i : ℕ) : d-k < ((K : ℤ)-(n+i)).toNat ↔ i < ((K : ℤ)-n).toNat-(d-k) := by
    omega
  simp_rw [ht]
  exact sum_range_if_lt _ _ (Nat.sub_le _ _) _

private theorem adjusted_reverse_triangle (J A B : Field) (s t u m n : ℤ) (L D : ℕ)
    (Q : ℕ → ℕ)
    (hD : ∀ i < L, ((L : ℤ) - i).toNat + ((Q i : ℤ) - (m + n - i)).toNat ≤ D)
    (hQ : ∀ i < L, ∀ p < ((L : ℤ) - i).toNat,
      Valid (stripResidue t A) (R (stripResidue s J) (stripResidue u B) ((i : ℤ) + p)) (Q i)) :
    (∑ i ∈ Finset.range L, (-epsilon m * chooseSign m i) • stripResidue (t+(s+u))
      (adjustedResidue t (s+u) A (adjustedResidue s u J B L i) (Q i) (m+n-i))) =
    ∑ d ∈ Finset.range D, Z (d : ℤ)
      (∑ k ∈ Finset.range (d+1), rightWeight ((s:ℂ)/3) ((t:ℂ)/3) d k •
        ∑ i ∈ Finset.range (L-k), (-epsilon m * chooseSign m i) •
          R (stripResidue t A) (R (stripResidue s J) (stripResidue u B) ((k : ℤ)+i))
            (m+n-i+(d-k : ℕ))) := by
  rw [adjusted_right_triangle A J B t s u L _ D Q (fun i => i) (fun i => m+n-i)
    (fun i => -epsilon m * chooseSign m i) hD hQ]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [rightWeight, add_comm (k : ℤ)]
  congr 1
  have ht (i : ℕ) : k < ((L : ℤ)-i).toNat ↔ i < L-k := by omega
  simp_rw [ht]
  exact sum_range_if_lt _ _ (Nat.sub_le _ _) _

/-- Fractional iterate for three local fields on the threefold cover.
The inner cutoffs are the three supplied locality orders. The outer orders
clear the actual nested products in each of the two ordered sums. -/
theorem adjustedResidue_iterate (J A B : Field) (s t u m n : ℤ) (I K L : ℕ)
    (hJ : InResidue s J) (hA : InResidue t A) (hB : InResidue u B)
    (hJA : coverDelta^[I] (coverComm J A) = 0)
    (hAB : coverDelta^[K] (coverComm A B) = 0)
    (hJB : coverDelta^[L] (coverComm J B) = 0) :
    ∃ (O : ℕ) (P Q : ℕ → ℕ),
      coverDelta^[O] (coverComm (adjustedResidue s t J A I m) B) = 0 ∧
      (∀ i : ℕ, coverDelta^[P i] (coverComm J (adjustedResidue t u A B K (n+i))) = 0) ∧
      (∀ i : ℕ, coverDelta^[Q i] (coverComm A (adjustedResidue s u J B L i)) = 0) ∧
      adjustedResidue (s+t) u (adjustedResidue s t J A I m) B O n =
        (∑ i ∈ Finset.range ((K : ℤ)-n).toNat, chooseSign m i •
          adjustedResidue s (t+u) J (adjustedResidue t u A B K (n+i)) (P i) (m-i)) +
        (∑ i ∈ Finset.range L, (-epsilon m * chooseSign m i) •
          adjustedResidue t (s+u) A (adjustedResidue s u J B L i) (Q i) (m+n-i)) := by
  obtain ⟨O, hO, hO'⟩ := adjustedResidue_iterate_left_locality J A B s t u m I hB
    ⟨I,hJA⟩ ⟨L,hJB⟩ ⟨K,hAB⟩
  choose P hP hP' using fun i : ℕ => adjustedResidue_iterate_right_locality J A B s t u (n+i)
    K hJ ⟨I,hJA⟩ ⟨L,hJB⟩ ⟨K,hAB⟩
  choose Q hQ hQ' using fun i : ℕ => adjustedResidue_iterate_right_locality A J B t s u i
    L hA (coverLocal_symm ⟨I,hJA⟩) ⟨K,hAB⟩ ⟨L,hJB⟩
  refine ⟨O,P,Q,hO,hP,hQ,?_⟩
  let N := ((K : ℤ) - n).toNat
  let fp (i : ℕ) := ((K : ℤ) - (n + i)).toNat + ((P i : ℤ) - (m - i)).toNat
  let fq (i : ℕ) := ((L : ℤ) - i).toNat + ((Q i : ℤ) - (m + n - i)).toNat
  let D := ((I : ℤ)-m).toNat + ((O : ℤ)-n).toNat +
    (Finset.range N).sup fp + (Finset.range L).sup fq
  have hD0 : ((I : ℤ)-m).toNat + ((O : ℤ)-n).toNat ≤ D := by dsimp [D]; omega
  have hD1 (i : ℕ) (hi : i < N) : fp i ≤ D := by
    have h := Finset.le_sup (f := fp) (Finset.mem_range.mpr hi)
    dsimp [D]
    omega
  have hD2 (i : ℕ) (hi : i < L) : fq i ≤ D := by
    have h := Finset.le_sup (f := fq) (Finset.mem_range.mpr hi)
    dsimp [D]
    omega
  have h := adjusted_left_triangle J A B s t u m n I O D hJ hA hB hJA hO' hD0
  have h1 := adjusted_forward_triangle J A B s t u m n K D P hD1 (fun i _ => hP' i)
  have h2 := adjusted_reverse_triangle J A B s t u m n L D Q hD2 (fun i _ => hQ' i)
  have hl (x y : ℤ) (X Y : Field) (k : ℕ) (q : ℤ) :
      adjustedResidue x y X Y k q =
        restoreResidue (x+y) (stripResidue (x+y) (adjustedResidue x y X Y k q)) :=
    (restoreResidue_stripResidue _ _ (adjusted_inResidue _ _ _ _ _ _)).symm
  conv_lhs => rw [hl (s+t) u, h]
  conv_rhs =>
    congr
    · arg 2
      ext i
      rw [hl s (t+u), show s+(t+u) = s+t+u by omega]
    · arg 2
      ext i
      rw [hl t (s+u), show t+(s+u) = s+t+u by omega]
  rw [← restore_sum_smul, ← restore_sum_smul, ← restore_add]
  rw [show s+(t+u) = s+t+u by omega] at h1
  rw [show t+(s+u) = s+t+u by omega] at h2
  rw [h1, h2, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  have hZ (d : ℤ) (X Y : Field) : Z d (X+Y) = Z d X + Z d Y := by
    apply ext_modes
    intro l
    simp only [Z_mode, map_add, Pi.add_apply]
  rw [← hZ]
  congr 1
  exact residue_iterate_degree _ _ _ _ _ m n K L d
    (stripLocality t u A B K hA hB hAB) (stripLocality s u J B L hJ hB hJB)

#print axioms adjustedResidue_iterate

open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qAllJetWickField (NativeStates nativeField)
open P48qThirdTwistedField (Cartan)
open ThirdEigenspacePairing (p48qAction)
open ThirdTwistedIterate (currentAlong)
open NativeStandardThirdLift (standardLift)
open LatticeAllStateReconstruction (mu stateField_iterate)
open P48qNativeCurrentLocality (nativeField_inResidue)
open P48qNativePairwiseLocality (nativeField_pairwise_locality)
open P48qChargedResidueProduct (adjustedResidue_ground_first_eigenstate)
open private groundSpan from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private mu_eigen current_lift_eigen adjusted_current_at_locality from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem source_cutoff (a b : NativeStates) :
    ∃ N : ℕ, ∀ q ≥ (N : ℤ), mu lattice a q b = 0 := by
  let Y := LatticeAllStateField.Y lattice a
  let e := ((HahnModule.of ℂ).symm (Y b)).order
  refine ⟨(-e).toNat, fun q hq => ?_⟩
  change (Y [[q]]) b = 0
  exact VertexOperator.ncoeff_eq_zero_of_lt_order Y q b (by change -q-1 < e; omega)

private theorem source_iterate_finset (J A B : NativeStates) (m n : ℤ) (K L : ℕ)
    (hK : ∀ q ≥ (K : ℤ), mu lattice A q B = 0)
    (hL : ∀ q ≥ (L : ℤ), mu lattice J q B = 0) :
    mu lattice (mu lattice J m A) n B =
      (∑ i ∈ Finset.range ((K : ℤ)-n).toNat, chooseSign m i •
        mu lattice J (m-i) (mu lattice A (n+i) B)) +
      (∑ i ∈ Finset.range L, (-epsilon m * chooseSign m i) •
        mu lattice A (m+n-i) (mu lattice J i B)) := by
  let F (i : ℕ) := chooseSign m i • mu lattice J (m-i) (mu lattice A (n+i) B)
  let G (i : ℕ) := chooseSign m i • mu lattice A (m+n-i) (mu lattice J i B)
  have e := (stateField_iterate lattice J A B m n).2.2
  change mu lattice (mu lattice J m A) n B =
    (∑ᶠ i, F i) - epsilon m • (∑ᶠ i, G i) at e
  have hf : (∑ᶠ i, F i) = ∑ i ∈ Finset.range ((K : ℤ)-n).toNat, F i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    contrapose! hi
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hi
    have hzero : F i = 0 := by
      dsimp only [F]
      rw [hK (n+i) (by omega), mu, map_zero, smul_zero]
    simpa only [Function.mem_support, not_not] using hzero
  have hg : (∑ᶠ i, G i) = ∑ i ∈ Finset.range L, G i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    contrapose! hi
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hi
    have hzero : G i = 0 := by
      dsimp only [G]
      rw [hL i (by omega), mu, map_zero, smul_zero]
    simpa only [Function.mem_support, not_not] using hzero
  rw [e, hf, hg, sub_eq_add_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  simp only [F, G, smul_smul, neg_smul, neg_mul]

/-- A negative eigen-current insertion over a ground eigenstate in the first
slot, against every native lift eigenstate. -/
theorem adjustedResidue_negative_eigenCurrent_ground_first
    (x : Cartan) (r : ℕ) (hr : r < 3) (hx : p48qAction x = (ζ ^ r) ^ 2 • x)
    (a b : NativeStates) (t u : ℤ) (ha : a ∈ groundSpan)
    (hae : σ a = ζ ^ t • a) (hbe : σ b = ζ ^ u • b)
    (d : ℕ+) (N : ℕ) (n : ℤ)
    (hN : coverDelta^[N]
      (coverComm (nativeField (mu lattice (currentAlong lattice x) (-((d : ℕ) : ℤ)) a))
        (nativeField b)) = 0) :
    adjustedResidue (-(r : ℤ)+t) u
      (nativeField (mu lattice (currentAlong lattice x) (-((d : ℕ) : ℤ)) a)) (nativeField b) N n =
        nativeField (mu lattice (mu lattice (currentAlong lattice x) (-((d : ℕ) : ℤ)) a) n b) := by
  let s := -(r : ℤ)
  let m := -((d : ℕ) : ℤ)
  let j := currentAlong lattice x
  let ja := mu lattice j m a
  have hje := current_lift_eigen x r hx
  have hre := mu_eigen j a s t m hje hae
  have hJ := nativeField_inResidue j s hje
  have hA := nativeField_inResidue a t hae
  have hB := nativeField_inResidue b u hbe
  obtain ⟨I,hI⟩ := nativeField_pairwise_locality j a
  obtain ⟨K₀,hK₀⟩ := nativeField_pairwise_locality a b
  obtain ⟨L₀,hL₀⟩ := nativeField_pairwise_locality j b
  obtain ⟨K₁,hK₁⟩ := source_cutoff a b
  obtain ⟨L₁,hL₁⟩ := source_cutoff j b
  let K := max K₀ K₁
  let L := max L₀ L₁
  have hK := cover_mono (le_max_left K₀ K₁) hK₀
  have hL := cover_mono (le_max_left L₀ L₁) hL₀
  obtain ⟨O,P,Q,hO,hP,hQ,e⟩ := adjustedResidue_iterate (nativeField j) (nativeField a)
    (nativeField b) s t u m n I K L hJ hA hB hI hK hL
  have hjap : adjustedResidue s t (nativeField j) (nativeField a) I m = nativeField ja :=
    adjusted_current_at_locality x r hr hx a t hae I m hI
  rw [hjap] at e hO
  have left (i : ℕ) :
      adjustedResidue s (t+u) (nativeField j)
        (adjustedResidue t u (nativeField a) (nativeField b) K (n+i)) (P i) (m-i) =
      nativeField (mu lattice j (m-i) (mu lattice a (n+i) b)) := by
    have hab := adjustedResidue_ground_first_eigenstate a b t u ha hae hbe K
      (fun p hp => clearedResidue_zero_of_locality _ _ _ _ hA hB K hK p hp) (n+i)
    have hh := hP i
    rw [hab] at hh ⊢
    exact adjusted_current_at_locality x r hr hx _ _ (mu_eigen a b t u (n+i) hae hbe)
      (P i) (m-i) hh
  have right (i : ℕ) :
      adjustedResidue t (s+u) (nativeField a)
        (adjustedResidue s u (nativeField j) (nativeField b) L i) (Q i) (m+n-i) =
      nativeField (mu lattice a (m+n-i) (mu lattice j i b)) := by
    have hjb := adjusted_current_at_locality x r hr hx b u hbe L i hL
    have hh := hQ i
    rw [hjb] at hh ⊢
    have hev := mu_eigen j b s u i hje hbe
    exact adjustedResidue_ground_first_eigenstate a _ t (s+u) ha hae hev (Q i)
      (fun p hp => clearedResidue_zero_of_locality _ _ _ _ hA
        (nativeField_inResidue _ _ hev) _ hh p hp) (m+n-i)
  simp_rw [left, right, ← map_smul, ← map_sum, ← map_add] at e
  have hh := source_iterate_finset j a b m n K L
    (fun q hq => hK₁ q (by dsimp [K] at hq; omega))
    (fun q hq => hL₁ q (by dsimp [L] at hq; omega))
  rw [← hh] at e
  have hjA := nativeField_inResidue ja (s+t) hre
  exact (adjusted_at_valid_cutoffs (s+t) u _ _ N O
    (fun p hp => clearedResidue_zero_of_locality _ _ _ _ hjA hB N hN p hp)
    (fun p hp => clearedResidue_zero_of_locality _ _ _ _ hjA hB O hO p hp) n).trans e

#print axioms adjustedResidue_negative_eigenCurrent_ground_first

#print axioms adjustedResidue_iterate_right_locality
#print axioms adjusted_right_triangle

#print axioms adjustedResidue_iterate_left_locality
#print axioms adjusted_left_triangle

#print axioms forwardKernel
#print axioms reverseKernel
#print axioms changeWeight

run_cmd do
  for name in [``forwardKernel, ``reverseKernel, ``changeWeight,
      ``adjustedResidue_iterate_degree, ``adjustedResidue_iterate_left_locality,
      ``adjustedResidue_iterate_right_locality, ``adjustedResidue_iterate,
      ``source_iterate_finset, ``adjustedResidue_negative_eigenCurrent_ground_first] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.contains ``propext &&
        axioms.contains ``Classical.choice && axioms.contains ``Quot.sound do
      throwError "Unexpected axiom closure for {name}: {axioms}"

#print axioms source_iterate_finset
end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
