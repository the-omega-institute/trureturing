/- GID: D5/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Work in progress on the original all-source physical L1 Ward law. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard
import D5.S3.VertexAlgebra.SourceMobius.PositiveMode

/- Classical twisted lattice construction; original conventions and notices
are inherited from the imported owners. No replacement field is introduced.
The intended endpoint is the all-source original corrected-field L1 law,
not the charged calculation below. The endpoint remains unfinished. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open scoped BigOperators TensorProduct
noncomputable section

private theorem charged_flat_zero_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (i : Fin D.rank) (j e : ℤ) :
    flatCoefficient D hu (chargedField D hu a) [(i, 0)] (j, ()) (e - 4) =
      if j < 0 then tensorCurrent D (ActualGround D hu) i j *
        chargedCoefficient D hu a (e + 2*j - 1)
      else chargedCoefficient D hu a (e + 2*j - 1) *
        tensorCurrent D (ActualGround D hu) i j := by
  have coeff (d : ℤ) : (chargedField D hu a).coeff d =
      chargedCoefficient D hu a d := by
    rw [chargedField, HVertexOperator.coeff_of_coeff]
  simp only [flatCoefficient, jetCurrent, jetScalar, Finset.range_zero,
    Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one,
    one_smul, Nat.cast_zero, mul_zero, add_zero, coeff]
  rw [show e - 4 + 2*j + 3 = e + 2*j - 1 by omega]

/-- Local quadratic expansion before pointwise finite summation. The j=0
normal-order boundary contributes both original charge pairings. -/
private theorem charged_pair_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (i l : Fin D.rank) (j e : ℤ) :
    tensorPair D (ActualGround D hu) i l j (-j) * chargedCoefficient D hu a e -
      chargedCoefficient D hu a e * tensorPair D (ActualGround D hu) i l j (-j) =
      (bilinear D (unitCharge D l) a : ℂ) •
        flatCoefficient D hu (chargedField D hu a) [(i, 0)] (j, ()) (e - 4) +
      (bilinear D (unitCharge D i) a : ℂ) •
        flatCoefficient D hu (chargedField D hu a) [(l, 0)] (-j, ()) (e - 4) +
      (if j = 0 then (bilinear D (unitCharge D i) a : ℂ) *
        (bilinear D (unitCharge D l) a : ℂ) else 0) •
        chargedCoefficient D hu a (e - 2) := by
  rw [tensorPair_eq, charged_flat_zero_jet, charged_flat_zero_jet]
  have ward (c : Fin D.rank) (k d : ℤ) := charged_tensor_current_ward D hu c a k d
  by_cases hj : j < 0
  · simp only [if_pos hj, if_neg (by omega : ¬ -j < 0),
      if_neg (by omega : j ≠ 0), zero_smul, add_zero]
    calc
      _ = tensorCurrent D (ActualGround D hu) i j *
          (tensorCurrent D (ActualGround D hu) l (-j) * chargedCoefficient D hu a e -
            chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) l (-j)) +
          (tensorCurrent D (ActualGround D hu) i j * chargedCoefficient D hu a e -
            chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) i j) *
              tensorCurrent D (ActualGround D hu) l (-j) := by noncomm_ring
      _ = _ := by
        rw [ward, ward]
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [show e - (2 * -j + 1) = e + 2*j - 1 by omega,
          show e - (2*j + 1) = e + 2*(-j) - 1 by omega]
  · by_cases hz : j = 0
    · subst j
      simp only [lt_self_iff_false, if_false, neg_zero, if_true, mul_zero, add_zero]
      have cross := ward l 0 (e - 1)
      simp only [mul_zero, zero_add] at cross
      calc
        _ = tensorCurrent D (ActualGround D hu) l 0 *
            (tensorCurrent D (ActualGround D hu) i 0 * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) i 0) +
            (tensorCurrent D (ActualGround D hu) l 0 * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) l 0) *
                tensorCurrent D (ActualGround D hu) i 0 := by noncomm_ring
        _ = _ := by
          rw [ward, ward]
          simp only [mul_zero, zero_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
          rw [show e - 1 - 1 = e - 2 by omega] at cross
          rw [sub_eq_iff_eq_add.mp cross, smul_add, smul_smul]
          abel
    · simp only [if_neg hj, if_pos (by omega : -j < 0), if_neg hz, zero_smul, add_zero]
      calc
        _ = tensorCurrent D (ActualGround D hu) l (-j) *
            (tensorCurrent D (ActualGround D hu) i j * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) i j) +
            (tensorCurrent D (ActualGround D hu) l (-j) * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) l (-j)) *
                tensorCurrent D (ActualGround D hu) i j := by noncomm_ring
        _ = _ := by
          rw [ward, ward]
          simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
          rw [show e - (2 * -j + 1) = e + 2*j - 1 by omega,
            show e - (2*j + 1) = e + 2*(-j) - 1 by omega]
          abel


/-- The quadratic-to-singleton transport is pointwise in the original actual
module. Finite support is used only after application at x and C_e x. -/
private theorem charged_normal_sum_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (i l : Fin D.rank) (e : ℤ) (x : ActualTensor D hu) :
    tensorNormalSum D (ActualGround D hu) i l 1 (chargedCoefficient D hu a e x) -
      chargedCoefficient D hu a e (tensorNormalSum D (ActualGround D hu) i l 1 x) =
      (bilinear D (unitCharge D l) a : ℂ) •
        (wordField D hu (chargedField D hu a) [(i, 0)]).coeff (e - 4) x +
      (bilinear D (unitCharge D i) a : ℂ) •
        (wordField D hu (chargedField D hu a) [(l, 0)]).coeff (e - 4) x +
      ((bilinear D (unitCharge D i) a : ℂ) *
        (bilinear D (unitCharge D l) a : ℂ)) • chargedCoefficient D hu a (e - 2) x := by
  classical
  let qi : ℂ := (bilinear D (unitCharge D i) a : ℂ)
  let ql : ℂ := (bilinear D (unitCharge D l) a : ℂ)
  let fi : ℤ → ActualTensor D hu := fun j =>
    flatTerm D hu (chargedField D hu a) [(i, 0)] (e - 4) x (j, ())
  let fl : ℤ → ActualTensor D hu := fun j =>
    flatTerm D hu (chargedField D hu a) [(l, 0)] (e - 4) x (j, ())
  let boundary : ℤ → ActualTensor D hu := fun j =>
    (if j = 0 then qi * ql else 0) • chargedCoefficient D hu a (e - 2) x
  have hfi : Function.HasFiniteSupport fi :=
    LatticeHalfFockChargedSeedPhysical.singleton_finite D hu a i (e - 4) x
  have hfl : Function.HasFiniteSupport fl :=
    LatticeHalfFockChargedSeedPhysical.singleton_finite D hu a l (e - 4) x
  have hflneg : Function.HasFiniteSupport (fun j : ℤ => fl (-j)) :=
    hfl.fun_comp_of_injective neg_injective
  have hboundary : Function.HasFiniteSupport boundary := by
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro j hj
    by_contra h
    apply hj
    simp only [Set.mem_singleton_iff] at h
    simp [boundary, h]
  have pairfinite (v : ActualTensor D hu) : Function.HasFiniteSupport
      (fun j : ℤ => tensorPair D (ActualGround D hu) i l j (-j) v) := by
    have shift (j : ℤ) : (1 : ℤ) - j - 1 = -j := by omega
    simpa only [shift] using tensorPair_finite D (ActualGround D hu) i l 1 v
  have pair (j : ℤ) :
      tensorPair D (ActualGround D hu) i l j (-j) (chargedCoefficient D hu a e x) -
        chargedCoefficient D hu a e (tensorPair D (ActualGround D hu) i l j (-j) x) =
        ql • fi j + qi • fl (-j) + boundary j := by
    exact congrArg (fun U : Module.End ℂ (ActualTensor D hu) => U x)
      (charged_pair_l1 D hu a i l j e)
  change (∑ᶠ j : ℤ, tensorPair D (ActualGround D hu) i l j (1-j-1)
      (chargedCoefficient D hu a e x)) -
    chargedCoefficient D hu a e
      (∑ᶠ j : ℤ, tensorPair D (ActualGround D hu) i l j (1-j-1) x) = _
  have shift (j : ℤ) : (1 : ℤ) - j - 1 = -j := by omega
  simp only [shift]
  rw [map_finsum _ (pairfinite x),
    ← finsum_sub_distrib (pairfinite (chargedCoefficient D hu a e x))
      ((pairfinite x).fun_comp (map_zero (chargedCoefficient D hu a e))),
    finsum_congr pair]
  have sumsplit : (∑ᶠ j : ℤ, (ql • fi j + qi • fl (-j) + boundary j)) =
      (∑ᶠ j : ℤ, ql • fi j) + (∑ᶠ j : ℤ, qi • fl (-j)) +
        ∑ᶠ j : ℤ, boundary j := by
    calc
      _ = (∑ᶠ j : ℤ, (ql • fi j + qi • fl (-j))) + ∑ᶠ j : ℤ, boundary j := by
        exact finsum_add_distrib ((hfi.fun_comp (smul_zero ql)).add
          (hflneg.fun_comp (smul_zero qi))) hboundary
      _ = _ := by
        congr 1
        exact finsum_add_distrib (hfi.fun_comp (smul_zero ql))
          (hflneg.fun_comp (smul_zero qi))
  rw [sumsplit, ← smul_finsum' ql hfi, ← smul_finsum' qi hflneg]
  have reindex : (∑ᶠ j : ℤ, fl (-j)) = ∑ᶠ j : ℤ, fl j :=
    finsum_eq_of_bijective (fun j : ℤ => -j) neg_bijective (fun _ => rfl)
  rw [reindex]
  have sumBoundary : (∑ᶠ j : ℤ, boundary j) =
      (qi * ql) • chargedCoefficient D hu a (e - 2) x := by
    rw [finsum_eq_single _ 0 (fun j hj => by simp [boundary, hj])]
    simp [boundary]
  rw [sumBoundary]
  change ql • (∑ᶠ j : ℤ, fi j) + qi • (∑ᶠ j : ℤ, fl j) + _ = _
  have left := singletonLinear_coefficient D hu (chargedField D hu a) (i, 0) (e - 4) x
  have right := singletonLinear_coefficient D hu (chargedField D hu a) (l, 0) (e - 4) x
  rw [← left, ← right]
  rfl


/-- Charged base on every original actual target input. This is a dependency,
not a replacement for the all-source corrected-field endpoint. -/
theorem charged_l1_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        chargedCoefficient D hu a e - chargedCoefficient D hu a e *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      (((e : ℂ) - 2) / 2 + (bilinear D a a : ℂ)) •
        chargedCoefficient D hu a (e - 2) := by
  classical
  let H := HalfFockSpectralFiberSource.actualInverse D
  have hHG := HalfFockSpectralFiberSource.actualInverse_left D hu
  have hGH := HalfFockSpectralFiberSource.actualInverse_right D hu
  have inv := LatticeSugawaraConformal.inverse_charge_contractions D H hHG hGH a
  apply LinearMap.ext
  intro x
  let chi : Fin D.rank → ℂ := fun i => (bilinear D (unitCharge D i) a : ℂ)
  let W : Fin D.rank → ActualTensor D hu := fun i =>
    (wordField D hu (chargedField D hu a) [(i, 0)]).coeff (e - 4) x
  let C : ActualTensor D hu := chargedCoefficient D hu a (e - 2) x
  let Q : ℂ := (bilinear D a a : ℂ)
  have rows : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l • (chi l • W i)) = ∑ i : Fin D.rank, (a i : ℂ) • W i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (∑ l : Fin D.rank, H i l * chi l) • W i := by
        simp only [Finset.sum_smul, smul_smul]
      _ = _ := by rw [inv.1 i]
  have cols : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l • (chi i • W l)) = ∑ l : Fin D.rank, (a l : ℂ) • W l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    calc
      _ = (∑ i : Fin D.rank, H i l * chi i) • W l := by
        simp only [Finset.sum_smul, smul_smul]
      _ = _ := by rw [inv.2 l]
  have quadratic : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l * chi i * chi l) = Q := by
    have h := LatticeSugawaraConformal.chargeQuadratic_eq D H hHG hGH a
    change (2 : ℂ)⁻¹ * (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l * chi i * chi l) = Q / 2 at h
    linear_combination (2 : ℂ) * h
  have quad : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l • ((chi i * chi l) • C)) = Q • C := by
    calc
      _ = (∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l * chi i * chi l) • C := by
        simp only [Finset.sum_smul, smul_smul, mul_assoc]
      _ = _ := by rw [quadratic]
  have seed : (∑ i : Fin D.rank, (a i : ℂ) • W i) - (Q / 2) • C =
      (((e : ℂ) - 2) / 2) • C := by
    have h := LatticeHalfFockChargedSeedPhysical.charged_seed_physical_coefficient
      D hu a (e - 4) x
    rw [show e - 4 + 2 = e - 2 by omega] at h
    simpa only [W, C, Q, chargeNorm, Int.cast_sub, Int.cast_ofNat] using h
  have l1 : tensorL D (ActualGround D hu) H 1 = tensorRawL D (ActualGround D hu) H 1 := by
    simp [tensorL, tensorRawL, L]
  have expansion : tensorL D (ActualGround D hu) H 1 (chargedCoefficient D hu a e x) -
      chargedCoefficient D hu a e (tensorL D (ActualGround D hu) H 1 x) =
      (2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ l : Fin D.rank,
        H i l • (chi l • W i + chi i • W l + (chi i * chi l) • C) := by
    rw [l1, tensor_rawL_finsum, tensor_rawL_finsum]
    simp_rw [map_smul, map_sum]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [map_smul, ← smul_sub]
    congr 1
    exact charged_normal_sum_l1 D hu a i l e x
  change tensorL D (ActualGround D hu) H 1 (chargedCoefficient D hu a e x) -
      chargedCoefficient D hu a e (tensorL D (ActualGround D hu) H 1 x) =
      (((e : ℂ) - 2) / 2 + Q) • C
  rw [expansion]
  simp_rw [smul_add, Finset.sum_add_distrib]
  rw [rows, cols, quad, sub_eq_iff_eq_add.mp seed]
  module


/-- The scalar Pascal step for the original normalized jets. -/
private theorem jet_shift (r : ℕ) (j : ℤ) :
    jetScalar (r + 1) (j - 1) = jetScalar (r + 1) j + jetScalar r j := by
  induction r with
  | zero => simp [jetScalar, Finset.prod_range_succ]; ring
  | succ r ih =>
    have hleft := LatticeHalfFockOriginalTranslation.jet_successor (r + 1) (j - 1)
    have hright := LatticeHalfFockOriginalTranslation.jet_successor (r + 1) j
    have hlower := LatticeHalfFockOriginalTranslation.jet_successor r j
    rw [ih] at hleft
    have hn : (r + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : r + 2 ≠ 0)
    apply (mul_left_cancel₀ hn)
    push_cast at hleft hright hlower ⊢
    linear_combination hleft - hright - hlower

/-- The only scalar product rule needed for the L1 singleton commutator. -/
private theorem jet_l1_scalar (r : ℕ) (j : ℤ) :
    ((j : ℂ) - (r : ℂ) - 1/2) * jetScalar r j -
        ((j : ℂ) - 1/2) * jetScalar r (j - 1) =
      if r = 0 then 0 else (r + 1 : ℂ) * jetScalar (r - 1) j := by
  cases r with
  | zero => simp [jetScalar]
  | succ r =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    rw [jet_shift]
    have h := LatticeHalfFockOriginalTranslation.jet_successor r j
    linear_combination -h

private theorem jet_boundary (r : ℕ) : jetScalar r (-1) = halfBinomial r := by
  unfold jetScalar halfBinomial
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  push_cast
  ring

private theorem actual_current_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (j : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        tensorCurrent D (ActualGround D hu) i j -
      tensorCurrent D (ActualGround D hu) i j *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      (-((j : ℂ) + 1/2)) • tensorCurrent D (ActualGround D hu) i (j + 1) := by
  apply TensorProduct.ext'
  intro p t
  have h := congrArg (fun U : Module.End ℂ (Oscillator D) => U p ⊗ₜ[ℂ] t)
    (L_current_commutator D (HalfFockSpectralFiberSource.actualInverse D)
      (HalfFockSpectralFiberSource.actualInverse_left D hu)
      (HalfFockSpectralFiberSource.actualInverse_right D hu) i 1 j)
  simpa only [tensorL, tensorCurrent, tensorEnd, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.sub_tmul, TensorProduct.smul_tmul',
    frequency, add_comm 1 j] using h


/-- A single original normal-order term. The hypothesis is local induction
information on the shorter source, not an assumption of the final theorem.
The only exceptional reindexing is j=-1 to the nonnegative mode 0. -/
private theorem singleton_term_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (F G H : NativeField D hu)
    (hF : ∀ d : ℤ,
      tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 * F.coeff d -
        F.coeff d * tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      G.coeff d + ((d : ℂ)/2-1) • F.coeff (d-2) + 2 • H.coeff (d-2))
    (i : Fin D.rank) (r : ℕ) (j e : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        flatCoefficient D hu F [(i,r)] (j,()) e -
      flatCoefficient D hu F [(i,r)] (j,()) e *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      flatCoefficient D hu G [(i,r)] (j,()) e +
        (((e+2*j+2*(r:ℤ)+3 : ℤ):ℂ)/2-1) •
          flatCoefficient D hu F [(i,r)] (j,()) (e-2) +
        2 • flatCoefficient D hu H [(i,r)] (j,()) (e-2) +
        (-frequency j * jetScalar r j) •
          flatCoefficient D hu F [(i,0)] (j+1,()) (e+2*(r:ℤ)-2) +
        if j = -1 then (1/2 * halfBinomial r : ℂ) •
          (tensorCurrent D (ActualGround D hu) i 0 * F.coeff (e+2*(r:ℤ)+1) -
            F.coeff (e+2*(r:ℤ)+1) * tensorCurrent D (ActualGround D hu) i 0)
        else 0 := by
  let T := tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
  let J := tensorCurrent D (ActualGround D hu) i
  have hc (k : ℤ) : T * J k - J k * T = (-frequency k) • J (k+1) := by
    exact actual_current_l1 D hu i k
  have left (k d : ℤ) : T * (J k * F.coeff d) - (J k * F.coeff d) * T =
      (-frequency k) • (J (k+1) * F.coeff d) + J k * G.coeff d +
        ((d:ℂ)/2-1) • (J k * F.coeff (d-2)) + 2 • (J k * H.coeff (d-2)) := by
    calc
      _ = (T*J k-J k*T)*F.coeff d + J k*(T*F.coeff d-F.coeff d*T) := by noncomm_ring
      _ = _ := by
        rw [hc, hF]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_add]
        abel
  have right (k d : ℤ) : T * (F.coeff d * J k) - (F.coeff d * J k) * T =
      G.coeff d * J k + ((d:ℂ)/2-1) • (F.coeff (d-2)*J k) +
        2 • (H.coeff (d-2)*J k) + (-frequency k) • (F.coeff d * J (k+1)) := by
    calc
      _ = (T*F.coeff d-F.coeff d*T)*J k + F.coeff d*(T*J k-J k*T) := by noncomm_ring
      _ = _ := by
        rw [hc, hF]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, add_mul]
  have scalar0 (k : ℤ) : jetScalar 0 k = 1 := by simp [jetScalar]
  have down : e-2+2*j+2*(r:ℤ)+3 = (e+2*j+2*(r:ℤ)+3)-2 := by omega
  have next : e+2*(r:ℤ)-2+2*(j+1)+3 = e+2*j+2*(r:ℤ)+3 := by omega
  simp only [flatCoefficient, jetCurrent, scalar0, Nat.cast_zero, mul_zero, add_zero, one_smul]
  simp only [down, next]
  change T * _ - _ * T = _
  by_cases cross : j = -1
  · subst j
    simp only [show (-1 : ℤ) < 0 by omega, ite_true,
      show ¬ (-1+1 : ℤ) < 0 by omega, ite_false, neg_add_cancel,
      show e+2*(-1)+2*(r:ℤ)+3 = e+2*(r:ℤ)+1 by omega]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
    rw [left]
    simp only [jet_boundary]
    simp only [frequency, Int.cast_neg, Int.cast_one]
    module
  · have signs : (j+1 < 0) ↔ j < 0 := by omega
    simp only [if_neg cross, signs, add_zero]
    by_cases negative : j < 0
    · simp only [negative, ite_true, if_neg cross, add_zero]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
      rw [left]
      module
    · simp only [negative, ite_false, if_neg cross, add_zero]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
      rw [right]
      module

#print axioms singleton_term_l1

#print axioms jet_shift
#print axioms jet_l1_scalar
#print axioms actual_current_l1

#print axioms charged_pair_l1
#print axioms charged_normal_sum_l1
#print axioms charged_l1_coefficient

end
end D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
