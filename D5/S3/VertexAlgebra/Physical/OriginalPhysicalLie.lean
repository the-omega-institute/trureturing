/- GID: D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie
   generality: I
   mirror-B: none(waiver:actual-original-physical-state-lie)
   mirror-E: none(waiver:actual-original-physical-state-lie)
   anchors: [D5/S3/VertexAlgebra/LatticeActualConformalEnergy,
     D5/S3/VertexAlgebra/LatticeActualConformalWard,
     D5/S3/VertexAlgebra/LatticeSugawaraVirasoro,
     D5/S3/VertexAlgebra/StateField/SkewSymmetry]
   utility: none
   digest: Original physical-state spaces, the exact translation quotient, and its zero-mode Lie bracket.
-/

import D5.S3.VertexAlgebra.LatticeActualConformalEnergy
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.VertexAlgebra.SourceMobius.Nilpotence
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Quotient.Bilinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeAllStateField
open D5.S3.VertexAlgebra.LatticeActualConformalEnergy
open D5.S3.VertexAlgebra.LatticeActualConformalWard
open D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
open D5.S3.VertexAlgebra.LatticeActualStateDerivative
open D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
open D5.S3.VertexAlgebra.LatticeAllStateReconstruction
open D5.S3.VertexAlgebra.LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial)
open D5.S3.VertexAlgebra.LatticeSugawaraConformal
open D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
open D5.S3.VertexAlgebra.SourceMobius
open D5.S3.VertexAlgebra.StateField.SkewSymmetry
open scoped BigOperators VertexOperator
noncomputable section

variable (D : LatticeData)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1)
variable (hGH : gramComplex D * H = 1)

abbrev actualL (n : ℤ) : Module.End ℂ (Carrier D) := sugawaraMode D H n

def weightSpace (h : ℤ) : Submodule ℂ (Carrier D) :=
  LinearMap.ker ((actualL D H) 0 - (h : ℂ) • LinearMap.id)

def primarySpace (h : ℤ) : Submodule ℂ (Carrier D) :=
  weightSpace D H h ⊓ ⨅ n : {n : ℤ // 0 < n}, LinearMap.ker ((actualL D H) n.1)

theorem mem_weightSpace_iff (h : ℤ) (v : Carrier D) :
    v ∈ weightSpace D H h ↔ actualL D H 0 v = (h : ℂ) • v := by
  rw [weightSpace, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem mem_primarySpace_iff (h : ℤ) (v : Carrier D) :
    v ∈ primarySpace D H h ↔
      actualL D H 0 v = (h : ℂ) • v ∧ ∀ n : ℤ, 0 < n → actualL D H n v = 0 := by
  constructor
  · intro hv
    refine ⟨(mem_weightSpace_iff D H h v).mp hv.1, ?_⟩
    intro n hn
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv.2 ⟨n, hn⟩)
  · rintro ⟨hw, hp⟩
    refine ⟨(mem_weightSpace_iff D H h v).mpr hw, ?_⟩
    change v ∈ ⨅ n : {n : ℤ // 0 < n}, LinearMap.ker (actualL D H n.1)
    apply (Submodule.mem_iInf _).mpr
    intro n
    exact LinearMap.mem_ker.mpr (hp n.1 n.2)

private theorem virasoro_comm (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (m n : ℤ) :
    actualL D H m * actualL D H n - actualL D H n * actualL D H m =
      ((m-n : ℤ) : ℂ) • actualL D H (m+n) +
        (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ (Carrier D)) :=
  sugawaraMode_virasoro D H hHG hGH m n

private theorem translation_eq (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) : actualL D H (-1) = translation D :=
  sugawaraMode_minus_one_eq_translation D H hHG hGH

private theorem translation_weight (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (h : ℤ) (v : Carrier D)
    (hv : actualL D H 0 v = (h : ℂ) • v) :
    actualL D H 0 (translation D v) = ((h+1 : ℤ) : ℂ) • translation D v := by
  rw [← translation_eq D H hHG hGH]
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
    (virasoro_comm D H hHG hGH 0 (-1))
  simp only [zero_sub, Int.cast_neg, Int.cast_one, add_neg_cancel, if_true,
    zero_pow, zero_sub, sub_zero, one_div, zero_mul, zero_smul, add_zero,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hc
  rw [hv] at hc
  simp only [map_smul, LinearMap.smul_apply] at hc
  have hc' := sub_eq_iff_eq_add.mp hc
  simpa [add_smul, add_comm, add_left_comm, add_assoc] using hc'

private theorem translation_primary (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (v : Carrier D)
    (hv : ∀ n : ℤ, 0 < n → actualL D H n v = 0)
    (hw : actualL D H 0 v = 0) :
    ∀ n : ℤ, 0 < n → actualL D H n (translation D v) = 0 := by
  intro n hn
  rw [← translation_eq D H hHG hGH]
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
    (virasoro_comm D H hHG hGH n (-1))
  by_cases hn1 : n = 1
  · subst n
    simpa [LinearMap.sub_apply, Module.End.mul_apply, hv 1 (by norm_num), hw]
      using hc
  · have hn2 : 0 < n - 1 := by omega
    have hn0 : n + (-1 : ℤ) ≠ 0 := by omega
    have hn0' : n - 1 ≠ 0 := by omega
    have hsum : n + (-1 : ℤ) = n - 1 := by omega
    rw [hsum] at hc
    simp only [if_neg hn0', LinearMap.sub_apply, Module.End.mul_apply] at hc
    simpa [hv n hn, hv (n-1) hn2, if_neg hn0'] using hc

theorem translation_mem_primary_zero_to_one
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (v : Carrier D)
    (hv : v ∈ primarySpace D H 0) : translation D v ∈ primarySpace D H 1 := by
  rw [mem_primarySpace_iff] at hv ⊢
  exact ⟨translation_weight D H hHG hGH 0 v (by simpa using hv.1),
    translation_primary D H hHG hGH v hv.2 (by simpa using hv.1)⟩

def translationP (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    primarySpace D H 0 →ₗ[ℂ] primarySpace D H 1 where
  toFun v := ⟨translation D v.1, translation_mem_primary_zero_to_one D H hHG hGH v.1 v.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

private theorem zeroMode_energy (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (a b : Carrier D) (alpha beta : ℂ)
    (ha : actualL D H 0 a = alpha • a)
    (hb : actualL D H 0 b = beta • b) :
    actualL D H 0 (mu D a 0 b) = (alpha + beta - 1) • mu D a 0 b := by
  simpa [actualL, mu] using
    fused_eigenstate_energy D H hHG hGH a b alpha beta ha hb 0

private theorem zeroMode_primary (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (a b : Carrier D)
    (ha : ∀ n : ℤ, 0 < n → actualL D H n a = 0)
    (hb : ∀ n : ℤ, 0 < n → actualL D H n b = 0)
    (ha0 : actualL D H 0 a = (1 : ℂ) • a) :
    ∀ n : ℤ, 0 < n → actualL D H n (mu D a 0 b) = 0 := by
  intro n hn
  have hward := congrArg (fun A : Module.End ℂ (Carrier D) => A b)
    (ward_commutator D H a n 0)
  have finite : (∑ᶠ j : ℕ, wardTerm D H a n 0 j) =
      ∑ j ∈ Finset.range 2, wardTerm D H a n 0 j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hnot
    have hj2 : 2 ≤ j := by
      have hjlt : ¬ j < 2 := by simpa [Finset.mem_range] using hnot
      omega
    have hpos : 0 < (j : ℤ) - 1 := by omega
    have hzero : actualL D H ((j : ℤ) - 1) a = 0 := ha ((j : ℤ) - 1) hpos
    apply hj
    simp [wardTerm, hzero]
  rw [finite] at hward
  norm_num [wardTerm, integerBinomial] at hward
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Int.cast_zero, zero_sub,
    add_zero] at hward
  have hminus : sugawaraMode D H (-1) = translation D :=
    sugawaraMode_minus_one_eq_translation D H hHG hGH
  have hzero : (↑(0 : ℕ) - 1 : ℤ) = -1 := by norm_num
  rw [hzero, hminus] at hward
  have hidx0 : n + 1 - (↑(0 : ℕ) : ℤ) = n + 1 := by omega
  have hidx1 : n + 1 - (↑(1 : ℕ) : ℤ) = n := by omega
  have hone : (↑(1 : ℕ) - 1 : ℤ) = 0 := by norm_num
  rw [hidx0, hidx1, hone] at hward
  have hderiv := state_derivative_modes D a (n + 1)
  have hidxd : n + 1 - 1 = n := by omega
  rw [hidxd] at hderiv
  rw [hderiv] at hward
  rw [ha0, hb n hn] at hward
  simp only [mu, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    map_zero, zero_smul, sub_zero, zero_add, one_smul] at hward
  simp only [Ring.choose_zero_right, Ring.choose_one_right, Int.cast_one,
    Int.cast_add, add_zero, one_smul] at hward
  rw [← add_smul] at hward
  have hcoef' : (-((n : ℂ) + 1) + ((n : ℂ) + 1)) = 0 := by ring
  rw [hcoef', zero_smul] at hward
  simpa [mu] using hward

theorem zeroMode_mem_primary_one (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (a b : Carrier D)
    (ha : a ∈ primarySpace D H 1) (hb : b ∈ primarySpace D H 1) :
    mu D a 0 b ∈ primarySpace D H 1 := by
  rw [mem_primarySpace_iff] at ha hb ⊢
  refine ⟨?_, ?_⟩
  · convert zeroMode_energy D H hHG hGH a b (1 : ℂ) (1 : ℂ)
      (by simpa using ha.1) (by simpa using hb.1) using 1 <;>
      norm_num
  · exact zeroMode_primary D H hHG hGH a b ha.2 hb.2 (by simpa using ha.1)

theorem zeroMode_mem_primary_zero (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (a : Carrier D) (b : Carrier D)
    (ha : a ∈ primarySpace D H 1) (hb : b ∈ primarySpace D H 0) :
    mu D a 0 b ∈ primarySpace D H 0 := by
  rw [mem_primarySpace_iff] at ha hb ⊢
  refine ⟨?_, ?_⟩
  · convert zeroMode_energy D H hHG hGH a b (1 : ℂ) (0 : ℂ)
      (by simpa using ha.1) (by simpa using hb.1) using 1 <;>
      norm_num
  · exact zeroMode_primary D H hHG hGH a b ha.2 hb.2 (by simpa using ha.1)

private def zeroModeCarrier : Carrier D →ₗ[ℂ] Carrier D →ₗ[ℂ] Carrier D :=
  LinearMap.mk₂ ℂ (fun a b => mu D a 0 b)
    (by intro a₁ a₂ b; simp [LatticeAllStateReconstruction.mu])
    (by intro c a b; simp [LatticeAllStateReconstruction.mu])
    (by intro a b₁ b₂; simp [LatticeAllStateReconstruction.mu])
    (by intro c a b; simp [LatticeAllStateReconstruction.mu])

def zeroModeP (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    primarySpace D H 1 →ₗ[ℂ]
    primarySpace D H 1 →ₗ[ℂ] primarySpace D H 1 :=
  LinearMap.mk₂ ℂ
    (fun a b =>
      ⟨zeroModeCarrier D a.1 b.1,
        zeroMode_mem_primary_one D H hHG hGH a.1 b.1 a.2 b.2⟩)
    (by intro a₁ a₂ b; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])
    (by intro c a b; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])
    (by intro a b₁ b₂; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])
    (by intro c a b; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])

private def zeroModeP10 (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    primarySpace D H 1 →ₗ[ℂ]
    primarySpace D H 0 →ₗ[ℂ] primarySpace D H 0 :=
  LinearMap.mk₂ ℂ
    (fun a b =>
      ⟨zeroModeCarrier D a.1 b.1,
        zeroMode_mem_primary_zero D H hHG hGH a.1 b.1 a.2 b.2⟩)
    (by intro a₁ a₂ b; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])
    (by intro c a b; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])
    (by intro a b₁ b₂; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])
    (by intro c a b; apply Subtype.ext; simp [zeroModeCarrier, LatticeAllStateReconstruction.mu])

private def skewBound (b a : Carrier D) : ℕ :=
  (-((HahnModule.of ℂ).symm (Y D b a)).order - 1).toNat

private def skewPrimitiveTerm (a b : Carrier D) (j : ℕ) : Carrier D :=
  (((-1 : ℂ) ^ (j + 2 : ℕ)) / ((j + 1).factorial : ℂ)) •
    ((translation D ^ j) (mu D b (j + 1 : ℤ) a))

private def skewPrimitive (a b : Carrier D) : Carrier D :=
  ∑ j ∈ Finset.range (skewBound D b a + 1), skewPrimitiveTerm D a b j

private theorem sum_range_succ_sub (f : ℕ → Carrier D) (N : ℕ) :
    (∑ j ∈ Finset.range N, f (j+1)) =
      (∑ j ∈ Finset.range (N+1), f j) - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    abel

private theorem skew_primitive_identity (a b : Carrier D) :
    translation D (skewPrimitive D a b) = mu D a 0 b + mu D b 0 a := by
  let F : ℕ → Carrier D := fun k =>
    (((-1 : ℂ) ^ (k + 1 : ℕ)) / (k.factorial : ℂ)) •
      ((translation D ^ k) (mu D b (k : ℤ) a))
  let N := skewBound D b a + 1
  have hF : ∀ k > skewBound D b a, F k = 0 := by
    intro k hk
    have hz : mu D b (k : ℤ) a = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      simp only [skewBound] at hk
      omega
    simp [F, hz]
  have hsum : (∑ᶠ k : ℕ, F k) = ∑ k ∈ Finset.range (N+1), F k := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hnot
    have hkN : N + 1 ≤ k := by
      simpa [Finset.mem_range] using hnot
    have hkbound : skewBound D b a < k := by
      dsimp [N] at hkN
      omega
    exact hk (hF k hkbound)
  have hshift : (∑ᶠ j : ℕ, F (j+1)) =
      (∑ k ∈ Finset.range N, F (k+1)) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hnot
    have hkN : N ≤ k := by
      simpa [Finset.mem_range] using hnot
    have hkbound : skewBound D b a < k + 1 := by
      dsimp [N] at hkN
      omega
    exact hk (hF (k+1) hkbound)
  have hskew := (skew_symmetry (actualVertexAlgebra D) a b).1 0
  have hskew' : mu D a 0 b = ∑ᶠ k : ℕ, F k := by
    have hskew2 : ((Y D a)[[0]]) b =
        ∑ᶠ j : ℕ, (((-1 : ℂ) ^ (j + 1)) / (j.factorial : ℂ)) •
          ((translation D ^ j) (mu D b (j : ℤ) a)) := by
      convert hskew.2 using 1
      · simp [actualVertexAlgebra]
      · apply finsum_congr
        intro j
        have hpow : (-1 : ℂ) ^ ((j : ℤ) + 1) = (-1 : ℂ) ^ (j + 1 : ℕ) := by
          rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, zpow_natCast]
        simpa [actualVertexAlgebra, LatticeAllStateReconstruction.mu, hpow]
    change ((Y D a)[[0]]) b = ∑ᶠ k : ℕ, F k
    simpa [F] using hskew2
  have hmap : translation D (skewPrimitive D a b) =
      ∑ k ∈ Finset.range N, F (k+1) := by
    rw [skewPrimitive, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [skewPrimitiveTerm, F, map_smul, Module.End.mul_apply,
      pow_succ', LinearMap.smul_apply]
    norm_num [Nat.cast_add]
  calc
    translation D (skewPrimitive D a b) = ∑ k ∈ Finset.range N, F (k+1) := hmap
    _ = (∑ k ∈ Finset.range (N+1), F k) - F 0 := sum_range_succ_sub D F N
    _ = (∑ᶠ k : ℕ, F k) - F 0 := by rw [← hsum]
    _ = mu D a 0 b - F 0 := by rw [hskew']
    _ = mu D a 0 b + mu D b 0 a := by simp [F, LatticeAllStateReconstruction.mu]

private theorem translation_power_weight (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (h : ℤ) (j : ℕ) (v : Carrier D)
    (hv : actualL D H 0 v = (h : ℂ) • v) :
    actualL D H 0 ((translation D ^ j) v) = ((h + j : ℤ) : ℂ) • ((translation D ^ j) v) := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ']
    have hi := translation_weight D H hHG hGH (h+j) ((translation D ^ j) v) ih
    simpa [pow_succ', Module.End.mul_apply, Int.cast_add, Int.cast_natCast, add_assoc] using hi

private theorem skewPrimitive_weight (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (a b : Carrier D)
    (ha : a ∈ primarySpace D H 1) (hb : b ∈ primarySpace D H 1) :
    actualL D H 0 (skewPrimitive D a b) = 0 := by
  rw [skewPrimitive, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have ha0 := (mem_primarySpace_iff D H 1 a).mp ha |>.1
  have hb0 := (mem_primarySpace_iff D H 1 b).mp hb |>.1
  have hmode := fused_eigenstate_energy D H hHG hGH b a (1 : ℂ) (1 : ℂ)
    (by simpa using hb0) (by simpa using ha0) (j+1 : ℤ)
  have hpower := translation_power_weight D H hHG hGH (-j : ℤ) j
    (mu D b (j+1 : ℤ) a)
    (by simpa [actualL, mu, Int.cast_natCast] using hmode)
  simp only [skewPrimitiveTerm, Module.End.mul_apply, map_smul,
    LinearMap.smul_apply] at hpower ⊢
  rw [hpower]
  simp [smul_smul, Int.cast_sub, Int.cast_one, Int.cast_natCast]

private theorem sl2_raise_weight {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e h : Module.End ℂ V) (lambda : ℂ) (v : V)
    (hh : h v = lambda • v)
    (hcomm : h * e - e * h = -(1 : ℂ) • e) (k : ℕ) :
    h ((e ^ k) v) = (lambda - (k : ℂ)) • ((e ^ k) v) := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have hc := congrArg (fun A : Module.End ℂ V => A ((e ^ k) v)) hcomm
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hc
    rw [ih] at hc
    simp only [map_smul, LinearMap.smul_apply] at hc
    have hc' := sub_eq_iff_eq_add.mp hc
    simpa [sub_eq_add_neg, add_smul, smul_add, add_comm, add_left_comm, add_assoc] using hc'

private theorem sl2_lower_raise {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e f h : Module.End ℂ V)
    (hcomm : e * f - f * e = (2 : ℂ) • h) (v : V) :
    f (e v) = e (f v) - (2 : ℂ) • h v := by
  have hc := congrArg (fun A : Module.End ℂ V => A v) hcomm
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hc
  have hc' := sub_eq_iff_eq_add.mp hc
  apply Eq.symm
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using hc'

private theorem sl2_lower_power {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e f h : Module.End ℂ V) (lambda : ℂ) (v : V)
    (hh : h v = lambda • v) (hf : f v = 0)
    (hraise : h * e - e * h = -(1 : ℂ) • e)
    (hcomm : e * f - f * e = (2 : ℂ) • h) :
    ∀ k : ℕ, 0 < k →
      f ((e ^ k) v) =
        (-(k : ℂ) * (2 * lambda - (k : ℂ) + 1)) • ((e ^ (k-1)) v) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    rw [pow_succ']
    have hstep := sl2_lower_raise e f h hcomm ((e ^ k) v)
    have hp := sl2_raise_weight e h lambda v hh hraise k
    by_cases hk0 : k = 0
    · subst k
      simp only [pow_zero, Module.End.one_apply, map_zero, zero_smul,
        sub_zero, Nat.cast_zero, mul_zero, zero_add, one_smul] at hstep ⊢
      rw [hf, hh] at hstep
      simpa [smul_smul] using hstep
    · have hprev := ih (by omega)
      change f (e ((e ^ k) v)) = _
      rw [hstep, hprev, hp]
      simp only [map_smul, LinearMap.smul_apply]
      have hepow : e ((e ^ (k - 1)) v) = (e ^ k) v := by
        change ((e * (e ^ (k - 1))) v) = _
        rw [← pow_succ']
        rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      rw [hepow]
      simp only [Nat.add_sub_cancel]
      module

private theorem translation_injective_negative (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (n : ℕ) (hn : 0 < n)
    (v : Carrier D)
    (hv : actualL D H 0 v = (-(n : ℤ) : ℂ) • v)
    (hTv : translation D v = 0) : v = 0 := by
  let e : Module.End ℂ (Carrier D) := actualL D H 1
  let f : Module.End ℂ (Carrier D) := actualL D H (-1)
  let h : Module.End ℂ (Carrier D) := actualL D H 0
  have hraise : h * e - e * h = -(1 : ℂ) • e := by
    simpa [e, h, sub_eq_add_neg] using virasoro_comm D H hHG hGH 0 1
  have hcomm : e * f - f * e = (2 : ℂ) • h := by
    simpa [e, f, h, translation_eq D H hHG hGH] using
      virasoro_comm D H hHG hGH 1 (-1)
  obtain ⟨k, hk⟩ := sugawara_one_locally_nilpotent D H hHG hGH v
  by_cases hv0 : v = 0
  · exact hv0
  have hex : ∃ m : ℕ, (e ^ m) v = 0 := by
    simpa [e] using (show ∃ m : ℕ, (actualL D H 1 ^ m) v = 0 from ⟨k, hk⟩)
  let k₀ := Nat.find hex
  have hk₀ : (e ^ k₀) v = 0 := by
    exact Nat.find_spec hex
  have hkpos : 0 < k₀ := by
    by_contra hkz
    have : k₀ = 0 := by omega
    exact hv0 (by simpa [this] using hk₀)
  have hkprev : (e ^ (k₀ - 1)) v ≠ 0 := by
    intro hz
    have hmin := Nat.find_min' hex hz
    omega
  have hTv' : f v = 0 := by
    change actualL D H (-1) v = 0
    rw [translation_eq D H hHG hGH]
    exact hTv
  have hlower := sl2_lower_power e f h (-(n : ℂ)) v
    (by simpa [e, h] using hv) hTv'
    hraise hcomm k₀ hkpos
  rw [hk₀] at hlower
  have hscalar : (-(k₀ : ℂ) * (2 * (-(n : ℂ)) - (k₀ : ℂ) + 1)) ≠ 0 := by
    intro hs
    have hs' : (k₀ : ℂ) * (2 * (-(n : ℂ)) - (k₀ : ℂ) + 1) = 0 := by
      simpa only [neg_mul, neg_eq_zero] using hs
    rcases mul_eq_zero.mp hs' with hkzero | hsecond
    · have hkzero : k₀ = 0 := by exact_mod_cast hkzero
      omega
    · have hsecond' : 2 * (n : ℂ) + (k₀ : ℂ) - 1 = 0 := by
        calc
          2 * (n : ℂ) + (k₀ : ℂ) - 1 =
              -(2 * (-(n : ℂ)) - (k₀ : ℂ) + 1) := by ring
          _ = 0 := by rw [hsecond]; simp
      have hz : (2 : ℤ) * (n : ℤ) + (k₀ : ℤ) - (1 : ℤ) = 0 := by
        exact_mod_cast hsecond'
      omega
  have hlower' : 0 =
      (-(k₀ : ℂ) * (2 * (-(n : ℂ)) - (k₀ : ℂ) + 1)) •
        ((e ^ (k₀ - 1)) v) := by simpa using hlower
  have : (e ^ (k₀ - 1)) v = 0 := by
    exact (smul_eq_zero.mp hlower'.symm).resolve_left (by simpa using hscalar)
  exact (hkprev this).elim

private theorem mode_weight_of_zero (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (n : ℤ) (v : Carrier D)
    (hv : actualL D H 0 v = 0) (hn : n ≠ 0) :
    actualL D H 0 (actualL D H n v) = (-(n : ℂ)) • actualL D H n v := by
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
    (virasoro_comm D H hHG hGH 0 n)
  simp only [zero_sub, Int.cast_zero, zero_add, if_neg hn, zero_pow, zero_sub,
    sub_zero, zero_smul, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at hc
  rw [hv] at hc
  simp only [map_zero, zero_smul, sub_zero, zero_add] at hc
  simpa [add_comm] using hc

private theorem skewPrimitive_primary (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (a b : Carrier D)
    (ha : a ∈ primarySpace D H 1) (hb : b ∈ primarySpace D H 1) :
    skewPrimitive D a b ∈ primarySpace D H 0 := by
  have hs0 := skewPrimitive_weight D H hHG hGH a b ha hb
  have hts : translation D (skewPrimitive D a b) ∈ primarySpace D H 1 := by
    rw [skew_primitive_identity D a b]
    exact Submodule.add_mem _
      (zeroMode_mem_primary_one D H hHG hGH a b ha hb)
      (zeroMode_mem_primary_one D H hHG hGH b a hb ha)
  have hts' := (mem_primarySpace_iff D H 1 (translation D (skewPrimitive D a b))).mp hts
  rw [mem_primarySpace_iff]
  refine ⟨by simpa using hs0, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn_nonneg : 0 ≤ n := le_of_lt hn
  let k : ℕ := n.toNat
  have hn_eq : (k : ℤ) = n := by dsimp [k]; omega
  rw [← hn_eq]
  induction k with
  | zero => simpa using hs0
  | succ k ih =>
    have hcomm := congrArg (fun A : Module.End ℂ (Carrier D) => A (skewPrimitive D a b))
      (virasoro_comm D H hHG hGH (k + 1 : ℤ) (-1))
    rw [translation_eq D H hHG hGH] at hcomm
    have hright : actualL D H (k + 1 : ℤ) (translation D (skewPrimitive D a b)) = 0 :=
      hts'.2 (k + 1 : ℤ) (by omega)
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_neg_cancel,
      if_false, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, map_zero, zero_smul, sub_zero, zero_add] at hcomm
    have hidx : (k : ℤ) + 1 + (-1 : ℤ) = (k : ℤ) := by omega
    by_cases hkz : k = 0
    · subst k
      have hright0 : actualL D H 1 (translation D (skewPrimitive D a b)) = 0 :=
        hts'.2 1 (by norm_num)
      have hi0 : actualL D H 0 (skewPrimitive D a b) = 0 := by simpa using ih
      simp at hcomm
      rw [hright0, hi0] at hcomm
      simp at hcomm
      have hT : translation D (actualL D H 1 (skewPrimitive D a b)) = 0 := by
        apply neg_eq_zero.mp
        simpa using hcomm
      have hw := mode_weight_of_zero D H hHG hGH 1 (skewPrimitive D a b) hs0
        (by norm_num)
      simpa using
        (translation_injective_negative D H hHG hGH 1 (by norm_num)
          (actualL D H 1 (skewPrimitive D a b)) hw hT)
    · have hk0 : (k : ℤ) + 1 + (-1 : ℤ) ≠ 0 := by
        rw [hidx]
        exact_mod_cast hkz
      simp [hidx, hk0] at hcomm
      rw [hright, ih] at hcomm
      simp [hkz] at hcomm
      have hT : translation D (actualL D H (k + 1 : ℤ) (skewPrimitive D a b)) = 0 := by
        apply neg_eq_zero.mp
        simpa using hcomm
      have hw := mode_weight_of_zero D H hHG hGH (k + 1 : ℤ) (skewPrimitive D a b) hs0
        (by omega)
      simpa [Int.cast_add, Int.cast_natCast] using
        (translation_injective_negative D H hHG hGH (k+1) (by omega)
          (actualL D H (k + 1 : ℤ) (skewPrimitive D a b)) hw hT)

private theorem zeroMode_translation_left (u b : Carrier D) :
    zeroModeCarrier D (translation D u) b = 0 := by
  simp [zeroModeCarrier, mu, state_derivative_modes]

private theorem zeroMode_translation_right (a u : Carrier D) :
    zeroModeCarrier D a (translation D u) =
      translation D (zeroModeCarrier D a u) := by
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A u)
    (stateField_covariance D a 0)
  simp only [Int.cast_zero, zero_smul, sub_zero, LinearMap.sub_apply,
    Module.End.mul_apply] at hc
  norm_num at hc
  change ((Y D a)[[0]]) (translation D u) = translation D (((Y D a)[[0]]) u)
  exact (sub_eq_zero.mp hc).symm

def physicalIdeal : Submodule ℂ (primarySpace D H 1) :=
  LinearMap.range (translationP D H hHG hGH)

abbrev physicalQuotient := primarySpace D H 1 ⧸ physicalIdeal D H hHG hGH

private def quotientZeroMode : primarySpace D H 1 →ₗ[ℂ]
    primarySpace D H 1 →ₗ[ℂ] physicalQuotient D H hHG hGH :=
  LinearMap.mk₂ ℂ
    (fun a b => (physicalIdeal D H hHG hGH).mkQ (zeroModeP D H hHG hGH a b))
    (by
      intro a₁ a₂ b
      change ((physicalIdeal D H hHG hGH).mkQ
        (zeroModeP D H hHG hGH (a₁ + a₂) b)) = _
      rw [(zeroModeP D H hHG hGH).map_add]
      simp only [LinearMap.add_apply, map_add])
    (by
      intro c a b
      change ((physicalIdeal D H hHG hGH).mkQ
        (zeroModeP D H hHG hGH (c • a) b)) = _
      rw [(zeroModeP D H hHG hGH).map_smul]
      simp only [LinearMap.smul_apply, map_smul])
    (by
      intro a b₁ b₂
      change ((physicalIdeal D H hHG hGH).mkQ
        (zeroModeP D H hHG hGH a (b₁ + b₂))) = _
      rw [(zeroModeP D H hHG hGH a).map_add]
      simp only [LinearMap.add_apply, map_add])
    (by
      intro c a b
      change ((physicalIdeal D H hHG hGH).mkQ
        (zeroModeP D H hHG hGH a (c • b))) = _
      rw [(zeroModeP D H hHG hGH a).map_smul]
      simp only [LinearMap.smul_apply, map_smul])

private theorem quotientZeroMode_left_ideal
    (x : primarySpace D H 1) (hx : x ∈ physicalIdeal D H hHG hGH) :
    x ∈ (quotientZeroMode D H hHG hGH).ker := by
  rcases hx with ⟨u, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  simp only [quotientZeroMode, LinearMap.mk₂_apply]
  change (physicalIdeal D H hHG hGH).mkQ
      (zeroModeP D H hHG hGH (translationP D H hHG hGH u) y) = 0
  rw [← Submodule.Quotient.mk_zero]
  apply (Submodule.Quotient.eq _).mpr
  have hzmem : zeroModeP D H hHG hGH (translationP D H hHG hGH u) y ∈
      physicalIdeal D H hHG hGH := by
    
    have hz : zeroModeP D H hHG hGH (translationP D H hHG hGH u) y = 0 := by
      apply Subtype.ext
      exact zeroMode_translation_left D (u : Carrier D) (y : Carrier D)
    rw [hz]
    exact Submodule.zero_mem _
  simpa using hzmem

private theorem quotientZeroMode_right_ideal
    (x : primarySpace D H 1) (hx : x ∈ physicalIdeal D H hHG hGH) :
    x ∈ (quotientZeroMode D H hHG hGH).flip.ker := by
  rcases hx with ⟨u, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  simp only [quotientZeroMode, LinearMap.mk₂_apply, LinearMap.flip_apply]
  change (physicalIdeal D H hHG hGH).mkQ
      (zeroModeP D H hHG hGH y (translationP D H hHG hGH u)) = 0
  rw [← Submodule.Quotient.mk_zero]
  apply (Submodule.Quotient.eq _).mpr
  have hzmem : zeroModeP D H hHG hGH y (translationP D H hHG hGH u) ∈
      physicalIdeal D H hHG hGH := by
    refine ⟨zeroModeP10 D H hHG hGH y u, ?_⟩
    apply Subtype.ext
    exact (zeroMode_translation_right D (y : Carrier D) (u : Carrier D)).symm
  simpa using hzmem

def physicalBracket : physicalQuotient D H hHG hGH →ₗ[ℂ]
    physicalQuotient D H hHG hGH →ₗ[ℂ] physicalQuotient D H hHG hGH :=
  (quotientZeroMode D H hHG hGH).liftQ₂
    (physicalIdeal D H hHG hGH) (physicalIdeal D H hHG hGH)
    (quotientZeroMode_left_ideal D H hHG hGH)
    (quotientZeroMode_right_ideal D H hHG hGH)

private theorem zeroMode_leibniz (a b c : Carrier D) :
    zeroModeCarrier D a (zeroModeCarrier D b c) =
      zeroModeCarrier D (zeroModeCarrier D a b) c +
        zeroModeCarrier D b (zeroModeCarrier D a c) := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A c)
    (mode_commutator D a b 0 0)
  have hz : (∑ᶠ j : ℕ, commutatorTerm D a b 0 0 j) =
      commutatorTerm D a b 0 0 0 := by
    rw [finsum_eq_single _ 0]
    · intro j hj
      simp [commutatorTerm, StateFieldResidueReconstruction.integerBinomial,
        Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  rw [hz] at h
  have h' := sub_eq_iff_eq_add.mp h
  simpa [zeroModeCarrier, commutatorTerm, StateFieldResidueReconstruction.integerBinomial,
    mu, add_assoc] using h'

private theorem physicalBracket_add_self (x y : physicalQuotient D H hHG hGH) :
    physicalBracket D H hHG hGH x y + physicalBracket D H hHG hGH y x = 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  simp only [physicalBracket, LinearMap.liftQ₂_mk, quotientZeroMode]
  change (physicalIdeal D H hHG hGH).mkQ (zeroModeP D H hHG hGH a b) +
      (physicalIdeal D H hHG hGH).mkQ (zeroModeP D H hHG hGH b a) = 0
  have hs := skewPrimitive_primary D H hHG hGH a.1 b.1 a.2 b.2
  rw [← (physicalIdeal D H hHG hGH).mkQ.map_add]
  rw [← (physicalIdeal D H hHG hGH).mkQ.map_zero]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨⟨skewPrimitive D a.1 b.1, hs⟩, ?_⟩
  apply Subtype.ext
  simpa [translationP, zeroModeP, zeroModeCarrier,
    LatticeAllStateReconstruction.mu] using
    (skew_primitive_identity D a.1 b.1)

private theorem physicalBracket_leibniz
    (x y z : physicalQuotient D H hHG hGH) :
    physicalBracket D H hHG hGH x (physicalBracket D H hHG hGH y z) =
      physicalBracket D H hHG hGH (physicalBracket D H hHG hGH x y) z +
        physicalBracket D H hHG hGH y (physicalBracket D H hHG hGH x z) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  refine Submodule.Quotient.induction_on _ z ?_
  intro c
  simp only [physicalBracket, LinearMap.liftQ₂_mk, quotientZeroMode]
  change (physicalIdeal D H hHG hGH).mkQ
      (zeroModeP D H hHG hGH a (zeroModeP D H hHG hGH b c)) =
      (physicalIdeal D H hHG hGH).mkQ
          (zeroModeP D H hHG hGH (zeroModeP D H hHG hGH a b) c) +
        (physicalIdeal D H hHG hGH).mkQ
          (zeroModeP D H hHG hGH b (zeroModeP D H hHG hGH a c))
  have hz : zeroModeP D H hHG hGH a (zeroModeP D H hHG hGH b c) =
      zeroModeP D H hHG hGH (zeroModeP D H hHG hGH a b) c +
        zeroModeP D H hHG hGH b (zeroModeP D H hHG hGH a c) := by
    apply Subtype.ext
    exact zeroMode_leibniz D a.1 b.1 c.1
  rw [← (physicalIdeal D H hHG hGH).mkQ.map_add]
  exact congrArg (physicalIdeal D H hHG hGH).mkQ hz

instance physicalLieRing : LieRing (physicalQuotient D H hHG hGH) where
  __ := (inferInstance : AddCommGroup (physicalQuotient D H hHG hGH))
  bracket := fun x y => physicalBracket D H hHG hGH x y
  add_lie := by intro x y z; simp [physicalBracket, map_add]
  lie_add := by intro x y z; simp [physicalBracket, map_add]
  lie_self := by
    intro x
    have h := physicalBracket_add_self D H hHG hGH x x
    have h' : (2 : ℂ) • physicalBracket D H hHG hGH x x = 0 := by
      simpa [two_smul] using h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  leibniz_lie := by
    intro x y z
    exact physicalBracket_leibniz D H hHG hGH x y z

instance physicalLieAlgebra : LieAlgebra ℂ (physicalQuotient D H hHG hGH) where
  __ := (inferInstance : Module ℂ (primarySpace D H 1 ⧸ physicalIdeal D H hHG hGH))
  lie_smul := by intro t x y; exact (physicalBracket D H hHG hGH x).map_smul t y

theorem physicalBracket_mk (a b : primarySpace D H 1) :
    ⁅(physicalIdeal D H hHG hGH).mkQ a, (physicalIdeal D H hHG hGH).mkQ b⁆ =
      (physicalIdeal D H hHG hGH).mkQ (zeroModeP D H hHG hGH a b) := by
  change physicalBracket D H hHG hGH ((physicalIdeal D H hHG hGH).mkQ a)
      ((physicalIdeal D H hHG hGH).mkQ b) = _
  simp [physicalBracket, quotientZeroMode, LinearMap.liftQ₂_mk, LinearMap.mk₂_apply]

end
end D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie
