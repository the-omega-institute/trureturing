/- GID: D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original corrected-field formal Mobius coefficients at every order. -/

import D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast

/-! Formal-u covariance on the original algebraic carriers. Multiplication of
endomorphisms acts right to left. No numeric target exponential is asserted.
The binomial-series implementation is due to Scott Carnahan (Apache 2.0);
the original lattice and current attributions remain with their suppliers. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeSugawaraCurrents
open LatticeHalfFockChargedTensorCoefficients LatticePositiveEnergy
open scoped BigOperators
noncomputable section

private abbrev A (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  (LinearMap.proj e).comp
    (HVertexOperator.coeff.comp (LatticeHalfFockCorrectedField.correctedField D hu))

private abbrev T (D : LatticeData) (hu : IsUnit D.G.det) :=
  tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1

private abbrev S (D : LatticeData) (j : ℤ) := sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ j

private def ad (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (Module.End ℂ (ActualTensor D hu)) :=
  LinearMap.mulLeft ℂ (T D hu) - LinearMap.mulRight ℂ (T D hu)

private def dividedAd (D : LatticeData) (hu : IsUnit D.G.det) (n : ℕ) (e : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  (n.factorial : ℂ)⁻¹ • ((ad D hu ^ n).comp (A D hu e))

private theorem inverse_eq (D : LatticeData) (hu : IsUnit D.G.det) :
    (LatticeSugawaraCurrents.gramComplex D)⁻¹ = HalfFockSpectralFiberSource.actualInverse D :=
  Matrix.inv_eq_left_inv (HalfFockSpectralFiberSource.actualInverse_left D hu)

private theorem source_weight_lowering (D : LatticeData) (hu : IsUnit D.G.det)
    (h : ℤ) (a : Carrier D) (ha : S D 0 a = (h : ℂ) • a) (k : ℕ) :
    S D 0 ((S D 1 ^ k) a) = ((h : ℂ) - (k : ℂ)) • (S D 1 ^ k) a := by
  have hv := LatticeSugawaraVirasoro.sugawaraMode_virasoro D
    (HalfFockSpectralFiberSource.actualInverse D)
    (HalfFockSpectralFiberSource.actualInverse_left D hu)
    (HalfFockSpectralFiberSource.actualInverse_right D hu) 0 1
  rw [← inverse_eq D hu] at hv
  have comm : S D 0 * S D 1 - S D 1 * S D 0 = -(S D 1) := by
    simpa [S] using hv
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    have hc := LinearMap.congr_fun comm ((S D 1 ^ k) a)
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply] at hc
    rw [ih, map_smul] at hc
    rw [pow_succ', Module.End.mul_apply]
    push_cast
    linear_combination (norm := module) hc

private theorem dividedAd_step (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (e : ℤ) (a : Carrier D) :
    (n + 1 : ℂ) • dividedAd D hu (n+1) e a = ad D hu (dividedAd D hu n e a) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [dividedAd, LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_smul,
    pow_succ', Module.End.mul_apply]
  congr 1
  field_simp

private def c (α : ℂ) (n k : ℕ) : ℂ :=
  if k ≤ n then Ring.choose (α - (k : ℂ)) (n-k) / (k.factorial : ℂ) else 0

private theorem choose_step (r : ℂ) (q : ℕ) :
    (q+1 : ℂ) * Ring.choose r (q+1) = (r-(q:ℂ)) * Ring.choose r q := by
  have h := Ring.choose_smul_choose r (by omega : q ≤ q+1)
  simpa [Nat.choose_succ_self_right, nsmul_eq_mul, mul_comm] using h

private theorem c_step_zero (α : ℂ) (n : ℕ) :
    (n+1 : ℂ) * c α (n+1) 0 = (α-(n:ℂ)) * c α n 0 := by
  simpa [c] using choose_step α n

private theorem c_step_succ (α : ℂ) (n k : ℕ) (hk : k ≤ n) :
    (n+1 : ℂ) * c α (n+1) (k+1) =
      c α n k + (α-(n:ℂ)-(k+1:ℂ)) * c α n (k+1) := by
  by_cases top : k=n
  · subst k
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hs : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [c, le_refl, ite_true, Nat.sub_self, Ring.choose_zero_right,
      Nat.not_succ_le_self, ite_false, mul_zero, add_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  · have hkn : k+1 ≤ n := by omega
    let m := n-(k+1)
    have split : n-k = m+1 := by omega
    have count : (n:ℂ) = (m:ℂ)+(k:ℂ)+1 := by exact_mod_cast (by omega : n=m+k+1)
    have hp := Ring.choose_succ_succ (α-(k+1:ℂ)) m
    have hs := choose_step (α-(k+1:ℂ)) m
    have ht : α-(k+1:ℂ)+1 = α-(k:ℂ) := by ring
    rw [ht] at hp
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hkp : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [c, if_pos hk, if_pos hkn, if_pos (show k+1 ≤ n+1 by omega),
      show n+1-(k+1)=m+1 by omega, show n-(k+1)=m by rfl, split,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hp, count]
    field_simp
    linear_combination hs

private theorem dividedAd_eq_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (e : ℤ) (a : Carrier D) :
    dividedAd D hu n e a =
      ∑ i ∈ Finset.range (n+1),
        ((-1:ℂ)^(n-i) / ((i.factorial:ℂ) * ((n-i).factorial:ℂ))) •
          (T D hu ^ i * A D hu e a * T D hu ^ (n-i)) := by
  have comm := (LinearMap.commute_mulLeft_right (R := ℂ) (T D hu) (T D hu)).neg_right
  have expansion := comm.add_pow n
  have term (i : ℕ) :
      ((LinearMap.mulLeft ℂ (T D hu)) ^ i *
        (-LinearMap.mulRight ℂ (T D hu)) ^ (n-i) * (n.choose i :
          Module.End ℂ (Module.End ℂ (ActualTensor D hu)))) (A D hu e a) =
      ((n.choose i:ℂ) * (-1:ℂ)^(n-i)) •
        (T D hu ^ i * A D hu e a * T D hu ^ (n-i)) := by
    rw [show -(LinearMap.mulRight ℂ (T D hu)) =
      (-1:ℂ) • LinearMap.mulRight ℂ (T D hu) by exact (neg_one_smul ℂ _).symm]
    simp only [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight,
      Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
      LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      ← Nat.cast_smul_eq_nsmul ℂ, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      smul_smul, mul_assoc]
    module
  change (n.factorial:ℂ)⁻¹ • (ad D hu ^ n) (A D hu e a) = _
  rw [show ad D hu = LinearMap.mulLeft ℂ (T D hu) +
    -LinearMap.mulRight ℂ (T D hu) by rfl, expansion, LinearMap.sum_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [term, smul_smul, Nat.cast_choose ℂ (by have := Finset.mem_range.mp hi; omega)]
  congr 1
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

private theorem sum_step (D : LatticeData) (hu : IsUnit D.G.det)
    (α : ℂ) (n : ℕ) (F : ℕ → Module.End ℂ (ActualTensor D hu)) :
    (n+1:ℂ) • (∑ k ∈ Finset.range (n+2), c α (n+1) k • F k) =
      (∑ k ∈ Finset.range (n+1), c α n k • F (k+1)) +
      ∑ k ∈ Finset.range (n+1), (c α n k * (α-(n:ℂ)-(k:ℂ))) • F k := by
  let g := fun k : ℕ => (c α n k * (α-(n:ℂ)-(k:ℂ))) • F k
  have top : g (n+1) = 0 := by simp [g,c]
  have shift : (∑ k ∈ Finset.range (n+1), g (k+1)) + g 0 =
      ∑ k ∈ Finset.range (n+1), g k := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ, top, add_zero]
  calc
    _ = (∑ k ∈ Finset.range (n+1),
        ((n+1:ℂ)*c α (n+1) (k+1)) • F (k+1)) +
        ((n+1:ℂ)*c α (n+1) 0) • F 0 := by
      rw [Finset.smul_sum, Finset.sum_range_succ']
      simp only [smul_smul]
    _ = (∑ k ∈ Finset.range (n+1), (c α n k • F (k+1) + g (k+1))) + g 0 := by
      rw [c_step_zero]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [c_step_succ α n k (by have := Finset.mem_range.mp hk; omega), add_smul]
        simp only [g, Nat.cast_add, Nat.cast_one, mul_comm]
      · simp [g,mul_comm]
    _ = _ := by
      rw [Finset.sum_add_distrib, add_assoc, shift]

private theorem homogeneous (D : LatticeData) (hu : IsUnit D.G.det)
    (h : ℤ) (a : Carrier D) (ha : S D 0 a = (h:ℂ) • a) (n : ℕ) (e : ℤ) :
    dividedAd D hu n e a =
      ∑ k ∈ Finset.range (n+1), c (2*(h:ℂ)+(e:ℂ)/2-1) n k •
        A D hu (e-2*(n:ℤ)+2*(k:ℤ)) ((S D 1 ^ k) a) := by
  let α : ℂ := 2*(h:ℂ)+(e:ℂ)/2-1
  induction n with
  | zero => simp [dividedAd,c]
  | succ n ih =>
    let F := fun k : ℕ => A D hu (e-2*((n+1:ℕ):ℤ)+2*(k:ℤ)) ((S D 1 ^ k) a)
    have mode (k : ℕ) :
        ad D hu (A D hu (e-2*(n:ℤ)+2*(k:ℤ)) ((S D 1 ^ k) a)) =
          F (k+1) + (α-(n:ℂ)-(k:ℂ)) • F k := by
      have law := ActualMobiusCovariance.corrected_field_l1_coefficient D hu
        ((S D 1 ^ k) a) (e-2*(n:ℤ)+2*(k:ℤ))
      change ad D hu _ = _ at law
      rw [source_weight_lowering D hu h a ha k] at law
      change ad D hu _ = A D hu _ _ + _ • A D hu _ _ +
        (2:ℂ) • A D hu _ (((h:ℂ)-(k:ℂ)) • _) at law
      rw [map_smul] at law
      have first : e-2*((n+1:ℕ):ℤ)+2*((k+1:ℕ):ℤ) = e-2*(n:ℤ)+2*(k:ℤ) := by omega
      have second : e-2*(n:ℤ)+2*(k:ℤ)-2 = e-2*((n+1:ℕ):ℤ)+2*(k:ℤ) := by omega
      dsimp only [F]
      rw [first, pow_succ', Module.End.mul_apply]
      rw [second] at law
      dsimp only [α]
      dsimp only [A, S, LinearMap.comp_apply, LinearMap.proj_apply] at law ⊢
      push_cast at law ⊢
      linear_combination (norm := module) law
    apply smul_right_injective (Module.End ℂ (ActualTensor D hu))
      (show (n+1:ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
    change (n+1:ℂ) • dividedAd D hu (n+1) e a = _
    rw [dividedAd_step D hu n e a, ih, map_sum]
    simp only [map_smul]
    calc
      _ = ∑ k ∈ Finset.range (n+1), c α n k •
          (F (k+1)+(α-(n:ℂ)-(k:ℂ)) • F k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [mode]
      _ = (∑ k ∈ Finset.range (n+1), c α n k • F (k+1)) +
          ∑ k ∈ Finset.range (n+1), (c α n k*(α-(n:ℂ)-(k:ℂ))) • F k := by
        simp only [smul_add, smul_smul, Finset.sum_add_distrib]
      _ = _ := (sum_step D hu α n F).symm

/-- Every formal-u order of conjugation of the ORIGINAL corrected field.
The right side uses the actual finite energy decomposition, signed grades,
the original source S1 and the original tensor T1. -/
theorem corrected_field_mobius_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (e : ℤ) (a : Carrier D) :
    (∑ i ∈ Finset.range (n+1),
      ((-1:ℂ)^(n-i) / ((i.factorial:ℂ) * ((n-i).factorial:ℂ))) •
        (tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ i *
          (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e *
          tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ (n-i))) =
    ∑ h ∈ stateEnergies D a, ∑ k ∈ Finset.range (n+1),
      (Ring.choose (2*(h:ℂ)+(e:ℂ)/2-(k:ℂ)-1) (n-k) / (k.factorial:ℂ)) •
        (LatticeHalfFockCorrectedField.correctedField D hu
          ((sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1 ^ k)
            (gradeProjection D h a))).coeff (e-2*(n:ℤ)+2*(k:ℤ)) := by
  classical
  change (∑ i ∈ Finset.range (n+1),
    ((-1:ℂ)^(n-i) / ((i.factorial:ℂ) * ((n-i).factorial:ℂ))) •
      (T D hu ^ i * A D hu e a * T D hu ^ (n-i))) = _
  rw [← dividedAd_eq_sum D hu n e a]
  have decomp := congrArg (dividedAd D hu n e) (sum_gradeProjections D a)
  rw [map_sum] at decomp
  rw [← decomp]
  apply Finset.sum_congr rfl
  intro h hh
  have eigen : S D 0 (gradeProjection D h a) = (h:ℂ) • gradeProjection D h a := by
    apply (actualL0_eigen_iff_grade D _ ?_ ?_ h _).mpr
    · exact gradeProjection_mem D h a
    · rw [inverse_eq D hu]
      exact HalfFockSpectralFiberSource.actualInverse_left D hu
    · rw [inverse_eq D hu]
      exact HalfFockSpectralFiberSource.actualInverse_right D hu
  rw [homogeneous D hu h _ eigen]
  apply Finset.sum_congr rfl
  intro k hk
  rw [c, if_pos (by have := Finset.mem_range.mp hk; omega)]
  have hs : 2*(h:ℂ)+(e:ℂ)/2-1-(k:ℂ) = 2*(h:ℂ)+(e:ℂ)/2-(k:ℂ)-1 := by ring
  simp only [hs]
  rfl

private def conjugationCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (a : Carrier D) (e : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  ∑ i ∈ Finset.range (n+1),
    ((-1:ℂ)^(n-i) / ((i.factorial:ℂ)*((n-i).factorial:ℂ))) •
      (T D hu ^ i * A D hu e a * T D hu ^ (n-i))

private theorem conjugation_bounded (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (a : Carrier D) (x : ActualTensor D hu) :
    BddBelow (Function.support (fun e => conjugationCoefficient D hu n a e x)) := by
  classical
  let F := LatticeHalfFockCorrectedField.correctedField D hu a
  let orders := fun j : ℕ => ((HahnModule.of ℂ).symm (F ((T D hu ^ j) x))).order
  let b : ℤ := (Finset.range (n+1)).inf' ⟨0, by simp⟩ orders
  refine ⟨b, ?_⟩
  intro e he
  by_contra outside
  have hz : conjugationCoefficient D hu n a e x = 0 := by
    dsimp only [conjugationCoefficient]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have member : n-i ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    have bound : b ≤ orders (n-i) := Finset.inf'_le orders member
    have zero : A D hu e a ((T D hu ^ (n-i)) x) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le (by omega : e < b) bound)
    rw [zero, map_zero, smul_zero]
  exact he hz

/-- The actual field at a fixed formal-u order, constructed using the finite
union of the original field supports on T1^j x. -/
def formalMobiusOrder (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (a : Carrier D) : LatticeHalfFockFockNormalField.NativeField D hu :=
  HVertexOperator.of_coeff (conjugationCoefficient D hu n a)
    (fun x => (conjugation_bounded D hu n a x).isWF.isPWO)

private def unitPower (β : ℂ) : PowerSeries ℂ :=
  PowerSeries.rescale (-1) (PowerSeries.binomialSeries ℂ β)

private theorem unitPower_add (β γ : ℂ) :
    unitPower (β+γ) = unitPower β * unitPower γ := by
  simp [unitPower]

private theorem unitPower_zero : unitPower 0 = 1 := by simp [unitPower]

private theorem unitPower_one : unitPower 1 = 1-PowerSeries.X := by
  have h := PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1
  simp only [Nat.cast_one, pow_one] at h
  simp only [unitPower, h, map_add, map_one, PowerSeries.rescale_X]
  simp [sub_eq_add_neg]

private def powerUnit (β : ℂ) : Units (PowerSeries ℂ) where
  val := unitPower β
  inv := unitPower (-β)
  val_inv := by rw [← unitPower_add, add_neg_cancel, unitPower_zero]
  inv_val := by rw [← unitPower_add, neg_add_cancel, unitPower_zero]

private theorem powerUnit_nat (β : ℂ) (n : ℕ) :
    powerUnit β ^ n = powerUnit ((n:ℂ)*β) := by
  induction n with
  | zero => apply Units.ext; simp [powerUnit,unitPower_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    apply Units.ext
    change unitPower ((n:ℂ)*β) * unitPower β = unitPower (((n+1:ℕ):ℂ)*β)
    rw [← unitPower_add]
    congr 1
    push_cast
    ring

private theorem powerUnit_int (β : ℂ) (d : ℤ) :
    powerUnit β ^ d = powerUnit ((d:ℂ)*β) := by
  cases d with
  | ofNat n => simpa using powerUnit_nat β n
  | negSucc n =>
    rw [zpow_negSucc, powerUnit_nat]
    apply Units.ext
    change unitPower (-(((n+1:ℕ):ℂ)*β)) = unitPower (((Int.negSucc n:ℤ):ℂ)*β)
    congr 1
    push_cast
    ring

/-- The unit factor of f_u(t)=t(1-u*t²)^(-1/2). Its type records both
constant-one normalization and the inverse-square-root equation. -/
def normalizedRawHalfUnit : { f : Units (PowerSeries ℂ) //
    PowerSeries.constantCoeff f.val = 1 ∧ f.val ^ 2 * (1-PowerSeries.X) = 1 } := by
  refine ⟨powerUnit (-1/2), ?_, ?_⟩
  · change PowerSeries.constantCoeff (unitPower (-1/2)) = 1
    simp [unitPower, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · change unitPower (-1/2) ^ 2 * (1-PowerSeries.X) = 1
    rw [pow_two, ← unitPower_add, ← unitPower_one, ← unitPower_add]
    norm_num [unitPower_zero]

private theorem halfUnit_power (d : ℤ) :
    (normalizedRawHalfUnit.val ^ d).val = unitPower (-(d:ℂ)/2) := by
  change (powerUnit (-1/2) ^ d).val = _
  rw [powerUnit_int]
  change unitPower ((d:ℂ)*(-1/2)) = _
  congr 1
  ring

private def sourceCutoff (D : LatticeData) (a : Carrier D) : ℕ :=
  a.support.sup (fun q => MvPolynomial.weightedTotalDegree
    (LatticeHalfFockFiniteCorrection.sourceWeight D) (a q)) + 1

private theorem source_after_cutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (k : ℕ) (hk : sourceCutoff D a ≤ k) : (S D 1 ^ k) a = 0 := by
  have h : (S D 1 ^ sourceCutoff D a) a = 0 := SourceMobius.actual_sugawara_one_bound D hu a
  rw [show k = (k-sourceCutoff D a)+sourceCutoff D a by omega,
    pow_add, Module.End.mul_apply, h, map_zero]

/-- Coefficient extraction from the independent normalized coordinate product.
The power-series variable tracks u. For a raw monomial t^d the complementary
power contributes t^(2(n-k)), so d=e-2(n-k). The source sum is truncated at
the actual oscillator cutoff, rather than assuming a target exponential. -/
def rawHalfCoordinateReadout (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (e : ℤ) (a : Carrier D) : Module.End ℂ (ActualTensor D hu) :=
  ∑ h ∈ stateEnergies D a,
    ∑ k ∈ Finset.range (sourceCutoff D (gradeProjection D h a)),
      (PowerSeries.coeff n (PowerSeries.X ^ k *
        (unitPower ((k:ℂ)-2*(h:ℂ)) *
          (normalizedRawHalfUnit.val ^ (e-2*((n-k:ℕ):ℤ))).val)) / (k.factorial:ℂ)) •
        (LatticeHalfFockCorrectedField.correctedField D hu
          ((sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1 ^ k)
            (gradeProjection D h a))).coeff (e-2*((n-k:ℕ):ℤ))

private theorem binomial_reflection (r : ℂ) (m : ℕ) :
    (-1:ℂ)^m * Ring.choose r m = Ring.choose (-r+(m:ℂ)-1) m := by
  have h := Ring.choose_neg (-r) m
  rw [neg_neg] at h
  rw [h]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num

private theorem raw_scalar (h e : ℤ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k *
      (unitPower ((k:ℂ)-2*(h:ℂ)) *
        (normalizedRawHalfUnit.val ^ (e-2*((n-k:ℕ):ℤ))).val)) / (k.factorial:ℂ) =
      c (2*(h:ℂ)+(e:ℂ)/2-1) n k := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hk : k ≤ n
  · rw [if_pos hk, halfUnit_power, ← unitPower_add]
    simp only [unitPower, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
      smul_eq_mul, mul_one]
    rw [binomial_reflection]
    have hp : -((k:ℂ)-2*(h:ℂ) + -((e-2*((n-k:ℕ):ℤ):ℤ):ℂ)/2) +
        ((n-k:ℕ):ℂ)-1 = (2*(h:ℂ)+(e:ℂ)/2-1)-(k:ℂ) := by
      push_cast
      rw [Nat.cast_sub hk]
      ring
    rw [hp, c, if_pos hk]
  · simp [hk,c]

private theorem raw_readout_closed (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (e : ℤ) (a : Carrier D) :
    rawHalfCoordinateReadout D hu n e a =
      ∑ h ∈ stateEnergies D a, ∑ k ∈ Finset.range (n+1),
        c (2*(h:ℂ)+(e:ℂ)/2-1) n k •
          A D hu (e-2*(n:ℤ)+2*(k:ℤ)) ((S D 1 ^ k) (gradeProjection D h a)) := by
  classical
  unfold rawHalfCoordinateReadout
  apply Finset.sum_congr rfl
  intro h hh
  let b := gradeProjection D h a
  let α : ℂ := 2*(h:ℂ)+(e:ℂ)/2-1
  let f := fun k : ℕ => c α n k • A D hu (e-2*((n-k:ℕ):ℤ)) ((S D 1 ^ k) b)
  have cutoff (k : ℕ) (hk : sourceCutoff D b ≤ k) : f k = 0 := by
    dsimp only [f]
    rw [source_after_cutoff D hu b k hk, map_zero, smul_zero]
  have degree (k : ℕ) (hk : n < k) : f k = 0 := by simp [f,c,show ¬ k ≤ n by omega]
  have left : (∑ k ∈ Finset.range (sourceCutoff D b), f k) =
      ∑ k ∈ Finset.range (max (sourceCutoff D b) (n+1)), f k := by
    apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
    intro k hk hn
    exact cutoff k (by simpa only [Finset.mem_range, not_lt] using hn)
  have right : (∑ k ∈ Finset.range (n+1), f k) =
      ∑ k ∈ Finset.range (max (sourceCutoff D b) (n+1)), f k := by
    apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
    intro k hk hn
    exact degree k (by simp only [Finset.mem_range] at hn; omega)
  calc
    _ = ∑ k ∈ Finset.range (sourceCutoff D b), f k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [raw_scalar]
      rfl
    _ = ∑ k ∈ Finset.range (n+1), f k := left.trans right.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [f]
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hd : e-2*((n-k:ℕ):ℤ) = e-2*(n:ℤ)+2*(k:ℤ) := by omega
      rw [hd]

/-- The fixed-order ORIGINAL field has exactly the coefficient readout of
the normalized raw half-coordinate product and the finite original source
exponential. Both sides are independently defined. -/
theorem formal_mobius_raw_coordinate (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (e : ℤ) (a : Carrier D) :
    (formalMobiusOrder D hu n a).coeff e = rawHalfCoordinateReadout D hu n e a := by
  rw [raw_readout_closed]
  have hc := corrected_field_mobius_coefficient D hu n e a
  change conjugationCoefficient D hu n a e = _
  rw [show conjugationCoefficient D hu n a e = _ from hc]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  rw [c, if_pos (by have := Finset.mem_range.mp hk; omega)]
  have hs : 2*(h:ℂ)+(e:ℂ)/2-1-(k:ℂ) = 2*(h:ℂ)+(e:ℂ)/2-(k:ℂ)-1 := by ring
  simp only [hs]
  rfl

end
end D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
