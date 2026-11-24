/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedInverseBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedInverseBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse mixed Leech BPZ transpose and detector reversal of the native graded product. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp

/-!
Huang, hep-th/9406190v7, §3.4 uses the upper half-turn for the opposite
field and the lower half-turn on the first state of the pair. Inverting
the latter uses the upper half-turn and cancels the two finite lowering
expansions. All field indices here are doubled physical exponents.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ

open Complex (I)
open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockGradedTrace
open LatticeInvolution (minusSpace)
open LatticeHalfFockParityT (actualParity_preserves_grade)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit OddCarrier paritySign)
open Orbifold.NativeOddUpperRightSkew
open Orbifold.NativeMixedPairState (mixedPairState_pairing)
open Orbifold.NativeMixedPairField (mu mu_coeff_of_grade mu_coeff_even_zero)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_symmetric)
open NativeMixedUpperProductCusp (bProductCoeff)

open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private lowering_eigen from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private lowering_pow_val actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew

local notation "ℒ" => leechData
local notation "L₁" => lowering ℒ leechUnit
local notation "Bₘ" => actualForm ℒ leechUnit
local notation "Bᵥ" => sourcePairing ℒ

private theorem lowered_grade {s : Bool} {M n : ℕ}
    {u : Twisted ℒ leechUnit s} (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hn : n ≤ M / 2) :
    ((L₁ s ^ n) u).val ∈ actualGrade ℒ leechUnit (M - 2 * n) := by
  rw [lowering_pow_val, actualGrade_eigen]
  have he := (actualGrade_eigen ℒ leechUnit M u.val).mp hu
  have hcast : (((M - 2 * n : ℕ) : ℂ)) = (((M : ℤ) - 2 * (n : ℤ) : ℤ) : ℂ) := by
    exact_mod_cast (show ((M - 2 * n : ℕ) : ℤ) = (M : ℤ) - 2 * (n : ℤ) by omega)
  rw [hcast]
  exact lowering_eigen ℒ leechUnit (M : ℤ) u.val (by simpa only [Int.cast_natCast] using he) n

private theorem inverse_phase (M n : ℕ) (hn : n ≤ M / 2) :
    I ^ (3 + (M : ℤ)) * I ^ (-(3 + ((M - 2 * n : ℕ) : ℤ))) = (-1 : ℂ) ^ n := by
  rw [← zpow_add₀ Complex.I_ne_zero,
    show (3 + (M : ℤ)) + -(3 + ((M - 2 * n : ℕ) : ℤ)) = 2 * (n : ℤ) by omega,
    zpow_mul, zpow_natCast, show I ^ (2 : ℤ) = -1 from
      (zpow_natCast I 2).trans Complex.I_sq]

private theorem alternating_factorials (r : ℕ) :
    (∑ n ∈ Finset.range (r + 1),
      (-1 : ℂ) ^ n * (n.factorial : ℂ)⁻¹ * ((r - n).factorial : ℂ)⁻¹) =
      (0 : ℂ) ^ r := by
  calc
    _ = (∑ n ∈ Finset.range (r + 1), (-1 : ℂ) ^ n * (r.choose n : ℂ)) /
        (r.factorial : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Nat.cast_choose ℂ (by simpa using hn : n ≤ r)]
      have hf (k : ℕ) : (k.factorial : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero k)
      field_simp [hf]
    _ = _ := by
      rw [show (∑ n ∈ Finset.range (r + 1), (-1 : ℂ) ^ n * (r.choose n : ℂ)) =
          (0 : ℂ) ^ r by simpa using (add_pow (-1 : ℂ) 1 r).symm]
      cases r <;> simp

private theorem cancel_lowering_orders (bound : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range (bound + 1), ∑ q ∈ Finset.range (bound - n + 1),
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹) * f (n + q)) = f 0 := by
  classical
  let term (n q : ℕ) := ((-1 : ℂ) ^ n * (n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹) *
    f (n + q)
  change (∑ n ∈ Finset.range (bound + 1), ∑ q ∈ Finset.range (bound - n + 1), term n q) = _
  calc
    _ = ∑ r ∈ Finset.range (bound + 1),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal r, term p.1 p.2 := by
      rw [Finset.sum_sigma' (f := term),
        Finset.sum_sigma' (f := fun (_ : ℕ) (p : ℕ × ℕ) => term p.1 p.2)]
      refine Finset.sum_bij' (fun p _ => ⟨p.1 + p.2, (p.1, p.2)⟩)
        (fun p _ => ⟨p.2.1, p.2.2⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨n, q⟩ h
        have hn : n < bound + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp h).1
        have hq : q < bound - n + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp h).2
        apply Finset.mem_sigma.mpr
        exact ⟨Finset.mem_range.mpr (show n + q < bound + 1 by omega),
          Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
      · rintro ⟨r, n, q⟩ h
        have hr : r < bound + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp h).1
        have hnq : n + q = r :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_sigma.mp h).2
        apply Finset.mem_sigma.mpr
        exact ⟨Finset.mem_range.mpr (show n < bound + 1 by omega),
          Finset.mem_range.mpr (show q < bound - n + 1 by omega)⟩
      · rintro ⟨n, q⟩ _
        rfl
      · rintro ⟨r, n, q⟩ h
        have hr : n + q = r :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_sigma.mp h).2
        change (⟨n + q, (n, q)⟩ : Σ _ : ℕ, ℕ × ℕ) = ⟨r, (n, q)⟩
        rw [hr]
      · intro _ _
        rfl
    _ = ∑ r ∈ Finset.range (bound + 1), (0 : ℂ) ^ r * f r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun n q => term n q), ← alternating_factorials, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ≤ r := by simpa using hn
      change _ * f (n + (r - n)) = _ * f r
      rw [Nat.add_sub_of_le hn']
    _ = f 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r _ hr
        simp [zero_pow hr]
      · simp

private theorem mu_pairing_forward_of_mode (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s))
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (a : OddCarrier ℒ) :
    Bᵥ ((mu s u).coeff (-2 * m - 3) v).val a.val =
      I ^ (-(3 + (M : ℤ))) * ∑ q ∈ Finset.range (M / 2 + 1),
        (q.factorial : ℂ)⁻¹ *
          Bₘ v.val ((rightField ℒ leechUnit s ((L₁ s ^ q) u)).coeff
            (-6 - 2 * (M : ℤ) + 2 * (q : ℤ) - (-2 * m - 3)) a).val := by
  rw [mu_coeff_of_grade s M K m u v hu hv, mixedPairState_pairing s M K m u v hu hv]
  simp only [mixedPairing, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, smul_eq_mul]
  apply congrArg (fun z : ℂ => I ^ (-(3 + (M : ℤ))) * z)
  apply Finset.sum_congr rfl
  intro q _
  rw [show -6 - 2 * (M : ℤ) + 2 * (q : ℤ) - (-2 * m - 3) =
    -2 * ((M : ℤ) - m - (q : ℤ)) - 3 by ring, rightField_coeff]

private theorem mu_pairing_forward (s : Bool) (M K : ℕ) (e : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s))
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (a : OddCarrier ℒ) :
    Bᵥ ((mu s u).coeff e v).val a.val =
      I ^ (-(3 + (M : ℤ))) * ∑ q ∈ Finset.range (M / 2 + 1),
        (q.factorial : ℂ)⁻¹ *
          Bₘ v.val ((rightField ℒ leechUnit s ((L₁ s ^ q) u)).coeff
            (-6 - 2 * (M : ℤ) + 2 * (q : ℤ) - e) a).val := by
  by_cases he : Even e
  · rw [mu_coeff_even_zero s e u v he]
    have hz (q : ℕ) : (rightField ℒ leechUnit s ((L₁ s ^ q) u)).coeff
        (-6 - 2 * (M : ℤ) + 2 * (q : ℤ) - e) a = 0 :=
      rightField_even_zero ℒ leechUnit s _ (by
        obtain ⟨k, hk⟩ := he
        exact ⟨-3 - (M : ℤ) + (q : ℤ) - k, by omega⟩) _ _
    simp [hz]
  · have hm : -2 * ((-e - 3) / 2) - 3 = e := by
      have := Int.not_even_iff.mp he
      omega
    simpa only [hm] using mu_pairing_forward_of_mode s M K ((-e - 3) / 2) u v hu hv a

private theorem rightField_pairing_of_detector_grade (s : Bool) (M K : ℕ) (j : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s))
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (a : OddCarrier ℒ) :
    Bₘ v.val ((rightField ℒ leechUnit s u).coeff j a).val =
      I ^ (3 + (M : ℤ)) * ∑ n ∈ Finset.range (M / 2 + 1),
        (n.factorial : ℂ)⁻¹ *
          Bᵥ ((mu s ((L₁ s ^ n) u)).coeff (2 * (n : ℤ) - 6 - 2 * (M : ℤ) - j) v).val
            a.val := by
  let f (r : ℕ) := Bₘ v.val
    ((rightField ℒ leechUnit s ((L₁ s ^ r) u)).coeff (j + 2 * (r : ℤ)) a).val
  have h0 : f 0 = Bₘ v.val ((rightField ℒ leechUnit s u).coeff j a).val := by simp [f]
  rw [← h0, ← cancel_lowering_orders (M / 2) f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ M / 2 := by simpa using hn
  rw [mu_pairing_forward s (M - 2 * n) K _ _ v (lowered_grade hu hn') hv,
    show (M - 2 * n) / 2 = M / 2 - n by omega,
    mul_left_comm (n.factorial : ℂ)⁻¹ (I ^ (-(3 + ((M - 2 * n : ℕ) : ℤ)))),
    ← mul_assoc, inverse_phase M n hn', ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have he : -6 - 2 * ((M - 2 * n : ℕ) : ℤ) + 2 * (q : ℤ) -
      (2 * (n : ℤ) - 6 - 2 * (M : ℤ) - j) = j + 2 * ((n + q : ℕ) : ℤ) := by omega
  rw [he, ← Module.End.mul_apply, ← pow_add, add_comm q n]
  dsimp only [f]
  ring

/-- The upper odd right field is the inverse BPZ transpose of the native
mixed pair. The inverse uses the upper half-turn on the first state, which
has doubled oscillator energy `M`. Both occupation parities, arbitrary
opposite-parity detectors, and all doubled right exponents are allowed. -/
theorem rightField_pairing_eq_inverse_bpz (s : Bool) (M : ℕ) (j : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s))
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (a : OddCarrier ℒ) :
    Bₘ v.val ((rightField ℒ leechUnit s u).coeff j a).val =
      I ^ (3 + (M : ℤ)) * ∑ n ∈ Finset.range (M / 2 + 1),
        (n.factorial : ℂ)⁻¹ *
          Bᵥ ((mu s ((L₁ s ^ n) u)).coeff (2 * (n : ℤ) - 6 - 2 * (M : ℤ) - j) v).val
            a.val := by
  let left : Module.Dual ℂ (Twisted ℒ leechUnit (!s)) :=
    (LinearMap.flip Bₘ ((rightField ℒ leechUnit s u).coeff j a).val).comp
      (paritySpace ℒ leechUnit (paritySign (!s))).subtype
  let right : Module.Dual ℂ (Twisted ℒ leechUnit (!s)) :=
    I ^ (3 + (M : ℤ)) • ∑ n ∈ Finset.range (M / 2 + 1),
      (n.factorial : ℂ)⁻¹ • ((LinearMap.flip Bᵥ a.val).comp (minusSpace ℒ).subtype).comp
        ((mu s ((L₁ s ^ n) u)).coeff (2 * (n : ℤ) - 6 - 2 * (M : ℤ) - j))
  have h (d : Twisted ℒ leechUnit (!s)) :
      left d = right d := by
    rw [← sum_projectedBasis (!s) d]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    let x := actualAmbientBasis ℒ leechUnit i
    let K := oddWeight ℒ i.1
    have hx : x ∈ actualGrade ℒ leechUnit K :=
      (actualGrade_eigen ℒ leechUnit K x).mpr (actual_basis_eigenvalue ℒ leechUnit i.1 i.2)
    have hproj : (project (!s) x).val ∈ actualGrade ℒ leechUnit K := by
      rw [project_val]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx (Submodule.smul_mem _ _
        (actualParity_preserves_grade ℒ leechUnit _ _ hx)))
    apply congrArg ((actualAmbientBasis ℒ leechUnit).repr d.val i • ·)
    simpa only [left, right, LinearMap.comp_apply, LinearMap.flip_apply, Submodule.subtype_apply,
      LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] using
      rightField_pairing_of_detector_grade s M K j u (project (!s) x) hu hproj a
  simpa only [left, right, LinearMap.comp_apply, LinearMap.flip_apply, Submodule.subtype_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] using h v

/-- Detector reversal of each native mixed B-product summand, at the very
same intermediate lattice grade `E`. The two external inputs acquire
opposite half-turns and their full finite lowering expansions. -/
theorem bProductCoeff_detector_reversal (s t : Bool) (M K L N : ℕ)
    (v : Twisted ℒ leechUnit s) (w : Twisted ℒ leechUnit (!s))
    (u : Twisted ℒ leechUnit t) (b : Twisted ℒ leechUnit (!t))
    (E : ℕ)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N) :
    bProductCoeff s t M K L N v w u b E =
      I ^ ((M : ℤ) - K) * ∑ n ∈ Finset.range (M / 2 + 1),
        ∑ q ∈ Finset.range (K / 2 + 1),
          ((n.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹) *
            bProductCoeff t s (K - 2 * q) (M - 2 * n) N L
              ((L₁ t ^ n) u) b ((L₁ s ^ q) v) w E := by
  simp only [bProductCoeff]
  rw [rightField_pairing_of_detector_grade t M N _ u b hu hb]
  have hphase : I ^ ((M : ℤ) - K) =
      I ^ (3 + (M : ℤ)) * I ^ (-(3 + (K : ℤ))) := by
    rw [← zpow_add₀ Complex.I_ne_zero]
    congr 1
    ring
  rw [hphase, mul_assoc]
  apply congrArg (fun z : ℂ => I ^ (3 + (M : ℤ)) * z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ M / 2 := by simpa using hn
  rw [sourcePairing_symmetric, mu_pairing_forward s K L _ v w hv hw]
  rw [mul_left_comm (n.factorial : ℂ)⁻¹ (I ^ (-(3 + (K : ℤ))))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : q ≤ K / 2 := by simpa using hq
  have hright : -6 - 2 * (K : ℤ) + 2 * (q : ℤ) - (2 * (E : ℤ) - (6 + (K : ℤ) + L)) =
      (L : ℤ) - ((K - 2 * q : ℕ) : ℤ) - 2 * (E : ℤ) := by omega
  have hpair : 2 * (n : ℤ) - 6 - 2 * (M : ℤ) - ((N : ℤ) - M - 2 * (E : ℤ)) =
      2 * (E : ℤ) - (6 + ((M - 2 * n : ℕ) : ℤ) + N) := by omega
  rw [hright, hpair]
  ring

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
