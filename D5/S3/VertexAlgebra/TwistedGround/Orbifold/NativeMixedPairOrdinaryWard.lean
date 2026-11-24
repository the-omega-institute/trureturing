/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairOrdinaryWard
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairOrdinaryWard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary divided mode-one powers for the native mixed Leech pair. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairMobius
import Batteries.Tactic.OpenPrivate

/-! Ordinary divided mode-one powers of the native mixed Leech pair. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairOrdinaryWard

open ActualLeechHyperbolic (leechData)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeSugawaraCurrents (sugawaraMode gramComplex)
open NativeOddTwistedIntertwiner (Twisted leechUnit)
open NativeOddUpperRightSkew (lowering)
open NativeMixedPairField (mu)
open NativeMixedPairMobius (mu_coeff_L1_mobius)
open private mode mode_apply post pre ad dividedAd dividedAd_eq_sum post_pow_apply pre_pow_apply from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairMobius

local notation "ℒ" => leechData
local notation "V" => sugawaraMode ℒ (gramComplex ℒ)⁻¹ 1
local notation "T" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev Mode (s : Bool) := State (!s) →ₗ[ℂ] Carrier ℒ

private theorem ordinary_divided_power (s : Bool) (n : ℕ) (e : ℤ)
    (u : State s) (v : State (!s)) :
    (n.factorial : ℂ)⁻¹ • (V ^ n) (((mu s u).coeff e v).val) =
      ∑ p ∈ Finset.range (n + 1),
        ((n - p).factorial : ℂ)⁻¹ • dividedAd s p e u ((T (!s) ^ (n - p)) v) := by
  have commutePre : Commute (post s) (pre s) := by
    rw [commute_iff_eq]
    exact LinearMap.ext₂ fun f w => rfl
  have commuteAd : Commute (ad s) (pre s) :=
    commutePre.sub_left (Commute.refl _)
  have hpost : post s = ad s + pre s := by simp [ad]
  have expansion : post s ^ n = ∑ p ∈ Finset.range (n + 1),
      ad s ^ p * pre s ^ (n - p) * (n.choose p : Module.End ℂ (Mode s)) := by
    calc
      _ = (ad s + pre s) ^ n := congrArg (fun f : Module.End ℂ (Mode s) => f ^ n) hpost
      _ = _ := commuteAd.add_pow n
  have term (p : ℕ) (hp : p ≤ n) :
      (n.factorial : ℂ)⁻¹ •
          (ad s ^ p * pre s ^ (n - p) *
            (n.choose p : Module.End ℂ (Mode s))) (mode s e u) v =
        ((n - p).factorial : ℂ)⁻¹ • dividedAd s p e u ((T (!s) ^ (n - p)) v) := by
    have hswap := (commuteAd.pow_pow p (n - p)).eq
    rw [hswap]
    simp only [Module.End.mul_apply, Module.End.natCast_apply,
      ← Nat.cast_smul_eq_nsmul ℂ, map_smul, pre_pow_apply,
      dividedAd, LinearMap.smul_apply, smul_smul]
    congr 1
    rw [Nat.cast_choose ℂ hp]
    have hf (k : ℕ) : (k.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    field_simp [hf] <;> ring
  rw [← mode_apply s e u v, ← post_pow_apply s n (mode s e u) v,
    expansion, LinearMap.sum_apply,
    LinearMap.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun p hp =>
    term p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))

private theorem dividedAd_on_native_pair (s : Bool) (M p : ℕ) (e : ℤ)
    (u : State s) (v : State (!s)) (hu : u.val ∈ actualGrade ℒ leechUnit M) :
    dividedAd s p e u v =
      ∑ i ∈ Finset.range (p + 1),
        (Ring.choose (3 + (M : ℂ) + (e : ℂ) / 2 - (i : ℂ) - 1) (p - i) /
          (i.factorial : ℂ)) •
          ((mu s ((T s ^ i) u)).coeff (e - 2 * (p : ℤ) + 2 * (i : ℤ)) v).val := by
  rw [dividedAd_eq_sum, LinearMap.sum_apply]
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, mode_apply] using
    mu_coeff_L1_mobius s M p e u v hu

/-- Formula (8) with indices j, i, and n-j-i on each finite diagonal. -/
theorem mu_coeff_L1_ordinary (s : Bool) (M n : ℕ) (e : ℤ)
    (u : State s) (v : State (!s)) (hu : u.val ∈ actualGrade ℒ leechUnit M) :
    (n.factorial : ℂ)⁻¹ • (V ^ n) (((mu s u).coeff e v).val) =
      ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n - j + 1),
        (Ring.choose (3 + (M : ℂ) + (e : ℂ) / 2 - (i : ℂ) - 1) (n - j - i) /
          ((i.factorial : ℂ) * (j.factorial : ℂ))) •
          ((mu s ((T s ^ i) u)).coeff (e - 2 * ((n - j - i : ℕ) : ℤ))
            ((T (!s) ^ j) v)).val := by
  rw [ordinary_divided_power, ← Finset.sum_range_reflect
    (fun p => ((n - p).factorial : ℂ)⁻¹ • dividedAd s p e u ((T (!s) ^ (n - p)) v))
    (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hreflect : n + 1 - 1 - j = n - j := by omega
  have hcancel : n - (n - j) = j := by omega
  rw [hreflect, hcancel, dividedAd_on_native_pair s M _ e u _ hu, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have he : e - 2 * ((n - j : ℕ) : ℤ) + 2 * (i : ℤ) =
      e - 2 * ((n - j - i : ℕ) : ℤ) := by omega
  rw [he, smul_smul]
  congr 1
  have hf (k : ℕ) : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hf] <;> ring

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairOrdinaryWard
