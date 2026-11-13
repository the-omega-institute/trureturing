/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootString
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootString
   mirror-E: none(waiver:source-only-uncompiled-not-enrolled)
   anchors: []
   utility: none
   digest: Exact finite unbroken original physical charge-support strings. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootLadder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-!
SOURCE_ONLY_UNCOMPILED. No native Lean, kernel, axiom-closure, C#, Reg, final
candidate review, CI or publication acceptance is asserted. The sealed Ladder,
Weyl, integrability, Cartan-character and exponential suppliers remain source
candidates. Accepted196 suppliers supersede older physical sources, including
the accepted196 OppositeRootBracket; no older version is substituted.

The carrier is the literal original physicalImage in global Cohomology, and
the predicate uses the literal physicalChargeFiber, INCLUDING ZERO CHARGE.
Both quotient slots retain arbitrary original State primitives. The complex
inverse Gram matrix retains BOTH inverse equations and rank26 is unchanged.
This is physical charge support, with no assertion that zero is a root under
the usual root-system convention. No charge exclusion, finite-dimensional
whole-image assumption, Noetherianity, signature, form positivity, real H,
unimodularity, perfectness, HPL invariance, convergence or root multiplicity
premise is added. No uniform nilpotence exponent is inferred.

Attribution: classical sl2/root-string theory supplies the mathematical route;
Mathlib contributors supply finite integer intervals, finite extrema and
arithmetic, and Batteries supplies exact private access. Original physical
suppliers retain Bakalov--Kac, Scott Carnahan, Kalle Kytölä,
Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman attribution.
This is no Monster/Borcherds recognition, denominator identity, or full string
theory completion. The Monster/VOA/CFT/anomaly/fusion/string/AdS goal remains
ACTIVE INCOMPLETE.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section

open private chargeEnergy_add_zsmul bracket_mem_fiber
  bilinear_zsmul_right bilinear_zsmul_left from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
open private normalizedOpposite_mem opposite_energy_one root_length_two from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootWeylReflection

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootString

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeSugawaraCurrents (gramComplex)
open LatticePositiveEnergy (chargeEnergy chargeEnergy_zero)
open LatticeBRSTCohomologyField (Cohomology)
open LatticeBRSTPhysicalLie (physicalImage)
open LatticeBRSTPhysicalChargeFiber (physicalChargeFiber)
open LatticeBRSTPhysicalCharacter (physicalChargeFiber_eq_bot_of_level_neg)
open LatticeBRSTRealRootLadder (real_root_adjoint_injective_of_negative_pairing)
open LatticeBRSTRealRootWeylReflection
  (normalizedOpposite normalizedOpposite_ne_zero WeylAlpha
    WeylAlpha_mem_fiber_iff chargeReflection)

-- This is a global bound for all supported indices, not a pointwise killing
-- bound for the adjoint of one vector.
private theorem quadratic_upper_bound (a b n : ℤ)
    (hquad : a + n * b + n ^ 2 ≤ 1) : n ≤ |b| + |a| + 3 := by
  by_contra hn
  have hn0 : 0 ≤ n := by have := abs_nonneg b; have := abs_nonneg a; omega
  have hn1 : 0 ≤ n - 1 := by have := abs_nonneg b; have := abs_nonneg a; omega
  have hcross : 0 ≤ n * (b + |b|) :=
    mul_nonneg hn0 (by have := neg_abs_le b; omega)
  have hscale : 0 ≤ (n - 1) * |a| := mul_nonneg hn1 (abs_nonneg a)
  have hlarge : 0 ≤ n * (n - |b| - |a| - 3) :=
    mul_nonneg hn0 (by omega)
  have ha : -|a| ≤ a := neg_abs_le a
  nlinarith only [hquad, hcross, hscale, hlarge, ha, hn1]

-- Strict sign-directed steps fill the interval from its two endpoints. This
-- explicitly handles the even zero center and the odd -1,+1 center.
private theorem fill_integer_interval (S : ℤ → Prop) (b l u : ℤ)
    (hl : S l) (hu : S u)
    (hraise : ∀ n : ℤ, b + 2 * n < 0 → S n → S (n + 1))
    (hlower : ∀ n : ℤ, 0 < b + 2 * n → S n → S (n - 1))
    (n : ℤ) (hln : l ≤ n) (hnu : n ≤ u) : S n := by
  have hup : ∀ k : ℕ, b + 2 * (l + (k : ℤ)) ≤ 0 → S (l + (k : ℤ)) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [Nat.cast_zero, add_zero] using hl
    | succ k ih =>
        intro hk
        have hprev : b + 2 * (l + (k : ℤ)) < 0 := by
          push_cast at hk
          omega
        have hs := hraise (l + (k : ℤ)) hprev (ih (le_of_lt hprev))
        simpa only [Nat.cast_succ, add_assoc] using hs
  have hdown : ∀ k : ℕ, 0 < b + 2 * (u - (k : ℤ)) → S (u - (k : ℤ)) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [Nat.cast_zero, sub_zero] using hu
    | succ k ih =>
        intro hk
        have hprev : 0 < b + 2 * (u - (k : ℤ)) := by
          push_cast at hk
          omega
        have hs := hlower (u - (k : ℤ)) hprev (ih hprev)
        have heq : u - ((k + 1 : ℕ) : ℤ) = (u - (k : ℤ)) - 1 := by
          push_cast
          ring
        rw [heq]
        exact hs
  by_cases hw : b + 2 * n ≤ 0
  · have hk : ((n - l).toNat : ℤ) = n - l :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hln)
    have heq : l + ((n - l).toNat : ℤ) = n := by omega
    have hs := hup (n - l).toNat (by omega)
    simpa only [heq] using hs
  · have hk : ((u - n).toNat : ℤ) = u - n :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hnu)
    have heq : u - ((u - n).toNat : ℤ) = n := by omega
    have hs := hdown (u - n).toNat (by omega)
    simpa only [heq] using hs

section Physical

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "Ph" => physicalImage D H h26 hHG hGH
local notation "Fib" => physicalChargeFiber D H h26 hHG hGH

private theorem nonzero_fiber_energy_le_one (gamma : Charge D)
    (c : Ph) (hc : (c : C) ∈ Fib gamma) (hc0 : c ≠ 0) :
    chargeEnergy D gamma ≤ 1 := by
  by_contra hnot
  have henergy : 1 < chargeEnergy D gamma := by omega
  have hgamma : gamma ≠ 0 := by
    intro hz
    rw [hz, chargeEnergy_zero] at henergy
    omega
  have hbot := physicalChargeFiber_eq_bot_of_level_neg
    D H h26 hHG hGH gamma hgamma (by omega)
  rw [hbot] at hc
  apply hc0
  apply Subtype.ext
  exact (Submodule.mem_bot ℂ (M := C)).mp hc

private theorem pairing_add_zsmul (alpha beta : Charge D)
    (hα : chargeEnergy D alpha = 1) (n : ℤ) :
    bilinear D alpha (beta + n • alpha) = bilinear D alpha beta + 2 * n := by
  rw [LatticeActualGeneratorLocality.bilinear_add_right,
    bilinear_zsmul_right, root_length_two D alpha hα]
  ring

private theorem support_raise (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0)
    (gamma : Charge D) (hw : bilinear D alpha gamma < 0)
    (c : Ph) (hc : (c : C) ∈ Fib gamma) (hc0 : c ≠ 0) :
    ∃ d : Ph, (d : C) ∈ Fib (gamma + alpha) ∧ d ≠ 0 := by
  refine ⟨⁅e, c⁆, ?_, ?_⟩
  · simpa only [add_comm] using
      bracket_mem_fiber D H h26 hHG hGH alpha gamma e c he hc
  · intro hz
    exact hc0 (real_root_adjoint_injective_of_negative_pairing
      D H h26 hHG hGH alpha hα e he he0 gamma hw c hc hz)

private theorem support_lower (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0)
    (gamma : Charge D) (hw : 0 < bilinear D alpha gamma)
    (c : Ph) (hc : (c : C) ∈ Fib gamma) (hc0 : c ≠ 0) :
    ∃ d : Ph, (d : C) ∈ Fib (gamma - alpha) ∧ d ≠ 0 := by
  have hneg : bilinear D (-alpha) gamma = -bilinear D alpha gamma := by
    simpa using bilinear_zsmul_left D alpha gamma (-1)
  obtain ⟨d, hd, hd0⟩ := support_raise D H h26 hHG hGH (-alpha)
    (opposite_energy_one D alpha hα)
    (normalizedOpposite D H h26 hHG hGH alpha hα e he he0)
    (normalizedOpposite_mem D H h26 hHG hGH alpha hα e he he0)
    (normalizedOpposite_ne_zero D H h26 hHG hGH alpha hα e he he0)
    gamma (by omega) c hc hc0
  exact ⟨d, by simpa only [sub_eq_add_neg] using hd, hd0⟩

end Physical

/-- Exact finite original physical charge support along an actual energy-one
root, retaining the zero-charge fiber and all integer indices. The base fiber
is inhabited explicitly by c; beta=0 and beta=alpha are included. -/
theorem physical_charge_support_real_root_string
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
    (e : physicalImage D H h26 hHG hGH)
    (he : (e : Cohomology D H h26 hHG hGH) ∈
      physicalChargeFiber D H h26 hHG hGH alpha) (he0 : e ≠ 0)
    (beta : Charge D) (c : physicalImage D H h26 hHG hGH)
    (hc : (c : Cohomology D H h26 hHG hGH) ∈
      physicalChargeFiber D H h26 hHG hGH beta) (hc0 : c ≠ 0) :
    ∃ p q : ℕ, (p : ℤ) - (q : ℤ) = bilinear D alpha beta ∧
      ∀ n : ℤ, (∃ z : physicalImage D H h26 hHG hGH,
        (z : Cohomology D H h26 hHG hGH) ∈
          physicalChargeFiber D H h26 hHG hGH (beta + n • alpha) ∧ z ≠ 0) ↔
        -(p : ℤ) ≤ n ∧ n ≤ (q : ℤ) := by
  classical
  let S : ℤ → Prop := fun n => ∃ z : physicalImage D H h26 hHG hGH,
    (z : Cohomology D H h26 hHG hGH) ∈
      physicalChargeFiber D H h26 hHG hGH (beta + n • alpha) ∧ z ≠ 0
  let b : ℤ := bilinear D alpha beta
  let R : ℤ := |b| + |chargeEnergy D beta| + 3
  have hbase : S 0 := ⟨c, by simpa only [zero_smul, add_zero] using hc, hc0⟩
  have hbound (n : ℤ) (hn : S n) : -R ≤ n ∧ n ≤ R := by
    obtain ⟨z, hz, hz0⟩ := hn
    have henergy := nonzero_fiber_energy_le_one D H h26 hHG hGH
      (beta + n • alpha) z hz hz0
    rw [chargeEnergy_add_zsmul D beta alpha n, hα,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D beta alpha, mul_one] at henergy
    have hquad : chargeEnergy D beta + n * b + n ^ 2 ≤ 1 := henergy
    have hp := quadratic_upper_bound (chargeEnergy D beta) b n hquad
    have hm := quadratic_upper_bound (chargeEnergy D beta) (-b) (-n)
      (by nlinarith only [hquad])
    rw [abs_neg] at hm
    change -(|b| + |chargeEnergy D beta| + 3) ≤ n ∧
      n ≤ |b| + |chargeEnergy D beta| + 3
    omega
  let T : Finset ℤ := (Finset.Icc (-R) R).filter S
  have hmem (n : ℤ) : n ∈ T ↔ S n := by
    simp only [T, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun h => h.2, fun h => ⟨hbound n h, h⟩⟩
  have hT : T.Nonempty := ⟨0, (hmem 0).mpr hbase⟩
  let l : ℤ := T.min' hT
  let u : ℤ := T.max' hT
  have hl : S l := (hmem l).mp (T.min'_mem hT)
  have hu : S u := (hmem u).mp (T.max'_mem hT)
  have hmin (n : ℤ) (hn : S n) : l ≤ n :=
    T.min'_le n ((hmem n).mpr hn)
  have hmax (n : ℤ) (hn : S n) : n ≤ u :=
    T.le_max' n ((hmem n).mpr hn)
  have hraise (n : ℤ) (hw : b + 2 * n < 0) (hn : S n) : S (n + 1) := by
    obtain ⟨z, hz, hz0⟩ := hn
    have hpair : bilinear D alpha (beta + n • alpha) < 0 := by
      rw [pairing_add_zsmul D alpha beta hα n]
      exact hw
    obtain ⟨d, hd, hd0⟩ := support_raise D H h26 hHG hGH
      alpha hα e he he0 (beta + n • alpha) hpair z hz hz0
    have heq : (beta + n • alpha) + alpha = beta + (n + 1) • alpha := by module
    exact ⟨d, by simpa only [heq] using hd, hd0⟩
  have hlower (n : ℤ) (hw : 0 < b + 2 * n) (hn : S n) : S (n - 1) := by
    obtain ⟨z, hz, hz0⟩ := hn
    have hpair : 0 < bilinear D alpha (beta + n • alpha) := by
      rw [pairing_add_zsmul D alpha beta hα n]
      exact hw
    obtain ⟨d, hd, hd0⟩ := support_lower D H h26 hHG hGH
      alpha hα e he he0 (beta + n • alpha) hpair z hz hz0
    have heq : (beta + n • alpha) - alpha = beta + (n - 1) • alpha := by module
    exact ⟨d, by simpa only [heq] using hd, hd0⟩
  let W := WeylAlpha D H h26 hHG hGH alpha hα e he he0
  have hreflect (n : ℤ) (hn : S n) : S (-b - n) := by
    obtain ⟨z, hz, hz0⟩ := hn
    have heq : chargeReflection D alpha (beta + n • alpha) =
        beta + (-b - n) • alpha := by
      rw [chargeReflection, pairing_add_zsmul D alpha beta hα n]
      dsimp only [b]
      module
    refine ⟨W z, ?_, ?_⟩
    · rw [← heq]
      exact (WeylAlpha_mem_fiber_iff D H h26 hHG hGH
        alpha hα e he he0 (beta + n • alpha) z).mpr hz
    · intro hzW
      apply hz0
      apply W.injective
      change W z = W 0
      exact hzW.trans W.toLinearEquiv.map_zero.symm
  -- The reverse implication uses only involutivity of the integer index,
  -- never W squared equals the identity on the physical Lie image.
  have hreflect_iff (n : ℤ) : S n ↔ S (-b - n) := by
    refine ⟨hreflect n, ?_⟩
    intro hn
    have hs := hreflect (-b - n) hn
    have heq : -b - (-b - n) = n := by ring
    simpa only [heq] using hs
  have hend : l + u = -b := by
    have hleft := hmin (-b - u) ((hreflect_iff u).mp hu)
    have hright := hmax (-b - l) ((hreflect_iff l).mp hl)
    omega
  have hl0 : l ≤ 0 := hmin 0 hbase
  have hu0 : 0 ≤ u := hmax 0 hbase
  let p : ℕ := (-l).toNat
  let q : ℕ := u.toNat
  have hp : (p : ℤ) = -l := Int.toNat_of_nonneg (by omega)
  have hq : (q : ℤ) = u := Int.toNat_of_nonneg hu0
  refine ⟨p, q, ?_, ?_⟩
  · change (p : ℤ) - (q : ℤ) = b
    omega
  · intro n
    change S n ↔ -(p : ℤ) ≤ n ∧ n ≤ (q : ℤ)
    constructor
    · intro hn
      have hln := hmin n hn
      have hnu := hmax n hn
      omega
    · rintro ⟨hpn, hnq⟩
      exact fill_integer_interval S b l u hl hu hraise hlower n (by omega) (by omega)

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootString
