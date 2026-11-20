/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostDerivativeBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostDerivativeBPZ
   mirror-E: none(waiver:algebraic-original-orbifold-brst-ghost-derivative-bpz)
   anchors: []
   utility: none
   digest: Signed BPZ mode transposition for all one-site states of the native bc Fock space. -/

import D5.S3.Quantum.Fermionic.BcGhostStateField
import D5.S3.VertexAlgebra.Analysis.IntegerNewton
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
import Batteries.Tactic.OpenPrivate

/-! In vertex indices, each term of the finite Möbius correction for a
one-site state has the same reflected generator mode. Its scalar sum is the
integer Chu–Vandermonde convolution, including negative weights and modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

noncomputable section
namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostDerivativeBPZ

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket vacuum create_vacuum parity)
open BcGhostFock (b c mode_correspondence ghost_vacuum)
open BcGhostStateField (Y)
open BcGhostVirasoro (L ward_b ward_c)
open FieldNormalProduct (identityField dividedDerivative)
open OriginalOrbifoldBRSTGhostBPZ (beta beta_b)
open Analysis.IntegerNewton (choose_succ_mul)

open private Y_ket wordField signedNormalMinusOne generatingMode derivative_modes from
  D5.S3.Quantum.Fermionic.BcGhostStateField
open private L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private ket_homogeneous parity_ket_charge ghost_adjoint ghost_c_adjoint from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard

/-- The one-site ket for the divided derivative of order `t`. False denotes b
and true denotes c, as in the native generating fields. -/
def site (species : Bool) (t : ℕ) : Fock :=
  ket {2 * t + if species then 1 else 0}

/-- The integer conformal weight of the one-site state. -/
def siteWeight (species : Bool) (t : ℕ) : ℤ :=
  (if species then -1 else 2) + (t : ℤ)

private theorem siteWeight_eq (species : Bool) (t : ℕ) :
    siteWeight species t = siteWeight species 0 + (t : ℤ) := by
  simp [siteWeight]

/-- Both b and c one-site states are odd for native occupation parity. -/
theorem site_parity (species : Bool) (t : ℕ) : parity (site species t) = -site species t := by
  simp [site, parity_ket]

private theorem normal_identity_mode (A : VertexOperator ℂ Fock) (n : ℤ) :
    ((signedNormalMinusOne 1 A identityField).1 [[n]]) = A [[n]] := by
  apply LinearMap.ext
  intro v
  rw [(signedNormalMinusOne 1 A identityField).2]
  simp only [one_smul]
  have identityModes (k : ℤ) : ((identityField : VertexOperator ℂ Fock) [[k]]) =
      if k = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -k - 1 = 0 ↔ k = -1 by omega]
  by_cases hn : 0 ≤ n
  · have hz : ∀ i : ℕ, (A [[-(i : ℤ) - 1]])
        (((identityField : VertexOperator ℂ Fock) [[n + i]]) v) = 0 := by
      intro i
      simp [identityModes, show n + (i : ℤ) ≠ -1 by omega]
    simp only [hz, finsum_zero, zero_add]
    rw [finsum_eq_single _ n.toNat]
    · simp [identityModes, Int.toNat_of_nonneg hn]
    · intro i hi
      simp [identityModes, show n - (i : ℤ) - 1 ≠ -1 by omega]
  · have hz : ∀ i : ℕ, ((identityField : VertexOperator ℂ Fock) [[n - i - 1]])
        ((A [[i]]) v) = 0 := by
      intro i
      simp [identityModes, show n - (i : ℤ) - 1 ≠ -1 by omega]
    simp only [hz, finsum_zero, add_zero]
    rw [finsum_eq_single _ (-n - 1).toNat]
    · rw [identityModes, Int.toNat_of_nonneg (by omega : 0 ≤ -n - 1), ite_eq_left (by omega)]
      simp only [LinearMap.id_apply]
      rw [show -(-n - 1) - 1 = n by omega]
    · intro i hi
      simp [identityModes, show n + (i : ℤ) ≠ -1 by omega]

private theorem site_modes (species : Bool) (t : ℕ) (n : ℤ) :
    ((Y (site species t)) [[n]]) =
      Ring.choose ((-n - 1 + (t : ℤ) : ℤ) : ℂ) t • generatingMode species (n - t) := by
  rw [site, Y_ket]
  simp only [Finset.sort_singleton, wordField, List.length_nil]
  have ht : (2 * t + (if species then 1 else 0)) / 2 = t := by
    split <;> omega
  have hs : ((2 * t + (if species then 1 else 0)) % 2 == 1) = species := by
    cases species
    · have h : (2 * t) % 2 = 0 := by omega
      simp [h]
    · have h : (2 * t + 1) % 2 = 1 := by omega
      simp [h]
  have hcast : ((Ring.choose (-n - 1 + (t : ℤ)) t : ℤ) : ℂ) =
      Ring.choose ((-n - 1 + (t : ℤ) : ℤ) : ℂ) t :=
    Ring.map_choose (Int.castRingHom ℂ) _ t
  rw [ht, hs, show (-1 : ℂ) ^ (0 : ℕ) = 1 from pow_zero _, normal_identity_mode,
    derivative_modes, hcast]

private theorem site_vacuum_mode (species : Bool) (t : ℕ) :
    generatingMode species (-(t : ℤ) - 1) vacuum = site species t := by
  cases species
  · change b (-(t : ℤ) - 1 - 1) vacuum = ket {2 * t + 0}
    rw [show -(t : ℤ) - 1 - 1 = -(t : ℤ) - 2 by omega,
      (mode_correspondence t).1, create_vacuum, Nat.add_zero]
  · change c (-(t : ℤ) - 1 + 2) vacuum = ket {2 * t + 1}
    rw [show -(t : ℤ) - 1 + 2 = 1 - (t : ℤ) by omega,
      (mode_correspondence t).2.2.1, create_vacuum]

private theorem L_generating_vacuum (species : Bool) (m n : ℤ) (hm : 0 ≤ m) :
    L m (generatingMode species n vacuum) =
      (((siteWeight species 0 - 1) * (m + 1) - n : ℤ) : ℂ) •
        generatingMode species (m + n) vacuum := by
  cases species
  · have h := LinearMap.congr_fun (ward_b m (n - 1)) vacuum
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      L_vacuum_nonneg m hm, map_zero, sub_zero] at h
    change L m (b (n - 1) vacuum) =
      ((((2 : ℤ) - 1) * (m + 1) - n : ℤ) : ℂ) • b (m + n - 1) vacuum
    rw [show ((2 : ℤ) - 1) * (m + 1) - n = m - (n - 1) by omega,
      show m + n - 1 = m + (n - 1) by omega]
    exact h
  · have h := LinearMap.congr_fun (ward_c m (n + 2)) vacuum
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      L_vacuum_nonneg m hm, map_zero, sub_zero] at h
    change L m (c (n + 2) vacuum) =
      ((((-1 : ℤ) - 1) * (m + 1) - n : ℤ) : ℂ) • c (m + n + 2) vacuum
    rw [show ((-1 : ℤ) - 1) * (m + 1) - n = -2 * m - (n + 2) by omega,
      show m + n + 2 = m + (n + 2) by omega]
    exact h

/-- The indicated weight is the eigenvalue of the actual ghost L(0). -/
theorem site_L0 (species : Bool) (t : ℕ) :
    L 0 (site species t) = (siteWeight species t : ℂ) • site species t := by
  have hc : (siteWeight species 0 - 1) * (0 + 1) - (-(t : ℤ) - 1) =
      siteWeight species t := by
    rw [siteWeight_eq species t]
    omega
  calc
    L 0 (site species t) = L 0 (generatingMode species (-(t : ℤ) - 1) vacuum) := by
      rw [site_vacuum_mode]
    _ = _ := by
      rw [L_generating_vacuum species 0 _ (by omega), hc, zero_add, site_vacuum_mode]

private theorem site_L1_zero (species : Bool) : L 1 (site species 0) = 0 := by
  have hz : generatingMode species 0 vacuum = 0 := by
    cases species
    · exact ghost_vacuum.1 (-1) (by omega)
    · exact ghost_vacuum.2.1 2 (by omega)
  rw [← site_vacuum_mode species 0, L_generating_vacuum species 1 _ (by omega), Nat.cast_zero,
    show (1 : ℤ) + (-0 - 1) = 0 by norm_num, hz, smul_zero]

private theorem site_L1_succ (species : Bool) (t : ℕ) :
    L 1 (site species (t + 1)) =
      ((2 * siteWeight species 0 + ((t + 1 : ℕ) : ℤ) - 1 : ℤ) : ℂ) • site species t := by
  have hc : (siteWeight species 0 - 1) * (1 + 1) - (-((t + 1 : ℕ) : ℤ) - 1) =
      2 * siteWeight species 0 + ((t + 1 : ℕ) : ℤ) - 1 := by omega
  rw [← site_vacuum_mode species (t + 1), L_generating_vacuum species 1 _ (by omega), hc,
    show 1 + (-((t + 1 : ℕ) : ℤ) - 1) = -(t : ℤ) - 1 by omega, site_vacuum_mode]

/-- Below the cutoff the actual L(1) powers have the falling-factorial coefficient. -/
theorem site_L1_pow (species : Bool) (t j : ℕ) (hj : j ≤ t) :
    (L 1 ^ j) (site species t) =
      ((j.factorial : ℂ) * Ring.choose ((2 * siteWeight species 0 + (t : ℤ) - 1 : ℤ) : ℂ) j) •
        site species (t - j) := by
  let A : ℤ := 2 * siteWeight species 0 + (t : ℤ) - 1
  change (L 1 ^ j) (site species t) =
    ((j.factorial : ℂ) * Ring.choose (A : ℂ) j) • site species (t - j)
  induction j with
  | zero => simp [Module.End.one_apply]
  | succ j ih =>
    have ht : j ≤ t := by omega
    have hs : t - j = (t - (j + 1)) + 1 := by omega
    have hc : 2 * siteWeight species 0 + (((t - (j + 1)) + 1 : ℕ) : ℤ) - 1 =
        A - (j : ℤ) := by
      dsimp [A]
      omega
    rw [pow_succ', Module.End.mul_apply, ih ht, hs, map_smul, site_L1_succ, hc, smul_smul]
    have hscalar : ((j.factorial : ℂ) * Ring.choose (A : ℂ) j) * ((A - (j : ℤ) : ℤ) : ℂ) =
        ((j + 1).factorial : ℂ) * Ring.choose (A : ℂ) (j + 1) := by
      calc
        _ = (j.factorial : ℂ) * (((A : ℂ) - (j : ℂ)) * Ring.choose (A : ℂ) j) := by
          push_cast
          ring
        _ = _ := by
          rw [← choose_succ_mul (A : ℂ) j, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
          ring
    rw [hscalar]

/-- Every L(1) power beyond the derivative order annihilates the state. -/
theorem site_L1_pow_eq_zero (species : Bool) (t j : ℕ) (hj : t < j) :
    (L 1 ^ j) (site species t) = 0 := by
  have hcut : (L 1 ^ (t + 1)) (site species t) = 0 := by
    rw [pow_succ', Module.End.mul_apply, site_L1_pow species t t le_rfl, Nat.sub_self,
      map_smul, site_L1_zero, smul_zero]
  rw [show j = (j - (t + 1)) + (t + 1) by omega, pow_add, Module.End.mul_apply, hcut, map_zero]

private theorem site_L1_divided (species : Bool) (t j : ℕ) (hj : j ≤ t) :
    (j.factorial : ℂ)⁻¹ • (L 1 ^ j) (site species t) =
      Ring.choose ((2 * siteWeight species 0 + (t : ℤ) - 1 : ℤ) : ℂ) j •
        site species (t - j) := by
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [site_L1_pow species t j hj, mul_smul, inv_smul_smul₀ hfac]

private theorem state_mode_smul (z : ℂ) (a : Fock) (m : ℤ) :
    ((Y (z • a)) [[m]]) = z • ((Y a) [[m]]) := by
  simp only [map_smul, Pi.smul_apply]

private theorem integer_choose_sum (A n : ℤ) (t : ℕ) :
    (∑ j ∈ Finset.range (t + 1),
      Ring.choose (A : ℂ) j * Ring.choose ((n - A : ℤ) : ℂ) (t - j)) =
      Ring.choose (n : ℂ) t := by
  have h := Ring.add_choose_eq (R := ℤ) (r := A) (s := n - A) t (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show A + (n - A) = n by omega] at h
  have hcast (a : ℤ) (k : ℕ) : ((Ring.choose a k : ℤ) : ℂ) = Ring.choose (a : ℂ) k :=
    Ring.map_choose (Int.castRingHom ℂ) a k
  simpa only [Int.cast_sum, Int.cast_mul, hcast] using congrArg (fun a : ℤ => (a : ℂ)) h.symm

private theorem reflected_site_modes (species : Bool) (t : ℕ) (n : ℤ) :
    (∑ j ∈ Finset.range (t + 1),
      ((Y ((j.factorial : ℂ)⁻¹ • (L 1 ^ j) (site species t)))
        [[2 * siteWeight species t - n - (j : ℤ) - 2]])) =
      Ring.choose (n : ℂ) t •
        generatingMode species (2 * siteWeight species 0 + (t : ℤ) - 2 - n) := by
  let A : ℤ := 2 * siteWeight species 0 + (t : ℤ) - 1
  let mode : ℤ := 2 * siteWeight species 0 + (t : ℤ) - 2 - n
  calc
    _ = ∑ j ∈ Finset.range (t + 1),
        (Ring.choose (A : ℂ) j * Ring.choose ((n - A : ℤ) : ℂ) (t - j)) •
          generatingMode species mode := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hle := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      let m : ℤ := 2 * siteWeight species t - n - (j : ℤ) - 2
      have hcoeff : -m - 1 + ((t - j : ℕ) : ℤ) = n - A := by
        dsimp [m, A]
        rw [siteWeight_eq species t]
        omega
      have hmode : m - ((t - j : ℕ) : ℤ) = mode := by
        dsimp [m, mode]
        rw [siteWeight_eq species t]
        omega
      change ((Y ((j.factorial : ℂ)⁻¹ • (L 1 ^ j) (site species t))) [[m]]) = _
      rw [site_L1_divided species t j hle, state_mode_smul, site_modes species (t - j) m,
        hcoeff, hmode, smul_smul]
    _ = _ := by
      rw [← Finset.sum_smul, integer_choose_sum]

private theorem derivative_choose (n : ℤ) (t : ℕ) :
    Ring.choose ((-n - 1 + (t : ℤ) : ℤ) : ℂ) t =
      (-1 : ℂ) ^ t * Ring.choose (n : ℂ) t := by
  have harg : ((-n - 1 + (t : ℤ) : ℤ) : ℂ) = -((n : ℂ) + 1 - (t : ℂ)) := by
    push_cast
    ring
  rw [harg, Ring.choose_neg,
    show (n : ℂ) + 1 - (t : ℂ) + (t : ℂ) - 1 = (n : ℂ) by ring]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]

private theorem generatingMode_bpz (species : Bool) (n : ℤ) (x y : Fock) :
    beta (generatingMode species n x) y =
      (-1 : ℂ) ^ siteWeight species 0 * beta (parity x)
        (generatingMode species (2 * siteWeight species 0 - n - 2) y) := by
  cases species
  · change beta (b (n - 1) x) y = (-1 : ℂ) ^ (2 : ℤ) * beta (parity x)
      (b (2 * 2 - n - 2 - 1) y)
    rw [show (2 : ℤ) * 2 - n - 2 - 1 = -(n - 1) by omega,
      show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num]
    refine ghost_adjoint (b (n - 1)) (b (-(n - 1))) 1 y ?_ x
    intro S
    rw [parity_ket_charge, map_smul, LinearMap.smul_apply, smul_eq_mul, one_mul]
    exact beta_b (n - 1) (ket_homogeneous S) y
  · change beta (c (n + 2) x) y = (-1 : ℂ) ^ (-1 : ℤ) * beta (parity x)
      (c (2 * (-1) - n - 2 + 2) y)
    rw [show (2 : ℤ) * (-1) - n - 2 + 2 = -(n + 2) by omega,
      show (-1 : ℂ) ^ (-1 : ℤ) = -1 by norm_num]
    exact ghost_c_adjoint (n + 2) x y

/-- The signed BPZ mode transpose of a native one-site state, for every
derivative order, integer vertex mode, and pair of Fock vectors. The finite sum
uses the divided powers of the actual L(1) on the state. -/
theorem beta_site_mode (species : Bool) (t : ℕ) (n : ℤ) (x y : Fock) :
    beta (((Y (site species t)) [[n]]) x) y =
      (-1 : ℂ) ^ siteWeight species t * beta (parity x)
        ((∑ j ∈ Finset.range (t + 1),
          ((Y ((j.factorial : ℂ)⁻¹ • (L 1 ^ j) (site species t)))
            [[2 * siteWeight species t - n - (j : ℤ) - 2]])) y) := by
  have hmode : 2 * siteWeight species 0 - (n - (t : ℤ)) - 2 =
      2 * siteWeight species 0 + (t : ℤ) - 2 - n := by omega
  rw [site_modes species t n, LinearMap.smul_apply, beta.map_smul, LinearMap.smul_apply,
    smul_eq_mul, generatingMode_bpz species (n - t) x y, hmode,
    reflected_site_modes species t n, LinearMap.smul_apply, (beta (parity x)).map_smul,
    smul_eq_mul, derivative_choose, siteWeight_eq species t,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
  ring

#print axioms site
#print axioms siteWeight
#print axioms site_parity
#print axioms site_L0
#print axioms site_L1_pow
#print axioms site_L1_pow_eq_zero
#print axioms beta_site_mode

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostDerivativeBPZ
