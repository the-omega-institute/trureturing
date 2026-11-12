/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPureDownHomotopy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPureDownHomotopy
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Actual invM/R homotopy on plus/transverse monomials with one c excitation. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureGhostPrimary

/-!
SOURCE ONLY, UNCOMPILED. This is the finite ORIGINAL-basis part of the HPL
pure-down bridge: it evaluates the actual h=R invM on every no-minus
monomial tensored with c_{-m}ket{1}, and kills the c0 term.

This is not the missing assertion that positive L_m preserve the no-minus
polynomial space, nor that the actual finite physicalLift lies in that space.
Those obligations remain explicit in source-export.json. The formulas retain
the actual plus count, ghost quartet count, 1/m and 1/pPlus denominators.
Complex frames, zero polynomials and arbitrary integral charges are allowed.

Attribution: original quartet/HPL suppliers, the actual occupation CAR, and
Mathlib basis functional calculus. No new contraction or transferred Q.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private grouped_coordinate_R from
  D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private b_nonnegative_down from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureGhostPrimary

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureDownHomotopy

open LatticeGeneratingFieldLocality LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration (derivative_monomial)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open D5.S3.Quantum.Fermionic CountableOccupationFock
open MvPolynomial

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
  (B : Module.Basis (Fin t) ℂ F.K)

/-- The actual coordinate condition, allowing arbitrary plus creators and
transverse creators and excluding only minus creators. -/
def NoMinus (e : Exponents t) : Prop := ∀ r, e (minus t,r) = 0

private theorem noMinus_derivative (e : Exponents t) (he : NoMinus e) (r : ℕ) :
    pderiv (minus t,r) (monomial e (1 : ℂ)) = 0 := by
  rw [derivative_monomial, he r, Nat.cast_zero, zero_smul]

private theorem positive_b_excitation (k r : ℕ) :
    BcGhostFock.b ((k : ℤ)+1)
        (BcGhostFock.c (-((r : ℤ)+1)) (ket {1})) =
      if k = r then ket {1} else 0 := by
  have h := LinearMap.congr_fun
    (BcGhostFock.ghost_mixed_car ((k : ℤ)+1) (-((r : ℤ)+1))) (ket {1})
  have he : ((k : ℤ)+1) + -((r : ℤ)+1) = 0 ↔ k = r := by omega
  simpa only [LinearMap.add_apply, Module.End.mul_apply,
    b_nonnegative_down ((k : ℤ)+1) (by omega), map_zero, add_zero,
    he, Module.End.one_apply, LinearMap.zero_apply, ite_apply] using h

private theorem positive_b_c0 (k : ℕ) :
    BcGhostFock.b ((k : ℤ)+1) (BcGhostFock.c 0 (ket {1})) = 0 := by
  have h := LinearMap.congr_fun
    (BcGhostFock.ghost_mixed_car ((k : ℤ)+1) 0) (ket {1})
  simpa only [LinearMap.add_apply, Module.End.mul_apply,
    b_nonnegative_down ((k : ℤ)+1) (by omega), map_zero, add_zero,
    if_neg (by omega : ((k : ℤ)+1)+0 ≠ 0), LinearMap.zero_apply] using h

private theorem negative_c_down (r : ℕ) :
    BcGhostFock.c (-((r : ℤ)+1)) (ket {1}) =
      -ket ({1, 2*(r+1)+3} : Finset ℕ) := by
  have hcast : -((r : ℤ)+1) = -((r+1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, BcGhostQuartetCount.c_negative, create_ket]
  have hsite : 2*(r+1)+3 ≠ 1 := by omega
  have hphase : phase (2*(r+1)+3) {1} = -1 := by
    simp [phase, lowerCount, show 1 < 2*(r+1)+3 by omega]
  simp [hsite, hphase, Finset.pair_comm]

private theorem excitation_count (r : ℕ) :
    GC.count ({1, 2*(r+1)+3} : Finset ℕ) = 1 := by
  have h1 : 2*(r+1)+3 ≠ 1 := by omega
  have h3 : 2*(r+1)+3 ≠ 3 := by omega
  simp [BcGhostQuartetCount.count, h1, h3, Ne.symm h1, Ne.symm h3]

private theorem invM_sector_ket (p : Charge D) (e : Exponents t) (S : Finset ℕ) :
    invM F B (sector F B p (monomial e 1) (ket S)) =
      (if totalCount ((⟨p,e⟩,S) : StateIndex D t) = 0 then 0 else
        (totalCount ((⟨p,e⟩,S) : StateIndex D t) : ℂ)⁻¹) •
          sector F B p (monomial e 1) (ket S) := by
  rw [← actualBasis_apply, invM, inverseNumber, diagonal_basis]

private theorem invM_excitation (p : Charge D) (e : Exponents t) (r : ℕ) :
    invM F B (sector F B p (monomial e 1)
      (BcGhostFock.c (-((r : ℤ)+1)) (ket {1}))) =
      ((longitudinalCount e + 1 : ℕ) : ℂ)⁻¹ •
        sector F B p (monomial e 1)
          (BcGhostFock.c (-((r : ℤ)+1)) (ket {1})) := by
  have hcount : totalCount (D := D)
      ((⟨p,e⟩, {1, 2*(r+1)+3}) : StateIndex D t) = longitudinalCount e + 1 := by
    rw [totalCount, excitation_count]
  simp only [negative_c_down,
    show -ket ({1, 2*(r+1)+3} : Finset ℕ) =
      (-1 : ℂ) • ket {1, 2*(r+1)+3} by simp,
    sector_smul_right, map_smul]
  rw [invM_sector_ket, hcount]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
  simp only [smul_smul, mul_comm]

private theorem R_excitation (p : Charge D) (e : Exponents t)
    (he : NoMinus e) (r : ℕ) :
    R F p (sector F B p (monomial e 1)
        (BcGhostFock.c (-((r : ℤ)+1)) (ket {1}))) =
      ((F.pPlus p)⁻¹ * (r+1 : ℂ)⁻¹) •
        sector F B p (X (plus t,r) * monomial e 1) (ket {1}) := by
  have hterm (k : ℕ) :
      rTerm F k (sector F B p (monomial e 1)
        (BcGhostFock.c (-((r : ℤ)+1)) (ket {1}))) =
      if k = r then (r+1 : ℂ)⁻¹ •
        sector F B p (X (plus t,r) * monomial e 1) (ket {1}) else 0 := by
    rw [grouped_coordinate_R, noMinus_derivative e he,
      positive_b_excitation]
    by_cases hk : k = r
    · subst k
      simp [sector]
    · simp [hk, sector]
  change (F.pPlus p)⁻¹ •
    (∑ᶠ k : ℕ, rTerm F k (sector F B p (monomial e 1)
      (BcGhostFock.c (-((r : ℤ)+1)) (ket {1})))) = _
  simp only [hterm]
  rw [finsum_eq_single _ r (fun k hk => by simp [hk])]
  simp only [if_pos rfl, smul_smul]

/-- The ACTUAL homotopy produces a pure-down state with one additional plus
creator. The extra +1 in the invM denominator is the actual single ghost
excitation count. This formula does not divide by a possibly zero count. -/
theorem h_excitation (p : Charge D) (e : Exponents t) (he : NoMinus e) (r : ℕ) :
    h F B p (sector F B p (monomial e 1)
        (BcGhostFock.c (-((r : ℤ)+1)) (ket {1}))) =
      (((longitudinalCount e + 1 : ℕ) : ℂ)⁻¹ *
        (F.pPlus p)⁻¹ * (r+1 : ℂ)⁻¹) •
        sector F B p (X (plus t,r) * monomial e 1) (ket {1}) := by
  rw [h, Module.End.mul_apply, invM_excitation, map_smul, R_excitation F B p e he]
  simp only [smul_smul, mul_assoc]

/-- The zero-mode c0 term is killed by the SAME actual h. This is essential:
it cannot be silently removed from the original Q-d0 calculation. -/
theorem h_c0 (p : Charge D) (e : Exponents t) (he : NoMinus e) :
    h F B p (sector F B p (monomial e 1) (BcGhostFock.c 0 (ket {1}))) = 0 := by
  have hr : R F p (sector F B p (monomial e 1)
      (BcGhostFock.c 0 (ket {1}))) = 0 := by
    change (F.pPlus p)⁻¹ •
      (∑ᶠ k : ℕ, rTerm F k (sector F B p (monomial e 1)
        (BcGhostFock.c 0 (ket {1})))) = 0
    have hterm (k : ℕ) : rTerm F k (sector F B p (monomial e 1)
        (BcGhostFock.c 0 (ket {1}))) = 0 := by
      rw [grouped_coordinate_R, noMinus_derivative e he, positive_b_c0]
      simp [sector]
    simp only [hterm, finsum_zero, smul_zero]
  have hi : ∃ a : ℂ, invM F B (sector F B p (monomial e 1)
      (BcGhostFock.c 0 (ket {1}))) =
        a • sector F B p (monomial e 1) (BcGhostFock.c 0 (ket {1})) := by
    refine ⟨if totalCount ((⟨p,e⟩,{1,3}) : StateIndex D t) = 0 then 0 else
      (totalCount ((⟨p,e⟩,{1,3}) : StateIndex D t) : ℂ)⁻¹, ?_⟩
    simp only [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTInsertedTailOrthogonality.c0_down]
    simp only [show -ket ({1,3} : Finset ℕ) = (-1 : ℂ) • ket {1,3} by simp,
      sector_smul_right, map_smul, invM_sector_ket, smul_smul, mul_comm]
  obtain ⟨a, ha⟩ := hi
  rw [h, Module.End.mul_apply, ha, map_smul, hr, smul_zero]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureDownHomotopy
