/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTGlobalPhysicalNondegeneracy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTGlobalPhysicalNondegeneracy
   mirror-E: none(waiver:source-only-global-physical-nondegeneracy)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas]
   utility: none
   digest: Both full radicals of the original global physical bilinear form vanish. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeRootBracket
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalDuality
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-!
SOURCE_ONLY_UNCOMPILED. The accepted196 suppliers are used at their sealed
bytes, especially OppositeRootBracket. The finite charge reconstruction in
PositiveRootIntegrability is a SOURCE supplier: its native acceptance is an
outstanding obligation, as is elaboration and kernel checking of this file.

The carrier is literally the original physicalImage in original Cohomology.
Primitives in BOTH global quotient slots remain arbitrary original State D.
There is no charge/root assumption in the public theorem, and zero charge
is retained. D is the original integral symmetric even lattice; H is complex
with BOTH inverse equations. No positivity, realness, signature, unimodularity,
global finite dimension, Noetherianity, perfectness, convergence or additional
physical hypothesis is used. In particular, no surjection from the whole
physical image onto its full algebraic dual is asserted.

This is the classical invariant-form argument for a charge-graded Lie
algebra: Cartan invariance gives the PLUS of the two weights, finite support
isolates each component, opposite-fiber duality treats nonzero charges, and
the actual neutral minus-Gram form treats zero charge. The right radical
uses SURJECTIVITY at the opposite charge and algebraic-dual separation;
symmetry of the physical bilinear form is never assumed or invoked.

Original lattice/VOA/BRST suppliers retain Bakalov--Kac, Scott Carnahan,
Kalle Kytölä, Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman
attribution. Mathlib supplies finite sums, linear algebra and algebraic-dual
separation (Johan Commelin, Fabian Glöckle, Kyle Miller and contributors);
Batteries supplies private-name access (Mario Carneiro and contributors).
The Pro conclusion is advisory mathematical data, not authority or kernel
evidence. The full Monster/VOA/CFT/anomaly/fusion/string/AdS goal remains
ACTIVE INCOMPLETE.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

-- These are exact MODULE paths, independently of ordinary namespace opens.
open private gamma_expansion coordinates_of_tests cartan_global_pairing from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeRootBracket
open private physicalComponent physicalComponent_mem_fiber physical_sum_components from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
open private fiberInclusion from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
open private cartanClass_mem from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalNondegeneracy

open LatticeGeneratingFieldLocality (LatticeData Charge)
open LatticeMatterGhostCoupling (State)
open LatticeSugawaraCurrents (gramComplex)
open LatticeBRSTCohomologyField (Cohomology)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie
  (physicalClass physicalImage)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
  (chargeSupport)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
  (physicalChargeFiber oppositePairing)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear
  (physicalBilinearForm)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalBilinearInvariant
  (physicalBilinearForm_invariant)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
  (neutralPhysicalImage neutralCartanEquiv cartanPhysicalImage cartan_adjoint gamma)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalDuality
  (nonzeroChargeDuality)

-- This is symmetry of the finite Gram expression, not symmetry of B.
private theorem gram_pairing_swap (D : LatticeData) (e f : Fin D.rank → ℂ) :
    (∑ i : Fin D.rank, ∑ j : Fin D.rank, e i * (D.G i j : ℂ) * f j) =
      ∑ j : Fin D.rank, ∑ i : Fin D.rank, f j * (D.G j i : ℂ) * e i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [D.symmetric i j]
  ring

-- Reuse the accepted coordinate recovery, rather than proving it again.
private theorem gamma_separates_charge (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hp : p ≠ 0) :
    ∃ v : Fin D.rank → ℂ, gamma D v p ≠ 0 := by
  classical
  by_contra! h
  have htests (f : Fin D.rank → ℂ) :
      -(∑ i : Fin D.rank, ∑ j : Fin D.rank,
        (p i : ℂ) * (D.G i j : ℂ) * f j) = gamma D f 0 * (0 : ℂ) := by
    calc
      _ = -(∑ i : Fin D.rank, ∑ j : Fin D.rank,
          f i * (D.G i j : ℂ) * (p j : ℂ)) :=
        congrArg Neg.neg (gram_pairing_swap D (fun i => (p i : ℂ)) f)
      _ = -gamma D f p := by rw [gamma_expansion]
      _ = gamma D f 0 * (0 : ℂ) := by rw [h f]; simp
  have hcoord : (fun i => (p i : ℂ)) = (0 : Fin D.rank → ℂ) := by
    simpa using coordinates_of_tests D H hGH 0 0 (fun i => (p i : ℂ)) htests
  apply hp
  funext i
  have hi : (p i : ℂ) = 0 := congrFun hcoord i
  exact_mod_cast hi

section Orthogonality

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "Ph" => physicalImage D H h26 hHG hGH
local notation "Fib" => physicalChargeFiber D H h26 hHG hGH
local notation "B" => physicalBilinearForm D H h26 hHG hGH

-- Includes both mixed zero/nonzero cases; it imposes only a+b ≠ 0.
private theorem charge_pairing_zero (a b : Charge D) (x y : Ph)
    (hx : (x : C) ∈ Fib a) (hy : (y : C) ∈ Fib b) (hab : a + b ≠ 0) :
    B x y = 0 := by
  have hweight (v : Fin D.rank → ℂ) :
      (gamma D v a + gamma D v b) * B x y = 0 := by
    have hinv := physicalBilinearForm_invariant D H h26 hHG hGH
      x (cartanPhysicalImage D H h26 hHG hGH v) y
    have hskew : ⁅x, cartanPhysicalImage D H h26 hHG hGH v⁆ =
        -(gamma D v a • x) := by
      calc
        _ = -⁅cartanPhysicalImage D H h26 hHG hGH v, x⁆ :=
          (lie_skew x (cartanPhysicalImage D H h26 hHG hGH v)).symm
        _ = _ := by rw [cartan_adjoint D H h26 hHG hGH v a x hx.2]
    rw [hskew, cartan_adjoint D H h26 hHG hGH v b y hy.2] at hinv
    simp only [map_neg, LinearMap.neg_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul] at hinv
    linear_combination -hinv
  obtain ⟨v, hv⟩ := gamma_separates_charge D H hGH (a + b) hab
  have hadd : gamma D v (a + b) = gamma D v a + gamma D v b := by
    simp only [gamma_expansion, Pi.add_apply, Int.cast_add, mul_add,
      Finset.sum_add_distrib]
  have hzero := hweight v
  rw [← hadd] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hv

end Orthogonality

/-- BOTH full radicals of the existing form vanish on the literal all-charge
original physical image. There is no root, charge or additional physical
assumption; the inverse matrix is complex and BOTH inverse equations remain.
Nondegenerate is exactly Mathlib's SeparatingLeft ∧ SeparatingRight. -/
theorem physicalBilinearForm_nondegenerate
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (physicalBilinearForm D H h26 hHG hGH).Nondegenerate := by
  classical
  let C := Cohomology D H h26 hHG hGH
  let Ph := physicalImage D H h26 hHG hGH
  let Fib := physicalChargeFiber D H h26 hHG hGH
  let B := physicalBilinearForm D H h26 hHG hGH
  change B.SeparatingLeft ∧ B.SeparatingRight
  constructor
  · intro x hx
    obtain ⟨u, hu⟩ := x.property
    let S := chargeSupport D (u : State D)
    let c : Charge D → Ph := physicalComponent D H h26 hHG hGH u
    have hc (a : Charge D) : (c a : C) ∈ Fib a :=
      physicalComponent_mem_fiber D H h26 hHG hGH u a
    have hsum : x = ∑ a ∈ S, c a := by
      calc
        x = (⟨physicalClass D H h26 hHG hGH u, ⟨u, rfl⟩⟩ : Ph) := by
          apply Subtype.ext
          exact hu.symm
        _ = _ := physical_sum_components D H h26 hHG hGH u
    have hzero (a : Charge D) (ha : a ∈ S) : c a = 0 := by
      have htest (z : Ph) (hz : (z : C) ∈ Fib (-a)) : B (c a) z = 0 := by
        have ht := hx z
        rw [hsum, map_sum, LinearMap.sum_apply] at ht
        have hsingle : (∑ q ∈ S, B (c q) z) = B (c a) z := by
          apply Finset.sum_eq_single a
          · intro q hq hqa
            apply charge_pairing_zero D H h26 hHG hGH q (-a) (c q) z (hc q) hz
            intro heq
            exact hqa (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using heq))
          · intro hnot
            exact False.elim (hnot ha)
        exact hsingle.symm.trans ht
      by_cases ha0 : a = 0
      · subst a
        -- Fib 0 and neutralPhysicalImage are the same literal intersection.
        let z0 : neutralPhysicalImage D H h26 hHG hGH := ⟨(c 0 : C), hc 0⟩
        let E := neutralCartanEquiv D H h26 hHG hGH
        let v : Fin D.rank → ℂ := E.symm z0
        have hv : cartanPhysicalImage D H h26 hHG hGH v = c 0 := by
          apply Subtype.ext
          change ((E v : neutralPhysicalImage D H h26 hHG hGH) : C) = (z0 : C)
          exact congrArg Subtype.val (E.apply_symm_apply z0)
        have htests (w : Fin D.rank → ℂ) :
            -(∑ i : Fin D.rank, ∑ j : Fin D.rank,
              v i * (D.G i j : ℂ) * w j) = gamma D w 0 * (0 : ℂ) := by
          calc
            _ = B (cartanPhysicalImage D H h26 hHG hGH v)
                (cartanPhysicalImage D H h26 hHG hGH w) :=
              (cartan_global_pairing D H h26 hHG hGH v w).symm
            _ = 0 := by
              rw [hv]
              exact htest (cartanPhysicalImage D H h26 hHG hGH w)
                (by simpa only [neg_zero] using
                  (cartanClass_mem D H h26 hHG hGH w))
            _ = gamma D w 0 * (0 : ℂ) := by simp
        have hv0 : v = 0 := by
          simpa using coordinates_of_tests D H hGH 0 0 v htests
        rw [← hv, hv0, map_zero]
      · let ca : Fib a := ⟨(c a : C), hc a⟩
        have hdual : nonzeroChargeDuality D H h26 hHG hGH a ha0 ca = 0 := by
          apply LinearMap.ext
          intro z
          change B (c a) (fiberInclusion D H h26 hHG hGH (-a) z) = 0
          exact htest (fiberInclusion D H h26 hHG hGH (-a) z) z.property
        have hca : ca = 0 :=
          (nonzeroChargeDuality D H h26 hHG hGH a ha0).injective
            (by rw [hdual, map_zero])
        apply Subtype.ext
        exact congrArg (fun z : Fib a => (z : C)) hca
    rw [hsum]
    exact Finset.sum_eq_zero hzero
  · intro y hy
    obtain ⟨u, hu⟩ := y.property
    let S := chargeSupport D (u : State D)
    let c : Charge D → Ph := physicalComponent D H h26 hHG hGH u
    have hc (b : Charge D) : (c b : C) ∈ Fib b :=
      physicalComponent_mem_fiber D H h26 hHG hGH u b
    have hsum : y = ∑ b ∈ S, c b := by
      calc
        y = (⟨physicalClass D H h26 hHG hGH u, ⟨u, rfl⟩⟩ : Ph) := by
          apply Subtype.ext
          exact hu.symm
        _ = _ := physical_sum_components D H h26 hHG hGH u
    have hzero (b : Charge D) (hb : b ∈ S) : c b = 0 := by
      have htest (z : Ph) (hz : (z : C) ∈ Fib (-b)) : B z (c b) = 0 := by
        have ht := hy z
        rw [hsum, map_sum] at ht
        have hsingle : (∑ q ∈ S, B z (c q)) = B z (c b) := by
          apply Finset.sum_eq_single b
          · intro q hq hqb
            apply charge_pairing_zero D H h26 hHG hGH (-b) q z (c q) hz (hc q)
            intro heq
            exact hqb (sub_eq_zero.mp
              (by simpa only [sub_eq_add_neg, add_comm] using heq))
          · intro hnot
            exact False.elim (hnot hb)
        exact hsingle.symm.trans ht
      by_cases hb0 : b = 0
      · subst b
        let z0 : neutralPhysicalImage D H h26 hHG hGH := ⟨(c 0 : C), hc 0⟩
        let E := neutralCartanEquiv D H h26 hHG hGH
        let w : Fin D.rank → ℂ := E.symm z0
        have hw : cartanPhysicalImage D H h26 hHG hGH w = c 0 := by
          apply Subtype.ext
          change ((E w : neutralPhysicalImage D H h26 hHG hGH) : C) = (z0 : C)
          exact congrArg Subtype.val (E.apply_symm_apply z0)
        have htests (v : Fin D.rank → ℂ) :
            -(∑ i : Fin D.rank, ∑ j : Fin D.rank,
              w i * (D.G i j : ℂ) * v j) = gamma D v 0 * (0 : ℂ) := by
          calc
            _ = -(∑ i : Fin D.rank, ∑ j : Fin D.rank,
                v i * (D.G i j : ℂ) * w j) :=
              congrArg Neg.neg (gram_pairing_swap D w v)
            _ = B (cartanPhysicalImage D H h26 hHG hGH v)
                (cartanPhysicalImage D H h26 hHG hGH w) :=
              (cartan_global_pairing D H h26 hHG hGH v w).symm
            _ = 0 := by
              rw [hw]
              exact htest (cartanPhysicalImage D H h26 hHG hGH v)
                (by simpa only [neg_zero] using
                  (cartanClass_mem D H h26 hHG hGH v))
            _ = gamma D v 0 * (0 : ℂ) := by simp
        have hw0 : w = 0 := by
          simpa using coordinates_of_tests D H hGH 0 0 w htests
        rw [← hw, hw0, map_zero]
      · let cb : Fib b := ⟨(c b : C), hc b⟩
        have hcb : cb = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ cb).mp (by
          intro f
          -- Surjectivity at -b, not injectivity at b. Rewrite -(-b) to b
          -- in the actual forward map before applying it to f : Dual(Fib b).
          have honto := (nonzeroChargeDuality D H h26 hHG hGH
            (-b) (neg_ne_zero.mpr hb0)).surjective
          change Function.Surjective (oppositePairing D H h26 hHG hGH (-b)) at honto
          simp only [oppositePairing, neg_neg] at honto
          obtain ⟨z, hz⟩ := honto f
          have heval := LinearMap.congr_fun hz cb
          change B (fiberInclusion D H h26 hHG hGH (-b) z) (c b) = f cb at heval
          calc
            f cb = B (fiberInclusion D H h26 hHG hGH (-b) z) (c b) := heval.symm
            _ = 0 := htest (fiberInclusion D H h26 hHG hGH (-b) z) z.property)
        apply Subtype.ext
        exact congrArg (fun z : Fib b => (z : C)) hcb
    rw [hsum]
    exact Finset.sum_eq_zero hzero

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalNondegeneracy
