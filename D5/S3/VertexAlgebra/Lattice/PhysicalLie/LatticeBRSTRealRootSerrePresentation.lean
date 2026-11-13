/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootSerrePresentation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootSerrePresentation
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Exact original physical real-root Serre relations and their actual Mathlib quotient representation. -/

/-
SOURCE_ONLY_UNCOMPILED. These are complete authored proof candidates, with no
native elaboration, kernel, axiom-closure, C# or registration acceptance claimed.
The full Monster/VOA/CFT/anomaly/fusion/string/AdS goal remains ACTIVE INCOMPLETE.

The original integral symmetric even D, arbitrary complex inverse Gram H with
BOTH inverse equations, rank26, literal global Cohomology and physicalImage
are unchanged. Both quotient slots retain all original State primitives.

Attribution: the original lattice fields retain Bakalov--Kac, Scott Carnahan
and Kalle Kytölä attribution, and the BRST/current construction retains
Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman attribution.
The physical suppliers provide charge addition, signed-shell vanishing, the
actual Cartan action and the normalized opposite/sl2 bracket. The presentation
is exactly Mathlib's SerreConstruction by Oliver Nash and Jonathan Reich,
with its Bourbaki and J.-P. Serre references; no replacement quotient is used.
Batteries supplies genuine private-name access without public aliases.
-/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootWeylReflection
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
import Mathlib.Algebra.Lie.SerreConstruction
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

open private bracket_mem_fiber iterate_mem_fiber chargeEnergy_add_zsmul
  bilinear_zsmul_left bilinear_zsmul_right from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
open private normalizedOpposite_mem sl2_ef gamma_charge root_length_two from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootWeylReflection
open private cartanClass_mem from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open private gamma_neg charge_energy_neg from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeRootBracket

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootSerrePresentation

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeSugawaraCurrents (gramComplex)
open LatticePositiveEnergy (chargeEnergy chargeEnergy_zero)
open LatticeBRSTCohomologyField (Cohomology)
open LatticeBRSTPhysicalLie (physicalImage)
open LatticeBRSTPhysicalChargeFiber (physicalChargeFiber)
open LatticeBRSTPhysicalCharacter (physicalChargeFiber_eq_bot_of_level_neg)
open LatticeBRSTNeutralPhysicalCartan (gamma cartanPhysicalImage cartan_adjoint)
open LatticeBRSTRealRootWeylReflection (normalizedOpposite)

universe u

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "Ph" => physicalImage D H h26 hHG hGH
local notation "Fib" => physicalChargeFiber D H h26 hHG hGH
local notation "hC" => cartanPhysicalImage D H h26 hHG hGH

/-- The exact root-vector Serre exponent on the original physical fibers.
The exponent depends on the two roots; this is not a uniform bound on Ph. -/
theorem real_root_serre
    (alpha beta : Charge D)
    (hα : chargeEnergy D alpha = 1) (hβ : chargeEnergy D beta = 1)
    (hb : bilinear D alpha beta ≤ 0)
    (x : Ph) (hx : (x : C) ∈ Fib alpha)
    (y : Ph) (hy : (y : C) ∈ Fib beta) :
    ((fun z : Ph => ⁅x, z⁆)^[(1 - bilinear D alpha beta).toNat]) y = 0 := by
  let b : ℤ := bilinear D alpha beta
  let n : ℕ := (1 - b).toNat
  have hb0 : b ≤ 0 := hb
  have hn : (n : ℤ) = 1 - b := Int.toNat_of_nonneg (by omega)
  have hn1 : 1 ≤ n := by omega
  have henergy : chargeEnergy D (beta + (n : ℤ) • alpha) = 2 - b := by
    rw [chargeEnergy_add_zsmul D beta alpha (n : ℤ), hβ, hα,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D beta alpha, hn]
    change 1 + (1 - b) * b + (1 - b) ^ 2 * 1 = 2 - b
    ring
  have hgt : 1 < chargeEnergy D (beta + (n : ℤ) • alpha) := by
    rw [henergy]
    omega
  have hcharge : beta + (n : ℤ) • alpha ≠ 0 := by
    intro hz
    rw [hz, chargeEnergy_zero] at hgt
    omega
  have hlevel : 1 - chargeEnergy D (beta + (n : ℤ) • alpha) < 0 := by omega
  have hmem := iterate_mem_fiber D H h26 hHG hGH alpha beta x hx n y hy
  rw [physicalChargeFiber_eq_bot_of_level_neg D H h26 hHG hGH
    (beta + (n : ℤ) • alpha) hcharge hlevel] at hmem
  have hz : (((fun z : Ph => ⁅x, z⁆)^[n]) y : C) = 0 :=
    (Submodule.mem_bot ℂ (M := C)).mp hmem
  apply Subtype.ext
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- A representation of the EXISTING Mathlib Serre quotient on the unchanged
physical image. Its free generators H_i, E_i, F_i are sent respectively to
hC(alpha_i complex), the chosen actual e_i, and its actual normalizedOpposite.
The index type is arbitrary; only the presentation's DecidableEq is classical.
No assertion of faithfulness, surjectivity, or Monster recognition is made. -/
theorem exists_realRootSerreRepresentation {I : Type u}
    (alpha : I → Charge D) (hq : ∀ i, chargeEnergy D (alpha i) = 1)
    (hb : ∀ i j, i ≠ j → bilinear D (alpha i) (alpha j) ≤ 0)
    (e : I → Ph) (he : ∀ i, (e i : C) ∈ Fib (alpha i))
    (he0 : ∀ i, e i ≠ 0) :
    letI : DecidableEq I := Classical.decEq I
    ∃ φ : Matrix.ToLieAlgebra ℂ (fun i j => bilinear D (alpha i) (alpha j)) →ₗ⁅ℂ⁆ Ph,
      (∀ i, φ (LieSubmodule.Quotient.mk (FreeLieAlgebra.of ℂ (.H i))) =
        hC (fun k => (alpha i k : ℂ))) ∧
      (∀ i, φ (LieSubmodule.Quotient.mk (FreeLieAlgebra.of ℂ (.E i))) = e i) ∧
      (∀ i, φ (LieSubmodule.Quotient.mk (FreeLieAlgebra.of ℂ (.F i))) =
        normalizedOpposite D H h26 hHG hGH
          (alpha i) (hq i) (e i) (he i) (he0 i)) := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    letI : DecidableEq I := Classical.decEq I
    let CM : Matrix I I ℤ := fun i j => bilinear D (alpha i) (alpha j)
    let f : I → Ph := fun i =>
      normalizedOpposite D H h26 hHG hGH (alpha i) (hq i) (e i) (he i) (he0 i)
    let h : I → Ph := fun i => hC (fun k => (alpha i k : ℂ))
    have hf (i : I) : (f i : C) ∈ Fib (-alpha i) :=
      normalizedOpposite_mem D H h26 hHG hGH
        (alpha i) (hq i) (e i) (he i) (he0 i)
    have hdiag (i : I) : CM i i = 2 := root_length_two D (alpha i) (hq i)
    have hnegq (i : I) : chargeEnergy D (-alpha i) = 1 := by
      rw [charge_energy_neg, hq i]
    have hnegCM (i j : I) : bilinear D (-alpha i) (-alpha j) = CM i j := by
      calc
        _ = bilinear D ((-1 : ℤ) • alpha i) ((-1 : ℤ) • alpha j) := by simp
        _ = CM i j := by
          rw [bilinear_zsmul_left D (alpha i) ((-1 : ℤ) • alpha j) (-1),
            bilinear_zsmul_right D (alpha i) (alpha j) (-1)]
          change -1 * (-1 * bilinear D (alpha i) (alpha j)) =
            bilinear D (alpha i) (alpha j)
          ring
    have hHH (i j : I) : ⁅h i, h j⁆ = 0 := by
      simpa [gamma, bilinear] using
        (cartan_adjoint D H h26 hHG hGH (fun k => (alpha i k : ℂ)) 0 (h j)
          (cartanClass_mem D H h26 hHG hGH (fun k => (alpha j k : ℂ))).2)
    have hEF (i : I) : ⁅e i, f i⁆ = h i :=
      sl2_ef D H h26 hHG hGH (alpha i) (hq i) (e i) (he i) (he0 i)
    have hEFoff (i j : I) (hij : i ≠ j) : ⁅e i, f j⁆ = 0 := by
      have henergy : chargeEnergy D (alpha i + -alpha j) = 2 - CM i j := by
        calc
          _ = chargeEnergy D (alpha i) + (-1 : ℤ) * bilinear D (alpha i) (alpha j) +
              (-1 : ℤ) ^ 2 * chargeEnergy D (alpha j) := by
            simpa only [neg_one_zsmul] using
              (chargeEnergy_add_zsmul D (alpha i) (alpha j) (-1))
          _ = 2 - CM i j := by rw [hq i, hq j]; dsimp [CM]; ring
      have hgt : 1 < chargeEnergy D (alpha i + -alpha j) := by
        have hb0 : CM i j ≤ 0 := hb i j hij
        rw [henergy]
        omega
      have hcharge : alpha i + -alpha j ≠ 0 := by
        intro hz
        rw [hz, chargeEnergy_zero] at hgt
        omega
      have hlevel : 1 - chargeEnergy D (alpha i + -alpha j) < 0 := by omega
      have hmem := bracket_mem_fiber D H h26 hHG hGH
        (alpha i) (-alpha j) (e i) (f j) (he i) (hf j)
      rw [physicalChargeFiber_eq_bot_of_level_neg D H h26 hHG hGH
        (alpha i + -alpha j) hcharge hlevel] at hmem
      apply Subtype.ext
      exact (Submodule.mem_bot ℂ (M := C)).mp hmem
    have hHE (i j : I) : ⁅h i, e j⁆ = (CM i j : ℂ) • e j := by
      simpa only [gamma_charge] using
        (cartan_adjoint D H h26 hHG hGH (fun k => (alpha i k : ℂ))
          (alpha j) (e j) (he j).2)
    have hHF (i j : I) : ⁅h i, f j⁆ = -(CM i j : ℂ) • f j := by
      simpa only [gamma_neg, gamma_charge] using
        (cartan_adjoint D H h26 hHG hGH (fun k => (alpha i k : ℂ))
          (-alpha j) (f j) (hf j).2)
    let g : CartanMatrix.Generators I → Ph
      | .H i => h i
      | .E i => e i
      | .F i => f i
    let T := FreeLieAlgebra ℂ (CartanMatrix.Generators I)
    let Φ : T →ₗ⁅ℂ⁆ Ph := FreeLieAlgebra.lift ℂ g
    have hgen (s : CartanMatrix.Generators I) :
        Φ (FreeLieAlgebra.of ℂ s) = g s := FreeLieAlgebra.lift_of_apply g s
    -- LieAlgebra.ad is LEFT bracketing. It has the opposite sign to inner.
    have hmap (a z : T) (n : ℕ) :
        Φ ((LieAlgebra.ad ℂ T a ^ n) z) =
          ((fun w : Ph => ⁅Φ a, w⁆)^[n]) (Φ z) := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply,
            Φ.map_lie, ih, Function.iterate_succ_apply']
    -- The extra initial bracket in Mathlib contributes the final +1.
    have hbridge (a z : T) (n : ℕ) :
        Φ ((LieAlgebra.ad ℂ T a ^ n) ⁅a, z⁆) =
          ((fun w : Ph => ⁅Φ a, w⁆)^[n + 1]) (Φ z) := by
      rw [hmap, Φ.map_lie, Function.iterate_succ_apply]
    have hHHrel (i j : I) : Φ (CartanMatrix.Relations.HH ℂ (i, j)) = 0 := by
      change Φ ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)⁆ = 0
      rw [Φ.map_lie, hgen, hgen]
      exact hHH i j
    have hEFrel (i j : I) : Φ (CartanMatrix.Relations.EF ℂ (i, j)) = 0 := by
      by_cases hij : i = j
      · subst j
        have hrel : CartanMatrix.Relations.EF ℂ (i, i) =
            ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)⁆ -
              FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i) := by
          simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ite_true,
            Function.comp_apply]
        rw [hrel]
        rw [map_sub, Φ.map_lie, hgen, hgen, hgen]
        change ⁅e i, f i⁆ - h i = 0
        rw [hEF, sub_self]
      · have hrel : CartanMatrix.Relations.EF ℂ (i, j) =
            ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆ := by
          simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, if_neg hij,
            Function.comp_apply]
        rw [hrel, Φ.map_lie, hgen, hgen]
        exact hEFoff i j hij
    have hHErel (i j : I) : Φ (CartanMatrix.Relations.HE ℂ CM (i, j)) = 0 := by
      change Φ (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆ -
        CM i j • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)) = 0
      rw [map_sub, map_zsmul, Φ.map_lie, hgen, hgen]
      change ⁅h i, e j⁆ - CM i j • e j = 0
      rw [hHE, Int.cast_smul_eq_zsmul ℂ, sub_self]
    have hHFrel (i j : I) : Φ (CartanMatrix.Relations.HF ℂ CM (i, j)) = 0 := by
      change Φ (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆ +
        CM i j • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)) = 0
      rw [map_add, map_zsmul, Φ.map_lie, hgen, hgen]
      change ⁅h i, f j⁆ + CM i j • f j = 0
      rw [hHF, neg_smul, Int.cast_smul_eq_zsmul ℂ, neg_add_cancel]
    have hAdErel (i j : I) : Φ (CartanMatrix.Relations.adE ℂ CM (i, j)) = 0 := by
      by_cases hij : i = j
      · subst j
        simp [CartanMatrix.Relations.adE, hdiag]
      · change Φ ((LieAlgebra.ad ℂ T (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)) ^
            (-CM i j).toNat) ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆) = 0
        rw [hbridge]
        simp only [hgen]
        have hn : (-CM i j).toNat + 1 = (1 - CM i j).toNat := by
          have hb0 : CM i j ≤ 0 := hb i j hij
          omega
        rw [hn]
        exact real_root_serre D H h26 hHG hGH (alpha i) (alpha j)
          (hq i) (hq j) (hb i j hij) (e i) (he i) (e j) (he j)
    have hAdFrel (i j : I) : Φ (CartanMatrix.Relations.adF ℂ CM (i, j)) = 0 := by
      by_cases hij : i = j
      · subst j
        simp [CartanMatrix.Relations.adF, hdiag]
      · change Φ ((LieAlgebra.ad ℂ T (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)) ^
            (-CM i j).toNat) ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆) = 0
        rw [hbridge]
        simp only [hgen]
        have hn : (-CM i j).toNat + 1 = (1 - CM i j).toNat := by
          have hb0 : CM i j ≤ 0 := hb i j hij
          omega
        rw [hn]
        have hbneg : bilinear D (-alpha i) (-alpha j) ≤ 0 := by
          rw [hnegCM]
          exact hb i j hij
        simpa only [hnegCM] using
          (real_root_serre D H h26 hHG hGH (-alpha i) (-alpha j)
            (hnegq i) (hnegq j) hbneg (f i) (hf i) (f j) (hf j))
    have hker : CartanMatrix.Relations.toIdeal ℂ CM ≤ Φ.ker := by
      apply LieSubmodule.lieSpan_le.mpr
      simp only [CartanMatrix.Relations.toSet, Set.union_subset_iff, Set.range_subset_iff]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
        rintro ⟨i, j⟩ <;> apply LieHom.mem_ker.mpr
      · exact hHHrel i j
      · exact hEFrel i j
      · exact hHErel i j
      · exact hHFrel i j
      · exact hAdErel i j
      · exact hAdFrel i j
    -- The pinned Lie quotient has no LieHom liftQ. Use its actual Submodule
    -- liftQ and prove bracket preservation on the actual quotient representatives.
    let ψ : Matrix.ToLieAlgebra ℂ CM →ₗ[ℂ] Ph :=
      (CartanMatrix.Relations.toIdeal ℂ CM).toSubmodule.liftQ Φ.toLinearMap (by
        intro z hz
        exact LieHom.mem_ker.mp (hker hz))
    let φ : Matrix.ToLieAlgebra ℂ CM →ₗ⁅ℂ⁆ Ph :=
      { ψ with
        map_lie' := by
          intro x y
          refine Submodule.Quotient.induction_on (CartanMatrix.Relations.toIdeal ℂ CM).toSubmodule x ?_
          intro a
          refine Submodule.Quotient.induction_on (CartanMatrix.Relations.toIdeal ℂ CM).toSubmodule y ?_
          intro b
          change Φ ⁅a, b⁆ = ⁅Φ a, Φ b⁆
          exact Φ.map_lie a b }
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro i
      change Φ (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) = h i
      exact hgen (CartanMatrix.Generators.H i)
    · intro i
      change Φ (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)) = e i
      exact hgen (CartanMatrix.Generators.E i)
    · intro i
      change Φ (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)) = f i
      exact hgen (CartanMatrix.Generators.F i)

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootSerrePresentation
