/- GID: D5/S3/FiniteGroups/FrattiniAutomorphismKernel
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FrattiniAutomorphismKernel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.Frattini, mathlib/module/Mathlib.GroupTheory.PGroup, mathlib/module/Mathlib.GroupTheory.GroupAction.Quotient]
   utility: none
   digest: The ordinary Frattini automorphism kernel of every finite p-group is a p-group. -/

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
Port of Qiuzhen-CFSG/CFSG, immutable revision
0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7:
Theory/GroupTheory/PGroup/FrattiniAutomorphismKernel.lean and the quotientAut
construction in Theory/GroupTheory/CentralCharacteristicAutomorphisms.lean.
Apache-2.0; full upstream license: docs/reports/licenses/cfsg-frattini-kernel-LICENSE.txt.
Modified namespace, imports, visibility and module syntax for the repository.
The port retires in favor of direct Mathlib use when this repository's pinned
Mathlib declares Subgroup.isPGroup_quotientAut_frattini_kernel with this type.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.FrattiniAutomorphismKernel
open Subgroup

section QuotientAction
variable {G : Type*} [Group G] (C : Subgroup G) [C.Characteristic]

/-- The action of automorphisms on the quotient by a characteristic subgroup. -/
def quotientAut : MulAut G →* MulAut (G ⧸ C) where
  toFun f := QuotientGroup.congr C C f (characteristic_iff_map_eq.mp inferInstance f)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl
  map_mul' f g := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl

@[simp] private theorem quotientAut_apply_mk (f : MulAut G) (x : G) :
    quotientAut C f (QuotientGroup.mk' C x) = QuotientGroup.mk' C (f x) := by rfl

end QuotientAction

/-- The automorphisms of a finite p-group inducing the identity on its
Frattini quotient form a p-group. -/
theorem isPGroup_quotientAut_frattini_kernel
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hG : IsPGroup p G) :
    IsPGroup p (quotientAut (frattini G)).ker := by
  classical
  let C := frattini G
  let K := (quotientAut C).ker
  let X := G → C
  have hdisp (a : K) (g : G) : g⁻¹ * (a : MulAut G) g ∈ C := by
    have ha := DFunLike.congr_fun a.property (QuotientGroup.mk' C g)
    have he : QuotientGroup.mk' C g = QuotientGroup.mk' C ((a : MulAut G) g) := by
      rw [quotientAut_apply_mk] at ha
      exact ha.symm
    exact QuotientGroup.eq.mp he
  let : MulAction K X :=
    { smul a f g := ⟨g⁻¹ * (a : MulAut G) (g * f g), by
        rw [map_mul, ← mul_assoc]
        exact C.mul_mem (hdisp a g)
          ((characteristic_iff_map_le.mp inferInstance (a : MulAut G))
            (mem_map_of_mem _ (f g).property))⟩
      one_smul f := by
        funext g
        apply Subtype.ext
        change g⁻¹ * ((1 : MulAut G) (g * f g)) = (f g : G)
        simp
      mul_smul a b f := by
        funext g
        apply Subtype.ext
        change g⁻¹ * (a : MulAut G) ((b : MulAut G) (g * f g)) =
          g⁻¹ * (a : MulAut G) (g * (g⁻¹ * (b : MulAut G) (g * f g)))
        simp }
  have hstab (f : X) : MulAction.stabilizer K f = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have hfix : ∀ g : G, (a : MulAut G) (g * f g) = g * f g := by
      intro g
      have hh := congrArg Subtype.val (congrFun ha g)
      change g⁻¹ * (a : MulAut G) (g * f g) = (f g : G) at hh
      calc
        (a : MulAut G) (g * f g) = g * (g⁻¹ * (a : MulAut G) (g * f g)) := by simp
        _ = g * f g := by rw [hh]
    let E := (a : MulAut G).toMonoidHom.eqLocus (MonoidHom.id G)
    have hsup : E ⊔ frattini G = ⊤ := by
      apply top_unique
      intro g _
      have hx : g * f g ∈ E ⊔ frattini G :=
        (show E ≤ E ⊔ frattini G from le_sup_left) (hfix g)
      have hy : ((f g : C) : G)⁻¹ ∈ E ⊔ frattini G :=
        (show frattini G ≤ E ⊔ frattini G from le_sup_right) (C.inv_mem (f g).property)
      simpa using (E ⊔ frattini G).mul_mem hx hy
    have hE : E = ⊤ := frattini_nongenerating hsup
    apply Subtype.ext
    apply MulEquiv.ext
    intro g
    have hg : g ∈ E := hE ▸ mem_top g
    exact hg
  have hcard : Nat.card K ∣ Nat.card X := by
    have e := MulAction.selfEquivOrbitsQuotientProd (G := K) (X := X) hstab
    rw [Nat.card_congr e, Nat.card_prod]
    exact dvd_mul_left _ _
  obtain ⟨n, hn⟩ := (hG.to_subgroup C).exists_card_dvd_pow
  apply IsPGroup.of_card_dvd_pow (n := n * Nat.card G)
  apply hcard.trans
  change Nat.card (G → C) ∣ p ^ (n * Nat.card G)
  rw [Nat.card_fun, pow_mul]
  exact pow_dvd_pow_of_dvd hn _

end D5.S3.FiniteGroups.FrattiniAutomorphismKernel
