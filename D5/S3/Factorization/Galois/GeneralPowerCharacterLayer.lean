/- GID: D5/S3/Factorization/Galois/GeneralPowerCharacterLayer
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/GeneralPowerCharacterLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite abelian power-character kernels equal power subgroups, with edge audits. -/
/- Library-search audit trail (2026-08-25):
   * Five repository routes checked exact names, kernel-intersection shapes, roots-of-unity
     concepts, character-separation declarations, and power-map call sites.
   * `QuadraticObservationBound` proves only the inclusion for binary observers, not this
     equality for arbitrary `n`; no repository declaration was equivalent to this theorem.
   * Pinned Mathlib's `rootsOfUnity`, `powMonoidHom`, and `Subgroup.mem_iInf` give the three
     named objects and the elementary inclusion.
   * The exact separation bridge is the parameterized theorem
     `CommGroup.forall_monoidHom_apply_eq_one_iff` in `FiniteAbelian/Duality.lean`.
   * `HasEnoughRootsOfUnity` for the complex numbers turns the separating complex-unit
     character into a character valued in `rootsOfUnity n ℂ`; no unbound atom remains.
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.GeneralPowerCharacterLayer

/-- The named group `μₙ` of complex `n`th roots of unity. For `n = 0`, Mathlib's
totalized convention makes this the full group of complex units. -/
abbrev complexNthRootsOfUnity (n : ℕ) := rootsOfUnity n ℂ

/-- A character whose values have order dividing `n`; surjectivity is not required. -/
abbrev PowerCharacter (G : Type*) [Group G] (n : ℕ) :=
  G →* complexNthRootsOfUnity n

/-- The subgroup denoted by `Gⁿ`, implemented as the range of the `n`th-power homomorphism. -/
def powerSubgroup (G : Type*) [CommGroup G] (n : ℕ) : Subgroup G :=
  (powMonoidHom n).range

/-- The intersection of the kernels of all characters valued in `μₙ`. -/
def powerCharacterJointKernel (G : Type*) [Group G] (n : ℕ) : Subgroup G :=
  ⨅ χ : PowerCharacter G n, MonoidHom.ker χ

/-- For a finite abelian group, all complex `n`-power characters have common kernel `Gⁿ`. -/
theorem power_character_joint_kernel_eq_power_subgroup
    (G : Type*) [CommGroup G] [Finite G] (n : ℕ) :
    powerCharacterJointKernel G n = powerSubgroup G n := by
  apply le_antisymm
  · intro x hx
    apply (CommGroup.forall_monoidHom_apply_eq_one_iff
      (G := G) ℂ (powerSubgroup G n) x).mp
    intro φ hφ
    let χ : PowerCharacter G n :=
      φ.codRestrict (rootsOfUnity n ℂ) fun g ↦ by
        rw [mem_rootsOfUnity, ← map_pow]
        exact hφ (g ^ n) ⟨g, rfl⟩
    have hxχ : χ x = 1 :=
      MonoidHom.mem_ker.mp ((Subgroup.mem_iInf.mp hx) χ)
    exact congrArg Subtype.val hxχ
  · rintro x ⟨g, rfl⟩
    rw [powerCharacterJointKernel, Subgroup.mem_iInf]
    intro χ
    rw [powMonoidHom_apply, MonoidHom.mem_ker, map_pow]
    exact OneMemClass.coe_eq_one.mp (χ g).prop

#print axioms power_character_joint_kernel_eq_power_subgroup

/-- The quotient by `Gⁿ` has exponent dividing `n`, including the totalized case `n = 0`. -/
theorem power_quotient_has_exponent_dividing (G : Type*) [CommGroup G] (n : ℕ) :
    Monoid.exponent (G ⧸ powerSubgroup G n) ∣ n := by
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩

#print axioms power_quotient_has_exponent_dividing

/-- `G/Gⁿ` is maximal among quotients in which every element has `n`th power one. -/
theorem power_subgroup_le_iff_quotient_pow_eq_one
    (G : Type*) [CommGroup G] (n : ℕ) (H : Subgroup G) :
    powerSubgroup G n ≤ H ↔ ∀ q : G ⧸ H, q ^ n = 1 := by
  constructor
  · intro h q
    refine QuotientGroup.induction_on q ?_
    intro g
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (h ⟨g, rfl⟩)
  · intro h x hx
    obtain ⟨g, rfl⟩ := hx
    exact (QuotientGroup.eq_one_iff _).1
      (by simpa using h (QuotientGroup.mk' H g))

#print axioms power_subgroup_le_iff_quotient_pow_eq_one

section DegenerateAudit

-- Empty-carrier audit: a group carrier is necessarily inhabited by its identity.
example {G : Type*} [Group G] : Nonempty G := ⟨1⟩

-- At `n = 0`, the root target is all complex units and both common kernel and `G⁰` are trivial.
example (G : Type*) [CommGroup G] [Finite G] :
    powerCharacterJointKernel G 0 = ⊥ ∧ powerSubgroup G 0 = ⊥ := by
  rw [power_character_joint_kernel_eq_power_subgroup]
  constructor <;> ext x <;>
    simp [powerSubgroup, MonoidHom.mem_range, powMonoidHom_apply, eq_comm]

-- At `n = 1`, the root target is trivial and both subgroups are all of `G`.
example (G : Type*) [CommGroup G] [Finite G] :
    powerCharacterJointKernel G 1 = ⊤ ∧ powerSubgroup G 1 = ⊤ := by
  rw [power_character_joint_kernel_eq_power_subgroup]
  constructor <;> ext x <;>
    simp [powerSubgroup, MonoidHom.mem_range, powMonoidHom_apply, eq_comm]

-- At `n = |G|`, every element has `n`th power one, so both subgroups are trivial.
example (G : Type*) [CommGroup G] [Finite G] :
    powerCharacterJointKernel G (Nat.card G) = ⊥ ∧
      powerSubgroup G (Nat.card G) = ⊥ := by
  rw [power_character_joint_kernel_eq_power_subgroup]
  constructor <;> ext x <;>
    simp [powerSubgroup, MonoidHom.mem_range, powMonoidHom_apply, eq_comm]

-- The one-element group satisfies the theorem for every `n`.
example (n : ℕ) : powerCharacterJointKernel Unit n = powerSubgroup Unit n :=
  power_character_joint_kernel_eq_power_subgroup Unit n

-- A concrete cyclic group satisfies the full arbitrary-power statement.
example (n : ℕ) :
    powerCharacterJointKernel (Multiplicative (ZMod 12)) n =
      powerSubgroup (Multiplicative (ZMod 12)) n :=
  power_character_joint_kernel_eq_power_subgroup _ n

-- If `n` is coprime to `|G|`, the power map is onto and both subgroups are all of `G`.
example (G : Type*) [CommGroup G] [Finite G] (n : ℕ)
    (h : n.Coprime (Nat.card G)) :
    powerCharacterJointKernel G n = ⊤ ∧ powerSubgroup G n = ⊤ := by
  rw [power_character_joint_kernel_eq_power_subgroup]
  have hp : powerSubgroup G n = ⊤ := by
    rw [powerSubgroup, MonoidHom.range_eq_top]
    exact h.symm.pow_left_bijective.surjective
  exact ⟨hp, hp⟩

-- The constant-one character is present but contributes no separation.
example (G : Type*) [Group G] (n : ℕ) (g : G) :
    (1 : PowerCharacter G n) g = 1 := by
  rfl

-- The identity character on the target itself separates distinct target values.
example (n : ℕ) (z : complexNthRootsOfUnity n) :
    MonoidHom.id (complexNthRootsOfUnity n) z = z := by
  rfl

-- The additive zero map is the type-tag counterpart of the constant-one character.
example (G : Type*) [Group G] (n : ℕ) (g : Additive G) :
    (0 : Additive G →+ Additive (complexNthRootsOfUnity n)) g = 0 := by
  rfl

end DegenerateAudit

end D5.S3.Factorization.Galois.GeneralPowerCharacterLayer
