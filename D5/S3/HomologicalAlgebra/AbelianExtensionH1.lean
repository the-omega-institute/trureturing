/- GID: D5/S3/HomologicalAlgebra/AbelianExtensionH1
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/AbelianExtensionH1
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.GroupExtension.Basic, mathlib/module/Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree]
   utility: none
   digest: Automorphisms of arbitrary abelian extensions modulo inner kernel automorphisms are actual first cohomology. -/

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.Group

set_option autoImplicit false
noncomputable section
namespace D5.S3.HomologicalAlgebra.AbelianExtensionH1
open groupCohomology

variable {N Q S : Type*} [CommGroup N] [Group Q] [Group S]
variable (E : GroupExtension N Q S)

private theorem conj_kernel (x : Q) (hx : x ∈ E.rightHom.ker) : E.conjAct x = 1 := by
  rw [← E.range_inl_eq_ker_rightHom] at hx
  obtain ⟨n, rfl⟩ := hx
  ext m
  apply E.inl_injective
  rw [E.inl_conjAct_comm]
  change E.inl n * E.inl m * (E.inl n)⁻¹ = E.inl m
  rw [← map_mul, ← map_inv, ← map_mul]
  simp [mul_comm]

/-- The actual quotient action, descended from conjugation in the given extension. -/
def action : S →* MulAut N :=
  E.rightHom.liftOfSurjective E.rightHom_surjective ⟨E.conjAct, conj_kernel E⟩

private theorem action_proj (y : Q) : action E (E.rightHom y) = E.conjAct y :=
  MonoidHom.liftOfRightInverse_comp_apply ..

private theorem inl_action (y : Q) (n : N) :
    E.inl (action E (E.rightHom y) n) = y * E.inl n * y⁻¹ := by
  rw [action_proj, E.inl_conjAct_comm]

/-- Integral coefficients with the actual, potentially nontrivial quotient action. -/
def coefficients : Rep ℤ S :=
  letI := MulDistribMulAction.compHom N (action E)
  Rep.ofMulDistribMulAction S N

/-- Automorphisms of the actual middle group fixing both endpoints pointwise. -/
def automorphisms : Subgroup (MulAut Q) where
  carrier := {a | (∀ n, a (E.inl n) = E.inl n) ∧ ∀ y, E.rightHom (a y) = E.rightHom y}
  one_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩
    exact ⟨fun n => by change a (b (E.inl n)) = _; rw [hb, ha],
      fun y => by change E.rightHom (a (b y)) = _; rw [hpa, hpb]⟩
  inv_mem' := by
    rintro a ⟨ha, hpa⟩
    constructor
    · intro n
      apply a.injective
      simpa using (ha n).symm
    · intro y
      simpa using (hpa (a⁻¹ y)).symm

private def rawDefect (a : automorphisms E) (y : Q) : N :=
  Classical.choose (show a.val y * y⁻¹ ∈ E.inl.range from by
    rw [E.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp [a.property.2 y])

private theorem raw_spec (a : automorphisms E) (y : Q) :
    E.inl (rawDefect E a y) = a.val y * y⁻¹ :=
  Classical.choose_spec (show a.val y * y⁻¹ ∈ E.inl.range from by
    rw [E.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp [a.property.2 y])

private theorem raw_apply (a : automorphisms E) (y : Q) :
    a.val y = E.inl (rawDefect E a y) * y := by rw [raw_spec]; group

private theorem raw_lift_independent (a : automorphisms E) (x y : Q)
    (h : E.rightHom x = E.rightHom y) : rawDefect E a x = rawDefect E a y := by
  obtain ⟨n, hn⟩ : x * y⁻¹ ∈ E.inl.range := by
    rw [E.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp [h]
  have hx : x = E.inl n * y := by rw [hn]; group
  apply E.inl_injective
  rw [hx, raw_spec, map_mul, a.property.1, raw_apply E a y]
  have hc : E.inl n * E.inl (rawDefect E a y) =
      E.inl (rawDefect E a y) * E.inl n := by rw [← map_mul, ← map_mul, mul_comm]
  rw [← mul_assoc, hc]
  group

/-- The defect of an automorphism, evaluated on any chosen lift. -/
def defect (a : automorphisms E) : S → N := fun s => rawDefect E a (E.surjInvRightHom s)

private theorem defect_spec (a : automorphisms E) (y : Q) :
    E.inl (defect E a (E.rightHom y)) = a.val y * y⁻¹ := by
  unfold defect
  rw [raw_lift_independent E a _ y (E.surjInvRightHom.rightInverse_rightHom _), raw_spec]

private theorem defect_cocycle (a : automorphisms E) (s t : S) :
    defect E a (s * t) = action E s (defect E a t) * defect E a s := by
  obtain ⟨x, rfl⟩ := E.rightHom_surjective s
  obtain ⟨y, rfl⟩ := E.rightHom_surjective t
  apply E.inl_injective
  rw [map_mul, inl_action, ← map_mul E.rightHom, defect_spec, map_mul,
    defect_spec, defect_spec]
  have hc : E.inl (action E (E.rightHom x) (defect E a (E.rightHom y))) *
      E.inl (defect E a (E.rightHom x)) =
      E.inl (defect E a (E.rightHom x)) *
      E.inl (action E (E.rightHom x) (defect E a (E.rightHom y))) := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [inl_action, defect_spec, defect_spec] at hc
  calc
    _ = (a.val x * x⁻¹) * (x * (a.val y * y⁻¹) * x⁻¹) := by group
    _ = _ := hc.symm

/-- Defects as pinned Mathlib one-cocycles. -/
def cocycle (a : automorphisms E) : cocycles₁ (coefficients E) :=
  ⟨Additive.ofMul ∘ defect E a, (mem_cocycles₁_iff _).2 (defect_cocycle E a)⟩

private theorem twist_map_mul (d : cocycles₁ (coefficients E)) (x y : Q) :
    E.inl (d (E.rightHom (x * y))).toMul * (x * y) =
      (E.inl (d (E.rightHom x)).toMul * x) * (E.inl (d (E.rightHom y)).toMul * y) := by
  have hd := (mem_cocycles₁_iff _).1 d.property (E.rightHom x) (E.rightHom y)
  change (d (E.rightHom x * E.rightHom y)).toMul =
    action E (E.rightHom x) (d (E.rightHom y)).toMul * (d (E.rightHom x)).toMul at hd
  rw [map_mul E.rightHom, hd, mul_comm (action E _ _), map_mul, inl_action]
  group

/-- A cocycle twists the given middle group, without a group section. -/
def twist (d : cocycles₁ (coefficients E)) : automorphisms E := by
  let f : Q →* Q := {
    toFun := fun y => E.inl (d (E.rightHom y)).toMul * y
    map_one' := by simp
    map_mul' := twist_map_mul E d }
  let e : E.Equiv E := GroupExtension.Equiv.ofMonoidHom f
    (by ext n; simp [f]) (by ext y; simp [f])
  exact ⟨e.toMulEquiv, e.map_inl, e.rightHom_map⟩

end D5.S3.HomologicalAlgebra.AbelianExtensionH1
