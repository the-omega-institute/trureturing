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

variable {N Q : Type*} {S : Type} [CommGroup N] [Group Q] [Group S]
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
  have h := raw_lift_independent E a (E.surjInvRightHom (E.rightHom y)) y (by simp)
  exact (congrArg E.inl h).trans (raw_spec E a y)

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

private theorem twist_apply (d : cocycles₁ (coefficients E)) (y : Q) :
    (twist E d).val y = E.inl (d (E.rightHom y)).toMul * y := rfl

private theorem cocycle_twist (d : cocycles₁ (coefficients E)) : cocycle E (twist E d) = d := by
  apply cocycles₁_ext
  intro s
  obtain ⟨y, rfl⟩ := E.rightHom_surjective s
  change Additive.ofMul (defect E (twist E d) (E.rightHom y)) = d (E.rightHom y)
  apply Additive.toMul.injective
  apply E.inl_injective
  rw [defect_spec, twist_apply]
  group

private theorem twist_cocycle (a : automorphisms E) : twist E (cocycle E a) = a := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  change E.inl (defect E a (E.rightHom y)) * y = a.val y
  rw [defect_spec]
  group

private theorem cocycle_mul (a b : automorphisms E) : cocycle E (a * b) = cocycle E a + cocycle E b := by
  apply cocycles₁_ext
  intro s
  obtain ⟨y, rfl⟩ := E.rightHom_surjective s
  change Additive.ofMul (defect E (a * b) (E.rightHom y)) =
    Additive.ofMul (defect E a (E.rightHom y) * defect E b (E.rightHom y))
  congr 1
  apply E.inl_injective
  rw [map_mul, defect_spec, defect_spec, defect_spec]
  have hb : b.val y = E.inl (defect E b (E.rightHom y)) * y := by
    rw [defect_spec]; group
  change a.val (b.val y) * y⁻¹ = _
  rw [hb, map_mul, a.property.1]
  have hc := congrArg E.inl (mul_comm (defect E a (E.rightHom y)) (defect E b (E.rightHom y)))
  simp only [map_mul, defect_spec] at hc
  calc
    _ = E.inl (defect E b (E.rightHom y)) * (a.val y * y⁻¹) := by group
    _ = _ := by rw [defect_spec] at hc; exact hc.symm

/-- Automorphism composition is addition of actual general-action cocycles. -/
def defectEquiv : Additive (automorphisms E) ≃+ cocycles₁ (coefficients E) where
  toFun a := cocycle E a.toMul
  invFun d := Additive.ofMul (twist E d)
  left_inv a := twist_cocycle E a.toMul
  right_inv := cocycle_twist E
  map_add' a b := cocycle_mul E a.toMul b.toMul

/-- The cohomology class of the actual automorphism defect. -/
def classMap : Additive (automorphisms E) →+ H1 (coefficients E) :=
  ((H1π (coefficients E)).hom.toAddMonoidHom).comp (defectEquiv E).toAddMonoidHom

private theorem classMap_surjective : Function.Surjective (classMap E) := by
  intro c
  induction c using H1_induction_on with
  | h d => exact ⟨(defectEquiv E).symm d, by simp [classMap]⟩

private theorem classMap_zero_iff (a : Additive (automorphisms E)) :
    classMap E a = 0 ↔ ∃ b : N, ∀ y : Q,
      a.toMul.val y = E.inl b * y * (E.inl b)⁻¹ := by
  rw [show classMap E a = H1π (coefficients E) (cocycle E a.toMul) from rfl,
    H1π_eq_zero_iff]
  change (Additive.ofMul ∘ defect E a.toMul) ∈ coboundaries₁ (coefficients E) ↔ _
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.toMul⁻¹, ?_⟩
    intro y
    have h := congrFun hb (E.rightHom y)
    change Additive.ofMul (action E (E.rightHom y) b.toMul * b.toMul⁻¹) =
      Additive.ofMul (defect E a.toMul (E.rightHom y)) at h
    have hi := congrArg E.inl (Additive.ofMul.injective h)
    rw [map_mul, map_inv, inl_action, defect_spec] at hi
    rw [map_inv]
    calc
      _ = (a.toMul.val y * y⁻¹) * y := by group
      _ = _ := by rw [← hi]; group
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b⁻¹, ?_⟩
    funext s
    obtain ⟨y, rfl⟩ := E.rightHom_surjective s
    change Additive.ofMul (action E (E.rightHom y) b⁻¹ * (b⁻¹)⁻¹) =
      Additive.ofMul (defect E a.toMul (E.rightHom y))
    congr 1
    apply E.inl_injective
    rw [map_mul, inl_action, map_inv, inv_inv, defect_spec, hb]
    group

/-- Actual inner-kernel automorphisms, identified by the vanishing defect class. -/
def innerKernel : AddSubgroup (Additive (automorphisms E)) := (classMap E).ker

/-- Classification for arbitrary abelian extensions, including nonsplit extensions,
nontrivial quotient actions and the zero coefficient group. -/
theorem classification :
    (∀ (a : automorphisms E) (y : Q),
      E.inl ((defectEquiv E (Additive.ofMul a)) (E.rightHom y)).toMul = a.val y * y⁻¹) ∧
    (∀ (d : cocycles₁ (coefficients E)) (y : Q),
      ((defectEquiv E).symm d).toMul.val y = E.inl (d (E.rightHom y)).toMul * y) ∧
    (∀ a : Additive (automorphisms E), a ∈ innerKernel E ↔
      ∃ b : N, ∀ y : Q, a.toMul.val y = E.inl b * y * (E.inl b)⁻¹) ∧
    Nonempty ((Additive (automorphisms E) ⧸ innerKernel E) ≃+ H1 (coefficients E)) := by
  refine ⟨defect_spec E, twist_apply E, ?_, ?_⟩
  · intro a
    exact classMap_zero_iff E a
  · exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective (classMap E) (classMap_surjective E)⟩

end D5.S3.HomologicalAlgebra.AbelianExtensionH1
