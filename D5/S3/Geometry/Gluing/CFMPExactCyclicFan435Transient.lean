import D5.S3.Geometry.Gluing.ActualLinkAffineFan

/-! Temporary exact applications for supplemental CFMP 122.3. -/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Set
open D5.S3.Geometry.Gluing.CyclicTriangleDisk

namespace CFMPExactCyclicFan435Transient

theorem prescribed_radial_homeomorphism (n : ℕ) (hn : 3 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∃ H : Fan n ≃ₜ Disk,
      ∀ x : Point n, (H (Quotient.mk (seamSetoid n) x)).val = radial x := by
  letI : NeZero n := ⟨by omega⟩
  exact ⟨homeomorphism,fun _ => rfl⟩

theorem common_apex (n : ℕ) (hn : 3 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ i j : Fin n, Quotient.mk (seamSetoid n) (apex i) =
      Quotient.mk (seamSetoid n) (apex j) := by
  letI : NeZero n := ⟨by omega⟩
  intro i j
  apply Quotient.sound
  apply (related_iff_normal_eq _ _).mpr
  simp [normal,radius,apex]

theorem open_apex_neighborhood (n : ℕ) (hn : 3 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∃ U : Set (Fan n), IsOpen U ∧
      Quotient.mk (seamSetoid n) (apex (0 : Fin n)) ∈ U ∧
      Nonempty (U ≃ₜ {z : ℂ // ‖z‖ < 1}) := by
  letI : NeZero n := ⟨by omega⟩
  let H : Fan n ≃ₜ Disk := homeomorphism
  let W : Set Disk := {z | ‖z.val‖ < 1}
  let U : Set (Fan n) := H ⁻¹' W
  have hW : IsOpen W :=
    isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  have hU : IsOpen U := hW.preimage H.continuous
  have ha : Quotient.mk (seamSetoid n) (apex (0 : Fin n)) ∈ U := by
    change ‖radial (apex (0 : Fin n))‖ < 1
    simp [radial,radius,apex]
  let e : U ≃ₜ W := H.subtype (fun _ => Iff.rfl)
  let k : W ≃ₜ {z : ℂ // ‖z‖ < 1} :=
    { toFun := fun z => ⟨z.val.val,z.property⟩
      invFun := fun z => ⟨⟨z.val,z.property.le⟩,z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun :=
        (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact ⟨U,hU,ha,⟨e.trans k⟩⟩

#print axioms open_apex_neighborhood
end CFMPExactCyclicFan435Transient
