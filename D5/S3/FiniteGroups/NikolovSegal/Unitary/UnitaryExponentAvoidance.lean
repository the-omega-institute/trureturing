/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryExponentAvoidance
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryExponentAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryInvolutionField

namespace NikolovSegal.UnitaryField

/- A generator avoids every nonzero exponent strictly shorter than the group order.
This is simultaneous, and is stronger than a union bound over polynomial roots. -/
theorem cyclic_simultaneous_avoidance (G : Type*) [CommGroup G] [Finite G] [IsCyclic G] :
    ∃ u : G, ∀ e : ℤ, e ≠ 0 → e.natAbs < Nat.card G → u ^ e ≠ 1 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := G)
  refine ⟨u, fun e he hlt hpow => ?_⟩
  have hd := (orderOf_dvd_iff_zpow_eq_one).mpr hpow
  rw [orderOf_eq_card_of_forall_mem_zpowers hu, Int.natCast_dvd] at hd
  exact (Nat.le_of_dvd (Int.natAbs_pos.mpr he) hd).not_gt hlt

variable {F : Type*} [Field F] [Finite F]

theorem norm_one_simultaneous_avoidance (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    ∃ u : Fˣ, (u : F) * ι u = 1 ∧
      ∀ e : ℤ, e ≠ 0 → e.natAbs < Nat.card (fixedField ι) + 1 → u ^ e ≠ 1 := by
  obtain ⟨u, hu⟩ := cyclic_simultaneous_avoidance (normOne ι)
  refine ⟨u.val, (mem_normOne ι hinv hne u.val).mp u.property, ?_⟩
  intro e he hlt hp
  apply hu e he
  · simpa only [card_normOne ι hinv hne] using hlt
  · exact Subtype.ext hp

theorem full_unit_simultaneous_avoidance (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    ∃ u : Fˣ, ∀ e : ℤ, e ≠ 0 →
      e.natAbs < Nat.card (fixedField ι) ^ 2 - 1 → u ^ e ≠ 1 := by
  simpa only [Nat.card_units, card_field ι hinv hne] using
    cyclic_simultaneous_avoidance Fˣ

def involutionUnit (ι : F ≃+* F) : Fˣ →* Fˣ := Units.map ι.toMonoidHom

@[simp] theorem involutionUnit_val (ι : F ≃+* F) (u : Fˣ) :
    (involutionUnit ι u : F) = ι u := rfl

theorem involutionUnit_pow (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) (u : Fˣ) :
    involutionUnit ι u = u ^ Nat.card (fixedField ι) := by
  apply Units.ext
  exact involution_eq_pow ι hinv hne u

theorem norm_one_correction (ι : F ≃+* F) (hinv : Function.Involutive ι) (u : Fˣ) :
    ((u / involutionUnit ι u : Fˣ) : F) *
      ι ((u / involutionUnit ι u : Fˣ) : F) = 1 := by
  simp only [Units.val_div_eq_div_val, involutionUnit_val, map_div₀, hinv]
  field_simp
  exact (hinv u).symm

end NikolovSegal.UnitaryField
