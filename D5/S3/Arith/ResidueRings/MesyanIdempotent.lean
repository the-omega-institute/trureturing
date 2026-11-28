/- GID: D5/S3/Arith/ResidueRings/MesyanIdempotent
   generality: I
   mirror-B: D5/B/S3/Arith/ResidueRings/MesyanIdempotent
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Binary additive-submonoid product units for additively idempotent semirings. -/

import D5.S3.Arith.ResidueRings.MesyanCancellative

/-!
The additively idempotent case of Mesyan's Question 36. The binary product
of additive submonoids admits a unit exactly when multiplication on the
carrier has a two-sided identity, even if multiplication is nonassociative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Pointwise

namespace D5.S3.Arith.ResidueRings.MesyanIdempotent

open MesyanCancellative

variable {R : Type*} [NonUnitalNonAssocSemiring R]

private theorem eq_zero_or_self_of_mem_multiples (hAdd : ∀ a : R, a + a = a)
    {a x : R} (hx : x ∈ AddSubmonoid.multiples a) : x = 0 ∨ x = a := by
  have hsucc (n : ℕ) : (n + 1) • a = a := by
    induction n with
    | zero => exact one_nsmul a
    | succ n ih =>
      rw [AddMonoid.nsmul_succ, ih, hAdd a]
  obtain ⟨n, hn⟩ := hx
  cases n with
  | zero => exact Or.inl (hn.symm.trans (zero_nsmul a))
  | succ n => exact Or.inr (hn.symm.trans (hsucc n))

/-- Idempotent addition forces a unit for the binary product of additive
submonoids to come from a global two-sided multiplicative identity. -/
theorem product_unit_iff (hAdd : ∀ a : R, a + a = a) :
    (∃ E : AddSubmonoid R, ∀ M : AddSubmonoid R, E * M = M ∧ M * E = M) ↔
      ∃ u : R, ∀ x : R, u * x = x ∧ x * u = x := by
  classical
  let C := cyclicPreservingMultipliers R
  constructor
  · rintro ⟨E, hE⟩
    obtain ⟨_, hFix⟩ := (product_unit_iff_eq_cyclicPreservingMultipliers E).1 hE
    have hLeft {e : R} (he : e ∈ C) (a : R) : e * a = 0 ∨ e * a = a :=
      eq_zero_or_self_of_mem_multiples hAdd (he a).1
    have hRight {e : R} (he : e ∈ C) (a : R) : a * e = 0 ∨ a * e = a :=
      eq_zero_or_self_of_mem_multiples hAdd (he a).2
    have same_of_nonzero_prod {e f : R} (he : e ∈ C) (hf : f ∈ C)
        (hne : e * f ≠ 0) : e = f :=
      ((hRight hf e).resolve_left hne).symm.trans ((hLeft he f).resolve_left hne)
    have sq_eq_self {e : R} (he : e ∈ C) (hne : e ≠ 0) : e * e = e := by
      obtain ⟨l, hl, hle⟩ := (hFix e).1
      have hlne : l * e ≠ 0 := hle.symm ▸ hne
      simpa only [same_of_nonzero_prod hl he hlne] using hle
    have unique_ne_zero {e f : R} (he : e ∈ C) (hf : f ∈ C)
        (he0 : e ≠ 0) (hf0 : f ≠ 0) : e = f := by
      by_contra hne
      have hef : e * f = 0 := by
        by_contra hprod
        exact hne (same_of_nonzero_prod he hf hprod)
      have hfe : f * e = 0 := by
        by_contra hprod
        exact hne (same_of_nonzero_prod hf he hprod).symm
      have hse : (e + f) * e = e := by rw [add_mul, sq_eq_self he he0, hfe, add_zero]
      have hsf : (e + f) * f = f := by rw [add_mul, hef, sq_eq_self hf hf0, zero_add]
      have hs := C.add_mem he hf
      have hse' : e + f = e := same_of_nonzero_prod hs he (hse.symm ▸ he0)
      have hsf' : e + f = f := same_of_nonzero_prod hs hf (hsf.symm ▸ hf0)
      exact hne (hse'.symm.trans hsf')
    by_cases hZero : ∀ x : R, x = 0
    · exact ⟨0, fun x => ⟨(zero_mul x).trans (hZero x).symm,
        (mul_zero x).trans (hZero x).symm⟩⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hZero
      obtain ⟨u, hu, hua⟩ := (hFix a).1
      have hu0 : u ≠ 0 := by
        rintro rfl
        exact ha (hua.symm.trans (zero_mul a))
      refine ⟨u, fun x => ?_⟩
      by_cases hx : x = 0
      · subst x
        exact ⟨mul_zero u, zero_mul u⟩
      · obtain ⟨l, hl, hlx⟩ := (hFix x).1
        obtain ⟨r, hr, hxr⟩ := (hFix x).2
        have hl0 : l ≠ 0 := by
          rintro rfl
          exact hx (hlx.symm.trans (zero_mul x))
        have hr0 : r ≠ 0 := by
          rintro rfl
          exact hx (hxr.symm.trans (mul_zero x))
        exact ⟨unique_ne_zero hl hu hl0 hu0 ▸ hlx, unique_ne_zero hr hu hr0 hu0 ▸ hxr⟩
  · rintro ⟨u, hu⟩
    have huC : u ∈ C := fun x =>
      ⟨⟨1, (one_nsmul x).trans (hu x).1.symm⟩, ⟨1, (one_nsmul x).trans (hu x).2.symm⟩⟩
    exact ⟨C, (product_unit_iff_eq_cyclicPreservingMultipliers C).2
      ⟨rfl, fun x => ⟨⟨u, huC, (hu x).1⟩, ⟨u, huC, (hu x).2⟩⟩⟩⟩

end D5.S3.Arith.ResidueRings.MesyanIdempotent
