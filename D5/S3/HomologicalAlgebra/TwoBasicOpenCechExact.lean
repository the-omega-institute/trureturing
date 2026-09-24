/- GID: D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/TwoBasicOpenCechExact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Localization.Away.Basic, mathlib/module/Mathlib.Algebra.Homology.ShortComplex.ModuleCat]
   utility: none
   digest: A two-principal-open affine cover gives a short exact degree-zero Cech complex. -/

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic

/- Library-search audit (2026-09-24):
   * Every repository Lean file and every pinned Mathlib Lean file was searched
     for the full short exact sequence, its overlap-map surjectivity, and an
     equivalent two-Away common-denominator theorem. No exact supplier exists.
   * Mathlib provides the two canonical Away maps, injectivity and gluing for
     a unit-ideal basic-open cover, powered spans, fraction representatives,
     and the ModuleCat short-exactness constructor. These are reused directly.
   * Stacks Project tags 00EK and 01X9 state the classical localization and
     Cech exactness results. The concrete ModuleCat packaging and explicit
     two-denominator surjectivity proof below are repository-derived.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.HomologicalAlgebra.TwoBasicOpenCechExact

open CategoryTheory

variable {R : Type*} [CommRing R]

private noncomputable def diagonal (f g : R) :
    R →ₗ[R] Localization.Away f × Localization.Away g :=
  LinearMap.prod (Algebra.linearMap R (Localization.Away f))
    (Algebra.linearMap R (Localization.Away g))

private noncomputable def overlapDifference (f g : R) :
    (Localization.Away f × Localization.Away g) →ₗ[R] Localization.Away (f * g) where
  toFun p := IsLocalization.Away.awayToAwayRight f g p.1 -
    IsLocalization.Away.awayToAwayLeft g f p.2
  map_add' x y := by
    change IsLocalization.Away.awayToAwayRight f g (x.1 + y.1) -
        IsLocalization.Away.awayToAwayLeft g f (x.2 + y.2) = _
    rw [map_add, map_add]
    abel
  map_smul' r x := by
    rw [Algebra.smul_def, Algebra.smul_def, Prod.algebraMap_apply]
    change IsLocalization.Away.awayToAwayRight f g
          (algebraMap R (Localization.Away f) r * x.1) -
        IsLocalization.Away.awayToAwayLeft g f
          (algebraMap R (Localization.Away g) r * x.2) =
      algebraMap R (Localization.Away (f * g)) r *
        (IsLocalization.Away.awayToAwayRight f g x.1 -
          IsLocalization.Away.awayToAwayLeft g f x.2)
    rw [map_mul, map_mul, IsLocalization.Away.awayToAwayRight_eq,
      IsLocalization.Away.awayToAwayLeft_eq]
    ring

/-- The degree-zero Cech complex for the two principal opens `D(f)` and `D(g)`. -/
noncomputable def twoBasicOpenCechComplex (f g : R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (diagonal f g) (overlapDifference f g) (by
    apply LinearMap.ext
    intro r
    simp [diagonal, overlapDifference,
      IsLocalization.Away.awayToAwayRight_eq,
      IsLocalization.Away.awayToAwayLeft_eq])

private lemma diagonal_exact {f g : R} (hspan : Ideal.span {f, g} = ⊤) :
    Function.Exact (diagonal f g) (overlapDifference f g) := by
  intro p
  constructor
  · intro hp
    have hcompat :
        IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g)) f g p.1 =
          IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f * g)) g f p.2 := by
      change IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g)) f g p.1 -
          IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f * g)) g f p.2 = 0 at hp
      exact sub_eq_zero.mp hp
    by_cases hfg : f = g
    · subst g
      have hf : IsUnit f := by
        apply Ideal.span_singleton_eq_top.mp
        simpa using hspan
      let ef := IsLocalization.atUnit R (Localization.Away f) f hf
      let eff := IsLocalization.atUnit R (Localization.Away (f * f)) (f * f) (hf.mul hf)
      obtain ⟨r, hr⟩ := ef.surjective p.1
      obtain ⟨s, hs⟩ := ef.surjective p.2
      have hef (t : R) : ef t = algebraMap R (Localization.Away f) t := by
        simpa using ef.commutes t
      have heff (t : R) : eff t = algebraMap R (Localization.Away (f * f)) t := by
        simpa using eff.commutes t
      have hrs : r = s := eff.injective (by
        rw [heff, heff]
        calc
          algebraMap R (Localization.Away (f * f)) r =
              IsLocalization.Away.awayToAwayRight f f
                (algebraMap R (Localization.Away f) r) := by
            rw [IsLocalization.Away.awayToAwayRight_eq]
          _ = IsLocalization.Away.awayToAwayLeft f f
                (algebraMap R (Localization.Away f) s) := by
            rw [← hef r, ← hef s, hr, hs]
            exact hcompat
          _ = algebraMap R (Localization.Away (f * f)) s := by
            rw [IsLocalization.Away.awayToAwayLeft_eq])
      refine ⟨r, ?_⟩
      apply Prod.ext
      · change algebraMap R (Localization.Away f) r = p.1
        exact (hef r).symm.trans hr
      · change algebraMap R (Localization.Away f) r = p.2
        rw [hrs]
        exact (hef s).symm.trans hs
    · classical
      let sections : (a : ({f, g} : Set R)) → Localization.Away a.1 := fun a ↦
        if ha : a.1 = f then
          cast (congrArg Localization.Away ha.symm) p.1
        else
          have hor : a.1 = f ∨ a.1 = g := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using a.2
          have hag : a.1 = g := hor.resolve_left ha
          cast (congrArg Localization.Away hag.symm) p.2
      have hsection : ∀ a b : ({f, g} : Set R),
          IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.1 * b.1))
              a.1 b.1 (sections a) =
            IsLocalization.Away.awayToAwayLeft b.1 a.1 (sections b) := by
        intro a b
        have ha : a = (⟨f, by simp⟩ : ({f, g} : Set R)) ∨
            a = (⟨g, by simp⟩ : ({f, g} : Set R)) := by
          have hav : a.1 = f ∨ a.1 = g := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using a.2
          exact hav.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)
        have hb : b = (⟨f, by simp⟩ : ({f, g} : Set R)) ∨
            b = (⟨g, by simp⟩ : ({f, g} : Set R)) := by
          have hbv : b.1 = f ∨ b.1 = g := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using b.2
          exact hbv.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)
        rcases ha with rfl | rfl
        · rcases hb with rfl | rfl
          · simp only [sections, dif_pos rfl, cast_eq]
            congr 1
          · simpa [sections, hfg, Ne.symm hfg] using hcompat
        · rcases hb with rfl | rfl
          · simp only [sections, dif_neg (Ne.symm hfg), dif_pos rfl, cast_eq]
            let e : Localization.Away (f * g) ≃ₐ[R] Localization.Away (g * f) :=
              AlgEquiv.cast (mul_comm f g)
            have hleftMap :
                e.toAlgHom.toRingHom.comp
                    (IsLocalization.Away.awayToAwayLeft
                      (S := Localization.Away g) (P := Localization.Away (f * g)) g f) =
                  IsLocalization.Away.awayToAwayRight
                    (S := Localization.Away g) (P := Localization.Away (g * f)) g f := by
              apply IsLocalization.ringHom_ext (Submonoid.powers g)
              ext r
              simp only [RingHom.comp_apply,
                IsLocalization.Away.awayToAwayLeft_eq,
                IsLocalization.Away.awayToAwayRight_eq]
              change e (algebraMap R (Localization.Away (f * g)) r) = _
              exact e.commutes r
            have hrightMap :
                e.toAlgHom.toRingHom.comp
                    (IsLocalization.Away.awayToAwayRight
                      (S := Localization.Away f) (P := Localization.Away (f * g)) f g) =
                  IsLocalization.Away.awayToAwayLeft
                    (S := Localization.Away f) (P := Localization.Away (g * f)) f g := by
              apply IsLocalization.ringHom_ext (Submonoid.powers f)
              ext r
              simp only [RingHom.comp_apply,
                IsLocalization.Away.awayToAwayRight_eq,
                IsLocalization.Away.awayToAwayLeft_eq]
              change e (algebraMap R (Localization.Away (f * g)) r) = _
              exact e.commutes r
            calc
              IsLocalization.Away.awayToAwayRight g f p.2 =
                  e (IsLocalization.Away.awayToAwayLeft g f p.2) :=
                (DFunLike.congr_fun hleftMap p.2).symm
              _ = e (IsLocalization.Away.awayToAwayRight f g p.1) :=
                congrArg e hcompat.symm
              _ = IsLocalization.Away.awayToAwayLeft f g p.1 :=
                DFunLike.congr_fun hrightMap p.1
          · simp only [sections, dif_neg (Ne.symm hfg), cast_eq]
            congr 1
      obtain ⟨r, hr, _⟩ :=
        Localization.existsUnique_algebraMap_eq_of_span_eq_top
          ({f, g} : Set R) hspan sections hsection
      refine ⟨r, ?_⟩
      ext
      · simpa [diagonal, sections] using hr ⟨f, by simp⟩
      · simpa [diagonal, sections, hfg, Ne.symm hfg] using hr ⟨g, by simp⟩
  · rintro ⟨r, hr⟩
    calc
      overlapDifference f g p = overlapDifference f g (diagonal f g r) :=
        congrArg (overlapDifference f g) hr.symm
      _ = 0 := by
        simp [diagonal, overlapDifference,
          IsLocalization.Away.awayToAwayRight_eq,
          IsLocalization.Away.awayToAwayLeft_eq]

private lemma overlapDifference_surjective {f g : R}
    (hspan : Ideal.span {f, g} = ⊤) :
    Function.Surjective (overlapDifference f g) := by
  intro z
  obtain ⟨a, s, hs⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (f * g)) z
  rw [← hs]
  obtain ⟨n, hn⟩ := s.property
  have hpow : Ideal.span ({f ^ n, g ^ n} : Set R) = ⊤ := by
    have himage : (fun x : R ↦ x ^ n) '' ({f, g} : Set R) = {f ^ n, g ^ n} := by
      ext x
      simp [eq_comm]
    rw [← himage]
    exact Ideal.span_pow_eq_top ({f, g} : Set R) hspan n
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp ((Ideal.eq_top_iff_one _).mp hpow)
  let x : Localization.Away f :=
    IsLocalization.mk' _ (a * v) (Submonoid.pow f n)
  let y : Localization.Away g :=
    IsLocalization.mk' _ (-(a * u)) (Submonoid.pow g n)
  refine ⟨⟨x, y⟩, ?_⟩
  apply (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away (f * g))
    (f * g) n).mul_left_inj.mp
  have hx0 :
      x * algebraMap R (Localization.Away f) (f ^ n) =
        algebraMap R (Localization.Away f) (a * v) := by
    simpa [x] using
      (IsLocalization.mk'_spec (S := Localization.Away f)
        (a * v) (Submonoid.pow f n))
  have hx :
      IsLocalization.Away.awayToAwayRight f g x *
          algebraMap R (Localization.Away (f * g)) (f ^ n) =
        algebraMap R (Localization.Away (f * g)) (a * v) := by
    rw [← IsLocalization.Away.awayToAwayRight_eq
      (S := Localization.Away f) (P := Localization.Away (f * g)) f g (f ^ n),
      ← map_mul, hx0, IsLocalization.Away.awayToAwayRight_eq]
  have hy0 :
      y * algebraMap R (Localization.Away g) (g ^ n) =
        algebraMap R (Localization.Away g) (-(a * u)) := by
    simpa [y] using
      (IsLocalization.mk'_spec (S := Localization.Away g)
        (-(a * u)) (Submonoid.pow g n))
  have hy :
      IsLocalization.Away.awayToAwayLeft g f y *
          algebraMap R (Localization.Away (f * g)) (g ^ n) =
        algebraMap R (Localization.Away (f * g)) (-(a * u)) := by
    rw [← IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away g)
      g f (g ^ n), ← map_mul, hy0, IsLocalization.Away.awayToAwayLeft_eq]
  change (IsLocalization.Away.awayToAwayRight f g x -
      IsLocalization.Away.awayToAwayLeft g f y) *
        algebraMap R (Localization.Away (f * g)) (f * g) ^ n = _
  rw [← map_pow]
  rw [mul_pow, map_mul]
  calc
    (_ - _) *
          (algebraMap R (Localization.Away (f * g)) (f ^ n) *
            algebraMap R (Localization.Away (f * g)) (g ^ n)) =
        (IsLocalization.Away.awayToAwayRight f g x *
            algebraMap R (Localization.Away (f * g)) (f ^ n)) *
              algebraMap R (Localization.Away (f * g)) (g ^ n) -
          (IsLocalization.Away.awayToAwayLeft g f y *
            algebraMap R (Localization.Away (f * g)) (g ^ n)) *
              algebraMap R (Localization.Away (f * g)) (f ^ n) := by ring
    _ = algebraMap R (Localization.Away (f * g)) (a * v) *
          algebraMap R (Localization.Away (f * g)) (g ^ n) -
        algebraMap R (Localization.Away (f * g)) (-(a * u)) *
          algebraMap R (Localization.Away (f * g)) (f ^ n) := by rw [hx, hy]
    _ = algebraMap R (Localization.Away (f * g)) a := by
      rw [← map_mul, ← map_mul, ← map_sub]
      congr 1
      calc
        a * v * g ^ n - -(a * u) * f ^ n =
            a * (u * f ^ n + v * g ^ n) := by ring
        _ = a := by rw [huv, mul_one]
    _ = IsLocalization.mk' (Localization.Away (f * g)) a s *
          (algebraMap R (Localization.Away (f * g)) (f ^ n) *
            algebraMap R (Localization.Away (f * g)) (g ^ n)) := by
      rw [← map_mul, ← mul_pow]
      calc
        algebraMap R (Localization.Away (f * g)) a =
            IsLocalization.mk' (Localization.Away (f * g)) a s *
              algebraMap R (Localization.Away (f * g)) (s : R) :=
          (IsLocalization.mk'_spec (M := Submonoid.powers (f * g))
            (S := Localization.Away (f * g)) a s).symm
        _ = _ := by rw [← hn]

/-- If `D(f)` and `D(g)` cover `Spec R`, their degree-zero Cech complex is short exact. -/
theorem two_basic_open_cech_short_exact {f g : R}
    (hspan : Ideal.span {f, g} = ⊤) :
    (twoBasicOpenCechComplex f g).ShortExact := by
  unfold twoBasicOpenCechComplex
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (diagonal f g) (overlapDifference f g)
    exact diagonal_exact hspan
  · change Function.Injective (diagonal f g)
    intro x y hxy
    apply Localization.algebraMap_injective_of_span_eq_top ({f, g} : Set R) hspan
    funext a
    rcases a with ⟨a, ha⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  · change Function.Surjective (overlapDifference f g)
    exact overlapDifference_surjective hspan

#print axioms D5.S3.HomologicalAlgebra.TwoBasicOpenCechExact.two_basic_open_cech_short_exact

end D5.S3.HomologicalAlgebra.TwoBasicOpenCechExact
