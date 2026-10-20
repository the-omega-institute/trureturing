/- GID: D5/S3/Factorization/Mordell/LocalKummer
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/LocalKummer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational base change and local split-cubic Kummer fibers. -/

import D5.S3.Factorization.Mordell.RationalKummer
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Basic.Real.Basic

/-! Rational-to-field naturality for the actual elliptic point and squareclass maps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Mordell.LocalKummer

open WeierstrassCurve WeierstrassCurve.Affine

namespace F
export FieldKummer (Context curve root descentRep descentUnit coordinate kummer SquareClass unitClass
  CoveringRep Covering projectRep project covering_fiber)
end F

namespace R
export RationalKummer (curve root descentRep coordinate kummer SquareClass classOf)
end R

universe u
variable {K : Type u} [Field K] [CharZero K] [DecidableEq K]

private def pointCast {W W' : WeierstrassCurve.Affine K} (h : W = W') :
    W.Point →+ W'.Point := by
  subst W'
  exact AddMonoidHom.id _

private theorem pointCast_some {W W' : WeierstrassCurve.Affine K} (h : W = W')
    (x y : K) (hP : W.Nonsingular x y) :
    pointCast h (.some x y hP) = .some x y (h ▸ hP) := by
  subst W'
  rfl

private theorem curve_baseChange (D : ℚ) : (R.curve D)⁄K = F.curve (D : K) := by
  ext <;> simp [RationalKummer.curve,FieldKummer.curve,
    WeierstrassCurve.baseChange,WeierstrassCurve.map]

private theorem curve_self (D : ℚ) : R.curve D = (R.curve D)⁄ℚ := by
  ext <;> simp [WeierstrassCurve.baseChange,WeierstrassCurve.map]

/-- Actual Mathlib point base change, transported along the coefficient equalities. -/
noncomputable def rationalBaseChange (D : ℚ) :
    (R.curve D).Point →+ (F.curve (D : K)).Point :=
  (pointCast (curve_baseChange D)).comp
    ((Point.baseChange ℚ K (W' := R.curve D)).comp
      (pointCast (curve_self D)))

private theorem rationalBaseChange_some (D x y : ℚ) (hP : (R.curve D).Nonsingular x y) :
    ∃ hK : (F.curve (D : K)).Nonsingular (x : K) (y : K),
      rationalBaseChange D (.some x y hP) = .some (x : K) (y : K) hK := by
  have h₀ := curve_self D
  have h₁ := curve_baseChange (K := K) D
  have hP₀ : ((R.curve D)⁄ℚ).Nonsingular x y := h₀ ▸ hP
  have e₀ := pointCast_some h₀ x y hP
  have hPK := ((R.curve D).baseChange_nonsingular (Algebra.ofId ℚ K).injective x y).mpr hP₀
  have e₁ := pointCast_some h₁ (x : K) (y : K) hPK
  refine ⟨h₁ ▸ hPK,?_⟩
  dsimp only [rationalBaseChange,AddMonoidHom.comp_apply]
  rw [e₀]
  change pointCast h₁ (Point.map (Algebra.ofId ℚ K) (.some x y hP₀)) = _
  rw [Point.map_some]
  exact e₁

/-- Squares of rational units map to squares of field units. No square reflection is used. -/
private theorem squares_preserved (f : ℚ →+* K) :
    (powMonoidHom 2 : ℚˣ →* ℚˣ).range ≤
      ((powMonoidHom 2 : Kˣ →* Kˣ).range).comap (Units.map f.toMonoidHom) := by
  rintro a ⟨b,rfl⟩
  exact ⟨Units.map f.toMonoidHom b,by simp⟩

/-- The induced additive squareclass homomorphism. It need not be injective. -/
def classMap : Additive R.SquareClass →+ Additive (F.SquareClass K) :=
  MonoidHom.toAdditive (QuotientGroup.map _ _ (Units.map (Rat.castHom K).toMonoidHom)
    (squares_preserved (Rat.castHom K)))

private theorem rep_baseChange (D : ℚ) (P : (R.curve D).Point) (i : Fin 3) :
    F.descentRep (D : K) i (rationalBaseChange D P) = (R.descentRep D i P : K) := by
  have hr : (R.root D i : K) = F.root (D : K) i := by
    fin_cases i <;> simp [RationalKummer.root,FieldKummer.root]
  cases P with
  | zero =>
    have hz := (rationalBaseChange (K := K) D).map_zero
    change rationalBaseChange D Point.zero = Point.zero at hz
    rw [hz]
    simp [FieldKummer.descentRep,RationalKummer.descentRep]
  | some x y hP =>
    obtain ⟨hK,hmap⟩ := rationalBaseChange_some (K := K) D x y hP
    rw [hmap]
    dsimp only [FieldKummer.descentRep,RationalKummer.descentRep]
    by_cases hx : x = R.root D i
    · have hxK : (x : K) = F.root (D : K) i := by rw [hx,hr]
      rw [if_pos hxK,if_pos hx]
      change 3 * (F.root (D : K) i)^2 - 20*(D : K)*F.root (D : K) i - 75*(D : K)^2 =
        ((3*(R.root D i)^2 - 20*D*R.root D i - 75*D^2 : ℚ) : K)
      rw [←hr]
      push_cast
      rfl
    · have hxK : (x : K) ≠ F.root (D : K) i := by
        rw [←hr]
        exact fun h => hx (Rat.cast_injective h)
      rw [if_neg hxK,if_neg hx,←hr]
      push_cast
      rfl

private theorem coordinate_naturality (D : ℚ) (hD : D ≠ 0)
    (P : (R.curve D).Point) (i : Fin 3) :
    F.coordinate (D : K) (Rat.cast_ne_zero.mpr hD) i (rationalBaseChange D P) =
      classMap (R.coordinate D hD i P) := by
  have hR : R.coordinate D hD i P = F.coordinate (K := ℚ) D hD i P := by
    cases P <;> rfl
  rw [hR]
  change Additive.ofMul ((F.descentUnit (D : K) (Rat.cast_ne_zero.mpr hD) i
      (rationalBaseChange D P) : Kˣ) : F.SquareClass K) =
    Additive.ofMul (QuotientGroup.map _ _ (Units.map (Rat.castHom K).toMonoidHom)
      (squares_preserved (Rat.castHom K)) ((F.descentUnit (K := ℚ) D hD i P : ℚˣ) : R.SquareClass))
  rw [QuotientGroup.map_mk]
  apply congrArg Additive.ofMul
  apply congrArg (QuotientGroup.mk' _)
  apply Units.ext
  have hrep : F.descentRep (K := ℚ) D i P = R.descentRep D i P := by cases P <;> rfl
  change F.descentRep (D : K) i (rationalBaseChange D P) = (F.descentRep (K := ℚ) D i P : K)
  rw [hrep]
  exact rep_baseChange D P i

/-- The delivered rational Kummer map commutes with actual point base change and quotient maps. -/
theorem rational_naturality (C : F.Context.{u}) (D : ℚˣ)
    (P : (R.curve (D : ℚ)).Point) :
    F.kummer ((D : ℚ) : C.Carrier) (Rat.cast_ne_zero.mpr D.ne_zero) (rationalBaseChange (D : ℚ) P) =
      (classMap.prodMap classMap) (R.kummer (D : ℚ) D.ne_zero P) := by
  apply Prod.ext
  · exact coordinate_naturality (D : ℚ) D.ne_zero P 0
  · exact coordinate_naturality (D : ℚ) D.ne_zero P 1

end D5.S3.Factorization.Mordell.LocalKummer
