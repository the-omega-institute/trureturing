/- GID: D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lie triple curvature, rational dual-chart denominators, and norm-five reduced words. -/

module
prelude
public import D5.S3.Geometry.LieTriple
public import D5.S3.Geometry.DualChartCayley
public import D5.S3.Fourier.HurwitzFreeGroup.Adjoint

namespace D5.S3.Quantum.AURICOmega.OmegaLieTripleAndFreeGroup

open Omega Omega.Geometry.LieTriple

/-- Exchanging the first two arguments negates the triple bracket. -/
public theorem lieTriple_antisymm (u v w : Vec3) :
    Eq (lieTriple u v w) (neg (lieTriple v u w)) :=
  Omega.Geometry.LieTriple.lieTriple_antisymm u v w

/-- The cyclic sum of the triple bracket vanishes. -/
public theorem lieTriple_jacobi (u v w : Vec3) :
    Eq (add (add (lieTriple u v w) (lieTriple v w u)) (lieTriple w u v)) zero :=
  Omega.Geometry.LieTriple.lieTriple_jacobi u v w

/-- Each pair of vectors acts by a derivation of the triple bracket. -/
public theorem lieTriple_derivation (x y u v w : Vec3) :
    Eq (lieTriple x y (lieTriple u v w))
      (add (add (lieTriple (lieTriple x y u) v w) (lieTriple u (lieTriple x y v) w))
        (lieTriple u v (lieTriple x y w))) :=
  Omega.Geometry.LieTriple.lieTriple_derivation x y u v w

/-- The positive curvature contraction equals the squared Gram area. -/
public theorem lieTriple_unit_sectional_curvature (u v : Vec3) :
    Eq ((lieTriple u v u).dot3 v) (gramAreaSq u v) :=
  Omega.Geometry.LieTriple.lieTriple_unit_sectional_curvature u v

/-- The contraction with the last two slots exchanged has the opposite sign. -/
public theorem lieTriple_sectional_curvature_reversed (u v : Vec3) :
    Eq ((lieTriple u v v).dot3 u) (gramAreaSq u v).neg :=
  Omega.Geometry.LieTriple.lieTriple_sectional_curvature_reversed u v

/-- The sectional curvature of every rational plane with nonzero Gram area is one. -/
public theorem lieTriple_sectional_ratio (u v : RatVec3)
    (h : Not (Eq (gramAreaSq u.num v.num) Int.zero)) :
    IntRatio.Equivalent
      ((rationalCurvatureNumerator u v).mul (rationalGramAreaSq u v).inv)
      (IntRatio.ofInt Int.one) :=
  Omega.Geometry.LieTriple.lieTriple_sectional_ratio u v h

open Omega.Geometry.DualChartCayley

/-- The normalized chart denominators sum to one. -/
public theorem dual_chart_denom_sum_one (u v : RatVec3) :
    IntRatio.Equivalent ((denomPlus u v).add (denomMinus u v)) (IntRatio.ofInt Int.one) :=
  Omega.Geometry.DualChartCayley.dual_chart_denom_sum_one u v

/-- At least one chart denominator is at least one half. -/
public theorem dual_chart_denom_ge_half (u v : RatVec3) :
    let half := IntRatio.fraction Int.one Nat.one
    Or (IntRatio.Le half (denomPlus u v)) (IntRatio.Le half (denomMinus u v)) :=
  Omega.Geometry.DualChartCayley.dual_chart_denom_ge_half u v

/-- The selected stereographic coordinates lie in the closed unit ball. -/
public theorem dual_chart_ball_containment (u v : RatVec3) :
    IntRatio.Le ((output u v).dot3 (output u v)) (IntRatio.ofInt Int.one) :=
  Omega.Geometry.DualChartCayley.dual_chart_ball_containment u v

/-- Both normalized denominators have the expanded MRP forms. -/
public theorem dual_chart_mrp_denominators (u v : RatVec3) :
    let r := (product u v).radiusPred
    And (IntRatio.Equivalent (denomPlus u v) (.fraction (mrpPlusNum u v) r))
      (IntRatio.Equivalent (denomMinus u v) (.fraction (mrpMinusNum u v) r)) :=
  Omega.Geometry.DualChartCayley.dual_chart_mrp_denominators u v

open Omega.Hurwitz.FreeGroup Omega.Geometry.Cayley3D

/-- The mod-five split image of every reduced word is nonzero. -/
public theorem reduced_word_split5_nonzero (w : Word) (hr : IsReduced w) :
    Eq (evalSplit5 w).isZero .false :=
  Omega.Hurwitz.FreeGroup.reduced_word_split5_nonzero w hr

/-- The squared norm is five to the length of the word. -/
public theorem reduced_word_normSq (w : Word) : Eq (evalQuat w).normSq (powFive w.length) :=
  Omega.Hurwitz.FreeGroup.reduced_word_normSq w

/-- Every reduced word has a quaternion coordinate indivisible by five. -/
public theorem reduced_word_not_div_five (w : Word) (hr : IsReduced w) :
    Not (AllDivisibleByFive (evalQuat w)) :=
  Omega.Hurwitz.FreeGroup.reduced_word_not_div_five w hr

/-- Every nonempty reduced word evaluates to a nonscalar quaternion. -/
public theorem reduced_word_non_scalar (w : Word) (hr : IsReduced w) (hn : Not (Eq w .nil)) :
    Not (IsScalar (evalQuat w)) :=
  Omega.Hurwitz.FreeGroup.reduced_word_non_scalar w hr hn

/-- Agreement of rational adjoint rotations on two coordinate axes identifies the reduced word. -/
public theorem reduced_words_adjoint_injective (u v : Word) (hu : IsReduced u) (hv : IsReduced v)
    (sameX : (Ad (evalQuat u) (RatVec3.ofInt axisX)).Equiv (Ad (evalQuat v) (RatVec3.ofInt axisX)))
    (sameY : (Ad (evalQuat u) (RatVec3.ofInt axisY)).Equiv (Ad (evalQuat v) (RatVec3.ofInt axisY))) :
    Eq u v :=
  Omega.Hurwitz.FreeGroup.reduced_words_adjoint_injective u v hu hv sameX sameY

end D5.S3.Quantum.AURICOmega.OmegaLieTripleAndFreeGroup
