/- GID: D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lie triple curvature, rational dual-chart denominators, and norm-five reduced words. -/

module
prelude
public import OmegaMath.Geometry.LieTriple
public import OmegaMath.Geometry.DualChartCayley

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

end D5.S3.Quantum.AURICOmega.OmegaLieTripleAndFreeGroup
