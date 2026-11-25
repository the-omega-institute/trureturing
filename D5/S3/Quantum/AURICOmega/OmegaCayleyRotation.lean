/- GID: D5/S3/Quantum/AURICOmega/OmegaCayleyRotation
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaCayleyRotation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact three-dimensional rational Cayley and adjoint rotations and heap recurrence. -/

module
prelude
public import OmegaMath.Geometry.Cayley3D

namespace D5.S3.Quantum.AURICOmega.OmegaCayleyRotation

open Omega Omega.Geometry.Cayley3D

/-- The normalized adjoint action preserves the rational dot product. -/
public theorem ad_dot (p : Quaternion) (hp : p.Nonzero) (u v : RatVec3) :
    IntRatio.Equivalent ((Ad p u).dot3 (Ad p v)) (u.dot3 v) :=
  Omega.Geometry.Cayley3D.ad_dot p hp u v

/-- Every nonzero signed scale on the quaternion gives the same adjoint action. -/
public theorem ad_scale (p : Quaternion) (hp : p.Nonzero) (k : Int) (hk : Not (Eq k Int.zero))
    (v : RatVec3) : RatVec3.Equiv (Ad (Quaternion.scale k p) v) (Ad p v) :=
  Omega.Geometry.Cayley3D.ad_scale p hp k hk v

/-- Hamilton multiplication composes the two adjoint actions. -/
public theorem ad_hom (p q : Quaternion) (hp : p.Nonzero) (hq : q.Nonzero) (v : RatVec3) :
    RatVec3.Equiv (Ad (p.mul q) v) (Ad p (Ad q v)) :=
  Omega.Geometry.Cayley3D.ad_hom p q hp hq v

/-- The forward Cayley matrix satisfies the denominator-cleared equation. -/
public theorem cayley_identity (s : RatVec3) :
    RatMat3.Equiv ((skewMinus s).mul (Cayley s)) (skewPlus s) :=
  Omega.Geometry.Cayley3D.cayley_identity s

/-- The transpose of the Cayley matrix is a left inverse. -/
public theorem cayley_orthogonal (s : RatVec3) :
    RatMat3.Equiv ((Cayley s).transpose.mul (Cayley s)) RatMat3.one :=
  Omega.Geometry.Cayley3D.cayley_orthogonal s

/-- The rational Cayley determinant is one. -/
public theorem cayley_det (s : RatVec3) : IntRatio.Equivalent (Cayley s).det (IntRatio.ofInt Int.one) :=
  Omega.Geometry.Cayley3D.cayley_det s

/-- Any number of Cayley steps preserves the exact rational squared norm. -/
public theorem cayley_iterate_norm (s v : RatVec3) (n : Nat) :
    IntRatio.Equivalent ((cayleyIterate s v n).dot3 (cayleyIterate s v n)) (v.dot3 v) :=
  Omega.Geometry.Cayley3D.cayley_iterate_norm s v n

/-- The signed spinor heap recurrence has exact rational squared norm one at every beat. -/
public theorem heap_norm_preserved (a b : PythSpinor) (n : Nat) :
    IntRatio.Equivalent (spinorNormSq (heapAt a b n)) (IntRatio.ofInt Int.one) :=
  Omega.Geometry.Cayley3D.heap_norm_preserved a b n

end D5.S3.Quantum.AURICOmega.OmegaCayleyRotation
