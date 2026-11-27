/- GID: D5/S3/Quantum/AURICOmega/OmegaTernionHeap
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaTernionHeap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer quaternion norms, projective ternion laws and signed spinor fidelity. -/

module
prelude
public import OmegaMath.Ternion.Heap

namespace D5.S3.Quantum.AURICOmega.OmegaTernionHeap

open Omega Omega.Ternion

/-- The squared norm of the Hamilton product is the product of squared norms. -/
public theorem normSq_mul (a b : Quaternion) :
    Eq (a.mul b).normSq (a.normSq.mul b.normSq) :=
  Quaternion.normSq_mul a b

/-- A repeated pair on the left cancels in the ray. -/
public theorem triad_left_absorption (x z : Quaternion) (hx : x.Nonzero) (hz : z.Nonzero) :
    RayEquiv (triad x x z) z :=
  Omega.Ternion.triad_left_absorption x z hx hz

/-- A repeated pair on the right cancels in the ray. -/
public theorem triad_right_absorption (x z : Quaternion) (hx : x.Nonzero) (hz : z.Nonzero) :
    RayEquiv (triad x z z) x :=
  Omega.Ternion.triad_right_absorption x z hx hz

/-- The two nestings of a nonzero quaternion heap product agree in the ray. -/
public theorem triad_assoc (x y z u v : Quaternion) (hx : x.Nonzero) (hy : y.Nonzero)
    (hz : z.Nonzero) (hu : u.Nonzero) (hv : v.Nonzero) :
    RayEquiv (triad (triad x y z) u v) (triad x y (triad z u v)) :=
  Omega.Ternion.triad_assoc x y z u v hx hy hz hu hv

/-- The sum of six squared minors is the exact complement of the squared dot product. -/
public theorem lagrange_identity (a b : Quaternion) :
    Eq ((Int.ofNat (a.normSq.mul b.normSq)).sub (Int.square (a.dot b))) (minorSquares a b) :=
  Omega.Ternion.lagrange_identity a b

/-- Projective Born fidelity between two nonzero inputs is at most one. -/
public theorem kappa_le_one (a b : Quaternion) (ha : a.Nonzero) (hb : b.Nonzero) :
    IntRatio.Le (kappa a b) (IntRatio.ofInt Int.one) :=
  Omega.Ternion.kappa_le_one a b ha hb

/-- Translating both inputs by the same heap arguments preserves projective fidelity. -/
public theorem kappa_heap_invariant (a b u v : Quaternion) (hu : u.Nonzero) (hv : v.Nonzero) :
    IntRatio.Equivalent (kappa (triad a u v) (triad b u v)) (kappa a b) :=
  Omega.Ternion.kappa_heap_invariant a b u v hu hv

/-- The homogeneous Cayley lift has squared numerator norm equal to squared radius. -/
public theorem lift_normSq (a b c d : Int) :
    Eq (PythSpinor.liftNum a b c d).normSq
      ((PythSpinor.liftRadius a b c d).mul (PythSpinor.liftRadius a b c d)) :=
  PythSpinor.lift_normSq a b c d

/-- The signed spinor kernel determines its projective kernel by a quadratic formula. -/
public theorem quadratic_kernel (p q : PythSpinor) :
    IntRatio.Equivalent (PythSpinor.kappa_proj p q)
      (let d := ((IntRatio.ofInt Int.two).mul (PythSpinor.kappa_spin p q)).sub (IntRatio.ofInt Int.one)
       d.mul d) :=
  PythSpinor.quadratic_kernel p q

end D5.S3.Quantum.AURICOmega.OmegaTernionHeap
