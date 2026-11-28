/- GID: D5/S3/Quantum/AURICOmega/OmegaShellOrientedAxis
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaShellOrientedAxis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The oriented axis identity for the integer quaternion maps v ↦ (c v) a with pure c and a. -/

module
prelude
public import OmegaMath.Algebra.Quaternion.Shell

namespace D5.S3.Quantum.AURICOmega.OmegaShellOrientedAxis

open Omega Omega.Quaternion

/-- For pure `p`, `q`, `r`, `a`, any `x` and the maps `u_c v = (c v) a`, the three cyclic
compositions minus the three reverse ones equal `6 N(a) (p·(q r)) (x a)`. -/
public theorem oriented_axis_from_shell {p q r a : Quaternion} (hp : p.IsPure) (hq : q.IsPure)
    (hr : r.IsPure) (ha : a.IsPure) (x : Quaternion) :
    let u := fun c v : Quaternion => (c.mul v).mul a
    let l := (a.dot a).mul (p.dot (q.mul r))
    let t := (l.add l).add l
    Eq ((((u p (u q (u r x))).add (u q (u r (u p x)))).add (u r (u p (u q x)))).sub
        (((u p (u r (u q x))).add (u r (u q (u p x)))).add (u q (u p (u r x)))))
      (scale (t.add t) (x.mul a)) :=
  Quaternion.oriented_axis hp hq hr ha x

end D5.S3.Quantum.AURICOmega.OmegaShellOrientedAxis
