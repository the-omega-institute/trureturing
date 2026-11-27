/- GID: D5/S3/Quantum/AURICOmega/OmegaShellExactness
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaShellExactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact classifications of the inputs for which the shell compression and triangle identities hold for every v. -/

module
prelude
public import OmegaMath.Algebra.Quaternion.Shell

namespace D5.S3.Quantum.AURICOmega.OmegaShellExactness

open Omega Omega.Quaternion

/-- For pure `p`, `q`, `a` and an integer `s`, the identity
`P_p P_q P_p v = 2 (s² + N(a) (p·q)) P_p v` holds for every `v` exactly when `s² = N(p) N(a)`, or
`s = 0` and `q = 0`. -/
public theorem shell_compress_iff_of_shell (s : Int) {p q a : Quaternion} (hp : p.IsPure)
    (hq : q.IsPure) (ha : a.IsPure) :
    let t := (s.mul s).add ((a.dot a).mul (p.dot q))
    Iff (∀ v : Quaternion,
        Eq (shell s p a (shell s q a (shell s p a v))) (scale (t.add t) (shell s p a v)))
      (Or (Eq (s.mul s) ((p.dot p).mul (a.dot a))) (And (Eq s Int.zero) (Eq q zero))) :=
  Quaternion.shell_compress_iff s hp hq ha

/-- For pure `p`, `q`, `r`, `a` and an integer `s`, the identity
`P_p P_q P_r z = 2 s (s² + N(a) (p·q + q·r + r·p)) z + 2 N(a) (p·(q r)) z a` with `z = P_p v` holds
for every `v` exactly when `s² = N(p) N(a)`, or `s = 0` and `q = 0` or `r = 0`, or `q = -r` and
`s² = N(r) N(a)`. -/
public theorem shell_triangle_iff_of_shell (s : Int) {p q r a : Quaternion} (hp : p.IsPure)
    (hq : q.IsPure) (hr : r.IsPure) (ha : a.IsPure) :
    let t := s.mul ((s.mul s).add ((a.dot a).mul (((p.dot q).add (q.dot r)).add (r.dot p))))
    let l := (a.dot a).mul (p.dot (q.mul r))
    Iff (∀ v : Quaternion,
        let z := shell s p a v
        Eq (shell s p a (shell s q a (shell s r a z)))
          ((scale (t.add t) z).add (scale (l.add l) (z.mul a))))
      (Or (Eq (s.mul s) ((p.dot p).mul (a.dot a)))
        (Or (And (Eq s Int.zero) (Or (Eq q zero) (Eq r zero)))
          (And (Eq q r.neg) (Eq (s.mul s) ((r.dot r).mul (a.dot a)))))) :=
  Quaternion.shell_triangle_iff s hp hq hr ha

end D5.S3.Quantum.AURICOmega.OmegaShellExactness
