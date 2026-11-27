/- GID: D5/S3/Quantum/AURICOmega/OmegaShellProjection
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaShellProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shell compression and triangle identities for integer quaternion shell maps. -/

module
prelude
public import OmegaMath.Algebra.Quaternion.Shell

namespace D5.S3.Quantum.AURICOmega.OmegaShellProjection

open Omega Omega.Quaternion

/-- For pure `p`, `q`, `a`, an integer `s` and any `v`, the shell map `P v = s v + p v a`
satisfies `P_p P_q P_p v = 2 (s² + N(a) (p·q)) P_p v + (s² - N(p) N(a)) (q v a - s v)`. -/
public theorem shell_compress (s : Int) {p q a : Quaternion} (hp : p.IsPure) (hq : q.IsPure)
    (ha : a.IsPure) (v : Quaternion) :
    let t := (s.mul s).add ((a.dot a).mul (p.dot q))
    let δ := (s.mul s).sub ((p.dot p).mul (a.dot a))
    Eq (shell s p a (shell s q a (shell s p a v)))
      ((scale (t.add t) (shell s p a v)).add (scale δ (shell s.neg q a v))) :=
  Quaternion.shell_compress s hp hq ha v

/-- When `s² = N(p) N(a)`, the composition `P_p P_q P_p` is `2 (s² + N(a) (p·q))` times `P_p`. -/
public theorem shell_compress_of_eq (s : Int) {p q a : Quaternion} (hp : p.IsPure)
    (hq : q.IsPure) (ha : a.IsPure) (hs : Eq (s.mul s) ((p.dot p).mul (a.dot a)))
    (v : Quaternion) :
    let t := (s.mul s).add ((a.dot a).mul (p.dot q))
    Eq (shell s p a (shell s q a (shell s p a v))) (scale (t.add t) (shell s p a v)) :=
  Quaternion.shell_compress_of_eq s hp hq ha hs v

/-- For pure `p`, `q`, `r`, `a`, an integer `s`, any `v` and `z = P_p v`, the shell maps satisfy
`P_p P_q P_r z = 2 s (s² + N(a) (p·q + q·r + r·p)) z + 2 N(a) (p·(q r)) z a
  + (N(p) N(a) - s²) P_{-s,r,a} P_{-s,q,a} v`. -/
public theorem shell_triangle (s : Int) {p q r a : Quaternion} (hp : p.IsPure)
    (hq : q.IsPure) (hr : r.IsPure) (ha : a.IsPure) (v : Quaternion) :
    let z := shell s p a v
    let t := s.mul ((s.mul s).add ((a.dot a).mul (((p.dot q).add (q.dot r)).add (r.dot p))))
    let l := (a.dot a).mul (p.dot (q.mul r))
    let δ := ((p.dot p).mul (a.dot a)).sub (s.mul s)
    Eq (shell s p a (shell s q a (shell s r a z)))
      ((scale (t.add t) z).add ((scale (l.add l) (z.mul a)).add
        (scale δ (shell s.neg r a (shell s.neg q a v))))) :=
  Quaternion.shell_triangle s hp hq hr ha v

/-- When `s² = N(p) N(a)` and `z = P_p v`, the triangle composition is
`P_p P_q P_r z = 2 s (s² + N(a) (p·q + q·r + r·p)) z + 2 N(a) (p·(q r)) z a`. -/
public theorem shell_triangle_of_eq (s : Int) {p q r a : Quaternion} (hp : p.IsPure)
    (hq : q.IsPure) (hr : r.IsPure) (ha : a.IsPure)
    (hs : Eq (s.mul s) ((p.dot p).mul (a.dot a))) (v : Quaternion) :
    let z := shell s p a v
    let t := s.mul ((s.mul s).add ((a.dot a).mul (((p.dot q).add (q.dot r)).add (r.dot p))))
    let l := (a.dot a).mul (p.dot (q.mul r))
    Eq (shell s p a (shell s q a (shell s r a z)))
      ((scale (t.add t) z).add (scale (l.add l) (z.mul a))) :=
  Quaternion.shell_triangle_of_eq s hp hq hr ha hs v

end D5.S3.Quantum.AURICOmega.OmegaShellProjection
