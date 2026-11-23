/- GID: D5/S3/Quantum/AURICOmega/ProjectiveOverlapScaling
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/ProjectiveOverlapScaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive scaling preserves the Chapter 39 projective overlap. -/

module
prelude
public import OmegaMath.Projective

namespace D5.S3.Quantum.AURICOmega.ProjectiveOverlapScaling

/-- The Chapter 39 overlap is preserved by every positive natural scale, including
    when both coordinate magnitudes are zero and the overlap is undefined. -/
public theorem kappa_scale (p q k : Omega.Nat) :
    Omega.Ratio.Equivalent
      (Omega.Projective.kappa (p.mul k.succ) (q.mul k.succ))
      (Omega.Projective.kappa p q) :=
  Omega.Projective.kappa_scale p q k

end D5.S3.Quantum.AURICOmega.ProjectiveOverlapScaling
