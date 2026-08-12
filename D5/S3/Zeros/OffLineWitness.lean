/- GID: D5/S3/Zeros/OffLineWitness
   generality: G
   mirror-B: D5/B/S3/Zeros/OffLineWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A closed off-line zero refutes the universal midline claim. -/

import Mathlib.Data.Complex.Basic

namespace D5.S3.Zeros.OffLineWitness

/-- One closed zero away from a proposed midline refutes the claim that every closed zero
lies on that line. -/
theorem closed_zero_midline_refutation (isZero closedAt : Complex → Prop)
    (midline : Real) (rho : Complex) (hZero : isZero rho) (hClosed : closedAt rho)
    (hOffLine : rho.re ≠ midline) :
    ¬∀ s, isZero s → closedAt s → s.re = midline := by
  intro hAll
  exact hOffLine (hAll rho hZero hClosed)

/-- The hypotheses and refutation are jointly inhabited by a concrete off-line zero model. -/
example : ¬∀ s : Complex, s = 0 → True → s.re = 1 :=
  closed_zero_midline_refutation
    (fun s => s = 0) (fun _ => True) 1 0 rfl trivial (by norm_num)

end D5.S3.Zeros.OffLineWitness
