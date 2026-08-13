/- GID: D5/S3/AnalyticClosure/CofinalTailDiscipline
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/CofinalTailDiscipline
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cofinal finite windows and a vanishing certified tail budget close an exact reading. -/

import D5.S3.Analytic.TailClosure

open Filter

namespace D5.S3.AnalyticClosure.CofinalTailDiscipline

open D5.S3.Analytic.TailCertificate

/-- Cofinal finite windows cover every finite source set, while a certified tail budget
that vanishes along the window filter forces the readings to converge to the exact value. -/
theorem cofinal_windows_and_vanishing_budget_close {Atom Window : Type*}
    (family : CofinalWindowFamily Atom Window)
    (control : TailControl Window) (value : Real)
    (certificate : Certificate family control value)
    (windows : Filter Window)
    (budget_vanishes : Tendsto certificate.budget windows (nhds 0))
    (finite : Finset Atom) :
    (exists window, finite ⊆ family.contents window) ∧
      Tendsto certificate.reading windows (nhds value) := by
  exact ⟨family.cofinal finite,
    D5.S3.Analytic.TailClosure.vanishing_tail_budget_closes
      family control value certificate windows budget_vanishes⟩

end D5.S3.AnalyticClosure.CofinalTailDiscipline
