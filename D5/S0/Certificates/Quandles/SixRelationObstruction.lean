/- GID: D5/S0/Certificates/Quandles/SixRelationObstruction
   generality: G
   mirror-B: D5/B/S0/Certificates/Quandles/SixRelationObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Monotone.Basic]
   utility: none
   digest: Six relations force collapse in a biordered idempotent magma. -/

/- proof_shape: content (strict-order cycle and order duality).
   admission_basis: escape-witness
   escape_witness: sixRelation_impossible_of_lt constructs h<c<d<e<h.
   Consumed by EightTwentyNonBiorderable.result on the whole presented carrier.
   This is a general order theorem, not finite or numerical computation. -/

import Mathlib.Order.Monotone.Basic

/-! Full presentation and order-obstruction sources; see the corresponding Scribe. -/


namespace D5.S0.Certificates.Quandles.SixRelationObstruction

variable {α : Type*} [LinearOrder α]

private theorem sixRelation_impossible_of_lt
    (op : α → α → α)
    (idem : ∀ x, op x x = x)
    (leftMono : ∀ z, StrictMono (op z))
    (rightMono : ∀ z, StrictMono (fun x => op x z))
    (a c d e f g h : α)
    (r_dg : op d g = e)
    (r_ge : op g e = h)
    (r_fd : op f d = g)
    (r_da : op d a = c)
    (r_ac : op a c = h)
    (r_fc : op f c = e)
    (hdg : d < g) : False := by
  have hde : d < e := by
    simpa only [idem, r_dg] using leftMono d hdg
  have heg : e < g := by
    simpa only [idem, r_dg] using rightMono g hdg
  have hcd : c < d := (leftMono f).lt_iff_lt.mp (by
    simpa only [r_fc, r_fd] using heg)
  have had : a < d := (leftMono d).lt_iff_lt.mp (by
    simpa only [r_da, idem] using hcd)
  have hac : a < c := by
    simpa only [idem, r_da] using rightMono a had
  have hhc : h < c := by
    simpa only [r_ac, idem] using rightMono c hac
  have heh : e < h := by
    simpa only [idem, r_ge] using rightMono e heg
  exact (lt_irrefl h) (hhc.trans (hcd.trans (hde.trans heh)))

/-- Six positive equations force equality in any linearly ordered idempotent
magma strictly increasing in both variables. No quandle axioms are needed. -/
theorem sixRelation_forces_eq
    (op : α → α → α)
    (idem : ∀ x, op x x = x)
    (leftMono : ∀ z, StrictMono (op z))
    (rightMono : ∀ z, StrictMono (fun x => op x z))
    (a c d e f g h : α)
    (r_dg : op d g = e)
    (r_ge : op g e = h)
    (r_fd : op f d = g)
    (r_da : op d a = c)
    (r_ac : op a c = h)
    (r_fc : op f c = e) : d = g := by
  rcases lt_trichotomy d g with hdg | heq | hgd
  · exact False.elim (sixRelation_impossible_of_lt op idem leftMono rightMono
      a c d e f g h r_dg r_ge r_fd r_da r_ac r_fc hdg)
  · exact heq
  · exact False.elim
      (sixRelation_impossible_of_lt (α := OrderDual α) op idem
        (by intro z x y hxy; exact leftMono z hxy)
        (by intro z x y hxy; exact rightMono z hxy)
        a c d e f g h r_dg r_ge r_fd r_da r_ac r_fc hgd)

end D5.S0.Certificates.Quandles.SixRelationObstruction
