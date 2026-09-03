/- GID: D5/S3/Fourier/DeloneModelSetCertificate
   generality: G
   mirror-B: D5/B/S3/Fourier/DeloneModelSetCertificate
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Explicit separation and covering certificates promote a cut-and-project model set to Mathlib's bundled DeloneSet. -/

import D5.S3.Fourier.CutProjectScheme
import Mathlib.Analysis.AperiodicOrder.Delone.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.DeloneModelSetCertificate

open Metric
open scoped NNReal
open D5.S3.Fourier.CutProjectScheme

universe u v

/-- Explicit metric data certifying that one model set is uniformly discrete and relatively dense. -/
structure Certificate
    {Physical : Type u} {Internal : Type v}
    [MetricSpace Physical] [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) (window : Set Internal) where
  packingRadius : ℝ≥0
  packingRadius_pos : 0 < packingRadius
  isSeparated_packingRadius : IsSeparated packingRadius (scheme.modelSet window)
  coveringRadius : ℝ≥0
  coveringRadius_pos : 0 < coveringRadius
  isCover_coveringRadius :
    IsCover coveringRadius Set.univ (scheme.modelSet window)

namespace Certificate

/-- Package a metric certificate as Mathlib's canonical bundled Delone set. -/
def toDeloneSet
    {Physical : Type u} {Internal : Type v}
    [MetricSpace Physical] [AddGroup Physical] [AddGroup Internal]
    {scheme : Scheme Physical Internal} {window : Set Internal}
    (certificate : Certificate scheme window) : Delone.DeloneSet Physical where
  carrier := scheme.modelSet window
  packingRadius := certificate.packingRadius
  packingRadius_pos := certificate.packingRadius_pos
  isSeparated_packingRadius := certificate.isSeparated_packingRadius
  coveringRadius := certificate.coveringRadius
  coveringRadius_pos := certificate.coveringRadius_pos
  isCover_coveringRadius := certificate.isCover_coveringRadius

@[simp]
theorem toDeloneSet_carrier
    {Physical : Type u} {Internal : Type v}
    [MetricSpace Physical] [AddGroup Physical] [AddGroup Internal]
    {scheme : Scheme Physical Internal} {window : Set Internal}
    (certificate : Certificate scheme window) :
    certificate.toDeloneSet.carrier = scheme.modelSet window := rfl

/-- Recover an explicit model-set certificate from a bundled Delone set with the same carrier. -/
def ofDeloneSet
    {Physical : Type u} {Internal : Type v}
    [MetricSpace Physical] [AddGroup Physical] [AddGroup Internal]
    {scheme : Scheme Physical Internal} {window : Set Internal}
    (delone : Delone.DeloneSet Physical)
    (carrier_eq : delone.carrier = scheme.modelSet window) :
    Certificate scheme window where
  packingRadius := delone.packingRadius
  packingRadius_pos := delone.packingRadius_pos
  isSeparated_packingRadius := by
    simpa only [← carrier_eq] using delone.isSeparated_packingRadius
  coveringRadius := delone.coveringRadius
  coveringRadius_pos := delone.coveringRadius_pos
  isCover_coveringRadius := by
    simpa only [← carrier_eq] using delone.isCover_coveringRadius

end Certificate

/-- A metric certificate exists exactly when the model-set carrier supports a bundled Delone structure. -/
theorem certificate_nonempty_iff_deloneSet_exists
    {Physical : Type u} {Internal : Type v}
    [MetricSpace Physical] [AddGroup Physical] [AddGroup Internal]
    (scheme : Scheme Physical Internal) (window : Set Internal) :
    Nonempty (Certificate scheme window) ↔
      ∃ delone : Delone.DeloneSet Physical,
        delone.carrier = scheme.modelSet window := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toDeloneSet, rfl⟩
  · rintro ⟨delone, carrier_eq⟩
    exact ⟨Certificate.ofDeloneSet delone carrier_eq⟩

/-- Any explicit certificate promotes the selected carrier to a genuine Delone set. -/
theorem deloneSet_of_certificate
    {Physical : Type u} {Internal : Type v}
    [MetricSpace Physical] [AddGroup Physical] [AddGroup Internal]
    {scheme : Scheme Physical Internal} {window : Set Internal}
    (certificate : Certificate scheme window) :
    ∃ delone : Delone.DeloneSet Physical,
      delone.carrier = scheme.modelSet window :=
  ⟨certificate.toDeloneSet, rfl⟩

#print axioms certificate_nonempty_iff_deloneSet_exists
#print axioms deloneSet_of_certificate

end D5.S3.Fourier.DeloneModelSetCertificate
