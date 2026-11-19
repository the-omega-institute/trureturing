import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9DiameterCertificatesFirst
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9DiameterCertificatesSecond

/-! Surviving coordinate profiles after the distance-eight certificates. -/

set_option autoImplicit false

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private DegreeCertificate.deficit all_decide_sound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9DegreeCertificatesProbe
open private DiameterCertificate DiameterCertificate.degree DiameterCertificate.Valid
  no_support_with_diameter_certificate from D5.S3.Combinatorics.Graph.HypercubeCritical.Q9DiameterCertificateCore

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private def diameterCertificates : List DiameterCertificate :=
  diameterCertificates1 ++ diameterCertificates2 ++ diameterCertificates3 ++
    diameterCertificates4 ++ diameterCertificates5 ++ diameterCertificates6 ++ diameterCertificates7

private lemma diameterCertificates_valid :
    diameterCertificates.all (fun c => decide (DiameterCertificate.Valid c)) = true := by
  simp only [diameterCertificates, List.all_append, diameterCertificates1_valid,
    diameterCertificates2_valid, diameterCertificates3_valid, diameterCertificates4_valid,
    diameterCertificates5_valid, diameterCertificates6_valid, diameterCertificates7_valid,
    Bool.and_true]

/-- The coordinate profiles that survive the degree and distance-eight restrictions. -/
def sixtySixProfilesAfterDiameterCertificates : List (List ℤ) :=
  sixtySixProfilesAfterDiameterCertificate.filter (fun profile =>
    !(diameterCertificates.map (fun c => List.ofFn (DegreeCertificate.deficit (DiameterCertificate.degree c)))).contains
      profile)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- The kernel evaluates the profile filters and the 45 newly excluded profiles.
theorem sixtySixProfilesAfterDiameterCertificates_length :
    sixtySixProfilesAfterDiameterCertificates.length = 58 := by
  decide +kernel

/-- Every 66-point Huang-balanced cubic support normalizes to one of the
58 profiles that survive the degree and distance-eight certificates. -/
theorem q9_sixty_six_mem_profiles_after_diameter_certificates {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterDiameterCertificates := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_diameter_certificate hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  simp only [sixtySixProfilesAfterDiameterCertificates, List.mem_filter, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]
  refine ⟨hprofile, ?_⟩
  rintro ⟨c, hc, he⟩
  have hcert : DiameterCertificate.Valid c := all_decide_sound diameterCertificates_valid hc
  have hr : DegreeCertificate.deficit (DiameterCertificate.degree c) = r := List.ofFn_inj.mp he
  exact no_support_with_diameter_certificate c hcert hS hregS hbS (by
    simpa only [hr] using hhalf)

#print axioms q9_sixty_six_mem_profiles_after_diameter_certificates

end D5.S3.Combinatorics.Graph.HypercubeCritical
