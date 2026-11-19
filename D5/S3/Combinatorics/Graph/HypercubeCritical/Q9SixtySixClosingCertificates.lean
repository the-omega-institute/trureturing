import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates1
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates2
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates3
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates4
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates5
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates6
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates7
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates8
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates9
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySix004555555Probe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyExclusionProbe

/-! The candidate list is exhausted by orbit certificates for the remaining profiles. -/

set_option autoImplicit false

open Finset
open D5.S3.Combinatorics.Graph.Hypercube

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private residualOrbitCertificates1 residualOrbitCertificates1_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates1
open private residualOrbitCertificates2 residualOrbitCertificates2_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates2
open private residualOrbitCertificates3 residualOrbitCertificates3_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates3
open private residualOrbitCertificates4 residualOrbitCertificates4_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates4
open private residualOrbitCertificates5 residualOrbitCertificates5_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates5
open private residualOrbitCertificates6 residualOrbitCertificates6_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates6
open private residualOrbitCertificates7 residualOrbitCertificates7_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates7
open private residualOrbitCertificates8 residualOrbitCertificates8_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates8
open private residualOrbitCertificates9 residualOrbitCertificates9_valid from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ResidualOrbitCertificates9

private def residualOrbitCertificates : List ResidualOrbitCertificate :=
  residualOrbitCertificates1 ++
  residualOrbitCertificates2 ++
  residualOrbitCertificates3 ++
  residualOrbitCertificates4 ++
  residualOrbitCertificates5 ++
  residualOrbitCertificates6 ++
  residualOrbitCertificates7 ++
  residualOrbitCertificates8 ++
  residualOrbitCertificates9

private theorem residualOrbitCertificates_valid :
    ∀ c ∈ residualOrbitCertificates, c.Valid := by
  simp only [residualOrbitCertificates, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨residualOrbitCertificates1_valid, residualOrbitCertificates2_valid⟩,
    residualOrbitCertificates3_valid⟩, residualOrbitCertificates4_valid⟩,
    residualOrbitCertificates5_valid⟩, residualOrbitCertificates6_valid⟩,
    residualOrbitCertificates7_valid⟩, residualOrbitCertificates8_valid⟩,
    residualOrbitCertificates9_valid⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
-- Reduction first enumerates the normalized profiles and then checks coverage by the certificates.
private theorem residualOrbitCertificates_cover :
    ∀ p ∈ sixtySixProfilesAfterForcedEdgeCertificate,
      p ∈ residualOrbitCertificates.map (fun c => List.ofFn c.deficit) := by
  decide +kernel

/-- The nine-cube has no Huang-balanced induced cubic support with 66 vertices. -/
theorem q9_no_balanced_induced_cubic_sixty_six
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    False := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hp⟩ :=
    q9_sixty_six_mem_profiles_after_forced_edge_certificate hC hreg hb
  obtain ⟨c, hc, hr⟩ := List.mem_map.mp (residualOrbitCertificates_cover _ hp)
  have he := List.ofFn_inj.mp hr
  subst r
  exact c.exclude (residualOrbitCertificates_valid c hc) hS hregS hbS hhalf

#print axioms q9_no_balanced_induced_cubic_sixty_six

/-- Below order 72, a nonempty Huang-balanced induced cubic support of the
nine-cube has order 48 or 54. -/
theorem q9_balanced_induced_cubic_small_orders
    (C : Finset (Q 9)) (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    C.card = 48 ∨ C.card = 54 ∨ 72 ≤ C.card := by
  have hl := BalancedCubeLowerBound.forty_eight_le_card C hC hr hb
  have he := BalancedCriticalSpectrum.direction_edge_count (d := 3) C hr hb 0
  have h60 : C.card ≠ 60 := fun h => no_huang_balanced_cubic_sixty C h hr hb
  have h66 : C.card ≠ 66 := fun h => q9_no_balanced_induced_cubic_sixty_six h hr hb
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical
