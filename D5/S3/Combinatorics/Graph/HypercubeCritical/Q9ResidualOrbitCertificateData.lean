import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySix114555555Probe

/-! The shared mathematical verifier for the residual orbit certificates. -/

set_option autoImplicit false

open Finset
open D5.S3.Combinatorics.Graph.Hypercube

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open BalancedCriticalSpectrum (Q IsBalanced)
open private certificate_contradiction upper lower keyedTerms Q9OrbitRow.Valid Q9OrbitRow.SignAllowed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySix114555555Probe
attribute [local instance] Classical.propDecidable

structure ResidualOrbitCertificate where
  deficit : Fin 9 → ℤ
  rows : List (Q9OrbitRow × ℤ × ℤ)

def ResidualOrbitCertificate.Valid (c : ResidualOrbitCertificate) : Prop :=
  (∀ i, 0 ≤ c.deficit i ∧ c.deficit i ≤ 5) ∧
  (∀ t ∈ c.rows, 0 ≤ t.2.2 ∧ Q9OrbitRow.Valid c.deficit t.1 ∧ Q9OrbitRow.SignAllowed t.2.1 t.1) ∧
  upper c.deficit c.rows < lower (keyedTerms c.deficit c.rows)

private instance (c : ResidualOrbitCertificate) : Decidable c.Valid := by
  unfold ResidualOrbitCertificate.Valid
  infer_instance

theorem ResidualOrbitCertificate.exclude (c : ResidualOrbitCertificate) (hv : c.Valid)
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * c.deficit i = 33) : False :=
  certificate_contradiction c.deficit c.rows hv.1 hC hreg hb hhalf hv.2.1 hv.2.2

end D5.S3.Combinatorics.Graph.HypercubeCritical
