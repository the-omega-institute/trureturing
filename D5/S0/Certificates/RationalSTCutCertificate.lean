/- GID: D5/S0/Certificates/RationalSTCutCertificate
   generality: G
   mirror-B: D5/B/S0/Certificates/RationalSTCutCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Certificates/LinearObjectiveDual]
   utility: kind=checker; basis=consumer=D5/S3/ConceptDynamics/PartialIdentification/BipartiteMediatorPricing.checked_pricing_isGreatest
   digest: Exact rational flow/cut certificates give a global minimum over every Boolean cut without enumerating those cuts or trusting a max-flow producer. -/

import D5.S0.Certificates.LinearObjectiveDual

/- Library audit (2026-09-06): reuse finite rational sums and the existing
   arithmetic tactic closure. Searches for maxFlow/minCut in the current repo
   and pinned Mathlib found no directly reusable finite certificate owner.
   This is the classical flow/cut weak-duality identity, not a new max-flow
   algorithm or a proof of polynomial-time discovery. Source and sink are
   represented by their incident flow vectors; all other nodes remain explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RationalSTCutCertificate

open scoped BigOperators

variable {Vertex : Type*} [Fintype Vertex]

/-- One-to-zero directed arcs cross the cut. A true vertex is on the source side. -/
def stCutValue (capacity : Vertex → Vertex → ℚ) (source sink : Vertex → ℚ)
    (side : Vertex → Bool) : ℚ :=
  (∑ i, if side i then sink i else source i) +
    ∑ i, ∑ j, if side i = true ∧ side j = false then capacity i j else 0

/-- Untrusted rational flows and a proposed cut, with no proof-valued fields. -/
structure STCutCertificate (Vertex : Type*) where
  internal : Vertex → Vertex → ℚ
  fromSource : Vertex → ℚ
  toSink : Vertex → ℚ
  side : Vertex → Bool

/-- Value of the proposed flow leaving the source. -/
def flowValue (certificate : STCutCertificate Vertex) : ℚ :=
  ∑ i, certificate.fromSource i

/-- Capacity, conservation and primal/dual contact are checked from the actual
finite input arrays. Internal cycles and simultaneous reverse arcs are allowed. -/
def ValidSTCutCertificate (capacity : Vertex → Vertex → ℚ)
    (source sink : Vertex → ℚ) (certificate : STCutCertificate Vertex) : Prop :=
  (∀ i j, 0 ≤ certificate.internal i j ∧ certificate.internal i j ≤ capacity i j) ∧
  (∀ i, 0 ≤ certificate.fromSource i ∧ certificate.fromSource i ≤ source i) ∧
  (∀ i, 0 ≤ certificate.toSink i ∧ certificate.toSink i ≤ sink i) ∧
  (∀ i, certificate.fromSource i + (∑ j, certificate.internal j i) =
    certificate.toSink i + ∑ j, certificate.internal i j) ∧
  stCutValue capacity source sink certificate.side = flowValue certificate

/-- Computable checker. A solver proposes the data; it has no trusted role. -/
def checkSTCutCertificate (capacity : Vertex → Vertex → ℚ)
    (source sink : Vertex → ℚ) (certificate : STCutCertificate Vertex) : Bool :=
  @decide (ValidSTCutCertificate capacity source sink certificate)
    (by unfold ValidSTCutCertificate; infer_instance)

theorem checkSTCutCertificate_eq_true_iff (capacity : Vertex → Vertex → ℚ)
    (source sink : Vertex → ℚ) (certificate : STCutCertificate Vertex) :
    checkSTCutCertificate capacity source sink certificate = true ↔
      ValidSTCutCertificate capacity source sink certificate := by
  simp only [checkSTCutCertificate, decide_eq_true_eq]

private def bit (b : Bool) : ℚ := if b then 1 else 0

private theorem internal_drift (flow : Vertex → Vertex → ℚ) (side : Vertex → Bool) :
    (∑ i, ∑ j, flow i j * (bit (side i) - bit (side j))) =
      ∑ i, ((∑ j, flow i j) - ∑ j, flow j i) * bit (side i) := by
  simp only [mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  have swap : (∑ i, ∑ j, flow i j * bit (side j)) =
      ∑ i, ∑ j, flow j i * bit (side i) := Finset.sum_comm
  rw [swap]

/-- Conservation telescopes over any Boolean cut, including cuts never visited
by the external producer. This is the global step of the certificate argument. -/
theorem flow_cut_accounting (certificate : STCutCertificate Vertex)
    (conservation : ∀ i, certificate.fromSource i + (∑ j, certificate.internal j i) =
      certificate.toSink i + ∑ j, certificate.internal i j) (side : Vertex → Bool) :
    flowValue certificate =
      (∑ i, if side i then certificate.toSink i else certificate.fromSource i) +
      ∑ i, ∑ j, certificate.internal i j *
        ((if side i then (1 : ℚ) else 0) - (if side j then 1 else 0)) := by
  change flowValue certificate =
    (∑ i, if side i then certificate.toSink i else certificate.fromSource i) +
      ∑ i, ∑ j, certificate.internal i j * (bit (side i) - bit (side j))
  rw [internal_drift, ← Finset.sum_add_distrib]
  unfold flowValue
  apply Finset.sum_congr rfl
  intro i _
  cases h : side i <;> simp [h, bit] <;> linarith [conservation i]

/-- Every feasible flow bounds every cut from below. No optimal flow premise. -/
theorem flowValue_le_every_cut (capacity : Vertex → Vertex → ℚ)
    (source sink : Vertex → ℚ) (certificate : STCutCertificate Vertex)
    (internal : ∀ i j, 0 ≤ certificate.internal i j ∧ certificate.internal i j ≤ capacity i j)
    (fromSource : ∀ i, certificate.fromSource i ≤ source i)
    (toSink : ∀ i, certificate.toSink i ≤ sink i)
    (conservation : ∀ i, certificate.fromSource i + (∑ j, certificate.internal j i) =
      certificate.toSink i + ∑ j, certificate.internal i j)
    (side : Vertex → Bool) : flowValue certificate ≤ stCutValue capacity source sink side := by
  rw [flow_cut_accounting certificate conservation side]
  unfold stCutValue
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    cases h : side i <;> simp [h]
    · exact fromSource i
    · exact toSink i
  · apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    cases hi : side i <;> cases hj : side j <;> simp [hi, hj] <;>
      linarith [(internal i j).1, (internal i j).2]

/-- A checked matching flow/cut pair certifies the true attained minimum over
all Boolean assignments, without enumerating the 2^|Vertex| cut family. -/
theorem checkSTCutCertificate_sound (capacity : Vertex → Vertex → ℚ)
    (source sink : Vertex → ℚ) (certificate : STCutCertificate Vertex)
    (accepted : checkSTCutCertificate capacity source sink certificate = true) :
    stCutValue capacity source sink certificate.side = flowValue certificate ∧
      ∀ side, flowValue certificate ≤ stCutValue capacity source sink side := by
  obtain ⟨internal, fromSource, toSink, conservation, contact⟩ :=
    (checkSTCutCertificate_eq_true_iff capacity source sink certificate).mp accepted
  exact ⟨contact, fun side => flowValue_le_every_cut capacity source sink certificate internal
    (fun i => (fromSource i).2) (fun i => (toSink i).2) conservation side⟩

#print axioms flow_cut_accounting
#print axioms flowValue_le_every_cut
#print axioms checkSTCutCertificate_sound

end D5.S0.Certificates.RationalSTCutCertificate
