/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor28
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor28
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor28.bound
   digest: An original triangle or singleton factor is bounded on the exact cut prefix. -/

/- Source only, uncompiled. Original cut1088: depth13/code17540/index42672.
Reuse the exact factor28 table from cut1137. A checked equality of the actual
Singleton12 prefix projections and an explicit event completion transport
its public bound; no equality of arbitrary caches or helper-ID premise is used.
The complete cut root consumes this factor with the other31 original factors. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Factor28

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor28
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMInflationScore (lhsSingleton singletonTail singletonBlock)
open EJMCertificateData (F2)
abbrev Assignment := Fin 20 → Fin 4

private def canonicalEvent (e : Assignment) : Assignment :=
  fun g => (prefixPartial 13 17589 g).getD (e g)

private theorem canonical_compatible (e : Assignment) :
    Compatible (prefixPartial 13 17589) (canonicalEvent e) := by
  intro g a ha
  change (prefixPartial 13 17589 g).getD (e g) = a
  rw [ha]
  rfl

private theorem projected_prefix : ∀ j : Fin 9,
    prefixPartial 13 17589 (lhsSingleton 12 j) =
      prefixPartial 13 17540 (lhsSingleton 12 j) := by
  decide +kernel

private theorem same_projection (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) :
    canonicalEvent e ∘ lhsSingleton 12 = e ∘ lhsSingleton 12 := by
  funext j
  change (prefixPartial 13 17589 (lhsSingleton 12 j)).getD (e (lhsSingleton 12 j)) =
    e (lhsSingleton 12 j)
  rw [projected_prefix]
  cases assigned : prefixPartial 13 17540 (lhsSingleton 12 j) with
  | none => rfl
  | some a =>
      change a = e (lhsSingleton 12 j)
      exact (hp (lhsSingleton 12 j) a assigned).symm

private theorem same_score (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) :
    singletonBlock F2 12 (canonicalEvent e) = singletonBlock F2 12 e := by
  have projected := same_projection e hp
  have tail : canonicalEvent e ∘ singletonTail 12 = e ∘ singletonTail 12 := by
    funext j
    exact congrFun projected (Fin.natAdd 1 j)
  unfold singletonBlock
  rw [projected, tail]

private theorem future : prefixPartial 13 17589 13 = none ∧
    prefixPartial 13 17589 15 = none ∧ prefixPartial 13 17589 16 = none := by
  decide +kernel

private theorem canonical13 (e : Assignment) : canonicalEvent e 13 = e 13 := by
  change (prefixPartial 13 17589 13).getD (e 13) = e 13
  rw [future.1]
  rfl
private theorem canonical15 (e : Assignment) : canonicalEvent e 15 = e 15 := by
  change (prefixPartial 13 17589 15).getD (e 15) = e 15
  rw [future.2.1]
  rfl
private theorem canonical16 (e : Assignment) : canonicalEvent e 16 = e 16 := by
  change (prefixPartial 13 17589 16).getD (e 16) = e 16
  rw [future.2.2]
  rfl

def table (x13 x15 x16 : Fin 4) : ℤ :=
  PreparedEJMCompleteMiniCut01137Factor28.table x13 x15 x16
def lowerAt (e : Assignment) : ℤ := table (e 13) (e 15) (e 16)
def score (e : Assignment) : ℤ := singletonBlock F2 12 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have source := PreparedEJMCompleteMiniCut01137Factor28.bound (canonicalEvent e)
    (canonical_compatible e)
  change PreparedEJMCompleteMiniCut01137Factor28.table
    (canonicalEvent e 13) (canonicalEvent e 15) (canonicalEvent e 16) ≤
      singletonBlock F2 12 (canonicalEvent e) at source
  rw [canonical13, canonical15, canonical16, same_score e hp] at source
  exact source

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor28
