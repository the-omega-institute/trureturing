/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalCachedGlobalReplay
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalCachedGlobalReplay
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: none
   digest: Fuel-prefix validity restricts transitions to actual unknown coordinates and preserves every original global branch and score margin. -/

/- Prepared final original-domain consumer, not yet kernel checked.
The complete original DAG replaces the older candidate by independent name.
No acceptance proof is asserted here: every reached suffix receipt and the
complete prefix still have to be checked before the unconditional result.
The actual initial/step/lower path and original F1/F2/scale are retained. -/
/- Prepared source, not compiled. Concrete local mirror and transition
acceptance is imported only from complete kernel receipts. The single remaining
globalAccepted proposition is the complete actual original-DAG replay, with the
same F1/F2, scale 6987435, exact contexts and all four branches. This module does
not assume a producer's global minimum or claim its uncomputed acceptance. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalDAGData
import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalCachedGlobalReplay
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
open D5.S3.Quantum.Entanglement.EJMInflationScore

/-- A depth prefix leaves every future global coordinate unknown. This is
proved along the actual fuel sequence, not guessed from shared branch shapes. -/
def Prefix (fuel : ℕ) (p : Partial (Fin 20) (Fin 4)) : Prop :=
  fuel ≤ 21 ∧ ∀ g, 21 - fuel ≤ g.val → p g = none

def Valid (fuel : ℕ) (cache : Cache) (p : Partial (Fin 20) (Fin 4)) : Prop :=
  Prefix fuel p ∧ AssociatedCache cache p

theorem initial_valid : Valid 21 initial (fun _ => none) := by
  refine ⟨⟨by decide, ?_⟩, initial_associated⟩
  intro g _
  rfl

private theorem split_coordinate (fuel : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size)
    (i : Fin 20) (children : Fin 4 → Fin EJMOriginalGlobalDAGData.Size)
    (split : EJMOriginalGlobalDAGData.nodes (fuel + 1) index = .split i children) :
    i.val = (21 - (fuel + 1)) % 20 := by
  unfold EJMOriginalGlobalDAGData.nodes at split
  dsimp only at split
  split_ifs at split with bound symmetry coordinate <;> cases split
  simpa only [Nat.mod_mod] using congrArg (fun x : ℕ => x % 20) coordinate

/-- Fuel zero rejects, so a successful split with remaining child fuel uses
the exact next unknown global coordinate. No known-coordinate table is needed. -/
theorem step_valid (fuel : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size) (cache : Cache)
    (p : Partial (Fin 20) (Fin 4)) (i : Fin 20)
    (children : Fin 4 → Fin EJMOriginalGlobalDAGData.Size)
    (split : EJMOriginalGlobalDAGData.nodes (fuel + 1) index = .split i children)
    (positive : 0 < fuel) (valid : Valid (fuel + 1) cache p) (a : Fin 4) :
    Valid fuel (step cache i a) (Function.update p i (some a)) := by
  have hlt : 21 - (fuel + 1) < 20 := by
    have h := valid.1.1
    omega
  have coordinate : i.val = 21 - (fuel + 1) := by
    rw [split_coordinate fuel index i children split, Nat.mod_eq_of_lt hlt]
  have unknown : p i = none := valid.1.2 i (by rw [coordinate])
  constructor
  · constructor
    · have h := valid.1.1
      omega
    · intro g future
      have different : g ≠ i := by
        intro same
        have hsame := congrArg Fin.val same
        have h := valid.1.1
        omega
      rw [Function.update_of_ne different]
      apply valid.1.2 g
      have h := valid.1.1
      omega
  · exact step_associated cache p valid.2 i a unknown

theorem valid_lower_le_score (fuel : ℕ) (cache : Cache) (p : Partial (Fin 20) (Fin 4))
    (e : Event (Fin 20) (Fin 4)) (valid : Valid fuel cache p) (hp : Compatible p e) :
    lower cache ≤ score F1 F2 e :=
  associated_lower_le_score cache p e valid.2 hp

def globalAccepted : Prop :=
  D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMOriginalGlobalDAGData.nodes
    step lower EJMGlobalScoreSymmetry.dominates scale 21 EJMOriginalGlobalDAGData.root
    initial (fun _ => none) = true

theorem accepted_score_lower_bound (accepted : globalAccepted) :
    ∀ e : Event (Fin 20) (Fin 4), scale ≤ score F1 F2 e := by
  exact D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_global_lower_bound
    (score F1 F2) FiniteLexSymmetry.rank EJMGlobalScoreSymmetry.act EJMOriginalGlobalDAGData.nodes
    step lower EJMGlobalScoreSymmetry.dominates scale Valid valid_lower_le_score
    step_valid EJMGlobalScoreSymmetry.actual_score_invariant
    EJMGlobalScoreSymmetry.dominates_rank_lt 21 EJMOriginalGlobalDAGData.root initial
    initial_valid accepted

/-- A complete prefix and separately earned actual suffix receipts prove the
same original bound. This is conditional until every reached frontier receipt
and the actual prefix check have been checked by the kernel. -/
theorem accepted_prefix_score_lower_bound
    (frontier : ℕ → Fin EJMOriginalGlobalDAGData.Size → Cache →
      Partial (Fin 20) (Fin 4) → Bool)
    (suffixes : ∀ fuel index cache p, frontier fuel index cache p = true →
      D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMOriginalGlobalDAGData.nodes
        step lower EJMGlobalScoreSymmetry.dominates scale fuel index cache p = true)
    (depth : ℕ)
    (accepted : D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checkPrefix
      EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates scale
      frontier depth 21 EJMOriginalGlobalDAGData.root initial (fun _ => none) = true) :
    ∀ e : Event (Fin 20) (Fin 4), scale ≤ score F1 F2 e := by
  apply accepted_score_lower_bound
  exact D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_prefix_and_frontier
    EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates scale
    frontier suffixes depth 21 EJMOriginalGlobalDAGData.root initial (fun _ => none) accepted

theorem accepted_score_positive (accepted : globalAccepted) :
    ∀ e : Event (Fin 20) (Fin 4), 1 ≤ score F1 F2 e := by
  intro e
  exact (by decide : (1 : ℤ) ≤ scale).trans (accepted_score_lower_bound accepted e)

theorem accepted_excludes_triangle_local (accepted : globalAccepted) :
    ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
      ejmDistribution :=
  positive_score_excludes_triangle_local F1 F2 (accepted_score_positive accepted)

#print axioms step_valid
#print axioms valid_lower_le_score
#print axioms accepted_score_lower_bound
#print axioms accepted_prefix_score_lower_bound
#print axioms accepted_excludes_triangle_local

end D5.S3.Quantum.Entanglement.EJM.EJMOriginalCachedGlobalReplay
