/- GID: D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reversing actual numbered paths computes chronological outgoing lifts on the original graph. -/
import D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualQuotientDynamics
import D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.FiniteWindowWordTransport
import D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
/-! Actual chronological path transport on the same original base graph. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualOutgoingDynamics
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
open D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.FiniteWindowWordTransport
open D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
variable {n : ℕ} {A : CountMat n n} {Q : Type}
def rhoLift {k : ℕ} {H : CountMat k k} (p : Q → Fin k) (hp : Function.Surjective p)
    (rho : (b : Edge H) → {u : Q // p u = b.source} → {v : Q // p v = b.target}) :
    IncomingLift H.transpose Q where
  project := p
  onto := hp
  lift b u := rho ⟨b.target,b.source,b.number⟩ u

-- Exact append composition via existing complete path-concatenation supplier.
theorem lift_append (L : IncomingLift A Q) {d : ℕ} {i j k : Fin n}
    (p : FinitePath A d i j) (a : Fin (A j k)) (v : {v : Q // L.project v = k}) :
    L.liftPath (appendPath p a) v = L.liftPath p (L.lift ⟨j,k,a⟩ v) := by
  obtain ⟨r,hw,hr⟩ := concatenate_paths L p (.cons a (.nil k))
  have he : r = appendPath p a := by
    apply sigma_mk_injective
    apply word_endpoint_injective
    exact hw.trans (D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.word_appendPath p a).symm
  exact he ▸ hr v

def rhoPath (p : Q → Fin n) (hp : Function.Surjective p)
    (rho : (b : Edge A) → {u : Q // p u = b.source} → {v : Q // p v = b.target}) :
    {d : ℕ} → {i j : Fin n} → FinitePath A d i j →
      {u : Q // p u = i} → {v : Q // p v = j}
  | _,_,_,.nil _,u => u
  | _,i,_,.cons (j:=j) b tail,u => rhoPath p hp rho tail (rho ⟨i,j,b⟩ u)

theorem chronological_rho (p : Q → Fin n) (hp : Function.Surjective p)
    (rho : (b : Edge A) → {u : Q // p u = b.source} → {v : Q // p v = b.target})
    {d : ℕ} {i j : Fin n} (beta : FinitePath A d i j) (u : {u : Q // p u = i}) :
    (rhoLift p hp rho).liftPath (reverseFinitePath beta) u = rhoPath p hp rho beta u := by
  induction beta with
  | nil => rfl
  | @cons d i j k b tail ih =>
    change (rhoLift p hp rho).liftPath (appendPath (reverseFinitePath tail) b) u = _
    rw [lift_append]
    exact ih (rho ⟨i,j,b⟩ u)

theorem reverse_reverse {d : ℕ} {i j : Fin n} (p : FinitePath A d i j) :
    reverseFinitePath (reverseFinitePath p) = p := by
  apply sigma_mk_injective
  apply word_endpoint_injective
  simp only [reverse_word,List.map_reverse,List.reverse_reverse,List.map_map]
  have h : (fun x : Edge A => reverseEdge (reverseEdge x)) = id := by
    funext x; cases x; rfl
  simpa only [Function.comp_def,h,List.map_id]

theorem rho_response_paths (p : Q → Fin n) (hp : Function.Surjective p)
    (rho : (b : Edge A) → {u : Q // p u = b.source} → {v : Q // p v = b.target})
    (d : ℕ) (u v : Q) :
    (rhoLift p hp rho).response d u v ↔ p u = p v ∧
      ∀ (i j : Fin n) (beta : FinitePath A d i j)
        (hu : p u = i) (hv : p v = i),
        (rhoPath p hp rho beta ⟨u,hu⟩).val = (rhoPath p hp rho beta ⟨v,hv⟩).val := by
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h,?_⟩
    intro i j beta hu hv
    have h' := congrArg (fun r => r.2 j i (reverseFinitePath beta)) h
    have huL : (rhoLift p hp rho).project u = i := hu
    have hvL : (rhoLift p hp rho).project v = i := hv
    simp only [IncomingLift.responseReadout,dif_pos huL,dif_pos hvL,Option.some.injEq] at h'
    simpa only [chronological_rho] using h'
  · rintro ⟨huv,h⟩
    change (rhoLift p hp rho).responseReadout d u = (rhoLift p hp rho).responseReadout d v
    apply Prod.ext huv
    funext i j alpha
    by_cases hu : p u = j
    · have hv := huv.symm.trans hu
      have huL : (rhoLift p hp rho).project u = j := hu
      have hvL : (rhoLift p hp rho).project v = j := hv
      simp only [IncomingLift.responseReadout,dif_pos huL,dif_pos hvL,Option.some.injEq]
      have h' := h j i (reverseFinitePath alpha) hu hv
      rw [← chronological_rho,← chronological_rho,reverse_reverse] at h'
      exact h'
    · have hv : p v ≠ j := fun hv => hu (huv.trans hv)
      have huL : (rhoLift p hp rho).project u ≠ j := hu
      have hvL : (rhoLift p hp rho).project v ≠ j := hv
      simp only [IncomingLift.responseReadout,dif_neg huL,dif_neg hvL]


#print axioms chronological_rho
#print axioms rho_response_paths
end D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualOutgoingDynamics
