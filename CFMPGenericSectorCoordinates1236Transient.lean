import CFMPOrderedEndpointCycle1210Transient
import CFMPGenericEndpointFan1191Transient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate
open D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceCycleCandidate
open D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate
open D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (Sector)
open private beta_values beta_simplex inverse_sector dominant_unique
  from D5.S3.Geometry.Gluing.ActualLinkAffineFan
variable {T : Type*}

def positions (j k : Fin 4) (b : Bool) : Fin 4 → Fin 4 :=
  ![j,k,if b then (edgeFaces (edgeIndex j k)).1 else (edgeFaces (edgeIndex j k)).2,
    if b then (edgeFaces (edgeIndex j k)).2 else (edgeFaces (edgeIndex j k)).1]

private theorem positions_bijective (j k : Fin 4) (h : j ≠ k) (b : Bool) :
    Function.Bijective (positions j k b) := by
  fin_cases j <;> fin_cases k <;> cases b <;>
    first | exact False.elim (h rfl) | decide

def localFrame (r : Occurrence T → Bool) (d : OrderedEnd T) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (positions d.val.1.2 d.val.2 (r (occ d.val)))
    (positions_bijective _ _ d.property _)

theorem frame_values (r : Occurrence T → Bool) (d : OrderedEnd T) :
    localFrame r d 0 = d.val.1.2 ∧ localFrame r d 1 = d.val.2 ∧
    localFrame r d 2 = outgoingFace r (occ d.val) ∧
    localFrame r d 3 = incomingFace r (occ d.val) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

def beta (r : Occurrence T → Bool) (d : OrderedEnd T) (p : ℝ × ℝ) : Fin 4 → ℝ :=
  fun l => D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta 0 0 p
    ((localFrame r d).symm l)

private theorem reference_values (p : ℝ × ℝ) :
    D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta 0 0 p 0 = 0 ∧
    D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta 0 0 p 1 = 1-(p.1+p.2)/2 ∧
    D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta 0 0 p 3 = p.1/2 ∧
    D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta 0 0 p 2 = p.2/2 := by
  simpa [D5.S3.Geometry.Gluing.ActualCornerPointPeriods.corner,
    D5.S3.Geometry.Gluing.ActualCornerPointPeriods.tip,
    D5.S3.Geometry.Gluing.ActualCornerPointPeriods.incoming,
    D5.S3.Geometry.Gluing.ActualCornerPointPeriods.outgoing]
    using beta_values (0 : Fin 4) (0 : Fin 3) p

theorem beta_actual_values (r : Occurrence T → Bool) (d : OrderedEnd T) (p : ℝ × ℝ) :
    beta r d p d.val.1.2 = 0 ∧
    beta r d p d.val.2 = 1-(p.1+p.2)/2 ∧
    beta r d p (incomingFace r (occ d.val)) = p.1/2 ∧
    beta r d p (outgoingFace r (occ d.val)) = p.2/2 := by
  have h := reference_values p
  have f := frame_values r d
  unfold beta
  rw [← f.1,← f.2.1,← f.2.2.1,← f.2.2.2]
  simpa only [Equiv.symm_apply_apply] using h

theorem beta_actual_simplex (r : Occurrence T → Bool) (d : OrderedEnd T) (p : Sector) :
    (∀ l, 0 ≤ beta r d p.val l) ∧
    (∑ l, beta r d p.val l) = 1 ∧ 1/2 < beta r d p.val d.val.2 := by
  have h := beta_simplex (0 : Fin 4) (0 : Fin 3) p
  refine ⟨fun l => h.1 _,?_,?_⟩
  · exact ((localFrame r d).symm.sum_comp
      (D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta 0 0 p.val)).trans h.2.1
  · rw [(beta_actual_values r d p.val).2.1]
    linarith [p.property.2.2]

theorem actual_inverse_sector (r : Occurrence T → Bool) (d : OrderedEnd T)
    (b : Fin 4 → ℝ) (hj : b d.val.1.2 = 0) (hn : ∀ l, 0 ≤ b l)
    (hs : (∑ l, b l) = 1) (hk : 1/2 < b d.val.2) :
    (0 ≤ 2*b (incomingFace r (occ d.val)) ∧
      0 ≤ 2*b (outgoingFace r (occ d.val)) ∧
      2*b (incomingFace r (occ d.val)) + 2*b (outgoingFace r (occ d.val)) < 1) ∧
    beta r d (2*b (incomingFace r (occ d.val)),
      2*b (outgoingFace r (occ d.val))) = b := by
  let c : Fin 4 → ℝ := fun l => b (localFrame r d l)
  have hc0 : c 0 = 0 := hj
  have hc1 : 1/2 < c 1 := hk
  have hcs : (∑ l, c l) = 1 := (Equiv.sum_comp (localFrame r d) b).trans hs
  have h := inverse_sector (0 : Fin 4) (0 : Fin 3) c hc0 (fun l => hn _) hcs hc1
  change (0 ≤ 2*c 3 ∧ 0 ≤ 2*c 2 ∧ 2*c 3+2*c 2 < 1) ∧
    D5.S3.Geometry.Gluing.ActualLinkAffineFan.beta 0 0 (2*c 3,2*c 2) = c at h
  refine ⟨h.1,?_⟩
  funext l
  have he := congrFun h.2 ((localFrame r d).symm l)
  simpa only [beta,c,(frame_values r d).2.2.1,
    (frame_values r d).2.2.2,Equiv.apply_symm_apply] using he

end D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate.frame_values,
      ``D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate.beta_actual_values,
      ``D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate.beta_actual_simplex,
      ``D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate.actual_inverse_sector] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1236 target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1236 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1236 CHECKED {name} axioms={axioms}"
