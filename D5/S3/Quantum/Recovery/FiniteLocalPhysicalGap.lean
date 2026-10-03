/- GID: D5/S3/Quantum/Recovery/FiniteLocalPhysicalGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalPhysicalGap
   mirror-E: none(waiver:finite-physical-tree-domination)
   anchors: []
   utility: none
   digest: Original finite CP recovery is dominated by the source Bellman value and frontier gap. -/

import D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
import D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Recovery.FiniteLocalPhysicalGap
open FiniteLocalProtocol FiniteLocalLatitudeGeometry FiniteLocalSharedLabelRecovery
open FiniteLocalBellmanEnvelope
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/-- Nonzero finite local work spaces at every actual node, with no bound shared
across protocols. Zero CP branches remain part of the tree. -/
def positiveDimensions {Y : Type} {d : Fin 2 → ℕ} : FiniteLocalProtocol.Tree Y d → Prop
  | .leaf _ => ∀ a, 0 < d a
  | .node _ children => (∀ a, 0 < d a) ∧ ∀ y, positiveDimensions (children y)

/-- Every protocol is individually finite. No common depth, branching or local
dimension bound is imposed. The same actual-label feedback is used on all
histories of that label and on every untouched finite reference. -/
def physicalSuccess (r : ℝ) : Set ℝ :=
  {p | 0 ≤ p ∧ p ≤ 1 ∧ ∃ (Y : Type) (_ : Fintype Y) (P : ActualProtocol Y)
    (accept : Y → Prop) (feedback : Y → Matrix.unitaryGroup (Fin 5) ℂ),
    positiveDimensions P.tree ∧ (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
      acceptedMap P r accept feedback X = (p : ℂ) • X) ∧
    (∀ (F : Type) [Fintype F] [DecidableEq F]
      (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
      referenceAcceptedMap P r accept feedback F X = (p : ℂ) • X)}

/-- The source supremum over the complete physical finite-protocol class. -/
def eta_fin (r : ℝ) : ℝ := sSup (physicalSuccess r)

set_option maxHeartbeats 3000000 in
-- The actual dependent-dimension tree induction and source supremum share one proof.
/-- The full source finite-recovery gap and closed-domain variational
certificate. Only physical-to-abstract domination is needed. -/
theorem full_source_finite_recovery_gap (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2) :
    (∀ (Y : Type) (P : ActualProtocol Y) (accept : Y → Prop)
      (feedback : Y → Matrix.unitaryGroup (Fin 5) ℂ) (p : ℝ), 0 ≤ p →
      (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
        acceptedMap P r accept feedback X = (p : ℂ) • X) →
      p ≤ 4*VInfinity r origin ∧ p ≤ U r-H r^3/(49152*kappa r) ∧ p ≤ 1 ∧
      (∀ q : ℝ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
          acceptedMap P r accept feedback X = (q : ℂ) • X) ↔
        (∀ (F : Type) [Fintype F] [DecidableEq F]
          (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
          referenceAcceptedMap P r accept feedback F X = (q : ℂ) • X))) ∧
    (0 ∈ physicalSuccess r ∧ BddAbove (physicalSuccess r) ∧
      IsLUB (physicalSuccess r) (eta_fin r)) ∧
    (0 ≤ eta_fin r ∧ eta_fin r ≤ 4*VInfinity r origin ∧
      eta_fin r ≤ U r-H r^3/(49152*kappa r) ∧
      4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
      U r-H r^3/(49152*kappa r) < U r) ∧
    (∀ z, VInfinity r z = treeValue r z) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r) ∧
    H r^3/(196608*kappa r) ≤ psi r origin := by
  classical
  rcases source_bellman_finite_tree_identity r hr hlo hhi with
    ⟨_,_,_,_,_,values,concave,_,bounds,flat,diagonal,convex⟩
  have originCertificate := same_tree_stopped_moment_certificate r hr hlo hhi origin
    (.stop origin) (fun _ => false) (by simp)
  have bellmanGap := originCertificate.2.1
  have strictGap := originCertificate.2.2.1
  have psiGap := originCertificate.2.2.2
  have physical : ∀ (Y : Type) (P : ActualProtocol Y) (accept : Y → Prop)
      (feedback : Y → Matrix.unitaryGroup (Fin 5) ℂ) (p : ℝ), 0 ≤ p →
      (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
        acceptedMap P r accept feedback X = (p : ℂ) • X) →
      p ≤ 4*VInfinity r origin ∧ p ≤ U r-H r^3/(49152*kappa r) ∧ p ≤ 1 ∧
      (∀ q : ℝ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
          acceptedMap P r accept feedback X = (q : ℂ) • X) ↔
        (∀ (F : Type) [Fintype F] [DecidableEq F]
          (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
          referenceAcceptedMap P r accept feedback F X = (q : ℂ) • X)) := by
    intro Y P accept feedback p hp recovery
    rcases actual_shared_label_support_rigidity P r hr accept feedback p hp recovery with
      ⟨pOne,_,normalized,_,reference,_,acceptedWeight,acceptedGeometry⟩
    let ball {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) (a : Fin 2) : Ball :=
      ⟨localBloch F a, by
        simpa only [Metric.mem_closedBall,dist_zero_right] using
          (normalized.2.2.1 F).1 a |>.2.2.1⟩
    let state {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) :
        FiniteLocalBellmanEnvelope.State := (ball F 0,ball F 1)
    have weightNonneg {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d) :
        0 ≤ effectWeight F :=
      mul_nonneg ((normalized.2.2.1 F).1 0).1 ((normalized.2.2.1 F).1 1).1
    have zeroWeight {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d)
        (hz : F.inputEffect = 0) : effectWeight F = 0 := by
      rw [← (normalized.2.2.1 F).2.2]
      simp [pairEffect,hz]
    have zeroEffect {d : Fin 2 → ℕ} (F : LocalFactors InputDimensions d)
        (hz : effectWeight F = 0) : F.inputEffect = 0 := by
      have he : pairEffect F = 0 := by
        rw [(normalized.2.2.1 F).2.1,hz]
        simp
      ext x z
      have h := congrFun (congrFun he (pairCoordinates.symm x)) (pairCoordinates.symm z)
      simpa [pairEffect] using h
    -- This induction retains exactly the chosen original leaf subset. It
    -- separates zero effects before invoking any trace-ratio split.
    have domination : ∀ {d : Fin 2 → ℕ} (T : FiniteLocalProtocol.Tree Y d)
        (F : LocalFactors InputDimensions d) (mark : T.Leaves → Prop),
        (∀ w, mark w → ((T.leafPath w).factors F).inputEffect ≠ 0 →
          (localBloch ((T.leafPath w).factors F) 0,
            localBloch ((T.leafPath w).factors F) 1) ∈ K_s r) →
        (∑ w : T.Leaves, if mark w then
          h r * effectWeight ((T.leafPath w).factors F) else 0) ≤
        effectWeight F * VInfinity r (state F) := by
      intro d T
      induction T with
      | @leaf d label =>
        intro F mark accepted
        by_cases hz : effectWeight F = 0
        · simp [FiniteLocalProtocol.Tree.Leaves,FiniteLocalProtocol.Tree.leafPath,
            ObservedPath.factors,hz]
        · by_cases hm : mark ()
          · have hk := accepted () hm (fun he => hz (zeroWeight F he))
            have hv := (flat (state F) hk).1
            simpa [FiniteLocalProtocol.Tree.Leaves,FiniteLocalProtocol.Tree.leafPath,
              ObservedPath.factors,hm,hv,mul_comm]
          · simpa [FiniteLocalProtocol.Tree.Leaves,FiniteLocalProtocol.Tree.leafPath,
              ObservedPath.factors,hm] using
              mul_nonneg (weightNonneg F) (bounds (state F)).1
      | @node d J children ih =>
        intro F mark accepted
        by_cases hz : effectWeight F = 0
        · have descendants := normalized.2.2.2.2 (.node J children) F (zeroEffect F hz)
          have leafZero : ∀ w : (FiniteLocalProtocol.Tree.node J children).Leaves,
              effectWeight (((FiniteLocalProtocol.Tree.node J children).leafPath w).factors F) = 0 :=
            fun w => zeroWeight _ (descendants w)
          simp only [leafZero,mul_zero,ite_self,Finset.sum_const_zero,hz,zero_mul,le_refl]
        · have positive : 0 < effectWeight F := lt_of_le_of_ne (weightNonneg F) (Ne.symm hz)
          rcases (normalized.2.2.2.1 F J).1 positive with
            ⟨nonneg,total,childWeight,mean,inactive⟩
          have jensen : (∑ y, splitWeight F J y *
              VInfinity r (state (F.advance J y))) ≤ VInfinity r (state F) := by
            by_cases ha : J.actor = 0
            · have inactiveOne (y : Fin J.outcomes) :
                  ball (F.advance J y) 1 = ball F 1 := by
                apply Subtype.ext
                exact inactive y 1 (by rw [ha]; decide)
              let sa : Split J.outcomes (active false (state F)) :=
                ⟨splitWeight F J,fun y => ball (F.advance J y) 0,nonneg,total,
                  by simpa [active,state,ball,ha] using mean.symm⟩
              have hs := concave false (state F) J.outcomes sa
              simpa [sa,place,passive,state,inactiveOne] using hs
            · have hb : J.actor = 1 := by
                have hj := J.actor.isLt
                have hn : J.actor.val ≠ 0 := fun he => ha (Fin.ext he)
                apply Fin.ext
                omega
              have inactiveZero (y : Fin J.outcomes) :
                  ball (F.advance J y) 0 = ball F 0 := by
                apply Subtype.ext
                exact inactive y 0 (by rw [hb]; decide)
              let sb : Split J.outcomes (active true (state F)) :=
                ⟨splitWeight F J,fun y => ball (F.advance J y) 1,nonneg,total,
                  by simpa [active,state,ball,hb] using mean.symm⟩
              have hs := concave true (state F) J.outcomes sb
              simpa [sb,place,passive,state,inactiveZero] using hs
          have childBounds (y : Fin J.outcomes) := ih y (F.advance J y)
            (fun w => mark ⟨y,w⟩) (fun w hw he => accepted ⟨y,w⟩ hw he)
          calc
            _ = ∑ y, ∑ w : (children y).Leaves,
                if mark ⟨y,w⟩ then h r * effectWeight
                  (((children y).leafPath w).factors (F.advance J y)) else 0 := by
              change (∑ w : (y : Fin J.outcomes) × (children y).Leaves,
                if mark w then h r * effectWeight
                  (((children w.1).leafPath w.2).factors (F.advance J w.1)) else 0) = _
              exact Fintype.sum_sigma _
            _ ≤ ∑ y, effectWeight (F.advance J y) *
                VInfinity r (state (F.advance J y)) :=
              Finset.sum_le_sum (fun y _ => childBounds y)
            _ = effectWeight F * (∑ y, splitWeight F J y *
                VInfinity r (state (F.advance J y))) := by
              simp_rw [childWeight]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
            _ ≤ effectWeight F * VInfinity r (state F) :=
              mul_le_mul_of_nonneg_left jensen (weightNonneg F)
    have originalAccepted : ∀ w : P.tree.Leaves,
        accept (P.tree.leafFeedback w) →
        ((P.tree.leafPath w).factors (P.ancillas.rootFactors InputDimensions)).inputEffect ≠ 0 →
        (localBloch (leafFactors P w) 0,localBloch (leafFactors P w) 1) ∈ K_s r := by
      intro w hw he
      have leafNonzero : leafEffect P w ≠ 0 := by
        intro hz
        apply he
        ext x z
        have eq := congrFun (congrFun hz (pairCoordinates.symm x)) (pairCoordinates.symm z)
        simpa [leafEffect,leafFactors] using eq
      exact ((acceptedGeometry ⟨w,hw⟩).2.2 leafNonzero).2.2 hlo hhi |>.2.1
    have atRoot := domination P.tree (P.ancillas.rootFactors InputDimensions)
      (fun w => accept (P.tree.leafFeedback w)) originalAccepted
    have rootState : state (P.ancillas.rootFactors InputDimensions) = origin := by
      apply Prod.ext <;> apply Subtype.ext <;> exact normalized.2.1 _
    have sumAccepted : (∑ w : P.tree.Leaves, if accept (P.tree.leafFeedback w) then
        h r * effectWeight (leafFactors P w) else 0) = p := by
      rw [acceptedWeight hlo hhi,Finset.mul_sum]
      symm
      change (∑ w : {w : P.tree.Leaves // accept (P.tree.leafFeedback w)},
        h r * effectWeight (leafFactors P w.val)) = _
      have hsub := Finset.sum_subtype
        (p := fun w : P.tree.Leaves => accept (P.tree.leafFeedback w))
        (F := inferInstanceAs (Fintype (Accepted P accept)))
        (Finset.univ.filter (fun w => accept (P.tree.leafFeedback w)))
        (by simp) (fun w => h r * effectWeight (leafFactors P w))
      exact hsub.symm.trans (Finset.sum_filter _ _)
    have bound : p ≤ 4*VInfinity r origin := by
      change (∑ w, if accept (P.tree.leafFeedback w) then
        h r * effectWeight (leafFactors P w) else 0) ≤ _ at atRoot
      simpa only [sumAccepted,normalized.1,rootState] using atRoot
    exact ⟨bound,bound.trans bellmanGap,pOne,reference⟩
  have zeroSuccess : 0 ∈ physicalSuccess r := by
    let ancillas : ProductAncillas (Fin 2) :=
      ⟨fun _ => 1,fun _ => ⟨1,zero_le_one,by simp [Matrix.trace]⟩⟩
    let P : ActualProtocol Unit := ⟨ancillas,.leaf ()⟩
    refine ⟨by norm_num,by norm_num,Unit,inferInstance,P,
      (fun _ => False),(fun _ => 1),?_,?_,?_⟩
    · simp [P,ancillas,positiveDimensions,InputDimensions]
    · intro X
      simp [acceptedMap,Accepted]
    · intro F _ _ X
      simp [referenceAcceptedMap,Accepted]
  have uniform : ∀ p ∈ physicalSuccess r, p ≤ 4*VInfinity r origin := by
    rintro p ⟨hp,_,Y,_,P,accept,feedback,_,recovery,_⟩
    exact (physical Y P accept feedback p hp recovery).1
  have bounded : BddAbove (physicalSuccess r) := ⟨4*VInfinity r origin,uniform⟩
  have nonempty : (physicalSuccess r).Nonempty := ⟨0,zeroSuccess⟩
  have etaNonneg : 0 ≤ eta_fin r := le_csSup bounded zeroSuccess
  have etaBound : eta_fin r ≤ 4*VInfinity r origin := csSup_le nonempty uniform
  exact ⟨physical,⟨zeroSuccess,bounded,isLUB_csSup nonempty bounded⟩,
    ⟨etaNonneg,etaBound,etaBound.trans bellmanGap,bellmanGap,strictGap⟩,
    (fun z => (values z).1),concave,bounds,flat,diagonal,convex,psiGap⟩

end D5.S3.Quantum.Recovery.FiniteLocalPhysicalGap
