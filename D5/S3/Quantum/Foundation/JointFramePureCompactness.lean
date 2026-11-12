/- GID: D5/S3/Quantum/Foundation/JointFramePureCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/JointFramePureCompactness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Joint original frames and point-exclusion incidence force closed pure points. -/

import D5.S3.Quantum.Foundation.FacetZeroGluing
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! All states, effects and exclusions refer to the same entire original cone base.
The joint-frame and incidence hypotheses are explicit; no ball or local-pair
condition is identified with these hypotheses without a further proof. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.JointFramePureCompactness

open CircuitBalancedConfirmation FacetZeroGluing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Three original states and three globally proper effects, jointly normalized
and with all nine Kronecker readings. Continuous linear maps exhaust the real
linear effects in this finite dimensional domain. -/
def jointFrame (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (s : Fin 3 → V) (e : Fin 3 → V →L[ℝ] ℝ) : Prop :=
  (∀ i, s i ∈ base C u) ∧ (∀ i, proper C u (e i).toLinearMap) ∧
    (∑ i, e i) = u.toContinuousLinearMap ∧
    ∀ i j, e i (s j) = if i = j then 1 else 0

/-- Every original pure point belongs to an original pure joint frame. No
continuity or uniqueness of a choice of completing frame is required. -/
def pureJointCompletion (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : pure C u, ∃ s e, (∀ i, s i ∈ pure C u) ∧ s 0 = (p : V) ∧ jointFrame C u s e

/-- Distinct original exclusion sets meet in at most one state, and a pure
point is determined by its entire exclusion set. -/
def pointBallIncidence (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  (∀ p q : pure C u, exclusion C u p ≠ exclusion C u q →
    (exclusion C u p ∩ exclusion C u q).Subsingleton) ∧
    Function.Injective (fun p : pure C u => exclusion C u p)

private theorem effects_compact {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) :
    IsCompact {f : V →L[ℝ] ℝ | proper C u f.toLinearMap} := by
  classical
  obtain ⟨s, hs, _, hspan, hind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ (C : Set V)
  let b : Module.Basis s ℝ V := Module.Basis.mk hind.linearIndependent (by
    simp [hspan, hgen])
  let M : ℝ := ∑ i : s, ‖u (b i)‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · change IsClosed {f : V →L[ℝ] ℝ | ∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    change IsClosed ({f : V →L[ℝ] ℝ | 0 ≤ f x} ∩ {f | f x ≤ u x})
    exact (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const)
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Fintype.card s • ‖b.equivFunL.toContinuousLinearMap‖ * M, ?_⟩
    intro f hf
    apply b.opNorm_le hM
    intro i
    have hbi : b i ∈ C := hs (by
      simpa [b, Module.Basis.coe_mk] using i.property)
    have hb := hf (b i) hbi
    calc
      ‖f (b i)‖ = f (b i) := Real.norm_of_nonneg hb.1
      _ ≤ u (b i) := hb.2
      _ ≤ ‖u (b i)‖ := le_abs_self _
      _ ≤ M := Finset.single_le_sum (fun j _ => norm_nonneg (u (b j)))
        (Finset.mem_univ i)

omit [FiniteDimensional ℝ V] in
/-- A proper confirmer with two distinct, simultaneously excluded states
cannot have a mixed one-face under point-exclusion incidence. -/
private theorem two_zero_confirming_face {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u)) (hI : pointBallIncidence C u)
    {x y z : V} (hx : x ∈ base C u) (hy : y ∈ base C u) (hz : z ∈ base C u)
    (hyz : y ≠ z) (a : V →L[ℝ] ℝ) (ha : proper C u a.toLinearMap)
    (hax : a x = 1) (hay : a y = 0) (haz : a z = 0) : x ∈ pure C u := by
  classical
  let F : Set V := {t | t ∈ base C u ∧ a t = 1}
  have hxF : x ∈ F := ⟨hx, hax⟩
  have hFc : IsCompact F := hK.inter_right (isClosed_eq a.continuous continuous_const)
  have hFe : IsExposed ℝ (base C u) F := by
    intro _
    refine ⟨a, Set.ext fun t => ?_⟩
    constructor
    · intro ht
      exact ⟨ht.1, fun v hv => (ha v hv.1).2.trans_eq (hv.2.trans ht.2.symm)⟩
    · intro ht
      refine ⟨ht.1, le_antisymm ?_ ?_⟩
      · exact (ha t ht.1.1).2.trans_eq ht.1.2
      · simpa [hax] using ht.2 x hx
  have hFconv := hFe.convex (base_convex C u)
  obtain ⟨p, hp⟩ := hFc.extremePoints_nonempty ⟨x, hxF⟩
  have hpP : p ∈ pure C u := hFe.isExtreme.extremePoints_subset_extremePoints hp
  have hext : F.extremePoints ℝ ⊆ {p} := by
    intro q hq
    have hqP : q ∈ pure C u := hFe.isExtreme.extremePoints_subset_extremePoints hq
    have hyD (r : pure C u) (hr : a r = 1) : y ∈ exclusion C u r :=
      ⟨hy, a.toLinearMap, ⟨ha, hr⟩, hay⟩
    have hzD (r : pure C u) (hr : a r = 1) : z ∈ exclusion C u r :=
      ⟨hz, a.toLinearMap, ⟨ha, hr⟩, haz⟩
    have hD : exclusion C u (⟨q, hqP⟩ : pure C u) =
        exclusion C u (⟨p, hpP⟩ : pure C u) := by
      by_contra hne
      exact hyz (hI.1 _ _ hne
        ⟨hyD ⟨q, hqP⟩ hq.1.2, hyD ⟨p, hpP⟩ hp.1.2⟩
        ⟨hzD ⟨q, hqP⟩ hq.1.2, hzD ⟨p, hpP⟩ hp.1.2⟩)
    exact congrArg Subtype.val (hI.2 hD)
  have hsingle : F ⊆ {p} := by
    rw [← closure_convexHull_extremePoints hFc hFconv]
    exact closure_minimal
      (convexHull_min hext (convex_singleton p)) isClosed_singleton
  have hxp : x = p := hsingle hxF
  exact hxp ▸ hpP

private theorem frame_first_pure {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u)) (hI : pointBallIncidence C u)
    {s : Fin 3 → V} {e : Fin 3 → V →L[ℝ] ℝ} (h : jointFrame C u s e) :
    s 0 ∈ pure C u := by
  have hyz : s 1 ≠ s 2 := by
    intro he
    have h1 := h.2.2.2 1 1
    have h2 := h.2.2.2 1 2
    simp only [ite_true, show (1 : Fin 3) ≠ 2 by decide, ite_false] at h1 h2
    rw [he] at h1
    linarith
  exact two_zero_confirming_face hK hI (h.1 0) (h.1 1) (h.1 2) hyz (e 0) (h.2.1 0)
    (by simpa using h.2.2.2 0 0) (by simpa using h.2.2.2 0 1)
    (by simpa using h.2.2.2 0 2)

/-- Original pure points are closed when all have genuine joint completions
and original exclusion incidence separates them. -/
theorem pure_closed_of_joint_completion {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (hJ : pureJointCompletion C u) (hI : pointBallIncidence C u) :
    IsClosed (pure C u) := by
  classical
  let T : Set ((Fin 3 → V) × (Fin 3 → V →L[ℝ] ℝ)) :=
    {w | jointFrame C u w.1 w.2}
  have hK := base_compact hclosed hstrict
  have hE := effects_compact (u := u) hgen
  have hT : IsCompact T := by
    have hc := (isCompact_univ_pi (fun _ : Fin 3 => hK)).prod
      (isCompact_univ_pi (fun _ : Fin 3 => hE))
    have hr : IsClosed {w : (Fin 3 → V) × (Fin 3 → V →L[ℝ] ℝ) |
        (∑ i, w.2 i) = u.toContinuousLinearMap ∧
          ∀ i j, w.2 i (w.1 j) = if i = j then 1 else 0} := by
      apply IsClosed.inter
      · exact isClosed_eq (by fun_prop) continuous_const
      · change IsClosed {w : (Fin 3 → V) × (Fin 3 → V →L[ℝ] ℝ) |
          ∀ i j, w.2 i (w.1 j) = if i = j then 1 else 0}
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_eq
            ((continuous_apply i |>.comp continuous_snd).clm_apply
              (continuous_apply j |>.comp continuous_fst)) continuous_const
    convert hc.inter_right hr using 1
    ext w
    simp only [T, jointFrame, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_pi, Set.mem_univ, forall_true_left]
    tauto
  have hP : pure C u = (fun w : (Fin 3 → V) × (Fin 3 → V →L[ℝ] ℝ) => w.1 0) '' T := by
    ext p
    constructor
    · intro hp
      obtain ⟨s, e, _, hs, hf⟩ := hJ ⟨p, hp⟩
      exact ⟨(s, e), hf, hs⟩
    · rintro ⟨⟨s, e⟩, hf, rfl⟩
      exact frame_first_pure hK hI hf
  rw [hP]
  exact (hT.image (by fun_prop)).isClosed

/-- The same entire pure set is compact, without assuming it finite or closed. -/
theorem pure_compact_of_joint_completion {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (hJ : pureJointCompletion C u) (hI : pointBallIncidence C u) :
    IsCompact (pure C u) :=
  (base_compact hclosed hstrict).of_isClosed_subset
    (pure_closed_of_joint_completion hclosed hstrict hgen hJ hI)
    (fun _ hp => hp.1)

end D5.S3.Quantum.Foundation.JointFramePureCompactness
