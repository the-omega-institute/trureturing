/- GID: D5/S3/Analytic/Convexity/WeakParetoDisconnected
   generality: I
   mirror-B: D5/B/S3/Analytic/Convexity/WeakParetoDisconnected
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Convexity/WeakParetoDisconnected.claim; result=D5/S3/Analytic/Convexity/WeakParetoDisconnected.result; claim=D5/S3/Analytic/Convexity/WeakParetoDisconnected.claim
   digest: Two continuous convex objectives on a closed convex planar strip have a disconnected weak Pareto solution set. -/

/- Source: Vu Trung Hieu, arXiv:2610.01029, §4.3.
   admission_basis: open-problem-resolution (#15516; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Reuse: convexOn_univ_norm, Even.convexOn_pow, ConvexOn.comp_affineMap,
     ConvexOn.sup, ConvexOn.pow, ConvexOn.sub, LinearMap.concaveOn,
     Convex.linear_preimage, Convex.inter.
   Definitions:
     weakPareto: proof_shape definition; consumers=claim, weak_of_boundary,
       weak_boundary, not_preconnected
     claim: proof_shape definition; consumer=result
     point: proof_shape definition; consumers=h_norm, convex_h, dominated_in_gap,
       not_preconnected
     h: proof_shape definition; consumers=h_positive, h_reciprocal, h_norm,
       convex_h, continuous_h, objectives, weak_of_boundary, dominated_in_gap,
       weak_boundary, not_preconnected
     feasible: proof_shape definition; consumers=feasible_properties,
       weak_of_boundary, dominated_in_gap, weak_boundary, not_preconnected, result
     objectives: proof_shape definition; consumers=convex_objectives,
       continuous_objectives, weak_of_boundary, dominated_in_gap, weak_boundary,
       not_preconnected, result
   Per-declaration proof_shape and live consumers:
     h_positive: bind-only; consumer=not_preconnected
     h_reciprocal: bind-only; consumer=dominated_in_gap
     h_norm: bind-only; consumer=convex_h
     convex_h: bind-only; consumer=convex_objectives
     convex_objectives: bind-only; consumer=result
     continuous_h: bind-only; consumers=continuous_objectives, not_preconnected
     continuous_objectives: bind-only; consumer=result
     feasible_properties: bind-only; consumer=result
     weak_of_boundary: bind-only; consumer=not_preconnected
     dominated_in_gap: content; consumer=weak_boundary
     weak_boundary: content; consumer=not_preconnected
     not_preconnected: content; consumer=result
     result: content; designated refutation conclusion
   A point strictly between the two boundary pieces admits an explicit strict
   dominator. Positive h separates the resulting solution pieces by open sets. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section

namespace D5.S3.Analytic.Convexity.WeakParetoDisconnected

/-- Weak Pareto solutions of `f : Fin m → (E → ℝ)` on `K`. -/
def weakPareto {E : Type*} {m : ℕ} (K : Set E) (f : Fin m → E → ℝ) : Set E :=
  {z | z ∈ K ∧ ¬ ∃ u ∈ K, ∀ i, f i u < f i z}

def claim : Prop :=
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
    ∀ (K : Set (EuclideanSpace ℝ (Fin n)))
      (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ),
      K.Nonempty → IsClosed K → Convex ℝ K →
      (∀ i, Continuous (f i)) → (∀ i, ConvexOn ℝ Set.univ (f i)) →
      IsPreconnected (weakPareto K f)

private def point (x y : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x, y]

private def h (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 1) - x

private def feasible : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2}

private def objectives (i : Fin 2) (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if i = 0 then (p 1) ^ 2 else (max (h (p 0) - p 1 / 2) 0) ^ 2 - p 1 / 2

private lemma h_positive (x : ℝ) : 0 < h x := by
  have hs := Real.sq_sqrt (by nlinarith [sq_nonneg x] : 0 ≤ x ^ 2 + 1)
  have hn := Real.sqrt_nonneg (x ^ 2 + 1)
  unfold h
  nlinarith

private lemma h_reciprocal (v : ℝ) (hv : 0 < v) : h (1 / v) < v / 2 := by
  have hx : 0 < 1 / v := one_div_pos.mpr hv
  have hmul : (1 / v) * v = 1 := by field_simp
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (1 / v) ^ 2 + 1)
  have hn := Real.sqrt_nonneg ((1 / v) ^ 2 + 1)
  unfold h
  nlinarith [sq_pos_of_pos hv]

private lemma h_norm (x : ℝ) : h x = ‖point x 1‖ - x := by
  have hn : ‖point x 1‖ ^ 2 = x ^ 2 + 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, point]
  have hs := Real.sq_sqrt (by positivity : 0 ≤ x ^ 2 + 1)
  have he : Real.sqrt (x ^ 2 + 1) = ‖point x 1‖ := by
    nlinarith [norm_nonneg (point x 1), Real.sqrt_nonneg (x ^ 2 + 1)]
  simp [h, he]

private lemma convex_h :
    ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin 2) => h (p 0)) := by
  let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun p => point (p 0) 0
      map_add' := by intros; ext i; fin_cases i <;> simp [point]
      map_smul' := by intros; ext i; fin_cases i <;> simp [point] }
  let g : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun p => point (p 0) 1
      linear := L
      map_vadd' := by intros; ext i; fin_cases i <;> simp [L, point] }
  have hn : ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin 2) =>
      ‖point (p 0) 1‖) := by
    simpa [g, Function.comp_def] using convexOn_univ_norm.comp_affineMap g
  have hc := hn.sub ((EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 2)).concaveOn convex_univ)
  change ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin 2) =>
    ‖point (p 0) 1‖ - p 0) at hc
  simpa only [← h_norm] using hc

private lemma convex_objectives : ∀ i, ConvexOn ℝ Set.univ (objectives i) := by
  let Y := EuclideanSpace.projₗ (𝕜 := ℝ) (1 : Fin 2)
  let H : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • Y
  have hH : ConcaveOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin 2) => p 1 / 2) := by
    have hc := H.concaveOn convex_univ
    change ConcaveOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin 2) =>
      (1 / 2 : ℝ) * p 1) at hc
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hc
  intro i
  fin_cases i
  · change ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin 2) => (p 1) ^ 2)
    simpa [Y, Function.comp_def] using
      (Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)).comp_affineMap Y.toAffineMap
  · have hm : ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin 2) =>
        max (h (p 0) - p 1 / 2) 0) :=
      (convex_h.sub hH).sup (convexOn_const 0 convex_univ)
    exact (hm.pow (fun _ _ => le_max_right _ _) 2).sub hH

private lemma continuous_h : Continuous h := by
  exact ((continuous_id.pow 2).add continuous_const).sqrt.sub continuous_id

private lemma continuous_objectives : ∀ i, Continuous (objectives i) := by
  intro i
  have hc (j : Fin 2) : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p j) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j
  fin_cases i
  · change Continuous (fun p : EuclideanSpace ℝ (Fin 2) => (p 1) ^ 2)
    exact (hc 1).pow 2
  · change Continuous (fun p : EuclideanSpace ℝ (Fin 2) =>
      (max (h (p 0) - p 1 / 2) 0) ^ 2 - p 1 / 2)
    exact
      ((((continuous_h.comp (hc 0)).sub ((hc 1).div_const 2)).max
        continuous_const).pow 2).sub ((hc 1).div_const 2)

private lemma feasible_properties : feasible.Nonempty ∧ IsClosed feasible ∧ Convex ℝ feasible := by
  have hc (j : Fin 2) : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p j) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j
  refine ⟨⟨0, by simp [feasible]⟩, ?_, ?_⟩
  · exact (isClosed_le continuous_const (hc 0)).inter
      ((isClosed_le continuous_const (hc 1)).inter (isClosed_le (hc 1) continuous_const))
  · exact ((convex_Ici (0 : ℝ)).linear_preimage
      (EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 2))).inter
      (((convex_Ici (0 : ℝ)).linear_preimage
        (EuclideanSpace.projₗ (𝕜 := ℝ) (1 : Fin 2))).inter
        ((convex_Iic (2 : ℝ)).linear_preimage
          (EuclideanSpace.projₗ (𝕜 := ℝ) (1 : Fin 2))))

private lemma weak_of_boundary (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ feasible) (hb : p 1 = 0 ∨ 2 * h (p 0) ≤ p 1) :
    p ∈ weakPareto feasible objectives := by
  refine ⟨hp, ?_⟩
  rintro ⟨u, hu, hlt⟩
  have h₀ := hlt 0
  have h₁ := hlt 1
  simp [objectives] at h₀ h₁
  rcases hb with hz | hb
  · rw [hz] at h₀
    nlinarith [sq_nonneg (u 1)]
  · have hmax : max (h (p 0) - p 1 / 2) 0 = 0 := max_eq_right (by linarith)
    rw [hmax] at h₁
    have hy : p 1 < u 1 := by
      nlinarith [sq_nonneg (max (h (u 0) - u 1 / 2) 0)]
    have hp₁ := hp.2.1
    nlinarith

private lemma dominated_in_gap (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ feasible) (hy : 0 < p 1) (hgap : p 1 < 2 * h (p 0)) :
    ∃ u ∈ feasible, ∀ i, objectives i u < objectives i p := by
  let d := objectives 1 p
  have hs : 0 < h (p 0) - p 1 / 2 := by linarith
  have hd : -p 1 / 2 < d := by
    dsimp [d, objectives]
    rw [max_eq_left hs.le]
    nlinarith [sq_pos_of_pos hs]
  let v := (max 0 (-2 * d) + p 1) / 2
  have hv : 0 < v := by dsimp [v]; linarith [le_max_left (0 : ℝ) (-2 * d)]
  have hvy : v < p 1 := by
    have hm : max 0 (-2 * d) < p 1 := max_lt hy (by linarith)
    dsimp [v]
    linarith
  have hvd : -v / 2 < d := by
    dsimp [v]
    linarith [le_max_right (0 : ℝ) (-2 * d)]
  refine ⟨point (1 / v) v, ?_, ?_⟩
  · simp only [feasible, Set.mem_ofPred_eq]
    simp only [point, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨(one_div_pos.mpr hv).le, hv.le, (hvy.trans_le hp.2.2).le⟩
  · intro i
    fin_cases i
    · simp [objectives, point]
      nlinarith [hp.2.1]
    · have hm : max (h (1 / v) - v / 2) 0 = 0 :=
        max_eq_right (by linarith [h_reciprocal v hv])
      change (max (h (1 / v) - v / 2) 0) ^ 2 - v / 2 < objectives 1 p
      rw [hm]
      simpa only [zero_pow (by decide : 2 ≠ 0), zero_sub, neg_div] using hvd

private lemma weak_boundary (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ weakPareto feasible objectives) :
    p 1 = 0 ∨ 2 * h (p 0) ≤ p 1 := by
  by_contra hb
  have hy : 0 < p 1 := lt_of_le_of_ne hp.1.2.1 (Ne.symm (not_or.mp hb).1)
  exact hp.2 (dominated_in_gap p hp.1 hy (lt_of_not_ge (not_or.mp hb).2))

private lemma not_preconnected : ¬ IsPreconnected (weakPareto feasible objectives) := by
  let U : Set (EuclideanSpace ℝ (Fin 2)) := {p | p 1 < h (p 0)}
  let V : Set (EuclideanSpace ℝ (Fin 2)) := {p | h (p 0) < p 1}
  have hc (j : Fin 2) : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p j) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j
  have hU : IsOpen U := isOpen_lt (hc 1) (continuous_h.comp (hc 0))
  have hV : IsOpen V := isOpen_lt (continuous_h.comp (hc 0)) (hc 1)
  have hcover : weakPareto feasible objectives ⊆ U ∪ V := by
    intro p hp
    rcases weak_boundary p hp with hz | hb
    · left
      change p 1 < h (p 0)
      rw [hz]
      exact h_positive _
    · right
      change h (p 0) < p 1
      linarith [h_positive (p 0)]
  have hzero : (weakPareto feasible objectives ∩ U).Nonempty := by
    refine ⟨point 0 0, weak_of_boundary _ ?_ (Or.inl ?_), ?_⟩
    · norm_num [feasible, point]
    · simp [point]
    · change (point 0 0) 1 < h ((point 0 0) 0)
      norm_num [point, h]
  have htwo : (weakPareto feasible objectives ∩ V).Nonempty := by
    refine ⟨point 0 2, weak_of_boundary _ ?_ (Or.inr ?_), ?_⟩
    · norm_num [feasible, point]
    · norm_num [point, h]
    · change h ((point 0 2) 0) < (point 0 2) 1
      norm_num [point, h]
  intro hp
  obtain ⟨p, hp, hpU, hpV⟩ := hp U V hU hV hcover hzero htwo
  change p 1 < h (p 0) at hpU
  change h (p 0) < p 1 at hpV
  exact (lt_asymm hpU hpV)

theorem result : ¬ claim := by
  intro hc
  obtain ⟨hne, hclosed, hconvex⟩ := feasible_properties
  exact not_preconnected
    (hc 2 2 (by norm_num) (by norm_num) feasible objectives hne hclosed hconvex
      continuous_objectives convex_objectives)

end D5.S3.Analytic.Convexity.WeakParetoDisconnected
