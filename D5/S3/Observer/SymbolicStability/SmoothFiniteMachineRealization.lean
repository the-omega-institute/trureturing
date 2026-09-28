/- GID: D5/S3/Observer/SymbolicStability/SmoothFiniteMachineRealization
   generality: G
   mirror-B: D5/B/S3/Observer/SymbolicStability/SmoothFiniteMachineRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth finite machines decode exactly under bounded noise at every prefix. -/

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

noncomputable section

namespace D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization

open scoped BigOperators

/-- Execute the actions in a finite word, in their listed order. -/
def symbolicRun {S A : Type*} (δ : A → S → S) (i : S) (w : List A) : S :=
  w.foldl (fun s a => δ a s) i

/-- Execute a word of action/noise pairs, adding each noise after its update. -/
def noisyRun {A E : Type*} [Add E] (T : A → E → E) (h : E)
    (w : List (A × E)) : E :=
  w.foldl (fun x step => T step.1 x + step.2) h

/-- Separated finite code points admit globally smooth updates which reset each
closed decoding ball to the required target code point. Arbitrary bounded
post-update errors preserve the correct state and output at every prefix.
Only nonemptiness of the finite state set is needed; the action type is arbitrary. -/
theorem smooth_finite_machine_realization
    {S A Y : Type*} [Finite S] [Nonempty S] {d : ℕ}
    (δ : A → S → S) (y : S → Y) (c : S → EuclideanSpace ℝ (Fin d))
    (Δ ν r R : ℝ)
    (hsep : ∀ i j, i ≠ j → Δ ≤ ‖c i - c j‖)
    (hν : 0 ≤ ν) (hνr : ν < r) (hrR : r < R) (hRΔ : R < Δ / 2) :
    ∃ (T : A → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (decode : EuclideanSpace ℝ (Fin d) → S)
      (readout : EuclideanSpace ℝ (Fin d) → Y),
      (∀ a, ContDiff ℝ 1 (T a)) ∧
      (∀ a i h, ‖h - c i‖ ≤ r → T a h = c (δ a i)) ∧
      (∀ i h, ‖h - c i‖ ≤ r → decode h = i ∧ readout h = y i) ∧
      ∀ (w : List (A × EuclideanSpace ℝ (Fin d))),
        (∀ step ∈ w, ‖step.2‖ ≤ ν) →
        ∀ i h, ‖h - c i‖ ≤ r → ∀ n : ℕ,
          let pre := w.take n
          let s := symbolicRun δ i (pre.map Prod.fst)
          let x := noisyRun T h pre
          ‖x - c s‖ ≤ r ∧ decode x = s ∧ readout x = y s := by
  classical
  let : Fintype S := Fintype.ofFinite S
  have hr : 0 < r := lt_of_le_of_lt hν hνr
  let bump : (i : S) → ContDiffBump (c i) :=
    fun i => ⟨r, R, hr, hrR⟩
  let base : S := Classical.choice ‹Nonempty S›
  let T : A → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun a h => c base + ∑ i : S, bump i h • (c (δ a i) - c base)
  have isolated : ∀ i j h, i ≠ j → ‖h - c i‖ ≤ r →
      R ≤ dist h (c j) := by
    intro i j h hij hhi
    have htri := dist_triangle (c i) h (c j)
    have hdist : dist (c i) h ≤ r := by
      simpa only [dist_eq_norm, norm_sub_rev] using hhi
    have hsep' : Δ ≤ dist (c i) (c j) := by
      simpa only [dist_eq_norm] using hsep i j hij
    linarith
  have plateau : ∀ a i h, ‖h - c i‖ ≤ r → T a h = c (δ a i) := by
    intro a i h hhi
    have hone : bump i h = 1 :=
      (bump i).one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,
        dist_eq_norm] using hhi)
    have hsum : (∑ j : S, bump j h • (c (δ a j) - c base)) =
        c (δ a i) - c base := by
      rw [Finset.sum_eq_single i]
      · rw [hone, one_smul]
      · intro j _ hji
        rw [(bump j).zero_of_le_dist (isolated i j h hji.symm hhi), zero_smul]
      · simp
    dsimp only [T]
    rw [hsum]
    abel
  have unique : ∀ i j h, ‖h - c i‖ ≤ r → ‖h - c j‖ ≤ r → i = j := by
    intro i j h hi hj
    by_contra hij
    have hout := isolated i j h hij hi
    rw [dist_eq_norm] at hout
    linarith
  let decode : EuclideanSpace ℝ (Fin d) → S := fun h =>
    if hex : ∃ i, ‖h - c i‖ ≤ r then hex.choose else base
  have decode_ball : ∀ i h, ‖h - c i‖ ≤ r → decode h = i := by
    intro i h hi
    have hex : ∃ j, ‖h - c j‖ ≤ r := ⟨i, hi⟩
    simp only [decode, dif_pos hex]
    exact unique _ _ h hex.choose_spec hi
  have invariant : ∀ (w : List (A × EuclideanSpace ℝ (Fin d))),
      (∀ step ∈ w, ‖step.2‖ ≤ ν) → ∀ i h, ‖h - c i‖ ≤ r →
      ‖noisyRun T h w - c (symbolicRun δ i (w.map Prod.fst))‖ ≤ r := by
    intro w
    induction w with
    | nil => intro _ i h hi; exact hi
    | cons step w ih =>
      intro hw i h hi
      have hnoise := hw step (List.mem_cons_self ..)
      have hnext : ‖T step.1 h + step.2 - c (δ step.1 i)‖ ≤ r := by
        rw [plateau step.1 i h hi, add_sub_cancel_left]
        exact hnoise.trans hνr.le
      exact ih (fun e he => hw e (List.mem_cons_of_mem _ he))
        (δ step.1 i) (T step.1 h + step.2) hnext
  refine ⟨T, decode, y ∘ decode, ?_, plateau, ?_, ?_⟩
  · intro a
    apply contDiff_const.add
    exact ContDiff.sum (fun i _ => (bump i).contDiff.smul_const _)
  · intro i h hi
    exact ⟨decode_ball i h hi, congrArg y (decode_ball i h hi)⟩
  · intro w hw i h hi n
    have hp := invariant (w.take n)
      (fun step hs => hw step (List.mem_of_mem_take hs)) i h hi
    exact ⟨hp, decode_ball _ _ hp, congrArg y (decode_ball _ _ hp)⟩

end D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
