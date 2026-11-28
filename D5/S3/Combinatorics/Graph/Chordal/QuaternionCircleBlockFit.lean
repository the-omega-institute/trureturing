/- GID: D5/S3/Combinatorics/Graph/Chordal/QuaternionCircleBlockFit
   generality: G
   mirror-B: none(waiver:covered-by-circle-coefficient-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Circle-valued gains admit potential fits on alternating orthogonal quaternion lines. -/

import D5.S3.Geometry.UnitQuaternionCircle
import D5.S3.Combinatorics.Graph.Chordal.ChordalScalarFit

/-! Omega original.

Circle-valued gains can be fitted on alternating orthogonal quaternion lines.
-/

open scoped Quaternion InnerProductSpace
noncomputable section

namespace SimpleGraph.CirclePowerPath

open Real Omega.Geometry.UnitQuaternion

variable {V : Type*} {G : SimpleGraph V}

/-- Ambient potentials take values in the entire unit three-sphere. -/
def Fits (G : SimpleGraph V) (g : V → V → U) (p : V → U) (r : ℝ) : Prop :=
  ∀ i j, G.Adj i j → roundDist (g i j) ((p i)⁻¹ * p j) ≤ r

def TriangleBound (G : SimpleGraph V) (g : V → V → U) (δ : ℝ) : Prop :=
  ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
    roundDist (g i j * g j k) (g i k) ≤ δ

/-- A real lift with the stated triangle bound suffices for a circle potential. -/
theorem fit_of_real_lift [Finite V] (hG : G.IsChordal)
    (a : V → V → ℝ) (hrev : ∀ i j, G.Adj i j → a j i = -a i j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      |a i j + a j k - a i k| ≤ δ) :
    ∃ p : V → U, Fits G (fun i j => phase (a i j)) p δ := by
  obtain ⟨f, hf⟩ := exists_scalar_fit hG a hrev hδ htri
  refine ⟨fun i => phase (f i), fun i j hij => ?_⟩
  rw [← phase_neg, ← phase_add]
  exact (phase_dist_le _ _).trans (by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hf i j hij)

/-- The second complex line in the quaternion model. -/
def jUnit : U := ofUnit ⟨0, 0, 1, 0⟩ (by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  norm_num [Quaternion.normSq_def])

def blockPoint (odd : Bool) (t : ℝ) : U := if odd then jUnit * phase t else phase t

theorem blockPoint_same (odd : Bool) (s t u : ℝ) :
    roundDist (blockPoint odd s * phase t) (blockPoint odd u) =
      roundDist (phase s * phase t) (phase u) := by
  cases odd <;> simp [blockPoint, mul_assoc, round_mul_left]

theorem blockPoint_cross {odd even : Bool} (hne : odd ≠ even) (s t u : ℝ) :
    roundDist (blockPoint odd s * phase t) (blockPoint even u) = π / 2 := by
  cases odd <;> cases even
  all_goals first
    | exact (hne rfl).elim
    | simp [blockPoint, roundDist, Quaternion.inner_def, phase, ofUnit,
        jUnit]

/-- Alternating orthogonal lines fit all inter-block edges at exactly `π / 2`.
Only same-block edges use a triangle bound. -/
theorem alternating_blocks_fit (b : V → V → ℝ)
    (hdiag : ∀ i, phase (b i i) = 1)
    (hrev : ∀ i j, G.Adj i j → phase (b j i) = (phase (b i j))⁻¹)
    (block : V → ℕ) (anchor : V → V)
    (hanchor : ∀ i, anchor i = i ∨ G.Adj (anchor i) i)
    (hanchor_eq : ∀ i j, block i = block j → anchor i = anchor j)
    (hedge : ∀ i j, G.Adj i j → block i = block j ∨
      block i + 1 = block j ∨ block j + 1 = block i)
    {δ : ℝ} (hδ : 0 ≤ δ) (htri : TriangleBound G (fun i j => phase (b i j)) δ) :
    ∃ p : V → U, Fits G (fun i j => phase (b i j)) p (max δ (π / 2)) := by
  let odd (i : V) : Bool := decide (block i % 2 = 1)
  let p (i : V) := blockPoint (odd i) (b (anchor i) i)
  refine ⟨p, fun i j hij => ?_⟩
  rw [round_edge]
  by_cases heq : block i = block j
  · have ha := hanchor_eq i j heq
    have ho : odd i = odd j := by simp [odd, heq]
    change roundDist (blockPoint (odd i) (b (anchor i) i) * phase (b i j))
      (blockPoint (odd j) (b (anchor j) j)) ≤ _
    rw [← ha, ← ho, blockPoint_same]
    apply le_trans ?_ (le_max_left _ _)
    rcases hanchor i with hai | hai
    · rw [hai, hdiag, one_mul, round_self]
      exact hδ
    · rcases hanchor j with haj | haj
      · rw [← ha] at haj
        rw [haj, hrev i j hij, inv_mul_cancel, hdiag, round_self]
        exact hδ
      · rw [← ha] at haj
        exact htri _ _ _ hai hij haj
  · have hop : odd i ≠ odd j := by
      have hh := hedge i j hij
      simp only [odd, ne_eq, decide_eq_decide] at *
      omega
    change roundDist (blockPoint (odd i) (b (anchor i) i) * phase (b i j))
      (blockPoint (odd j) (b (anchor j) j)) ≤ _
    rw [blockPoint_cross hop]
    exact le_max_right _ _

end SimpleGraph.CirclePowerPath
