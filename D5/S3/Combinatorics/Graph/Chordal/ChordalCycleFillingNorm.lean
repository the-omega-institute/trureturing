/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalCycleFillingNorm
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/ChordalCycleFillingNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded triangle-flat cochains define a finite-dimensional norm on chains. -/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith

namespace SimpleGraph.ChordalReconstruction

open scoped BigOperators

noncomputable section

variable {I T : Type*} [Fintype I]

/-- The sum of the absolute values of the chain coordinates. -/
def mass (z : I → ℝ) : ℝ := ∑ i, |z i|

/-- Evaluate a coordinate cochain on a chain. -/
def pairing (f z : I → ℝ) : ℝ := ∑ i, f i * z i

/-- Cochains bounded on coordinates and on the given triangle chains. -/
def Admissible (triangle : T → I → ℝ) (f : I → ℝ) : Prop :=
  (∀ i, |f i| ≤ 3) ∧ ∀ t, |pairing f (triangle t)| ≤ 1

private theorem abs_pairing_le (f z : I → ℝ) (c : ℝ) (hf : ∀ i, |f i| ≤ c) :
    |pairing f z| ≤ c * mass z := by
  unfold pairing mass
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _)

private def values (triangle : T → I → ℝ) (z : I → ℝ) : Set ℝ :=
  {r | ∃ f, Admissible triangle f ∧ r = |pairing f z|}

private theorem values_nonempty (triangle : T → I → ℝ) (z : I → ℝ) :
    (values triangle z).Nonempty := by
  refine ⟨0, 0, ⟨fun _ => by norm_num, fun _ => by simp [pairing]⟩, ?_⟩
  simp [pairing]

private theorem values_bddAbove (triangle : T → I → ℝ) (z : I → ℝ) :
    BddAbove (values triangle z) :=
  ⟨3 * mass z, by rintro _ ⟨f, hf, rfl⟩; exact abs_pairing_le f z 3 hf.1⟩

/-- The dual norm obtained from bounded cochains of triangle defect at most one. -/
def dualNorm (triangle : T → I → ℝ) (z : I → ℝ) : ℝ := sSup (values triangle z)

theorem abs_pairing_le_dualNorm {triangle : T → I → ℝ} {f : I → ℝ}
    (hf : Admissible triangle f) (z : I → ℝ) : |pairing f z| ≤ dualNorm triangle z :=
  le_csSup (values_bddAbove triangle z) ⟨f, hf, rfl⟩

theorem dualNorm_triangle (triangle : T → I → ℝ) (t : T) : dualNorm triangle (triangle t) ≤ 1 := by
  apply csSup_le (values_nonempty triangle _)
  rintro _ ⟨f, hf, rfl⟩
  exact hf.2 t

theorem dualNorm_le_mass (triangle : T → I → ℝ) (z : I → ℝ) :
    dualNorm triangle z ≤ 3 * mass z :=
  csSup_le (values_nonempty triangle z) (fun _ ⟨f, hf, hr⟩ => hr.symm ▸ abs_pairing_le f z 3 hf.1)

theorem mass_le_dualNorm {triangle : T → I → ℝ} (h : ∀ t, mass (triangle t) ≤ 3)
    (z : I → ℝ) : mass z ≤ 3 * dualNorm triangle z := by
  let f (i : I) : ℝ := if 0 ≤ z i then 1 / 3 else -(1 / 3)
  have hf (i : I) : |f i| ≤ 1 / 3 := by
    unfold f
    split <;> norm_num
  have had : Admissible triangle f := by
    refine ⟨fun i => (hf i).trans (by norm_num), fun t => ?_⟩
    exact (abs_pairing_le f (triangle t) (1 / 3) hf).trans (by linarith [h t])
  have he : pairing f z = (1 / 3) * mass z := by
    unfold pairing mass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ z i
    · simp [f, hi, abs_of_nonneg hi]
    · simp [f, hi, abs_of_neg (lt_of_not_ge hi)]
  have hh := abs_pairing_le_dualNorm had z
  have hm : 0 ≤ mass z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [he, abs_of_nonneg (by positivity)] at hh
  linarith

/-- Real coordinate chains with the norm dual to the bounded admissible cochains. -/
def DualChains (triangle : T → I → ℝ) := I → ℝ

instance (triangle : T → I → ℝ) : AddCommGroup (DualChains triangle) :=
  inferInstanceAs (AddCommGroup (I → ℝ))
instance (triangle : T → I → ℝ) : Module ℝ (DualChains triangle) :=
  inferInstanceAs (Module ℝ (I → ℝ))
instance (triangle : T → I → ℝ) : FiniteDimensional ℝ (DualChains triangle) :=
  inferInstanceAs (FiniteDimensional ℝ (I → ℝ))
instance (triangle : T → I → ℝ) : Norm (DualChains triangle) := ⟨dualNorm triangle⟩

private theorem dualNorm_smul_le (triangle : T → I → ℝ) (a : ℝ) (z : I → ℝ) :
    dualNorm triangle (a • z) ≤ |a| * dualNorm triangle z := by
  apply csSup_le (values_nonempty triangle _)
  rintro _ ⟨f, hf, rfl⟩
  have he : pairing f (a • z) = a * pairing f z := by
    simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_pairing_le_dualNorm hf z) (abs_nonneg _)

private theorem dualNorm_zero (triangle : T → I → ℝ) :
    dualNorm triangle 0 = 0 :=
  le_antisymm (by simpa [mass] using dualNorm_le_mass triangle 0)
    (by
      have h : Admissible triangle (0 : I → ℝ) := by constructor <;> simp [pairing]
      simpa [pairing] using abs_pairing_le_dualNorm h (0 : I → ℝ))

/-- Norm structure for the cochain dual when all triangle chains have mass at most three. -/
def dualChainsCore (triangle : T → I → ℝ) (h : ∀ t, mass (triangle t) ≤ 3) :
    NormedSpace.Core ℝ (DualChains triangle) where
  norm_nonneg z :=
    (abs_nonneg _).trans (abs_pairing_le_dualNorm
      (f := 0) (by constructor <;> simp [pairing]) z)
  norm_triangle x y := by
    change dualNorm triangle (x + y) ≤ dualNorm triangle x + dualNorm triangle y
    apply csSup_le (values_nonempty triangle _)
    rintro _ ⟨f, hf, rfl⟩
    have he : pairing f (x + y) = pairing f x + pairing f y := by
      simp [pairing, mul_add, Finset.sum_add_distrib]
    rw [he]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_pairing_le_dualNorm hf x) (abs_pairing_le_dualNorm hf y))
  norm_smul a z := by
    change dualNorm triangle (a • z) = ‖a‖ * dualNorm triangle z
    rw [Real.norm_eq_abs]
    refine le_antisymm (dualNorm_smul_le triangle a z) ?_
    by_cases ha : a = 0
    · simp [ha, dualNorm_zero]
    have hi := dualNorm_smul_le triangle a⁻¹ (a • z)
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv, ← div_eq_inv_mul,
      le_div_iff₀ (abs_pos.mpr ha), mul_comm] at hi
    exact hi
  norm_eq_zero_iff z := by
    change dualNorm triangle z = 0 ↔ z = 0
    refine ⟨fun hz => ?_, fun hz => hz ▸ dualNorm_zero triangle⟩
    funext i
    have hm := mass_le_dualNorm h (show I → ℝ from z)
    rw [hz, mul_zero] at hm
    exact abs_nonpos_iff.mp
      ((Finset.single_le_sum (f := fun j => |z j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)).trans hm)

end

end SimpleGraph.ChordalReconstruction
