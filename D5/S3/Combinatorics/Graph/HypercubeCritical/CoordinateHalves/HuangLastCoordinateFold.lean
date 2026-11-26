/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The last-coordinate Huang fold gives integral transverse row constraints. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-! The unsigned last-coordinate flip preserves the signs of the Huang rows.
Adding and subtracting the reflected eigenvector gives two integral transverse equations. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangLastCoordinateFold

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip)
open ComponentBoundary.Q9IsotropicHuang (flipSign weightedAction)

/-- Flip the last bit of a vertex of the successor-dimensional cube. -/
def lastFlip {n : ℕ} (x : Q (n + 1)) : Q (n + 1) :=
  flip x (Fin.last n)

/-- The signed Huang row with the last coordinate omitted. -/
def transverseAction {n : ℕ} (f : Q (n + 1) → ℤ) (x : Q (n + 1)) : ℤ :=
  ∑ i : Fin n, flipSign i.castSucc x * f (flip x i.castSucc)

private theorem flipSign_flip_of_le {n : ℕ} (i j : Fin n) (hij : i ≤ j) (x : Q n) :
    flipSign i (flip x j) = flipSign i x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        have : (i : ℕ) + 1 ≤ 0 := hij
        omega
      | succ j =>
        have hhead : flip x j.succ 0 = x 0 := by
          simp [BalancedCriticalSpectrum.flip, (Fin.succ_ne_zero j).symm]
        have htail : Sensitivity.π (flip x j.succ) = flip (Sensitivity.π x) j := by
          funext k
          simp only [Sensitivity.π, BalancedCriticalSpectrum.flip, Function.comp_apply,
            Function.update_apply, Fin.succ_inj]
        change (if flip x j.succ 0 then 1 else -1) *
            flipSign i (Sensitivity.π (flip x j.succ)) =
          (if x 0 then 1 else -1) * flipSign i (Sensitivity.π x)
        rw [hhead, htail, ih i j (Fin.succ_le_succ_iff.mp hij)]

/-- The unsigned last-coordinate flip commutes with the full signed Huang action. -/
theorem last_flip_commutes {n : ℕ} (f : Q (n + 1) → ℤ) (x : Q (n + 1)) :
    (∑ i : Fin (n + 1), flipSign i x * (f ∘ lastFlip) (flip x i)) =
      ∑ i : Fin (n + 1), flipSign i (lastFlip x) * f (flip (lastFlip x) i) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, lastFlip, flipSign_flip_of_le i _ (Fin.le_last i),
    BalancedCubeGirth.flip_comm x i (Fin.last n)]

/-- The integer sum and difference with the reflected vector satisfy the two
transverse Huang equations, for any integer eigenvalue. -/
theorem transverseAction_channels {n : ℕ} {f : Q (n + 1) → ℤ} {eigenvalue : ℤ}
    (hf : ∀ x, (∑ i : Fin (n + 1), flipSign i x * f (flip x i)) = eigenvalue * f x)
    (x : Q (n + 1)) :
    transverseAction (f + f ∘ lastFlip) x =
        (eigenvalue - flipSign (Fin.last n) x) * (f x + f (lastFlip x)) ∧
      transverseAction (f - f ∘ lastFlip) x =
        (eigenvalue + flipSign (Fin.last n) x) * (f x - f (lastFlip x)) := by
  have splitRow (g : Q (n + 1) → ℤ)
      (hg : (∑ i : Fin (n + 1), flipSign i x * g (flip x i)) = eigenvalue * g x) :
      transverseAction g x + flipSign (Fin.last n) x * g (lastFlip x) =
        eigenvalue * g x := by
    simpa only [Fin.sum_univ_castSucc, transverseAction, lastFlip] using hg
  have original := splitRow f (hf x)
  have reflected := splitRow (f ∘ lastFlip) ((last_flip_commutes f x).trans (hf (lastFlip x)))
  simp only [Function.comp_apply, lastFlip, BalancedCriticalSpectrum.flip_flip] at reflected
  change transverseAction (f ∘ lastFlip) x + flipSign (Fin.last n) x * f x =
    eigenvalue * f (lastFlip x) at reflected
  constructor
  · calc
      _ = transverseAction f x + transverseAction (f ∘ lastFlip) x := by
        simp only [transverseAction, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      _ = _ := by linear_combination original + reflected
  · calc
      _ = transverseAction f x - transverseAction (f ∘ lastFlip) x := by
        simp only [transverseAction, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      _ = _ := by linear_combination original - reflected

/-- For a Huang 3-eigenvector on the nine-cube, the antisymmetric row is
divisible by four at a positive last edge, and zero at an equal axial pair. -/
theorem q9_antisymmetric_row {f : Q 9 → ℤ}
    (hf : weightedAction (fun _ => 1) f = (3 : ℤ) • f) (x : Q 9) :
    (flipSign (Fin.last 8) x = 1 → (4 : ℤ) ∣ transverseAction (f - f ∘ lastFlip) x) ∧
      (f x = f (lastFlip x) → transverseAction (f - f ∘ lastFlip) x = 0) := by
  have rows (y : Q 9) : (∑ i : Fin 9, flipSign i y * f (flip y i)) = 3 * f y := by
    simpa only [weightedAction, Int.cast_id, one_mul, Pi.smul_apply, smul_eq_mul]
      using congrFun hf y
  have h := (transverseAction_channels rows x).2
  constructor
  · intro hsign
    refine ⟨f x - f (lastFlip x), ?_⟩
    rw [h, hsign]
    norm_num
  · intro hagree
    rw [h, hagree, sub_self, mul_zero]

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangLastCoordinateFold
