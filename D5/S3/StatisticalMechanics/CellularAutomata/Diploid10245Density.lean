/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Diploid rule 10-245 has exact density 1/4 + λ/2 from time one. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density

def bit (b : Bool) : ℝ := if b then 1 else 0

def rule10 (x _y z : Bool) : Bool := (!x) && z

def rule245 (x y z : Bool) : Bool := !(rule10 x y z)

def p (lam : ℝ) (x y z : Bool) : ℝ :=
  (1 - lam) * bit (rule10 x y z) + lam * bit (rule245 x y z)

def w (lam : ℝ) (b x y z : Bool) : ℝ :=
  if b then p lam x y z else 1 - p lam x y z

/-- Independent simultaneous updates on an interval, with its two exterior parents. -/
def evolve (lam : ℝ) (R : (n : ℕ) → (Fin n → Bool) → ℝ)
    (n : ℕ) (b : Fin n → Bool) : ℝ :=
  ∑ a : Fin (n + 2) → Bool,
    (∏ j : Fin n, w lam (b j) (a j.castSucc.castSucc)
      (a j.succ.castSucc) (a j.succ.succ)) * R (n + 2) a

/-- The full cylinder hierarchy from the fair Bernoulli law, without periodic indexing. -/
def P (lam : ℝ) : ℕ → (n : ℕ) → (Fin n → Bool) → ℝ :=
  Nat.rec (motive := fun _ : ℕ => (n : ℕ) → (Fin n → Bool) → ℝ)
    (fun n _ => (1 / 2 : ℝ) ^ n) (fun _ R => evolve lam R)

def d (lam : ℝ) (t : ℕ) : ℝ := P lam t 1 (fun _ => true)

def CylinderLaw (lam : ℝ) : Prop :=
  (∀ t n (b : Fin n → Bool), 0 ≤ P lam t n b) ∧
  (∀ t n, (∑ b : Fin n → Bool, P lam t n b) = 1) ∧
  (∀ t n (b : Fin n → Bool),
    (∑ c : Bool, P lam t (n + 1) (Fin.snoc b c)) = P lam t n b) ∧
  (∀ t n (b : Fin n → Bool),
    (∑ c : Bool, P lam t (n + 1) (Fin.cons c b)) = P lam t n b)

/-- The exact density strengthens the asymptotic question in Fukś–Fatès, §5,
arXiv:2607.01917. CylinderLaw certifies the hierarchy's finite probability laws;
no separate infinite-product probability space is asserted here. -/
def claim : Prop :=
  ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    CylinderLaw lam ∧
    (∀ t : ℕ, 1 ≤ t → d lam t = 1 / 4 + lam / 2) ∧
    Tendsto (fun t : ℕ => d lam t) atTop (𝓝 (1 / 4 + lam / 2))

private def A (x z : Bool) : ℝ := (1 - bit x) * bit z

private def q (lam : ℝ) (t : ℕ) : ℝ :=
  ∑ c : Bool, P lam t 3 (Fin.cons false (Fin.cons c (Fin.cons true Fin.elim0)))

private theorem P_zero (lam : ℝ) (n : ℕ) (b : Fin n → Bool) :
    P lam 0 n b = (1 / 2 : ℝ) ^ n := rfl

private theorem P_succ (lam : ℝ) (t n : ℕ) (b : Fin n → Bool) :
    P lam (t + 1) n b = evolve lam (P lam t) n b := rfl

private theorem p_affine (lam : ℝ) (x y z : Bool) :
    p lam x y z = lam + (1 - 2 * lam) * A x z := by
  cases x <;> cases z
  all_goals simp [p, rule10, rule245, bit, A]
  all_goals ring

private theorem w_sum (lam : ℝ) (x y z : Bool) :
    (∑ b : Bool, w lam b x y z) = 1 := by
  rw [Fintype.sum_bool]
  change p lam x y z + (1 - p lam x y z) = 1
  ring

private theorem w_nonneg (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (b x y z : Bool) : 0 ≤ w lam b x y z := by
  obtain ⟨h0, h1⟩ := hlam
  cases b <;> cases x <;> cases z <;>
    simp [w, p, rule10, rule245, bit] <;> linarith

end D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density
