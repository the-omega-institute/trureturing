/- GID: D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit
   mirror-E: none(waiver:formal-unit-only)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Finite tournament path transfer, reflection, padding and the defect-spectrum convergence criterion. -/

import D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit

open Filter Matrix

abbrev IsTournament {V : Type*} (R : V → V → Prop) : Prop :=
  D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence.IsTournament R

/-- True encodes a forward edge, false a backward edge. -/
def flips : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: w => (if a = b then 0 else 1) + flips (b :: w)

/-- All vertex maps are allowed; only the arc conditions constrain a map. -/
def ArcPreserving {N : ℕ} (R : Fin N → Fin N → Prop) (w : List Bool)
    (φ : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ i : Fin w.length,
    if w[i] then R (φ i.castSucc) (φ i.succ) else R (φ i.succ) (φ i.castSucc)

noncomputable def homCount {N : ℕ} (R : Fin N → Fin N → Prop) (w : List Bool) : ℕ :=
  Nat.card {φ : Fin (w.length + 1) → Fin N // ArcPreserving R w φ}

noncomputable def homDensity {N : ℕ} (R : Fin N → Fin N → Prop) (w : List Bool) : ℝ :=
  (homCount R w : ℝ) / (N : ℝ) ^ (w.length + 1)

def TAS (w : List Bool) : Prop :=
  ∀ N : ℕ, 0 < N → ∀ R : Fin N → Fin N → Prop,
    IsTournament R → homDensity R w ≤ (1 / 2 : ℝ) ^ w.length

noncomputable def thresholds (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (k + 1)).filter fun m =>
    ∀ w : List Bool, w.length = k → flips w < m → TAS w

private theorem thresholds_nonempty (k : ℕ) : (thresholds k).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp [thresholds]

/-- The source's exact maximum, including its strict flip threshold. -/
noncomputable def f (k : ℕ) : ℕ := (thresholds k).max' (thresholds_nonempty k)

/-- Its value at zero is immaterial: the quantifiers below only use positive lengths. -/
def FullConvergence : Prop :=
  ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 1 ≤ K ∧
    ∀ k : ℕ, K ≤ k → |(f k : ℝ) / (k : ℝ) - L| < ε

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]

def step (A : Matrix V V ℝ) (b : Bool) : Matrix V V ℝ := if b then A else Aᵀ

def transfer (A : Matrix V V ℝ) (w : List Bool) : Matrix V V ℝ :=
  (w.map (step A)).prod

def mass (M : Matrix V V ℝ) : ℝ :=
  (∑ i, ∑ j, M i j) / (Fintype.card V : ℝ)

def reflect (w : List Bool) : List Bool := w.reverse.map Bool.not

theorem transfer_append (A : Matrix V V ℝ) (u v : List Bool) :
    transfer A (u ++ v) = transfer A u * transfer A v := by
  simp [transfer]

private theorem step_not (A : Matrix V V ℝ) (b : Bool) :
    step A (!b) = (step A b)ᵀ := by
  cases b <;> simp [step]

theorem transfer_reflect (A : Matrix V V ℝ) (w : List Bool) :
    transfer A (reflect w) = (transfer A w)ᵀ := by
  induction w with
  | nil => simp [reflect, transfer]
  | cons b w ih =>
    simp only [reflect, List.reverse_cons, List.map_append, List.map_singleton]
    rw [transfer_append]
    change transfer A (reflect w) * step A (!b) = (step A b * transfer A w)ᵀ
    rw [ih, step_not, Matrix.transpose_mul]

theorem reflected_pair_transfer (A : Matrix V V ℝ) (w : List Bool) :
    transfer A (w ++ reflect w) = transfer A w * (transfer A w)ᵀ := by
  rw [transfer_append, transfer_reflect]

theorem transfer_nonneg (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (w : List Bool) : ∀ i j, 0 ≤ transfer A w i j := by
  induction w with
  | nil => intro i j; simp [transfer, Matrix.one_apply]; split_ifs <;> norm_num
  | cons b w ih =>
    intro i j
    change 0 ≤ (step A b * transfer A w) i j
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (ih x j)
    cases b <;> simp [step, hA]

/-- A nonnegative reflected transfer has average at least the square of the old average. -/
theorem reflected_mass_sq_le (B : Matrix V V ℝ) [Nonempty V] :
    (mass B) ^ 2 ≤ mass (B * Bᵀ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : V => (1 : ℝ)) (fun j : V => ∑ i, B i j)
  have hs : (∑ i, ∑ j, (B * Bᵀ) i j) = ∑ j, (∑ i, B i j) ^ 2 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext j
    rw [Finset.sum_comm]
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  rw [Finset.sum_comm] at hcs
  dsimp [mass]
  rw [hs, div_pow]
  apply (div_le_div_iff₀ (pow_pos hN 2) hN).mpr
  nlinarith

end Transfer

section DefectSpectrum

/-- Every realizable defect contributes its flip count plus the cost of one join. -/
def defectSpectrum (Bad : ℕ → ℕ → Prop) : Set ℝ :=
  {x | x = 1 ∨ ∃ k r : ℕ, 0 < k ∧ Bad k r ∧ x = ((r : ℝ) + 1) / (k : ℝ)}

noncomputable def defectLimit (Bad : ℕ → ℕ → Prop) : ℝ := sInf (defectSpectrum Bad)

private theorem spectrum_nonempty (Bad : ℕ → ℕ → Prop) :
    (defectSpectrum Bad).Nonempty := ⟨1, Or.inl rfl⟩

private theorem spectrum_bddBelow (Bad : ℕ → ℕ → Prop) :
    BddBelow (defectSpectrum Bad) := by
  refine ⟨0, ?_⟩
  rintro x (rfl | ⟨k, r, hk, _, rfl⟩)
  · norm_num
  · positivity

/-- The analytic final step only needs eventual propagation of each finite defect.
The tournament application must still supply that propagation from its transfer matrices. -/
theorem convergence_of_defect_propagation (F : ℕ → ℕ) (Bad : ℕ → ℕ → Prop)
    (hbounded : ∀ k, F k ≤ k)
    (hwitness : ∀ k, 0 < k → F k < k → Bad k (F k))
    (hpropagate : ∀ k r, 0 < k → Bad k r → ∀ δ : ℝ, 0 < δ →
      ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 < n →
        (F n : ℝ) / (n : ℝ) < ((r : ℝ) + 1) / (k : ℝ) + δ) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 1 ≤ K ∧ ∀ n : ℕ, K ≤ n →
      |(F n : ℝ) / (n : ℝ) - defectLimit Bad| < ε := by
  intro ε hε
  have hL1 : defectLimit Bad ≤ 1 := csInf_le (spectrum_bddBelow Bad) (Or.inl rfl)
  have hnear := exists_lt_of_csInf_lt (spectrum_nonempty Bad)
    (show defectLimit Bad < defectLimit Bad + ε / 2 by linarith)
  obtain ⟨x, hx, hxlt⟩ := hnear
  have hupper : ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 < n →
      (F n : ℝ) / (n : ℝ) < defectLimit Bad + ε := by
    rcases hx with rfl | ⟨k, r, hk, hbad, rfl⟩
    · refine ⟨1, ?_⟩
      intro n _ hn
      have hrat : (F n : ℝ) / (n : ℝ) ≤ 1 :=
        (div_le_one (Nat.cast_pos.mpr hn)).mpr (Nat.cast_le.mpr (hbounded n))
      linarith
    · obtain ⟨K, hK⟩ := hpropagate k r hk hbad (ε / 2) (by linarith)
      exact ⟨K, fun n hn hp => lt_trans (hK n hn hp) (by linarith)⟩
  obtain ⟨Kupper, hKupper⟩ := hupper
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
  refine ⟨max Kupper (M + 1), by omega, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hinv : 1 / (n : ℝ) < ε := by
    apply lt_of_le_of_lt _ hM
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (M : ℝ) + 1)
    exact_mod_cast (show M + 1 ≤ n by omega)
  have hlower : defectLimit Bad - ε < (F n : ℝ) / (n : ℝ) := by
    by_cases hlt : F n < n
    · have hm : ((F n : ℝ) + 1) / (n : ℝ) ∈ defectSpectrum Bad :=
        Or.inr ⟨n, F n, hnpos, hwitness n hnpos hlt, rfl⟩
      have hL := csInf_le (spectrum_bddBelow Bad) hm
      rw [add_div] at hL
      linarith
    · have heq : F n = n := by have := hbounded n; omega
      rw [heq, div_self (ne_of_gt hnreal)]
      linarith
  exact abs_lt.mpr ⟨by linarith, by
    have := hKupper n (by omega) hnpos
    linarith⟩

end DefectSpectrum

end D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit
