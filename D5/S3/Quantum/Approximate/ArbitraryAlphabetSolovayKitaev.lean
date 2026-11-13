/- GID: D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev
   generality: G
   mirror-B: D5/B/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev
   mirror-E: none(waiver:stage-a-candidate)
   anchors: []
   utility: none
   digest: Ordinary-word approximation over finite dense inverse-closed SU(2) alphabets. -/

/-
Attributed algebraic support: Csd@9b2d2c17e926ae13795119c5f2f62e85ea240c2d.
Original files: CsdLean4/Mathlib/QuantumInfo/SU2Rotation.lean and
CsdLean4/Mathlib/QuantumInfo/CommutatorDecomposition.lean,
CsdLean4/Mathlib/QuantumInfo/CliffordTNet.lean,
CsdLean4/Mathlib/Analysis/CStarAlgebra/GroupCommutator.lean, and
CsdLean4/Mathlib/QuantumInfo/SolovayKitaevStep.lean.
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore.
Full license: docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
Only the SU(2) quaternion identities needed by this candidate are retained.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Tactic

/-! # Arbitrary finite-alphabet ordinary-word Solovay–Kitaev candidate -/

@[expose] public section

open Matrix
open Metric Set
open scoped Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Approximate.ArbitraryAlphabetSolovayKitaev

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The unit-quaternion matrix used by the licensed SU(2) support. -/
noncomputable def su2 (w x y z : ℝ) : Mat2 :=
  !![(w : ℂ) - Complex.I * z, -Complex.I * ((x : ℂ) - Complex.I * y);
     -Complex.I * ((x : ℂ) + Complex.I * y), (w : ℂ) + Complex.I * z]

/-- Quaternion multiplication in matrix form. -/
theorem su2_mul (w x y z w' x' y' z' : ℝ) :
    su2 w x y z * su2 w' x' y' z' =
      su2 (w * w' - x * x' - y * y' - z * z') (w * x' + x * w' + y * z' - z * y')
        (w * y' - x * z' + y * w' + z * x') (w * z' + x * y' - y * x' + z * w') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    constructor <;> ring

theorem su2_one : su2 1 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2]

theorem su2_det (w x y z : ℝ) :
    (su2 w x y z).det = ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) := by
  rw [su2, Matrix.det_fin_two_of]
  push_cast
  simp [Complex.ext_iff, ← Complex.ofReal_pow]
  constructor <;> ring

/-- Rotation by `theta` about a unit axis. -/
noncomputable def axisRot (a b c θ : ℝ) : Mat2 :=
  su2 (Real.cos (θ / 2)) (a * Real.sin (θ / 2))
    (b * Real.sin (θ / 2)) (c * Real.sin (θ / 2))

theorem axisRot_det {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    (axisRot a b c θ).det = 1 := by
  rw [axisRot, su2_det,
    show Real.cos (θ / 2) ^ 2 + (a * Real.sin (θ / 2)) ^ 2
        + (b * Real.sin (θ / 2)) ^ 2 + (c * Real.sin (θ / 2)) ^ 2 = 1 by
      linear_combination (Real.sin (θ / 2)) ^ 2 * hu + Real.sin_sq_add_cos_sq (θ / 2)]
  norm_num

theorem su2_star (w x y z : ℝ) : star (su2 w x y z) = su2 w (-x) (-y) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Matrix.star_apply, Complex.ext_iff]

theorem su2_mem_unitary {w x y z : ℝ}
    (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) : su2 w x y z ∈ unitary Mat2 := by
  rw [Unitary.mem_iff]
  constructor
  · rw [su2_star, su2_mul, ← su2_one]
    congr 1 <;> (first | linear_combination hu | linear_combination -hu | ring)
  · rw [su2_star, su2_mul, ← su2_one]
    congr 1 <;> (first | linear_combination hu | linear_combination -hu | ring)

theorem axisRot_mem_unitary {a b c : ℝ}
    (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) : axisRot a b c θ ∈ unitary Mat2 := by
  apply su2_mem_unitary
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2), hu]

/-!
The finite-net lemma is the compactness step from the licensed CSD source
`CsdLean4/Mathlib/QuantumInfo/CliffordTNet.lean` (Apache 2.0, Zayn Blore).
It is retained here because the receiver has no imported generic statement.
-/
theorem compact_exists_finite_net {X : Type*} [MetricSpace X] {K D : Set X}
    (hK : IsCompact K) (hKD : K ⊆ closure D) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset X, (↑F : Set X) ⊆ D ∧ ∀ x ∈ K, ∃ y ∈ F, dist x y < ε := by
  have hcover : K ⊆ ⋃ y ∈ D, ball y ε := by
    intro x hx
    obtain ⟨y, hyD, hdist⟩ := Metric.mem_closure_iff.1 (hKD hx) ε hε
    exact mem_biUnion hyD (by rwa [mem_ball])
  obtain ⟨b, hbD, hbfin, hbcover⟩ :=
    hK.elim_finite_subcover_image (fun _ _ => isOpen_ball) hcover
  refine ⟨hbfin.toFinset, ?_, ?_⟩
  · intro y hy
    exact hbD (hbfin.mem_toFinset.1 hy)
  · intro x hx
    obtain ⟨y, hyb, hxy⟩ := Set.mem_iUnion₂.1 (hbcover hx)
    exact ⟨y, hbfin.mem_toFinset.2 hyb, mem_ball.1 hxy⟩

/-!
The following perturbation estimates are the minimal licensed stability support from
`CsdLean4/Mathlib/QuantumInfo/SolovayKitaevStep.lean` and its
`CsdLean4/Mathlib/Analysis/CStarAlgebra/GroupCommutator.lean` prerequisite.
-/

theorem norm_mul_sub_mul_comm_le (V W : Mat2) :
    ‖V * W - W * V‖ ≤ 2 * ‖V - 1‖ * ‖W - 1‖ := by
  have key : V * W - W * V = (V - 1) * (W - 1) - (W - 1) * (V - 1) := by
    noncomm_ring
  rw [key]
  calc
    ‖(V - 1) * (W - 1) - (W - 1) * (V - 1)‖
        ≤ ‖(V - 1) * (W - 1)‖ + ‖(W - 1) * (V - 1)‖ := norm_sub_le _ _
    _ ≤ ‖V - 1‖ * ‖W - 1‖ + ‖W - 1‖ * ‖V - 1‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖V - 1‖ * ‖W - 1‖ := by ring

theorem groupCommutator_sub_one_eq {V W : Mat2} (hV : V ∈ unitary Mat2)
    (hW : W ∈ unitary Mat2) :
    V * W * star V * star W - 1 = (V * W - W * V) * (star V * star W) := by
  have h1 : W * V * (star V * star W) = 1 := by
    rw [show W * V * (star V * star W) = W * (V * star V) * star W from by noncomm_ring,
      Unitary.mul_star_self_of_mem hV, mul_one, Unitary.mul_star_self_of_mem hW]
  rw [sub_mul, h1]
  noncomm_ring

theorem norm_groupCommutator_sub_le_basic {V W : Mat2}
    (hV : V ∈ unitary Mat2) (hW : W ∈ unitary Mat2) :
    ‖V * W * star V * star W - 1‖ ≤ 2 * ‖V - 1‖ * ‖W - 1‖ := by
  rw [groupCommutator_sub_one_eq hV hW,
    CStarRing.norm_mul_mem_unitary _ (mul_mem (Unitary.star_mem hV) (Unitary.star_mem hW))]
  exact norm_mul_sub_mul_comm_le V W

theorem norm_mul_sub_mul_le_weighted (A B A' B' : Mat2) :
    ‖A * B - A' * B'‖ ≤ ‖A - A'‖ * ‖B‖ + ‖A'‖ * ‖B - B'‖ := by
  have key : A * B - A' * B' = (A - A') * B + A' * (B - B') := by
    noncomm_ring
  rw [key]
  exact le_trans (norm_add_le _ _) (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

theorem norm_mul_sub_mul_comm_sub_le {V W V' W' : Mat2} {a δ : ℝ}
    (haW : ‖W - 1‖ ≤ a) (haV' : ‖V' - 1‖ ≤ a) (haV : ‖V - 1‖ ≤ a)
    (haW' : ‖W' - 1‖ ≤ a) (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖(V * W - W * V) - (V' * W' - W' * V')‖ ≤ 4 * a * δ := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδV
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) haV
  have hid : (V * W - W * V) - (V' * W' - W' * V')
      = ((V - 1) * (W - 1) - (V' - 1) * (W' - 1))
        - ((W - 1) * (V - 1) - (W' - 1) * (V' - 1)) := by
    noncomm_ring
  have h1 : ‖(V - 1) * (W - 1) - (V' - 1) * (W' - 1)‖ ≤ 2 * a * δ := by
    refine le_trans (norm_mul_sub_mul_le_weighted (V - 1) (W - 1) (V' - 1) (W' - 1)) ?_
    have e1 : (V - 1) - (V' - 1) = V - V' := by noncomm_ring
    have e2 : (W - 1) - (W' - 1) = W - W' := by noncomm_ring
    rw [e1, e2]
    nlinarith [mul_le_mul hδV haW (norm_nonneg _) hδ0,
      mul_le_mul haV' hδW (norm_nonneg _) ha0]
  have h2 : ‖(W - 1) * (V - 1) - (W' - 1) * (V' - 1)‖ ≤ 2 * a * δ := by
    refine le_trans (norm_mul_sub_mul_le_weighted (W - 1) (V - 1) (W' - 1) (V' - 1)) ?_
    have e1 : (W - 1) - (W' - 1) = W - W' := by noncomm_ring
    have e2 : (V - 1) - (V' - 1) = V - V' := by noncomm_ring
    rw [e1, e2]
    nlinarith [mul_le_mul hδW haV (norm_nonneg _) hδ0,
      mul_le_mul haW' hδV (norm_nonneg _) ha0]
  rw [hid]
  calc
    ‖((V - 1) * (W - 1) - (V' - 1) * (W' - 1))
        - ((W - 1) * (V - 1) - (W' - 1) * (V' - 1))‖
        ≤ ‖(V - 1) * (W - 1) - (V' - 1) * (W' - 1)‖
          + ‖(W - 1) * (V - 1) - (W' - 1) * (V' - 1)‖ := norm_sub_le _ _
    _ ≤ 2 * a * δ + 2 * a * δ := add_le_add h1 h2
    _ = 4 * a * δ := by ring

theorem norm_groupCommutator_sub_le {V W V' W' : Mat2}
    (hV : V ∈ unitary Mat2) (hW : W ∈ unitary Mat2)
    (hV' : V' ∈ unitary Mat2) (hW' : W' ∈ unitary Mat2) {a δ : ℝ}
    (haV : ‖V - 1‖ ≤ a) (haW : ‖W - 1‖ ≤ a)
    (haV' : ‖V' - 1‖ ≤ a) (haW' : ‖W' - 1‖ ≤ a)
    (hδV : ‖V - V'‖ ≤ δ) (hδW : ‖W - W'‖ ≤ δ) :
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖ ≤
      4 * a * δ * (1 + a) := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδV
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) haV
  have hsplit : V * W * star V * star W - V' * W' * star V' * star W'
      = ((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)
        + (V' * W' - W' * V') * (star V * star W - star V' * star W') := by
    have h1 : V * W * star V * star W = 1 + (V * W - W * V) * (star V * star W) := by
      rw [← groupCommutator_sub_one_eq hV hW]
      abel
    have h2 : V' * W' * star V' * star W' =
        1 + (V' * W' - W' * V') * (star V' * star W') := by
      rw [← groupCommutator_sub_one_eq hV' hW']
      abel
    rw [h1, h2]
    noncomm_ring
  have hQu : (star V * star W) ∈ unitary Mat2 :=
    mul_mem (Unitary.star_mem hV) (Unitary.star_mem hW)
  have hP : ‖((V * W - W * V) - (V' * W' - W' * V')) *
      (star V * star W)‖ ≤ 4 * a * δ := by
    rw [CStarRing.norm_mul_mem_unitary _ hQu]
    exact norm_mul_sub_mul_comm_sub_le haW haV' haV haW' hδV hδW
  have hP' : ‖V' * W' - W' * V'‖ ≤ 2 * a * a := by
    refine le_trans (norm_mul_sub_mul_comm_le V' W') ?_
    nlinarith [mul_le_mul haV' haW' (norm_nonneg _) ha0]
  have hQ : ‖star V * star W - star V' * star W'‖ ≤ 2 * δ := by
    have e1 : ‖star V - star V'‖ ≤ δ := by rw [← star_sub, norm_star]; exact hδV
    have e2 : ‖star W - star W'‖ ≤ δ := by rw [← star_sub, norm_star]; exact hδW
    refine le_trans (norm_mul_sub_mul_le_weighted (star V) (star W) (star V') (star W')) ?_
    rw [CStarRing.norm_of_mem_unitary (Unitary.star_mem hW),
      CStarRing.norm_of_mem_unitary (Unitary.star_mem hV'), mul_one, one_mul]
    nlinarith [e1, e2]
  calc
    ‖V * W * star V * star W - V' * W' * star V' * star W'‖
        ≤ ‖((V * W - W * V) - (V' * W' - W' * V')) * (star V * star W)‖
          + ‖(V' * W' - W' * V') * (star V * star W - star V' * star W')‖ := by
            rw [hsplit]
            exact norm_add_le _ _
    _ ≤ 4 * a * δ + (2 * a * a) * (2 * δ) := by
      refine add_le_add hP ?_
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul hP' hQ (norm_nonneg _) (by positivity)
    _ = 4 * a * δ * (1 + a) := by ring

/-- A literal inverse-letter selector need only choose an inverse, not be involutive. -/
def inverseWord {m : ℕ} (inverseLetter : Fin m → Fin m) (w : List (Fin m)) : List (Fin m) :=
  w.reverse.map inverseLetter

/-- Actual ordinary words, evaluated left-to-right as `Gamma i * eval tail`. -/
def evalGamma {m : ℕ} (Gamma : Fin m → Mat2) : List (Fin m) → Mat2
  | [] => 1
  | i :: w => Gamma i * evalGamma Gamma w

@[simp] theorem evalGamma_nil {m : ℕ} (Gamma : Fin m → Mat2) :
    evalGamma Gamma [] = 1 := rfl

@[simp] theorem evalGamma_cons {m : ℕ} (Gamma : Fin m → Mat2) (i : Fin m) (w : List (Fin m)) :
    evalGamma Gamma (i :: w) = Gamma i * evalGamma Gamma w := rfl

theorem evalGamma_append {m : ℕ} (Gamma : Fin m → Mat2) (u v : List (Fin m)) :
    evalGamma Gamma (u ++ v) = evalGamma Gamma u * evalGamma Gamma v := by
  induction u with
  | nil => simp
  | cons i u ih => simp [ih, mul_assoc]

theorem evalGamma_inverseWord {m : ℕ} (Gamma : Fin m → Mat2)
    (inverseLetter : Fin m → Fin m)
    (hinverse : ∀ i, Gamma (inverseLetter i) = star (Gamma i))
    (w : List (Fin m)) :
    evalGamma Gamma (inverseWord inverseLetter w) = star (evalGamma Gamma w) := by
  induction w with
  | nil => simp [inverseWord, evalGamma]
  | cons i w ih =>
      rw [inverseWord, List.reverse_cons, List.map_append, evalGamma_append]
      simp only [List.map_cons, List.map_nil, evalGamma_cons, evalGamma_nil, mul_one]
      have ih' : evalGamma Gamma (List.map inverseLetter w.reverse) =
          star (evalGamma Gamma w) := by
        simpa [inverseWord] using ih
      rw [ih', hinverse]
      rw [← star_mul]

theorem inverseWord_length {m : ℕ} (inverseLetter : Fin m → Fin m)
    (w : List (Fin m)) : (inverseWord inverseLetter w).length = w.length := by
  simp [inverseWord]

/-- The produced successor word required by the registered event. -/
def balancedCommutatorWord {m : ℕ} (inverseLetter : Fin m → Fin m)
    (v w u : List (Fin m)) : List (Fin m) :=
  v ++ w ++ inverseWord inverseLetter v ++ inverseWord inverseLetter w ++ u

theorem eval_balancedCommutatorWord {m : ℕ} (Gamma : Fin m → Mat2)
    (inverseLetter : Fin m → Fin m)
    (hinverse : ∀ i, Gamma (inverseLetter i) = star (Gamma i))
    (v w u : List (Fin m)) :
    evalGamma Gamma (balancedCommutatorWord inverseLetter v w u) =
      evalGamma Gamma v * evalGamma Gamma w * star (evalGamma Gamma v) *
        star (evalGamma Gamma w) * evalGamma Gamma u := by
  simp only [balancedCommutatorWord, evalGamma_append, evalGamma_inverseWord Gamma
    inverseLetter hinverse, mul_assoc]

/-- The exact exponent required by the event. -/
noncomputable def skExponent : ℝ := Real.log 5 / Real.log (3 / 2)

/-- Determinant-one unitaries in the fixed two-dimensional matrix carrier. -/
def SU2 (U : Mat2) : Prop := U ∈ unitary Mat2 ∧ U.det = 1

/-! ### Compactness and the finite actual-word base net -/

def SU2Set : Set Mat2 := {U | SU2 U}

theorem isClosed_SU2Set : IsClosed SU2Set := by
  rw [show SU2Set = (unitary Mat2 : Set Mat2) ∩ (fun U : Mat2 => U.det) ⁻¹' ({1} : Set ℂ) by
    rfl]
  exact (isClosed_unitary (R := Mat2)).inter
    (isClosed_singleton.preimage continuous_id.matrix_det)

theorem su2Set_subset_closedBall : SU2Set ⊆ Metric.closedBall (0 : Mat2) 1 := by
  intro U hU
  rw [mem_closedBall_zero_iff]
  rw [CStarRing.norm_of_mem_unitary hU.1]

theorem isCompact_SU2Set : IsCompact SU2Set :=
  (isCompact_closedBall (0 : Mat2) 1).of_isClosed_subset
    isClosed_SU2Set su2Set_subset_closedBall

/-- The registered density premise, including the zero-letter case. -/
def DenseAlphabet {m : ℕ} (Gamma : Fin m → Mat2) : Prop :=
  ∀ U, SU2 U → ∀ η : ℝ, 0 < η → ∃ w : List (Fin m),
    ‖U - evalGamma Gamma w‖ < η

theorem SU2Set_subset_closure_evalGamma {m : ℕ} (Gamma : Fin m → Mat2)
    (hDense : DenseAlphabet Gamma) : SU2Set ⊆ closure (Set.range (evalGamma Gamma)) := by
  intro U hU
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨w, hw⟩ := hDense U hU η hη
  refine ⟨evalGamma Gamma w, ⟨w, rfl⟩, ?_⟩
  simpa [dist_eq_norm] using hw

/-! A choice of one actual word for each matrix in the finite net. -/

theorem exists_finite_word_net {m : ℕ} (Gamma : Fin m → Mat2)
    (hDense : DenseAlphabet Gamma) {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset (List (Fin m)), ∃ L₀ : ℕ,
      (∀ w ∈ F, w.length ≤ L₀) ∧
        ∀ U, SU2 U → ∃ w ∈ F, ‖U - evalGamma Gamma w‖ < η := by
  classical
  obtain ⟨A, hAsub, hAnet⟩ :=
    compact_exists_finite_net isCompact_SU2Set
      (SU2Set_subset_closure_evalGamma Gamma hDense) hη
  let wordOf : Mat2 → List (Fin m) := fun A =>
    if hA : A ∈ Set.range (evalGamma Gamma) then Classical.choose hA else []
  let F : Finset (List (Fin m)) := A.image wordOf
  let L₀ : ℕ := F.sup List.length
  have hwordOf_eval {A : Mat2} (hA : A ∈ Set.range (evalGamma Gamma)) :
      evalGamma Gamma (wordOf A) = A := by
    simp only [wordOf, dite_eq_left hA]
    exact Classical.choose_spec hA
  refine ⟨F, L₀, ?_, ?_⟩
  · intro w hw
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.le_sup (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
  · intro U hU
    obtain ⟨A, hA, hdist⟩ := hAnet U hU
    have hArange : A ∈ Set.range (evalGamma Gamma) := hAsub hA
    refine ⟨wordOf A, Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
    rw [hwordOf_eval hArange]
    simpa [dist_eq_norm] using hdist

/-- The exact ordinary-word conclusion, with one same witness in both bounds. -/
def UniformPolylog {m : ℕ} (Gamma : Fin m → Mat2) : Prop :=
  ∃ K ε₀ : ℝ, 0 < K ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ U, SU2 U → ∃ w : List (Fin m),
      ‖U - evalGamma Gamma w‖ ≤ ε ∧
      (w.length : ℝ) ≤ K * (Real.log (1 / ε)) ^ skExponent

/-- The exact preregistered event, without any quantitative or physical strengthening. -/
def OrdinaryWordSolovayKitaevEvent : Prop :=
  ∀ m : ℕ, ∀ Gamma : Fin m → Mat2,
    (∀ i, SU2 (Gamma i)) →
    (∀ i, ∃ j, Gamma j = star (Gamma i)) →
    DenseAlphabet Gamma → UniformPolylog Gamma

/-- A residual is formed from the previous-level word, as required by the event. -/
def residual {m : ℕ} (Gamma : Fin m → Mat2) (U : Mat2) (u : List (Fin m)) : Mat2 :=
  U * star (evalGamma Gamma u)

/-- The same-level successor has the literal five-piece ordinary list. -/
def successorWord {m : ℕ} (inverseLetter : Fin m → Fin m)
    (v w u : List (Fin m)) : List (Fin m) :=
  balancedCommutatorWord inverseLetter v w u

theorem successorWord_length {m : ℕ} (inverseLetter : Fin m → Fin m)
    (v w u : List (Fin m)) :
    (successorWord inverseLetter v w u).length =
      v.length + w.length + v.length + w.length + u.length := by
  simp only [successorWord, balancedCommutatorWord, List.length_append, inverseWord_length]

end
end D5.S3.Quantum.Approximate.ArbitraryAlphabetSolovayKitaev
