/- GID: D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev
   generality: G
   mirror-B: D5/B/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev
   mirror-E: none(waiver:kernel-checked-content)
   anchors: []
   utility: none
   digest: Ordinary-word approximation over finite dense inverse-closed SU(2) alphabets. -/

/-
Attributed algebraic support: Csd@9b2d2c17e926ae13795119c5f2f62e85ea240c2d.
Source files:
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/CliffordTWords.lean
(original QuantumInfo.SU2.ctEval, ctInvWord, skWords and
length_le_of_mem_skWords, used as proof sources for ordinary-list operations),
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/CliffordTNet.lean
(original QuantumInfo.SU2.compact_exists_finite_net),
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/Analysis/CStarAlgebra/GroupCommutator.lean
(original CStarRing.norm_mul_sub_mul_comm_le and groupCommutator_sub_one_eq),
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/SolovayKitaevStep.lean
(original CSD.SolovayKitaev.norm_mul_sub_mul_le', norm_mul_sub_mul_comm_sub_le,
and norm_groupCommutator_sub_le), and
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/SolovayKitaevCount.lean
(original QuantumInfo.SU2.exists_mem_skWords_norm_sub_le and
exists_word_approx_polylog, used as proof sources for the alphabet-parametric construction).
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore.
Full license: docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
The compact-net and stability estimates are licensed reuse. Quaternion decomposition
and scalar rate estimates are in the two directly imported support modules.
-/


import D5.S3.Quantum.Approximate.BalancedSU2Commutator
import D5.S3.Quantum.Approximate.SolovayKitaevRate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import Mathlib.Tactic

/-! # Arbitrary finite-alphabet ordinary-word Solovay–Kitaev approximation -/


open Matrix
open Metric Set
open scoped Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Approximate.ArbitraryAlphabetSolovayKitaev

noncomputable section

open BalancedSU2Commutator SolovayKitaevRate

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-!
The finite-net lemma is the compactness step from the licensed CSD source
`CsdLean4/Mathlib/QuantumInfo/CliffordTNet.lean` (Apache 2.0, Zayn Blore).
The net points lie in the dense set; no quantitative cardinality is asserted.
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

@[simp] theorem evalGamma_cons {m : ℕ} (Gamma : Fin m → Mat2) (i : Fin m) (w : List (Fin m)) :
    evalGamma Gamma (i :: w) = Gamma i * evalGamma Gamma w := rfl

theorem evalGamma_append {m : ℕ} (Gamma : Fin m → Mat2) (u v : List (Fin m)) :
    evalGamma Gamma (u ++ v) = evalGamma Gamma u * evalGamma Gamma v := by
  induction u with
  | nil => simp [evalGamma]
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
      simp only [List.map_cons, List.map_nil, evalGamma_cons, evalGamma, mul_one]
      have ih' : evalGamma Gamma (List.map inverseLetter w.reverse) =
          star (evalGamma Gamma w) := by
        simpa [inverseWord] using ih
      rw [ih', hinverse]
      rw [← star_mul]

theorem inverseWord_length {m : ℕ} (inverseLetter : Fin m → Fin m)
    (w : List (Fin m)) : (inverseWord inverseLetter w).length = w.length := by
  simp [inverseWord]

/-- The literal five-piece ordinary successor list. -/
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

/-- Determinant-one unitaries in the fixed two-dimensional matrix carrier. -/
def SU2 (U : Mat2) : Prop := U ∈ unitary Mat2 ∧ U.det = 1

/-! ### Compactness and the finite actual-word base net -/

def SU2Set : Set Mat2 := {U | SU2 U}

theorem isClosed_SU2Set : IsClosed SU2Set := by
  rw [show SU2Set = (unitary Mat2 : Set Mat2) ∩ (fun U : Mat2 => U.det) ⁻¹' ({1} : Set ℂ) by
    rfl]
  exact (isClosed_unitary (R := Mat2)).inter
    (isClosed_singleton.preimage continuous_id.matrix_det)

theorem isCompact_SU2Set : IsCompact SU2Set := by
  have hc : IsCompact (unitary Mat2 : Set Mat2) :=
    isCompact_iff_compactSpace.mpr
      (D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.unitaryCompactSpace (n := Fin 2))
  exact hc.of_isClosed_subset isClosed_SU2Set (fun _ hU => hU.1)

/-- Density of ordinary words, including the zero-letter case. -/
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

/-- The uniform approximation assertion over all finite SU(2) alphabets. -/
def OrdinaryWordSolovayKitaevEvent : Prop :=
  ∀ m : ℕ, ∀ Gamma : Fin m → Mat2,
    (∀ i, SU2 (Gamma i)) →
    (∀ i, ∃ j, Gamma j = star (Gamma i)) →
    DenseAlphabet Gamma → UniformPolylog Gamma

/-- Residual formed from the previous-level approximation to the target. -/
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


/-- Every ordinary word in determinant-one unitary generators stays in SU(2). -/
theorem evalGamma_SU2 {m : ℕ} (Gamma : Fin m → Mat2)
    (hGamma : ∀ i, SU2 (Gamma i)) (u : List (Fin m)) : SU2 (evalGamma Gamma u) := by
  induction u with
  | nil => exact ⟨one_mem _, Matrix.det_one⟩
  | cons i u ih =>
      exact ⟨mul_mem (hGamma i).1 ih.1, by
        rw [evalGamma_cons, Matrix.det_mul, (hGamma i).2, ih.2, mul_one]⟩

/--
One ordinary list has both the recursive approximation error and the actual length bound.
The construction follows the licensed CSD ordinary-word induction in
SolovayKitaevCount.exists_mem_skWords_norm_sub_le, with an arbitrary alphabet and
an existential inverse selector. Determinant one is preserved by every letter.
-/
theorem exists_word_at_level {m : ℕ} (Gamma : Fin m → Mat2)
    (hGamma : ∀ i, SU2 (Gamma i)) (inverseLetter : Fin m → Fin m)
    (hinverse : ∀ i, Gamma (inverseLetter i) = star (Gamma i))
    {e : ℝ} (he : 0 ≤ e) (hsmall : Real.sqrt e ≤ 1 / 33) {L₀ : ℕ}
    (hnet : ∀ U, SU2 U → ∃ u : List (Fin m),
      ‖U - evalGamma Gamma u‖ ≤ e ∧ u.length ≤ L₀) (n : ℕ) :
    ∀ U, SU2 U → ∃ u : List (Fin m),
      ‖U - evalGamma Gamma u‖ ≤ skErr e n ∧ u.length ≤ 5 ^ n * L₀ := by
  induction n with
  | zero =>
      intro U hU
      simpa using hnet U hU
  | succ n ih =>
      intro U hU
      obtain ⟨u, hdu, hlu⟩ := ih U hU
      have hε0 : 0 ≤ skErr e n := skErr_nonneg he n
      have hεe : skErr e n ≤ e := skErr_le_base he hsmall n
      have hAu := evalGamma_SU2 Gamma hGamma u
      have hΔu : residual Gamma U u ∈ unitary Mat2 :=
        mul_mem hU.1 (Unitary.star_mem hAu.1)
      have hΔdet : (residual Gamma U u).det = 1 := by
        rw [residual, Matrix.det_mul, Matrix.star_eq_conjTranspose,
          Matrix.det_conjTranspose, hU.2, hAu.2, star_one, one_mul]
      have hΔeq1 : residual Gamma U u - 1 =
          (U - evalGamma Gamma u) * star (evalGamma Gamma u) := by
        rw [sub_mul, Unitary.mul_star_self_of_mem hAu.1]
        rfl
      have hΔnorm : ‖residual Gamma U u - 1‖ = ‖U - evalGamma Gamma u‖ := by
        rw [hΔeq1, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hAu.1)]
      have hΔle : ‖residual Gamma U u - 1‖ ≤ skErr e n := by
        rw [hΔnorm]
        exact hdu
      obtain ⟨V, W, hVu, hWu, hVd, hWd, hΔfactor, hVb, hWb⟩ :=
        exists_commutator_of_det_one hΔu hΔdet
      obtain ⟨v, hdv, hlv⟩ := ih V ⟨hVu, hVd⟩
      obtain ⟨w, hdw, hlw⟩ := ih W ⟨hWu, hWd⟩
      have hcvu := (evalGamma_SU2 Gamma hGamma v).1
      have hcwu := (evalGamma_SU2 Gamma hGamma w).1
      have hmul : Real.sqrt 2 * Real.sqrt ‖residual Gamma U u - 1‖
          ≤ Real.sqrt 2 * Real.sqrt (skErr e n) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hΔle) (Real.sqrt_nonneg 2)
      have haV : ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        linarith
      have haW : ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        linarith
      have haV' : ‖evalGamma Gamma v - 1‖ ≤
          Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        calc ‖evalGamma Gamma v - 1‖
            ≤ ‖evalGamma Gamma v - V‖ + ‖V - 1‖ := by
              have h : evalGamma Gamma v - 1 = evalGamma Gamma v - V + (V - 1) := by abel
              rw [h]
              exact norm_add_le _ _
          _ ≤ skErr e n + Real.sqrt 2 * Real.sqrt ‖residual Gamma U u - 1‖ := by
            rw [norm_sub_rev (evalGamma Gamma v) V]
            exact add_le_add hdv hVb
          _ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by linarith
      have haW' : ‖evalGamma Gamma w - 1‖ ≤
          Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        calc ‖evalGamma Gamma w - 1‖
            ≤ ‖evalGamma Gamma w - W‖ + ‖W - 1‖ := by
              have h : evalGamma Gamma w - 1 = evalGamma Gamma w - W + (W - 1) := by abel
              rw [h]
              exact norm_add_le _ _
          _ ≤ skErr e n + Real.sqrt 2 * Real.sqrt ‖residual Gamma U u - 1‖ := by
            rw [norm_sub_rev (evalGamma Gamma w) W]
            exact add_le_add hdw hWb
          _ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by linarith
      have hcomm := norm_groupCommutator_sub_le hVu hWu hcvu hcwu
        haV haW haV' haW' hdv hdw
      have hUfac : U = (V * W * star V * star W) * evalGamma Gamma u := by
        rw [← hΔfactor, residual, mul_assoc, Unitary.star_mul_self_of_mem hAu.1, mul_one]
      refine ⟨successorWord inverseLetter v w u, ?_, ?_⟩
      · have hsplitU : U - evalGamma Gamma (successorWord inverseLetter v w u)
            = (V * W * star V * star W -
                evalGamma Gamma v * evalGamma Gamma w * star (evalGamma Gamma v) *
                  star (evalGamma Gamma w)) * evalGamma Gamma u := by
          rw [successorWord, eval_balancedCommutatorWord Gamma inverseLetter hinverse,
            hUfac, sub_mul]
        rw [hsplitU, CStarRing.norm_mul_mem_unitary _ hAu.1, skErr_succ]
        refine le_trans hcomm (step_bound hε0 ?_)
        have h33 := le_trans (Real.sqrt_le_sqrt hεe) hsmall
        linarith
      · rw [successorWord_length, pow_succ]
        nlinarith

/--
Every finite inverse-closed dense determinant-one unitary alphabet has the uniform
ordinary-word bound, with the same list in its error and actual length inequalities.
The error and logarithmic rate estimates are licensed CSD reuse; the word invariant
is alphabet-parametric. This asserts existence with no effective or runtime bound.
-/
theorem ordinary_word_solovay_kitaev : OrdinaryWordSolovayKitaevEvent := by
  intro m Gamma hGamma hclosed hDense
  classical
  choose inverseLetter hinverse using hclosed
  let e : ℝ := 1 / 2178
  have he0 : 0 < e := by norm_num [e]
  have hsqrt : Real.sqrt e ≤ 1 / 33 := by
    calc Real.sqrt e ≤ Real.sqrt (1 / 1089) := Real.sqrt_le_sqrt (by norm_num [e])
      _ = 1 / 33 := by
        rw [show (1 : ℝ) / 1089 = (1 / 33) ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num)]
  obtain ⟨F, l₀, hFlen, hFnet⟩ := exists_finite_word_net Gamma hDense he0
  have hnet : ∀ U, SU2 U → ∃ w : List (Fin m),
      ‖U - evalGamma Gamma w‖ ≤ e ∧ w.length ≤ l₀ := by
    intro U hU
    obtain ⟨w, hw, hd⟩ := hFnet U hU
    exact ⟨w, hd.le, hFlen w hw⟩
  obtain ⟨b, hb_eq⟩ : ∃ b : ℝ, b = 1089 * e := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb_eq]; positivity
  have hb1 : b < 1 := by rw [hb_eq]; norm_num [e]
  have hlb : Real.log b < 0 := Real.log_neg hb0 hb1
  have hlogb : 0 < Real.log b⁻¹ := by rw [Real.log_inv]; linarith
  have hKpos : 0 < 5 * ((l₀ : ℝ) + 1) / (Real.log b⁻¹) ^ skExponent :=
    div_pos (by positivity) (Real.rpow_pos_of_pos hlogb _)
  refine ⟨5 * ((l₀ : ℝ) + 1) / (Real.log b⁻¹) ^ skExponent, e, hKpos, he0, by norm_num [e], ?_⟩
  intro ε hε hεe U hU
  have h1089ε : 0 < 1089 * ε := by positivity
  have hεb : 1089 * ε ≤ b := by rw [hb_eq]; linarith

  have hclosed := skError_le_rpow (show (0 : ℝ) < 33 by norm_num)
    (skErr_nonneg he0.le) (fun k => le_of_eq (skErr_succ e k)) (skLevel b (1089 * ε))
  have hbase : (33 : ℝ) ^ 2 * skErr e 0 = b := by rw [skErr_zero, hb_eq]; norm_num
  rw [hbase] at hclosed
  have hreach : b ^ ((3 / 2 : ℝ) ^ skLevel b (1089 * ε)) ≤ 1089 * ε :=
    skLevel_rpow_le hb0 hb1 h1089ε hεb
  have herr : skErr e (skLevel b (1089 * ε)) ≤ ε := by
    have h1 : (1089 : ℝ) * skErr e (skLevel b (1089 * ε)) ≤ 1089 * ε := by
      calc (1089 : ℝ) * skErr e (skLevel b (1089 * ε))
          = (33 : ℝ) ^ 2 * skErr e (skLevel b (1089 * ε)) := by norm_num
        _ ≤ b ^ ((3 / 2 : ℝ) ^ skLevel b (1089 * ε)) := hclosed
        _ ≤ 1089 * ε := hreach
    linarith

  obtain ⟨u, hdu, hlu⟩ :=
    exists_word_at_level Gamma hGamma inverseLetter hinverse he0.le hsqrt
      hnet (skLevel b (1089 * ε)) U hU
  refine ⟨u, le_trans hdu herr, ?_⟩
  have hlenR : (u.length : ℝ) ≤ 5 ^ skLevel b (1089 * ε) * (l₀ : ℝ) := by
    exact_mod_cast hlu
  have hfive : (5 : ℝ) ^ skLevel b (1089 * ε)
      ≤ 5 * (Real.log (1089 * ε) / Real.log b) ^ skExponent :=
    five_pow_skLevel_le hb0 hb1 h1089ε hεb

  have hinv : Real.log (1 / ε) / Real.log b⁻¹ = Real.log ε / Real.log b := by
    simp only [one_div, Real.log_inv, neg_div_neg_eq]
  have hratio : Real.log (1089 * ε) / Real.log b ≤ Real.log (1 / ε) / Real.log b⁻¹ := by
    rw [hinv, Real.log_mul (by norm_num) (ne_of_gt hε)]
    have hdiff : Real.log ε / Real.log b - (Real.log 1089 + Real.log ε) / Real.log b
        = -Real.log 1089 / Real.log b := by
      rw [div_sub_div_same]
      congr 1
      ring
    have hnn : 0 ≤ -Real.log 1089 / Real.log b := by
      refine div_nonneg_iff.2 (Or.inr ⟨?_, hlb.le⟩)
      simp [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1089)]
    linarith [hdiff, hnn]
  have hr0' : 0 ≤ Real.log (1089 * ε) / Real.log b := (log_ratio_pos hb0 hb1 h1089ε hεb).le
  have hlogεinv : 0 ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv]
    have : Real.log ε < 0 := Real.log_neg hε (by linarith)
    linarith
  have hpow : (Real.log (1089 * ε) / Real.log b) ^ skExponent
      ≤ (Real.log (1 / ε)) ^ skExponent / (Real.log b⁻¹) ^ skExponent := by
    rw [← Real.div_rpow hlogεinv hlogb.le]
    exact Real.rpow_le_rpow hr0' hratio skExponent_pos.le
  calc (u.length : ℝ) ≤ 5 ^ skLevel b (1089 * ε) * (l₀ : ℝ) := hlenR
    _ ≤ (5 * (Real.log (1089 * ε) / Real.log b) ^ skExponent) * ((l₀ : ℝ) + 1) :=
        mul_le_mul hfive (by linarith) (by positivity)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hr0' _))
    _ ≤ (5 * ((Real.log (1 / ε)) ^ skExponent / (Real.log b⁻¹) ^ skExponent)) * ((l₀ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith [hpow]) (by positivity)
    _ = 5 * ((l₀ : ℝ) + 1) / (Real.log b⁻¹) ^ skExponent * (Real.log (1 / ε)) ^ skExponent := by
        ring


end
end D5.S3.Quantum.Approximate.ArbitraryAlphabetSolovayKitaev
