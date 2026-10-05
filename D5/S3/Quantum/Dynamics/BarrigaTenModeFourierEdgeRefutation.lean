/- GID: D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim; result=D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result; claim=D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim
   digest: Refutes the 25-edge lower bound of Barriga et al. for ten-mode Fourier transforms: a connected 23-edge real coupling matrix realizes F_10. -/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation

open Complex Matrix
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-- The ten-dimensional discrete Fourier transform, entries exp(-2πi x y / 10) / √10. -/
def F10 : Matrix (Fin 10) (Fin 10) ℂ := fun x y =>
  Complex.exp (-(2 * Real.pi * Complex.I * (x : ℕ) * (y : ℕ)) / 10) / Real.sqrt 10

/-- Number of edges of the support graph: unordered pairs x < y with H x y ≠ 0. -/
def edgeCount (H : Matrix (Fin 10) (Fin 10) ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
    (fun p => p.1 < p.2 ∧ H p.1 p.2 ≠ 0)).card

/-- The support graph of H. -/
def supportGraph (H : Matrix (Fin 10) (Fin 10) ℝ) : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun x y => H x y ≠ 0)

def IsUnimodularDiagonal (Φ : Matrix (Fin 10) (Fin 10) ℂ) : Prop :=
  ∃ z : Fin 10 → ℂ, (∀ x, ‖z x‖ = 1) ∧ Φ = Matrix.diagonal z

def claim : Prop :=
  ∀ H : Matrix (Fin 10) (Fin 10) ℝ, H.IsSymm →
    (∀ x y, x ≠ y → 0 ≤ H x y) → (supportGraph H).Connected →
    (∃ Φout Φin, IsUnimodularDiagonal Φout ∧ IsUnimodularDiagonal Φin ∧
      Φout * hamiltonianPropagator (H.map (↑)) 1 * Φin = F10) → 25 ≤ edgeCount H

private def s : ℝ := Real.sqrt 5
private def c : ℝ := (s - 1) / 4
private def d : ℝ := Real.sqrt (10 + 2 * s) / 4
private def ω : ℂ := (c : ℂ) + (d : ℂ) * I
private def q : ℝ := (21 * s - 65) / 20
private def r : ℝ := Real.sqrt (1 - q ^ 2)
private def γ : ℂ := (q : ℂ) + (r : ℂ) * I
private def a : ℝ := Real.pi * (35 - 13 * s) / 25
private def b : ℝ := Real.pi * (35 + 13 * s) / 25

private def C0 : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  if j = k then 0 else if (k.val + 5 - j.val) % 5 = 1 ∨
    (k.val + 5 - j.val) % 5 = 4 then a else b

private def P : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  ((γ * ω ^ ((j.val + k.val + 4) % 5)).re +
    (ω ^ ((j.val + 5 - k.val) % 5)).re) / 5

private def K : Matrix (Fin 5) (Fin 5) ℝ := C0 + (2 * Real.pi) • P


private def κ : Matrix (Fin 5) (Fin 5) ℝ :=
  let t := d * r
  !![2*t/5 - 43*s/100 + 5/4, 0, -2*t/5 - s/100 + 43/20,
      -t*s/5 + t/5 + 16*s/25 + 11/10, t*s/5 - t/5 - s/5 + 11/10;
    0, -2*t/5 - 43*s/100 + 5/4, -t*s/5 + t/5 - s/5 + 11/10,
      t*s/5 - t/5 + 16*s/25 + 11/10, 2*t/5 - s/100 + 43/20;
    -2*t/5 - s/100 + 43/20, -t*s/5 + t/5 - s/5 + 11/10,
      t*s/5 - t/5 + 11*s/50 + 1/5, 2*t/5 - 17*s/20 + 43/20, 21*s/25;
    -t*s/5 + t/5 + 16*s/25 + 11/10, t*s/5 - t/5 + 16*s/25 + 11/10,
      2*t/5 - 17*s/20 + 43/20, 21*s/50 - 9/10, -2*t/5 - 17*s/20 + 43/20;
    t*s/5 - t/5 - s/5 + 11/10, 2*t/5 - s/100 + 43/20, 21*s/25,
      -2*t/5 - 17*s/20 + 43/20, -t*s/5 + t/5 + 11*s/50 + 1/5]

private def H : Matrix (Fin 10) (Fin 10) ℝ := fun x y =>
  (if x.val % 2 = y.val % 2 then
    K ⟨x.val % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨y.val % 5, Nat.mod_lt _ (by norm_num)⟩ else 0) +
  (if x ≠ y ∧ x.val % 5 = y.val % 5 then Real.pi / 4 else 0)

private def edgeRel (x y : Fin 10) : Prop :=
  x ≠ y ∧ ((x.val % 2 = y.val % 2 ∧
    ¬((x = 0 ∧ y = 6) ∨ (x = 6 ∧ y = 0) ∨
      (x = 1 ∧ y = 5) ∨ (x = 5 ∧ y = 1))) ∨ x.val % 5 = y.val % 5)

private def z (x : Fin 10) : ℂ :=
  (-I) ^ (x.val % 2) * ω ^ (4 * (x.val % 5) ^ 2)

set_option maxHeartbeats 4000000 in
/-- A connected real symmetric nonnegative coupling matrix with 23 edges realizes `F10`
after diagonal phase shifts, refuting the claimed 25-edge lower bound. -/
theorem result : ¬ claim := by
  classical
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hd : d ^ 2 = (5 + s) / 8 := by
    have h := Real.sq_sqrt (show 0 ≤ 10 + 2 * s by linarith)
    dsimp [d]
    nlinarith
  have h2 : ω ^ 2 = (-(s + 1) / 4 : ℝ) + (((s - 1) * d / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [ω, c, pow_two, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd]
  have h3 : ω ^ 3 = (-(s + 1) / 4 : ℝ) - (((s - 1) * d / 2 : ℝ) : ℂ) * I := by
    rw [pow_succ, h2]
    apply Complex.ext <;> simp [ω, c, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd, show s ^ 2 * d = 5 * d by rw [hs], show s * (d ^ 2) = s * ((5 + s) / 8) by rw [hd]]
  have h4 : ω ^ 4 = (c : ℂ) - (d : ℂ) * I := by
    rw [pow_succ, h3]
    apply Complex.ext <;> simp [ω, c, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd, show s ^ 2 * d = 5 * d by rw [hs], show s * (d ^ 2) = s * ((5 + s) / 8) by rw [hd]]
  have h5 : ω ^ 5 = 1 := by
    rw [pow_succ, h4]
    apply Complex.ext <;> simp [ω, c, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hs, hd]
  have hK : K = Real.pi • κ := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [K, C0, P, κ, h2, h3, h4] <;>
      simp [a, b, γ, ω, c, q] <;>
      nlinarith [hs, show Real.pi * s ^ 2 = Real.pi * 5 by rw [hs]]
  have hs_bounds : 11 / 5 < s ∧ s < 9 / 4 := by
    constructor <;> nlinarith [hs]
  have hq_bounds : -1 < q ∧ q < -7 / 8 := by
    dsimp [q]
    constructor <;> linarith [hs_bounds.1, hs_bounds.2]
  have hr : r ^ 2 = 1 - q ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [hq_bounds.1, hq_bounds.2]
  have hr_bounds : 0 ≤ r ∧ r < 1 / 2 := by
    have hn : 0 ≤ r := Real.sqrt_nonneg _
    constructor
    · exact hn
    · nlinarith [hr, hq_bounds.1, hq_bounds.2]
  have hd_bounds : 0 ≤ d ∧ d < 1 := by
    have hn : 0 ≤ d := by dsimp [d]; positivity
    constructor
    · exact hn
    · nlinarith [hd, hs_bounds.2]
  have ht_bounds : 0 ≤ d * r ∧ d * r < 1 / 2 := by
    constructor
    · exact mul_nonneg hd_bounds.1 hr_bounds.1
    · nlinarith [mul_nonneg hd_bounds.1 hr_bounds.1]
  have hts_bounds : 0 ≤ d * r * s ∧ d * r * s < 9 / 8 := by
    constructor
    · exact mul_nonneg ht_bounds.1 hs_nonneg
    · nlinarith [ht_bounds.1, ht_bounds.2, hs_bounds.1, hs_bounds.2]
  have hκ_zero : ∀ j k : Fin 5, j ≠ k →
      (κ j k = 0 ↔ (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp [κ] at hjk ⊢ <;>
      nlinarith [hs_bounds.1, hs_bounds.2, ht_bounds.1, ht_bounds.2,
        hts_bounds.1, hts_bounds.2]
  have hκ_nonneg : ∀ j k : Fin 5, j ≠ k → 0 ≤ κ j k := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp [κ] at hjk ⊢ <;>
      nlinarith [hs_bounds.1, hs_bounds.2, ht_bounds.1, ht_bounds.2,
        hts_bounds.1, hts_bounds.2]
  have hsymm : H.IsSymm := by
    have hκ_symm : κ.IsSymm := by
      ext j k
      fin_cases j <;> fin_cases k <;> rfl
    have hK_symm : ∀ j k, K j k = K k j := by
      intro j k
      rw [hK]
      exact congrArg (fun t : ℝ => Real.pi * t) (congrFun (congrFun hκ_symm j) k).symm
    ext x y
    simp only [H, Matrix.transpose_apply]
    rw [hK_symm]
    simp only [eq_comm, ne_comm]

  have hnonneg : ∀ x y, x ≠ y → 0 ≤ H x y := by
    intro x y hxy
    unfold H
    apply add_nonneg
    · split_ifs with hp
      · rw [hK]
        apply mul_nonneg Real.pi_pos.le
        apply hκ_nonneg
        intro he
        have hm := congrArg Fin.val he
        change x.val % 5 = y.val % 5 at hm
        have hx := x.isLt
        have hy := y.isLt
        have hval : x.val = y.val := by omega
        exact hxy (Fin.ext hval)
      · exact le_refl 0
    · split_ifs <;> positivity

  have hH_nonzero : ∀ x y : Fin 10, x ≠ y → (H x y ≠ 0 ↔ edgeRel x y) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [H, hK, hκ_zero, edgeRel, Real.pi_ne_zero] at hxy ⊢
  have hgraph : ∀ x y, (supportGraph H).Adj x y ↔ edgeRel x y := by
    intro x y
    by_cases hxy : x = y
    · subst y
      simp [supportGraph, edgeRel]
    · simp only [supportGraph, SimpleGraph.fromRel_adj,
        hH_nonzero x y hxy, hH_nonzero y x (Ne.symm hxy)]
      have he : edgeRel y x ↔ edgeRel x y := by
        simp only [edgeRel, eq_comm, ne_comm]
        tauto
      rw [he, or_self]
      exact and_iff_right_of_imp (fun h => h.1)
  have hconnected : (supportGraph H).Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable (supportGraph H)).mpr
    refine ⟨2, ?_⟩
    have h27 : (supportGraph H).Reachable 2 7 :=
      ((hgraph 2 7).mpr (by unfold edgeRel; decide)).reachable
    intro x
    fin_cases x
    · exact ((hgraph 2 0).mpr (by unfold edgeRel; decide)).reachable
    · exact h27.trans ((hgraph 7 1).mpr (by unfold edgeRel; decide)).reachable
    · exact .refl 2
    · exact h27.trans ((hgraph 7 3).mpr (by unfold edgeRel; decide)).reachable
    · exact ((hgraph 2 4).mpr (by unfold edgeRel; decide)).reachable
    · exact h27.trans ((hgraph 7 5).mpr (by unfold edgeRel; decide)).reachable
    · exact ((hgraph 2 6).mpr (by unfold edgeRel; decide)).reachable
    · exact h27
    · exact ((hgraph 2 8).mpr (by unfold edgeRel; decide)).reachable
    · exact h27.trans ((hgraph 7 9).mpr (by unfold edgeRel; decide)).reachable

  have hphases : ∃ Φout Φin, IsUnimodularDiagonal Φout ∧ IsUnimodularDiagonal Φin ∧
      Φout * hamiltonianPropagator (H.map (↑)) 1 * Φin = F10 := by sorry
  have hedges : edgeCount H = 23 := by
    have he : ∀ p : Fin 10 × Fin 10,
        (p.1 < p.2 ∧ H p.1 p.2 ≠ 0) ↔ (p.1 < p.2 ∧ edgeRel p.1 p.2) := by
      intro p
      by_cases hp : p.1 < p.2
      · simp only [hp, true_and, hH_nonzero p.1 p.2 (ne_of_lt hp)]
      · simp only [hp, false_and]
    letI : DecidableRel edgeRel := fun x y => by unfold edgeRel; infer_instance
    have hc : ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
        (fun p => p.1 < p.2 ∧ edgeRel p.1 p.2)).card = 23 := by decide
    unfold edgeCount
    rw [← hc]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgeCount]
    exact he p

  intro h
  have hbound := h H hsymm hnonneg hconnected hphases
  rw [hedges] at hbound
  omega

end D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
