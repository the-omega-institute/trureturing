/- GID: D5/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/SimplexTwoCochainL2Projection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact tetrahedral energy and its optimal residual-energy coefficient. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection

universe u

/-- Contraction of an ordered triangle cochain in its first vertex. -/
noncomputable def contraction {V : Type u} [Fintype V]
    (F : V → V → V → ℝ) (i j : V) : ℝ := ∑ r : V, F r i j

/-- The mean of the anchored edge cochains. -/
noncomputable def averageEdge {V : Type u} [Fintype V]
    (F : V → V → V → ℝ) (i j : V) : ℝ :=
  contraction F i j / (Fintype.card V : ℝ)

/-- The ordered coboundary of an edge cochain. -/
def edgeCoboundary {V : Type u} (a : V → V → ℝ) (i j k : V) : ℝ :=
  a j k - a i k + a i j

/-- The ordered coboundary of a triangle cochain. -/
def tetraDefect {V : Type u} (F : V → V → V → ℝ) (r i j k : V) : ℝ :=
  F i j k - F r j k + F r i k - F r i j

set_option maxHeartbeats 800000 in
-- The local energy calculation and determinant witness share one elaboration budget.
/-- The ordered defect energy equals `4 * |V|` times the averaged residual
energy, and this coefficient is optimal whenever there are at least four vertices. -/
theorem tetra_defect_energy_eq_and_optimal
    {V : Type u} [Fintype V] [Nonempty V] :
    (∀ (F : V → V → V → ℝ)
      (h12 : ∀ i j k, F j i k = -F i j k)
      (h23 : ∀ i j k, F i k j = -F i j k),
      (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
        (tetraDefect F r i j k) ^ 2) =
        4 * (Fintype.card V : ℝ) *
          (∑ i : V, ∑ j : V, ∑ k : V,
            (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2)) ∧
    (4 ≤ Fintype.card V → ∀ C : ℝ,
      (∀ (F : V → V → V → ℝ)
        (h12 : ∀ i j k, F j i k = -F i j k)
        (h23 : ∀ i j k, F i k j = -F i j k),
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
          (tetraDefect F r i j k) ^ 2) ≤
          C * (∑ i : V, ∑ j : V, ∑ k : V,
            (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2)) →
      4 * (Fintype.card V : ℝ) ≤ C) := by
  classical
  have hequality (F : V → V → V → ℝ)
      (h12 : ∀ i j k, F j i k = -F i j k)
      (h23 : ∀ i j k, F i k j = -F i j k) :
      (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
        (tetraDefect F r i j k) ^ 2) =
        4 * (Fintype.card V : ℝ) *
          (∑ i : V, ∑ j : V, ∑ k : V,
            (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2) := by
    let n : ℝ := Fintype.card V
    let S : V → V → ℝ := contraction F
    let a : V → V → ℝ := averageEdge F
    let R : V → V → V → ℝ :=
      fun i j k => F i j k - edgeCoboundary a i j k
    have hn : n ≠ 0 := by
      change (Fintype.card V : ℝ) ≠ 0
      exact_mod_cast Fintype.card_ne_zero (α := V)
    have hSskew (i j : V) : S j i = -S i j := by
      change (∑ r : V, F r j i) = -(∑ r : V, F r i j)
      calc
        _ = ∑ r : V, -F r i j := by
          apply Finset.sum_congr rfl
          intro r _
          exact h23 r i j
        _ = _ := by rw [Finset.sum_neg_distrib]
    have hSdiv (j : V) : (∑ i : V, S i j) = 0 := by
      have hneg : (∑ i : V, ∑ r : V, F r i j) =
          -(∑ i : V, ∑ r : V, F r i j) := by
        calc
          _ = ∑ r : V, ∑ i : V, F r i j := Finset.sum_comm
          _ = ∑ r : V, ∑ i : V, -F i r j := by
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro i _
            exact h12 i r j
          _ = -(∑ i : V, ∑ r : V, F r i j) := by simp
      change (∑ i : V, ∑ r : V, F r i j) = 0
      linarith
    have haskew (i j : V) : a j i = -a i j := by
      change S j i / n = -(S i j / n)
      rw [hSskew]
      ring
    have hadiv (j : V) : (∑ i : V, a i j) = 0 := by
      change (∑ i : V, S i j / n) = 0
      rw [← Finset.sum_div]
      rw [hSdiv]
      simp
    have hcarda (i j : V) : n * a i j = S i j := by
      change n * (S i j / n) = S i j
      field_simp
    have hRfirst (i j : V) : (∑ r : V, R r i j) = 0 := by
      have hsum : (∑ r : V, edgeCoboundary a r i j) = S i j := by
        simp only [edgeCoboundary, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        rw [hadiv j, hadiv i]
        simp only [sub_zero, Finset.sum_const, Finset.card_univ]
        simpa [n, nsmul_eq_mul] using hcarda i j
      change (∑ r : V, (F r i j - edgeCoboundary a r i j)) = 0
      rw [Finset.sum_sub_distrib]
      change S i j - (∑ r : V, edgeCoboundary a r i j) = 0
      rw [hsum]
      ring
    have hR12 (i j k : V) : R j i k = -R i j k := by
      change F j i k - (a i k - a j k + a j i) =
        -(F i j k - (a j k - a i k + a i j))
      rw [h12, haskew i j]
      ring
    have hR23 (i j k : V) : R i k j = -R i j k := by
      change F i k j - (a k j - a i j + a i k) =
        -(F i j k - (a j k - a i k + a i j))
      rw [h23, haskew j k]
      ring
    have hRsecond (i k : V) : (∑ j : V, R i j k) = 0 := by
      calc
        _ = ∑ j : V, -R j i k := by
          apply Finset.sum_congr rfl
          intro j _
          exact hR12 j i k
        _ = 0 := by simp [hRfirst]
    have hRthird (i j : V) : (∑ k : V, R i j k) = 0 := by
      calc
        _ = ∑ k : V, -R i k j := by
          apply Finset.sum_congr rfl
          intro k _
          exact hR23 i k j
        _ = 0 := by simp [hRsecond]
    let E : ℝ := ∑ i : V, ∑ j : V, ∑ k : V, (R i j k) ^ 2
    have diagA :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, (R i j k) ^ 2) = n * E := by
      simp [E, n, Finset.sum_const, nsmul_eq_mul]
    have diagB :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, (R r j k) ^ 2) = n * E := by
      simp [E, n, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    have diagC :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, (R r i k) ^ 2) = n * E := by
      simp [E, n, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    have diagD :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, (R r i j) ^ 2) = n * E := by
      simp [E, n, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    have crossAB :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, R i j k * R r j k) = 0 := by
      calc
        _ = ∑ r : V, ∑ j : V, ∑ k : V, ∑ i : V, R i j k * R r j k := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
        _ = 0 := by simp [← Finset.sum_mul, hRfirst]
    have crossAC :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, R i j k * R r i k) = 0 := by
      calc
        _ = ∑ r : V, ∑ i : V, ∑ k : V, ∑ j : V, R i j k * R r i k := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = 0 := by simp [← Finset.sum_mul, hRsecond]
    have crossAD :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, R i j k * R r i j) = 0 := by
      simp [← Finset.sum_mul, hRthird]
    have crossBC :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, R r j k * R r i k) = 0 := by
      calc
        _ = ∑ r : V, ∑ i : V, ∑ k : V, ∑ j : V, R r j k * R r i k := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = 0 := by simp [← Finset.sum_mul, hRsecond]
    have crossBD :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, R r j k * R r i j) = 0 := by
      simp [← Finset.sum_mul, hRthird]
    have crossCD :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V, R r i k * R r i j) = 0 := by
      simp [← Finset.sum_mul, hRthird]
    have henergy :
        (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
          (tetraDefect R r i j k) ^ 2) = 4 * n * E := by
      have expand (r i j k : V) :
          (tetraDefect R r i j k) ^ 2 =
            (R i j k) ^ 2 + (R r j k) ^ 2 + (R r i k) ^ 2 + (R r i j) ^ 2
            - 2 * (R i j k * R r j k) + 2 * (R i j k * R r i k)
            - 2 * (R i j k * R r i j) - 2 * (R r j k * R r i k)
            + 2 * (R r j k * R r i j) - 2 * (R r i k * R r i j) := by
        unfold tetraDefect
        ring
      simp_rw [expand]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [diagA, diagB, diagC, diagD,
        crossAB, crossAC, crossAD, crossBC, crossBD, crossCD]
      ring
    have hdefect (r i j k : V) : tetraDefect F r i j k = tetraDefect R r i j k := by
      dsimp [tetraDefect, R, edgeCoboundary]
      ring
    change (∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
        (tetraDefect F r i j k) ^ 2) = 4 * n * E
    simp_rw [hdefect]
    exact henergy
  refine ⟨hequality, ?_⟩
  intro hcard C hbound
  obtain ⟨p⟩ : Nonempty (Fin 4 ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  let p0 : V := p 0
  let p1 : V := p 1
  let p2 : V := p 2
  let p3 : V := p 3
  have h01 : p0 ≠ p1 := p.injective.ne (by decide)
  have h02 : p0 ≠ p2 := p.injective.ne (by decide)
  have h03 : p0 ≠ p3 := p.injective.ne (by decide)
  have h12 : p1 ≠ p2 := p.injective.ne (by decide)
  have h13 : p1 ≠ p3 := p.injective.ne (by decide)
  have h23 : p2 ≠ p3 := p.injective.ne (by decide)
  let u : V → ℝ := fun x => if x = p1 then 1 else 0
  let v : V → ℝ := fun x => if x = p2 then 1 else 0
  let w : V → ℝ := fun x => if x = p3 then 1 else 0
  let F : V → V → V → ℝ := fun i j k =>
    u i * v j * w k + u j * v k * w i + u k * v i * w j
      - u i * v k * w j - u j * v i * w k - u k * v j * w i
  have hF12 (i j k : V) : F j i k = -F i j k := by
    dsimp [F]
    ring
  have hF23 (i j k : V) : F i k j = -F i j k := by
    dsimp [F]
    ring
  have hu0 : u p0 = 0 := by simp [u, h01]
  have hv0 : v p0 = 0 := by simp [v, h02]
  have hw0 : w p0 = 0 := by simp [w, h03]
  have hF123 : F p1 p2 p3 = 1 := by
    simp [F, u, v, w, h12, h13, h23]
  have hF0first (i j : V) : F p0 i j = 0 := by
    simp [F, hu0, hv0, hw0]
  have hF0second (i j : V) : F i p0 j = 0 := by
    simp [F, hu0, hv0, hw0]
  have hF0third (i j : V) : F i j p0 = 0 := by
    simp [F, hu0, hv0, hw0]
  have hdefect : tetraDefect F p0 p1 p2 p3 = 1 := by
    simp [tetraDefect, hF123, hF0first]
  have hTpos : 0 < ∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
      (tetraDefect F r i j k) ^ 2 := by
    have hterm : (tetraDefect F p0 p1 p2 p3) ^ 2 ≤
        ∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
          (tetraDefect F r i j k) ^ 2 := by
      calc
        _ ≤ ∑ k : V, (tetraDefect F p0 p1 p2 k) ^ 2 :=
          Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ p3)
        _ ≤ ∑ j : V, ∑ k : V, (tetraDefect F p0 p1 j k) ^ 2 :=
          Finset.single_le_sum
            (fun j _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
            (Finset.mem_univ p2)
        _ ≤ ∑ i : V, ∑ j : V, ∑ k : V, (tetraDefect F p0 i j k) ^ 2 :=
          Finset.single_le_sum
            (fun i _ => Finset.sum_nonneg (fun j _ =>
              Finset.sum_nonneg (fun k _ => sq_nonneg _)))
            (Finset.mem_univ p1)
        _ ≤ ∑ r : V, ∑ i : V, ∑ j : V, ∑ k : V,
            (tetraDefect F r i j k) ^ 2 :=
          Finset.single_le_sum
            (fun r _ => Finset.sum_nonneg (fun i _ =>
              Finset.sum_nonneg (fun j _ =>
                Finset.sum_nonneg (fun k _ => sq_nonneg _))))
            (Finset.mem_univ p0)
    rw [hdefect] at hterm
    exact lt_of_lt_of_le (by norm_num) hterm
  have hfactor : 0 < 4 * (Fintype.card V : ℝ) := by
    have hn : 0 < (Fintype.card V : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := V)
    exact mul_pos (by norm_num) hn
  have henergy := hequality F hF12 hF23
  have hEpos : 0 < ∑ i : V, ∑ j : V, ∑ k : V,
      (F i j k - edgeCoboundary (averageEdge F) i j k) ^ 2 := by
    rw [henergy] at hTpos
    exact (mul_pos_iff_of_pos_left hfactor).mp hTpos
  have hC := hbound F hF12 hF23
  rw [henergy] at hC
  exact le_of_mul_le_mul_right hC hEpos

#print axioms tetra_defect_energy_eq_and_optimal

end D5.S3.Fourier.CharacterSelection.SimplexTwoCochainL2Projection
