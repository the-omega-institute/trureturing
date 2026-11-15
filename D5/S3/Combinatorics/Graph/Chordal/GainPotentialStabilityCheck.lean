import D5.S3.Combinatorics.Graph.Chordal.GainPotentialStability

universe u v

example {V : Type u} [Finite V] {H : Type v} [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] (G : SimpleGraph V)
    (hG : G.IsChordal) (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      dist (g i j * g j k) (g i k) ≤ ε) :
    ∃ φ : V → H, ∀ i j, G.Adj i j →
      dist (g i j) ((φ i)⁻¹ * φ j) ≤ ((Nat.card V - 2 : ℕ) : ℝ) * ε :=
  hG.exists_approximate_gain_potential g ε hε hrev htri

example {H : Type v} [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]
    (G : SimpleGraph Empty) (g : Empty → Empty → H) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ φ : Empty → H, ∀ i j, G.Adj i j → dist (g i j) ((φ i)⁻¹ * φ j) ≤ 0 := by
  have hG : G.IsChordal := by intro x; exact x.elim
  have hr : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹ := by intro i; exact i.elim
  have ht : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      dist (g i j * g j k) (g i k) ≤ ε := by intro i; exact i.elim
  simpa using hG.exists_approximate_gain_potential g ε hε hr ht

namespace ConcreteCheck
noncomputable section

private def discreteMetric (X : Type*) [DecidableEq X] : MetricSpace X where
  dist a b := if a = b then 0 else 1
  dist_self a := ite_eq_left rfl
  dist_comm a b := by split_ifs <;> simp_all
  dist_triangle a b c := by split_ifs <;> simp_all
  eq_of_dist_eq_zero := by intro a b h; split_ifs at h <;> simp_all

private abbrev H := Equiv.Perm (Fin 3)
local instance : MetricSpace H := discreteMetric H
local instance : IsIsometricSMul H H := ⟨fun c => Isometry.of_dist_eq (fun a b => by
  change (if c * a = c * b then (0 : ℝ) else 1) = (if a = b then 0 else 1)
  simp only [mul_left_cancel_iff])⟩
local instance : IsIsometricSMul Hᵐᵒᵖ H := ⟨fun c => Isometry.of_dist_eq (fun a b => by
  change (if a * c.unop = b * c.unop then (0 : ℝ) else 1) =
    (if a = b then 0 else 1)
  simp only [mul_right_cancel_iff])⟩

private def t : H := Equiv.swap 0 1
private def r : H := Equiv.swap 1 2

-- The instantiated group is noncommutative, with explicit noncommuting elements.
example : t * r ≠ r * t := by decide
example : t ≠ 1 := by decide

private theorem smallChordal (n : ℕ) (hn : n ≤ 3) :
    (⊤ : SimpleGraph (Fin n)).IsChordal := by
  intro x c hc hlen
  have hcard := hc.support_nodup.length_le_card
  rw [List.length_tail, c.length_support] at hcard
  simp only [Fintype.card_fin] at hcard
  omega

-- A genuine nonidentity edge with zero defect on an inhabited graph.
example : ∃ φ : Fin 2 → H, ∀ i j, (⊤ : SimpleGraph (Fin 2)).Adj i j →
    dist ((if i = 0 then (1 : H) else t)⁻¹ * (if j = 0 then 1 else t))
      ((φ i)⁻¹ * φ j) ≤ 0 := by
  let θ : Fin 2 → H := fun i => if i = 0 then 1 else t
  let g : Fin 2 → Fin 2 → H := fun i j => (θ i)⁻¹ * θ j
  have hr : ∀ i j, (⊤ : SimpleGraph (Fin 2)).Adj i j → g j i = (g i j)⁻¹ := by
    intro i j _; simp [g]
  have ht : ∀ i j k, (⊤ : SimpleGraph (Fin 2)).Adj i j →
      (⊤ : SimpleGraph (Fin 2)).Adj j k → (⊤ : SimpleGraph (Fin 2)).Adj i k →
      dist (g i j * g j k) (g i k) ≤ 0 := by
    intro i j k _ _ _; simp [g, mul_assoc]
  simpa [g, θ] using (smallChordal 2 (by decide)).exists_approximate_gain_potential
    g 0 le_rfl hr ht

-- All six oriented edges of a triangle carry a transposition. The triangle defect is 1.
private def noisy (i j : Fin 3) : H := if i = j then 1 else t

example : dist (noisy 0 1 * noisy 1 2) (noisy 0 2) = 1 := by
  change (if noisy 0 1 * noisy 1 2 = noisy 0 2 then (0 : ℝ) else 1) = 1
  have h : noisy 0 1 * noisy 1 2 ≠ noisy 0 2 := by decide
  simp only [h, ite_false]

example : ∃ φ : Fin 3 → H, ∀ i j, (⊤ : SimpleGraph (Fin 3)).Adj i j →
    dist (noisy i j) ((φ i)⁻¹ * φ j) ≤ 1 := by
  have hr : ∀ i j, (⊤ : SimpleGraph (Fin 3)).Adj i j →
      noisy j i = (noisy i j)⁻¹ := by decide
  have ht : ∀ i j k, (⊤ : SimpleGraph (Fin 3)).Adj i j →
      (⊤ : SimpleGraph (Fin 3)).Adj j k → (⊤ : SimpleGraph (Fin 3)).Adj i k →
      dist (noisy i j * noisy j k) (noisy i k) ≤ 1 := by
    intro i j k _ _ _
    change (if noisy i j * noisy j k = noisy i k then (0 : ℝ) else 1) ≤ 1
    split_ifs <;> norm_num
  simpa using (smallChordal 3 (by decide)).exists_approximate_gain_potential
    noisy 1 (by norm_num) hr ht

-- This same nonzero-defect input admits no potential with zero edge error.
example : ¬ ∃ φ : Fin 3 → H, ∀ i j, (⊤ : SimpleGraph (Fin 3)).Adj i j →
    dist (noisy i j) ((φ i)⁻¹ * φ j) ≤ 0 := by
  rintro ⟨φ, hφ⟩
  have h01 := dist_le_zero.mp (hφ 0 1 (by decide))
  have h12 := dist_le_zero.mp (hφ 1 2 (by decide))
  have h02 := dist_le_zero.mp (hφ 0 2 (by decide))
  have hbad : noisy 0 1 * noisy 1 2 = noisy 0 2 := by
    rw [h01, h12, h02]
    simp [mul_assoc]
  exact (by decide : noisy 0 1 * noisy 1 2 ≠ noisy 0 2) hbad

end ConcreteCheck

#print axioms SimpleGraph.IsChordal.exists_approximate_gain_potential
#check @SimpleGraph.IsChordal.exists_approximate_gain_potential
