/- GID: D5/S3/Combinatorics/Graph/LinearForests/AlternatingCompletionLaw
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/AlternatingCompletionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact extension-event probabilities and conditioning for labelled alternating cycles. -/

import D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory

/-! Uniform conditioning on fixed prescribed edges of a labelled alternating cycle. -/

namespace D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw

open CompatibleCycleInventory DirectedForestCompletion Relation
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open scoped ENNReal

variable {V : Type*}

/-- Full cycles that alternate the two colors on the original vertices. -/
abbrev AlternatingFullCycle (k : V → Bool) :=
  Compatible k (fun x => !(k x))

/-- View an actual alternating completion as a member of the ambient cycle space. -/
def includeCompletion (E : V → V → Prop) (k : V → Bool)
    (τ : AlternatingCompletion E k) : AlternatingFullCycle k :=
  ⟨τ.1, τ.2.1, τ.2.2.1, fun x => Bool.not_eq_iff.mpr (τ.2.2.2.2 x).symm⟩

private def extensionEquiv (E : V → V → Prop) (k : V → Bool) :
    {σ : AlternatingFullCycle k // ∀ x y, E x y → σ.1 x = y} ≃
      AlternatingCompletion E k where
  toFun σ := ⟨σ.1.1, σ.1.2.1, σ.1.2.2.1, σ.2,
    fun x => (Bool.not_eq_iff.mp (σ.1.2.2.2 x)).symm⟩
  invFun τ := ⟨includeCompletion E k τ, τ.2.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ambient_card [Finite V] (k : V → Bool) (n : ℕ) (hn : 0 < n)
    (hr : Nat.card (Side k false) = n) (hb : Nat.card (Side k true) = n) :
    Nat.card (AlternatingFullCycle k) = n.factorial * (n - 1).factorial := by
  have hRed : inventory k (fun x => !(k x)) false true = n :=
    (cross_inventory k false).trans hr
  have hBlue : inventory k (fun x => !(k x)) true false = n :=
    (cross_inventory k true).trans hb
  have hV : Nat.card V ≠ 0 := by
    have hSide : 0 < Nat.card (Side k false) := hr.symm ▸ hn
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hSide
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective))
  rw [compatible_cycle_card _ _ (hRed.trans hBlue.symm), ite_eq_right hV, hRed, ite_eq_left hn,
    hr, hb]
  have hf := Nat.factorial_succ (n - 1)
  rw [Nat.sub_add_cancel hn] at hf
  rw [hf]

/-- The exact event mass and static conditional distribution on actual alternating completions. -/
theorem alternating_completion_law [Finite V] (E : V → V → Prop) (k : V → Bool)
    (n : ℕ) (hn : 0 < n)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) (hk : ∀ x y, E x y → k x ≠ k y)
    (hr : Nat.card (Side k false) = n) (hb : Nat.card (Side k true) = n) :
    let S : Set (AlternatingFullCycle k) := {σ | ∀ x y, E x y → σ.1 x = y}
    let D := n.factorial * (n - 1).factorial
    ∃ (t : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : AlternatingCompletion E k ≃ Compatible (fun A => k (h A)) (fun A => !(k (t A))))
      (μ : PMF (AlternatingFullCycle k)),
      (∀ A, Quotient.mk (EqvGen.setoid E) (t A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      (∀ σ A, σ.1 (t A) = h ((Φ σ).1 A)) ∧
      (∀ σ, μ σ = (D : ℝ≥0∞)⁻¹) ∧
      μ.toOuterMeasure S = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞) / D ∧
      (0 < μ.toOuterMeasure S ↔ Nonempty (AlternatingCompletion E k)) ∧
      ∀ hs : ∃ σ ∈ S, σ ∈ μ.support,
        ∃ ν : PMF (AlternatingCompletion E k),
          (∀ τ, ν τ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹) ∧
          μ.filter S hs = ν.map (includeCompletion E k) ∧
          (∀ ρ, ν.map Φ.toFun ρ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹) := by
  classical
  dsimp only
  obtain ⟨t, h, Φ, ht, hh, hΦ, _⟩ := alternating_completion_classification n E k
    hout hin ha hk hr hb
  let p (σ : AlternatingFullCycle k) := ∀ x y, E x y → σ.1 x = y
  let S : Set (AlternatingFullCycle k) := {σ | p σ}
  let e : S ≃ AlternatingCompletion E k := extensionEquiv E k
  let D := n.factorial * (n - 1).factorial
  have hD : 0 < D := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  let : Fintype (AlternatingFullCycle k) := Fintype.ofFinite _
  let : Nonempty (AlternatingFullCycle k) :=
    Finite.card_pos_iff.mp ((ambient_card k n hn hr hb).symm ▸ hD)
  let : Fintype S := Fintype.ofFinite S
  have hAmbient : Fintype.card (AlternatingFullCycle k) = D :=
    Nat.card_eq_fintype_card.symm.trans (ambient_card k n hn hr hb)
  have hEvent : Fintype.card S = Nat.card (AlternatingCompletion E k) :=
    Nat.card_eq_fintype_card.symm.trans (Nat.card_congr e)
  let μ := uniformPmf (AlternatingFullCycle k)
  have hmass : μ.toOuterMeasure S = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞) / D := by
    rw [uniformPmf_toOuterMeasure_apply, hEvent, hAmbient]
  refine ⟨t, h, Φ, μ, ht, hh, hΦ, ?_, hmass, ?_, ?_⟩
  · intro σ
    simp only [μ, uniformPmf, PMF.ofFintype_apply, hAmbient, D]
  · change 0 < μ.toOuterMeasure S ↔ _
    have hInv : (D : ℝ≥0∞)⁻¹ ≠ 0 := (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)).ne'
    rw [hmass, div_eq_mul_inv, pos_iff_ne_zero, mul_ne_zero_iff]
    simp only [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finite.card_pos_iff]
    exact and_iff_left hInv
  · intro hs
    let : Nonempty {σ : AlternatingFullCycle k // p σ} := by
      obtain ⟨σ, hσ, _⟩ := hs
      exact ⟨⟨σ, hσ⟩⟩
    let : Fintype (AlternatingCompletion E k) := Fintype.ofFinite _
    let : Nonempty (AlternatingCompletion E k) := Nonempty.map
      (extensionEquiv E k) ‹Nonempty {σ : AlternatingFullCycle k // p σ}›
    refine ⟨uniformPmf (AlternatingCompletion E k), ?_, ?_, ?_⟩
    · intro τ
      simp only [uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card]
    · change μ.filter S hs = _
      let e' : {σ : AlternatingFullCycle k // p σ} ≃ AlternatingCompletion E k := e
      have he := uniform_equiv e'.symm
      calc
        _ = (uniformPmf {σ : AlternatingFullCycle k // p σ}).map Subtype.val :=
          uniform_filter p hs
        _ = ((uniformPmf (AlternatingCompletion E k)).map e'.symm).map Subtype.val := by rw [he]
        _ = _ := by rw [PMF.map_comp]; rfl
    · intro ρ
      let : Fintype (Compatible (fun A => k (h A)) (fun A => !(k (t A)))) := Fintype.ofFinite _
      let : Nonempty (Compatible (fun A => k (h A)) (fun A => !(k (t A)))) :=
        Nonempty.map Φ inferInstance
      change ((uniformPmf (AlternatingCompletion E k)).map Φ) ρ = _
      rw [uniform_equiv Φ]
      simp only [uniformPmf, PMF.ofFintype_apply, ← Nat.card_eq_fintype_card, Nat.card_congr Φ]

end D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw
