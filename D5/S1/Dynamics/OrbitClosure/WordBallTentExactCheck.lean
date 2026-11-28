module
public import D5.S1.Dynamics.OrbitClosure.WordBallTent
@[expose] public section
universe u v
open Set
example {G : Type u} {X : Type v} [Group G] [MetricSpace X] [CompactSpace X]
    [MulAction G X] (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hS : Subgroup.closure (S : Set G) = ⊤)
    (hcont : ∀ g : G, Continuous (fun x : X => g • x))
    (hinf : (Set.range (MulAction.toPermHom G X)).Infinite)
    (R : ℕ) (hR : 2 ≤ R) :
    ∃ u : C(X, ℝ), ∃ x₀ : X, ∃ g₀ : G,
      (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧ u x₀ = 1 ∧ u (g₀ • x₀) = 0 ∧
      (∀ s ∈ S, ∀ x, |u (s • x) - u x| ≤ 1 / (R : ℝ)) ∧
      (∀ v : C(X, ℝ), (∀ g : G, ∀ x : X, v (g • x) = v x) →
        (1 / 2 : ℝ) ≤ ‖u - v‖) :=
  D5.S1.Dynamics.OrbitClosure.WordBallTent.exists_continuous_wordBall_tent
    S hsym hS hcont hinf R (Nat.le_trans (by decide : 1 ≤ 2) hR)
