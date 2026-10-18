/- GID: D5/S3/Combinatorics/Graph/Pressure/StationaryVariational
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/StationaryVariational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero-aware stationary KL identity and attained pressure for the actual weighted graph. -/
import D5.S3.Combinatorics.Graph.Pressure.PerronDoob
import D5.S3.Divergence.GrandmotherTheorem

/-! Finite weighted graph pressure on the original support. -/
noncomputable section
open scoped BigOperators Matrix
open D5.S3.Divergence.ClassicalDPI D5.S3.Divergence.GrandmotherTheorem
namespace D5.S3.Combinatorics.Graph.Pressure.Network
universe u
variable {X : Type u} [Fintype X] [DecidableEq X] (G : Network X)
namespace StationaryPair
variable {G}
variable (p : G.StationaryPair)
def entropy : ℝ := -(∑ i, ∑ j, p.π i * p.Q i j * Real.log (p.Q i j))
def energy (c : X → X → ℝ) : ℝ := ∑ i, ∑ j, p.π i * p.Q i j * c i j
def objective (c : X → X → ℝ) (τ : ℝ) : ℝ := p.energy c - τ * p.entropy

lemma flow_mass : (∑ i, ∑ j, p.π i * p.Q i j) = 1 := by
  simp_rw [← Finset.mul_sum,p.sumQ,mul_one]
  exact p.sumπ

/-- Exact cancellation for an arbitrary potential, with no positive-mass assumption. -/
lemma potential_cancel (v : X → ℝ) :
    (∑ i, ∑ j, p.π i * p.Q i j * (v i - v j)) = 0 := by
  have hr : (∑ i, ∑ j, p.π i * p.Q i j * v i) = ∑ i, p.π i * v i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (p.π i * v i) * ∑ j, p.Q i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [p.sumQ,mul_one]
  have hc : (∑ i, ∑ j, p.π i * p.Q i j * v j) = ∑ j, p.π j * v j := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,p.stationary]
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [hr,hc,sub_self]
end StationaryPair

variable (c : X → X → ℝ) (τ : ℝ)
def weightedKL (p : G.StationaryPair) : ℝ :=
  ∑ i, p.π i * klDivergence (p.Q i) (G.Qstar c τ i)

/-- The finite KL supplier is applied to the full rows, including their zeros. -/
lemma weightedKL_nonneg (p : G.StationaryPair) : 0 ≤ G.weightedKL c τ p := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (p.nonnegπ i)
  apply kl_divergence_nonneg _ _ ⟨p.nonnegQ i,p.sumQ i⟩
    ⟨G.Qstar_nonneg c τ i,G.Qstar_rowsum c τ i⟩
  intro j hz
  apply p.supported i j
  intro he
  exact (ne_of_gt ((G.Qstar_pos_iff c τ i j).2 he)) hz

/-- The original weighted stationary KL identity for every supported stationary pair. -/
theorem stationary_kl_identity (hτ : 0 < τ) (p : G.StationaryPair) :
    τ * G.weightedKL c τ p = p.objective c τ + τ * Real.log (G.perron c τ).root := by
  classical
  let r := (G.perron c τ).right
  let lam := (G.perron c τ).root
  have hr : ∀ i, r i ≠ 0 := fun i => ne_of_gt ((G.perron c τ).right_pos i)
  have hl : lam ≠ 0 := ne_of_gt (G.perron c τ).root_pos
  have ht (i j : X) : p.π i * τ * (p.Q i j * Real.log (p.Q i j / G.Qstar c τ i j)) =
      p.π i * p.Q i j * c i j + τ * (p.π i * p.Q i j * Real.log (p.Q i j)) +
      τ * (p.π i * p.Q i j * (Real.log (r i) - Real.log (r j))) +
      τ * (p.π i * p.Q i j * Real.log lam) := by
    by_cases hq : p.Q i j = 0
    · simp [hq]
    have he : G.edge i j := by
      by_contra hn
      exact hq (p.supported i j hn)
    have hstar : G.Qstar c τ i j ≠ 0 := ne_of_gt ((G.Qstar_pos_iff c τ i j).2 he)
    have hlog : Real.log (G.Qstar c τ i j) = -c i j / τ + Real.log (r j) -
        (Real.log lam + Real.log (r i)) := by
      rw [Qstar,W,if_pos he,Real.log_div (mul_ne_zero (Real.exp_ne_zero _) (hr j)) (mul_ne_zero hl (hr i)),
        Real.log_mul (Real.exp_ne_zero _) (hr j),Real.log_exp,Real.log_mul hl (hr i)]
    rw [Real.log_div hq hstar,hlog]
    field_simp [ne_of_gt hτ]
    <;> ring
  have hx : τ * G.weightedKL c τ p =
      ∑ i, ∑ j, (p.π i * p.Q i j * c i j + τ * (p.π i * p.Q i j * Real.log (p.Q i j)) +
      τ * (p.π i * p.Q i j * (Real.log (r i) - Real.log (r j))) +
      τ * (p.π i * p.Q i j * Real.log lam)) := by
    unfold weightedKL klDivergence
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simpa only [mul_assoc,mul_left_comm,mul_comm] using ht i j
  rw [hx]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  rw [p.potential_cancel (fun i => Real.log (r i)),p.flow_mass]
  simp only [StationaryPair.objective,StationaryPair.energy,StationaryPair.entropy]
  ring

/-- An actual minimum, attained by the actual Doob row with an actual stationary law. -/
theorem variational_minimum (hτ : 0 < τ) :
    ∃ p : G.StationaryPair, p.Q = G.Qstar c τ ∧
      p.objective c τ = -τ * Real.log (G.perron c τ).root ∧
      ∀ q : G.StationaryPair, -τ * Real.log (G.perron c τ).root ≤ q.objective c τ := by
  classical
  obtain ⟨p,hp⟩ := G.exists_stationary_doob c τ
  have hk : G.weightedKL c τ p = 0 := by
    unfold weightedKL
    rw [hp]
    apply Finset.sum_eq_zero
    intro i _
    suffices klDivergence (G.Qstar c τ i) (G.Qstar c τ i) = 0 by rw [this,mul_zero]
    unfold klDivergence
    apply Finset.sum_eq_zero
    intro j _
    by_cases hz : G.Qstar c τ i j = 0 <;> simp [hz]
  refine ⟨p,hp,?_,?_⟩
  · have h := G.stationary_kl_identity c τ hτ p
    rw [hk,mul_zero] at h
    linarith
  · intro q
    have h := G.stationary_kl_identity c τ hτ q
    have hn := mul_nonneg hτ.le (G.weightedKL_nonneg c τ q)
    linarith
end D5.S3.Combinatorics.Graph.Pressure.Network
