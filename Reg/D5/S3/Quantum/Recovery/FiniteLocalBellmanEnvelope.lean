import D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope

abbrev signature : Signature where
  Params := ℝ
  State _ := State
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ r z => VInfinity r z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def originalStatement : Prop := ∀ (r : ℝ) (hr : 0 < r) (hlo : 1 / 2 < r ^ 2) (hhi : r ^ 2 < 2),
    (IsCompact (K_s r)) ∧
    (∀ n, Admissible r (V r n)) ∧
    (∀ n z, V r n z ≤ V r (n+1) z) ∧
    (∀ n actor z,
      (∃ s : Split 5 (active actor z),
        fiveValue actor (V r n) z =
          ∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ∧
      (∀ m (s : Split m (active actor z)),
        (∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ≤
          fiveValue actor (V r n) z)) ∧
    (∀ n z,
      (∃ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n ∧ T.reward (terminal r) = V r n z) ∧
      (∀ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n → T.reward (terminal r) ≤ V r n z)) ∧
    (∀ z, VInfinity r z = treeValue r z ∧
      0 ≤ VInfinity r z ∧ VInfinity r z ≤ h r) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ u : State → ℝ, SeparatelyConcave u →
      (∀ z, terminal r z ≤ u z) → ∀ z, VInfinity r z ≤ u z) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r)

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (hr : 0 < r) (hlo : 1 / 2 < r ^ 2) (hhi : r ^ 2 < 2),
    (IsCompact (K_s r)) ∧
    (∀ n, Admissible r (V r n)) ∧
    (∀ n z, V r n z ≤ V r (n+1) z) ∧
    (∀ n actor z,
      (∃ s : Split 5 (active actor z),
        fiveValue actor (V r n) z =
          ∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ∧
      (∀ m (s : Split m (active actor z)),
        (∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ≤
          fiveValue actor (V r n) z)) ∧
    (∀ n z,
      (∃ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n ∧ T.reward (terminal r) = V r n z) ∧
      (∀ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n → T.reward (terminal r) ≤ V r n z)) ∧
    (∀ z, R.readout () r z = treeValue r z ∧
      0 ≤ VInfinity r z ∧ VInfinity r z ≤ h r) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ u : State → ℝ, SeparatelyConcave u →
      (∀ z, terminal r z ≤ u z) → ∀ z, VInfinity r z ≤ u z) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r)

theorem actual_law : arena.Law actual := source_bellman_finite_tree_identity

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  let zero : Ball := ⟨0,by simp⟩
  have hb := bad 1 (by norm_num) (by norm_num) (by norm_num)
  have ha := source_bellman_finite_tree_identity 1 (by norm_num) (by norm_num) (by norm_num)
  have he := (hb.2.2.2.2.2.1 (zero,zero)).1
  have hg := (ha.2.2.2.2.2.1 (zero,zero)).2.1
  have hv := (ha.2.2.2.2.2.1 (zero,zero)).1
  change -1 = treeValue 1 (zero,zero) at he
  rw [← hv] at he
  linarith

def registration : Registration arena originalStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    obtain ⟨⟨a,b⟩,hab⟩ := (all_r_flat_geometry 1 (by norm_num) (by norm_num) (by norm_num)).2.2.2.1
    let x : Ball := ⟨a,by simpa only [Metric.mem_closedBall,dist_zero_right,hab.1] using (le_rfl : (1 : ℝ) ≤ 1)⟩
    let y : Ball := ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right,hab.2.1] using (le_rfl : (1 : ℝ) ≤ 1)⟩
    have ha := source_bellman_finite_tree_identity 1 (by norm_num) (by norm_num) (by norm_num)
    have hflat := ha.2.2.2.2.2.2.2.2.2.1 (x,y) hab
    have hdiag := ha.2.2.2.2.2.2.2.2.2.2.1 x hab.1
    refine ⟨(1 : ℝ),(x,y),(x,x),?_⟩
    change VInfinity 1 (x,y) ≠ VInfinity 1 (x,x)
    rw [hflat.1,hdiag.1]
    unfold h kappa
    positivity

register_information_theorem source_bellman_finite_tree_identity in arena
  readout via (realize signature (fun _ r z => VInfinity r z) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

end Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
