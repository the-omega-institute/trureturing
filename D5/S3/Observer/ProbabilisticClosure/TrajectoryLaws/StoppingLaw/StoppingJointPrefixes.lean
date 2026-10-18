/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingJointPrefixes
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingJointPrefixes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete stopping masses determine every zero-prefix and actual-target spin section. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteTreeLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.StoppingPrefixes
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

/-- Events are decreasing even if the same edge is queried repeatedly. -/
theorem zero_prefix_antitone (es : List ℤ) {r t : ℕ} (hrt : r ≤ t) :
    zeroEdges (es.take t).toFinset ⊆ zeroEdges (es.take r).toFinset := by
  intro S h e he
  apply h e
  exact List.mem_toFinset.mpr
    (List.take_subset_take_left es hrt (List.mem_toFinset.mp he))

theorem zero_edge_difference (es : List ℤ) (φ : Bool) (r : ℕ) (hr : r < es.length) :
    zeroEdges (es.take r).toFinset \ zeroEdges (es.take (r + 1)).toFinset =
      {S | ((ReadTree.edgeComb es φ).run (visible φ S)).output = some (.a true) ∧
        ((ReadTree.edgeComb es φ).run (visible φ S)).paid = r + 1} := by
  ext S
  change ((∀ e ∈ (es.take r).toFinset, S e = S (e + 1)) ∧
    ¬(∀ e ∈ (es.take (r + 1)).toFinset, S e = S (e + 1))) ↔ _
  rw [← ReadTree.edge_zero_prefix, ← ReadTree.edge_zero_prefix]
  exact ReadTree.zero_prefix_difference _ _ r (by simpa using hr)

theorem joint_zero_prefix_mass (β : Bias) (V : Finset ℤ) (j : Bool) (es : List ℤ)
    (hq : j.toInt ∈ V) (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j)))
    (s : Bool) (r : ℕ) (hr : r ≤ es.length) :
    prob β V (zeroEdges (es.take r).toFinset ∩ {S | S j.toInt = s}) =
      β.π s * β.T (r + 1) := by
  induction r with
  | zero =>
    have he : zeroEdges (es.take 0).toFinset = Set.univ := by ext S; simp [zeroEdges]
    rw [he, Set.univ_inter, spin_prob β V j.toInt hq s, β.T_one, mul_one]
  | succ r ih =>
    have hr' : r ≤ es.length := by omega
    have hrl : r < es.length := by omega
    have hi := ih hr'
    have hdiff := zero_edge_difference es (!j) r hrl
    let C : Set Spins := zeroEdges (es.take r).toFinset ∩ {S | S j.toInt = s}
    let D : Set Spins := zeroEdges (es.take (r + 1)).toFinset ∩ {S | S j.toInt = s}
    have hDC : D ⊆ C := fun _ h => ⟨zero_prefix_antitone es (by omega) h.1, h.2⟩
    have he : C \ D = {S | S j.toInt = s ∧
        ((ReadTree.edgeComb es (!j)).run (visible (!j) S)).output = some (.a true) ∧
        ((ReadTree.edgeComb es (!j)).run (visible (!j) S)).paid = r + 1} := by
      calc
        C \ D = {S | S j.toInt = s} ∩
            (zeroEdges (es.take r).toFinset \ zeroEdges (es.take (r + 1)).toFinset) := by
          ext S
          simp only [C, D, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
          tauto
        _ = _ := by rw [hdiff]; rfl
    have hp : prob β V (C \ D) = β.π s * β.d (r + 1) := by
      rw [he]
      exact ReadTree.stopping_law_b_depth β V j s es.length (r + 1)
        (ReadTree.edgeComb es (!j)) hlaw (by omega) (by omega)
    rw [prob_diff β V hDC] at hp
    change prob β V C = β.π s * β.T (r + 1) at hi
    change prob β V D = β.π s * β.T ((r + 1) + 1)
    rw [hi] at hp
    simp only [Bias.d] at hp
    nlinarith

theorem zero_prefix_mass (β : Bias) (V : Finset ℤ) (j : Bool) (es : List ℤ)
    (hq : j.toInt ∈ V) (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j)))
    (r : ℕ) (hr : r ≤ es.length) :
    prob β V (zeroEdges (es.take r).toFinset) = β.T (r + 1) := by
  rw [split_spin β V j.toInt]
  have h0 := joint_zero_prefix_mass β V j es hq hlaw false r hr
  have h1 := joint_zero_prefix_mass β V j es hq hlaw true r hr
  rw [Set.inter_comm] at h0 h1
  rw [h0, h1, ← add_mul, β.π_sum, one_mul]

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
