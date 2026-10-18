/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingStructure
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-phase execution constraints force every constructor of the stopping comb. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.ReadTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace ReadTree

/-- In the opposite phase every spin configuration returns a0 at the prescribed depth. -/
def OppositeSection (T : ReadTree) (φ : Bool) (k : ℕ) : Prop :=
  ∀ S : Spins, (T.run (visible (!φ) S)).output = some (.a false) ∧
    (T.run (visible (!φ) S)).paid = k

/-- Every positive paid depth occurs with output a1 in the active phase. -/
def AllStoppingDepths (T : ReadTree) (φ : Bool) (k : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → ∃ S : Spins,
    (T.run (visible φ S)).output = some (.a true) ∧
      (T.run (visible φ S)).paid = i

/-- Neither the comb shape nor the addresses' parity is an input assumption. -/
theorem sections_force_stopComb (k : ℕ) (T : ReadTree) (φ : Bool)
    (hh : T.height ≤ k) (hA : T.OppositeSection φ k)
    (hB : T.AllStoppingDepths φ k) :
    ∃ ts : List ℤ, ts.length = k ∧
      (∀ t ∈ ts, (t - φ.toInt) % 2 = 0) ∧ T = stopComb ts := by
  induction k generalizing T with
  | zero =>
    have h0 := hA (fun _ => false)
    have he := leaf_of_paid_zero T _ h0.2
    refine ⟨[], rfl, by simp, ?_⟩
    simpa [stopComb, h0.1] using he
  | succ k ih =>
    cases T with
    | leaf a =>
      have hn := (hA (fun _ => false)).2
      simp [run, Execution.paid] at hn
    | read t z o =>
      obtain ⟨S, hs, hn⟩ := hB 1 (by omega) (by omega)
      have hzero := hA (fun _ => false)
      have hconst : visible (!φ) (fun _ => false) t = false := constant_visible _ _ _
      have hzout : (z.run (visible (!φ) (fun _ => false))).output = some (.a false) := by
        simpa only [run, hconst, Bool.false_eq_true, ↓reduceIte, Execution.output_prepend]
          using hzero.1
      have htrue : visible φ S t = true := by
        cases he : visible φ S t with
        | false =>
          have hz0 : (z.run (visible φ S)).paid = 0 := by
            simp only [run, he, Bool.false_eq_true, ↓reduceIte, Execution.paid_prepend] at hn
            omega
          have hzleaf := leaf_of_paid_zero z (visible φ S) hz0
          have hzlabel : (z.run (visible φ S)).output = some (.a true) := by
            simpa only [run, he, Bool.false_eq_true, ↓reduceIte, Execution.output_prepend] using hs
          rw [hzlabel] at hzleaf
          rw [hzleaf] at hzout
          simp [run] at hzout
        | true => rfl
      have ht : (t - φ.toInt) % 2 = 0 := by
        by_contra h
        simp [visible, h] at htrue
      have ho0 : (o.run (visible φ S)).paid = 0 := by
        simp only [run, htrue, ↓reduceIte, Execution.paid_prepend] at hn
        omega
      have holeaf := leaf_of_paid_zero o (visible φ S) ho0
      have holabel : (o.run (visible φ S)).output = some (.a true) := by
        simpa only [run, htrue, ↓reduceIte, Execution.output_prepend] using hs
      rw [holabel] at holeaf
      have hzheight : z.height ≤ k := by
        simp only [height] at hh
        have := le_max_left z.height o.height
        omega
      have hzA : z.OppositeSection φ k := by
        intro R
        have hr := hA R
        have hv := opposite_phase_visible φ R t ht
        simp only [run, hv, Bool.false_eq_true, ↓reduceIte,
          Execution.output_prepend, Execution.paid_prepend] at hr
        exact ⟨hr.1, by omega⟩
      have hzB : z.AllStoppingDepths φ k := by
        intro i hi hik
        obtain ⟨R, hrout, hrn⟩ := hB (i + 1) (by omega) (by omega)
        have hv : visible φ R t = false := by
          cases he : visible φ R t with
          | false => rfl
          | true =>
            simp [run, he, holeaf, Execution.paid, Execution.prepend] at hrn
            omega
        simp only [run, hv, Bool.false_eq_true, ↓reduceIte,
          Execution.output_prepend, Execution.paid_prepend] at hrout hrn
        exact ⟨R, hrout, by omega⟩
      obtain ⟨ts, hlen, hpar, heq⟩ := ih z hzheight hzA hzB
      refine ⟨t :: ts, by simp [hlen], ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ht
        · exact hpar a ha
      · rw [heq, holeaf]; rfl

/-- Active integer labels are exactly the lifted spin-edge indices, without an ordering restriction. -/
theorem stopComb_edge_indices (k : ℕ) (T : ReadTree) (φ : Bool)
    (hh : T.height ≤ k) (hA : T.OppositeSection φ k)
    (hB : T.AllStoppingDepths φ k) :
    ∃ es : List ℤ, es.length = k ∧
      T = stopComb (es.map (fun e => 2 * e + φ.toInt)) := by
  obtain ⟨ts, hlen, hpar, heq⟩ := sections_force_stopComb k T φ hh hA hB
  refine ⟨ts.map (fun t => (t - φ.toInt) / 2), by simpa, ?_⟩
  rw [List.map_map]
  have hm : ts.map (fun t => 2 * ((t - φ.toInt) / 2) + φ.toInt) = ts := by
    calc
      _ = ts.map (fun t => t) := by
        apply List.map_congr_left
        intro t ht
        have := hpar t ht
        omega
      _ = ts := List.map_id' ts
  simpa only [Function.comp_def, hm] using heq

end ReadTree
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
