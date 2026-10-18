/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete finite stopping law forces the exact comb, consecutive edges, and target separation. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.StoppingJointPrefixes

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- A finite window containing every potential source dependency and both possible target indices. -/
def lawWindow (T : ReadTree) : Finset ℤ := T.support ∪ {0, 1}

namespace ReadTree

theorem edgeComb_support (es : List ℤ) (φ : Bool) :
    ∀ e ∈ es, e ∈ (edgeComb es φ).support ∧ e + 1 ∈ (edgeComb es φ).support := by
  induction es with
  | nil => simp
  | cons a es ih =>
    intro e he
    simp only [edgeComb, List.map_cons, stopComb, support]
    rcases List.mem_cons.mp he with rfl | he
    · have h0 : e ∈ ({(2 * e + φ.toInt) / 2, (2 * e + φ.toInt) / 2 + 1,
          (2 * e + φ.toInt - 1) / 2, (2 * e + φ.toInt - 1) / 2 + 1} : Finset ℤ) := by
        cases φ <;> simp
      have h1 : e + 1 ∈ ({(2 * e + φ.toInt) / 2, (2 * e + φ.toInt) / 2 + 1,
          (2 * e + φ.toInt - 1) / 2, (2 * e + φ.toInt - 1) / 2 + 1} : Finset ℤ) := by
        cases φ <;> simp
      exact ⟨Finset.mem_union_left _ h0, Finset.mem_union_left _ h1⟩
    · have hh := ih e he
      exact ⟨Finset.mem_union_right _ (Finset.mem_union_left _ hh.1),
        Finset.mem_union_right _ (Finset.mem_union_left _ hh.2)⟩

end ReadTree

/-- Full law recovers tree constructors and integer geometry at each fixed biased parameter. -/
theorem finite_full_law_forces_stopping_path (β : Bias) (j : Bool) (k : ℕ)
    (hk : 1 ≤ k) (T : ReadTree) (hh : T.height ≤ k)
    (hlaw : HasStoppingLaw β (lawWindow T) j k T) :
    ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
      T = ReadTree.stopComb (es.map (fun e => 2 * e + (!j).toInt)) ∧
      es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k := by
  have hV : T.support ⊆ lawWindow T := Finset.subset_union_left
  obtain ⟨hA, hB⟩ := ReadTree.stopping_law_sections β (lawWindow T) j k T hV hlaw
  obtain ⟨es, hlen, heq⟩ := ReadTree.stopComb_edge_indices k T (!j) hh hA hB
  have hcomb : T = ReadTree.edgeComb es (!j) := heq
  have hes : SpinWindow.SupportsEdges (lawWindow T) es := by
    intro e he
    have hs := ReadTree.edgeComb_support es (!j) e he
    rw [← hcomb] at hs
    exact ⟨hV hs.1, hV hs.2⟩
  have hq : j.toInt ∈ lawWindow T := by cases j <;> simp [lawWindow]
  have hlaw' : HasStoppingLaw β (lawWindow T) j es.length (ReadTree.edgeComb es (!j)) := by
    simpa only [hlen, ← hcomb] using hlaw
  have hm : SpinWindow.PrefixMasses β (lawWindow T) es := fun r _ hr =>
    SpinWindow.zero_prefix_mass β (lawWindow T) j es hq hlaw' r hr
  have ht (s : Bool) :
      SpinWindow.prob β (lawWindow T) (SpinWindow.zeroEdges es.toFinset ∩ {S | S j.toInt = s}) =
        β.π s * β.T (es.length + 1) := by
    simpa only [List.take_length] using
      SpinWindow.joint_zero_prefix_mass β (lawWindow T) j es hq hlaw' s es.length le_rfl
  obtain ⟨hnod, L, hL, hsep⟩ :=
    SpinWindow.finite_path_geometry β (lawWindow T) es j.toInt (by omega) hes hm ht
  exact ⟨es, hlen, hnod, L, heq, by simpa only [hlen] using hL,
    by simpa only [hlen] using hsep⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
