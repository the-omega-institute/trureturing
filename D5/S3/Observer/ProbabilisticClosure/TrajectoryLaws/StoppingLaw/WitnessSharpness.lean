/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WitnessSharpness
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WitnessSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original-clock stopping witness attains the finite remote-read probability bound. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.StoppingWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

theorem witness_window (j : Bool) (k : ℕ) (hk : 1 ≤ k) :
    pathVertices (j.toInt + 1) k ⊆ lawWindow (witnessTree j k) := by
  apply SpinWindow.path_vertices_supported _ _ hk
  intro e he
  have hed : e ∈ witnessEdges j k := by
    have hh := witness_prefix_edges j k k le_rfl
    rw [List.take_of_length_le (by simp)] at hh
    exact List.mem_toFinset.mp (hh.symm ▸ he)
  have hs := ReadTree.edgeComb_support (witnessEdges j k) (!j) e hed
  exact ⟨Finset.mem_union_left _ hs.1, Finset.mem_union_left _ hs.2⟩

/-- The witness realizes the complete target law on its canonical finite dependency window. -/
theorem witness_canonical_law (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) :
    HasStoppingLaw β (lawWindow (witnessTree j k)) j k (witnessTree j k) :=
  witness_full_law β _ j k hk Finset.subset_union_right (witness_window j k hk)

theorem witness_address_bound (j : Bool) (k : ℕ) :
    ∀ t ∈ (witnessEdges j k).map (fun e => 2 * e + (!j).toInt),
      |t - j.toInt| ≤ (2 * k + 1 : ℕ) := by
  rw [witness_read_addresses]
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  have hik : i < k := List.mem_range.mp hi
  rw [show j.toInt + 2 * ((i : ℤ) + 1) + 1 - j.toInt = 2 * ((i : ℤ) + 1) + 1 by ring,
    abs_of_nonneg (by omega)]
  omega

/-- Every actual call is charged and remains within the original-clock radius. -/
theorem witness_execution_bounds (j φ : Bool) (k : ℕ) (S : Spins) :
    ((witnessTree j k).run (visible φ S)).paid ≤ k ∧
      ∀ a ∈ ((witnessTree j k).run (visible φ S)).record,
        |a.1 - j.toInt| ≤ (2 * k + 1 : ℕ) := by
  constructor
  · apply ReadTree.paid_cap
    simp [witnessTree, ReadTree.edgeComb]
  · intro a ha
    have hc (ts : List ℤ) : (ReadTree.stopComb ts).addresses = ts.toFinset := by
      induction ts with
      | nil => simp [ReadTree.stopComb, ReadTree.addresses]
      | cons t ts ih => simp [ReadTree.stopComb, ReadTree.addresses, ih]
    have hm := ReadTree.record_addresses (witnessTree j k) (visible φ S) a ha
    change a.1 ∈ (ReadTree.stopComb _).addresses at hm
    rw [hc] at hm
    exact witness_address_bound j k a.1 (List.mem_toFinset.mp hm)

theorem witness_remote_active (j : Bool) (n : ℕ) :
    remoteEvent (witnessTree j (n + 1)) j (2 * (n + 1) + 1) (!j) =
      SpinWindow.zeroEdges ((witnessEdges j (n + 1)).take n).toFinset := by
  let pre := (witnessEdges j n).map (fun e => 2 * e + (!j).toInt)
  let t : ℤ := j.toInt + 2 * ((n : ℤ) + 1) + 1
  have hsplit : (witnessEdges j (n + 1)).map (fun e => 2 * e + (!j).toInt) =
      pre ++ t :: [] := by
    rw [witness_read_addresses]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [show pre = (List.range n).map
      (fun i : ℕ => j.toInt + 2 * ((i : ℤ) + 1) + 1) from witness_read_addresses j n]
  have hn : ∀ a ∈ pre, ¬Far j (2 * (n + 1) + 1) a := by
    intro a ha
    have hb := witness_address_bound j n a ha
    unfold Far
    omega
  have ht : Far j (2 * (n + 1) + 1) t := by
    unfold Far t
    rw [abs_of_nonneg (by omega)]
    omega
  ext S
  change (∃ a ∈ ((ReadTree.stopComb _).run (visible (!j) S)).record,
    Far j (2 * (n + 1) + 1) a.1) ↔ _
  rw [hsplit, ReadTree.remote_iff_first_prefix j _ pre t [] hn ht]
  have hlen : pre.length = n := by simp [pre]
  rw [hlen]
  change ReadTree.ZeroReplies pre n (visible (!j) S) ↔
    ∀ e ∈ ((witnessEdges j (n + 1)).take n).toFinset, S e = S (e + 1)
  rw [← ReadTree.edge_zero_prefix (witnessEdges j (n + 1)) (!j) S n]
  change ReadTree.ZeroReplies pre n (visible (!j) S) ↔
    ReadTree.ZeroReplies
      ((witnessEdges j (n + 1)).map (fun e => 2 * e + (!j).toInt)) n (visible (!j) S)
  simp only [ReadTree.ZeroReplies]
  rw [hsplit, ← hlen, List.take_left, List.take_length]

/-- The witness attains the lower probability, including probability one at budget one. -/
theorem witness_remote_mass (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) :
    remoteMass β (lawWindow (witnessTree j k)) j (2 * k + 1) (witnessTree j k) =
      (1 + β.T k) / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  let V := lawWindow (witnessTree j (n + 1))
  have hq : j.toInt ∈ V := by cases j <;> simp [V, lawWindow]
  have hfar : ∃ t ∈ (witnessEdges j (n + 1)).map (fun e => 2 * e + (!j).toInt),
      Far j (2 * (n + 1) + 1) t := by
    rw [witness_read_addresses]
    refine ⟨j.toInt + 2 * ((n : ℤ) + 1) + 1,
      List.mem_map.mpr ⟨n, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    unfold Far
    rw [abs_of_nonneg (by omega)]
    omega
  have hA : SpinWindow.prob β V
      (remoteEvent (witnessTree j (n + 1)) j (2 * (n + 1) + 1) j) = 1 := by
    unfold witnessTree
    rw [ReadTree.edgeComb_opposite_remote _ _ _ hfar, SpinWindow.prob_univ]
  have hB : SpinWindow.prob β V
      (remoteEvent (witnessTree j (n + 1)) j (2 * (n + 1) + 1) (!j)) = β.T (n + 1) := by
    rw [witness_remote_active]
    apply SpinWindow.zero_prefix_mass β V j (witnessEdges j (n + 1)) hq
    · simpa only [witnessEdges_length, V, witnessTree] using
        witness_canonical_law β j (n + 1) (by omega)
    · simp
  unfold remoteMass
  change (∑ φ : Bool, SpinWindow.prob β V
    (remoteEvent (witnessTree j (n + 1)) j (2 * (n + 1) + 1) φ)) / 2 = _
  cases j <;> simp only [Fintype.sum_bool, Bool.not_false, Bool.not_true] at hA hB ⊢ <;>
    rw [hA, hB] <;> ring

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
