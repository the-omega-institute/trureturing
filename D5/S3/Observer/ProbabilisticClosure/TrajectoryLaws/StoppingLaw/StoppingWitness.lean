/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingWitness
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit stopping rule on the original clock has the complete prescribed finite law. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.RemoteReadSection

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

def witnessEdges (j : Bool) (k : ℕ) : List ℤ :=
  (List.range k).map (fun i : ℕ => j.toInt + (i : ℤ) + 1)

def witnessTree (j : Bool) (k : ℕ) : ReadTree :=
  ReadTree.edgeComb (witnessEdges j k) (!j)

@[simp] theorem witnessEdges_length (j : Bool) (k : ℕ) : (witnessEdges j k).length = k := by
  simp [witnessEdges]

theorem witness_prefix_edges (j : Bool) (k r : ℕ) (hr : r ≤ k) :
    ((witnessEdges j k).take r).toFinset = pathEdges (j.toInt + 1) r := by
  unfold witnessEdges
  rw [← List.map_take, List.take_range, Nat.min_eq_left hr]
  ext e
  simp only [List.mem_toFinset, List.mem_map, List.mem_range, pathEdges, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩; constructor <;> omega
  · intro he
    refine ⟨(e - j.toInt - 1).toNat, ?_, ?_⟩ <;> omega

theorem witness_read_addresses (j : Bool) (k : ℕ) :
    (witnessEdges j k).map (fun e => 2 * e + (!j).toInt) =
      (List.range k).map (fun i : ℕ => j.toInt + 2 * ((i : ℤ) + 1) + 1) := by
  simp only [witnessEdges, List.map_map]
  apply List.map_congr_left
  intro i _
  cases j <;> simp only [Function.comp_apply, Bool.toInt_false, Bool.toInt_true,
    Bool.not_false, Bool.not_true] <;> ring

theorem witness_opposite_run (j : Bool) (k : ℕ) (S : Spins) :
    (witnessTree j k).run (visible j S) =
      ⟨some (.a false), ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt)).map
        (fun t => (t, false))⟩ := by
  apply ReadTree.stopComb_all_zero
  intro t ht
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
  have ha : (2 * e + (!j).toInt - (!j).toInt) % 2 = 0 := by omega
  simpa only [Bool.not_not] using opposite_phase_visible (!j) S _ ha

theorem witness_outcomes (j φ : Bool) (k : ℕ) (S : Spins) :
    ((witnessTree j k).run (visible φ S)).output = some (.a false) ∧
      ((witnessTree j k).run (visible φ S)).paid = k ∨
    ((witnessTree j k).run (visible φ S)).output = some (.a true) ∧
      1 ≤ ((witnessTree j k).run (visible φ S)).paid ∧
      ((witnessTree j k).run (visible φ S)).paid ≤ k := by
  simpa only [witnessTree, ReadTree.edgeComb, List.length_map, witnessEdges_length] using
    ReadTree.stopComb_outcomes ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt))
      (visible φ S)

theorem witness_joint_prefix (β : Bias) (V : Finset ℤ) (j : Bool) (k r : ℕ)
    (hr : r ≤ k) (hq : j.toInt ∈ V) (hV : pathVertices (j.toInt + 1) k ⊆ V) (s : Bool) :
    SpinWindow.prob β V (SpinWindow.zeroEdges ((witnessEdges j k).take r).toFinset ∩
      {S | S j.toInt = s}) = β.π s * β.T (r + 1) := by
  rw [witness_prefix_edges j k r hr, SpinWindow.zero_path_eq_block]
  have ht : {S : Spins | S j.toInt = s} = SpinWindow.constant {j.toInt} s := by
    ext S; simp [SpinWindow.constant]
  rw [ht]
  have hVr : pathVertices (j.toInt + 1) r ⊆ V := by
    intro a ha
    apply hV
    simp only [pathVertices, Finset.mem_Icc] at ha ⊢
    omega
  have hd : Disjoint (pathVertices (j.toInt + 1) r) ({j.toInt} : Finset ℤ) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_singleton] at hb
    subst a
    simp [pathVertices] at ha
  rw [SpinWindow.block_constant_prob β V _ _ hVr (by simpa) hd
    ⟨j.toInt + 1, by simp [pathVertices]⟩, vertices_card]
  simp [mul_comm]

theorem witness_joint_stop (β : Bias) (V : Finset ℤ) (j : Bool) (k i : ℕ)
    (hi : 1 ≤ i) (hik : i ≤ k) (hq : j.toInt ∈ V)
    (hV : pathVertices (j.toInt + 1) k ⊆ V) (s : Bool) :
    SpinWindow.prob β V {S | S j.toInt = s ∧
      ((witnessTree j k).run (visible (!j) S)).output = some (.a true) ∧
      ((witnessTree j k).run (visible (!j) S)).paid = i} = β.π s * β.d i := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, i = r + 1 := ⟨i - 1, by omega⟩
  have hd := SpinWindow.zero_edge_difference (witnessEdges j k) (!j) r (by simp; omega)
  let C := SpinWindow.zeroEdges ((witnessEdges j k).take r).toFinset ∩ {S | S j.toInt = s}
  let D := SpinWindow.zeroEdges ((witnessEdges j k).take (r + 1)).toFinset ∩ {S | S j.toInt = s}
  have hsub : D ⊆ C := fun _ h => ⟨SpinWindow.zero_prefix_antitone _ (by omega) h.1, h.2⟩
  have he : {S : Spins | S j.toInt = s ∧
      ((witnessTree j k).run (visible (!j) S)).output = some (.a true) ∧
      ((witnessTree j k).run (visible (!j) S)).paid = r + 1} = C \ D := by
    calc
      _ = {S | S j.toInt = s} ∩
          (SpinWindow.zeroEdges ((witnessEdges j k).take r).toFinset \
            SpinWindow.zeroEdges ((witnessEdges j k).take (r + 1)).toFinset) := by
        rw [hd]; rfl
      _ = C \ D := by
        ext S
        simp only [C, D, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
        tauto
  rw [he, SpinWindow.prob_diff β V hsub,
    witness_joint_prefix β V j k r (by omega) hq hV s,
    witness_joint_prefix β V j k (r + 1) hik hq hV s]
  unfold Bias.d
  ring

theorem witness_joint_final (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ)
    (hq : j.toInt ∈ V) (hV : pathVertices (j.toInt + 1) k ⊆ V) (s : Bool) :
    SpinWindow.prob β V {S | S j.toInt = s ∧
      ((witnessTree j k).run (visible (!j) S)).output = some (.a false) ∧
      ((witnessTree j k).run (visible (!j) S)).paid = k} = β.π s * β.T (k + 1) := by
  have he : {S : Spins | S j.toInt = s ∧
      ((witnessTree j k).run (visible (!j) S)).output = some (.a false) ∧
      ((witnessTree j k).run (visible (!j) S)).paid = k} =
      SpinWindow.zeroEdges ((witnessEdges j k).take k).toFinset ∩ {S | S j.toInt = s} := by
    ext S
    have hp := ReadTree.zero_prefix_final
      ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (visible (!j) S)
    simp only [List.length_map, witnessEdges_length] at hp
    rw [ReadTree.edge_zero_prefix] at hp
    change (S j.toInt = s ∧
      ((ReadTree.stopComb ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt))).run
        (visible (!j) S)).output = some (.a false) ∧
      ((ReadTree.stopComb ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt))).run
        (visible (!j) S)).paid = k) ↔
      (∀ e ∈ ((witnessEdges j k).take k).toFinset, S e = S (e + 1)) ∧ S j.toInt = s
    rw [hp]
    tauto
  rw [he]
  exact witness_joint_prefix β V j k k le_rfl hq hV s

/-- Unsupported outputs and nonreturn indicators have zero complete source mass. -/
theorem witness_mass_support (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ) (z : Observation)
    (h : z.returned ≠ true ∨ (z.output ≠ some (.a false) ∧ z.output ≠ some (.a true))) :
    fullMass β V j (witnessTree j k) z = 0 := by
  have he (φ : Bool) : {S : Spins | observation j φ (witnessTree j k) S = z} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro S hz
    have ho := witness_outcomes j φ k S
    have hret : (observation j φ (witnessTree j k) S).returned = true := by
      rcases ho with ho | ho <;> simp [observation, Execution.returned, ho.1]
    have hout : (observation j φ (witnessTree j k) S).output = some (.a false) ∨
        (observation j φ (witnessTree j k) S).output = some (.a true) := ho.elim
          (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    change observation j φ (witnessTree j k) S = z at hz
    rw [hz] at hret hout
    rcases h with h | h
    · exact h hret
    · exact hout.elim h.1 h.2
  simp [fullMass, he]

/-- Exact full law on any finite window containing the used block and target coordinates. -/
theorem witness_full_law (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ) (hk : 1 ≤ k)
    (h01 : ({0, 1} : Finset ℤ) ⊆ V) (hV : pathVertices (j.toInt + 1) k ⊆ V) :
    HasStoppingLaw β V j k (witnessTree j k) := by
  have hq : j.toInt ∈ V := h01 (by cases j <;> simp)
  have hqa : targetIndex j j ∈ V := h01 (by cases j <;> simp [targetIndex])
  intro z
  rcases z with ⟨h, o, d, n⟩
  cases d with
  | false =>
    rw [witness_mass_support β V j k _ (Or.inl (by simp))]
    rfl
  | true =>
    by_cases ho : o = some (.a false) ∨ o = some (.a true)
    · rcases ho with rfl | rfl
      · cases h with
        | a s =>
          have hm := ReadTree.fullMass_a β V j s (witnessTree j k) (some (.a false)) n
          simp only [Option.isSome_some] at hm
          rw [hm]
          have he : {S : Spins | S (targetIndex j j) = s ∧
              ((witnessTree j k).run (visible j S)).output = some (.a false) ∧
              ((witnessTree j k).run (visible j S)).paid = n} =
              if n = k then {S | S (targetIndex j j) = s} else ∅ := by
            ext S
            simp [witness_opposite_run, Execution.paid, eq_comm, and_comm]
          rw [he]
          by_cases hn : n = k <;> simp [stoppingMass, hn, SpinWindow.spin_prob β V _ hqa s]
        | b s =>
          have hm := ReadTree.fullMass_b β V j s (witnessTree j k) (some (.a false)) n
          simp only [Option.isSome_some] at hm
          rw [hm]
          by_cases hn : n = k
          · subst n
            rw [witness_joint_final β V j k hq hV s]
            simp [stoppingMass]
          · have he : {S : Spins | S j.toInt = s ∧
                ((witnessTree j k).run (visible (!j) S)).output = some (.a false) ∧
                ((witnessTree j k).run (visible (!j) S)).paid = n} = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro S hS
              obtain ⟨_, hout, hpaid⟩ := hS
              rcases witness_outcomes j (!j) k S with h | h
              · exact hn (hpaid.symm.trans h.2)
              · have := hout.symm.trans h.1; cases this
            simp [he, stoppingMass, hn]
      · cases h with
        | a s =>
          have hm := ReadTree.fullMass_a β V j s (witnessTree j k) (some (.a true)) n
          simp only [Option.isSome_some] at hm
          rw [hm]
          have he : {S : Spins | S (targetIndex j j) = s ∧
              ((witnessTree j k).run (visible j S)).output = some (.a true) ∧
              ((witnessTree j k).run (visible j S)).paid = n} = ∅ := by
            ext S; simp [witness_opposite_run]
          simp [he, stoppingMass]
        | b s =>
          have hm := ReadTree.fullMass_b β V j s (witnessTree j k) (some (.a true)) n
          simp only [Option.isSome_some] at hm
          rw [hm]
          by_cases hn : 1 ≤ n ∧ n ≤ k
          · rw [witness_joint_stop β V j k n hn.1 hn.2 hq hV s]
            simp [stoppingMass, hn]
          · have he : {S : Spins | S j.toInt = s ∧
                ((witnessTree j k).run (visible (!j) S)).output = some (.a true) ∧
                ((witnessTree j k).run (visible (!j) S)).paid = n} = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro S hS
              obtain ⟨_, hout, hpaid⟩ := hS
              rcases witness_outcomes j (!j) k S with h | h
              · have := hout.symm.trans h.1; cases this
              · exact hn (by simpa [hpaid] using h.2)
            simp [he, stoppingMass, hn]
    · rw [witness_mass_support β V j k _ (Or.inr (not_or.mp ho))]
      cases h <;> cases o with
      | none => rfl
      | some out => cases out with
        | b s => rfl
        | a s => cases s <;> simp_all

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
