/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full laws on arbitrary unchanged seed spaces force deterministic source sections. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

def witnessEdges (j : Bool) (k : ℕ) : List ℤ :=
  (List.range k).map (fun i : ℕ => j.toInt + (i : ℤ) + 1)

def witnessTree (j : Bool) (k : ℕ) : ReadTree :=
  ReadTree.edgeComb (witnessEdges j k) (!j)

@[simp] private theorem witnessEdges_length (j : Bool) (k : ℕ) : (witnessEdges j k).length = k := by
  simp [witnessEdges]

private theorem witness_prefix_edges (j : Bool) (k r : ℕ) (hr : r ≤ k) :
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

private theorem witness_opposite_run (j : Bool) (k : ℕ) (S : Spins) :
    (witnessTree j k).run (visible j S) =
      ⟨some (.a false), ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt)).map
        (fun t => (t, false))⟩ := by
  apply ReadTree.stopComb_all_zero
  intro t ht
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
  have ha : (2 * e + (!j).toInt - (!j).toInt) % 2 = 0 := by omega
  simpa only [Bool.not_not] using opposite_phase_visible (!j) S _ ha

private theorem witness_outcomes (j φ : Bool) (k : ℕ) (S : Spins) :
    ((witnessTree j k).run (visible φ S)).output = some (.a false) ∧
      ((witnessTree j k).run (visible φ S)).paid = k ∨
    ((witnessTree j k).run (visible φ S)).output = some (.a true) ∧
      1 ≤ ((witnessTree j k).run (visible φ S)).paid ∧
      ((witnessTree j k).run (visible φ S)).paid ≤ k := by
  simpa only [witnessTree, ReadTree.edgeComb, List.length_map, witnessEdges_length] using
    ReadTree.stopComb_outcomes ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt))
      (visible φ S)

private theorem witness_joint_prefix (β : Bias) (V : Finset ℤ) (j : Bool) (k r : ℕ)
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

private theorem witness_joint_stop (β : Bias) (V : Finset ℤ) (j : Bool) (k i : ℕ)
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

private theorem witness_joint_final (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ)
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
private theorem witness_mass_support (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ) (z : Observation)
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
private theorem witness_full_law (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ) (hk : 1 ≤ k)
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

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

private theorem witness_window (j : Bool) (k : ℕ) (hk : 1 ≤ k) :
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

private theorem witness_address_bound (j : Bool) (k : ℕ) :
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
private theorem witness_execution_bounds (j φ : Bool) (k : ℕ) (S : Spins) :
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

private theorem witness_remote_active (j : Bool) (n : ℕ) :
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
private theorem witness_remote_mass (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) :
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

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
universe u

/-- Evaluation on a countable tree space is jointly measurable. -/
private theorem measurable_tree_observation (j : Bool) :
    Measurable (fun p : SourcePoint × ReadTree => observation j p.1.1 p.2 p.1.2) :=
  measurable_from_prod_countable_left (fun T => measurable_observation j T)

def selectorJoint {U : Type u} (j : Bool) (T : U → ReadTree)
    (z : SourcePoint × U) : U × Observation := (z.2, observation j z.1.1 (T z.2) z.1.2)

theorem measurable_selectorJoint {U : Type u} [MeasurableSpace U]
    (j : Bool) (T : U → ReadTree) (hT : Measurable T) : Measurable (selectorJoint j T) :=
  measurable_snd.prodMk ((measurable_tree_observation j).comp
    (measurable_fst.prodMk (hT.comp measurable_snd)))

namespace RawRule
variable {U : Type u} [MeasurableSpace U]

def rawObservation (Q : RawRule U) (j : Bool) (s : SourcePoint) (u : U) : Observation :=
  let o := Q.output u (visible s.1 s.2)
  ⟨hidden s.1 s.2 j.toInt, o, decide (Q.returnTime u (visible s.1 s.2) < ⊤),
    (Q.paidCount u (visible s.1 s.2)).toNat⟩

def joint (Q : RawRule U) (j : Bool) (z : SourcePoint × U) : U × Observation :=
  (z.2, Q.rawObservation j z.1 z.2)

def fullLaw (Q : RawRule U) (β : Bias) (j : Bool) (ν : Measure U) : Measure (U × Observation) :=
  ((sourceLaw β).prod ν).map (Q.joint j)

def SameFullLaw (Q R : RawRule U) (β : Bias) (j : Bool) (ν : Measure U) : Prop :=
  Q.fullLaw β j ν = R.fullLaw β j ν

private theorem observation_normalize (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k)
    (j : Bool) (s : SourcePoint) (u : U) :
    Q.rawObservation j s u = StoppingLaw.observation j s.1 (Q.normalize k u) s.2 := by
  obtain ⟨_, ho, hn⟩ := Q.normalization_pointwise k hc s.1 s.2 u
  simp only [rawObservation, StoppingLaw.observation, ho, hn, ENat.toNat_natCast,
    Q.normalization_return_indicator k hc]

private theorem joint_normalize (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k) (j : Bool) :
    Q.joint j = selectorJoint j (Q.normalize k) := by
  funext z
  exact congrArg (Prod.mk z.2) (Q.observation_normalize k hc j z.1 z.2)

private theorem Lawful.completionLawful {Q : RawRule U} (hQ : Q.Lawful) (ν : Measure U) :
    Q.CompletionLawful ν :=
  ⟨fun r => (hQ.measurable_next r).nullMeasurable.measurable',
    fun r => (hQ.measurable_wait r).nullMeasurable.measurable'⟩

private theorem aemeasurable_normalize (Q : RawRule U) (ν : Measure U)
    (hQ : Q.CompletionLawful ν) (k : ℕ) : AEMeasurable (Q.normalize k) ν := by
  obtain ⟨T₀, hm, he⟩ := Q.completion_normalization_version ν hQ k
  have he' : Q.normalize k =ᵐ[ν] (fun u => (T₀ u).val) := he
  exact (measurable_subtype_coe.comp hm).aemeasurable.congr he'.symm

private theorem aemeasurable_joint (Q : RawRule U) (ν : Measure U) (β : Bias)
    (hQ : Q.CompletionLawful ν) (k : ℕ) (hc : Q.TotalCap k) (j : Bool) :
    AEMeasurable (Q.joint j) ((sourceLaw β).prod ν) := by
  rw [Q.joint_normalize k hc]
  have hn : AEMeasurable (fun p : SourcePoint × U => Q.normalize k p.2)
      ((sourceLaw β).prod ν) := (Q.aemeasurable_normalize ν hQ k).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd
  have hp : AEMeasurable (fun p : SourcePoint × U => (p.1, Q.normalize k p.2))
      ((sourceLaw β).prod ν) := measurable_fst.aemeasurable.prodMk hn
  exact measurable_snd.aemeasurable.prodMk
    ((measurable_tree_observation j).comp_aemeasurable hp)

/-- No change of seed space or measure occurs when a tree selector is realized. -/
theorem fullLaw_realize (T : U → ReadTree) (k : ℕ) (hT : ∀ u, (T u).height ≤ k)
    (β : Bias) (j : Bool) (ν : Measure U) :
    (realize T).fullLaw β j ν = ((sourceLaw β).prod ν).map (selectorJoint j T) := by
  have hc := realize_cap T k hT
  unfold fullLaw
  congr 1
  rw [(realize T).joint_normalize k hc]
  have he : (realize T).normalize k = T := by
    funext u; exact normalize_realize T k u (hT u)
  rw [he]

end RawRule

/-- Countable fibers recover source sections from the complete unchanged-seed joint law. -/
private theorem selector_full_law_sections {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν]
    (T : U → ReadTree) (hT : Measurable T) (w : SourcePoint → Observation) (hw : Measurable w)
    (hlaw : ((sourceLaw β).prod ν).map (selectorJoint j T) =
      ((sourceLaw β).prod ν).map (fun z : SourcePoint × U => (z.2, w z.1))) :
    ∀ᵐ u ∂ν, ∀ z : Observation,
      fullMass β (lawWindow (T u)) j (T u) z = (sourceLaw β).real (w ⁻¹' {z}) := by
  have hfiber (t : ReadTree) (hne : ν (T ⁻¹' {t}) ≠ 0) (z : Observation) :
      fullMass β (lawWindow t) j t z = (sourceLaw β).real (w ⁻¹' {z}) := by
    let B := T ⁻¹' {t}
    have hB : MeasurableSet B := hT (measurableSet_singleton t)
    have h := congrArg (fun μ : Measure (U × Observation) => μ.real (B ×ˢ {z})) hlaw
    have hwj : Measurable (fun p : SourcePoint × U => (p.2, w p.1)) :=
      measurable_snd.prodMk (hw.comp measurable_fst)
    rw [map_measureReal_apply (measurable_selectorJoint j T hT)
      (hB.prod (measurableSet_singleton z)),
      map_measureReal_apply hwj (hB.prod (measurableSet_singleton z))] at h
    have he : selectorJoint j T ⁻¹' (B ×ˢ {z}) =
        {s : SourcePoint | observation j s.1 t s.2 = z} ×ˢ B := by
      ext p
      simp only [selectorJoint, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨hb, hz⟩
        have ht : T p.2 = t := hb
        exact ⟨by simpa only [ht] using hz, hb⟩
      · rintro ⟨hz, hb⟩
        have ht : T p.2 = t := hb
        exact ⟨hb, by simpa only [ht] using hz⟩
    have he' : (fun p : SourcePoint × U => (p.2, w p.1)) ⁻¹' (B ×ˢ {z}) =
        (w ⁻¹' {z}) ×ˢ B := by ext p; simp; tauto
    rw [he, he', measureReal_prod_prod, measureReal_prod_prod, sourceLaw_observation] at h
    have hreal : ν.real B ≠ 0 := by
      exact (ENNReal.toReal_ne_zero).2 ⟨hne, measure_ne_top _ _⟩
    exact mul_right_cancel₀ hreal h
  have hall : ∀ᵐ u ∂ν, ∀ t : ReadTree, T u = t → ∀ z : Observation,
      fullMass β (lawWindow t) j t z = (sourceLaw β).real (w ⁻¹' {z}) := by
    apply ae_all_iff.2
    intro t
    by_cases hzero : ν (T ⁻¹' {t}) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with u hu
      intro ht
      exact (hu ht).elim
    · exact Filter.Eventually.of_forall (fun _ _ z => hfiber t hzero z)
  filter_upwards [hall] with u hu
  exact hu (T u) rfl

/-- Completed next-event versions are first normalized pointwise, then transported a.e. -/
theorem full_same_seed_law_forces_sections {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν]
    (Q : RawRule U) (hQ : Q.CompletionLawful ν) (k : ℕ) (hc : Q.TotalCap k)
    (w : SourcePoint → Observation) (hw : Measurable w)
    (hlaw : Q.fullLaw β j ν =
      ((sourceLaw β).prod ν).map (fun z : SourcePoint × U => (z.2, w z.1))) :
    ∀ᵐ u ∂ν, ∀ z : Observation,
      fullMass β (lawWindow (Q.normalize k u)) j (Q.normalize k u) z =
        (sourceLaw β).real (w ⁻¹' {z}) := by
  obtain ⟨T₀, hm, he, ht⟩ := Q.completion_normalization_bridge ν hQ k hc
  let T : U → ReadTree := fun u => (T₀ u).val
  have hT : Measurable T := measurable_subtype_coe.comp hm
  have hj : Q.joint j =ᵐ[(sourceLaw β).prod ν] selectorJoint j T := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae ht] with p hp
    obtain ⟨_, ho, hn⟩ := hp p.1.1 p.1.2
    have hd : decide (Q.returnTime p.2 (visible p.1.1 p.1.2) < ⊤) =
        ((T₀ p.2).val.run (visible p.1.1 p.1.2)).returned := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq, Execution.returned, ho] using
        Q.finite_return_iff p.2 (visible p.1.1 p.1.2)
    simp only [RawRule.joint, RawRule.rawObservation, selectorJoint,
      StoppingLaw.observation, ho, hn, hd, ENat.toNat_natCast, T]
  have hmap : ((sourceLaw β).prod ν).map (selectorJoint j T) =
      ((sourceLaw β).prod ν).map (fun z : SourcePoint × U => (z.2, w z.1)) :=
    (Measure.map_congr hj).symm.trans hlaw
  have hsections := selector_full_law_sections β j ν T hT w hw hmap
  filter_upwards [he, hsections] with u hu hs
  simpa only [hu, T] using hs

/-- The lawful stopping witness ignores its unchanged seed and the bias parameter. -/
def stoppingRule {U : Type u} [MeasurableSpace U] (j : Bool) (k : ℕ) : RawRule U :=
  RawRule.realize (fun _ => witnessTree j k)

private theorem stoppingRule_height (j : Bool) (k : ℕ) : (witnessTree j k).height ≤ k := by
  simp [witnessTree, ReadTree.edgeComb]

private theorem stoppingRule_lawful {U : Type u} [MeasurableSpace U] (j : Bool) (k : ℕ) :
    (stoppingRule (U := U) j k).Lawful := RawRule.realize_lawful _ measurable_const

private theorem stoppingRule_cap {U : Type u} [MeasurableSpace U] (j : Bool) (k : ℕ) :
    (stoppingRule (U := U) j k).TotalCap k :=
  RawRule.realize_cap _ k (fun _ => stoppingRule_height j k)

/-- The witness has the exact full original-source mass on every measurable seed rectangle. -/
theorem stopping_witness_full_law {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν]
    (B : Set U) (hB : MeasurableSet B) (z : Observation) :
    ((stoppingRule j k).fullLaw β j ν).real (B ×ˢ {z}) =
      ν.real B * stoppingMass β k z := by
  let W : RawRule U := stoppingRule j k
  have hc : W.TotalCap k := stoppingRule_cap j k
  have hW : W.CompletionLawful ν := (stoppingRule_lawful j k).completionLawful ν
  rw [RawRule.fullLaw, map_measureReal_apply_of_aemeasurable
    (W.aemeasurable_joint ν β hW k hc j) (hB.prod (measurableSet_singleton z))]
  have he : W.joint j ⁻¹' (B ×ˢ {z}) =
      {s : SourcePoint | observation j s.1 (witnessTree j k) s.2 = z} ×ˢ B := by
    ext p
    have ho := W.observation_normalize k hc j p.1 p.2
    have hn : W.normalize k p.2 = witnessTree j k :=
      RawRule.normalize_realize _ k p.2 (stoppingRule_height j k)
    rw [hn] at ho
    simp only [RawRule.joint, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_setOf_eq, ho]
    tauto
  rw [he, measureReal_prod_prod, sourceLaw_observation, witness_canonical_law β j k hk z]
  ring

/-- Full original-rule law forces the finite-core stopping law at almost every seed. -/
private theorem original_stopping_law_sections {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν]
    (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k)
    (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν) :
    ∀ᵐ u ∂ν, HasStoppingLaw β (lawWindow (Q.normalize k u)) j k (Q.normalize k u) := by
  have hW := RawRule.fullLaw_realize (fun _ : U => witnessTree j k) k
    (fun _ => stoppingRule_height j k) β j ν
  have hj : Q.fullLaw β j ν = ((sourceLaw β).prod ν).map
      (fun z : SourcePoint × U => (z.2, observation j z.1.1 (witnessTree j k) z.1.2)) :=
    hlaw.trans hW
  have hs := full_same_seed_law_forces_sections β j ν Q hQ k hc
    (fun s => observation j s.1 (witnessTree j k) s.2)
    (measurable_observation j (witnessTree j k)) hj
  filter_upwards [hs] with u hu
  apply (hasStoppingLaw_iff_capped β (lawWindow (Q.normalize k u)) j k
    (Q.normalize k u) (Q.unfold_height k u [])).2
  intro z
  rw [hu z.val]
  exact (sourceLaw_observation β j (witnessTree j k) z.val).trans
    (witness_canonical_law β j k hk z.val)

/-- Arbitrary raw lawful competitors obey stopping-tree rigidity on the original clock. -/
theorem original_rule_stopping_rigidity {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν]
    (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k)
    (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν) :
    ∀ᵐ u ∂ν, ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
      Q.normalize k u = ReadTree.stopComb (es.map (fun e => 2 * e + (!j).toInt)) ∧
      es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k := by
  filter_upwards [original_stopping_law_sections β j k hk ν Q hQ hc hlaw] with u hu
  exact finite_full_law_forces_stopping_path β j k hk (Q.normalize k u)
    (Q.unfold_height k u []) hu

def selectorRemote {U : Type u} (T : U → ReadTree) (j : Bool) (R : ℕ) :
    Set (SourcePoint × U) :=
  {p | ∃ a ∈ ((T p.2).run (visible p.1.1 p.1.2)).record, Far j R a.1}

private theorem measurable_selectorRemote {U : Type u} [MeasurableSpace U]
    (T : U → ReadTree) (hT : Measurable T) (j : Bool) (R : ℕ) :
    MeasurableSet (selectorRemote T j R) := by
  have he : Measurable (fun p : SourcePoint × ReadTree => p.2.run (visible p.1.1 p.1.2)) := by
    apply measurable_from_prod_countable_left
    intro t
    exact measurable_from_prod_countable_right t.measurable_source_run
  exact (he.comp (measurable_fst.prodMk (hT.comp measurable_snd)))
    (MeasurableSet.of_discrete (s := {v : Execution | ∃ a ∈ v.record, Far j R a.1}))

namespace RawRule
variable {U : Type u} [MeasurableSpace U]

/-- An actual paid call, formulated before any cap or normalization is imposed. -/
def remote (Q : RawRule U) (j : Bool) (R : ℕ) : Set (SourcePoint × U) :=
  {p | ∃ n r, Q.readPrefix p.2 (visible p.1.1 p.1.2) n = some r ∧
    ∃ a ∈ r, Far j R a.1}

def WithinActualRadius (Q : RawRule U) (j : Bool) (R : ℕ) : Prop :=
  ∀ (φ : Bool) (S : Spins) (u : U) (n : ℕ) (r : Record),
    Q.readPrefix u (visible φ S) n = some r →
      ∀ a ∈ r, |a.1 - j.toInt| ≤ (R : ℤ)

private theorem remote_normalize (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k) (j : Bool) (R : ℕ) :
    Q.remote j R = selectorRemote (Q.normalize k) j R := by
  ext p
  have hv := (Q.normalization_pointwise k hc p.1.1 p.1.2 p.2).1
  constructor
  · rintro ⟨n, r, hr, a, ha, hf⟩
    exact ⟨a, Q.completes_record_subset _ _ hv hr a ha, hf⟩
  · rintro ⟨a, ha, hf⟩
    exact ⟨_, _, hv.1, a, ha, hf⟩

end RawRule

/-- Measurable countable selectors integrate their finite source-section bounds. -/
private theorem selector_remote_lower_bound {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν]
    (T : U → ReadTree) (hT : Measurable T) (hh : ∀ u, (T u).height ≤ k)
    (hlaw : ∀ᵐ u ∂ν, HasStoppingLaw β (lawWindow (T u)) j k (T u)) :
    (1 + β.T k) / 2 ≤ ((sourceLaw β).prod ν).real (selectorRemote T j (2 * k + 1)) := by
  have hsec : ∀ᵐ u ∂ν, ENNReal.ofReal ((1 + β.T k) / 2) ≤
      sourceLaw β {s | (s,u) ∈ selectorRemote T j (2 * k + 1)} := by
    filter_upwards [hlaw] with u hu
    obtain ⟨m, _, _, _, hb⟩ := finite_remote_read_section β j k hk (T u) (hh u) hu
    have hm := sourceLaw_remote β j (2 * k + 1) (T u)
    have hr : (1 + β.T k) / 2 ≤ (sourceLaw β).real
        {s | (s,u) ∈ selectorRemote T j (2 * k + 1)} := by
      exact hb.trans_eq hm.symm
    have := ENNReal.ofReal_le_ofReal hr
    rw [ofReal_measureReal (μ := sourceLaw β)] at this
    exact this
  have hb := lintegral_mono_ae hsec
  rw [lintegral_const, measure_univ, mul_one] at hb
  have hp := Measure.prod_apply_symm (μ := sourceLaw β) (ν := ν)
    (measurable_selectorRemote T hT j (2 * k + 1))
  have hb' := hb.trans_eq hp.symm
  have := ENNReal.toReal_mono (measure_ne_top _ _) hb'
  rw [ENNReal.toReal_ofReal (by
    have : 0 ≤ β.T k := by
      exact add_nonneg (pow_nonneg (sub_nonneg.mpr β.lt_one.le) _) (pow_nonneg β.pos.le _)
    positivity)] at this
  exact this

/-- Sharp lower probability for actual paid reads of every raw original-rule competitor. -/
private theorem original_rule_remote_probability {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν]
    (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k)
    (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν) :
    (1 + β.T k) / 2 ≤ ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) := by
  obtain ⟨T₀, hm, he⟩ := Q.completion_normalization_version ν hQ k
  let T : U → ReadTree := fun u => (T₀ u).val
  have hT : Measurable T := measurable_subtype_coe.comp hm
  have hs := original_stopping_law_sections β j k hk ν Q hQ hc hlaw
  have hLaw : ∀ᵐ u ∂ν, HasStoppingLaw β (lawWindow (T u)) j k (T u) := by
    filter_upwards [he, hs] with u hu hs
    simpa only [hu, T] using hs
  have hb := selector_remote_lower_bound β j k hk ν T hT (fun u => (T₀ u).property) hLaw
  have hE : Q.remote j (2 * k + 1) =ᵐ[(sourceLaw β).prod ν]
      selectorRemote T j (2 * k + 1) := by
    rw [Q.remote_normalize k hc]
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae he] with p hp
    simp only [selectorRemote, Set.mem_setOf_eq, hp, T]
  exact hb.trans_eq (congrArg ENNReal.toReal (measure_congr hE)).symm

/-- The raw witness attains the remote-read bound on the same arbitrary seed space. -/
private theorem stopping_witness_remote_probability {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] :
    ((sourceLaw β).prod ν).real ((stoppingRule (U := U) j k).remote j (2 * k + 1)) =
      (1 + β.T k) / 2 := by
  rw [RawRule.remote_normalize _ k (stoppingRule_cap j k)]
  have hn : (stoppingRule (U := U) j k).normalize k = fun _ => witnessTree j k := by
    funext u; exact RawRule.normalize_realize _ k u (stoppingRule_height j k)
  rw [hn]
  have he : selectorRemote (fun _ : U => witnessTree j k) j (2 * k + 1) =
      {s : SourcePoint | ∃ a ∈ ((witnessTree j k).run (visible s.1 s.2)).record,
        Far j (2 * k + 1) a.1} ×ˢ Set.univ := by
    ext p; simp [selectorRemote]
  rw [he, measureReal_prod_prod, probReal_univ, mul_one, sourceLaw_remote]
  exact witness_remote_mass β j k hk

/-- Both the universal bound and its attainment concern actual paid original-rule reads. -/
theorem original_rule_sharp_remote_probability {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν]
    (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k)
    (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν) :
    ((1 + β.T k) / 2 ≤ ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) ∧
      ((sourceLaw β).prod ν).real ((stoppingRule (U := U) j k).remote j (2 * k + 1)) =
        (1 + β.T k) / 2) ∧
      (k = 1 → ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) = 1) := by
  have hb := original_rule_remote_probability β j k hk ν Q hQ hc hlaw
  refine ⟨⟨hb, stopping_witness_remote_probability β j k hk ν⟩, ?_⟩
  intro hk1
  apply le_antisymm measureReal_le_one
  simpa [hk1, β.T_one] using hb

/-- The witness stays inside radius 2k+1 on every source and seed, including null paths. -/
private theorem stopping_witness_radius {U : Type u} [MeasurableSpace U] (j : Bool) (k : ℕ) :
    (stoppingRule (U := U) j k).WithinActualRadius j (2 * k + 1) := by
  intro φ S u n r hr a ha
  have hnorm := (stoppingRule (U := U) j k).normalization_pointwise k
    (stoppingRule_cap j k) φ S u
  have hn : (stoppingRule (U := U) j k).normalize k u = witnessTree j k :=
    RawRule.normalize_realize _ k u (stoppingRule_height j k)
  have hmem := (stoppingRule (U := U) j k).completes_record_subset _ _ hnorm.1 hr a ha
  rw [hn] at hmem
  exact (witness_execution_bounds j φ k S).2 a hmem

/-- The complete original-rule witness contract, including all formal branch returns. -/
theorem stopping_witness_original_contract {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] :
    (stoppingRule (U := U) j k).Lawful ∧ (stoppingRule (U := U) j k).TotalCap k ∧
      (∀ v ∈ (witnessTree j k).formalRuns,
        v.returned = true ∧ 1 ≤ v.paid ∧ v.paid ≤ k) ∧
      (∀ B : Set U, MeasurableSet B → ∀ z : Observation,
        ((stoppingRule j k).fullLaw β j ν).real (B ×ˢ {z}) =
          ν.real B * stoppingMass β k z) ∧
      (stoppingRule (U := U) j k).WithinActualRadius j (2 * k + 1) := by
  refine ⟨stoppingRule_lawful j k, stoppingRule_cap j k, ?_,
    (fun B hB z => stopping_witness_full_law β j k hk ν B hB z),
    stopping_witness_radius j k⟩
  intro v hv
  have hout : v.output = some (.a false) ∧ v.paid = k ∨
      v.output = some (.a true) ∧ 1 ≤ v.paid ∧ v.paid ≤ k := by
    simpa only [witnessTree, ReadTree.edgeComb, List.length_map, witnessEdges_length] using
      ReadTree.stopComb_formal_outcomes
        ((witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) v hv
  rcases hout with ⟨ho, hn⟩ | ⟨ho, hn, hb⟩
  · exact ⟨by simp [Execution.returned, ho], by omega, by omega⟩
  · exact ⟨by simp [Execution.returned, ho], hn, hb⟩

/-- The actual positive-mass remote event excludes every smaller preserving radius. -/
theorem original_rule_radius_lower {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν]
    (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k)
    (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν)
    (R : ℕ) (hR : Q.WithinActualRadius j R) : 2 * k + 1 ≤ R := by
  by_contra hn
  have he : Q.remote j (2 * k + 1) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨n, r, hr, a, ha, hf⟩ := hp
    have hb := hR p.1.1 p.1.2 p.2 n r hr a ha
    unfold Far at hf
    omega
  have hb := (original_rule_sharp_remote_probability β j k hk ν Q hQ hc hlaw).1.1
  rw [he, measureReal_empty] at hb
  have hT : 0 ≤ β.T k := by
    exact add_nonneg (pow_nonneg (sub_nonneg.mpr β.lt_one.le) _) (pow_nonneg β.pos.le _)
  linarith

/-- The minimum ranges over raw lawful full-law representatives on the given seed space. -/
theorem stopping_witness_exact_radius {U : Type u} [MeasurableSpace U]
    (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] :
    IsLeast {R : ℕ | ∃ Q : RawRule U, Q.CompletionLawful ν ∧ Q.TotalCap k ∧
      Q.SameFullLaw (stoppingRule j k) β j ν ∧ Q.WithinActualRadius j R} (2 * k + 1) := by
  constructor
  · have hw := stopping_witness_original_contract β j k hk ν
    exact ⟨stoppingRule j k, hw.1.completionLawful ν, hw.2.1, rfl, hw.2.2.2.2⟩
  · rintro R ⟨Q, hQ, hc, hlaw, hR⟩
    exact original_rule_radius_lower β j k hk ν Q hQ hc hlaw R hR

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end


noncomputable section
open Classical MeasureTheory
open scoped ENNReal
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace CompletedRule
universe u
variable {U : Type u} [MeasurableSpace U]

def completedJoint (Q : CompletedRule U) (j : Bool) (p : SourcePoint × U) : U × Observation :=
  (p.2, (Q.atSource p.1).rawObservation j p.1 p.2)

def fullLaw (Q : CompletedRule U) (β : Bias) (j : Bool) (ν : Measure U) :
    Measure (U × Observation) := ((sourceLaw β).prod ν).map (Q.completedJoint j)

def remote (Q : CompletedRule U) (j : Bool) (R : ℕ) : Set (SourcePoint × U) :=
  {p | p ∈ (Q.atSource p.1).remote j R}

def CompletedWithinActualRadius (Q : CompletedRule U) (j : Bool) (R : ℕ) : Prop :=
  ∀ (s : SourcePoint) (u : U) (n : ℕ) (r : Record),
    (Q.atSource s).readPrefix u (visible s.1 s.2) n = some r →
      ∀ a ∈ r, |a.1 - j.toInt| ≤ (R : ℤ)

theorem completed_joint_normalize (Q : CompletedRule U) (k : ℕ) (hc : Q.TotalCap k)
    (j : Bool) (p : SourcePoint × U) :
    Q.completedJoint j p = (p.2, observation j p.1.1 (Q.normalize k p) p.1.2) := by
  obtain ⟨_, ho, hn⟩ := Q.completed_normalization_execution k hc p
  have hd : decide ((Q.atSource p.1).returnTime p.2 (visible p.1.1 p.1.2) < ⊤) =
      ((Q.normalize k p).run (visible p.1.1 p.1.2)).returned := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, Execution.returned, ho] using
      (Q.atSource p.1).finite_return_iff p.2 (visible p.1.1 p.1.2)
  simp only [completedJoint, RawRule.rawObservation, observation, ho, hn, hd, ENat.toNat_natCast]

private theorem completed_remote_normalize (Q : CompletedRule U) (k : ℕ) (hc : Q.TotalCap k)
    (j : Bool) (R : ℕ) (p : SourcePoint × U) :
    p ∈ Q.remote j R ↔ ∃ a ∈ ((Q.normalize k p).run (visible p.1.1 p.1.2)).record,
      Far j R a.1 := by
  have hv := (Q.completed_normalization_execution k hc p).1
  constructor
  · rintro ⟨n, r, hr, a, ha, hf⟩
    exact ⟨a, (Q.atSource p.1).completes_record_subset _ _ hv hr a ha, hf⟩
  · rintro ⟨a, ha, hf⟩
    exact ⟨_, _, hv.1, a, ha, hf⟩

/-- Ambient null changes are transported through one common event version and Fubini.
The actual cap and pointwise execution theorem remain separate from this a.e. identity. -/
theorem full_law_sections (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν]
    (Q : CompletedRule U) (hQ : Q.Lawful ((sourceLaw β).prod ν))
    (k : ℕ) (hc : Q.TotalCap k) (w : SourcePoint → Observation) (hw : Measurable w)
    (hlaw : Q.fullLaw β j ν =
      ((sourceLaw β).prod ν).map (fun p : SourcePoint × U => (p.2, w p.1))) :
    ∃ T : U → {t : ReadTree // t.height ≤ k}, Measurable T ∧
      (Q.normalize k =ᵐ[(sourceLaw β).prod ν] fun p => (T p.2).val) ∧
      (∀ᵐ u ∂ν, (∀ᵐ s ∂sourceLaw β, Q.normalize k (s,u) = (T u).val) ∧
        ∀ z, fullMass β (lawWindow (T u).val) j (T u).val z =
          (sourceLaw β).real (w ⁻¹' {z})) := by
  obtain ⟨T, hm, he⟩ := Q.normalization_version ((sourceLaw β).prod ν) hQ k
  have hT : Measurable (fun u => (T u).val) := measurable_subtype_coe.comp hm
  have hj : Q.completedJoint j =ᵐ[(sourceLaw β).prod ν] selectorJoint j (fun u => (T u).val) := by
    filter_upwards [he] with p hp
    rw [Q.completed_joint_normalize k hc j p, hp]
    rfl
  have hmap := (Measure.map_congr hj).symm.trans hlaw
  have hs := selector_full_law_sections β j ν (fun u => (T u).val) hT w hw hmap
  have hswap : ∀ᵐ p ∂ν.prod (sourceLaw β), Q.normalize k (p.2,p.1) = (T p.1).val :=
    (Measure.measurePreserving_swap (μ := ν) (ν := sourceLaw β)).quasiMeasurePreserving.ae he
  exact ⟨T, hm, he, (Measure.ae_ae_of_ae_prod hswap).and hs⟩

/-- Stopping rigidity and the sharp read bound include the permitted ambient completion versions. -/
theorem original_rule_stopping_results (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k)
    (ν : Measure U) [IsProbabilityMeasure ν] (Q : CompletedRule U)
    (hQ : Q.Lawful ((sourceLaw β).prod ν)) (hc : Q.TotalCap k)
    (hlaw : Q.fullLaw β j ν = (stoppingRule j k).fullLaw β j ν) :
    (∃ T : U → {t : ReadTree // t.height ≤ k}, Measurable T ∧
      (∀ᵐ u ∂ν, (∀ᵐ s ∂sourceLaw β, Q.normalize k (s,u) = (T u).val) ∧
        ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
          (T u).val = ReadTree.stopComb (es.map (fun e => 2 * e + (!j).toInt)) ∧
          es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k)) ∧
      ((1 + β.T k) / 2 ≤ ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1))) ∧
      (((sourceLaw β).prod ν).real
        ((stoppingRule (U := U) j k).remote j (2 * k + 1)) = (1 + β.T k) / 2) ∧
      (k = 1 → ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) = 1) := by
  have hW := RawRule.fullLaw_realize (fun _ : U => witnessTree j k) k
    (fun _ => stoppingRule_height j k) β j ν
  obtain ⟨T, hm, he, hs⟩ := Q.full_law_sections β j ν hQ k hc
    (fun s => observation j s.1 (witnessTree j k) s.2)
    (measurable_observation j (witnessTree j k)) (hlaw.trans hW)
  have hLaw : ∀ᵐ u ∂ν, HasStoppingLaw β (lawWindow (T u).val) j k (T u).val := by
    filter_upwards [hs] with u hu
    intro z
    exact (hu.2 z).trans ((sourceLaw_observation β j (witnessTree j k) z).trans
      (witness_canonical_law β j k hk z))
  constructor
  · refine ⟨T, hm, ?_⟩
    filter_upwards [hs, hLaw] with u hu hl
    exact ⟨hu.1, finite_full_law_forces_stopping_path β j k hk (T u).val (T u).property hl⟩
  · have hb := selector_remote_lower_bound β j k hk ν (fun u => (T u).val)
      (measurable_subtype_coe.comp hm) (fun u => (T u).property) hLaw
    have hE : Q.remote j (2 * k + 1) =ᵐ[(sourceLaw β).prod ν]
        selectorRemote (fun u => (T u).val) j (2 * k + 1) := by
      filter_upwards [he] with p hp
      apply propext
      rw [Q.completed_remote_normalize k hc, hp]
      rfl
    have hbound : (1 + β.T k) / 2 ≤
        ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) :=
      hb.trans_eq (congrArg ENNReal.toReal (measure_congr hE)).symm
    refine ⟨hbound, stopping_witness_remote_probability β j k hk ν, ?_⟩
    intro hk1
    apply le_antisymm measureReal_le_one
    simpa [hk1, β.T_one] using hbound

/-- The exact law-preserving radius also ranges over ambient completed lawful events. -/
theorem completed_stopping_witness_exact_radius (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k)
    (ν : Measure U) [IsProbabilityMeasure ν] :
    IsLeast {R : ℕ | ∃ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) ∧
      Q.TotalCap k ∧ Q.fullLaw β j ν = (stoppingRule j k).fullLaw β j ν ∧
        Q.CompletedWithinActualRadius j R} (2 * k + 1) := by
  constructor
  · refine ⟨fromRaw (stoppingRule j k),
      fromRaw_completion_lawful _ ν ((stoppingRule_lawful j k).completionLawful ν) _
        Measure.quasiMeasurePreserving_snd, ?_, rfl, ?_⟩
    · intro s u; exact stoppingRule_cap j k s.1 s.2 u
    · intro s u n r hr a ha
      exact stopping_witness_radius j k s.1 s.2 u n r hr a ha
  · rintro R ⟨Q, hQ, hc, hlaw, hR⟩
    by_contra hn
    have he : Q.remote j (2 * k + 1) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨n, r, hr, a, ha, hf⟩ := hp
      have hb := hR p.1 p.2 n r hr a ha
      unfold Far at hf
      omega
    have hb := (Q.original_rule_stopping_results β j k hk ν hQ hc hlaw).2.1
    rw [he, measureReal_empty] at hb
    have hT : 0 ≤ β.T k := add_nonneg
      (pow_nonneg (sub_nonneg.mpr β.lt_one.le) _) (pow_nonneg β.pos.le _)
    linarith

end CompletedRule
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
end
