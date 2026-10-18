/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/RemoteReadSection
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/RemoteReadSection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first remote stopping-comb read has exact mass one half plus its zero-prefix mass. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

def Far (j : Bool) (R : ℕ) (t : ℤ) : Prop := (R : ℤ) ≤ |t - j.toInt|

def remoteEvent (T : ReadTree) (j : Bool) (R : ℕ) (φ : Bool) : Set Spins :=
  {S | ∃ a ∈ (T.run (visible φ S)).record, Far j R a.1}

def remoteMass (β : Bias) (V : Finset ℤ) (j : Bool) (R : ℕ) (T : ReadTree) : ℝ :=
  (∑ φ : Bool, SpinWindow.prob β V (remoteEvent T j R φ)) / 2

/-- A first occurrence exists for any decidable predicate on a finite list. -/
theorem first_far_split (j : Bool) (R : ℕ) (ts : List ℤ)
    (h : ∃ t ∈ ts, Far j R t) :
    ∃ pre : List ℤ, ∃ t : ℤ, ∃ post : List ℤ,
      ts = pre ++ t :: post ∧ (∀ a ∈ pre, ¬Far j R a) ∧ Far j R t := by
  induction ts with
  | nil => simpa using h
  | cons a ts ih =>
    by_cases ha : Far j R a
    · exact ⟨[], a, ts, rfl, by simp, ha⟩
    · have ht : ∃ t ∈ ts, Far j R t := by
        obtain ⟨t, ht, hf⟩ := h
        rcases List.mem_cons.mp ht with rfl | ht
        · exact (ha hf).elim
        · exact ⟨t, ht, hf⟩
      obtain ⟨pre, t, post, he, hn, hf⟩ := ih ht
      refine ⟨a :: pre, t, post, by simp [he], ?_, hf⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hn b hb

namespace ReadTree

theorem remote_iff_first_prefix (j : Bool) (R : ℕ) (pre : List ℤ) (t : ℤ) (post : List ℤ)
    (hn : ∀ a ∈ pre, ¬Far j R a) (hf : Far j R t) (x : ℤ → Bool) :
    (∃ a ∈ ((stopComb (pre ++ t :: post)).run x).record, Far j R a.1) ↔
      ZeroReplies pre pre.length x := by
  induction pre with
  | nil =>
    constructor
    · intro _; simp [ZeroReplies]
    · intro _
      refine ⟨(t, x t), ?_, hf⟩
      simp only [List.nil_append, stopComb, run, Execution.prepend]
      exact List.mem_cons_self
  | cons a pre ih =>
    have hna : ¬Far j R a := hn a (by simp)
    have hnp : ∀ b ∈ pre, ¬Far j R b := fun b hb => hn b (by simp [hb])
    cases hx : x a with
    | true => simp [stopComb, run, hx, Execution.prepend, hna, ZeroReplies]
    | false =>
      simpa [stopComb, run, hx, Execution.prepend, hna, ZeroReplies] using ih hnp

theorem edgeComb_opposite_remote (es : List ℤ) (j : Bool) (R : ℕ)
    (hf : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j R t) :
    remoteEvent (edgeComb es (!j)) j R j = Set.univ := by
  ext S
  constructor
  · intro _; trivial
  · intro _
    have hz : ∀ t ∈ es.map (fun e => 2 * e + (!j).toInt), visible j S t = false := by
      intro t ht
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
      have ha : (2 * e + (!j).toInt - (!j).toInt) % 2 = 0 := by omega
      simpa only [Bool.not_not] using opposite_phase_visible (!j) S _ ha
    obtain ⟨t, ht, hfar⟩ := hf
    have hr := stopComb_all_zero (es.map (fun e => 2 * e + (!j).toInt)) (visible j S) hz
    change ∃ a ∈ ((stopComb _).run (visible j S)).record, Far j R a.1
    rw [hr]
    exact ⟨(t, false), List.mem_map.mpr ⟨t, ht, rfl⟩, hfar⟩

end ReadTree

/-- Exact source mass of the first remote call, with the paid-depth boundary m=1 included. -/
theorem comb_first_remote_section (β : Bias) (V : Finset ℤ) (j : Bool) (R : ℕ)
    (es : List ℤ) (hq : j.toInt ∈ V)
    (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j)))
    (hfar : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j R t) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ es.length ∧
      remoteMass β V j R (ReadTree.edgeComb es (!j)) = (1 + β.T m) / 2 := by
  obtain ⟨pre, t, post, hts, hpre, ht⟩ := first_far_split j R _ hfar
  have hm : pre.length + 1 ≤ es.length := by
    have hlen := congrArg List.length hts
    simp only [List.length_map, List.length_append, List.length_cons] at hlen
    omega
  have he : remoteEvent (ReadTree.edgeComb es (!j)) j R (!j) =
      SpinWindow.zeroEdges (es.take pre.length).toFinset := by
    ext S
    change (∃ a ∈ ((ReadTree.stopComb _).run (visible (!j) S)).record, Far j R a.1) ↔ _
    rw [hts, ReadTree.remote_iff_first_prefix j R pre t post hpre ht]
    change ReadTree.ZeroReplies pre pre.length (visible (!j) S) ↔
      ∀ e ∈ (es.take pre.length).toFinset, S e = S (e + 1)
    rw [← ReadTree.edge_zero_prefix es (!j) S pre.length]
    simp only [ReadTree.ZeroReplies, hts, List.take_left, List.take_length]
  have hA : SpinWindow.prob β V (remoteEvent (ReadTree.edgeComb es (!j)) j R j) = 1 := by
    rw [ReadTree.edgeComb_opposite_remote es j R hfar, SpinWindow.prob_univ]
  have hB : SpinWindow.prob β V (remoteEvent (ReadTree.edgeComb es (!j)) j R (!j)) =
      β.T (pre.length + 1) := by
    rw [he]
    exact SpinWindow.zero_prefix_mass β V j es hq hlaw pre.length (by omega)
  refine ⟨pre.length + 1, by omega, hm, ?_⟩
  unfold remoteMass
  cases j <;> simp only [Fintype.sum_bool, Bool.not_false, Bool.not_true] at hA hB ⊢ <;>
    rw [hA, hB] <;> ring

/-- Every competing tree executes a threshold-remote call with the stated sharp lower bound. -/
theorem finite_remote_read_section (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k)
    (T : ReadTree) (hh : T.height ≤ k) (hlaw : HasStoppingLaw β (lawWindow T) j k T) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧
      remoteMass β (lawWindow T) j (2 * k + 1) T = (1 + β.T m) / 2 ∧
      (1 + β.T k) / 2 ≤ remoteMass β (lawWindow T) j (2 * k + 1) T := by
  obtain ⟨es, hlen, _, L, heq, hpath, hsep⟩ :=
    finite_full_law_forces_stopping_path β j k hk T hh hlaw
  have hfar : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j (2 * k + 1) t := by
    obtain ⟨e, he, hf⟩ := detached_path_remote j hk L hsep
    have he' : e ∈ es := List.mem_toFinset.mp (hpath ▸ he)
    refine ⟨2 * e + (!j).toInt, List.mem_map.mpr ⟨e, he', rfl⟩, ?_⟩
    simpa [Far] using hf
  have hcomb : T = ReadTree.edgeComb es (!j) := heq
  have hq : j.toInt ∈ lawWindow T := by cases j <;> simp [lawWindow]
  have hLaw' : HasStoppingLaw β (lawWindow T) j es.length (ReadTree.edgeComb es (!j)) := by
    simpa only [hlen, ← hcomb] using hlaw
  obtain ⟨m, hm0, hmk, hm⟩ := comb_first_remote_section β (lawWindow T) j (2 * k + 1)
    es hq hLaw' hfar
  have hmk' : m ≤ k := by omega
  rw [← hcomb] at hm
  refine ⟨m, hm0, hmk', hm, ?_⟩
  rw [hm]
  have hT := β.T_antitone hmk'
  linarith

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
