/- GID: D5/S3/Observer/Budget/ActualDyadicDeadlineLabelSupport
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ActualDyadicDeadlineLabelSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-history causal label supports characterize a shared hidden-schedule raw-bit decoder. -/

import D5.S3.Observer.Budget.ActualDyadicDeadlineSupport
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Observer.Budget.ActualDyadicDeadlineLabelSupport
open D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity
open ActualDyadicDeadlineSupport

/-- Closed circular phase center of a source prefix. -/
def prefixPhase (d : Nat) (t : Fin (2 ^ d)) : AddCircle ((2 ^ (d + 1) : Nat) : ℝ) :=
  (((2 ^ (d + 1) - 1 - 2 * t.val : Nat) : ℝ) : AddCircle ((2 ^ (d + 1) : Nat) : ℝ))

/-- Properness for the actual supported types and overlapping closed phase balls. -/
def ActualTypeColoring {Z : Type*} (d : Nat) (b : Fin 2) (D : Nat) (eps : ℝ)
    (color : Fin (2 ^ d) × Fin 2 → Z) : Prop :=
  ∀ x ∈ actualTypes d b D, ∀ y ∈ actualTypes d b D, x ≠ y →
    (∃ q, dist q (prefixPhase d x.1) ≤ eps ∧ dist q (prefixPhase d y.1) ≤ eps) →
    color x ≠ color y

/-- The writer receives only its policy and acquired pre-final record. One receiver
handles all schedules, sources and closed errors without seeing the policy or clock. -/
def CommonRepairFeasible {Z : Type*} (d : Nat) (b : Fin 2) (D : Nat) (eps : ℝ)
    (writer : (Record → Action (2 ^ (d + 1))) → Record → Z) : Prop :=
  ∃ decoder : AddCircle ((2 ^ (d + 1) : Nat) : ℝ) → Fin 2 → Z → Nat,
    ∀ policy, actualDeadlineFamily d b D policy →
      ∀ r past N bit, DeadlineObservation d b D policy r past N bit →
        ∀ q, dist q (terminalPhase r) ≤ eps →
          decoder q bit (writer policy ⟨N, past⟩) = r.val

/-- Every proper type coloring has a causal writer and one common raw-Y decoder. -/
theorem actual_type_coloring_common_decoder {Z : Type*} (d : Nat) (b : Fin 2)
    (D : Nat) (eps : ℝ) (color : Fin (2 ^ d) × Fin 2 → Z)
    (proper : ActualTypeColoring d b D eps color) :
    ∃ writer : (Record → Action (2 ^ (d + 1))) → Record → Z,
      (∀ policy record, writer policy record = color
        (⟨acquiredPrefix (P := 2 ^ (d + 1)) b record.reads 0 % 2 ^ d,
          Nat.mod_lt _ (Nat.two_pow_pos d)⟩,
         ⟨record.events / 2 ^ (d + 1) % 2, Nat.mod_lt _ (by decide)⟩)) ∧
      CommonRepairFeasible d b D eps writer := by
  classical
  let writer : (Record → Action (2 ^ (d + 1))) → Record → Z := fun _ record => color
    (⟨acquiredPrefix (P := 2 ^ (d + 1)) b record.reads 0 % 2 ^ d,
      Nat.mod_lt _ (Nat.two_pow_pos d)⟩,
     ⟨record.events / 2 ^ (d + 1) % 2, Nat.mod_lt _ (by decide)⟩)
  let compatible (q : AddCircle ((2 ^ (d + 1) : Nat) : ℝ)) (z : Z)
      (x : Fin (2 ^ d) × Fin 2) : Prop :=
    x ∈ actualTypes d b D ∧ color x = z ∧ dist q (prefixPhase d x.1) ≤ eps
  let decoder : AddCircle ((2 ^ (d + 1) : Nat) : ℝ) → Fin 2 → Z → Nat := fun q Y z =>
    if found : ∃ x, compatible q z x then
      let x := Classical.choose found
      2 * x.1.val + (Y.val + b.val + x.2.val) % 2
    else 0
  refine ⟨writer, by intro policy record; rfl, decoder, ?_⟩
  intro policy family r past N bit observation q noise
  obtain ⟨_, acquired, _, _, raw, _⟩ :=
    actual_deadline_observation_normal_form d b D policy family r past N bit observation
  have tn : r.val / 2 < 2 ^ d := by
    have := r.isLt
    have power : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
    omega
  let x : Fin (2 ^ d) × Fin 2 :=
    (⟨r.val / 2, tn⟩, ⟨N / 2 ^ (d + 1) % 2, Nat.mod_lt _ (by decide)⟩)
  have label : writer policy ⟨N, past⟩ = color x := by
    simp only [writer, x, acquired, Nat.mod_eq_of_lt tn]
  have supported : x ∈ actualTypes d b D := by
    simp only [actualTypes, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [actualParitySupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨N, ⟨policy, family, r, past, bit, rfl, observation⟩, rfl⟩
  have phase : prefixPhase d x.1 = terminalPhase r := rfl
  have live : compatible q (color x) x := ⟨supported, rfl, by rw [phase]; exact noise⟩
  have found : ∃ y, compatible q (color x) y := ⟨x, live⟩
  let y := Classical.choose found
  have other : compatible q (color x) y := Classical.choose_spec found
  have same : y = x := by
    by_contra different
    exact (proper y other.1 x supported different ⟨q, other.2.2, live.2.2⟩) other.2.1
  rw [label]
  have decode : decoder q bit (color x) = 2 * x.1.val + (bit.val + b.val + x.2.val) % 2 := by
    simp only [decoder, dif_pos found]
    change 2 * y.1.val + (bit.val + b.val + y.2.val) % 2 = _
    rw [same]
  rw [decode]
  dsimp [x]
  have lastBit : r.val % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

/-- All labels of one type, ranging over every realizing policy and actual history. -/
def actualLabelSupport {Z : Type*} (d : Nat) (b : Fin 2) (D : Nat)
    (writer : (Record → Action (2 ^ (d + 1))) → Record → Z)
    (x : Fin (2 ^ d) × Fin 2) : Set Z :=
  {z | ∃ policy, actualDeadlineFamily d b D policy ∧ ∃ r past N bit,
    DeadlineObservation d b D policy r past N bit ∧ r.val / 2 = x.1.val ∧
    N / 2 ^ (d + 1) % 2 = x.2.val ∧ writer policy ⟨N, past⟩ = z}

private theorem actual_label_support_nonempty {Z : Type*} (d : Nat) (b : Fin 2) (D : Nat)
    (writer : (Record → Action (2 ^ (d + 1))) → Record → Z)
    (x : Fin (2 ^ d) × Fin 2) (hx : x ∈ actualTypes d b D) :
    (actualLabelSupport d b D writer x).Nonempty := by
  classical
  simp only [actualTypes, actualParitySupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨N, support, parity⟩ := hx
  obtain ⟨policy, family, r, past, bit, quotient, observation⟩ := support
  exact ⟨writer policy ⟨N,past⟩, policy, family, r, past, N, bit,
    observation, quotient, parity, rfl⟩

private theorem actual_label_support_zero_read {Z : Type*} (d : Nat) (b : Fin 2) (D : Nat)
    (writer : (Record → Action (2 ^ (d + 1))) → Record → Z)
    (x : Fin (2 ^ d) × Fin 2) (z : Z)
    (member : z ∈ actualLabelSupport d b D writer x) :
    ∃ policy, actualDeadlineFamily d b D policy ∧ ∃ r past N,
      DeadlineObservation d b D policy r past N 0 ∧
      r.val / 2 = x.1.val ∧ r.val % 2 = (b.val + x.2.val) % 2 ∧
      writer policy ⟨N,past⟩ = z := by
  obtain ⟨policy, family, r0, past, N, bit, observation, quotient, parity, label⟩ := member
  obtain ⟨word0, terminal0, run0, bound0, _, shape0, deadline⟩ := observation
  have success : ∀ r, ∃ word terminal,
      Execution (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ word terminal ∧
      word.length ≤ d + 1 ∧ terminal.2 = r := by
    intro r
    obtain ⟨past, N, bit, word, terminal, run, bound, answer, _, _⟩ := family r
    exact ⟨word, terminal, run, bound, answer⟩
  let u := (b.val + x.2.val) % 2
  let r : Fin (2 ^ (d + 1)) := ⟨2 * x.1.val + u, by
    have small := x.1.isLt
    have bitBound : u < 2 := Nat.mod_lt _ (by decide)
    rw [pow_succ]; omega⟩
  have pair : r0.val / 2 = r.val / 2 := by
    have bitBound : u < 2 := Nat.mod_lt _ (by decide)
    dsimp [r]; omega
  obtain ⟨word, terminal, run, bound, answer⟩ := success r
  obtain ⟨past', N', v, v', _, _, _, _, shape0', shape', _, _, _, _, raw, _, _, _⟩ :=
    actual_acquired_prefix_and_final_query (Nat.two_pow_pos (d + 1)) d rfl b policy
      success r0 r pair word0 word terminal0 terminal run0 run bound0 bound
  have last : (N',v) = (N,bit) := by
    simpa using congrArg List.getLast? (shape0'.symm.trans shape0)
  have clock : N' = N := congrArg Prod.fst last
  have value : v = bit := congrArg Prod.snd last
  simp only [clock, value] at shape0' shape' raw
  have histEq : past' = past := List.append_cancel_right (shape0'.symm.trans shape0)
  rw [histEq] at shape'
  have sourceQuotient : r.val / 2 = x.1.val := by dsimp [r, u]; omega
  have sourceBit : r.val % 2 = (b.val + x.2.val) % 2 := by dsimp [r, u]; omega
  have zero : v'.val = 0 := by
    rw [sourceBit] at raw
    have pBound := x.2.isLt
    omega
  have bitZero : v' = 0 := Fin.ext zero
  rw [bitZero] at shape'
  exact ⟨policy, family, r, past, N, ⟨word, terminal, run, bound, answer, shape', deadline⟩,
    sourceQuotient, sourceBit, label⟩

/-- Adjacent supported types have disjoint all-history label supports whenever
one receiver recovers every policy and every closed error. -/
theorem actual_common_decoder_support_separation {Z : Type*} (d : Nat) (b : Fin 2)
    (D : Nat) (eps : ℝ)
    (writer : (Record → Action (2 ^ (d + 1))) → Record → Z)
    (feasible : CommonRepairFeasible d b D eps writer) :
    (∀ x ∈ actualTypes d b D, (actualLabelSupport d b D writer x).Nonempty) ∧
    ∀ x ∈ actualTypes d b D, ∀ y ∈ actualTypes d b D, x ≠ y →
      (∃ q, dist q (prefixPhase d x.1) ≤ eps ∧ dist q (prefixPhase d y.1) ≤ eps) →
      Disjoint (actualLabelSupport d b D writer x) (actualLabelSupport d b D writer y) := by
  refine ⟨actual_label_support_nonempty d b D writer, ?_⟩
  obtain ⟨decoder, recover⟩ := feasible
  intro x hx y hy different overlap
  apply Set.disjoint_left.mpr
  intro z zx zy
  obtain ⟨policy, family, r, past, N, observation, quotient, sourceBit, label⟩ :=
    actual_label_support_zero_read d b D writer x z zx
  obtain ⟨policy', family', s, past', N', observation', quotient', sourceBit', label'⟩ :=
    actual_label_support_zero_read d b D writer y z zy
  obtain ⟨q, noise, noise'⟩ := overlap
  have phase : terminalPhase r = prefixPhase d x.1 := by
    unfold terminalPhase prefixPhase; rw [quotient]
  have phase' : terminalPhase s = prefixPhase d y.1 := by
    unfold terminalPhase prefixPhase; rw [quotient']
  have answer := recover policy family r past N 0 observation q (by rw [phase]; exact noise)
  have answer' := recover policy' family' s past' N' 0 observation' q (by rw [phase']; exact noise')
  rw [label] at answer
  rw [label'] at answer'
  have sameSource : r.val = s.val := answer.symm.trans answer'
  have prefixes : x.1 = y.1 := by apply Fin.ext; omega
  have parities : x.2 = y.2 := by
    apply Fin.ext
    have := x.2.isLt
    have := y.2.isLt
    omega
  exact different (Prod.ext prefixes parities)

/-- Allowing labels to depend on all old causal state cannot improve on a proper
coloring of the actual supported type graph. The receiver is shared by all policies. -/
theorem actual_all_history_coloring_iff {Z : Type*} (d : Nat) (b : Fin 2)
    (D : Nat) (eps : ℝ) :
    (∃ writer : (Record → Action (2 ^ (d + 1))) → Record → Z,
      CommonRepairFeasible d b D eps writer) ↔
    ∃ color : Fin (2 ^ d) × Fin 2 → Z, ActualTypeColoring d b D eps color := by
  classical
  constructor
  · rintro ⟨writer, feasible⟩
    obtain ⟨nonempty, separated⟩ := actual_common_decoder_support_separation d b D eps writer feasible
    let default : Z := writer (fun _ => .read) ⟨0, []⟩
    let color : Fin (2 ^ d) × Fin 2 → Z := fun x =>
      if hx : x ∈ actualTypes d b D then Classical.choose (nonempty x hx) else default
    refine ⟨color, ?_⟩
    intro x hx y hy different overlap
    simp only [color, dif_pos hx, dif_pos hy]
    intro equal
    have first := Classical.choose_spec (nonempty x hx)
    have second := Classical.choose_spec (nonempty y hy)
    rw [← equal] at second
    exact Set.disjoint_left.mp (separated x hx y hy different overlap) first second
  · rintro ⟨color, proper⟩
    obtain ⟨writer, _, feasible⟩ := actual_type_coloring_common_decoder d b D eps color proper
    exact ⟨writer, feasible⟩

end D5.S3.Observer.Budget.ActualDyadicDeadlineLabelSupport
