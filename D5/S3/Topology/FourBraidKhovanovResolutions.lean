/- GID: D5/S3/Topology/FourBraidKhovanovResolutions
   generality: I
   mirror-B: D5/B/S3/Topology/FourBraidKhovanovResolutions
   mirror-E: none(waiver:algebraically-proved)
   anchors: [lake/module/Mathlib.Logic.Relation]
   utility: none
   digest: Kernel evaluation of the resolution partitions and quantum gradings. -/

import D5.S3.Topology.FourBraidKhovanovResolutionData

/-!
Partitions are evaluated in blocks to share the geometric work between rows.
Geometry below quantum degree seventeen is needed only for the grading bound.
-/

set_option autoImplicit false

namespace D5.S3.Topology.FourBraidKhovanovCube

private def replayEntry (s : Nat) : ResolutionEntry :=
  (snapshots[s / 32]!)[s % 32]!

private theorem replayEntry_eq (s : Nat) (hs : s < 2 ^ crossings) :
    replayEntry s = resolutionEntry s := by
  have hb : s / 32 < 64 := by norm_num [crossings, braid] at hs; omega
  unfold replayEntry
  rw [snapshot_correct _ hb]
  have h : s % 32 < (calculateBlock (s / 32)).size := by
    simp [calculateBlock]
    omega
  rw [getElem!_pos (calculateBlock (s / 32)) (s % 32) h]
  simp only [calculateBlock, List.getElem_toArray, List.getElem_map, List.getElem_range',
    Nat.mul_one, Nat.one_mul]
  exact congrArg resolutionEntry (by omega)

/-- Cache for evaluating the saddle maps. On every input it agrees with the
geometrically defined resolution; only upper-row values are stored. -/
def replayResolution (s : Nat) : Partition :=
  if s < 2 ^ crossings then
    let entry := replayEntry s
    if entry.1 ≥ 17 then entry.2 else resolve s
  else resolve s

theorem replayResolution_eq : replayResolution = resolve := by
  funext s
  by_cases hs : s < 2 ^ crossings
  · simp only [replayResolution, ite_eq_left hs, replayEntry_eq s hs, resolutionEntry]
    split <;> simp_all
  · simp [replayResolution, hs]

/-- Compute the extreme bases using the checked grading cutoff. -/
def replayBasis (j k : Nat) : List Enhanced :=
  (List.range (2 ^ crossings)).flatMap fun s =>
    if j ≤ (replayEntry s).1 && weight s == k then
      labels j s (replayEntry s).2
    else []

theorem replayBasis_eq (j k : Nat) (hj : 17 ≤ j) :
    replayBasis j k = basis resolve j k := by
  apply List.flatMap_congr
  intro s hs
  have hs' := List.mem_range.mp hs
  rw [replayEntry_eq s hs']
  by_cases hq : j ≤ upperQuantum s (resolve s)
  · have h17 := hj.trans hq
    simp [resolutionEntry, hq, h17]
  · have hl : labels j s (resolve s) = [] := by
      unfold labels
      change (if j ≤ upperQuantum s (resolve s) && _ then _ else _) = []
      simp [hq]
    simp [resolutionEntry, hq, hl]

private def gradingOK (entry : ResolutionEntry) : Bool :=
  entry.1 ≤ 21 && entry.1 % 2 == 1

private theorem checkedGradings :
    snapshots.toList.all (fun block => block.toList.all gradingOK) = true := rfl

/-- In every geometric resolution the greatest label grading is odd and
at most twenty-one. -/
theorem upperQuantum_bound (s : Nat) (hs : s < 2 ^ crossings) :
    upperQuantum s (resolve s) ≤ 21 ∧ upperQuantum s (resolve s) % 2 = 1 := by
  have hb : s / 32 < snapshots.size := by
    change s / 32 < 64
    norm_num [crossings, braid] at hs
    omega
  have hq : s % 32 < snapshots[s / 32].size := by
    have h := snapshot_correct (s / 32) (show s / 32 < 64 from hb)
    rw [getElem!_pos snapshots (s / 32) hb] at h
    rw [h]
    simp [calculateBlock]
    omega
  have hc := List.all_eq_true.mp checkedGradings _ (Array.getElem_mem_toList hb)
  have he := List.all_eq_true.mp hc _ (Array.getElem_mem_toList hq)
  have eq := replayEntry_eq s hs
  unfold replayEntry at eq
  rw [getElem!_pos snapshots (s / 32) hb,
    getElem!_pos (snapshots[s / 32]'hb) (s % 32) hq] at eq
  rw [eq] at he
  simpa [gradingOK, resolutionEntry] using he

/-- The actual signed cube has no terms above quantum degree twenty-one
and no terms of even quantum degree. -/
theorem basis_empty_of_above_or_even (j k : Nat) (h : 21 < j ∨ j % 2 = 0) :
    basis resolve j k = [] := by
  unfold basis
  apply List.flatMap_eq_nil_iff.mpr
  intro s hs
  have hq := upperQuantum_bound s (List.mem_range.mp hs)
  by_cases hw : weight s = k
  · simp only [hw, beq_self_eq_true, ↓reduceIte]
    unfold labels
    change (if j ≤ upperQuantum s (resolve s) &&
      (upperQuantum s (resolve s) - j) % 2 == 0 then _ else _) = []
    split
    · rename_i yes
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at yes
      rcases h with h | h <;> omega
    · rfl
  · simp [hw]

end D5.S3.Topology.FourBraidKhovanovCube
