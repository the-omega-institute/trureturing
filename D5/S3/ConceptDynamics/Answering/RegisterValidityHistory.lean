/- GID: D5/S3/ConceptDynamics/Answering/RegisterValidityHistory
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Answering/RegisterValidityHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Append-only validity deltas keep exactly one active settlement per assertion key. -/

import Mathlib.Data.List.Basic

/- Library-search audit trail (2026-09-02):
   * `rg -l 'validity|Validity|void' D5 --include='*.lean'` hit the transport
     and semantic-transport certificate-validity modules, which pull validity
     back along admission maps; none models a last-assignment status history.
   * `History/AppendOnlyAnswerabilityMonotonicity` shows append-only logs
     preserve answerable targets; it does not track active-versus-void
     record status or a per-key uniqueness invariant.
   * Pinned Lean core supplies `List.foldl_append`, `List.prefix_append`,
     `List.mem_map`, and `List.mem_singleton`; the last-assignment fold and
     its revision invariants are composed here from those. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Answering.RegisterValidityHistory

/-- Validity status of one settlement record. -/
inductive Status
  | active
  | void
  deriving DecidableEq, Repr

/-- One append-only validity assignment: record `id` is assigned `status`. -/
structure Assignment (Rec : Type*) where
  id : Rec
  status : Status

/-- A later assignment to `r` overrides the accumulated status of `r`. -/
def assignStep {Rec : Type*} [DecidableEq Rec] (r : Rec) (acc : Option Status)
    (a : Assignment Rec) : Option Status :=
  if a.id = r then some a.status else acc

/-- The effective status of a record is its latest assignment in the history. -/
def effectiveStatus {Rec : Type*} [DecidableEq Rec] (history : List (Assignment Rec))
    (r : Rec) : Option Status :=
  history.foldl (assignStep r) none

/-- A record is active for `key` when it carries that key and its effective
status is `active`. -/
def IsActive {Rec Key : Type*} [DecidableEq Rec] (keyOf : Rec → Key)
    (history : List (Assignment Rec)) (key : Key) (r : Rec) : Prop :=
  keyOf r = key ∧ effectiveStatus history r = some .active

/-- The validity delta that voids every listed record. -/
def voidAll {Rec : Type*} (superseded : List Rec) : List (Assignment Rec) :=
  superseded.map fun r => ⟨r, .void⟩

/-- Revision appends a validity delta voiding the superseded records and then
appends the replacement settlement as `active`; nothing is overwritten. -/
def revise {Rec : Type*} (history : List (Assignment Rec)) (superseded : List Rec)
    (replacement : Rec) : List (Assignment Rec) :=
  history ++ voidAll superseded ++ [⟨replacement, .active⟩]

/-- Assignments to other records do not change the accumulated status of `r`. -/
theorem foldl_assignStep_of_not_mem {Rec : Type*} [DecidableEq Rec] (r : Rec) (acc : Option Status)
    (t : List (Assignment Rec)) (h : ∀ a ∈ t, a.id ≠ r) :
    t.foldl (assignStep r) acc = acc := by
  induction t generalizing acc with
  | nil => rfl
  | cons a t ih =>
    have ha : a.id ≠ r := h a (List.mem_cons.mpr (Or.inl rfl))
    rw [List.foldl_cons, assignStep, if_neg ha]
    exact ih acc fun b hb => h b (List.mem_cons.mpr (Or.inr hb))

/-- Every assignment produced by `voidAll` names a superseded record. -/
theorem voidAll_id_not_mem {Rec : Type*} (r : Rec) (t : List Rec) (hr : r ∉ t) :
    ∀ a ∈ voidAll t, a.id ≠ r := by
  intro a ha
  simp only [voidAll, List.mem_map] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  intro hxr
  have hxr' : x = r := hxr
  exact hr (hxr' ▸ hx)

/-- Voiding a list that contains `r` leaves `r` void, whatever came before. -/
theorem foldl_assignStep_of_mem {Rec : Type*} [DecidableEq Rec] (r : Rec) (acc : Option Status)
    (superseded : List Rec) (h : r ∈ superseded) :
    (voidAll superseded).foldl (assignStep r) acc = some .void := by
  induction superseded generalizing acc with
  | nil => simp at h
  | cons a t ih =>
    by_cases hr : r ∈ t
    · rw [voidAll, List.map_cons, List.foldl_cons]
      exact ih _ hr
    · have hra : r = a := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact h1
        · exact absurd h1 hr
      subst hra
      rw [voidAll, List.map_cons, List.foldl_cons, assignStep, if_pos rfl]
      exact foldl_assignStep_of_not_mem r _ _ (voidAll_id_not_mem r t hr)

/-- Appending assignments to other records preserves the effective status of `r`. -/
theorem effectiveStatus_append_of_not_mem {Rec : Type*} [DecidableEq Rec]
    (history t : List (Assignment Rec)) (r : Rec)
    (h : ∀ a ∈ t, a.id ≠ r) :
    effectiveStatus (history ++ t) r = effectiveStatus history r := by
  unfold effectiveStatus
  rw [List.foldl_append]
  exact foldl_assignStep_of_not_mem r _ t h

/-- The latest appended assignment to `r` is its effective status. -/
theorem effectiveStatus_append_singleton {Rec : Type*} [DecidableEq Rec]
    (history : List (Assignment Rec)) (r : Rec)
    (s : Status) : effectiveStatus (history ++ [⟨r, s⟩]) r = some s := by
  unfold effectiveStatus
  rw [List.foldl_append]
  simp [assignStep]

/-- After a voiding delta that names `r`, the effective status of `r` is `void`. -/
theorem effectiveStatus_append_voidAll_of_mem {Rec : Type*} [DecidableEq Rec]
    (history : List (Assignment Rec))
    (superseded : List Rec) (r : Rec) (h : r ∈ superseded) :
    effectiveStatus (history ++ voidAll superseded) r = some .void := by
  unfold effectiveStatus
  rw [List.foldl_append]
  exact foldl_assignStep_of_mem r _ superseded h

/-- Revision never overwrites: the prior history is a prefix of the revised history. -/
theorem revise_preserves_history_prefix {Rec : Type*} (history : List (Assignment Rec))
    (superseded : List Rec) (replacement : Rec) :
    history <+: revise history superseded replacement :=
  ⟨voidAll superseded ++ [⟨replacement, .active⟩], by simp [revise]⟩

/-- Records outside the revised key keep their effective status. -/
theorem effectiveStatus_revise_of_key_ne {Rec Key : Type*} [DecidableEq Rec]
    (keyOf : Rec → Key) (history : List (Assignment Rec))
    (key : Key) (superseded : List Rec) (replacement : Rec)
    (hsup : ∀ x ∈ superseded, keyOf x = key) (hkey : keyOf replacement = key)
    (r : Rec) (hr : keyOf r ≠ key) :
    effectiveStatus (revise history superseded replacement) r = effectiveStatus history r := by
  unfold revise
  rw [effectiveStatus_append_of_not_mem, effectiveStatus_append_of_not_mem]
  · exact voidAll_id_not_mem r superseded fun hm => hr (hsup r hm)
  · intro a ha
    rw [List.mem_singleton] at ha
    subst ha
    intro h
    have h' : replacement = r := h
    subst h'
    exact hr hkey

/-- After revision, exactly one record is active for the revised key: the
replacement, provided the delta voided every previously active record of that
key and the replacement is a fresh record carrying that key. -/
theorem revise_leaves_exactly_one_active {Rec Key : Type*} [DecidableEq Rec]
    (keyOf : Rec → Key)
    (history : List (Assignment Rec)) (key : Key) (superseded : List Rec)
    (replacement : Rec)
    (hcover : ∀ r, IsActive keyOf history key r → r ∈ superseded)
    (hfresh : replacement ∉ superseded) (hkey : keyOf replacement = key) (r : Rec) :
    IsActive keyOf (revise history superseded replacement) key r ↔ r = replacement := by
  constructor
  · intro hr
    by_contra hne
    obtain ⟨hk, hs⟩ := hr
    have hlast : effectiveStatus (revise history superseded replacement) r
        = effectiveStatus (history ++ voidAll superseded) r := by
      unfold revise
      apply effectiveStatus_append_of_not_mem
      intro a ha
      rw [List.mem_singleton] at ha
      subst ha
      intro h
      have h' : replacement = r := h
      exact hne h'.symm
    by_cases hmem : r ∈ superseded
    · rw [hlast, effectiveStatus_append_voidAll_of_mem history superseded r hmem] at hs
      simp at hs
    · rw [hlast,
        effectiveStatus_append_of_not_mem history _ r (voidAll_id_not_mem r superseded hmem)]
        at hs
      exact hmem (hcover r ⟨hk, hs⟩)
  · rintro rfl
    refine ⟨hkey, ?_⟩
    unfold revise
    exact effectiveStatus_append_singleton _ _ _

/-- Revision of one key leaves the active records of every other key unchanged. -/
theorem revise_preserves_other_keys {Rec Key : Type*} [DecidableEq Rec]
    (keyOf : Rec → Key) (history : List (Assignment Rec))
    (key key' : Key) (superseded : List Rec) (replacement : Rec)
    (hsup : ∀ x ∈ superseded, keyOf x = key) (hkey : keyOf replacement = key)
    (hne : key' ≠ key) (r : Rec) :
    IsActive keyOf (revise history superseded replacement) key' r ↔
      IsActive keyOf history key' r := by
  unfold IsActive
  have hstat : effectiveStatus (revise history superseded replacement) r
      = effectiveStatus history r ∨ keyOf r ≠ key' := by
    by_cases hk : keyOf r = key'
    · exact Or.inl (effectiveStatus_revise_of_key_ne keyOf history key superseded replacement
        hsup hkey r (by rw [hk]; exact hne))
    · exact Or.inr hk
  rcases hstat with hstat | hstat
  · rw [hstat]
  · constructor <;> rintro ⟨hk, _⟩ <;> exact absurd hk hstat

/-- Records are keyed by their tens digit; two records of key 1, one of key 2. -/
def sampleHistory : List (Assignment Nat) :=
  [⟨11, .active⟩, ⟨12, .active⟩, ⟨12, .void⟩, ⟨21, .active⟩]

/- Revising key 1 voids the old active record and activates the replacement. -/
example : effectiveStatus (revise sampleHistory [11] 13) 11 = some .void ∧
    effectiveStatus (revise sampleHistory [11] 13) 13 = some .active := by
  decide

/- The already-void record stays void and the other key's record stays active. -/
example : effectiveStatus (revise sampleHistory [11] 13) 12 = some .void ∧
    effectiveStatus (revise sampleHistory [11] 13) 21 = some .active := by
  decide

#print axioms revise_preserves_history_prefix
#print axioms revise_leaves_exactly_one_active
#print axioms revise_preserves_other_keys

end D5.S3.ConceptDynamics.Answering.RegisterValidityHistory
