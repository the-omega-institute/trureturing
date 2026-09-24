/- GID: D5/S3/Combinatorics/CircularTwoChoiceParkingOperational
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CircularTwoChoiceParkingOperational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Operational fixed-increment two-choice circular parking. -/

import D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata

/-!
# Circular two-choice parking

The definitions below implement the ordered two-choice process on `n + 1`
circular spots.  A single bounded scanner is shared by the actual process and
its one-choice comparison process.  The final equivalences retain the complete
increment vector and the observed empty spot.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularTwoChoiceParkingBijection

open D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata

/-- Circular spots for `n` cars. -/
abbrev Spot (n : Nat) := ZMod (n + 1)

/-- A positive clockwise increment, necessarily at most `n`. -/
def Increment (n : Nat) := {k : Nat // 1 <= k /\ k <= n}

/-- The literal ordered pair tried by a car. -/
structure ActualChoice (n : Nat) where
  anchor : Spot n
  second : Spot n
  distinct : second ≠ anchor

/-- One actual ordered choice for every car. -/
abbrev ActualPreferences (n : Nat) := Fin n -> ActualChoice n

/-- One anchor for every car. -/
abbrev Anchors (n : Nat) := Fin n -> Spot n

/-- The observable clockwise increment of every actual choice. -/
abbrev IncrementMatrix (n : Nat) := Fin n -> Increment n

private def orbitEquiv (n : Nat) (start : Spot n) : Fin (n + 1) ≃ Spot n :=
  (ZMod.finEquiv (n + 1)).toEquiv.trans (Equiv.addRight start)

private def freeOffsets (n : Nat) (occupied : Finset (Spot n)) (start : Spot n) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter fun r => orbitEquiv n start r ∉ occupied

private def firstFreeOffset (n : Nat) (occupied : Finset (Spot n)) (start : Spot n) :
    Fin (n + 1) :=
  if h : (freeOffsets n occupied start).Nonempty then
    (freeOffsets n occupied start).min' h
  else 0

/-- The sole circular search primitive: inspect offsets `0, ..., n` in order. -/
private def firstFree (n : Nat) (occupied : List (Spot n)) (start : Spot n) : Spot n :=
  orbitEquiv n start (firstFreeOffset n occupied.toFinset start)

private theorem freeOffsets_nonempty (n : Nat) (occupied : Finset (Spot n))
    (start : Spot n) (hcard : occupied.card <= n) :
    (freeOffsets n occupied start).Nonempty := by
  by_contra hnone
  have hall : ∀ x : Spot n, x ∈ occupied := by
    intro x
    by_contra hx
    let r := (orbitEquiv n start).symm x
    apply hnone
    refine ⟨r, ?_⟩
    simp only [freeOffsets, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [r] using hx
  have huniv : occupied = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  have hlarge : n + 1 <= n := by
    simpa [huniv] using hcard
  omega

private theorem firstFree_fresh (n : Nat) (occupied : List (Spot n)) (start : Spot n)
    (hnodup : occupied.Nodup) (hcard : occupied.length <= n) :
    firstFree n occupied start ∉ occupied := by
  have hc : occupied.toFinset.card <= n := by
    simpa [occupied.toFinset_card_of_nodup hnodup] using hcard
  have hne := freeOffsets_nonempty n occupied.toFinset start hc
  have hm := Finset.min'_mem (freeOffsets n occupied.toFinset start) hne
  simp only [freeOffsets, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  change orbitEquiv n start (firstFreeOffset n occupied.toFinset start) ∉ occupied
  rw [firstFreeOffset, dif_pos hne]
  exact fun hmem => hm (List.mem_toFinset.mpr hmem)

private theorem firstFree_skipped (n : Nat) (occupied : List (Spot n)) (start : Spot n)
    (hnodup : occupied.Nodup) (hcard : occupied.length <= n)
    (r : Fin (n + 1)) (hr : r < firstFreeOffset n occupied.toFinset start) :
    orbitEquiv n start r ∈ occupied := by
  have hc : occupied.toFinset.card <= n := by
    simpa [occupied.toFinset_card_of_nodup hnodup] using hcard
  have hne := freeOffsets_nonempty n occupied.toFinset start hc
  by_contra hfree
  have hrmem : r ∈ freeOffsets n occupied.toFinset start := by
    simp [freeOffsets, hfree]
  have hle := Finset.min'_le (freeOffsets n occupied.toFinset start) r hrmem
  simp only [firstFreeOffset, dif_pos hne] at hr
  exact (not_le_of_gt hr) hle

/-- The actual ordered rule: take the anchor when free, otherwise scan from the second choice. -/
def actualStep (n : Nat) (occupied : List (Spot n)) (q : ActualChoice n) : Spot n :=
  if q.anchor ∈ occupied then firstFree n occupied q.second else q.anchor

/-- The comparison rule scans clockwise from its single anchor. -/
def oneStep (n : Nat) (occupied : List (Spot n)) (anchor : Spot n) : Spot n :=
  firstFree n occupied anchor

def parkFrom {n : Nat} {α : Type} (step : List (Spot n) -> α -> Spot n)
    (occupied : List (Spot n)) : List α -> List (Spot n)
  | [] => []
  | x :: xs =>
      let y := step occupied x
      y :: parkFrom step (y :: occupied) xs

private theorem parkFrom_length {n : Nat} {α : Type}
    (step : List (Spot n) -> α -> Spot n) (occupied : List (Spot n)) (xs : List α) :
    (parkFrom step occupied xs).length = xs.length := by
  induction xs generalizing occupied with
  | nil => rfl
  | cons x xs ih => simp [parkFrom, ih]

private theorem parkFrom_nodup_and_fresh {n : Nat} {α : Type}
    (step : List (Spot n) -> α -> Spot n)
    (fresh : ∀ occupied x, occupied.Nodup -> occupied.length <= n ->
      step occupied x ∉ occupied)
    (occupied : List (Spot n)) (xs : List α)
    (hnodup : occupied.Nodup) (hcap : occupied.length + xs.length <= n) :
    (parkFrom step occupied xs).Nodup /\
      ∀ y ∈ parkFrom step occupied xs, y ∉ occupied := by
  induction xs generalizing occupied with
  | nil => simp [parkFrom]
  | cons x xs ih =>
      let y := step occupied x
      have hy : y ∉ occupied := fresh occupied x hnodup (by omega)
      have hnext : (y :: occupied).length + xs.length <= n := by
        simp only [List.length_cons]
        simp only [List.length_cons] at hcap
        omega
      have hi := ih (y :: occupied) (List.nodup_cons.mpr ⟨hy, hnodup⟩) hnext
      constructor
      · rw [parkFrom, List.nodup_cons]
        refine ⟨?_, hi.1⟩
        intro hymem
        exact (hi.2 y hymem) (by simp)
      · intro z hz
        simp only [parkFrom, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hy
        · exact fun hzo => hi.2 z hz (by simp [hzo])

private theorem actualStep_fresh (n : Nat) (occupied : List (Spot n))
    (q : ActualChoice n) (hnodup : occupied.Nodup) (hcard : occupied.length <= n) :
    actualStep n occupied q ∉ occupied := by
  simp only [actualStep]
  split
  · exact firstFree_fresh n occupied q.second hnodup hcard
  · assumption

/-- Landing spots of the literal ordered two-choice process, in car order. -/
def actualSpots (n : Nat) (choices : ActualPreferences n) : List (Spot n) :=
  parkFrom (actualStep n) [] (List.ofFn choices)

/-- Landing spots of the comparison one-choice process, in car order. -/
def oneSpots (n : Nat) (anchors : Anchors n) : List (Spot n) :=
  parkFrom (oneStep n) [] (List.ofFn anchors)

/-- Every actual prefix has its exact number of landings and no spot is repeated. -/
theorem actual_prefix_fresh (n : Nat) (choices : List (ActualChoice n))
    (h : choices.length <= n) :
    (parkFrom (actualStep n) [] choices).length = choices.length /\
      (parkFrom (actualStep n) [] choices).Nodup := by
  exact ⟨parkFrom_length _ [] choices,
    (parkFrom_nodup_and_fresh (actualStep n) (actualStep_fresh n) [] choices
      (by simp) (by simpa using h)).1⟩

private theorem one_prefix_fresh (n : Nat) (anchors : List (Spot n))
    (h : anchors.length <= n) :
    (parkFrom (oneStep n) [] anchors).length = anchors.length /\
      (parkFrom (oneStep n) [] anchors).Nodup := by
  exact ⟨parkFrom_length _ [] anchors,
    (parkFrom_nodup_and_fresh (oneStep n)
      (fun occupied anchor hnodup hcard =>
        firstFree_fresh n occupied anchor hnodup hcard) [] anchors
      (by simp) (by simpa using h)).1⟩

private def vacancy (n : Nat) (landings : List (Spot n)) : Spot n :=
  firstFree n landings 0

/-- The unique empty spot after all actual choices have run. -/
def actualEmpty (n : Nat) (choices : ActualPreferences n) : Spot n :=
  vacancy n (actualSpots n choices)

/-- The unique empty spot after all one-choice anchors have run. -/
def oneEmpty (n : Nat) (anchors : Anchors n) : Spot n :=
  vacancy n (oneSpots n anchors)

private theorem unique_vacancy_of_full {n : Nat} (landings : List (Spot n))
    (hlen : landings.length = n) (hnodup : landings.Nodup) :
    ∀ x : Spot n, x ∉ landings ↔ x = vacancy n landings := by
  have hcard : landings.toFinset.card = n := by
    simpa [landings.toFinset_card_of_nodup hnodup] using hlen
  have hempty : vacancy n landings ∉ landings := by
    exact firstFree_fresh n landings 0 hnodup (by omega)
  intro x
  constructor
  · intro hx
    by_contra hne
    have hsub : landings.toFinset ∪ {x, vacancy n landings} ⊆ Finset.univ := by simp
    have hle := Finset.card_le_card hsub
    have hpair : ({x, vacancy n landings} : Finset (Spot n)).card = 2 := by simp [hne]
    have hdis : Disjoint landings.toFinset ({x, vacancy n landings} : Finset (Spot n)) := by
      rw [Finset.disjoint_left]
      intro a ha hapair
      simp only [Finset.mem_insert, Finset.mem_singleton] at hapair
      rcases hapair with rfl | rfl
      · exact hx (List.mem_toFinset.mp ha)
      · exact hempty (List.mem_toFinset.mp ha)
    rw [Finset.card_union_of_disjoint hdis, hcard, hpair] at hle
    simpa using hle
  · rintro rfl
    exact hempty

/-- Exactly one circular spot is empty after the actual run. -/
theorem actual_unique_vacancy (n : Nat) (choices : ActualPreferences n) :
    ∀ x : Spot n, x ∉ actualSpots n choices ↔ x = actualEmpty n choices := by
  apply unique_vacancy_of_full (actualSpots n choices)
  · simp [actualSpots, parkFrom_length]
  · exact (actual_prefix_fresh n (List.ofFn choices) (by simp)).2

theorem one_unique_vacancy (n : Nat) (anchors : Anchors n) :
    ∀ x : Spot n, x ∉ oneSpots n anchors ↔ x = oneEmpty n anchors := by
  apply unique_vacancy_of_full (oneSpots n anchors)
  · simp [oneSpots, parkFrom_length]
  · exact (one_prefix_fresh n (List.ofFn anchors) (by simp)).2

private def rotateList {n : Nat} (t : Spot n) (occupied : List (Spot n)) : List (Spot n) :=
  occupied.map fun x => x + t

private theorem mem_rotateList_iff {n : Nat} (t x : Spot n) (occupied : List (Spot n)) :
    x + t ∈ rotateList t occupied ↔ x ∈ occupied := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨y, hy, heq⟩
    have : y = x := by simpa using add_right_cancel heq
    simpa [this] using hy
  · intro h
    exact List.mem_map.mpr ⟨x, h, rfl⟩

private theorem freeOffsets_rotate {n : Nat} (t start : Spot n)
    (occupied : List (Spot n)) :
    freeOffsets n (rotateList t occupied).toFinset (start + t) =
      freeOffsets n occupied.toFinset start := by
  ext r
  simp only [freeOffsets, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset]
  change orbitEquiv n (start + t) r ∉ rotateList t occupied ↔
    orbitEquiv n start r ∉ occupied
  rw [show orbitEquiv n (start + t) r = orbitEquiv n start r + t by
    simp [orbitEquiv, add_assoc, add_comm, add_left_comm]]
  exact not_congr (mem_rotateList_iff t _ occupied)

private theorem firstFree_rotate {n : Nat} (t start : Spot n)
    (occupied : List (Spot n)) :
    firstFree n (rotateList t occupied) (start + t) = firstFree n occupied start + t := by
  have hf := freeOffsets_rotate t start occupied
  have hoff : firstFreeOffset n (rotateList t occupied).toFinset (start + t) =
      firstFreeOffset n occupied.toFinset start := by
    simp only [firstFreeOffset]
    split <;> split
    · simpa [hf]
    · rename_i hleft hright
      exact (hright (hf ▸ hleft)).elim
    · rename_i hleft hright
      exact (hleft (hf.symm ▸ hright)).elim
    · rfl
  simp only [firstFree]
  rw [hoff]
  simp [orbitEquiv, add_assoc, add_comm, add_left_comm]

/-- Rotate both entries of an actual ordered choice. -/
def rotateChoice {n : Nat} (t : Spot n) (q : ActualChoice n) : ActualChoice n where
  anchor := q.anchor + t
  second := q.second + t
  distinct := by simpa using q.distinct

/-- Rotate every actual choice by the same displacement. -/
def rotateActual {n : Nat} (t : Spot n) (choices : ActualPreferences n) :
    ActualPreferences n := fun i => rotateChoice t (choices i)

/-- Rotate every one-choice anchor by the same displacement. -/
def rotateAnchors {n : Nat} (t : Spot n) (anchors : Anchors n) : Anchors n :=
  fun i => anchors i + t

private theorem actualStep_rotate {n : Nat} (t : Spot n) (occupied : List (Spot n))
    (q : ActualChoice n) :
    actualStep n (rotateList t occupied) (rotateChoice t q) = actualStep n occupied q + t := by
  by_cases h : q.anchor ∈ occupied
  · have hr : q.anchor + t ∈ rotateList t occupied := (mem_rotateList_iff t q.anchor occupied).2 h
    simp [actualStep, rotateChoice, h, hr, firstFree_rotate]
  · have hr : q.anchor + t ∉ rotateList t occupied := by
      simpa only [mem_rotateList_iff] using h
    simp [actualStep, rotateChoice, h, hr]

private theorem parkFrom_rotate {n : Nat} {α : Type}
    (step : List (Spot n) -> α -> Spot n) (rotateInput : α -> α) (t : Spot n)
    (hstep : ∀ occupied x,
      step (rotateList t occupied) (rotateInput x) = step occupied x + t)
    (occupied : List (Spot n)) (xs : List α) :
    parkFrom step (rotateList t occupied) (xs.map rotateInput) =
      rotateList t (parkFrom step occupied xs) := by
  induction xs generalizing occupied with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, parkFrom]
      rw [hstep]
      rw [show (step occupied x + t) :: rotateList t occupied =
        rotateList t (step occupied x :: occupied) by rfl]
      rw [ih]
      rfl

/-- Actual landings rotate with both ordered choices. -/
theorem actualSpots_rotate {n : Nat} (t : Spot n) (choices : ActualPreferences n) :
    actualSpots n (rotateActual t choices) = rotateList t (actualSpots n choices) := by
  have hofFn :
      List.ofFn (rotateActual t choices) = (List.ofFn choices).map (rotateChoice t) := by
    ext i hi
    simp [rotateActual]
  rw [actualSpots, hofFn]
  exact parkFrom_rotate (actualStep n) (rotateChoice t) t (actualStep_rotate t) [] _

private theorem oneSpots_rotate {n : Nat} (t : Spot n) (anchors : Anchors n) :
    oneSpots n (rotateAnchors t anchors) = rotateList t (oneSpots n anchors) := by
  have hofFn :
      List.ofFn (rotateAnchors t anchors) = (List.ofFn anchors).map (fun x => x + t) := by
    ext i hi
    simp [rotateAnchors]
  have hstep : ∀ occupied anchor,
      oneStep n (rotateList t occupied) (anchor + t) = oneStep n occupied anchor + t :=
    fun occupied anchor => firstFree_rotate t anchor occupied
  rw [oneSpots, hofFn]
  exact parkFrom_rotate (oneStep n) (fun x => x + t) t hstep [] _

/-- The actual empty spot obeys the concrete translation law. -/
theorem actualEmpty_rotate {n : Nat} (t : Spot n) (choices : ActualPreferences n) :
    actualEmpty n (rotateActual t choices) = actualEmpty n choices + t := by
  symm
  apply (actual_unique_vacancy n (rotateActual t choices) _).1
  rw [actualSpots_rotate]
  simpa [mem_rotateList_iff] using
    (actual_unique_vacancy n choices (actualEmpty n choices)).2 rfl

private theorem oneEmpty_rotate {n : Nat} (t : Spot n) (anchors : Anchors n) :
    oneEmpty n (rotateAnchors t anchors) = oneEmpty n anchors + t := by
  symm
  apply (one_unique_vacancy n (rotateAnchors t anchors) _).1
  rw [oneSpots_rotate]
  simpa [mem_rotateList_iff] using
    (one_unique_vacancy n anchors (oneEmpty n anchors)).2 rfl

/-- Recover the clockwise increment from an actual ordered pair. -/
def actualIncrement {n : Nat} (q : ActualChoice n) : Increment n :=
  ⟨(q.second - q.anchor).val, by
    constructor
    · by_contra h
      have hz : (q.second - q.anchor).val = 0 := by omega
      have heq : q.second - q.anchor = 0 :=
        ZMod.val_injective (n + 1) (by simpa using hz)
      exact q.distinct (sub_eq_zero.mp heq)
    · have := ZMod.val_lt (q.second - q.anchor)
      omega⟩

/-- Reconstruct an actual ordered pair from its anchor and positive increment. -/
def choiceOfAnchorIncrement {n : Nat} (anchor : Spot n) (k : Increment n) : ActualChoice n where
  anchor := anchor
  second := anchor + (k.1 : Spot n)
  distinct := by
    intro h
    have hklt : k.1 < n + 1 := (Nat.lt_succ_iff).2 k.property.2
    have hz : ((k.1 : Nat) : Spot n) = 0 := by
      apply_fun fun x => x - anchor at h
      simpa [add_sub_cancel_left] using h
    have hv := congrArg ZMod.val hz
    have hkzero : k.1 = 0 := by
      simpa [ZMod.val_natCast_of_lt hklt] using hv
    have hkpos := k.property.1
    omega

/-- The increment readout of all actual choices. -/
def actualIncrements {n : Nat} (choices : ActualPreferences n) : IncrementMatrix n :=
  fun i => actualIncrement (choices i)

private def anchorsOf {n : Nat} (choices : ActualPreferences n) : Anchors n :=
  fun i => (choices i).anchor

private def choicesOf {n : Nat} (anchors : Anchors n) (increments : IncrementMatrix n) :
    ActualPreferences n :=
  fun i => choiceOfAnchorIncrement (anchors i) (increments i)

private def fixedActualEmpty {n : Nat} (increments : IncrementMatrix n)
    (anchors : Anchors n) : Spot n :=
  actualEmpty n (choicesOf anchors increments)

private def normalizeAnchors {n : Nat} (empty : Anchors n -> Spot n)
    (j : Spot n) (anchors : Anchors n) : Anchors n :=
  rotateAnchors (j - empty anchors) anchors

/-- Actual fixed-increment inputs whose unique vacancy is the observed spot. -/
def FixedActualFiber (n : Nat) (increments : IncrementMatrix n) (j : Spot n) :=
  {choices : ActualPreferences n //
    actualIncrements choices = increments /\ actualEmpty n choices = j}

/-- One-choice circular inputs whose unique vacancy is the observed spot. -/
def OneChoiceFiber (n : Nat) (j : Spot n) :=
  {anchors : Anchors n // oneEmpty n anchors = j}

/-- Orbit normalization transports a fixed-increment actual fiber to the
one-choice fiber with the same observed vacancy. -/
def fixedFiberToOneChoice {n : Nat} (increments : IncrementMatrix n) (j : Spot n) :
    FixedActualFiber n increments j -> OneChoiceFiber n j := fun choices =>
  let anchors := anchorsOf choices.1
  let normalized := normalizeAnchors (oneEmpty n) j anchors
  ⟨normalized, by
    dsimp [normalized, normalizeAnchors]
    rw [oneEmpty_rotate]
    abel⟩

/-- The inverse orbit normalization reconstructs both ordered choices. -/
def oneChoiceToFixedFiber {n : Nat} (increments : IncrementMatrix n) (j : Spot n) :
    OneChoiceFiber n j -> FixedActualFiber n increments j := fun anchors =>
  let normalized := normalizeAnchors (fixedActualEmpty increments) j anchors.1
  ⟨choicesOf normalized increments,
    by
      funext i
      apply Subtype.ext
      simp only [actualIncrements, choicesOf, actualIncrement, choiceOfAnchorIncrement]
      rw [add_sub_cancel_left,
        ZMod.val_natCast_of_lt ((Nat.lt_succ_iff).2 (increments i).property.2)],
    by
      have hchoicesRotate : ∀ (t : Spot n) (a : Anchors n),
          choicesOf (rotateAnchors t a) increments =
            rotateActual t (choicesOf a increments) := by
        intro t a
        funext i
        simp only [choicesOf, rotateAnchors, rotateActual, choiceOfAnchorIncrement,
          rotateChoice]
        congr 1 <;> abel
      dsimp [normalized, normalizeAnchors]
      rw [hchoicesRotate, actualEmpty_rotate]
      change fixedActualEmpty increments anchors.1 +
        (j - fixedActualEmpty increments anchors.1) = j
      abel⟩

/-- The explicit fixed-increment, fixed-vacancy transport and its inverse. -/
def fixedFiberOneChoiceEquiv {n : Nat} (increments : IncrementMatrix n) (j : Spot n) :
    FixedActualFiber n increments j ≃ OneChoiceFiber n j where
  toFun := fixedFiberToOneChoice increments j
  invFun := oneChoiceToFixedFiber increments j
  left_inv choices := by
    apply Subtype.ext
    have hchoice : ∀ q : ActualChoice n,
        choiceOfAnchorIncrement q.anchor (actualIncrement q) = q := by
      intro q
      cases q with
      | mk anchor second distinct =>
          simp only [choiceOfAnchorIncrement, actualIncrement]
          congr
          rw [ZMod.natCast_zmod_val]
          abel
    have hrecover : choicesOf (anchorsOf choices.1) increments = choices.1 := by
      calc
        choicesOf (anchorsOf choices.1) increments =
            choicesOf (anchorsOf choices.1) (actualIncrements choices.1) := by
              rw [choices.2.1]
        _ = choices.1 := by
          funext i
          exact hchoice (choices.1 i)
    have hbase : fixedActualEmpty increments (anchorsOf choices.1) = j := by
      change actualEmpty n (choicesOf (anchorsOf choices.1) increments) = j
      rw [hrecover]
      exact choices.2.2
    have hchoicesRotate : ∀ (t : Spot n) (a : Anchors n),
        choicesOf (rotateAnchors t a) increments =
          rotateActual t (choicesOf a increments) := by
      intro t a
      funext i
      simp only [choicesOf, rotateAnchors, rotateActual, choiceOfAnchorIncrement,
        rotateChoice]
      congr 1 <;> abel
    have hfixedRotate : ∀ (t : Spot n) (a : Anchors n),
        fixedActualEmpty increments (rotateAnchors t a) =
          fixedActualEmpty increments a + t := by
      intro t a
      change actualEmpty n (choicesOf (rotateAnchors t a) increments) =
        actualEmpty n (choicesOf a increments) + t
      rw [hchoicesRotate, actualEmpty_rotate]
    have hcross :
        normalizeAnchors (fixedActualEmpty increments) j
          (normalizeAnchors (oneEmpty n) j (anchorsOf choices.1)) =
            anchorsOf choices.1 := by
      funext i
      simp only [normalizeAnchors, rotateAnchors]
      rw [hfixedRotate, hbase]
      abel
    change choicesOf
      (normalizeAnchors (fixedActualEmpty increments) j
        (normalizeAnchors (oneEmpty n) j (anchorsOf choices.1))) increments = choices.1
    rw [hcross]
    exact hrecover
  right_inv anchors := by
    apply Subtype.ext
    have hcross :
        normalizeAnchors (oneEmpty n) j
          (normalizeAnchors (fixedActualEmpty increments) j anchors.1) = anchors.1 := by
      funext i
      simp only [normalizeAnchors, rotateAnchors]
      rw [oneEmpty_rotate, anchors.2]
      abel
    change normalizeAnchors (oneEmpty n) j
      (anchorsOf (choicesOf
        (normalizeAnchors (fixedActualEmpty increments) j anchors.1) increments)) = anchors.1
    change normalizeAnchors (oneEmpty n) j
      (normalizeAnchors (fixedActualEmpty increments) j anchors.1) = anchors.1
    exact hcross

def cutSpot {n : Nat} (j x : Spot n) : Nat :=
  (x - j).val

def uncutSpot {n : Nat} (j : Spot n) (p : Nat) : Spot n :=
  j + (p : Spot n)

private theorem firstFree_of_not_mem {n : Nat} (occupied : List (Spot n))
    (start : Spot n) (hfree : start ∉ occupied) :
    firstFree n occupied start = start := by
  have hzero : (0 : Fin (n + 1)) ∈ freeOffsets n occupied.toFinset start := by
    simp [freeOffsets, orbitEquiv, hfree]
  have hne : (freeOffsets n occupied.toFinset start).Nonempty := ⟨0, hzero⟩
  have hmin : (freeOffsets n occupied.toFinset start).min' hne = 0 :=
    le_antisymm (Finset.min'_le _ _ hzero) (Fin.zero_le _)
  simp [firstFree, firstFreeOffset, hne, hmin, orbitEquiv]

private theorem firstFree_cut_zero {n : Nat} (occupied : List (Spot n))
    (start : Spot n) (hnodup : occupied.Nodup) (hcard : occupied.length <= n)
    (hzero : (0 : Spot n) ∉ occupied) (hyzero : firstFree n occupied start ≠ 0) :
    cutSpot 0 (firstFree n occupied start) =
      parkStep (occupied.map (cutSpot 0)) (cutSpot 0 start) := by
  have orbit_apply (s : Spot n) (r : Fin (n + 1)) :
      orbitEquiv n s r = (r.val : Spot n) + s := by
    simp only [orbitEquiv, Equiv.trans_apply]
    have hfin : (ZMod.finEquiv (n + 1)).toEquiv r = (r.val : Spot n) := by
      apply ZMod.val_injective (n + 1)
      change r.val = ((r.val : Nat) : Spot n).val
      rw [ZMod.val_natCast_of_lt r.isLt]
    rw [hfin, Equiv.coe_addRight]
  let off := firstFreeOffset n occupied.toFinset start
  let y := firstFree n occupied start
  have hstart : start ≠ 0 := by
    intro hs
    subst start
    exact hyzero (firstFree_of_not_mem occupied 0 hzero)
  letI : NeZero start := ⟨hstart⟩
  let zeroOff : Fin (n + 1) := ⟨(-start).val, ZMod.val_lt _⟩
  have hzeroOrbit : orbitEquiv n start zeroOff = 0 := by
    rw [orbit_apply]
    dsimp [zeroOff]
    rw [ZMod.natCast_zmod_val]
    abel
  have hzeroMem : zeroOff ∈ freeOffsets n occupied.toFinset start := by
    simp [freeOffsets, hzeroOrbit, hzero]
  have hne : (freeOffsets n occupied.toFinset start).Nonempty := ⟨zeroOff, hzeroMem⟩
  have hoffle : off <= zeroOff := by
    change firstFreeOffset n occupied.toFinset start <= zeroOff
    rw [firstFreeOffset, dif_pos hne]
    exact Finset.min'_le _ _ hzeroMem
  have hofflt : off < zeroOff := by
    exact hoffle.lt_of_ne fun heq => hyzero (by
      change firstFree n occupied start = 0
      rw [firstFree, show firstFreeOffset n occupied.toFinset start = zeroOff from heq]
      exact hzeroOrbit)
  have hzeroVal : zeroOff.val = n + 1 - start.val := by
    exact ZMod.val_neg_of_ne_zero start
  have hsum : start.val + off.val < n + 1 := by
    change off.val < zeroOff.val at hofflt
    rw [hzeroVal] at hofflt
    omega
  have hyval : y.val = start.val + off.val := by
    have hsum' : start.val + (firstFreeOffset n occupied.toFinset start).val < n + 1 := by
      simpa [off] using hsum
    change (firstFree n occupied start).val =
      start.val + (firstFreeOffset n occupied.toFinset start).val
    rw [firstFree, orbit_apply]
    have hoffVal :
        (((firstFreeOffset n occupied.toFinset start).val : Nat) : Spot n).val =
          (firstFreeOffset n occupied.toFinset start).val :=
      ZMod.val_natCast_of_lt (firstFreeOffset n occupied.toFinset start).isLt
    rw [ZMod.val_add_of_lt (by simpa [hoffVal, add_comm] using hsum'), hoffVal]
    omega
  have hyfresh : y ∉ occupied := by
    exact firstFree_fresh n occupied start hnodup hcard
  have hyMap : y.val ∉ occupied.map (cutSpot 0) := by
    intro hm
    rcases List.mem_map.mp hm with ⟨z, hz, heq⟩
    apply hyfresh
    have : z = y := ZMod.val_injective (n + 1) (by simpa [cutSpot] using heq)
    simpa [this] using hz
  have hskipped : ∀ q, start.val <= q -> q < y.val ->
      q ∈ occupied.map (cutSpot 0) := by
    intro q hp hq
    have hqn : q < n + 1 := lt_trans hq (ZMod.val_lt y)
    let r : Fin (n + 1) := ⟨q - start.val, by omega⟩
    have hr : r < off := by
      rw [hyval] at hq
      change r.val < off.val
      dsimp [r]
      omega
    have hrmem := firstFree_skipped n occupied start hnodup hcard r hr
    have horbit : orbitEquiv n start r = (q : Spot n) := by
      rw [orbit_apply]
      dsimp [r]
      calc
        ((q - start.val : Nat) : Spot n) + start =
            ((q - start.val : Nat) : Spot n) + (start.val : Spot n) := by
              rw [ZMod.natCast_zmod_val]
        _ = (((q - start.val) + start.val : Nat) : Spot n) := by
              rw [Nat.cast_add]
        _ = (q : Spot n) := by congr 1; omega
    rw [horbit] at hrmem
    apply List.mem_map.mpr
    refine ⟨(q : Spot n), hrmem, ?_⟩
    simp [cutSpot, ZMod.val_natCast_of_lt hqn]
  have hlinear := parkStep_spec (occupied.map (cutSpot 0)) start.val
  have hforward : y.val <= parkStep (occupied.map (cutSpot 0)) start.val := by
    by_contra hlt
    exact hlinear.1 (hskipped _ (le_parkStep _ _) (by omega))
  have hbackward : parkStep (occupied.map (cutSpot 0)) start.val <= y.val := by
    by_contra hlt
    exact hyMap (hlinear.2 y.val (by rw [hyval]; omega) (by omega))
  simpa [cutSpot, y] using le_antisymm hforward hbackward

theorem firstFree_cut {n : Nat} (occupied : List (Spot n)) (start j : Spot n)
    (hnodup : occupied.Nodup) (hcard : occupied.length <= n)
    (hj : j ∉ occupied) (hyj : firstFree n occupied start ≠ j) :
    cutSpot j (firstFree n occupied start) =
      parkStep (occupied.map (cutSpot j)) (cutSpot j start) := by
  have hrotNodup : (rotateList (-j) occupied).Nodup := by
    exact hnodup.map fun _ _ h => add_right_cancel h
  have hrotCard : (rotateList (-j) occupied).length <= n := by
    simpa [rotateList] using hcard
  have hrotZero : (0 : Spot n) ∉ rotateList (-j) occupied := by
    intro h
    apply hj
    apply (mem_rotateList_iff (-j) j occupied).1
    simpa using h
  have hrotLanding : firstFree n (rotateList (-j) occupied) (start - j) ≠ 0 := by
    rw [show start - j = start + -j by abel, firstFree_rotate]
    intro h
    apply hyj
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)
  have h := firstFree_cut_zero (rotateList (-j) occupied) (start - j)
    hrotNodup hrotCard hrotZero hrotLanding
  rw [show start - j = start + -j by abel, firstFree_rotate] at h
  have hmap : (rotateList (-j) occupied).map (cutSpot 0) =
      occupied.map (cutSpot j) := by
    simp [cutSpot, rotateList, List.map_map, Function.comp_def, sub_eq_add_neg]
  rw [hmap] at h
  simpa [cutSpot, sub_eq_add_neg, add_comm] using h

theorem firstFree_ne_vacancy {n : Nat} (occupied : List (Spot n))
    (j : Spot n) (p q : Nat) (hp : 1 <= p) (hpq : p <= q) (hq : q <= n)
    (hfree : uncutSpot j q ∉ occupied) :
    firstFree n occupied (uncutSpot j p) ≠ j := by
  have orbit_apply (s : Spot n) (r : Fin (n + 1)) :
      orbitEquiv n s r = (r.val : Spot n) + s := by
    simp only [orbitEquiv, Equiv.trans_apply]
    have hfin : (ZMod.finEquiv (n + 1)).toEquiv r = (r.val : Spot n) := by
      apply ZMod.val_injective (n + 1)
      change r.val = ((r.val : Nat) : Spot n).val
      rw [ZMod.val_natCast_of_lt r.isLt]
    rw [hfin, Equiv.coe_addRight]
  let qoff : Fin (n + 1) := ⟨q - p, by omega⟩
  let joff : Fin (n + 1) := ⟨n + 1 - p, by omega⟩
  have hqorbit : orbitEquiv n (uncutSpot j p) qoff = uncutSpot j q := by
    rw [orbit_apply]
    simp only [qoff, uncutSpot]
    have hc : ((q - p : Nat) : Spot n) + (p : Spot n) = (q : Spot n) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    rw [show ((q - p : Nat) : Spot n) + (j + (p : Spot n)) =
      j + (((q - p : Nat) : Spot n) + (p : Spot n)) by abel, hc]
  have hjorbit : orbitEquiv n (uncutSpot j p) joff = j := by
    rw [orbit_apply]
    simp only [joff, uncutSpot]
    have hm : ((n + 1 : Nat) : Spot n) = 0 := ZMod.natCast_self (n + 1)
    have hc : ((n + 1 - p : Nat) : Spot n) + (p : Spot n) = 0 := by
      rw [← Nat.cast_add, show n + 1 - p + p = n + 1 by omega, hm]
    rw [show ((n + 1 - p : Nat) : Spot n) + (j + (p : Spot n)) =
      j + (((n + 1 - p : Nat) : Spot n) + (p : Spot n)) by abel, hc, add_zero]
  have hqmem : qoff ∈ freeOffsets n occupied.toFinset (uncutSpot j p) := by
    simp [freeOffsets, hqorbit, hfree]
  have hne : (freeOffsets n occupied.toFinset (uncutSpot j p)).Nonempty := ⟨qoff, hqmem⟩
  have hoffq : firstFreeOffset n occupied.toFinset (uncutSpot j p) <= qoff := by
    rw [firstFreeOffset, dif_pos hne]
    exact Finset.min'_le _ _ hqmem
  have hqj : qoff < joff := by
    change q - p < n + 1 - p
    omega
  intro hy
  have heq : firstFreeOffset n occupied.toFinset (uncutSpot j p) = joff := by
    apply (orbitEquiv n (uncutSpot j p)).injective
    calc
      orbitEquiv n (uncutSpot j p)
          (firstFreeOffset n occupied.toFinset (uncutSpot j p)) =
          firstFree n occupied (uncutSpot j p) := rfl
      _ = j := hy
      _ = orbitEquiv n (uncutSpot j p) joff := hjorbit.symm
  rw [heq] at hoffq
  exact (not_le_of_gt hqj) hoffq

theorem cut_run {n : Nat} (j : Spot n) (occupied : List (Spot n))
    (anchors : List (Spot n)) (hnodup : occupied.Nodup)
    (hcap : occupied.length + anchors.length <= n) (hjocc : j ∉ occupied)
    (hjrun : j ∉ parkFrom (oneStep n) occupied anchors) :
    D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
        (occupied.map (cutSpot j)) (anchors.map (cutSpot j)) =
        (parkFrom (oneStep n) occupied anchors).map (cutSpot j) /\
      ∀ x ∈ anchors, x ≠ j := by
  induction anchors generalizing occupied with
  | nil =>
      constructor
      · rfl
      · simp
  | cons x xs ih =>
      let y := oneStep n occupied x
      have hyfresh := firstFree_fresh n occupied x hnodup (by omega)
      have hyj : y ≠ j := by
        intro heq
        apply hjrun
        simp [parkFrom, y, heq]
      have hxj : x ≠ j := by
        intro heq
        subst x
        exact hyj (by simp [y, oneStep, firstFree_of_not_mem occupied j hjocc])
      have hstep : cutSpot j y = parkStep (occupied.map (cutSpot j)) (cutSpot j x) :=
        firstFree_cut occupied x j hnodup (by omega) hjocc (by simpa [oneStep, y] using hyj)
      have htail : j ∉ parkFrom (oneStep n) (y :: occupied) xs := by
        intro hm
        exact hjrun (by simp [parkFrom, y, hm])
      have hi := ih (y :: occupied) (List.nodup_cons.mpr ⟨hyfresh, hnodup⟩)
        (by simp only [List.length_cons] at hcap ⊢; omega)
        (by simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hyj, hjocc⟩) htail
      constructor
      · simp only [List.map_cons,
          D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom, parkFrom]
        rw [← hstep]
        change cutSpot j y ::
            D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
              (cutSpot j y :: occupied.map (cutSpot j))
              (xs.map (cutSpot j)) =
          cutSpot j y :: (parkFrom (oneStep n) (y :: occupied) xs).map (cutSpot j)
        apply congrArg (List.cons (cutSpot j y))
        simpa only [List.map_cons] using hi.1
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxj
        · exact hi.2 z hz

end D5.S3.Combinatorics.CircularTwoChoiceParkingBijection
