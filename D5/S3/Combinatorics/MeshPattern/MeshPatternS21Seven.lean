/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Seven
   mirror-E: none(waiver:elementary-rank-three-local-construction)
   anchors: [mathlib/module/Mathlib.Order.Monotone.Defs]
   utility: none
   digest: The partial seven-state rule succeeds on every rank-bounded permutation rectangle. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Region
import Mathlib.Order.Monotone.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21

inductive SevenLabel
  | empty | one | twoRow | twoCol | threeRow | hook | threeCol
  deriving DecidableEq

def SevenLabel.size : SevenLabel → ℕ
  | .empty => 0
  | .one => 1
  | .twoRow | .twoCol => 2
  | .threeRow | .hook | .threeCol => 3

def sevenEdge (smaller larger : SevenLabel) : Bool :=
  smaller == larger || match smaller, larger with
    | .empty, .one | .one, .twoRow | .one, .twoCol | .twoRow, .threeRow
    | .twoRow, .hook | .twoCol, .hook | .twoCol, .threeCol => true
    | _, _ => false

def sevenInverse (northeast northwest southeast : SevenLabel) :
    Option (SevenLabel × Bool) :=
  match northeast, northwest, southeast with
  | .empty, .empty, .empty => some (.empty, false)
  | .one, .one, .one => some (.one, false)
  | .one, .one, .empty | .one, .empty, .one => some (.empty, false)
  | .one, .empty, .empty => some (.empty, true)
  | .twoRow, .twoRow, .twoRow => some (.twoRow, false)
  | .twoRow, .twoRow, .one | .twoRow, .one, .twoRow => some (.one, false)
  | .twoRow, .one, .one => some (.one, true)
  | .twoCol, .twoCol, .twoCol => some (.twoCol, false)
  | .twoCol, .twoCol, .one | .twoCol, .one, .twoCol => some (.one, false)
  | .twoCol, .one, .one => some (.empty, false)
  | .threeRow, .threeRow, .threeRow => some (.threeRow, false)
  | .threeRow, .threeRow, .twoRow | .threeRow, .twoRow, .threeRow =>
    some (.twoRow, false)
  | .threeRow, .twoRow, .twoRow => some (.twoRow, true)
  | .hook, .hook, .hook => some (.hook, false)
  | .hook, .hook, .twoRow | .hook, .twoRow, .hook => some (.twoRow, false)
  | .hook, .hook, .twoCol | .hook, .twoCol, .hook => some (.twoCol, false)
  | .hook, .twoRow, .twoCol | .hook, .twoCol, .twoRow => some (.one, false)
  | .hook, .twoRow, .twoRow => some (.one, false)
  | .hook, .twoCol, .twoCol => some (.twoCol, true)
  | .threeCol, .threeCol, .threeCol => some (.threeCol, false)
  | .threeCol, .threeCol, .twoCol | .threeCol, .twoCol, .threeCol =>
    some (.twoCol, false)
  | .threeCol, .twoCol, .twoCol => some (.one, false)
  | _, _, _ => none

def sevenForward (southwest northwest southeast : SevenLabel) (entry : Bool) :
    Option SevenLabel :=
  [SevenLabel.empty, .one, .twoRow, .twoCol, .threeRow, .hook, .threeCol].find?
    (fun northeast => decide (sevenInverse northeast northwest southeast =
      some (southwest, entry)))

def sevenDiagram (p : List ℕ) (x y : ℕ) : Option SevenLabel :=
  match x, y with
  | 0, _ | _, 0 => some .empty
  | x + 1, y + 1 => do
    let southwest ← sevenDiagram p x y
    let northwest ← sevenDiagram p x (y + 1)
    let southeast ← sevenDiagram p (x + 1) y
    sevenForward southwest northwest southeast (decide (p.getD x 0 = y + 1))
termination_by x + y

open scoped Classical in
theorem seven_state_construction (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n)) :
    ∀ x ≤ n, ∀ y ≤ n, (rectangle p x y).card ≤ 3 →
      ∃ label, sevenDiagram p x y = some label ∧
        label.size = (rectangle p x y).card ∧
        (∀ west, sevenDiagram p (x - 1) y = some west → sevenEdge west label = true) ∧
        (∀ south, sevenDiagram p x (y - 1) = some south → sevenEdge south label = true) := by
  have hlength : p.length = n := by simpa using hp.length_eq
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hpositive : ∀ position < n, 0 < p.getD position 0 := by
    intro position hposition
    have hmem := hp.mem_iff.mp (List.getElem_mem (show position < p.length by omega))
    rw [List.mem_range'_1] at hmem
    rw [List.getD_eq_getElem p 0 (by omega)]
    omega
  have hinjective : ∀ first < n, ∀ second < n,
      p.getD first 0 = p.getD second 0 → first = second := by
    intro first hfirst second hsecond heq
    rw [List.getD_eq_getElem p 0 (by omega),
      List.getD_eq_getElem p 0 (by omega)] at heq
    exact hnodup.getElem_inj_iff.mp heq
  have hmono : ∀ x y width height, x ≤ width → y ≤ height →
      rectangle p x y ⊆ rectangle p width height := by
    intro x y width height hx hy position hposition
    simp only [rectangle, Finset.mem_filter, Finset.mem_range] at hposition ⊢
    exact ⟨by omega, by omega⟩
  have hzero : ∀ x ≤ n, rectangle p x 0 = ∅ := by
    intro x hx
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro position hposition
    simp only [rectangle, Finset.mem_filter, Finset.mem_range] at hposition
    have := hpositive position (by omega)
    omega
  have hhorizontal : ∀ x < n, ∀ y,
      rectangle p (x + 1) y =
        if p.getD x 0 ≤ y then insert x (rectangle p x y) else rectangle p x y := by
    intro x hx y
    ext position
    by_cases hvalue : p.getD x 0 ≤ y
    · simp only [hvalue, if_true, rectangle, Finset.mem_filter, Finset.mem_range,
        Finset.mem_insert]
      constructor
      · rintro ⟨hposition, hbound⟩
        by_cases heq : position = x
        · exact Or.inl heq
        · exact Or.inr ⟨by omega, hbound⟩
      · rintro (rfl | ⟨hposition, hbound⟩)
        · exact ⟨by omega, hvalue⟩
        · exact ⟨by omega, hbound⟩
    · simp only [hvalue, if_false, rectangle, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hposition, hbound⟩
        have : position ≠ x := by rintro rfl; exact hvalue hbound
        exact ⟨by omega, hbound⟩
      · rintro ⟨hposition, hbound⟩
        exact ⟨by omega, hbound⟩
  have hlocal : ∀ southwest northwest southeast : SevenLabel, ∀ entry : Bool,
      sevenEdge southwest northwest = true → sevenEdge southwest southeast = true →
      (entry = true → southwest = northwest ∧ southwest = southeast) →
      northwest.size + southeast.size + (if entry then 1 else 0) ≤ southwest.size + 3 →
      ∃ northeast, sevenForward southwest northwest southeast entry = some northeast ∧
        northeast.size + southwest.size =
          northwest.size + southeast.size + (if entry then 1 else 0) ∧
        sevenEdge northwest northeast = true ∧ sevenEdge southeast northeast = true := by
    intro southwest northwest southeast entry
    cases southwest <;> cases northwest <;> cases southeast <;> cases entry <;> decide
  have hequal : ∀ smaller larger : SevenLabel,
      sevenEdge smaller larger = true → smaller.size = larger.size → smaller = larger := by
    intro smaller larger
    cases smaller <;> cases larger <;> decide
  have haxis : ∀ width, sevenDiagram p width 0 = some .empty := by
    intro width
    cases width <;> simp [sevenDiagram]
  intro x
  induction x with
  | zero =>
    intro hx y hy hrank
    refine ⟨.empty, ?_, ?_, ?_, ?_⟩
    · simp [sevenDiagram]
    · simp [SevenLabel.size, rectangle]
    · intro west hwest
      simp [sevenDiagram] at hwest
      subst west
      rfl
    · intro south hsouth
      simp [sevenDiagram] at hsouth
      subst south
      rfl
  | succ x ihx =>
    intro hx y
    induction y with
    | zero =>
      intro hy hrank
      refine ⟨.empty, ?_, ?_, ?_, ?_⟩
      · simp [sevenDiagram]
      · simp [SevenLabel.size, hzero (x + 1) hx]
      · intro west hwest
        simp only [Nat.add_sub_cancel, haxis, Option.some.injEq] at hwest
        subst west
        rfl
      · intro south hsouth
        simp [sevenDiagram] at hsouth
        subst south
        rfl
    | succ y ihy =>
      intro hy hrank
      have hswsub := hmono x y (x + 1) (y + 1) (by omega) (by omega)
      have hnwsub := hmono x (y + 1) (x + 1) (y + 1) (by omega) (by omega)
      have hsesub := hmono (x + 1) y (x + 1) (y + 1) (by omega) (by omega)
      obtain ⟨southwest, hsw, hswsize, _, _⟩ :=
        ihx (by omega) y (by omega) (le_trans (Finset.card_le_card hswsub) hrank)
      obtain ⟨northwest, hnw, hnwsize, _, hswedge⟩ :=
        ihx (by omega) (y + 1) hy (le_trans (Finset.card_le_card hnwsub) hrank)
      obtain ⟨southeast, hse, hsesize, hseedge, _⟩ :=
        ihy (by omega) (le_trans (Finset.card_le_card hsesub) hrank)
      have hedgeNW : sevenEdge southwest northwest = true := by
        apply hswedge
        simpa using hsw
      have hedgeSE : sevenEdge southwest southeast = true := by
        apply hseedge
        simpa using hsw
      have hnotmem : x ∉ rectangle p x y := by simp [rectangle]
      have hnotmemTop : x ∉ rectangle p x (y + 1) := by simp [rectangle]
      have hcount : (rectangle p (x + 1) (y + 1)).card + (rectangle p x y).card =
          (rectangle p x (y + 1)).card + (rectangle p (x + 1) y).card +
            (if p.getD x 0 = y + 1 then 1 else 0) := by
        rw [hhorizontal x (by omega) (y + 1), hhorizontal x (by omega) y]
        split_ifs
        all_goals
          try simp only [Finset.card_insert_of_notMem hnotmem,
            Finset.card_insert_of_notMem hnotmemTop]
          omega
      have hoccupied : p.getD x 0 = y + 1 →
          rectangle p x (y + 1) = rectangle p x y ∧
          rectangle p (x + 1) y = rectangle p x y := by
        intro hentry
        constructor
        · ext position
          simp only [rectangle, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hposition, hvalue⟩
            have hneq : p.getD position 0 ≠ y + 1 := by
              intro heq
              have := hinjective position (by omega) x (by omega) (heq.trans hentry.symm)
              omega
            exact ⟨hposition, by omega⟩
          · rintro ⟨hposition, hvalue⟩
            exact ⟨hposition, by omega⟩
        · rw [hhorizontal x (by omega) y, if_neg (show ¬p.getD x 0 ≤ y by omega)]
      let entry : Bool := decide (p.getD x 0 = y + 1)
      have hentryLabels : entry = true → southwest = northwest ∧ southwest = southeast := by
        intro hentry
        have hhit : p.getD x 0 = y + 1 := of_decide_eq_true hentry
        obtain ⟨hnweq, hseeq⟩ := hoccupied hhit
        constructor
        · apply hequal _ _ hedgeNW
          rw [hswsize, hnwsize, hnweq]
        · apply hequal _ _ hedgeSE
          rw [hswsize, hsesize, hseeq]
      have hsizeBound : northwest.size + southeast.size + (if entry then 1 else 0) ≤
          southwest.size + 3 := by
        rw [hnwsize, hsesize, hswsize]
        have hbit : (if entry then 1 else 0) =
            (if p.getD x 0 = y + 1 then 1 else 0) := by simp [entry]
        rw [hbit]
        omega
      obtain ⟨northeast, hforward, hsize, hnwedge, hsedge⟩ :=
        hlocal southwest northwest southeast entry hedgeNW hedgeSE hentryLabels hsizeBound
      refine ⟨northeast, ?_, ?_, ?_, ?_⟩
      · simp [sevenDiagram, hsw, hnw, hse, ← hforward, entry]
      · rw [hswsize, hnwsize, hsesize] at hsize
        have hbit : (if entry then 1 else 0) =
            (if p.getD x 0 = y + 1 then 1 else 0) := by simp [entry]
        rw [hbit] at hsize
        omega
      · intro west hwest
        have : west = northwest := by simpa [hnw] using hwest.symm
        subst west
        exact hnwedge
      · intro south hsouth
        have : south = southeast := by simpa [hse] using hsouth.symm
        subst south
        exact hsedge

theorem seven_order_interpretation (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n)) :
    ∀ x ≤ n, ∀ y ≤ n, ∀ label, sevenDiagram p x y = some label →
      (rectangle p x y).card ≤ 3 →
      (StrictMonoOn (fun position => p.getD position 0) (rectangle p x y) ↔
        label = .empty ∨ label = .one ∨ label = .twoRow ∨ label = .threeRow) ∧
      (StrictAntiOn (fun position => p.getD position 0) (rectangle p x y) ↔
        label = .empty ∨ label = .one ∨ label = .twoCol ∨ label = .threeCol) := by
  classical
  let increasing := fun label : SevenLabel =>
    label = .empty ∨ label = .one ∨ label = .twoRow ∨ label = .threeRow
  let decreasing := fun label : SevenLabel =>
    label = .empty ∨ label = .one ∨ label = .twoCol ∨ label = .threeCol
  have htable : ∀ southwest northwest southeast northeast : SevenLabel, ∀ entry : Bool,
      sevenInverse northeast northwest southeast = some (southwest, entry) →
      (if entry then increasing northeast ↔ increasing southwest
        else if northwest.size = southwest.size then increasing northeast ↔ increasing southeast
        else if southeast.size = southwest.size then increasing northeast ↔ increasing northwest
        else ¬ increasing northeast) ∧
      (if entry then decreasing northeast ↔ southwest.size = 0
        else if northwest.size = southwest.size then decreasing northeast ↔ decreasing southeast
        else if southeast.size = southwest.size then decreasing northeast ↔ decreasing northwest
        else decreasing northeast ↔ decreasing northwest ∧ decreasing southeast) := by
    intro southwest northwest southeast northeast entry hinverse
    cases northeast <;> cases northwest <;> cases southeast <;>
      simp only [sevenInverse, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hinverse
    all_goals
      obtain ⟨rfl, rfl⟩ := hinverse
      decide
  have hlength : p.length = n := by simpa using hp.length_eq
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hinjective : ∀ first < n, ∀ second < n,
      p.getD first 0 = p.getD second 0 → first = second := by
    intro first hfirst second hsecond heq
    rw [List.getD_eq_getElem p 0 (by omega),
      List.getD_eq_getElem p 0 (by omega)] at heq
    exact hnodup.getElem_inj_iff.mp heq
  have hpositive : ∀ position < n, 0 < p.getD position 0 := by
    intro position hposition
    have hmem := hp.mem_iff.mp (List.getElem_mem (show position < p.length by omega))
    rw [List.mem_range'_1] at hmem
    rw [List.getD_eq_getElem p 0 (by omega)]
    omega
  have hmono : ∀ x y width height, x ≤ width → y ≤ height →
      rectangle p x y ⊆ rectangle p width height := by
    intro x y width height hx hy position hposition
    simp only [rectangle, Finset.mem_filter, Finset.mem_range] at hposition ⊢
    exact ⟨by omega, by omega⟩
  have hzero : ∀ x ≤ n, rectangle p x 0 = ∅ := by
    intro x hx
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro position hposition
    have hpos : position < x ∧ p.getD position 0 ≤ 0 := by
      simpa only [rectangle, Finset.mem_filter, Finset.mem_range] using hposition
    have := hpositive position (by omega)
    omega
  intro x
  induction x with
  | zero =>
    intro hx y hy label hlabel hrank
    simp only [sevenDiagram, Option.some.injEq] at hlabel
    subst label
    simp [rectangle, StrictMonoOn, StrictAntiOn]
  | succ x ihx =>
    intro hx y
    induction y with
    | zero =>
      intro hy label hlabel hrank
      simp only [sevenDiagram, Option.some.injEq] at hlabel
      subst label
      simp [hzero _ hx, StrictMonoOn, StrictAntiOn]
    | succ y ihy =>
      intro hy northeast hne hrank
      let southwestSet := rectangle p x y
      let northwestSet := rectangle p x (y + 1)
      let southeastSet := rectangle p (x + 1) y
      let northeastSet := rectangle p (x + 1) (y + 1)
      change (StrictMonoOn (fun position => p.getD position 0) northeastSet ↔
        increasing northeast) ∧
        (StrictAntiOn (fun position => p.getD position 0) northeastSet ↔
          decreasing northeast)
      have hswsub := hmono x y (x + 1) (y + 1) (by omega) (by omega)
      have hnwsub := hmono x (y + 1) (x + 1) (y + 1) (by omega) (by omega)
      have hsesub := hmono (x + 1) y (x + 1) (y + 1) (by omega) (by omega)
      obtain ⟨southwest, hsw, hswsize, _, _⟩ :=
        seven_state_construction n p hp x (by omega) y (by omega)
          (le_trans (Finset.card_le_card hswsub) hrank)
      obtain ⟨northwest, hnw, hnwsize, _, _⟩ :=
        seven_state_construction n p hp x (by omega) (y + 1) hy
          (le_trans (Finset.card_le_card hnwsub) hrank)
      obtain ⟨southeast, hse, hsesize, _, _⟩ :=
        seven_state_construction n p hp (x + 1) hx y (by omega)
          (le_trans (Finset.card_le_card hsesub) hrank)
      have hswOrder := ihx (by omega) y (by omega) southwest hsw
        (le_trans (Finset.card_le_card hswsub) hrank)
      have hnwOrder := ihx (by omega) (y + 1) hy northwest hnw
        (le_trans (Finset.card_le_card hnwsub) hrank)
      have hseOrder := ihy (by omega) southeast hse
        (le_trans (Finset.card_le_card hsesub) hrank)
      let entry := decide (p.getD x 0 = y + 1)
      have hforward : sevenForward southwest northwest southeast entry = some northeast := by
        rw [sevenDiagram, hsw, hnw, hse] at hne
        exact hne
      have hinverse : sevenInverse northeast northwest southeast =
          some (southwest, entry) := by
        have := List.find?_some hforward
        simpa [sevenForward] using this
      have hlabels := htable southwest northwest southeast northeast entry hinverse
      have hmem : ∀ width height position,
          position ∈ rectangle p width height ↔ position < width ∧
            p.getD position 0 ≤ height := by
        intro width height position
        simp only [rectangle, Finset.mem_filter, Finset.mem_range]
      by_cases hoccupied : p.getD x 0 = y + 1
      · have hentry : entry = true := decide_eq_true hoccupied
        have hset : northeastSet = insert x southwestSet := by
          ext position
          simp only [northeastSet, southwestSet, hmem, Finset.mem_insert]
          constructor
          · rintro ⟨hposition, hvalue⟩
            by_cases heq : position = x
            · exact Or.inl heq
            · have hneq : p.getD position 0 ≠ y + 1 := by
                intro heqValue
                have := hinjective position (by omega) x (by omega)
                  (heqValue.trans hoccupied.symm)
                omega
              exact Or.inr ⟨by omega, by omega⟩
          · rintro (rfl | ⟨hposition, hvalue⟩)
            · exact ⟨by omega, by omega⟩
            · exact ⟨by omega, by omega⟩
        have hinc : StrictMonoOn (fun position => p.getD position 0) northeastSet ↔
            StrictMonoOn (fun position => p.getD position 0) southwestSet := by
          constructor
          · intro horder first hfirst second hsecond hlt
            exact horder (hswsub hfirst) (hswsub hsecond) hlt
          · intro horder first hfirst second hsecond hlt
            change p.getD first 0 < p.getD second 0
            rw [hset] at hfirst hsecond
            rcases Finset.mem_insert.mp hfirst with rfl | hfirst
            · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
              · omega
              · have := (hmem _ _ _).mp hsecond
                omega
            · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
              · have hvalue := ((hmem _ _ _).mp hfirst).2
                omega
              · exact horder hfirst hsecond hlt
        have hdec : StrictAntiOn (fun position => p.getD position 0) northeastSet ↔
            southwestSet.card = 0 := by
          constructor
          · intro horder
            apply Finset.card_eq_zero.mpr
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro position hposition
            have hpos := (hmem x y position).mp hposition
            have hfirst : position ∈ northeastSet := hswsub hposition
            have hlast : x ∈ northeastSet := by rw [hset]; exact Finset.mem_insert_self _ _
            have := horder hfirst hlast hpos.1
            dsimp only at this
            omega
          · intro hcard
            rw [Finset.card_eq_zero.mp hcard] at hset
            intro first hfirst second hsecond hlt
            rw [hset] at hfirst hsecond
            have hfirstEq : first = x := by simpa using hfirst
            have hsecondEq : second = x := by simpa using hsecond
            omega
        simp only [hentry, if_true] at hlabels
        exact ⟨hinc.trans (hswOrder.1.trans hlabels.1.symm),
          hdec.trans ((by rw [← hswsize] : southwestSet.card = 0 ↔ southwest.size = 0)
            |>.trans hlabels.2.symm)⟩
      · have hentry : entry = false := decide_eq_false hoccupied
        have hunion : northeastSet = northwestSet ∪ southeastSet := by
          ext position
          simp only [northeastSet, northwestSet, southeastSet, hmem, Finset.mem_union]
          constructor
          · rintro ⟨hposition, hvalue⟩
            by_cases hleft : position < x
            · exact Or.inl ⟨hleft, hvalue⟩
            · have heq : position = x := by omega
              subst position
              exact Or.inr ⟨hposition, by omega⟩
          · rintro (⟨hposition, hvalue⟩ | ⟨hposition, hvalue⟩)
            · exact ⟨by omega, hvalue⟩
            · exact ⟨hposition, by omega⟩
        have hswNW : southwestSet ⊆ northwestSet := hmono _ _ _ _ (by omega) (by omega)
        have hswSE : southwestSet ⊆ southeastSet := hmono _ _ _ _ (by omega) (by omega)
        by_cases hsameNW : northwest.size = southwest.size
        · have hset : northeastSet = southeastSet := by
            have hequal : southwestSet = northwestSet :=
              Finset.eq_of_subset_of_card_le hswNW (by rw [← hnwsize, ← hswsize, hsameNW])
            rw [hunion, ← hequal]
            exact Finset.union_eq_right.mpr hswSE
          simp only [hentry, hsameNW, if_true] at hlabels
          rw [hset]
          exact ⟨hseOrder.1.trans hlabels.1.symm, hseOrder.2.trans hlabels.2.symm⟩
        by_cases hsameSE : southeast.size = southwest.size
        · have hset : northeastSet = northwestSet := by
            have hequal : southwestSet = southeastSet :=
              Finset.eq_of_subset_of_card_le hswSE (by rw [← hsesize, ← hswsize, hsameSE])
            rw [hunion, ← hequal]
            exact Finset.union_eq_left.mpr hswNW
          simp only [hentry, if_false, hsameNW, hsameSE, if_true] at hlabels
          rw [hset]
          exact ⟨hnwOrder.1.trans hlabels.1.symm, hnwOrder.2.trans hlabels.2.symm⟩
        have hnwLarger : southwestSet.card < northwestSet.card := by
          have := Finset.card_le_card hswNW
          rw [← hswsize, ← hnwsize] at this ⊢
          omega
        have hseLarger : southwestSet.card < southeastSet.card := by
          have := Finset.card_le_card hswSE
          rw [← hswsize, ← hsesize] at this ⊢
          omega
        obtain ⟨top, htopNW, htopNot⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card hnwLarger
        obtain ⟨last, hlastSE, hlastNot⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card hseLarger
        have htop : top < x ∧ p.getD top 0 = y + 1 := by
          have hpos := (hmem x (y + 1) top).mp htopNW
          have hnot := (hmem x y top).not.mp htopNot
          omega
        have hlast : last = x ∧ p.getD x 0 ≤ y := by
          have hpos := (hmem (x + 1) y last).mp hlastSE
          have hnot := (hmem x y last).not.mp hlastNot
          have heq : last = x := by omega
          exact ⟨heq, by simpa only [heq] using hpos.2⟩
        have hinc : ¬ StrictMonoOn (fun position => p.getD position 0) northeastSet := by
          intro horder
          have htopNE : top ∈ northeastSet := hnwsub htopNW
          have hlastNE : x ∈ northeastSet := hsesub (by
            simpa only [hlast.1] using hlastSE)
          have := horder htopNE hlastNE htop.1
          dsimp only at this
          omega
        have hdec : StrictAntiOn (fun position => p.getD position 0) northeastSet ↔
            StrictAntiOn (fun position => p.getD position 0) northwestSet ∧
              StrictAntiOn (fun position => p.getD position 0) southeastSet := by
          constructor
          · intro horder
            exact ⟨fun _ hfirst _ hsecond hlt =>
              horder (hnwsub hfirst) (hnwsub hsecond) hlt,
              fun _ hfirst _ hsecond hlt => horder (hsesub hfirst) (hsesub hsecond) hlt⟩
          · rintro ⟨hnwAnti, hseAnti⟩ first hfirst second hsecond hlt
            change p.getD second 0 < p.getD first 0
            rw [hunion] at hfirst hsecond
            rcases Finset.mem_union.mp hfirst with hfirst | hfirst
            · rcases Finset.mem_union.mp hsecond with hsecond | hsecond
              · exact hnwAnti hfirst hsecond hlt
              · by_cases hsecondNW : second ∈ northwestSet
                · exact hnwAnti hfirst hsecondNW hlt
                · have hsecondPos := (hmem (x + 1) y second).mp hsecond
                  have hsecondNot := (hmem x (y + 1) second).not.mp hsecondNW
                  have hsecondEq : second = x := by omega
                  subst second
                  by_cases hfirstSE : first ∈ southeastSet
                  · exact hseAnti hfirstSE hsecond hlt
                  · have hfirstPos := (hmem x (y + 1) first).mp hfirst
                    have hfirstNot := (hmem (x + 1) y first).not.mp hfirstSE
                    omega
            · rcases Finset.mem_union.mp hsecond with hsecond | hsecond
              · have hsecondPos := (hmem x (y + 1) second).mp hsecond
                have hfirstPos := (hmem (x + 1) y first).mp hfirst
                have hfirstNW : first ∈ northwestSet := (hmem x (y + 1) first).mpr
                  ⟨by omega, by omega⟩
                exact hnwAnti hfirstNW hsecond hlt
              · exact hseAnti hfirst hsecond hlt
        simp only [hentry, if_false, hsameNW, hsameSE] at hlabels
        exact ⟨iff_of_false hinc hlabels.1,
          hdec.trans ((and_congr hnwOrder.2 hseOrder.2).trans hlabels.2.symm)⟩

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21
