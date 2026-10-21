/- GID: D5/S3/Combinatorics/InversionSeq/ClassCInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/ClassCInsertion
   mirror-E: none(waiver:labelled-path-insertion-and-first-old-complements)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Sum]
   utility: none
   digest: Marked prefix insertion partitions actual finite labelled paths. -/

import D5.S3.Combinatorics.InversionSeq.ClassCPaths
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.ClassCInsertion

open ClassCSites ClassCPaths

/-- Prepending keeps the flag, including coherent false-flag words ending in S. -/
def prepend (v : List Site) (q : State) : State :=
  ⟨v ++ q.p, q.s, q.hs, q.h, by
    intro h
    obtain ⟨p, hp⟩ := q.coherent h
    exact ⟨v ++ p, by simp [hp, List.append_assoc]⟩⟩

def shiftOld (v : List Site) (q : State) (i : Fin q.p.length) :
    Fin (prepend v q).p.length :=
  ⟨v.length + i.val, by simp only [prepend, List.length_append]; omega⟩

def markedOld (v : List Site) (q : State) (i : Fin v.length) :
    Fin (prepend v q).p.length :=
  ⟨i.val, by simp only [prepend, List.length_append]; omega⟩

private theorem child_shift (v : List Site) (q : State) (i : Fin q.p.length) :
    child (prepend v q) (.inl (shiftOld v q i)) = child q (.inl i) := by
  have he : (prepend v q).h = true ∧ (shiftOld v q i).val + 1 =
      (prepend v q).p.length ↔ q.h = true ∧ i.val + 1 = q.p.length := by
    change (q.h = true ∧ v.length + i.val + 1 = (v ++ q.p).length) ↔
      (q.h = true ∧ i.val + 1 = q.p.length)
    rw [List.length_append]
    constructor
    · rintro ⟨hh, hi⟩
      exact ⟨hh, by omega⟩
    · rintro ⟨hh, hi⟩
      exact ⟨hh, by omega⟩
  simp only [child, he]
  split
  · rfl
  · apply State.ext
    · simp only [lowerState, prepend, shiftOld]
      rw [show v.length + i.val + 1 = v.length + (i.val + 1) by omega,
        List.drop_length_add_append]
    · rfl
    · rfl

private theorem child_new (v : List Site) (q : State) (j : Fin q.s) :
    child (prepend v q) (.inr j) = prepend v (child q (.inr j)) := by
  apply State.ext
  · simp [child, prepend, List.append_assoc]
  · rfl
  · rfl

/-- The first choice separates marked sites from every unchanged old/new label. -/
def choiceSplit (v : List Site) (q : State) :
    Fin v.length ⊕ StateChoice q ≃ StateChoice (prepend v q) where
  toFun
    | .inl i => .inl (markedOld v q i)
    | .inr (.inl i) => .inl (shiftOld v q i)
    | .inr (.inr j) => .inr j
  invFun
    | .inl i => if hi : i.val < v.length then .inl ⟨i.val, hi⟩
      else .inr (.inl ⟨i.val - v.length, by
        have := i.is_lt
        simp only [prepend, List.length_append] at this
        omega⟩)
    | .inr j => .inr (.inr j)
  left_inv := by
    rintro (i | (i | j))
    · simp [markedOld, i.is_lt]
    · have hi : ¬ v.length + i.val < v.length := by omega
      simp [shiftOld, hi]
    · rfl
  right_inv := by
    rintro (i | j)
    · by_cases hi : i.val < v.length
      · simp only [dif_pos hi]
        rfl
      · simp only [dif_neg hi]
        congr 1
        apply Fin.ext
        change v.length + (i.val - v.length) = i.val
        omega
    · rfl

private def pathStep (r : ℕ) (q : State) : Path (r + 1) q ≃
    ((i : Fin q.p.length) × Path r (child q (.inl i))) ⊕
      ((j : Fin q.s) × Path r (child q (.inr j))) :=
  Equiv.sumSigmaDistrib _

/-- At stop, choose a marked old site and retain an arbitrary actual tail.
At next, retain the exact new label and continue the first-old search. -/
def Outside (v : List Site) : ℕ → State → Type
  | 0, _ => Empty
  | r + 1, q =>
    ((i : Fin v.length) × Path r (child (prepend v q) (.inl (markedOld v q i)))) ⊕
      ((j : Fin q.s) × Outside v r (child q (.inr j)))

instance outside_finite (v : List Site) (r : ℕ) (q : State) :
    Finite (Outside v r q) := by
  induction r generalizing q with
  | zero => change Finite Empty; infer_instance
  | succ r ih =>
    change Finite (((i : Fin v.length) ×
      Path r (child (prepend v q) (.inl (markedOld v q i)))) ⊕
      ((j : Fin q.s) × Outside v r (child q (.inr j))))
    letI : ∀ j : Fin q.s, Finite (Outside v r (child q (.inr j))) := fun j => ih _
    letI : ∀ i : Fin v.length, Fintype
        (Path r (child (prepend v q) (.inl (markedOld v q i)))) :=
      fun _ => Fintype.ofFinite _
    letI : ∀ j : Fin q.s, Fintype (Outside v r (child q (.inr j))) :=
      fun _ => Fintype.ofFinite _
    exact Finite.of_fintype _

private def expandedTail (v : List Site) (r : ℕ) (q : State) :
    Fin v.length ⊕ StateChoice q → Type
  | .inl i => Path r (child (prepend v q) (.inl (markedOld v q i)))
  | .inr (.inl i) => Path r (child q (.inl i))
  | .inr (.inr j) => Path r (prepend v (child q (.inr j)))

private def expandedEquiv (v : List Site) (r : ℕ) (q : State) :
    ((d : Fin v.length ⊕ StateChoice q) × expandedTail v r q d) ≃
      Path (r + 1) (prepend v q) :=
  Equiv.sigmaCongr (choiceSplit v q) fun d => by
    rcases d with i | (i | j)
    · exact Equiv.refl _
    · exact Equiv.cast (congrArg (Path r) (child_shift v q i).symm)
    · exact Equiv.cast (congrArg (Path r) (child_new v q j).symm)

private def insertionStep (v : List Site) (r : ℕ) (q : State) :
    Path (r + 1) (prepend v q) ≃
      ((i : Fin v.length) × Path r (child (prepend v q) (.inl (markedOld v q i)))) ⊕
        (((i : Fin q.p.length) × Path r (child q (.inl i))) ⊕
          ((j : Fin q.s) × Path r (prepend v (child q (.inr j))))) :=
  (expandedEquiv v r q).symm.trans
    ((Equiv.sumSigmaDistrib _).trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.sumSigmaDistrib _)))

private def shuffle (M O N X : Type) :
    M ⊕ (O ⊕ (N ⊕ X)) ≃ (O ⊕ N) ⊕ (M ⊕ X) where
  toFun
    | .inl m => .inr (.inl m)
    | .inr (.inl o) => .inl (.inl o)
    | .inr (.inr (.inl n)) => .inl (.inr n)
    | .inr (.inr (.inr x)) => .inr (.inr x)
  invFun
    | .inl (.inl o) => .inr (.inl o)
    | .inl (.inr n) => .inr (.inr (.inl n))
    | .inr (.inl m) => .inl m
    | .inr (.inr x) => .inr (.inr (.inr x))
  left_inv := by rintro (m | (o | (n | x))) <;> rfl
  right_inv := by rintro ((o | n) | (m | x)) <;> rfl

/-- Explicit first-old decoder and reconstruction. Old source positions are shifted;
new labels recurse. A first marked old choice stops and retains the whole tail. -/
def splitInserted (v : List Site) (r : ℕ) (q : State) :
    Path r (prepend v q) ≃ Path r q ⊕ Outside v r q := by
  induction r generalizing q with
  | zero =>
    exact {
      toFun := fun _ => .inl ()
      invFun := fun x => match x with
        | .inl _ => ()
        | .inr e => nomatch e
      left_inv := by rintro ⟨⟩; rfl
      right_inv := by rintro (⟨⟩ | e); rfl; exact nomatch e }
  | succ r ih =>
    let en : ((j : Fin q.s) × Path r (prepend v (child q (.inr j)))) ≃
        ((j : Fin q.s) × Path r (child q (.inr j))) ⊕
          ((j : Fin q.s) × Outside v r (child q (.inr j))) :=
      (Equiv.sigmaCongrRight fun j => ih (child q (.inr j))).trans
        (Equiv.sigmaSumDistrib _ _)
    exact (insertionStep v r q).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) en)).trans
        ((shuffle _ _ _ _).trans
          (Equiv.sumCongr (pathStep r q).symm (Equiv.refl _))))

/-- The actual insertion map is the inverse decoder's source branch. -/
def insertPath (v : List Site) (r : ℕ) (q : State) (x : Path r q) :
    Path r (prepend v q) := (splitInserted v r q).symm (.inl x)

private theorem insertPath_injective (v : List Site) (r : ℕ) (q : State) :
    Function.Injective (insertPath v r q) :=
  (splitInserted v r q).symm.injective.comp Sum.inl_injective

private def rightComplement {A B C : Type} (e : C ≃ A ⊕ B) :
    {c : C // ¬ ∃ x : A, e.symm (.inl x) = c} ≃ B where
  toFun c := match h : e c.val with
    | .inl x => False.elim (c.property ⟨x, by
        apply e.injective
        simpa using h.symm⟩)
    | .inr y => y
  invFun y := ⟨e.symm (.inr y), by
    rintro ⟨x, hx⟩
    have := congrArg e hx
    simpa using this⟩
  left_inv := by
    intro c
    apply Subtype.ext
    dsimp
    split
    · rename_i x hx
      exact False.elim (c.property ⟨x, by apply e.injective; simpa using hx.symm⟩)
    · rename_i y hy
      apply e.injective
      simpa using hy.symm
  right_inv := by
    intro y
    dsimp only
    split
    · rename_i x hx
      have he : Sum.inr y = Sum.inl x :=
        (e.apply_symm_apply (Sum.inr y)).symm.trans hx
      cases he
    · rename_i z hz
      exact (Sum.inr.inj ((e.apply_symm_apply (Sum.inr y)).symm.trans hz)).symm

/-- This identifies the genuine finite complement, rather than defining a difference. -/
def insertionComplement (v : List Site) (r : ℕ) (q : State) :
    {y : Path r (prepend v q) // ¬ ∃ x : Path r q, insertPath v r q x = y} ≃
      Outside v r q := rightComplement (splitInserted v r q)

/-- Counting the explicit partition gives an exact natural sum. -/
private theorem insertion_card (v : List Site) (r : ℕ) (q : State) :
    phi r (prepend v q) = phi r q + Nat.card (Outside v r q) := by
  exact (Nat.card_congr (splitInserted v r q)).trans Nat.card_sum

/-- The unused-site injection retains every old position and every new label. -/
def unusedInjection (r s k : ℕ) (hs : 1 ≤ s) :
    Path r (lowerState k s hs) ↪ Path r (lowerState (k + 1) s hs) where
  toFun := insertPath [.U] r (lowerState k s hs)
  inj' := insertPath_injective [.U] r (lowerState k s hs)

private def emptyNewStep (r s : ℕ) (hs : 1 ≤ s) :
    Path (r + 1) (lowerState 0 s hs) ≃
      ((j : Fin s) × Path r (child (lowerState 0 s hs) (.inr j))) := by
  letI : IsEmpty (Fin (lowerState 0 s hs).p.length) := by
    change IsEmpty (Fin 0)
    infer_instance
  exact (pathStep r (lowerState 0 s hs)).trans (Equiv.emptySum _ _)

private theorem repeat_new (s : ℕ) (hs : 1 ≤ s) (j : Fin s) :
    child (repeatState s hs) (.inr j) =
      prepend [.S] (child (lowerState 0 s hs) (.inr j)) := by
  apply State.ext <;> simp [child, prepend, repeatState, lowerState, List.append_assoc]

private def repeatStep (r s : ℕ) (hs : 1 ≤ s) :
    Path (r + 1) (repeatState s hs) ≃
      Path r (repeatState (s + 1) (by omega)) ⊕
        ((j : Fin s) × Path r (prepend [.S] (child (lowerState 0 s hs) (.inr j)))) :=
  by
  letI : Unique (Fin (repeatState s hs).p.length) := by
    change Unique (Fin 1)
    infer_instance
  exact
  (pathStep r (repeatState s hs)).trans (Equiv.sumCongr
    ((Equiv.uniqueSigma _).trans (Equiv.cast (by
      congr 1)))
    (Equiv.sigmaCongrRight fun j =>
      Equiv.cast (congrArg (Path r) (repeat_new s hs j))))

/-- Empty-to-S has a distinct immediate repeat branch. Every later stop is
after at least one new label, and uses the generic marked-S complement. -/
def EmptyOutside : ℕ → (s : ℕ) → 1 ≤ s → Type
  | 0, _, _ => Empty
  | r + 1, s, hs => Path r (repeatState (s + 1) (by omega)) ⊕
      ((j : Fin s) × Outside [.S] r (child (lowerState 0 s hs) (.inr j)))

instance emptyOutside_finite (r s : ℕ) (hs : 1 ≤ s) : Finite (EmptyOutside r s hs) := by
  cases r with
  | zero => change Finite Empty; infer_instance
  | succ r =>
    change Finite (Path r (repeatState (s + 1) _) ⊕
      ((j : Fin s) × Outside [.S] r (child (lowerState 0 s hs) (.inr j))))
    letI : Fintype (Path r (repeatState (s + 1) (by omega))) := Fintype.ofFinite _
    letI : ∀ j : Fin s, Fintype (Outside [.S] r (child (lowerState 0 s hs) (.inr j))) :=
      fun _ => Fintype.ofFinite _
    exact Finite.of_fintype _

private def rotate (M N X : Type) : M ⊕ (N ⊕ X) ≃ N ⊕ (M ⊕ X) where
  toFun
    | .inl m => .inr (.inl m)
    | .inr (.inl n) => .inl n
    | .inr (.inr x) => .inr (.inr x)
  invFun
    | .inl n => .inr (.inl n)
    | .inr (.inl m) => .inl m
    | .inr (.inr x) => .inr (.inr x)
  left_inv := by rintro (m | (n | x)) <;> rfl
  right_inv := by rintro (n | (m | x)) <;> rfl

/-- Special initial-step decoder correctly changes the initial flag to true. -/
def splitEmpty (r s : ℕ) (hs : 1 ≤ s) :
    Path r (repeatState s hs) ≃ Path r (lowerState 0 s hs) ⊕ EmptyOutside r s hs := by
  cases r with
  | zero =>
    exact {
      toFun := fun _ => .inl ()
      invFun := fun x => match x with
        | .inl _ => ()
        | .inr e => nomatch e
      left_inv := by rintro ⟨⟩; rfl
      right_inv := by rintro (⟨⟩ | e); rfl; exact nomatch e }
  | succ r =>
    let en := (Equiv.sigmaCongrRight fun j : Fin s =>
      splitInserted [.S] r (child (lowerState 0 s hs) (.inr j))).trans
        (Equiv.sigmaSumDistrib _ _)
    exact (repeatStep r s hs).trans
      ((Equiv.sumCongr (Equiv.refl _) en).trans
        ((rotate _ _ _).trans (Equiv.sumCongr (emptyNewStep r s hs).symm (Equiv.refl _))))

def emptyInjection (r s : ℕ) (hs : 1 ≤ s) :
    Path r (lowerState 0 s hs) ↪ Path r (repeatState s hs) where
  toFun x := (splitEmpty r s hs).symm (.inl x)
  inj' := (splitEmpty r s hs).symm.injective.comp Sum.inl_injective

def emptyComplement (r s : ℕ) (hs : 1 ≤ s) :
    {y : Path r (repeatState s hs) //
      ¬ ∃ x : Path r (lowerState 0 s hs), emptyInjection r s hs x = y} ≃
        EmptyOutside r s hs := rightComplement (splitEmpty r s hs)

/-- A legal initial-new history ending at its first marked old choice.
Each next constructor retains its Fin label and adds that label to k.
The stop branch retains an arbitrary Path tail in the exact lower state. -/
def LowerComplement : ℕ → (s k : ℕ) → 1 ≤ s → Type
  | 0, _, _, _ => Empty
  | r + 1, s, k, hs => Path r (lowerState k (s + 1) (by omega)) ⊕
      ((j : Fin s) × LowerComplement r (s - j.val) (k + j.val)
        (by have := j.is_lt; omega))

private theorem marked_child (x : Site) (q : State) (i : Fin ([x] : List Site).length) :
    child (prepend [x] q) (.inl (markedOld [x] q i)) =
      lowerState (q.p.count .U) (q.s + 1) (by omega) := by
  have hi : i.val = 0 := by
    have := i.is_lt
    simp only [List.length_singleton] at this
    omega
  have hn : ¬ ((prepend [x] q).h = true ∧
      (markedOld [x] q i).val + 1 = (prepend [x] q).p.length) := by
    change ¬ (q.h = true ∧ i.val + 1 = ([x] ++ q.p).length)
    rintro ⟨hh, hl⟩
    obtain ⟨p, hp⟩ := q.coherent hh
    simp [hi, hp] at hl
  simp only [child, if_neg hn]
  simp [prepend, markedOld, hi]

private theorem new_unused (q : State) (j : Fin q.s) :
    (child q (.inr j)).p.count .U = q.p.count .U + j.val := by
  simp [child, List.count_append]

/-- Full history decoding computes its terminal slack and suffix-U multiplicity.
All histories with the same sum still occupy separate dependent sum branches. -/
def outsideLowerEquiv (x : Site) (r : ℕ) (q : State) :
    Outside [x] r q ≃ LowerComplement r q.s (q.p.count .U) q.hs := by
  induction r generalizing q with
  | zero => exact Equiv.refl _
  | succ r ih =>
    letI : Unique (Fin ([x] : List Site).length) := by
      change Unique (Fin 1)
      infer_instance
    let stop : ((i : Fin ([x] : List Site).length) ×
        Path r (child (prepend [x] q) (.inl (markedOld [x] q i)))) ≃
          Path r (lowerState (q.p.count .U) (q.s + 1) (by omega)) :=
      (Equiv.sigmaCongrRight fun i =>
        Equiv.cast (congrArg (Path r) (marked_child x q i))).trans (Equiv.uniqueSigma _)
    exact Equiv.sumCongr stop (Equiv.sigmaCongrRight fun j =>
      (ih (child q (.inr j))).trans (Equiv.cast (by
        change LowerComplement r (q.s - j.val) ((child q (.inr j)).p.count .U) _ = _
        rw [new_unused])))

instance lowerComplement_finite (r s k : ℕ) (hs : 1 ≤ s) :
    Finite (LowerComplement r s k hs) := by
  have hc : (lowerState k s hs).p.count .U = k := by simp [lowerState]
  exact Finite.of_equiv (Outside [.U] r (lowerState k s hs))
    ((outsideLowerEquiv .U r (lowerState k s hs)).trans (Equiv.cast (by rw [hc]; rfl)))

/-- Exactly the marked-U complement, in its legal labelled history form. -/
def unusedComplementDecoded (r s k : ℕ) (hs : 1 ≤ s) :
    {y : Path r (lowerState (k + 1) s hs) //
      ¬ ∃ x : Path r (lowerState k s hs), unusedInjection r s k hs x = y} ≃
        LowerComplement r s k hs :=
  (insertionComplement [.U] r (lowerState k s hs)).trans
    ((outsideLowerEquiv .U r (lowerState k s hs)).trans
      (Equiv.cast (by simp [lowerState])))

/-- Immediate repeat, or at least one initial new label followed by a lower stop.
This is the exact changed-flag complement with arbitrary native Path tails. -/
def RepeatComplement : ℕ → (s : ℕ) → 1 ≤ s → Type
  | 0, _, _ => Empty
  | r + 1, s, hs => Path r (repeatState (s + 1) (by omega)) ⊕
      ((j : Fin s) × LowerComplement r (s - j.val) j.val
        (by have := j.is_lt; omega))

private def emptyOutsideDecoded (r s : ℕ) (hs : 1 ≤ s) :
    EmptyOutside r s hs ≃ RepeatComplement r s hs := by
  cases r with
  | zero => exact Equiv.refl _
  | succ r =>
    exact Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight fun j =>
      (outsideLowerEquiv .S r (child (lowerState 0 s hs) (.inr j))).trans
        (Equiv.cast (by simp [new_unused, lowerState, child, List.count_append])))

instance repeatComplement_finite (r s : ℕ) (hs : 1 ≤ s) :
    Finite (RepeatComplement r s hs) :=
  Finite.of_equiv (EmptyOutside r s hs) (emptyOutsideDecoded r s hs)

def emptyComplementDecoded (r s : ℕ) (hs : 1 ≤ s) :
    {y : Path r (repeatState s hs) //
      ¬ ∃ x : Path r (lowerState 0 s hs), emptyInjection r s hs x = y} ≃
        RepeatComplement r s hs :=
  (emptyComplement r s hs).trans (emptyOutsideDecoded r s hs)

/-- The natural difference is exactly the decoded first-marked-U complement. -/
theorem unused_difference (r s k : ℕ) (hs : 1 ≤ s) :
    phi r (lowerState k s hs) ≤ phi r (lowerState (k + 1) s hs) ∧
      phi r (lowerState (k + 1) s hs) - phi r (lowerState k s hs) =
        Nat.card (LowerComplement r s k hs) := by
  have h := insertion_card [.U] r (lowerState k s hs)
  change phi r (lowerState (k + 1) s hs) = _ at h
  have he : Nat.card (Outside [.U] r (lowerState k s hs)) =
      Nat.card (LowerComplement r s k hs) := by
    simpa [lowerState] using Nat.card_congr (outsideLowerEquiv .U r (lowerState k s hs))
  rw [he] at h
  omega

/-- The natural empty-to-repeat difference has the changed-flag finite complement. -/
theorem empty_difference (r s : ℕ) (hs : 1 ≤ s) :
    phi r (lowerState 0 s hs) ≤ b r s hs ∧
      b r s hs - phi r (lowerState 0 s hs) = Nat.card (RepeatComplement r s hs) := by
  have h := (Nat.card_congr (splitEmpty r s hs)).trans Nat.card_sum
  change b r s hs = phi r (lowerState 0 s hs) + Nat.card (EmptyOutside r s hs) at h
  rw [Nat.card_congr (emptyOutsideDecoded r s hs)] at h
  omega

end D5.S3.Combinatorics.InversionSeq.ClassCInsertion
