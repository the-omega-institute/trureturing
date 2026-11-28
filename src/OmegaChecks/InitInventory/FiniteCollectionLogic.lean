module
public import Lean

public section

namespace OmegaChecks.InitBoundaries
universe u

namespace FiniteMembership

/-- Any two elements of a type have either equal or unequal values. -/
def EqualityCases : Prop := ∀ {α : Type u} (a b : α), a = b ∨ a ≠ b

theorem ofListMember (branch : type_of% (@List.eq_or_ne_mem_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  exact (branch (a := a) (b := b) (l := [a]) (.tail _ (.head _))).imp_right And.left

theorem ofArrayMember (branch : type_of% (@Array.eq_or_ne_mem_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  have mem : a ∈ (#[a].push b) := ⟨.head _⟩
  exact (branch mem).imp_right And.left

theorem ofFirstListMember (split : type_of% (@List.eq_append_cons_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  obtain ⟨before, after, eq, absent⟩ := split (a := a) (xs := [b,a]) (.tail _ (.head _))
  cases before with
  | nil => exact .inl (List.cons.inj eq).1.symm
  | cons c cs =>
    have same := (List.cons.inj eq).1
    exact .inr fun e => absent ((e.trans same) ▸ List.Mem.head _)

/-- Appending cannot change the first entry of a nonempty array. -/
private theorem pushKeepsHead {α : Type u} {acc : Array α} {a v : α}
    (h : acc.toList.head? = some v) : (acc.push a).toList.head? = some v := by
  cases acc with
  | mk l => cases l with
    | nil => cases h
    | cons c cs => exact h

private theorem appendKeepsHead {α : Type u} {xs ys : Array α} {v : α}
    (h : xs.toList.head? = some v) : (xs ++ ys).toList.head? = some v := by
  have loop (fuel j : Nat) (acc : Array α) (head : acc.toList.head? = some v) :
      (Array.foldlM.loop (m := Id) (fun a x => pure (a.push x)) ys ys.size
        (Nat.le_refl _) fuel j acc).run.toList.head? = some v := by
    induction fuel generalizing j acc with
    | zero =>
      unfold Array.foldlM.loop
      split <;> exact head
    | succ fuel ih =>
      unfold Array.foldlM.loop
      split
      · exact ih (j+1) _ (pushKeepsHead head)
      · exact head
  change (Array.foldl (fun a x => a.push x) xs ys).toList.head? = some v
  unfold Array.foldl Array.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  exact loop ys.size 0 xs h

theorem ofFirstArrayMember (split : type_of% (@Array.eq_push_append_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  have mem : a ∈ #[b,a] := ⟨.tail _ (.head _)⟩
  obtain ⟨⟨before⟩, after, eq, absent⟩ := split mem
  have eqHead := congrArg (fun xs => xs.toList.head?) eq
  cases before with
  | nil => exact .inl (Option.some.inj (eqHead.trans (appendKeepsHead rfl))).symm
  | cons c cs =>
    have same : b = c := Option.some.inj (eqHead.trans (appendKeepsHead (pushKeepsHead rfl)))
    exact .inr fun e => absent ⟨(e.trans same) ▸ List.Mem.head _⟩

theorem ofRunDecomposition (split : type_of% (@List.eq_replicate_or_eq_replicate_append_cons.{u})) :
    EqualityCases.{u} := by
  intro α a b
  rcases split [a, b] with emp | ⟨n, c, eq, positive⟩ | ⟨n, c, d, rest, eq, positive, apart⟩
  · cases emp
  · cases n with
    | zero => cases positive
    | succ n => cases n with
      | zero => cases eq
      | succ n =>
        have heads := List.cons.inj eq
        exact .inl (heads.1.trans (List.cons.inj heads.2).1.symm)
  · cases n with
    | zero => cases positive
    | succ n => cases n with
      | zero =>
        have heads := List.cons.inj eq
        exact .inr fun h => apart (heads.1.symm.trans (h.trans (List.cons.inj heads.2).1))
      | succ n =>
        have heads := List.cons.inj eq
        exact .inl (heads.1.trans (List.cons.inj heads.2).1.symm)

theorem ofRunInduction (rec : type_of% (@List.replicateRecOn.{u})) : EqualityCases.{u} := by
  apply ofRunDecomposition
  intro α l
  apply rec l
  · exact .inl rfl
  · intro a n h
    exact .inr (.inl ⟨n, a, rfl, h⟩)
  · intro a b n l ne pos _
    exact .inr (.inr ⟨n, a, b, l, rfl, pos, ne⟩)

/-- A comparison of two elements suffices to split at the first occurrence. -/
theorem firstListMemberOfEqualityCases {α : Type u} (casesEq : ∀ a b : α, a = b ∨ a ≠ b) :
    type_of% (@List.eq_append_cons_of_mem α) := by
  intro a xs mem
  induction mem with
  | head xs => exact ⟨[], xs, rfl, List.not_mem_nil⟩
  | tail b mem ih =>
    cases casesEq a b with
    | inl eq => cases eq; exact ⟨[], _, rfl, List.not_mem_nil⟩
    | inr ne =>
      obtain ⟨before, after, eq, absent⟩ := ih
      refine ⟨b :: before, after, congrArg (b :: ·) eq, ?_⟩
      intro h
      cases h with
      | head => exact ne rfl
      | tail _ inside => exact absent inside

/-- Extending a nonempty run only requires comparing its first entry with the new head. -/
theorem runDecompositionOfEqualityCases {α : Type u} (casesEq : ∀ a b : α, a = b ∨ a ≠ b) :
    type_of% (@List.eq_replicate_or_eq_replicate_append_cons α) := by
  intro l
  induction l with
  | nil => exact .inl rfl
  | cons a l ih =>
    apply Or.inr
    rcases ih with rfl | ⟨n, b, rfl, pos⟩ | ⟨n, b, c, rest, rfl, pos, ne⟩
    · exact .inl ⟨1, a, rfl, Nat.zero_lt_succ _⟩
    · cases n with
      | zero => exact False.elim (Nat.lt_irrefl 0 pos)
      | succ n =>
        rcases casesEq a b with rfl | ne
        · exact .inl ⟨n+2, a, rfl, Nat.zero_lt_succ _⟩
        · exact .inr ⟨1, a, b, List.replicate n b, rfl, Nat.zero_lt_succ _, ne⟩
    · cases n with
      | zero => exact False.elim (Nat.lt_irrefl 0 pos)
      | succ n =>
        rcases casesEq a b with rfl | ne'
        · exact .inr ⟨n+2, a, c, rest, rfl, Nat.zero_lt_succ _, ne⟩
        · exact .inr ⟨1, a, b, List.replicate n b ++ c :: rest, rfl, Nat.zero_lt_succ _, ne'⟩

/-- Removing the first nonempty run strictly decreases the length. -/
theorem runInductionOfDecomposition {α : Type u}
    (split : type_of% (@List.eq_replicate_or_eq_replicate_append_cons α)) :
    type_of% (@List.replicateRecOn α) := by
  intro p l base repeated step
  have longer (n : Nat) (a : α) (rest : List α) :
      rest.length ≤ (List.replicate n a ++ rest).length := by
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih => exact Nat.le_succ_of_le ih
  suffices all : ∀ (bound : Nat) (xs : List α), xs.length < bound → p xs from all _ l (Nat.lt_succ_self _)
  intro bound
  induction bound with
  | zero => exact fun _ small => False.elim (Nat.not_lt_zero _ small)
  | succ bound ih =>
    intro xs small
    rcases split xs with rfl | ⟨n, a, rfl, pos⟩ | ⟨n, a, b, rest, rfl, pos, ne⟩
    · exact base
    · exact repeated a n pos
    · apply step a b n rest ne pos
      apply ih
      cases n with
      | zero => exact False.elim (Nat.lt_irrefl 0 pos)
      | succ n =>
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (longer n a (b :: rest))) (Nat.le_of_lt_succ small)

theorem firstListMemberIffEqualityCases : (type_of% @List.eq_append_cons_of_mem.{u}) ↔ EqualityCases.{u} :=
  ⟨ofFirstListMember, fun h {α} => @firstListMemberOfEqualityCases α h⟩

theorem runDecompositionIffEqualityCases :
    (type_of% @List.eq_replicate_or_eq_replicate_append_cons.{u}) ↔ EqualityCases.{u} :=
  ⟨ofRunDecomposition, fun h {α} => @runDecompositionOfEqualityCases α h⟩

theorem runInductionIffEqualityCases : (type_of% @List.replicateRecOn.{u}) ↔ EqualityCases.{u} :=
  ⟨ofRunInduction, fun h {α} => @runInductionOfDecomposition α (runDecompositionOfEqualityCases h)⟩

/-- Equality of vector values ignores their length proof. These kernels build the same
array data with length proofs that replay without axioms. -/
theorem sizeAfterPush {α : Type u} (xs : Array α) (v : α) :
    (xs.push v).size = xs.size + 1 := by
  cases xs with
  | mk xs =>
    change (xs.concat v).length = xs.length + 1
    induction xs with
    | nil => rfl
    | cons x xs ih => exact congrArg Nat.succ ih

@[expose] def pushed {α : Type u} {n} (xs : Vector α n) (v : α) : Vector α (n+1) :=
  ⟨xs.toArray.push v, (sizeAfterPush xs.toArray v).trans (congrArg Nat.succ xs.size_toArray)⟩

theorem ofVectorMember (branch : ∀ {α : Type u} {n} {a b : α} {xs : Vector α n},
    a ∈ pushed xs b → a = b ∨ (a ≠ b ∧ a ∈ xs)) :
    EqualityCases.{u} := by
  intro α a b
  have h : a ∈ pushed #[a].toVector b := ⟨⟨.head _⟩⟩
  exact (branch h).imp_right And.left

example (branch : type_of% (@Vector.eq_or_ne_mem_of_mem.{u})) : EqualityCases.{u} :=
  ofVectorMember (@branch)

theorem sizeAfterAppend {α : Type u} (xs ys : Array α) : (xs ++ ys).size = xs.size + ys.size := by
  have loop (fuel i : Nat) (st : Array α) (eqn : i + fuel = ys.size) :
      (Array.foldlM.loop (m := Id) (fun as x => pure (as.push x)) ys ys.size (Nat.le_refl _)
        fuel i st).run.size = st.size + fuel := by
    induction fuel generalizing i st with
    | zero =>
      have n : ¬ i < ys.size := (eqn ▸ Nat.lt_irrefl i)
      unfold Array.foldlM.loop
      rw [dite_eq_right n]
      rfl
    | succ fuel ih =>
      have hi : i < ys.size := eqn ▸ (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.succ_le_succ (Nat.le_add_right i fuel)))
      unfold Array.foldlM.loop
      rw [dite_eq_left hi]
      exact (ih (i+1) (st.push ys[i]) ((Nat.succ_add i fuel).trans eqn)).trans
        ((congrArg (· + fuel) (sizeAfterPush st ys[i])).trans (Nat.succ_add st.size fuel))
  change (Array.foldl (fun st x => st.push x) xs ys).size = _
  unfold Array.foldl Array.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  exact loop ys.size 0 xs (Nat.zero_add _)

@[expose] def appended {α : Type u} {n m} (xs : Vector α n) (ys : Vector α m) : Vector α (n+m) :=
  ⟨xs.toArray ++ ys.toArray, (sizeAfterAppend ..).trans ((congrArg (· + ys.toArray.size) xs.size_toArray).trans (congrArg (n + ·) ys.size_toArray))⟩

@[expose] def casted {α : Type u} {n m} (h : n = m) (xs : Vector α n) : Vector α m :=
  ⟨xs.toArray, xs.size_toArray.trans h⟩

theorem ofFirstVectorMember (split : ∀ {α : Type u} {n} {xs : Vector α n} {x : α} (_ : x ∈ xs),
      ∃ (i j : Nat) (pre : Vector α i) (post : Vector α j) (h : i + 1 + j = n),
        xs = casted h (appended (pushed pre x) post) ∧ x ∉ pre) :
    EqualityCases.{u} := by
  apply ofFirstArrayMember
  intro α xs x mem
  obtain ⟨_, _, pre, post, h, shape, absent⟩ := split (xs := xs.toVector) ⟨mem⟩
  exact ⟨pre.toArray, post.toArray, congrArg Vector.toArray shape, fun h => absent ⟨h⟩⟩

example (split : type_of% (@Vector.eq_push_append_of_mem.{u})) : EqualityCases.{u} :=
  ofFirstVectorMember (@split)

end FiniteMembership

namespace VectorExistence

private theorem appendOne (l : List α) (x : α) : (l.concat x).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a tail ih => exact congrArg Nat.succ ih
private def push (xs : Vector α n) (x : α) : Vector α (n+1) :=
  ⟨xs.toArray.push x, (appendOne xs.toArray.toList x).trans (congrArg Nat.succ xs.size_toArray)⟩
/-- The size proof in the official push operation is irrelevant to definitional equality. -/
def DecideSucc : Type 1 := ∀ {α : Type} {n : Nat} (P : Vector α (n+1) → Prop),
  [Decidable (∀ (x : α) (xs : Vector α n), ¬ P (push xs x))] → Decidable (∃ xs, P xs)
example : (type_of% (@Vector.instDecidableExistsVectorSucc.{0})) = DecideSucc := rfl
theorem emOfVectorSucc (existsDec : DecideSucc) (p : Prop) : p ∨ ¬p := by
  let goal := p ∨ ¬p
  have nn : ¬¬goal := fun ng => ng (.inr fun hp => ng (.inl hp))
  let reject : Decidable (∀ (_ : Unit) (_ : Vector Unit 0), ¬goal) :=
    .isFalse fun h => nn (h () ⟨#[], rfl⟩)
  cases @existsDec Unit 0 (fun _ => goal) reject with
  | isTrue yes => exact yes.elim fun _ hp => hp
  | isFalse no => exact (nn (fun hp => no ⟨⟨#[()], rfl⟩, hp⟩)).elim

private theorem endOfNonempty {α : Type u} (a : α) (as : List α) :
    ∃ (p : List α) (z : α), a :: as = p.concat z := by
  induction as generalizing a with
  | nil => exact ⟨[], a, rfl⟩
  | cons b bs ih =>
    obtain ⟨p,z,h⟩ := ih b
    exact ⟨a :: p, z, congrArg (a :: ·) h⟩

private theorem decompose {α : Type u} {n : Nat} (v : Vector α (n+1)) :
    ∃ (xs : Vector α n) (x : α), v = push xs x := by
  rcases v with ⟨⟨as⟩, size⟩
  cases as with
  | nil => exact (Nat.noConfusion size)
  | cons a as =>
    obtain ⟨p, z, eq⟩ := endOfNonempty a as
    have length : p.length = n := Nat.succ.inj (((appendOne p z).symm.trans
      (congrArg List.length eq.symm)).trans size)
    refine ⟨⟨⟨p⟩, length⟩, z, ?_⟩
    have same {a b : Vector α (n+1)} (sameList : a.toArray.toList = b.toArray.toList) : a = b := by
      rcases a with ⟨⟨xs⟩, size⟩
      rcases b with ⟨⟨ys⟩, size'⟩
      change xs = ys at sameList
      cases sameList
      rfl
    exact same eq

/-- The official decision of universal absence is enough once excluded middle is supplied. -/
noncomputable def ofExcludedMiddle (em : ∀ p : Prop, p ∨ ¬p) : DecideSucc := fun {α n} P d => by
  cases d with
  | isTrue absent =>
    exact .isFalse fun ⟨v, h⟩ => (decompose v).elim fun xs h' => h'.elim fun x eq => absent x xs (eq ▸ h)
  | isFalse possible =>
    exact .isTrue ((em (∃ v, P v)).elim id fun no =>
      (possible fun x xs h => no ⟨push xs x, h⟩).elim)


theorem nonemptyDeciderIffExcludedMiddle :
    Nonempty DecideSucc ↔ ∀ p : Prop, p ∨ ¬p :=
  ⟨fun decider => decider.elim emOfVectorSucc, fun em => ⟨ofExcludedMiddle em⟩⟩

end VectorExistence

end OmegaChecks.InitBoundaries
