/- GID: D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Parking/BackgammonMotzkinPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted and signed Motzkin formulas for increasing-prefix backgammon outcomes. -/

import D5.S3.Combinatorics.Parking.BackgammonReverseWeights

/- The four-slot registration audit is unfinished. See https://github.com/the-omega-institute/trureturing/issues/35186. -/

namespace BackgammonMotzkinPaths

open BackgammonIncreasingPrefix

inductive Step
  | horizontal | up | down

private def Step.next : Step → Nat → Option Nat
  | .horizontal, h => some h
  | .up, h => some (h + 1)
  | .down, 0 => none
  | .down, h + 1 => some h

/-- Read a literal Motzkin step word. A down-step below zero fails. A successful
read reports the final height and the number of steps landing at height zero. -/
def trace : List Step → Nat → Option (Nat × Nat)
  | [], h => some (h, 0)
  | step :: rest, h => do
    let next ← step.next h
    let (finish, visits) ← trace rest next
    return (finish, (if next = 0 then 1 else 0) + visits)

private theorem trace_append (left right : List Step) (h mid visits : Nat)
    (start : trace left h = some (mid, visits)) (finish visits' : Nat)
    (stop : trace right mid = some (finish, visits')) :
    trace (left ++ right) h = some (finish, visits + visits') := by
  induction left generalizing h visits with
  | nil => simp [trace] at start; obtain ⟨rfl, rfl⟩ := start; simpa using stop
  | cons step rest ih =>
    cases hn : step.next h with
    | none => simp [trace, hn] at start
    | some next =>
      cases ht : trace rest next with
      | none => simp [trace, hn, ht] at start
      | some result =>
        obtain ⟨m, v⟩ := result
        simp [trace, hn, ht] at start
        obtain ⟨rfl, rfl⟩ := start
        simp [trace, hn, ih next v ht, Nat.add_assoc]

private theorem trace_raise (word : List Step) (h finish visits : Nat)
    (ok : trace word h = some (finish, visits)) :
    trace word (h + 1) = some (finish + 1, 0) := by
  induction word generalizing h visits with
  | nil => simp [trace] at ok; exact congrArg (fun n => some (n + 1, 0)) ok.1
  | cons step rest ih =>
    have raise (next : Nat) (hn : step.next h = some next) :
        step.next (h + 1) = some (next + 1) := by
      cases step <;> cases h <;> simp [Step.next] at hn ⊢ <;> omega
    cases hn : step.next h with
    | none => simp [trace, hn] at ok
    | some next =>
      cases ht : trace rest next with
      | none => simp [trace, hn, ht] at ok
      | some result =>
        obtain ⟨m, v⟩ := result
        simp [trace, hn, ht] at ok
        obtain ⟨rfl, rfl⟩ := ok
        simp [trace, raise _ hn, ih _ _ ht]

/-- Scan at relative height `h` up to the first down-step which would leave
that relative half-plane. The separating down-step is omitted. -/
private def firstDescent : List Step → Nat → Option (List Step × List Step)
  | [], _ => none
  | step :: rest, h =>
    match step.next h with
    | none => some ([], rest)
    | some next => (firstDescent rest next).map (fun (inside, outside) => (step :: inside, outside))

private theorem firstDescent_after (inside outside : List Step) (h visits : Nat)
    (valid : trace inside h = some (0, visits)) :
    firstDescent (inside ++ .down :: outside) h = some (inside, outside) := by
  induction inside generalizing h visits with
  | nil =>
    simp [trace] at valid
    obtain ⟨rfl, _⟩ := valid
    rfl
  | cons step rest ih =>
    cases hn : step.next h with
    | none => simp [trace, hn] at valid
    | some next =>
      cases ht : trace rest next with
      | none => simp [trace, hn, ht] at valid
      | some result =>
        obtain ⟨m, v⟩ := result
        simp [trace, hn, ht] at valid
        obtain ⟨rfl, _⟩ := valid
        simp [firstDescent, hn, ih _ _ ht]

private theorem firstDescent_split (word : List Step) (h visits : Nat)
    (valid : trace word (h + 1) = some (0, visits)) :
    ∃ inside outside a b, word = inside ++ .down :: outside ∧
      trace inside h = some (0, a) ∧ trace outside 0 = some (0, b) := by
  induction word generalizing h visits with
  | nil => simp [trace] at valid
  | cons step rest ih =>
    have propagate (next : Nat) (small : step.next h = some next)
        (large : step.next (h + 1) = some (next + 1)) :
        ∃ inside outside a b, step :: rest = inside ++ .down :: outside ∧
          trace inside h = some (0, a) ∧ trace outside 0 = some (0, b) := by
      have reduced : trace rest (next + 1) = some (0, visits) := by
        cases ht : trace rest (next + 1) with
        | none => simp [trace, large, ht] at valid
        | some result =>
          obtain ⟨m, v⟩ := result
          simp [trace, large, ht] at valid
          simp [valid.1, valid.2]
      obtain ⟨i, o, a, b, eq, hi, ho⟩ := ih next visits reduced
      exact ⟨step :: i, o, (if next = 0 then 1 else 0) + a, b,
        congrArg (step :: ·) eq, by simp [trace, small, hi], ho⟩
    cases step with
    | horizontal => exact propagate h rfl rfl
    | up => exact propagate (h + 1) rfl rfl
    | down =>
      cases h with
      | zero =>
        cases ht : trace rest 0 with
        | none => simp [trace, Step.next, ht] at valid
        | some result =>
          obtain ⟨m, v⟩ := result
          simp [trace, Step.next, ht] at valid
          obtain ⟨rfl, _⟩ := valid
          exact ⟨[], rest, 0, v, rfl, rfl, ht⟩
      | succ h => exact propagate h rfl rfl

/-- A closed Motzkin walk in its first-return decomposition. The interior of
an arch is a walk at height one above the base. -/
private inductive Path
  | empty
  | horizontal (rest : Path)
  | arch (inside rest : Path)

private def Path.steps : Path → List Step
  | .empty => []
  | .horizontal rest => .horizontal :: rest.steps
  | .arch inside rest => .up :: inside.steps ++ .down :: rest.steps

private def Path.length (p : Path) : Nat := p.steps.length

/-- Count returns to the horizontal axis, including the final endpoint
and excluding the initial endpoint. The empty walk has zero returns. -/
private def Path.rank : Path → Nat
  | .empty => 0
  | .horizontal rest | .arch _ rest => rest.rank + 1

private theorem trace_steps (p : Path) : trace p.steps 0 = some (0, p.rank) := by
  induction p with
  | empty => rfl
  | horizontal rest ih => simp [Path.steps, Path.rank, trace, Step.next, ih, Nat.add_comm]
  | arch inside rest hi hr =>
    have raised := trace_raise _ _ _ _ hi
    have tail : trace (.down :: rest.steps) 1 = some (0, rest.rank + 1) := by
      simp [trace, Step.next, hr, Nat.add_comm]
    have combined := trace_append _ _ _ _ _ raised _ _ tail
    simp [Path.steps, Path.rank, trace, Step.next, combined]

private theorem steps_injective (p q : Path) (eq : p.steps = q.steps) : p = q := by
  induction p generalizing q with
  | empty => cases q <;> simp [Path.steps] at eq ⊢
  | horizontal p ih =>
    cases q with
    | empty | arch => simp [Path.steps] at eq
    | horizontal q =>
      simp only [Path.steps, List.cons.injEq, true_and] at eq
      exact congrArg Path.horizontal (ih _ eq)
  | arch inside rest hi hr =>
    cases q with
    | empty | horizontal => simp [Path.steps] at eq
    | arch inside' rest' =>
      have eq := (List.cons.inj eq).2
      change inside.steps ++ .down :: rest.steps = inside'.steps ++ .down :: rest'.steps at eq
      have first := firstDescent_after inside.steps rest.steps 0 inside.rank (trace_steps inside)
      have second := firstDescent_after inside'.steps rest'.steps 0 inside'.rank (trace_steps inside')
      rw [eq, second] at first
      have pair := Option.some.inj first
      rw [hi _ (congrArg Prod.fst pair).symm, hr _ (congrArg Prod.snd pair).symm]

private theorem steps_surjective (word : List Step) (r : Nat) (valid : trace word 0 = some (0, r)) :
    ∃ p : Path, p.steps = word := by
  match word with
  | [] => exact ⟨.empty, rfl⟩
  | .horizontal :: rest =>
    cases ht : trace rest 0 with
    | none => simp [trace, Step.next, ht] at valid
    | some result =>
      obtain ⟨m, v⟩ := result
      simp [trace, Step.next, ht] at valid
      obtain ⟨rfl, _⟩ := valid
      obtain ⟨p, hp⟩ := steps_surjective rest v ht
      exact ⟨.horizontal p, congrArg (Step.horizontal :: ·) hp⟩
  | .down :: rest => simp [trace, Step.next] at valid
  | .up :: rest =>
    have elevated : trace rest 1 = some (0, r) := by
      cases ht : trace rest 1 with
      | none => simp [trace, Step.next, ht] at valid
      | some result =>
        obtain ⟨m, v⟩ := result
        simp [trace, Step.next, ht] at valid
        simp [valid.1, valid.2]
    obtain ⟨i, o, a, b, split, hi, ho⟩ := firstDescent_split rest 0 r elevated
    have len := congrArg List.length split
    simp only [List.length_append, List.length_cons] at len
    have : i.length < (Step.up :: rest).length := by simp; omega
    have : o.length < (Step.up :: rest).length := by simp; omega
    obtain ⟨p, hp⟩ := steps_surjective i a hi
    obtain ⟨q, hq⟩ := steps_surjective o b ho
    exact ⟨.arch p q, by simp [Path.steps, hp, hq, split]⟩
termination_by word.length
decreasing_by all_goals first | assumption | simp


private def Path.join : Path → Path → Path
  | .empty, right => right
  | .horizontal rest, right => .horizontal (rest.join right)
  | .arch inside rest, right => .arch inside (rest.join right)

private theorem join_steps (left right : Path) :
    (left.join right).steps = left.steps ++ right.steps := by
  induction left with
  | empty => rfl
  | horizontal rest ih => simp [Path.join, Path.steps, ih]
  | arch inside rest _ ih => simp [Path.join, Path.steps, ih, List.append_assoc]

/-- All ways to cut a walk at the base height, including both endpoints. -/
private def Path.cuts : Path → List (Path × Path)
  | .empty => [(.empty, .empty)]
  | .horizontal rest =>
    (.empty, .horizontal rest) :: rest.cuts.map (fun (a, b) => (.horizontal a, b))
  | .arch inside rest =>
    (.empty, .arch inside rest) :: rest.cuts.map (fun (a, b) => (.arch inside a, b))

private theorem mem_cuts (path left right : Path) :
    (left, right) ∈ path.cuts ↔ left.join right = path := by
  induction path generalizing left right with
  | empty => cases left <;> cases right <;> simp [Path.cuts, Path.join]
  | horizontal rest ih =>
    cases left <;> simp [Path.cuts, Path.join, Prod.ext_iff, ih]
  | arch inside rest _ ih =>
    cases left with
    | empty | horizontal => simp [Path.cuts, Path.join, Prod.ext_iff]
    | arch p q =>
      simp only [Path.cuts, List.mem_cons, Prod.mk.injEq, reduceCtorEq, false_and,
        List.mem_map, Prod.exists, ih, false_or, Path.join, Path.arch.injEq]
      constructor
      · rintro ⟨a, b, equal, ⟨rfl, rfl⟩, rfl⟩
        exact ⟨rfl, equal⟩
      · rintro ⟨rfl, h⟩
        exact ⟨q, right, h, ⟨rfl, rfl⟩, rfl⟩

private theorem cuts_nodup (path : Path) : path.cuts.Nodup := by
  induction path with
  | empty => simp [Path.cuts]
  | horizontal rest ih =>
    rw [Path.cuts, List.nodup_cons]
    refine ⟨by simp [Prod.ext_iff], ih.map _ ?_⟩
    intro a b ne eq
    rcases a with ⟨a, a'⟩
    rcases b with ⟨b, b'⟩
    exact ne (by simpa using eq)
  | arch inside rest _ ih =>
    rw [Path.cuts, List.nodup_cons]
    refine ⟨by simp [Prod.ext_iff], ih.map _ ?_⟩
    intro a b ne eq
    rcases a with ⟨a, a'⟩
    rcases b with ⟨b, b'⟩
    exact ne (by simpa using eq)

private def archCut (cut : Path × Path) : Path := .arch cut.1 cut.2

/-- Enumerate walks without a length cutoff. In the up-step branch, a cut
determines which part of the shorter walk goes inside the first arch. -/
private def paths : Nat → List Path
  | 0 => [.empty]
  | 1 => [.horizontal .empty]
  | m + 2 => (paths (m + 1)).map Path.horizontal ++
      (paths m).flatMap (fun path => path.cuts.map archCut)

private theorem length_horizontal (p : Path) :
    (p.horizontal).length = p.length + 1 := rfl

private theorem length_arch (p q : Path) :
    (p.arch q).length = p.length + q.length + 2 := by
  simp [Path.length, Path.steps]
  omega

private theorem length_join (p q : Path) : (p.join q).length = p.length + q.length := by
  simp [Path.length, join_steps]

private theorem length_zero (p : Path) : p.length = 0 ↔ p = .empty := by
  cases p with
  | empty => simp [Path.length, Path.steps]
  | horizontal p => simp [length_horizontal]
  | arch p q => simp [length_arch]

private theorem mem_paths (m : Nat) (path : Path) : path ∈ paths m ↔ path.length = m := by
  match m with
  | 0 => simp [paths, length_zero]
  | 1 =>
    cases path with
    | empty => simp [paths, Path.length, Path.steps]
    | horizontal rest => simp [paths, length_horizontal, length_zero]
    | arch p q => simp [paths, length_arch]
  | m + 2 =>
    constructor
    · intro member
      simp only [paths, List.mem_append, List.mem_map, List.mem_flatMap] at member
      rcases member with ⟨rest, hr, rfl⟩ | ⟨shorter, hshort, cut, hcut, rfl⟩
      · rw [length_horizontal, (mem_paths (m + 1) rest).mp hr]
      · obtain ⟨p, q⟩ := cut
        have eq := (mem_cuts shorter p q).mp hcut
        have size := (mem_paths m shorter).mp hshort
        simpa [archCut, length_arch, ← eq, length_join] using size
    · intro len
      cases path with
      | empty => simp [Path.length, Path.steps] at len
      | horizontal rest =>
        apply List.mem_append_left
        apply List.mem_map.mpr
        refine ⟨rest, (mem_paths (m + 1) rest).mpr ?_, rfl⟩
        rw [length_horizontal] at len
        omega
      | arch p q =>
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨p.join q, (mem_paths m (p.join q)).mpr ?_, List.mem_map.mpr ?_⟩
        · rw [length_arch] at len
          rw [length_join]
          omega
        · exact ⟨(p, q), (mem_cuts _ _ _).mpr rfl, rfl⟩

private theorem nodup_paths (m : Nat) : (paths m).Nodup := by
  match m with
  | 0 | 1 => simp [paths]
  | m + 2 =>
    rw [paths, List.nodup_append]
    refine ⟨(nodup_paths (m + 1)).map _ (by simp), ?_, ?_⟩
    · rw [List.Nodup, List.pairwise_flatMap]
      refine ⟨?_, ?_⟩
      · intro p _
        exact (cuts_nodup p).map _ (by
          intro a b ne eq
          apply ne
          cases a
          cases b
          simpa [archCut, Prod.ext_iff] using eq)
      · apply (nodup_paths m).imp
        intro a b ne u hu v hv eq
        obtain ⟨⟨p, q⟩, hp, rfl⟩ := List.mem_map.mp hu
        obtain ⟨⟨p', q'⟩, hq, rfl⟩ := List.mem_map.mp hv
        simp only [archCut, Path.arch.injEq] at eq
        obtain ⟨rfl, rfl⟩ := eq
        exact ne (((mem_cuts a p q).mp hp).symm.trans ((mem_cuts b p q).mp hq))
    · intro a ha b hb eq
      obtain ⟨rest, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨_, _, member⟩ := List.mem_flatMap.mp hb
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      cases eq

/-- Each literal step sequence of the given length, without repetitions. -/
def motzkinWalks (m : Nat) : List (List Step) := (paths m).map Path.steps

/-- Definition 3.14: a Motzkin walk is a word of the prescribed length whose
steps stay at nonnegative height and end back at height zero. -/
theorem mem_motzkinWalks (m : Nat) (word : List Step) :
    word ∈ motzkinWalks m ↔ word.length = m ∧ ∃ rank, trace word 0 = some (0, rank) := by
  constructor
  · intro mem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp mem
    exact ⟨(mem_paths _ _).mp hp, p.rank, trace_steps p⟩
  · rintro ⟨len, r, hr⟩
    obtain ⟨p, hp⟩ := steps_surjective word r hr
    exact List.mem_map.mpr ⟨p, (mem_paths _ _).mpr (by simpa [Path.length, hp] using len), hp⟩

theorem motzkinWalks_nodup (m : Nat) : (motzkinWalks m).Nodup :=
  (nodup_paths m).map _ (fun a b ne eq => ne (steps_injective a b eq))


private theorem liftWeight_succ (weight : Nat → Nat) (rank : Nat) :
    liftWeight weight (rank + 1) = liftWeight weight rank + weight (rank + 2) := by
  unfold liftWeight
  rw [List.range'_concat, List.map_append, List.sum_append]
  simp [Nat.add_comm, Nat.add_left_comm]

private theorem cuts_weight (path : Path) (weight : Nat → Nat) :
    (path.cuts.map (fun cut => weight (cut.2.rank + 1))).sum =
      liftWeight weight path.rank := by
  induction path with
  | empty => simp [Path.cuts, Path.rank, liftWeight, List.range']
  | horizontal rest ih =>
    simp only [Path.cuts, List.map_cons, List.sum_cons, Path.rank, liftWeight_succ,
      List.map_map, Function.comp_def, Nat.add_assoc, ih]
    exact Nat.add_comm _ _
  | arch inside rest _ ih =>
    simp only [Path.cuts, List.map_cons, List.sum_cons, Path.rank, liftWeight_succ,
      List.map_map, Function.comp_def, Nat.add_assoc, ih]
    exact Nat.add_comm _ _

/-- Sum weights of ground returns over the literal step words. -/
def walkWeight (m : Nat) (weight : Nat → Nat) : Nat :=
  ((motzkinWalks m).map (fun word => weight ((trace word 0).getD (0, 0)).2)).sum

private theorem walkWeight_paths (m : Nat) (weight : Nat → Nat) :
    walkWeight m weight = ((paths m).map (fun path => weight path.rank)).sum := by
  unfold walkWeight motzkinWalks
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp [trace_steps]

/-- The exact Motzkin counting transition. An initial horizontal step adds one
return. An initial arch wraps the first part of the shorter path at any cut
at ground height. -/
theorem walkWeight_succ_succ (m : Nat) (weight : Nat → Nat) :
    walkWeight (m + 2) weight =
      walkWeight (m + 1) (fun r => weight (r + 1)) +
        walkWeight m (liftWeight weight) := by
  simp only [walkWeight_paths, paths, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, Path.rank]
  congr 1
  rw [List.map_flatMap]
  induction paths m with
  | nil => rfl
  | cons path rest ih =>
    rw [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih, List.map_map]
    exact congrArg (· + _) (cuts_weight path weight)

private theorem reverse_zero (weight : Nat → Nat) :
    outcomeWeight (reverseOutcome 0) weight = weight 0 := by
  change weight 0 + 0 = weight 0
  exact Nat.add_zero _

private theorem reverse_one (weight : Nat → Nat) :
    outcomeWeight (reverseOutcome 1) weight = weight 1 := by
  change weight 1 + 0 = weight 1
  exact Nat.add_zero _

/-- Rank-by-rank agreement for every weight. For a nonempty walk of rank
`r`, the paper's number of interior touches is `r - 1`. -/
theorem reverseOutcome_weight_eq_motzkin (m : Nat) (weight : Nat → Nat) :
    outcomeWeight (reverseOutcome m) weight = walkWeight m weight := by
  match m with
  | 0 => simp [reverse_zero, walkWeight_paths, paths, Path.rank]
  | 1 => simp [reverse_one, walkWeight_paths, paths, Path.rank]
  | m + 2 =>
    rw [reverseOutcome_weight_succ_succ, walkWeight_succ_succ,
      reverseOutcome_weight_eq_motzkin (m + 1), reverseOutcome_weight_eq_motzkin m]

/-- The increasing prefix outcome is counted by weighting ordinary Motzkin
walks of length `n - k` by the number of ways to insert the `k` prefix cars. -/
theorem increasingPrefix_count_eq_motzkin (n k : Nat) (bound : k ≤ n) :
    (outcomeWords (withIncreasingPrefix k (reverseOutcome (n - k)))).length =
      walkWeight (n - k) (iteratedLiftCount k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le bound
  rw [Nat.add_sub_cancel_left, ← reverseOutcome_weight_eq_motzkin, increasingPrefix_count,
    outcomeWeight]

private theorem liftWeight_shift (weight : Nat → Nat) (r : Nat) :
    liftWeight weight (r + 1) = weight 1 + liftWeight (fun s => weight (s + 1)) r := by
  unfold liftWeight
  conv => lhs; rw [List.range']
  simp only [List.map_cons, List.sum_cons, Nat.reduceAdd]
  rw [List.range'_succ_left, List.map_map]
  rfl

private theorem sumNat_map_mul_left {α : Type} (xs : List α) (a : Nat) (f : α → Nat) :
    ((xs.map fun x => a * f x).sum) = a * (xs.map f).sum := by
  induction xs <;> simp_all [Nat.mul_add]

private theorem sumNat_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    ((xs.map fun x => f x + g x).sum) = (xs.map f).sum + (xs.map g).sum := by
  induction xs <;> simp_all [Nat.add_left_comm, Nat.add_assoc]

/-- The diagonal of the lift triangle. Its Catalan recurrence is proved below. -/
def liftCatalan (k : Nat) : Nat := iteratedLiftCount k 0

private theorem liftCatalan_succ (k : Nat) : liftCatalan (k + 1) = iteratedLiftCount k 1 := by
  change iteratedLiftCount k 1 + 0 = iteratedLiftCount k 1
  exact Nat.add_zero _

private theorem sum_rank_weights {α β : Type} (entries : List α) (rank : α → Nat)
    (terms : List β) (c : β → Nat) (f : β → Nat → Nat) :
    (entries.map fun entry => (terms.map fun x => c x * f x (rank entry)).sum).sum =
      (terms.map fun x => c x * (entries.map fun entry => f x (rank entry)).sum).sum := by
  induction terms with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sumNat_map_add, sumNat_map_mul_left, ih]

/-- One extra ground return convolves the lift counts with the Catalan diagonal. -/
private theorem iteratedLiftCount_shift (k r : Nat) :
    iteratedLiftCount k (r + 1) =
      ((List.finRange (k + 1)).map fun i =>
        liftCatalan i.val * iteratedLiftCount (k - i.val) r).sum := by
  induction k generalizing r with
  | zero => simp [List.finRange_succ, liftCatalan, iteratedLiftCount, iteratedLiftWeight]
  | succ k ih =>
    change liftWeight (iteratedLiftCount k) (r + 1) = _
    rw [liftWeight_shift, List.finRange_succ_last, List.map_append, List.sum_append]
    simp only [List.map_map, Function.comp_def, Fin.val_castSucc, List.map_singleton,
      List.sum_cons, List.sum_nil, Nat.add_zero, Fin.val_last, Nat.sub_self]
    rw [liftCatalan_succ]
    have same (i : Fin (k + 1)) : k + 1 - i.val = k - i.val + 1 := by omega
    simp only [same]
    change iteratedLiftCount k 1 + liftWeight (fun s => iteratedLiftCount k (s + 1)) r =
      _ + iteratedLiftCount k 1 * 1
    simp only [Nat.mul_one]
    have expanded := sum_rank_weights (List.range' 1 (r + 1)) id (List.finRange (k + 1))
      (fun i => liftCatalan i.val) (fun i => iteratedLiftCount (k - i.val))
    change liftWeight (fun s => ((List.finRange (k + 1)).map fun i =>
      liftCatalan i.val * iteratedLiftCount (k - i.val) s).sum) r = _ at expanded
    rw [← funext (ih ·)] at expanded
    rw [expanded, Nat.add_comm (iteratedLiftCount k 1)]
    rfl

/-- The initial value and convolution characterize the ordinary Catalan numbers. -/
theorem liftCatalan_spec :
    liftCatalan 0 = 1 ∧ ∀ k,
      liftCatalan (k + 1) =
        ((List.finRange (k + 1)).map fun i => liftCatalan i.val * liftCatalan (k - i.val)).sum :=
  ⟨rfl, fun k => (liftCatalan_succ k).trans (iteratedLiftCount_shift k 0)⟩

private theorem weighted_walk_recurrence (k m : Nat) :
    walkWeight m (iteratedLiftCount (k + 1)) +
      ((List.finRange (k + 1)).map fun i =>
        liftCatalan i.val * walkWeight (m + 1) (iteratedLiftCount (k - i.val))).sum =
      walkWeight (m + 2) (iteratedLiftCount k) := by
  rw [walkWeight_succ_succ, Nat.add_comm]
  change _ + walkWeight m (iteratedLiftCount (k + 1)) =
    _ + walkWeight m (iteratedLiftCount (k + 1))
  congr 1
  unfold walkWeight
  simp only [iteratedLiftCount_shift]
  exact (sum_rank_weights (motzkinWalks (m + 1))
    (fun word => ((trace word 0).getD (0, 0)).2) (List.finRange (k + 1))
    (fun i => liftCatalan i.val) (fun i => iteratedLiftCount (k - i.val))).symm

private def subtractCoefficients : List Int → List Int → List Int
  | [], right => right.map Neg.neg
  | left, [] => left
  | a :: as, b :: bs => (a - b) :: subtractCoefficients as bs

/-- Coefficients in increasing offset from the suffix length `n - k`.
If `P_k(T)` is the Laurent polynomial in shifts from `n`, this list
represents `T^k P_k(T)`. -/
def signedCoefficients : Nat → List Int
  | 0 => [1]
  | k + 1 => 0 :: (List.finRange (k + 1)).foldr
      (fun i acc => subtractCoefficients acc
        ((signedCoefficients (k - i.val)).map ((liftCatalan i.val : Int) * ·)))
      (0 :: signedCoefficients k)
termination_by k => k
decreasing_by all_goals omega

private theorem subtractCoefficients_length (as bs : List Int) (bound : bs.length ≤ as.length) :
    (subtractCoefficients as bs).length = as.length := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [subtractCoefficients]
  | cons a as ih =>
    cases bs with
    | nil => simp [subtractCoefficients]
    | cons b bs =>
      simp only [subtractCoefficients, List.length_cons]
      rw [ih bs (by simpa using bound)]

private theorem subtractCoefficients_append (as bs : List Int) (a : Int)
    (bound : bs.length ≤ as.length) :
    subtractCoefficients (as ++ [a]) bs = subtractCoefficients as bs ++ [a] := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [subtractCoefficients]
  | cons b as ih =>
    cases bs with
    | nil => simp [subtractCoefficients]
    | cons c bs =>
      simp only [List.cons_append, subtractCoefficients, List.cons.injEq, true_and]
      exact ih bs (by simpa using bound)

private theorem fold_subtract_coefficients {α : Type} (xs : List α) (coeffs : α → List Int)
    (base : List Int) (a : Int) (bound : ∀ x ∈ xs, (coeffs x).length ≤ base.length) :
    ∃ front : List Int, front.length = base.length ∧
      xs.foldr (fun x acc => subtractCoefficients acc (coeffs x)) (base ++ [a]) =
        front ++ [a] := by
  induction xs with
  | nil => exact ⟨base, rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨front, size, eq⟩ := ih (fun y hy => bound y (List.mem_cons_of_mem x hy))
    have fits : (coeffs x).length ≤ front.length := size ▸ bound x (by simp)
    exact ⟨subtractCoefficients front (coeffs x), (subtractCoefficients_length _ _ fits).trans size,
      by rw [List.foldr_cons, eq, subtractCoefficients_append _ _ _ fits]⟩

/-- The coefficient of the highest shift is one. In positive rank the
zero offset vanishes, so there are at most `2 * k` nonzero shifts. -/
theorem signedCoefficients_shape (k : Nat) :
    (signedCoefficients k).length = 2 * k + 1 ∧
      (signedCoefficients k).getLast? = some 1 ∧
      (0 < k → (signedCoefficients k).head? = some 0) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp [signedCoefficients]
    | succ k =>
      obtain ⟨size, last, _⟩ := ih k (Nat.lt_succ_self k)
      obtain ⟨lower, split⟩ := List.getLast?_eq_some_iff.mp last
      let start := 0 :: lower
      have startSize : start.length = 2 * k + 1 := by
        rw [split] at size
        simp only [List.length_append, List.length_cons, List.length_nil] at size
        simp [start, Nat.add_right_cancel size]
      obtain ⟨front, prefixSize, eq⟩ := fold_subtract_coefficients (List.finRange (k + 1))
        (fun i => (signedCoefficients (k - i.val)).map ((liftCatalan i.val : Int) * ·))
        start 1 (by
          intro i _
          rw [List.length_map, (ih (k - i.val) (by omega)).1, startSize]
          omega)
      have startSplit : 0 :: signedCoefficients k = start ++ [1] :=
        congrArg (0 :: ·) split
      rw [signedCoefficients, startSplit, eq]
      simp [List.getLast?_cons, List.getLast?_append, prefixSize, startSize]
      omega

private def shiftSum (coefficients : List Int) (m : Nat) : Int :=
  ((coefficients.zipIdx m).map (fun (a, j) => a * ((motzkinWalks j).length : Int))).sum

@[simp] private theorem shiftSum_nil (m : Nat) : shiftSum [] m = 0 := rfl

@[simp] private theorem shiftSum_cons (a : Int) (as : List Int) (m : Nat) :
    shiftSum (a :: as) m = a * ((motzkinWalks m).length : Int) + shiftSum as (m + 1) := by
  simp [shiftSum]

private theorem shiftSum_scale (a : Int) (as : List Int) (m : Nat) :
    shiftSum (as.map (a * ·)) m = a * shiftSum as m := by
  induction as generalizing m <;> simp_all [Int.mul_add, Int.mul_assoc]

private theorem shiftSum_sub (as bs : List Int) (m : Nat) :
    shiftSum (subtractCoefficients as bs) m = shiftSum as m - shiftSum bs m := by
  induction as generalizing bs m with
  | nil =>
    simp only [subtractCoefficients, shiftSum_nil]
    have negated : bs.map Neg.neg = bs.map ((-1 : Int) * ·) := by
      exact congrArg (fun f => bs.map f) (funext Int.neg_eq_neg_one_mul)
    rw [negated, shiftSum_scale]
    omega
  | cons a as ih =>
    cases bs with
    | nil => simp [subtractCoefficients]
    | cons b bs =>
      simp only [subtractCoefficients, shiftSum_cons, ih, Int.sub_mul]
      omega

private theorem shiftSum_fold_sub {α : Type} (xs : List α) (coeffs : α → List Int)
    (base : List Int) (m : Nat) :
    shiftSum (xs.foldr (fun x acc => subtractCoefficients acc (coeffs x)) base) m =
      shiftSum base m - (xs.map fun x => shiftSum (coeffs x) m).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, shiftSum_sub, ih, List.map_cons, List.sum_cons]
    omega

private theorem cast_sum {α : Type} (xs : List α) (f : α → Nat) :
    ((xs.map f).sum : Int) = (xs.map fun x => (f x : Int)).sum := by
  induction xs <;> simp_all [Int.natCast_add]

private theorem shiftSum_eq_walkWeight (k m : Nat) :
    shiftSum (signedCoefficients k) m = walkWeight m (iteratedLiftCount k) := by
  induction k using Nat.strongRecOn generalizing m with
  | ind k ih =>
    cases k with
    | zero =>
      simp [signedCoefficients]
      simp [walkWeight, iteratedLiftCount, iteratedLiftWeight, List.map_const',
        List.sum_replicate_nat]
    | succ k =>
      rw [signedCoefficients, shiftSum_cons, Int.zero_mul, Int.zero_add, shiftSum_fold_sub]
      simp only [shiftSum_cons, Int.zero_mul, Int.zero_add, shiftSum_scale]
      have term (i : Fin (k + 1)) :
          shiftSum (signedCoefficients (k - i.val)) (m + 1) =
            walkWeight (m + 1) (iteratedLiftCount (k - i.val)) :=
        ih (k - i.val) (by omega) (m + 1)
      simp only [ih k (Nat.lt_succ_self k), term]
      have recurrence := congrArg Int.ofNat (weighted_walk_recurrence k m)
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, cast_sum, Int.natCast_mul] at recurrence
      rw [show m + 1 + 1 = m + 2 by rfl]
      omega

/-- The parking count is a signed sum of shifted ordinary Motzkin numbers.
Coefficient list indices start at offset zero from the suffix length. -/
theorem increasingPrefix_count_eq_signed_motzkin (n k : Nat) (bound : k ≤ n) :
    ((outcomeWords (withIncreasingPrefix k (reverseOutcome (n - k)))).length : Int) =
      (((signedCoefficients k).zipIdx (n - k)).map
        (fun (a, j) => a * ((motzkinWalks j).length : Int))).sum := by
  rw [increasingPrefix_count_eq_motzkin n k bound]
  exact (shiftSum_eq_walkWeight k (n - k)).symm

end BackgammonMotzkinPaths
