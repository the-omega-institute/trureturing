/- GID: D5/S3/Observer/Budget/HussainRecognitionDepth
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/HussainRecognitionDepth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Deterministic recognition depth stabilizes under finite Hom and Het. -/

import D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound

/-!
# Eventual constancy of deterministic recognition depth

Hussain's Question 3 asks whether finite Hom and Het force the exact minimum
recognition depth to stabilize. A common pair of equal adjacent coordinates
permits same-depth transfer from the preceding length.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.HussainRecognitionDepth

open WorstCaseDepthInformationLowerBound
open scoped List

universe u v w x

/-- The subtree below the unique unlabeled edge of the source's root.
At a query the nonempty set specifies the distinct, present letter branches.
When the alphabet is finite, the inductive tree is finitely branching and finite. -/
inductive SourceTree (Alphabet : Type u) (Query : Type v) (State : Type w)
  | terminal (label : State)
  | query (coordinate : Query) (letters : Set Alphabet) (present : letters.Nonempty)
      (next : letters → SourceTree Alphabet Query State)

/-- A complete path records its query edges in order and its terminal label. -/
inductive CompletePath {Alphabet : Type u} {Query : Type v} {State : Type w} :
    SourceTree Alphabet Query State → List (Query × Alphabet) → State → Prop
  | terminal (label : State) : CompletePath (.terminal label) [] label
  | step {coordinate : Query} {letters : Set Alphabet} {present : letters.Nonempty}
      {next : letters → SourceTree Alphabet Query State} {tail : List (Query × Alphabet)}
      {label : State} (answer : letters) (path : CompletePath (next answer) tail label) :
      CompletePath (.query coordinate letters present next) ((coordinate, answer.val) :: tail) label

/-- All queried letters along a path agree with the input. -/
def Compatible {Alphabet : Type u} {Query : Type v} {State : Type w}
    (readout : Query → State → Alphabet) (state : State) (path : List (Query × Alphabet)) :
    Prop :=
  ∀ edge ∈ path, readout edge.1 state = edge.2

/-- The bound applies to every complete path, including those with no compatible input. -/
def DepthLE {Alphabet : Type u} {Query : Type v} {State : Type w}
    (tree : SourceTree Alphabet Query State) (depth : Nat) : Prop :=
  ∀ ⦃path label⦄, CompletePath tree path label → path.length ≤ depth

/-- Every input has a compatible complete path and every such path gives its label. -/
def Recognizes {Alphabet : Type u} {Query : Type v} {State : Type w}
    (readout : Query → State → Alphabet) (tree : SourceTree Alphabet Query State) : Prop :=
  (∀ state, ∃ path label, CompletePath tree path label ∧ Compatible readout state path) ∧
  ∀ state path label, CompletePath tree path label → Compatible readout state path → label = state

/-- Feasible source depth with Definition 8's zero-depth convention for the empty promise.
Each actual tree labels its leaves by members of the promise type. -/
def SourceExactAtDepth {Alphabet : Type u} {Query : Type v} {State : Type w}
    (readout : Query → State → Alphabet) (depth : Nat) : Prop :=
  IsEmpty State ∨ ∃ tree, DepthLE tree depth ∧ Recognizes readout tree

private theorem exists_completePath {Alphabet : Type u} {Query : Type v} {State : Type w}
    (tree : SourceTree Alphabet Query State) :
    ∃ path label, CompletePath tree path label := by
  induction tree with
  | terminal label => exact ⟨[], label, .terminal label⟩
  | query coordinate letters present next ih =>
      obtain ⟨answer, belongs⟩ := present
      obtain ⟨path, label, complete⟩ := ih ⟨answer, belongs⟩
      exact ⟨(coordinate, answer) :: path, label, .step ⟨answer, belongs⟩ complete⟩

private theorem source_to_protocol {Alphabet : Type u} {Query : Type v} {State : Type w}
    {B : Nat} (encode : Alphabet ≃ Fin B) (readout : Query → State → Alphabet)
    (tree : SourceTree Alphabet Query State) {depth : Nat} (bound : DepthLE tree depth) :
    ∃ protocol : AdaptiveProtocol State B depth,
      UsesReadoutFamily (fun coordinate state => encode (readout coordinate state)) protocol ∧
      ∀ (left right : State) (leftPath rightPath : List (Query × Alphabet))
        (leftLabel rightLabel : State),
        CompletePath tree leftPath leftLabel → CompletePath tree rightPath rightLabel →
        Compatible readout left leftPath → Compatible readout right rightPath →
        adaptiveTranscript protocol left = adaptiveTranscript protocol right →
        leftLabel = rightLabel := by
  classical
  induction tree generalizing depth with
  | terminal label =>
      refine ⟨.leaf, trivial, ?_⟩
      intro left right leftPath rightPath leftLabel rightLabel leftComplete rightComplete _ _ _
      cases leftComplete
      cases rightComplete
      rfl
  | query coordinate letters present next ih =>
      cases depth with
      | zero =>
          obtain ⟨answer, belongs⟩ := present
          obtain ⟨path, label, complete⟩ := exists_completePath (next ⟨answer, belongs⟩)
          exact (Nat.not_succ_le_zero path.length (bound (.step ⟨answer, belongs⟩ complete))).elim
      | succ depth =>
          have childBound (answer : letters) : DepthLE (next answer) depth := by
            intro path label complete
            exact Nat.le_of_succ_le_succ (bound (.step answer complete))
          choose child allowed identifies using fun answer => ih answer (childBound answer)
          let branch (code : Fin B) : AdaptiveProtocol State B depth :=
            if belongs : encode.symm code ∈ letters then child ⟨encode.symm code, belongs⟩
            else .leaf
          refine ⟨.query (fun state => encode (readout coordinate state)) branch, ?_, ?_⟩
          · refine ⟨⟨coordinate, rfl⟩, fun code => ?_⟩
            dsimp [branch]
            split
            · exact allowed _
            · trivial
          · intro left right leftPath rightPath leftLabel rightLabel leftComplete rightComplete
              leftCompatible rightCompatible same
            cases leftComplete with
            | step leftAnswer leftTail =>
              cases rightComplete with
              | step rightAnswer rightTail =>
                have leftRead := leftCompatible _ (List.mem_cons_self)
                have rightRead := rightCompatible _ (List.mem_cons_self)
                simp only [adaptiveTranscript, leftRead, rightRead, List.cons.injEq] at same
                have answersEqual : leftAnswer = rightAnswer :=
                  Subtype.ext (encode.injective same.1)
                subst rightAnswer
                apply identifies leftAnswer left right _ _ _ _ leftTail rightTail
                  (fun edge mem => leftCompatible edge (List.mem_cons_of_mem _ mem))
                  (fun edge mem => rightCompatible edge (List.mem_cons_of_mem _ mem))
                simpa only [branch, Equiv.symm_apply_apply, dite_eq_left leftAnswer.property]
                  using same.2

private theorem protocol_to_source {Alphabet : Type u} {Query : Type v} {State : Type w}
    {B depth : Nat} (encode : Alphabet ≃ Fin B) (readout : Query → State → Alphabet)
    (fallback : State) (protocol : AdaptiveProtocol State B depth)
    (allowed : UsesReadoutFamily (fun coordinate state => encode (readout coordinate state))
      protocol) (context : Set State)
    (identifies : ∀ left ∈ context, ∀ right ∈ context,
      adaptiveTranscript protocol left = adaptiveTranscript protocol right → left = right) :
    ∃ tree : SourceTree Alphabet Query State, DepthLE tree depth ∧
      (∀ state ∈ context, ∃ path label,
        CompletePath tree path label ∧ Compatible readout state path) ∧
      ∀ state ∈ context, ∀ path label, CompletePath tree path label →
        Compatible readout state path → label = state := by
  classical
  induction protocol generalizing context with
  | leaf =>
      let label := if inhabited : context.Nonempty then inhabited.choose else fallback
      refine ⟨.terminal label, ?_, ?_, ?_⟩
      · intro path output complete
        cases complete
        exact Nat.zero_le _
      · intro state stateIn
        exact ⟨[], label, .terminal label, by simp [Compatible]⟩
      · intro state stateIn path output complete _
        cases complete
        have inhabited : context.Nonempty := ⟨state, stateIn⟩
        simpa only [label, dite_eq_left inhabited] using
          identifies inhabited.choose inhabited.choose_spec state stateIn rfl
  | query question next ih =>
      rcases allowed with ⟨⟨coordinate, rfl⟩, nextAllowed⟩
      let childContext (answer : Alphabet) : Set State :=
        {state | state ∈ context ∧ readout coordinate state = answer}
      have childIdentifies (answer : Alphabet) :
          ∀ left ∈ childContext answer, ∀ right ∈ childContext answer,
            adaptiveTranscript (next (encode answer)) left =
              adaptiveTranscript (next (encode answer)) right → left = right := by
        intro left leftIn right rightIn same
        apply identifies left leftIn.1 right rightIn.1
        simp only [adaptiveTranscript, leftIn.2, rightIn.2, same]
      choose child bound covers sound using fun answer : Alphabet =>
        ih (encode answer) (nextAllowed (encode answer))
          (childContext answer) (childIdentifies answer)
      refine ⟨.query coordinate Set.univ ⟨readout coordinate fallback, Set.mem_univ _⟩
        (fun answer => child answer.val), ?_, ?_, ?_⟩
      · intro path label complete
        cases complete with
        | step answer tail => exact Nat.succ_le_succ (bound answer.val tail)
      · intro state stateIn
        obtain ⟨path, label, complete, compatible⟩ :=
          covers (readout coordinate state) state ⟨stateIn, rfl⟩
        refine ⟨_, label, .step ⟨readout coordinate state, Set.mem_univ _⟩ complete, ?_⟩
        intro edge mem
        rcases List.mem_cons.mp mem with rfl | mem
        · rfl
        · exact compatible edge mem
      · intro state stateIn path label complete compatible
        cases complete with
        | step answer tail =>
          exact sound answer.val state ⟨stateIn, compatible _ List.mem_cons_self⟩ _ label tail
            (fun edge mem => compatible edge (List.mem_cons_of_mem _ mem))

private theorem source_exact_iff {Alphabet : Type u} {Query : Type v} {State : Type w}
    {B depth : Nat} (encode : Alphabet ≃ Fin B) (readout : Query → State → Alphabet) :
    SourceExactAtDepth readout depth ↔
      ExactAtDepth (fun coordinate state => encode (readout coordinate state)) depth := by
  constructor
  · rintro (empty | ⟨tree, bound, covers, sound⟩)
    · exact ⟨zeroQuestionProtocol State B depth, trivial, fun state => empty.false state |>.elim⟩
    · obtain ⟨protocol, allowed, identifies⟩ := source_to_protocol encode readout tree bound
      refine ⟨protocol, allowed, ?_⟩
      intro left right same
      obtain ⟨leftPath, leftLabel, leftComplete, leftCompatible⟩ := covers left
      obtain ⟨rightPath, rightLabel, rightComplete, rightCompatible⟩ := covers right
      rw [← sound left leftPath leftLabel leftComplete leftCompatible,
        ← sound right rightPath rightLabel rightComplete rightCompatible]
      exact identifies left right leftPath rightPath leftLabel rightLabel
        leftComplete rightComplete leftCompatible rightCompatible same
  · rintro ⟨protocol, allowed, identifies⟩
    cases isEmpty_or_nonempty State with
    | inl empty => exact Or.inl empty
    | inr inhabited =>
        obtain ⟨fallback⟩ := inhabited
        obtain ⟨tree, bound, covers, sound⟩ := protocol_to_source encode readout fallback
          protocol allowed Set.univ (fun left _ right _ => @identifies left right)
        exact Or.inr ⟨tree, bound, fun state => covers state (Set.mem_univ _),
          fun state => sound state (Set.mem_univ _)⟩

/-- The length-n promise, with arrays indexed by coordinates and membership tested on words. -/
def Promise {Alphabet : Type u} (language : Set (List Alphabet)) (n : Nat) :=
  {word : Fin n → Alphabet // List.ofFn word ∈ language}

/-- The queried letter at a named coordinate. -/
def coordinateReadout {Alphabet : Type u} {language : Set (List Alphabet)} {n : Nat}
    (coordinate : Fin n) (word : Promise language n) : Alphabet :=
  word.val coordinate

private theorem queryAll_spec {Query : Type v} {State : Type w} {B depth : Nat}
    (readout : Query → State → Fin B) (coordinate : Fin depth → Query) :
    let protocol := adaptiveProtocol B depth (fun state i => readout (coordinate i) state)
    UsesReadoutFamily readout protocol ∧
      ∀ left right, adaptiveTranscript protocol left = adaptiveTranscript protocol right →
        ∀ i, readout (coordinate i) left = readout (coordinate i) right := by
  induction depth with
  | zero =>
      exact ⟨trivial, fun _ _ _ i => Fin.elim0 i⟩
  | succ depth ih =>
      obtain ⟨allowed, recovers⟩ := ih (fun i => coordinate i.castSucc)
      refine ⟨⟨⟨coordinate (Fin.last depth), rfl⟩, fun _ => allowed⟩, ?_⟩
      intro left right equal i
      simp only [adaptiveProtocol, adaptiveTranscript, List.cons.injEq] at equal
      exact Fin.lastCases equal.1 (recovers left right equal.2) i

private theorem protocol_exists {Alphabet : Type u} [Fintype Alphabet]
    (language : Set (List Alphabet)) (n : Nat) :
    ∃ depth, ExactAtDepth (fun (i : Fin n) (word : Promise language n) =>
      Fintype.equivFin Alphabet (coordinateReadout i word)) depth := by
  let readout (i : Fin n) (word : Promise language n) :=
    Fintype.equivFin Alphabet (coordinateReadout i word)
  obtain ⟨allowed, recovers⟩ := queryAll_spec readout (id : Fin n → Fin n)
  refine ⟨n, adaptiveProtocol (Fintype.card Alphabet) n (fun word i => readout i word),
    allowed, ?_⟩
  intro left right equal
  exact Subtype.ext (funext fun i => (Fintype.equivFin Alphabet).injective
    (recovers left right equal i))

private theorem source_exact_exists {Alphabet : Type u} [Finite Alphabet]
    (language : Set (List Alphabet)) (n : Nat) :
    ∃ depth, SourceExactAtDepth (@coordinateReadout Alphabet language n) depth := by
  let _ : Fintype Alphabet := Fintype.ofFinite Alphabet
  obtain ⟨depth, exactAtDepth⟩ := protocol_exists language n
  exact ⟨depth, (source_exact_iff (Fintype.equivFin Alphabet) coordinateReadout).mpr exactAtDepth⟩

/-- Hussain's minimum deterministic recognition depth, including zero for the empty promise. -/
noncomputable def recognitionDepth {Alphabet : Type u} [Fintype Alphabet]
    (language : Set (List Alphabet)) (n : Nat) : Nat := by
  classical
  exact Nat.find (source_exact_exists language n)

private theorem recognitionDepth_eq_adaptiveIdentificationDepth
    {Alphabet : Type u} [Fintype Alphabet] (language : Set (List Alphabet)) (n : Nat) :
    recognitionDepth language n =
      adaptiveIdentificationDepth (fun (i : Fin n) (word : Promise language n) =>
        Fintype.equivFin Alphabet (coordinateReadout i word)) (protocol_exists language n) := by
  classical
  let bridge (depth : Nat) := @source_exact_iff Alphabet (Fin n) (Promise language n)
    (Fintype.card Alphabet) depth (Fintype.equivFin Alphabet) coordinateReadout
  apply Nat.le_antisymm
  · exact Nat.find_min' (source_exact_exists language n)
      ((bridge _).mpr (Nat.find_spec (protocol_exists language n)))
  · exact Nat.find_min' (protocol_exists language n)
      ((bridge _).mp (Nat.find_spec (source_exact_exists language n)))

/-- Downward closure for scattered subwords. -/
def SubwordClosed {Alphabet : Type u} (language : Set (List Alphabet)) : Prop :=
  ∀ ⦃small large⦄, small <+ large → large ∈ language → small ∈ language

/-- Exponents used to define Hom, including exponent zero whenever its pattern occurs. -/
def HomExponents {Alphabet : Type u} (language : Set (List Alphabet)) : Set Nat :=
  {e | ∃ a b, a ≠ b ∧ (List.replicate e a ++ [b] ++ List.replicate e a) ∈ language}

/-- Exponents used to define Het, including exponent zero whenever its pattern occurs. -/
def HetExponents {Alphabet : Type u} (language : Set (List Alphabet)) : Set Nat :=
  {e | ∃ a b, a ≠ b ∧ (List.replicate e a ++ List.replicate e b) ∈ language}

private theorem exists_replicate_sublist {Alphabet : Type u} [Fintype Alphabet]
    (word : List Alphabet) (bound : Nat) (long : Fintype.card Alphabet * bound < word.length) :
    ∃ letter : Alphabet, List.replicate (bound + 1) letter <+ word := by
  classical
  by_contra! none
  have countBound (a : Alphabet) : word.count a ≤ bound := by
    have noReplicate := none a
    rw [List.replicate_sublist_iff] at noReplicate
    omega
  have lengthBound : word.length ≤ Fintype.card Alphabet * bound := by
    calc
      word.length = ∑ a ∈ word.toFinset, word.count a := (List.sum_toFinset_count_eq_length _).symm
      _ ≤ ∑ _a ∈ word.toFinset, bound := Finset.sum_le_sum (fun a _ => countBound a)
      _ = word.toFinset.card * bound := by simp
      _ ≤ Fintype.card Alphabet * bound :=
        Nat.mul_le_mul_right bound (Finset.card_le_univ _)
  exact (not_lt_of_ge lengthBound) long

private theorem middle_pair_equal {Alphabet : Type u} [Fintype Alphabet]
    {language : Set (List Alphabet)} (closed : SubwordClosed language) (m h : Nat)
    (hom : ∀ e ∈ HomExponents language, e ≤ m)
    (het : ∀ e ∈ HetExponents language, e ≤ h)
    (before suffix : List Alphabet) (left right : Alphabet)
    (prefixLong : Fintype.card Alphabet * max m h < before.length)
    (suffixLong : Fintype.card Alphabet * max m h < suffix.length)
    (accepted : before ++ (left :: right :: suffix) ∈ language) :
    left = right := by
  obtain ⟨a, prefixCopies⟩ := exists_replicate_sublist before (max m h) prefixLong
  obtain ⟨b, suffixCopies⟩ := exists_replicate_sublist suffix (max m h) suffixLong
  have shrink (e : Nat) (leMax : e ≤ max m h) (letter : Alphabet) :
      List.replicate (e + 1) letter <+ List.replicate (max m h + 1) letter :=
    (List.replicate_sublist_replicate letter).mpr (Nat.succ_le_succ leMax)
  have same : a = b := by
    by_contra different
    have hetPattern : List.replicate (h + 1) a ++ List.replicate (h + 1) b <+
        before ++ (left :: right :: suffix) :=
      ((shrink h (le_max_right _ _) a).trans prefixCopies).append
        (((shrink h (le_max_right _ _) b).trans suffixCopies).cons _ |>.cons _)
    exact (Nat.not_succ_le_self h) (het _ ⟨a, b, different, closed hetPattern accepted⟩)
  subst b
  have prefixHom := (shrink m (le_max_left _ _) a).trans prefixCopies
  have suffixHom := (shrink m (le_max_left _ _) a).trans suffixCopies
  have force (middle : Alphabet) (hit : middle ∈ [left, right]) : middle = a := by
    by_contra different
    have singleton : [middle] <+ [left, right] := List.singleton_sublist.mpr hit
    have homPattern : List.replicate (m + 1) a ++ [middle] ++ List.replicate (m + 1) a <+
        before ++ (left :: right :: suffix) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (prefixHom.append singleton).append suffixHom
    exact (Nat.not_succ_le_self m)
      (hom _ ⟨a, middle, (fun equal => different equal.symm), closed homPattern accepted⟩)
  exact (force left (by simp)).trans (force right (by simp)).symm

private theorem common_adjacent_coordinate {Alphabet : Type u} [Fintype Alphabet]
    {language : Set (List Alphabet)} (closed : SubwordClosed language) (m h : Nat)
    (hom : ∀ e ∈ HomExponents language, e ≤ m)
    (het : ∀ e ∈ HetExponents language, e ≤ h) :
    let cut := Fintype.card Alphabet * max m h + 1
    ∀ n, 2 * cut + 1 ≤ n →
      ∀ (i : Fin n), i.val = cut →
        ∀ word : Promise language (n + 1), word.val i.castSucc = word.val i.succ := by
  dsimp only
  intro n long i atCut word
  let letters := List.ofFn word.val
  have length : letters.length = n + 1 := List.length_ofFn
  have leftExists : i.val < letters.length := by omega
  have rightExists : i.val + 1 < letters.length := by omega
  have split : letters = letters.take i.val ++
      (letters[i.val] :: letters[i.val + 1] :: letters.drop (i.val + 2)) := by
    have splitAt := (List.take_append_drop i.val letters).symm
    rw [List.drop_eq_getElem_cons leftExists, List.drop_eq_getElem_cons rightExists] at splitAt
    exact splitAt
  have prefixLength : Fintype.card Alphabet * max m h < (letters.take i.val).length := by
    rw [List.length_take_of_le (Nat.le_of_lt leftExists)]
    omega
  have suffixLength : Fintype.card Alphabet * max m h < (letters.drop (i.val + 2)).length := by
    rw [List.length_drop, length]
    omega
  have both : letters[i.val] = letters[i.val + 1] :=
    middle_pair_equal closed m h hom het _ _ _ _ prefixLength suffixLength
      (split ▸ word.property)
  rw [List.getElem_ofFn, List.getElem_ofFn] at both
  exact both

/-- Precompose every query with the state map, retaining each answer branch. -/
private def pullbackProtocol {LongState : Type u} {ShortState : Type v} {B depth : Nat}
    (stateMap : LongState → ShortState) :
    AdaptiveProtocol ShortState B depth → AdaptiveProtocol LongState B depth
  | .leaf => .leaf
  | .query question next =>
      .query (fun state => question (stateMap state))
        (fun answer => pullbackProtocol stateMap (next answer))

/-- A readout-preserving map of queries pulls an exact protocol back at the same depth. -/
private theorem exactAtDepth_pullback
    {LongState : Type u} {ShortState : Type v} {LongQuery : Type w} {ShortQuery : Type x}
    {B depth : Nat}
    {longReadout : LongQuery → LongState → Fin B}
    {shortReadout : ShortQuery → ShortState → Fin B}
    (stateMap : LongState → ShortState) (queryMap : ShortQuery → LongQuery)
    (stateMap_injective : Function.Injective stateMap)
    (readout_eq : ∀ query state,
      shortReadout query (stateMap state) = longReadout (queryMap query) state)
    (short_exact : ExactAtDepth shortReadout depth) :
    ExactAtDepth longReadout depth := by
  have pullback_spec {remaining : Nat} (protocol : AdaptiveProtocol ShortState B remaining)
      (allowed : UsesReadoutFamily shortReadout protocol) :
      UsesReadoutFamily longReadout (pullbackProtocol stateMap protocol) ∧
        ∀ state, adaptiveTranscript (pullbackProtocol stateMap protocol) state =
          adaptiveTranscript protocol (stateMap state) := by
    induction protocol with
    | leaf =>
        exact ⟨trivial, fun _ => rfl⟩
    | query question next ih =>
        rcases allowed with ⟨⟨selected, rfl⟩, allowedNext⟩
        constructor
        · exact ⟨⟨queryMap selected, funext (readout_eq selected)⟩,
            fun answer => (ih answer (allowedNext answer)).1⟩
        · intro state
          simp only [pullbackProtocol, adaptiveTranscript]
          let answer := shortReadout selected (stateMap state)
          exact congrArg (List.cons answer) ((ih answer (allowedNext answer)).2 state)
  obtain ⟨protocol, allowed, transcript_injective⟩ := short_exact
  obtain ⟨pulled_allowed, transcript_eq⟩ := pullback_spec protocol allowed
  refine ⟨pullbackProtocol stateMap protocol, pulled_allowed, ?_⟩
  intro left right sameTranscript
  apply stateMap_injective
  apply transcript_injective
  exact (transcript_eq left).symm.trans (sameTranscript.trans (transcript_eq right))

private theorem delete_subword {Alphabet : Type u} {n : Nat}
    (word : Fin (n + 1) → Alphabet) (i : Fin (n + 1)) :
    List.ofFn (i.removeNth word) <+ List.ofFn word := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  let short := Fin.castOrderIso (List.length_ofFn (f := i.removeNth word))
  let long := Fin.castOrderIso (List.length_ofFn (f := word))
  refine ⟨short.toOrderEmbedding.trans (i.succAboveOrderEmb.trans long.symm.toOrderEmbedding), ?_⟩
  intro j
  simp only [List.get_ofFn, Fin.removeNth_apply]
  rfl

private theorem exactAtDepth_deleteAdjacentEqual {Alphabet : Type u} [Fintype Alphabet]
    {language : Set (List Alphabet)} {n depth : Nat}
    (closed : SubwordClosed language) (i : Fin n)
    (adjacent : ∀ word : Promise language (n + 1), word.val i.castSucc = word.val i.succ)
    (shortExact : ExactAtDepth (fun (j : Fin n) (word : Promise language n) =>
      Fintype.equivFin Alphabet (coordinateReadout j word)) depth) :
    ExactAtDepth (fun (j : Fin (n + 1)) (word : Promise language (n + 1)) =>
      Fintype.equivFin Alphabet (coordinateReadout j word)) depth := by
  let delete (word : Promise language (n + 1)) : Promise language n :=
    ⟨i.succ.removeNth word.val, closed (delete_subword word.val i.succ) word.property⟩
  let restore (word : Fin n → Alphabet) : Fin (n + 1) → Alphabet :=
    i.succ.insertNth (word i) word
  have restore_delete (word : Promise language (n + 1)) : restore (delete word).val = word.val := by
    have retained_eq : i.succ.removeNth word.val i = word.val i.succ := by
      rw [Fin.removeNth_apply, Fin.succAbove_succ_self]
      exact adjacent word
    change i.succ.insertNth (i.succ.removeNth word.val i) (i.succ.removeNth word.val) = word.val
    rw [retained_eq]
    exact Fin.insertNth_self_removeNth i.succ word.val
  have delete_injective : Function.Injective delete := by
    intro left right equal
    apply Subtype.ext
    calc
      left.val = restore (delete left).val := (restore_delete left).symm
      _ = restore (delete right).val := congrArg (fun word => restore word.val) equal
      _ = right.val := restore_delete right
  exact exactAtDepth_pullback delete i.succ.succAbove delete_injective (fun _ _ => rfl) shortExact

private theorem recognitionDepth_succ_le {Alphabet : Type u} [Fintype Alphabet]
    {language : Set (List Alphabet)} {n : Nat}
    (closed : SubwordClosed language) (i : Fin n)
    (adjacent : ∀ word : Promise language (n + 1), word.val i.castSucc = word.val i.succ) :
    recognitionDepth language (n + 1) ≤ recognitionDepth language n := by
  classical
  rw [recognitionDepth_eq_adaptiveIdentificationDepth,
    recognitionDepth_eq_adaptiveIdentificationDepth]
  exact Nat.find_min' (protocol_exists language (n + 1))
    (exactAtDepth_deleteAdjacentEqual closed i adjacent
      (Nat.find_spec (protocol_exists language n)))

/-- The positive resolution of Question 3 with the hypotheses of Theorem 1(c).
The finiteness of the exact exponent sets expresses finite Hom and Het, including the
source's dimension-zero convention for an empty exponent set. -/
def claim : Prop :=
  ∀ (Alphabet : Type u) [Fintype Alphabet] (language : Set (List Alphabet)),
    2 ≤ Fintype.card Alphabet → SubwordClosed language →
    (HomExponents language).Finite → (HetExponents language).Finite →
    ∃ N d : Nat, 1 ≤ N ∧ ∀ n ≥ N, recognitionDepth language n = d

/-- Hussain, arXiv:2611.27454v1, §6, Question 3. -/
theorem result : claim := by
  intro Alphabet _ language _alphabetSize closed finiteHom finiteHet
  obtain ⟨m, hom⟩ := finiteHom.bddAbove
  obtain ⟨h, het⟩ := finiteHet.bddAbove
  let cut := Fintype.card Alphabet * max m h + 1
  let start := 2 * cut + 1
  have antitone : Antitone (fun k : Nat => recognitionDepth language (start + k)) := by
    apply antitone_nat_of_succ_le
    intro k
    let n := start + k
    have long : 2 * cut + 1 ≤ n := by dsimp [n, start]; omega
    have cut_lt : cut < n := by omega
    let i : Fin n := ⟨cut, cut_lt⟩
    exact recognitionDepth_succ_le closed i
      (common_adjacent_coordinate closed m h hom het n long i rfl)
  obtain ⟨first, stable⟩ := WellFoundedLT.antitone_chain_condition antitone
  refine ⟨start + first, recognitionDepth language (start + first), ?_, ?_⟩
  · dsimp [start]
    omega
  · intro n atLeast
    have after : first ≤ n - start := by omega
    have shift : start + (n - start) = n := by omega
    have equal := (stable (n - start) after).symm
    rwa [shift] at equal

end D5.S3.Observer.Budget.HussainRecognitionDepth
