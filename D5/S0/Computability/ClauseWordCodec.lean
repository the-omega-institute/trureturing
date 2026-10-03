/- GID: D5/S0/Computability/ClauseWordCodec
   generality: G
   mirror-B: D5/B/S0/Computability/ClauseWordCodec
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S0/Computability/ClausePreprocessorRefinement.pre_word_run; instance=D5/S0/Computability/ClauseQueryPreprocessor.dummyQuery
   digest: Total raw-word decoding of explicit-universe clauses and succinct physical queries. -/

import D5.S0.Computability.ClauseQueryPreprocessor

/-!
The total raw-word recognizer is checker infrastructure. The actual all-input
preprocessor refinement uses its soundness on accepted source words and on the
machine's exact physical-query output. Its malformed branch concretely checks
dummyQuery and applies soundness to identify the complete zero-variable,
one-empty-clause encoding. This is the valid fallback required for raw source
rejection, and also preserves the valid source with that same query.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic.ClauseCodec

def readUnary : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readUnary rest).map (fun r => (r.1 + 1, r.2))

/-- The budget is a fixed three-literal syntax bound, not an input-sized state. -/
def readClause (n : Nat) : Nat → List Bool →
    Option (Std.Sat.CNF.Clause (Fin n) × List Bool)
  | _, true :: false :: rest => some ([], rest)
  | budget + 1, true :: true :: polarity :: rest => do
      let (i, rest) ← readUnary rest
      if h : i < n then
        let (c, tail) ← readClause n budget rest
        some ((⟨i, h⟩, polarity) :: c, tail)
      else none
  | _, _ => none

def readTerm (n : Nat) (physical : Bool) (w : List Bool) :
    Option (Std.Sat.CNF.Clause (Fin n) × List Bool) := do
  let rest ← if physical then do
    let (coefficient, rest) ← readUnary w
    if coefficient = n + 1 then some rest else none
  else some w
  readClause n 3 rest

def readBody (n : Nat) (physical : Bool) : Nat → List Bool → Option (UnaryFormula n)
  | 0, _ => none
  | _ + 1, [false, false] => some []
  | fuel + 1, false :: true :: rest => do
      let (c, tail) ← readTerm n physical rest
      let F ← readBody n physical fuel tail
      some (c :: F)
  | _, _ => none

def readFixed : List Bool → List Bool → Option (List Bool)
  | [], w => some w
  | a :: tag, b :: w => if a = b then readFixed tag w else none
  | _, [] => none

def readWord (physical : Bool) (w : List Bool) : Option (Σ n, UnaryFormula n) := do
  let rest ← readFixed (if physical then [true, true] else []) w
  let (n, rest) ← readUnary rest
  let rest ← readFixed (if physical then [false, false, false, true] else []) rest
  let F ← readBody n physical (rest.length + 1) rest
  some ⟨n, F⟩

def termWord {n : Nat} (physical : Bool) (c : Std.Sat.CNF.Clause (Fin n)) : List Bool :=
  (if physical then List.replicate (n + 1) true ++ [false] else []) ++
    c.flatMap unaryLiteral ++ [true, false]

def bodyWord {n : Nat} (physical : Bool) (F : UnaryFormula n) : List Bool :=
  F.flatMap (fun c => [false, true] ++ termWord physical c) ++ [false, false]

def encodeWord {n : Nat} (physical : Bool) (F : UnaryFormula n) : List Bool :=
  (if physical then [true, true] else []) ++ List.replicate n true ++ [false] ++
    (if physical then [false, false, false, true] else []) ++ bodyWord physical F

/-- Both decoders accept precisely the raw clauses of width at most three.
No validity witness is supplied by the caller; the word determines the universe,
literal indices, coefficients, clauses and complete framing. -/
theorem codec_exact (physical : Bool) (w : List Bool) (n : Nat) (F : UnaryFormula n) :
    readWord physical w = some ⟨n, F⟩ ↔
      w = encodeWord physical F ∧ ∀ c ∈ F, c.length ≤ 3 := by
  have unary : ∀ w i rest, readUnary w = some (i, rest) ↔
      w = List.replicate i true ++ false :: rest := by
    intro w
    induction w with
    | nil => intro i rest; simp [readUnary]
    | cons b w ih =>
      intro i rest
      cases b
      · cases i <;> simp [readUnary, List.replicate_succ]
      · cases i with
        | zero => simp [readUnary, Option.map_eq_some_iff]
        | succ i =>
          simp only [readUnary, Option.map_eq_some_iff]
          constructor
          · rintro ⟨⟨j, tail⟩, h, e⟩
            have : j = i ∧ tail = rest := by simpa using e
            rcases this with ⟨rfl, rfl⟩
            simpa [List.replicate_succ] using (ih _ _).mp h
          · intro h
            refine ⟨(i, rest), (ih i rest).mpr ?_, rfl⟩
            simpa [List.replicate_succ] using h
  have clause : ∀ budget w (c : Std.Sat.CNF.Clause (Fin n)) rest,
      readClause n budget w = some (c, rest) ↔
        w = c.flatMap unaryLiteral ++ [true, false] ++ rest ∧ c.length ≤ budget := by
    intro budget
    induction budget with
    | zero =>
      intro w c rest
      cases c with
      | nil => cases w with
        | nil => simp [readClause]
        | cons b w => cases b <;> cases w with
          | nil => simp [readClause]
          | cons b w => cases b <;> simp [readClause]
      | cons l c =>
        have h : ¬ (l :: c).length ≤ 0 := by simp
        simp only [h, and_false, iff_false]
        cases w with
        | nil => simp [readClause]
        | cons b w => cases b <;> cases w with
          | nil => simp [readClause]
          | cons b w => cases b <;> simp [readClause]
    | succ budget ih =>
      intro w c rest
      constructor
      · intro h
        cases w with
        | nil => simp [readClause] at h
        | cons b w => cases b with
          | false => simp [readClause] at h
          | true => cases w with
            | nil => simp [readClause] at h
            | cons b w => cases b with
              | false =>
                simp only [readClause, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                simp
              | true => cases w with
                | nil => simp [readClause] at h
                | cons p w =>
                  cases hu : readUnary w with
                  | none => simp [readClause, hu] at h
                  | some r =>
                    rcases r with ⟨i, tail⟩
                    by_cases hi : i < n
                    · cases hc : readClause n budget tail with
                      | none => simp [readClause, hu, hi, hc] at h
                      | some r =>
                        rcases r with ⟨d, tail'⟩
                        simp [readClause, hu, hi, hc, bind, Option.bind] at h
                        rcases h with ⟨rfl, rfl⟩
                        obtain ⟨hw, hd⟩ := (ih tail d tail').mp hc
                        rw [(unary w i tail).mp hu, hw]
                        simp [unaryLiteral, List.append_assoc, hd, Nat.succ_le_succ_iff]
                    · simp [readClause, hu, hi] at h
      · rintro ⟨rfl, width⟩
        cases c with
        | nil => simp [readClause]
        | cons l c =>
          rcases l with ⟨i, p⟩
          have tailWidth : c.length ≤ budget := by simp only [List.length_cons] at width; omega
          have hu := (unary (List.replicate i.val true ++ false ::
            (c.flatMap unaryLiteral ++ [true, false] ++ rest)) i.val
            (c.flatMap unaryLiteral ++ [true, false] ++ rest)).mpr rfl
          have hc := (ih _ c rest).mpr ⟨rfl, tailWidth⟩
          simp only [List.cons_append, List.nil_append, List.append_assoc] at hu hc
          simp [unaryLiteral, List.append_assoc, readClause, hu, i.isLt, hc]
  have term : ∀ w c rest, readTerm n physical w = some (c, rest) ↔
      w = termWord physical c ++ rest ∧ c.length ≤ 3 := by
    intro w c rest
    cases physical with
    | false => simpa [readTerm, termWord, List.append_assoc] using clause 3 w c rest
    | true =>
      simp only [readTerm, Bool.true_eq, ↓reduceIte, bind, Option.bind]
      cases hu : readUnary w with
      | none =>
        simp only [hu, bind, Option.bind, reduceCtorEq, false_iff, not_and]
        intro hw
        have : readUnary w = some (n + 1, c.flatMap unaryLiteral ++ [true, false] ++ rest) :=
          (unary _ _ _).mpr (by simpa [termWord, List.append_assoc] using hw)
        rw [hu] at this
        contradiction
      | some r =>
        rcases r with ⟨i, tail⟩
        by_cases hi : i = n + 1
        · subst i
          simp only [bind, Option.bind, Prod.fst, Prod.snd, ↓reduceIte]
          rw [clause]
          have hw := (unary _ _ _).mp hu
          simp only [termWord, Bool.true_eq, ↓reduceIte, List.append_assoc]
          rw [hw]
          simp
        · simp only [bind, Option.bind, Prod.fst, Prod.snd, hi, ↓reduceIte,
            reduceCtorEq, false_iff, not_and]
          intro hw
          have : readUnary w = some (n + 1, c.flatMap unaryLiteral ++ [true, false] ++ rest) :=
            (unary _ _ _).mpr (by simpa [termWord, List.append_assoc] using hw)
          rw [hu] at this
          simp only [Option.some.injEq, Prod.mk.injEq] at this
          exact False.elim (hi this.1)
  have bodySound : ∀ fuel w F, readBody n physical fuel w = some F →
      w = bodyWord physical F ∧ ∀ c ∈ F, c.length ≤ 3 := by
    intro fuel
    induction fuel with
    | zero => intro w F h; simp [readBody] at h
    | succ fuel ih =>
      intro w F h
      cases w with
      | nil => simp [readBody] at h
      | cons b w => cases b with
        | true => simp [readBody] at h
        | false => cases w with
          | nil => simp [readBody] at h
          | cons b w => cases b with
            | false => cases w with
              | nil => simp only [readBody, Option.some.injEq] at h; subst F; simp [bodyWord]
              | cons b w => simp [readBody] at h
            | true =>
              cases ht : readTerm n physical w with
              | none => simp [readBody, ht] at h
              | some r =>
                rcases r with ⟨c, rest⟩
                cases hb : readBody n physical fuel rest with
                | none => simp [readBody, ht, hb] at h
                | some G =>
                  simp [readBody, ht, hb, bind, Option.bind] at h
                  subst F
                  obtain ⟨hw, hc⟩ := (term w c rest).mp ht
                  obtain ⟨hr, hG⟩ := ih rest G hb
                  constructor
                  · simp [bodyWord, hw, hr, List.append_assoc]
                  · simpa using And.intro hc hG
  have bodyComplete : ∀ F fuel, F.length < fuel → (∀ c ∈ F, c.length ≤ 3) →
      readBody n physical fuel (bodyWord physical F) = some F := by
    intro F
    induction F with
    | nil => intro fuel hf hw; cases fuel <;> simp_all [readBody, bodyWord]
    | cons c F ih =>
      intro fuel hf hw
      cases fuel with
      | zero => omega
      | succ fuel =>
        have ht := (term (termWord physical c ++ bodyWord physical F) c
          (bodyWord physical F)).mpr ⟨rfl, hw c (by simp)⟩
        have hF := ih fuel (by simp only [List.length_cons] at hf; omega)
          (fun d hd => hw d (by simp [hd]))
        rw [show bodyWord physical (c :: F) =
          false :: true :: (termWord physical c ++ bodyWord physical F) by
            simp [bodyWord, List.append_assoc]]
        simp [readBody, ht, hF, bind, Option.bind]
  have bodyLength : ∀ F : UnaryFormula n, F.length < (bodyWord physical F).length + 1 := by
    intro F
    induction F with
    | nil => simp [bodyWord]
    | cons c F ih =>
      simp only [bodyWord, List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil] at ih ⊢
      omega
  have finish : ∀ rest, readBody n physical (rest.length + 1) rest = some F ↔
      rest = bodyWord physical F ∧ ∀ c ∈ F, c.length ≤ 3 := by
    intro rest
    constructor
    · exact bodySound _ _ _
    · rintro ⟨rfl, hw⟩; exact bodyComplete F _ (bodyLength F) hw
  have fixed : ∀ tag w rest, readFixed tag w = some rest ↔ w = tag ++ rest := by
    intro tag
    induction tag with
    | nil => intro w rest; simp [readFixed]
    | cons a tag ih =>
      intro w rest
      cases w with
      | nil => simp [readFixed]
      | cons b w =>
        by_cases h : a = b
        · subst b; simp [readFixed, ih]
        · simp [readFixed, h, Ne.symm h]
  let tag := if physical then [true, true] else []
  let marker := if physical then [false, false, false, true] else []
  change (do
    let rest ← readFixed tag w
    let (j, rest) ← readUnary rest
    let rest ← readFixed marker rest
    let G ← readBody j physical (rest.length + 1) rest
    some (⟨j, G⟩ : Σ n, UnaryFormula n)) = some ⟨n, F⟩ ↔ _
  constructor
  · intro h
    cases h0 : readFixed tag w with
    | none => simp [h0] at h
    | some v =>
      cases h1 : readUnary v with
      | none => simp [h0, h1] at h
      | some r =>
        rcases r with ⟨j, rest⟩
        cases h2 : readFixed marker rest with
        | none => simp [h0, h1, h2] at h
        | some tail =>
          cases h3 : readBody j physical (tail.length + 1) tail with
          | none => simp [h0, h1, h2, h3] at h
          | some G =>
            simp [h0, h1, h2, h3, bind, Option.bind] at h
            rcases h with ⟨hn, hF⟩
            subst j
            have he : G = F := eq_of_heq hF
            subst G
            obtain ⟨ht, hw⟩ := (finish tail).mp h3
            refine ⟨?_, hw⟩
            rw [(fixed _ _ _).mp h0, (unary _ _ _).mp h1, (fixed _ _ _).mp h2, ht]
            simp [encodeWord, tag, marker, List.append_assoc]
  · rintro ⟨rfl, width⟩
    have h0 : readFixed tag (encodeWord physical F) =
        some (List.replicate n true ++ false :: (marker ++ bodyWord physical F)) :=
      (fixed _ _ _).mpr (by simp [encodeWord, tag, marker, List.append_assoc])
    have h1 := (unary (List.replicate n true ++ false :: (marker ++ bodyWord physical F))
      n (marker ++ bodyWord physical F)).mpr rfl
    have h2 := (fixed marker (marker ++ bodyWord physical F) (bodyWord physical F)).mpr rfl
    have h3 := (finish (bodyWord physical F)).mpr ⟨rfl, width⟩
    simp [h0, h1, h2, h3, bind, Option.bind]

end PredictiveThermodynamic.ClauseCodec
