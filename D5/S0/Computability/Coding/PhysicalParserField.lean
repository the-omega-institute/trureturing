/- GID: D5/S0/Computability/Coding/PhysicalParserField
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/PhysicalParserField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Size]
   utility: none
   digest: Physical header allocation and backwards payload copy with paid synchronized tallies. -/

import D5.S0.Computability.Coding.PhysicalParserTally

namespace D5.S0.Computability.Coding.PhysicalParserField

open PhysicalSixParser

/-- Only the selected buffer is replaced in this proof-side frame. -/
def memory (m : Track → ℤ → Bool) (i : Fin 6) (bs : List Bool) : Track → ℤ → Bool :=
  fun (p,b) => if p = parameterPair i then wordCell bs b else m (p,b)

/-- Raw and selected-buffer coordinates at a stable parse boundary. -/
def heads (h : Track → ℤ) (i : Fin 6) (n : ℕ) (j : ℤ) : Track → ℤ :=
  fun t => if t = (0,false) then n + 1
    else if t.1 = parameterPair i then j else h t

/-- Stable equality of tallies is specification data, unavailable to control. -/
def configuration (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6)
    (n : ℕ) (bs : List Bool) (j : ℤ) (c : Control) : Configuration :=
  PhysicalParserTally.configuration (memory m i bs) (heads h i n j) n n.bits 0 c

/-- Source cells and unused tracks are literal frames throughout parsing. -/
def Frame (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6) (N : ℕ)
    (c : Configuration) : Prop :=
  (∀ t : Track, t.1 ≠ parameterPair i → t.1 ≠ 7 → t.1 ≠ 8 → c.cell t = m t) ∧
  (∀ t : Track, t ≠ (0,false) → t.1 ≠ parameterPair i → t.1 ≠ 7 → t.1 ≠ 8 →
    c.head t = h t) ∧
  (∀ t : Track, t = (0,false) ∨ t.1 = parameterPair i ∨ t.1 = 7 ∨ t.1 = 8 →
    0 ≤ c.head t ∧ c.head t ≤ N + 1)

/-- Static continuation after the final home-marker test. -/
def next (i : Fin 6) : Control :=
  if h : i.val < 5 then .header ⟨i.val + 1, by omega⟩ 0 else .count .finish 0

/-- One complete field executes from raw header bits to a little-endian physical buffer. -/
theorem parse_field (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6)
    (n N : ℕ) (payload : List Bool) (hN : n + 2 * payload.length + 1 ≤ N)
    (hraw : ∀ k < 2 * payload.length + 1,
      m (0,false) (n + k + 1) =
        (List.replicate payload.length true ++ false :: payload)[k]?.getD false) :
    ∃ T : ℕ, T ≤ (2 * payload.length + 1) * (8 * N + 20) + 2 ∧
      run (configuration m h i n [] 0 (.header i 0)) T =
        configuration m h i (n + 2 * payload.length + 1) payload.reverse 0 (next i) ∧
      ∀ t ≤ T, Frame m h i N (run (configuration m h i n [] 0 (.header i 0)) t) := by
  have configExt {a b : Configuration} (hc : a.control=b.control)
      (hh : a.head=b.head) (hm : a.cell=b.cell) : a=b := by
    cases a
    cases b
    cases hc
    cases hh
    cases hm
    rfl
  have hi0 : parameterPair i ≠ 0 := by
    intro he; have hv := congrArg Fin.val he
    simp only [parameterPair] at hv; omega
  have hi7 : parameterPair i ≠ 7 := by
    intro he; have hv := congrArg Fin.val he
    simp only [parameterPair] at hv; have := i.isLt; omega
  have hi8 : parameterPair i ≠ 8 := by
    intro he; have hv := congrArg Fin.val he
    simp only [parameterPair] at hv; have := i.isLt; omega
  have h0i := Ne.symm hi0
  have h7i := Ne.symm hi7
  have h8i := Ne.symm hi8
  have bitsBound (a : ℕ) : a.bits.length ≤ a := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self : a < 2 ^ a)
  have safe (a : ℕ) (word : List Bool) (j : ℤ) (c : Control)
      (ha : a ≤ N) (hj : 0 ≤ j) (hjN : j ≤ N + 1) :
      Frame m h i N (configuration m h i a word j c) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨p,b⟩ hpi h7 h8
      simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
        memory, hpi, h7, h8]
    · rintro ⟨p,b⟩ h0 hpi h7 h8
      simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.heads,
        heads, h0, hpi, h7, h8]
    · rintro t (ht | ht | ht | ht)
      · subst t
        simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.heads,
          heads]; omega
      · rcases t with ⟨p,b⟩; dsimp only at ht; subst p; cases b <;>
          simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.heads,
            heads, hi0, hi7, hi8, hj, hjN]
      · rcases t with ⟨p,b⟩; dsimp only at ht; subst p; cases b <;>
          simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.heads,
            heads] <;> omega
      · rcases t with ⟨p,b⟩; dsimp only at ht; subst p; cases b <;>
          simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.heads,
            heads] <;> omega
  have join (a b : ℕ) (x y : Configuration) (he : run x a = y)
      (hx : ∀ t ≤ a, Frame m h i N (run x t))
      (hy : ∀ t ≤ b, Frame m h i N (run y t)) :
      ∀ t ≤ b + a, Frame m h i N (run x t) := by
    intro t ht
    by_cases hta : t ≤ a
    · exact hx t hta
    · have ht' : t = (t - a) + a := by omega
      rw [ht']
      simp only [run, Function.iterate_add_apply]
      change Frame m h i N (run (run x a) (t - a))
      rw [he]
      exact hy _ (by omega)
  have consume (a : ℕ) (word : List Bool) (j : ℤ) (c : Continuation)
      (ha : a + 1 ≤ N) (hj : 0 ≤ j) (hjN : j ≤ N + 1) :
      ∃ T : ℕ, T ≤ 8 * N + 15 ∧
        run (configuration m h i a word j (.consume c)) T =
          configuration m h i (a+1) word j (resume c) ∧
        ∀ t ≤ T, Frame m h i N
          (run (configuration m h i a word j (.consume c)) t) := by
    obtain ⟨T,hT,he,hs⟩ := PhysicalParserTally.count_one
      (memory m i word) (heads h i (a+1) j) a a c
    have entry : run (configuration m h i a word j (.consume c)) 1 =
        PhysicalParserTally.configuration (memory m i word) (heads h i (a+1) j)
          a a.bits 0 (.count c 0) := by
      apply configExt
      · rfl
      · funext t
        rcases t with ⟨p,b⟩
        by_cases h7 : p = 7 <;> by_cases h8 : p = 8 <;>
          by_cases hpi : p = parameterPair i <;> by_cases h0 : p = 0 <;> cases b <;>
          simp [run, step, program, configuration, PhysicalParserTally.configuration,
            PhysicalParserTally.heads, heads, Function.update_apply,
            h7, h8, hpi, h0, hi0, h0i, hi7, h7i, hi8, h8i] <;> omega
      · rfl
    have hs' : ∀ t ≤ T, Frame m h i N
        (run (PhysicalParserTally.configuration (memory m i word)
          (heads h i (a+1) j) a a.bits 0 (.count c 0)) t) := by
      intro t ht
      obtain ⟨hf,hu,hb⟩ := hs t ht
      refine ⟨?_, ?_, ?_⟩
      · intro v hpi h7 h8
        simpa [memory, hpi] using (hf v h7 h8).2
      · intro v h0 hpi h7 h8
        simpa [heads, h0, hpi] using (hf v h7 h8).1
      · rintro v (hv | hv | hv | hv)
        · subst v
          rw [(hf (0,false) (by decide) (by decide)).1]
          simp [heads]; omega
        · rcases v with ⟨p,b⟩; dsimp only at hv; subst p
          rw [(hf (parameterPair i,b) hi7 hi8).1]
          cases b <;> simp [heads, hi0, hj, hjN]
        · rcases v with ⟨p,b⟩; dsimp only at hv; subst p
          obtain ⟨hl,hh⟩ := hu b
          constructor <;> omega
        · rcases v with ⟨p,b⟩; dsimp only at hv; subst p
          obtain ⟨hl,hh⟩ := hb b
          have hab := bitsBound a
          constructor <;> omega
    have first : ∀ t ≤ 1, Frame m h i N
        (run (configuration m h i a word j (.consume c)) t) := by
      intro t ht
      interval_cases t
      · exact safe a word j (.consume c) (by omega) hj hjN
      · rw [entry]
        exact hs' 0 (by omega)
    refine ⟨T+1, by have := bitsBound a; omega, ?_, ?_⟩
    · change run (run (configuration m h i a word j (.consume c)) 1) T = _
      rw [entry]
      exact he
    · exact join 1 T _ _ entry first hs'
  have extend (bs : List Bool) (v b : Bool) :
      wordCell (bs ++ [v]) b =
        Function.update (wordCell bs b) (bs.length + 1) (if b then v else true) := by
    funext z
    by_cases hz : z = (bs.length : ℤ) + 1
    · subst z
      have hp : 0 < (bs.length : ℤ) + 1 := by omega
      cases b <;> simp [wordCell, ne_of_gt hp, hp, Function.update_apply, List.getElem?_append]
    · have hz' : (bs.length : ℤ) + 1 ≠ z := Ne.symm hz
      simp only [Function.update_of_ne hz]
      cases b <;> by_cases h0 : z = 0 <;> by_cases hp : 0 < z <;>
        simp [wordCell, h0, hp, List.getElem?_append]
      · congr 1
        omega
      · have hn : z.toNat - 1 ≠ bs.length := by omega
        by_cases hl : z.toNat - 1 < bs.length
        · simp [hl]
        · have hg : bs.length < z.toNat - 1 := by omega
          have he : bs[z.toNat - 1]? = none := List.getElem?_eq_none (by omega)
          have he2 : [v][z.toNat - 1 - bs.length]? = none :=
            List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
          simp [hl, he2, he]
  have replace (pre suf : List Bool) (a v b : Bool) :
      wordCell (pre ++ v :: suf) b =
        if b then Function.update (wordCell (pre ++ a :: suf) true) (pre.length + 1) v
        else wordCell (pre ++ a :: suf) false := by
    cases b
    · funext z
      simp [wordCell]
    · funext z
      by_cases hz : z = (pre.length : ℤ) + 1
      · subst z
        have hp : 0 < (pre.length : ℤ) + 1 := by omega
        simp [wordCell, ne_of_gt hp, hp, Function.update_apply, List.getElem?_append]
      · have hz' : (pre.length : ℤ) + 1 ≠ z := Ne.symm hz
        simp only [Bool.true_eq, ↓reduceIte, Function.update_of_ne hz]
        by_cases h0 : z = 0 <;> by_cases hp : 0 < z <;>
          simp [wordCell, h0, hp, List.getElem?_append, List.getElem?_cons]
        have hn : z.toNat - 1 ≠ pre.length := by omega
        by_cases hl : z.toNat - 1 < pre.length
        · simp [hl]
        · have hs : z.toNat - 1 - pre.length ≠ 0 := by omega
          simp [hl, hs]

  have appendMemory (a : ℕ) (word : List Bool) :
      Function.update
        (Function.update (PhysicalParserTally.memory (memory m i word) a a.bits)
          (parameterPair i,false) (Function.update (wordCell word false) (word.length+1) true))
        (parameterPair i,true) (Function.update (wordCell word true) (word.length+1) false) =
      PhysicalParserTally.memory (memory m i (word ++ [false])) a a.bits := by
    funext t z
    rcases t with ⟨p,b⟩
    by_cases hp : p = parameterPair i
    · subst p
      cases b
      · simpa [PhysicalParserTally.memory, memory, Function.update_apply, hi7, hi8] using
          congrFun (extend word false false).symm z
      · simpa [PhysicalParserTally.memory, memory, Function.update_apply, hi7, hi8] using
          congrFun (extend word false true).symm z
    · simp [PhysicalParserTally.memory, memory, Function.update_apply, hp]
  have replaceMemory (a : ℕ) (pre done : List Bool) (b : Bool) :
      Function.update (PhysicalParserTally.memory (memory m i (pre ++ false :: done)) a a.bits)
        (parameterPair i,true)
        (Function.update (wordCell (pre ++ false :: done) true) (pre.length+1) b) =
      PhysicalParserTally.memory (memory m i (pre ++ b :: done)) a a.bits := by
    funext t z
    rcases t with ⟨p,v⟩
    by_cases hp : p = parameterPair i
    · subst p
      cases v
      · simpa [PhysicalParserTally.memory, memory, Function.update_apply, hi7, hi8] using
          congrFun (replace pre done false b false).symm z
      · simpa [PhysicalParserTally.memory, memory, Function.update_apply, hi7, hi8] using
          congrFun (replace pre done false b true).symm z
    · simp [PhysicalParserTally.memory, memory, Function.update_apply, hp]
  have headerStep (a : ℕ) (word : List Bool) (ha : a + 1 ≤ N)
      (hw : word.length < N + 1) (hr : m (0,false) (a+1) = true) :
      ∃ T : ℕ, T ≤ 8 * N + 20 ∧
        run (configuration m h i a word word.length (.header i 0)) T =
          configuration m h i (a+1) (word ++ [false]) (word.length+1) (.header i 0) ∧
        ∀ t ≤ T, Frame m h i N
          (run (configuration m h i a word word.length (.header i 0)) t) := by
    have micro : run (configuration m h i a word word.length (.header i 0)) 5 =
        configuration m h i a (word ++ [false]) (word.length+1) (.consume (.header i)) := by
      simp only [run, show 5 = 1+1+1+1+1 from rfl,
        Function.iterate_succ_apply, Function.iterate_zero_apply]
      apply configExt
      · simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
          PhysicalParserTally.heads, memory, heads, step, program, hr, h0i]
      · simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
          PhysicalParserTally.heads, memory, heads, step, program, hr, h0i]
        funext t
        rcases t with ⟨p,b⟩
        by_cases h7 : p = 7 <;> by_cases h8 : p = 8 <;>
          by_cases hpi : p = parameterPair i <;> by_cases h0 : p = 0 <;> cases b <;>
          simp [PhysicalParserTally.heads, heads, Function.update_apply,
            h7, h8, hpi, h0, hi0, h0i, hi7, h7i, hi8, h8i]
      · simpa [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
          PhysicalParserTally.heads, memory, heads, step, program, hr, h0i, hi0, hi7, hi8,
          Function.update_apply] using appendMemory a word
    have ms : ∀ t ≤ 5, Frame m h i N
        (run (configuration m h i a word word.length (.header i 0)) t) := by
      intro t ht
      interval_cases t <;>
        simp [run, Function.iterate_succ_apply, configuration,
          PhysicalParserTally.configuration, PhysicalParserTally.memory,
          PhysicalParserTally.heads, memory, heads, step, program, hr,
          hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply] <;> refine ⟨?_, ?_, ?_⟩
      all_goals solve
        | (rintro ⟨p,b⟩ hpi h7 h8
           simp [run, Function.iterate_succ_apply, configuration,
             PhysicalParserTally.configuration, PhysicalParserTally.memory,
             PhysicalParserTally.heads, memory, heads, step, program, hr,
             hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply, hpi, h7, h8])
        | (rintro ⟨p,b⟩ h0 hpi h7 h8
           simp [run, Function.iterate_succ_apply, configuration,
             PhysicalParserTally.configuration, PhysicalParserTally.memory,
             PhysicalParserTally.heads, memory, heads, step, program, hr,
             hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply, h0, hpi, h7, h8])
        | (rintro ⟨p,b⟩ (ht | ht | ht | ht)
           all_goals
             simp only [Prod.mk.injEq] at ht
             first | (rcases ht with ⟨rfl,rfl⟩) | subst p
             try cases b
             all_goals
               simp [run, Function.iterate_succ_apply, configuration,
                 PhysicalParserTally.configuration, PhysicalParserTally.memory,
                 PhysicalParserTally.heads, memory, heads, step, program, hr,
                 hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply] <;> omega)
    obtain ⟨T,hT,he,hs⟩ := consume a (word ++ [false]) (word.length+1) (.header i)
      ha (by omega) (by omega)
    refine ⟨T+5, by omega, ?_, join 5 T _ _ micro ms hs⟩
    change run (run (configuration m h i a word word.length (.header i 0)) 5) T = _
    rw [micro]
    exact he
  have payloadStep (a : ℕ) (pre done : List Bool) (b : Bool) (ha : a + 1 ≤ N)
      (hw : pre.length + 1 ≤ N + 1) (hr : m (0,false) (a+1) = b) :
      ∃ T : ℕ, T ≤ 8 * N + 20 ∧
        run (configuration m h i a (pre ++ false :: done) (pre.length+1) (.payload i 0)) T =
          configuration m h i (a+1) (pre ++ b :: done) pre.length (.payload i 0) ∧
        ∀ t ≤ T, Frame m h i N
          (run (configuration m h i a (pre ++ false :: done) (pre.length+1) (.payload i 0)) t) := by
    have hp : 0 < (pre.length : ℤ) + 1 := by omega
    have bo : wordCell (pre ++ false :: done) false (pre.length+1) = true := by
      simp [wordCell, hp, ne_of_gt hp]
    have bv : wordCell (pre ++ false :: done) true (pre.length+1) = false := by
      simp [wordCell, hp, ne_of_gt hp, List.getElem?_append]
    have micro : run (configuration m h i a (pre ++ false :: done) (pre.length+1) (.payload i 0)) 5 =
        configuration m h i a (pre ++ b :: done) pre.length (.consume (.payload i)) := by
      simp only [run, show 5 = 1+1+1+1+1 from rfl,
        Function.iterate_succ_apply, Function.iterate_zero_apply]
      apply configExt
      · cases b <;>
          simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
            PhysicalParserTally.heads, memory, heads, step, program, hr, h0i, hi0, hi7, hi8, bo]
      · cases b <;>
          simp [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
            PhysicalParserTally.heads, memory, heads, step, program, hr, h0i, hi0, hi7, hi8, bo]
        all_goals
          funext t
          rcases t with ⟨p,v⟩
          by_cases h7 : p = 7 <;> by_cases h8 : p = 8 <;>
            by_cases hpi : p = parameterPair i <;> by_cases h0 : p = 0 <;> cases v <;>
            simp [PhysicalParserTally.heads, heads, Function.update_apply,
              h7, h8, hpi, h0, hi0, h0i, hi7, h7i, hi8, h8i]
      · cases b
        · simpa [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
            PhysicalParserTally.heads, memory, heads, step, program, hr, h0i, hi0, hi7, hi8, bo,
            Function.update_apply, bv] using replaceMemory a pre done false
        · simpa [configuration, PhysicalParserTally.configuration, PhysicalParserTally.memory,
            PhysicalParserTally.heads, memory, heads, step, program, hr, h0i, hi0, hi7, hi8, bo,
            Function.update_apply, bv] using replaceMemory a pre done true
    have ms : ∀ t ≤ 5, Frame m h i N
        (run (configuration m h i a (pre ++ false :: done) (pre.length+1) (.payload i 0)) t) := by
      intro t ht
      cases b <;> interval_cases t <;>
        simp [run, Function.iterate_succ_apply, configuration,
          PhysicalParserTally.configuration, PhysicalParserTally.memory,
          PhysicalParserTally.heads, memory, heads, step, program, hr, bo,
          hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply] <;> refine ⟨?_, ?_, ?_⟩
      all_goals solve
        | (rintro ⟨p,v⟩ hpi h7 h8
           simp [run, Function.iterate_succ_apply, configuration,
             PhysicalParserTally.configuration, PhysicalParserTally.memory,
             PhysicalParserTally.heads, memory, heads, step, program, hr, bo,
             hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply, hpi, h7, h8])
        | (rintro ⟨p,v⟩ h0 hpi h7 h8
           simp [run, Function.iterate_succ_apply, configuration,
             PhysicalParserTally.configuration, PhysicalParserTally.memory,
             PhysicalParserTally.heads, memory, heads, step, program, hr, bo,
             hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply, h0, hpi, h7, h8])
        | (rintro ⟨p,v⟩ (ht | ht | ht | ht)
           all_goals
             simp only [Prod.mk.injEq] at ht
             first | (rcases ht with ⟨rfl,rfl⟩) | subst p
             try cases v
             all_goals
               simp [run, Function.iterate_succ_apply, configuration,
                 PhysicalParserTally.configuration, PhysicalParserTally.memory,
                 PhysicalParserTally.heads, memory, heads, step, program, hr, bo,
                 hi0, h0i, hi7, h7i, hi8, h8i, Function.update_apply] <;> omega)
    obtain ⟨T,hT,he,hs⟩ := consume a (pre ++ b :: done) pre.length (.payload i)
      ha (by omega) (by omega)
    refine ⟨T+5, by omega, ?_, join 5 T _ _ micro ms hs⟩
    change run (run (configuration m h i a (pre ++ false :: done)
      (pre.length+1) (.payload i 0)) 5) T = _
    rw [micro]
    exact he
  have headers (k : ℕ) : ∀ a j : ℕ, a+k ≤ N → j+k ≤ N+1 →
      (∀ r < k, m (0,false) (a+r+1) = true) →
      ∃ T : ℕ, T ≤ k * (8*N+20) ∧
        run (configuration m h i a (List.replicate j false) j (.header i 0)) T =
          configuration m h i (a+k) (List.replicate (j+k) false) (j+k) (.header i 0) ∧
        ∀ t ≤ T, Frame m h i N
          (run (configuration m h i a (List.replicate j false) j (.header i 0)) t) := by
    induction k with
    | zero =>
      intro a j ha hj hr
      refine ⟨0, by omega, by simp [run], ?_⟩
      intro t ht
      have : t=0 := by omega
      subst t
      exact safe a _ j _ (by omega) (by omega) (by omega)
    | succ k ih =>
      intro a j ha hj hr
      obtain ⟨T,hT,he,hs⟩ := headerStep a (List.replicate j false)
        (by omega) (by simp; omega) (by simpa using hr 0 (by omega))
      simp only [List.length_replicate, ← List.replicate_succ'] at he hs
      obtain ⟨U,hU,ue,us⟩ := ih (a+1) (j+1) (by omega) (by omega)
        (by intro r hr'; simpa [Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm,
          Int.add_left_comm] using hr (r+1) (by omega))
      refine ⟨U+T, by simp only [Nat.add_mul, Nat.one_mul]; omega, ?_, ?_⟩
      · simp only [run, Function.iterate_add_apply]
        change run (run _ T) U = _
        rw [he]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.cast_add,
          Nat.cast_one, Int.add_assoc, Int.add_comm, Int.add_left_comm] using ue
      · exact join T U _ _ he hs (by simpa only [Nat.cast_add, Nat.cast_one] using us)
  have payloads (rem : List Bool) : ∀ (a : ℕ) (done : List Bool),
      a+rem.length ≤ N → rem.length ≤ N+1 →
      (∀ r < rem.length, m (0,false) (a+r+1) = rem[r]?.getD false) →
      ∃ T : ℕ, T ≤ rem.length * (8*N+20) + 2 ∧
        run (configuration m h i a (List.replicate rem.length false ++ done)
          rem.length (.payload i 0)) T =
          configuration m h i (a+rem.length) (rem.reverse ++ done) 0 (next i) ∧
        ∀ t ≤ T, Frame m h i N
          (run (configuration m h i a (List.replicate rem.length false ++ done)
            rem.length (.payload i 0)) t) := by
    induction rem with
    | nil =>
      intro a done ha hj hr
      refine ⟨2, by simp, ?_, ?_⟩
      · simp [run, Function.iterate_succ_apply, configuration,
          PhysicalParserTally.configuration, PhysicalParserTally.memory,
          PhysicalParserTally.heads, memory, heads, step, program, wordCell, next,
          hi0, hi7, hi8]
      · intro t ht
        interval_cases t <;>
          simpa [Frame, run, Function.iterate_succ_apply, configuration,
            PhysicalParserTally.configuration, PhysicalParserTally.memory,
            PhysicalParserTally.heads, memory, heads, step, program, wordCell, next,
            hi0, hi7, hi8] using safe a done 0 (.payload i 0) (by simpa using ha) (by omega) (by omega)
    | cons b rem ih =>
      intro a done ha hj hr
      obtain ⟨T,hT,he,hs⟩ := payloadStep a (List.replicate rem.length false) done b
        (by simp only [List.length_cons] at ha; omega)
        (by simpa using hj) (by simpa using hr 0 (by simp))
      simp only [List.length_replicate] at he hs
      obtain ⟨U,hU,ue,us⟩ := ih (a+1) (b::done)
        (by simp only [List.length_cons] at ha; omega)
        (by simp only [List.length_cons] at hj; omega)
        (by intro r hr'; simpa [Nat.cast_add, Nat.cast_one, Int.add_assoc,
          Int.add_comm, Int.add_left_comm, List.getElem?_cons] using hr (r+1) (by simp; omega))
      have initEq : List.replicate (b::rem).length false ++ done =
          List.replicate rem.length false ++ false :: done := by
        simp [List.replicate_succ', List.append_assoc]
      refine ⟨U+T, by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega, ?_, ?_⟩
      · rw [initEq]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        simp only [run, Function.iterate_add_apply]
        change run (run _ T) U = _
        rw [he]
        simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ue
      · rw [initEq]
        simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using join T U _ _ he hs us
  obtain ⟨H,hH,he,hs⟩ := headers payload.length n 0 (by omega) (by omega)
    (by
      intro r hr
      have hh := hraw r (by omega)
      simpa [List.getElem?_append, List.getElem?_replicate, hr] using hh)
  simp only [List.replicate_zero, Nat.zero_add, Nat.cast_zero, Int.zero_add] at he hs
  have delimiter : m (0,false) (n + payload.length + 1) = false := by
    have hh := hraw payload.length (by omega)
    simpa [List.getElem?_append] using hh
  have delimRun : run (configuration m h i (n+payload.length)
      (List.replicate payload.length false) payload.length (.header i 0)) 1 =
      configuration m h i (n+payload.length) (List.replicate payload.length false)
        payload.length (.consume (.payload i)) := by
    simp [run, Function.iterate_succ_apply, configuration,
      PhysicalParserTally.configuration, PhysicalParserTally.memory,
      PhysicalParserTally.heads, memory, heads, step, program, delimiter,
      Nat.cast_add, h0i]
  have delimSafe : ∀ t ≤ 1, Frame m h i N
      (run (configuration m h i (n+payload.length)
        (List.replicate payload.length false) payload.length (.header i 0)) t) := by
    intro t ht
    interval_cases t
    · exact safe _ _ _ _ (by omega) (by omega) (by omega)
    · rw [delimRun]
      exact safe _ _ _ _ (by omega) (by omega) (by omega)
  obtain ⟨D,hD,de,ds⟩ := consume (n+payload.length) (List.replicate payload.length false)
    payload.length (.payload i) (by omega) (by omega) (by omega)
  obtain ⟨P,hP,pe,ps⟩ := payloads payload (n+payload.length+1) [] (by omega) (by omega)
    (by
      intro r hr
      have hh := hraw (payload.length+1+r) (by omega)
      simpa [List.getElem?_append, List.getElem?_cons, Nat.cast_add, Nat.cast_one,
        Int.add_assoc, Int.add_comm, Int.add_left_comm,
        show ¬payload.length+1+r < payload.length by omega,
        show payload.length+1+r-payload.length = r+1 by omega] using hh)
  simp only [List.append_nil] at pe ps
  refine ⟨((P+D)+1)+H, ?_, ?_, ?_⟩
  · rw [Nat.two_mul payload.length, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  · simp only [run, Function.iterate_add_apply]
    change run (run (run (run _ H) 1) D) P = _
    rw [he, delimRun, de]
    simpa [resume, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul] using pe
  · have s1 := join D P _ _ de ds (by simpa [resume] using ps)
    have s2 := join 1 (P+D) _ _ delimRun delimSafe s1
    exact join H _ _ _ he hs s2

end D5.S0.Computability.Coding.PhysicalParserField
