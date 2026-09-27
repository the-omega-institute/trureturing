/- GID: D5/S0/Computability/Coding/PhysicalParserTally
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/PhysicalParserTally
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Size]
   utility: none
   digest: Physical unary append and canonical binary increment with a literal tape frame. -/

import D5.S0.Computability.Coding.PhysicalSixParser

namespace D5.S0.Computability.Coding.PhysicalParserTally

open PhysicalSixParser

/-- Specification of the two tally pairs; all other cells retain their original values. -/
def memory (m : Track → ℤ → Bool) (u : ℕ) (bs : List Bool) : Track → ℤ → Bool :=
  fun (p, b) => if p = 7 then wordCell (List.replicate u true) b
    else if p = 8 then wordCell bs b else m (p, b)

/-- Specification of independently positioned component heads. -/
def heads (h : Track → ℤ) (uo uv bo bv : ℤ) : Track → ℤ :=
  fun (p, b) => if p = 7 then if b then uv else uo
    else if p = 8 then if b then bv else bo else h (p, b)

/-- A complete tally boundary configuration, not a runtime data register. -/
def configuration (m : Track → ℤ → Bool) (h : Track → ℤ) (u : ℕ)
    (bs : List Bool) (p : ℤ) (c : Control) : Configuration :=
  ⟨c, heads h u u p p, memory m u bs⟩

/-- Bounds and literal framing through partial tally writes and moves. -/
def Frame (m : Track → ℤ → Bool) (h : Track → ℤ) (u L : ℕ)
    (c : Configuration) : Prop :=
  (∀ t : Track, t.1 ≠ 7 → t.1 ≠ 8 → c.head t = h t ∧ c.cell t = m t) ∧
  (∀ b, (u : ℤ) ≤ c.head (7, b) ∧ c.head (7, b) ≤ u + 1) ∧
  (∀ b, 0 ≤ c.head (8, b) ∧ c.head (8, b) ≤ L + 1)

/-- The shared routine physically appends one mark and increments the binary counter.
Both counters are allowed arbitrary initial values so equality is obtained at stable boundaries
by starting with equal values. All other tapes and heads are literal frames. -/
theorem count_one (m : Track → ℤ → Bool) (h : Track → ℤ) (u n : ℕ)
    (c : Continuation) :
    ∃ T : ℕ, T ≤ 8 * n.bits.length + 14 ∧
      run (configuration m h u n.bits 0 (.count c 0)) T =
        configuration m h (u + 1) (n + 1).bits 0 (resume c) ∧
      ∀ t ≤ T, Frame m h u n.bits.length
        (run (configuration m h u n.bits 0 (.count c 0)) t) := by
  have configExt {a b : Configuration} (hc : a.control=b.control)
      (hh : a.head=b.head) (hm : a.cell=b.cell) : a=b := by
    cases a
    cases b
    cases hc
    cases hh
    cases hm
    rfl
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

  have writeBinary (u' : ℕ) (pre suf : List Bool) (a v : Bool) :
      Function.update (memory m u' (pre ++ a :: suf)) (8, true)
        (Function.update (wordCell (pre ++ a :: suf) true) (pre.length + 1) v) =
          memory m u' (pre ++ v :: suf) := by
    funext t z
    rcases t with ⟨p, b⟩
    by_cases hp : p = 8
    · subst p
      cases b
      · simpa [memory, Function.update_apply] using congrFun (replace pre suf a v false).symm z
      · simpa [memory, Function.update_apply] using congrFun (replace pre suf a v true).symm z
    · simp [memory, Function.update_apply, hp]
  have appendBinary (u' : ℕ) (bs : List Bool) (v : Bool) :
      Function.update
        (Function.update (memory m u' bs) (8, false)
          (Function.update (wordCell bs false) (bs.length + 1) true)) (8, true)
        (Function.update (wordCell bs true) (bs.length + 1) v) =
          memory m u' (bs ++ [v]) := by
    funext t z
    rcases t with ⟨p, b⟩
    by_cases hp : p = 8
    · subst p
      cases b
      · simpa [memory, Function.update_apply] using congrFun (extend bs v false).symm z
      · simpa [memory, Function.update_apply] using congrFun (extend bs v true).symm z
    · simp [memory, Function.update_apply, hp]
  have appendUnary (u' : ℕ) (bs : List Bool) :
      Function.update
        (Function.update (memory m u' bs) (7, false)
          (Function.update (wordCell (List.replicate u' true) false) (u' + 1) true)) (7, true)
        (Function.update (wordCell (List.replicate u' true) true) (u' + 1) true) =
          memory m (u' + 1) bs := by
    funext t z
    rcases t with ⟨p, b⟩
    by_cases hp : p = 7
    · subst p
      cases b
      · simpa [memory, Function.update_apply, List.replicate_succ'] using
          congrFun (extend (List.replicate u' true) true false).symm z
      · simpa [memory, Function.update_apply, List.replicate_succ'] using
          congrFun (extend (List.replicate u' true) true true).symm z
    · simp [memory, Function.update_apply, hp]
  let bump : List Bool → List Bool :=
    List.rec [true] (fun b bs rec => if b then false :: rec else true :: bs)
  have bump_nat (x : ℕ) : bump x.bits = (x + 1).bits := by
    induction x using Nat.binaryRec' with
    | zero => simp [bump]
    | bit b x hx ih =>
      cases b
      · have hx0 : x ≠ 0 := by simpa using hx
        simp [Nat.bit, Nat.bit0_bits x hx0, Nat.bit1_bits, bump]
      · rw [show Nat.bit true x = 2 * x + 1 from rfl, Nat.bit1_bits]
        change false :: bump x.bits = (2 * x + 1 + 1).bits
        rw [show 2 * x + 1 + 1 = 2 * (x + 1) by omega, Nat.bit0_bits _ (by omega), ih]
  have bump_length (bs : List Bool) :
      bs.length ≤ (bump bs).length ∧ (bump bs).length ≤ bs.length + 1 := by
    induction bs with
    | nil => simp [bump]
    | cons b bs ih => cases b <;> simp [bump] at * <;> omega
  let cfg (u' : ℕ) (bs : List Bool) (p : ℤ) (s : Fin 19) :=
    configuration m h u' bs p (.count c s)
  have readOcc (bs : List Bool) (j : ℕ) (hj : 0 < j) :
      wordCell bs false j = decide (j ≤ bs.length) := by
    simp [wordCell, hj, Nat.ne_of_gt hj]
  have readBit (pre : List Bool) (b : Bool) (bs : List Bool) :
      wordCell (pre ++ b :: bs) true (pre.length + 1) = b := by
    have hp : 0 < (pre.length : ℤ) + 1 := by omega
    simp [wordCell, ne_of_gt hp, hp, List.getElem?_append]

  have enter (bs : List Bool) :
      run (cfg u bs 0 0) 6 = cfg (u + 1) bs 1 6 := by
    simp only [run, show 6 = 1 + 1 + 1 + 1 + 1 + 1 from rfl,
      Function.iterate_succ_apply, Function.iterate_zero_apply]
    apply configExt
    · simp [cfg, configuration, step, program]
    · simp [cfg, configuration, step, program, heads]
      funext t
      rcases t with ⟨p, b⟩
      by_cases h7 : p = 7 <;> by_cases h8 : p = 8 <;> cases b <;>
        simp [heads, Function.update_apply, h7, h8]
    · simpa [cfg, configuration, step, program, heads, memory, Function.update_apply] using
        appendUnary u bs
  have carryZero (pre bs : List Bool) :
      run (cfg (u + 1) (pre ++ false :: bs) (pre.length + 1) 6) 3 =
        cfg (u + 1) (pre ++ true :: bs) (pre.length + 1) 13 := by
    have hp : 0 < (pre.length : ℤ) + 1 := by omega
    have ho : wordCell (pre ++ false :: bs) false (pre.length + 1) = true := by
      simp [wordCell, ne_of_gt hp, hp]
    have hv := readBit pre false bs
    simp only [run, show 3 = 1 + 1 + 1 from rfl,
      Function.iterate_succ_apply, Function.iterate_zero_apply]
    apply configExt
    · simp [cfg, configuration, step, program, heads, memory, ho, hv]
    · simp [cfg, configuration, step, program, heads, memory, ho, hv]
    · simpa [cfg, configuration, step, program, heads, memory, ho, hv] using
        writeBinary (u + 1) pre bs false true
  have carryBlank (pre : List Bool) :
      run (cfg (u + 1) pre (pre.length + 1) 6) 3 =
        cfg (u + 1) (pre ++ [true]) (pre.length + 1) 13 := by
    have hp : 0 < (pre.length : ℤ) + 1 := by omega
    have ho : wordCell pre false (pre.length + 1) = false := by
      simp [wordCell, ne_of_gt hp, hp]
    simp only [run, show 3 = 1 + 1 + 1 from rfl,
      Function.iterate_succ_apply, Function.iterate_zero_apply]
    apply configExt
    · simp [cfg, configuration, step, program, heads, memory, ho, Function.update_apply]
    · simp [cfg, configuration, step, program, heads, memory, ho, Function.update_apply]
    · simpa [cfg, configuration, step, program, heads, memory, ho, Function.update_apply] using
        appendBinary (u + 1) pre true
  have carryOne (pre bs : List Bool) :
      run (cfg (u + 1) (pre ++ true :: bs) (pre.length + 1) 6) 5 =
        cfg (u + 1) (pre ++ false :: bs) (pre.length + 2) 6 := by
    have hp : 0 < (pre.length : ℤ) + 1 := by omega
    have ho : wordCell (pre ++ true :: bs) false (pre.length + 1) = true := by
      simp [wordCell, ne_of_gt hp, hp]
    have hv := readBit pre true bs
    simp only [run, show 5 = 1 + 1 + 1 + 1 + 1 from rfl,
      Function.iterate_succ_apply, Function.iterate_zero_apply]
    apply configExt
    · simp [cfg, configuration, step, program, heads, memory, ho, hv]
    · simp [cfg, configuration, step, program, heads, memory, ho, hv]
      funext t
      rcases t with ⟨p, b⟩
      by_cases h7 : p = 7 <;> by_cases h8 : p = 8 <;> cases b <;>
        simp [heads, Function.update_apply, h7, h8] <;> omega
    · simpa [cfg, configuration, step, program, heads, memory, ho, hv] using
        writeBinary (u + 1) pre bs true false

  have enterSafe (bs : List Bool) : ∀ t ≤ 6,
      Frame m h u n.bits.length (run (cfg u bs 0 0) t) := by
    intro t ht
    interval_cases t <;> constructor
    all_goals first
      | (rintro ⟨p, b⟩ h7 h8
         simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
           heads, memory, Function.update_apply, h7, h8])
      | (constructor <;> intro b <;> cases b <;>
          simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
            heads, memory, Function.update_apply] <;> omega)
  have carrySafe (pre bs : List Bool) (b : Bool)
      (hlen : pre.length + (b :: bs).length ≤ n.bits.length) :
      ∀ t ≤ (if b then 5 else 3), Frame m h u n.bits.length
        (run (cfg (u + 1) (pre ++ b :: bs) (pre.length + 1) 6) t) := by
    have hp : 0 < (pre.length : ℤ) + 1 := by omega
    have ho : wordCell (pre ++ b :: bs) false (pre.length + 1) = true := by
      simp [wordCell, ne_of_gt hp, hp]
    have hv := readBit pre b bs
    cases b <;> intro t ht <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht
    all_goals interval_cases t <;> constructor
    all_goals first
      | (rintro ⟨p, b⟩ h7 h8
         simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
           heads, memory, Function.update_apply, ho, hv, h7, h8])
      | (constructor <;> intro b <;> cases b <;>
          simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
            heads, memory, Function.update_apply, ho, hv] <;>
          simp only [List.length_cons] at hlen <;> omega)
  have blankSafe (pre : List Bool) (hlen : pre.length ≤ n.bits.length) :
      ∀ t ≤ 3, Frame m h u n.bits.length
        (run (cfg (u + 1) pre (pre.length + 1) 6) t) := by
    have hp : 0 < (pre.length : ℤ) + 1 := by omega
    have ho : wordCell pre false (pre.length + 1) = false := by
      simp [wordCell, ne_of_gt hp, hp]
    intro t ht
    interval_cases t <;> constructor
    all_goals first
      | (rintro ⟨p, b⟩ h7 h8
         simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
           heads, memory, Function.update_apply, ho, h7, h8])
      | (constructor <;> intro b <;> cases b <;>
          simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
            heads, memory, Function.update_apply, ho] <;> omega)
  have join (a b : ℕ) (x y : Configuration) (he : run x a = y)
      (hx : ∀ t ≤ a, Frame m h u n.bits.length (run x t))
      (hy : ∀ t ≤ b, Frame m h u n.bits.length (run y t)) :
      ∀ t ≤ b + a, Frame m h u n.bits.length (run x t) := by
    intro t ht
    by_cases hta : t ≤ a
    · exact hx t hta
    · have ht' : t = (t - a) + a := by omega
      rw [ht']
      simp only [run, Function.iterate_add_apply]
      change Frame m h u n.bits.length (run (run x a) (t - a))
      rw [he]
      exact hy _ (by omega)
  have carry (bs pre : List Bool) (hL : pre.length + bs.length ≤ n.bits.length) :
      ∃ r : ℕ, r ≤ bs.length ∧
      run (cfg (u + 1) (pre ++ bs) (pre.length + 1) 6) (5 * r + 3) =
        cfg (u + 1) (pre ++ bump bs) (pre.length + r + 1) 13 ∧
      pre.length + r + 1 ≤ (pre ++ bump bs).length ∧
      (∀ t ≤ 5 * r + 3, Frame m h u n.bits.length
        (run (cfg (u + 1) (pre ++ bs) (pre.length + 1) 6) t)) := by
    induction bs generalizing pre with
    | nil =>
      refine ⟨0, by simp, ?_, ?_, ?_⟩
      · simpa [bump] using carryBlank pre
      · simp [bump]
      · simpa using blankSafe pre (by simpa using hL)
    | cons b bs ih =>
      cases b
      · refine ⟨0, by simp, ?_, ?_, ?_⟩
        · simpa [bump] using carryZero pre bs
        · simp [bump]
        · simpa using carrySafe pre bs false hL
      · obtain ⟨r, hr, hex, hlen, hsafe⟩ := ih (pre ++ [false])
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hL)
        refine ⟨r + 1, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
        · have ht : 5 * (r + 1) + 3 = (5 * r + 3) + 5 := by omega
          rw [ht]
          change run (run (cfg (u + 1) (pre ++ true :: bs) (pre.length + 1) 6) 5)
            (5 * r + 3) = _
          rw [carryOne]
          simpa [List.append_assoc, bump, Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm, Int.add_left_comm] using hex
        · simp [List.append_assoc, bump] at hlen ⊢
          omega
        · have hs : ∀ t ≤ 5 * r + 3, Frame m h u n.bits.length
              (run (cfg (u + 1) (pre ++ false :: bs) (pre.length + 2) 6) t) := by
            simpa [List.append_assoc, Nat.cast_add, Nat.cast_one, Int.add_assoc] using hsafe
          have hall := join 5 (5 * r + 3) _ _ (carryOne pre bs)
            (by simpa using carrySafe pre bs true hL) hs
          intro t ht
          exact hall t (by omega)
  have rewind (bs : List Bool) (j : ℕ) (hj : j ≤ bs.length)
      (hJ : j ≤ n.bits.length + 1) :
      run (cfg (u + 1) bs j 13) (3 * j + 2) =
        configuration m h (u + 1) bs 0 (resume c) ∧
      ∀ t ≤ 3 * j + 2, Frame m h u n.bits.length (run (cfg (u + 1) bs j 13) t) := by
    induction j with
    | zero =>
      constructor
      · simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
          memory, heads, wordCell]
      · intro t ht
        interval_cases t <;> constructor
        all_goals first
          | (rintro ⟨p, b⟩ h7 h8
             simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
               heads, memory, wordCell, h7, h8])
          | (constructor <;> intro b <;> cases b <;>
              simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
                heads, memory, wordCell] <;> omega)
    | succ j ih =>
      obtain ⟨he, hs⟩ := ih (by omega) (by omega)
      have ho : wordCell bs false ((j : ℤ) + 1) = true := by
        have hp : 0 < (j : ℤ) + 1 := by omega
        simp [wordCell, ne_of_gt hp, hp, hj]
      have three : run (cfg (u + 1) bs (j + 1) 13) 3 = cfg (u + 1) bs j 13 := by
        simp only [run, show 3 = 1 + 1 + 1 from rfl,
          Function.iterate_succ_apply, Function.iterate_zero_apply]
        apply configExt <;>
          simp [cfg, configuration, step, program, memory, heads, ho]
        funext t
        rcases t with ⟨p, b⟩
        by_cases h7 : p = 7 <;> by_cases h8 : p = 8 <;> cases b <;>
          simp [heads, Function.update_apply, h7, h8] <;> omega
      have threeSafe : ∀ t ≤ 3, Frame m h u n.bits.length
          (run (cfg (u + 1) bs (j + 1) 13) t) := by
        intro t ht
        interval_cases t <;> constructor
        all_goals first
          | (rintro ⟨p, b⟩ h7 h8
             simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
               heads, memory, Function.update_apply, ho, h7, h8])
          | (constructor <;> intro b <;> cases b <;>
              simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
                heads, memory, Function.update_apply, ho] <;> omega)
      constructor
      · have ht : 3 * (j + 1) + 2 = (3 * j + 2) + 3 := by omega
        rw [ht]
        change run (run (cfg (u + 1) bs (j + 1) 13) 3) (3 * j + 2) = _
        rw [three]
        exact he
      · have hall := join 3 (3 * j + 2) _ _ three threeSafe hs
        intro t ht
        exact hall t (by omega)
  obtain ⟨r, hr, hc, hl, hs⟩ := carry n.bits [] (by simp)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at hc hl hs
  obtain ⟨hw, hws⟩ := rewind (bump n.bits) (r + 1) hl (by omega)
  have endpoint : run (cfg u n.bits 0 0) (8 * r + 14) =
      configuration m h (u + 1) (n + 1).bits 0 (resume c) := by
    have ht : 8 * r + 14 = ((3 * (r + 1) + 2) + (5 * r + 3)) + 6 := by omega
    rw [ht]
    simp only [run, Function.iterate_add_apply]
    change run (run (run (cfg u n.bits 0 0) 6) (5 * r + 3)) (3 * (r + 1) + 2) = _
    rw [enter, hc]
    simpa only [Nat.cast_add, Nat.cast_one, bump_nat] using hw
  refine ⟨8 * r + 14, by omega, endpoint, ?_⟩
  have hws' : ∀ t ≤ 3 * (r + 1) + 2, Frame m h u n.bits.length
      (run (cfg (u + 1) (bump n.bits) ((r : ℤ) + 1) 13) t) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hws
  have hrest := join (5 * r + 3) (3 * (r + 1) + 2) _ _ hc hs hws'
  have hall := join 6 ((3 * (r + 1) + 2) + (5 * r + 3)) _ _
    (enter n.bits) (enterSafe n.bits) hrest
  intro t ht
  exact hall t (by omega)

end D5.S0.Computability.Coding.PhysicalParserTally
