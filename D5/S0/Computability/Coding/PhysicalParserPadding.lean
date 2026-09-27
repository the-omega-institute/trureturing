/- GID: D5/S0/Computability/Coding/PhysicalParserPadding
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/PhysicalParserPadding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Size]
   utility: none
   digest: A ruler-driven physical zero-padding sweep and four-head rewind with a literal frame. -/

import D5.S0.Computability.Coding.PhysicalSixParser

namespace D5.S0.Computability.Coding.PhysicalParserPadding

open PhysicalSixParser

/-- Specification of a selected parameter buffer and the retained unary ruler. -/
def memory (m : Track → ℤ → Bool) (i : Fin 6) (W : ℕ) (bs : List Bool) :
    Track → ℤ → Bool := fun (p, b) =>
  if p = 7 then wordCell (List.replicate W true) b
  else if p = parameterPair i then wordCell bs b else m (p, b)

/-- Aligned sweep boundaries; each component still has its own physical head in the machine. -/
def heads (h : Track → ℤ) (i : Fin 6) (j : ℤ) : Track → ℤ :=
  fun (p, b) => if p = 7 ∨ p = parameterPair i then j else h (p, b)

/-- The exact boundary configuration used in the sweep proof. -/
def configuration (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6)
    (W : ℕ) (bs : List Bool) (j : ℤ) (c : Control) : Configuration :=
  ⟨c, heads h i j, memory m i W bs⟩

/-- All-prefix preservation and bounds, including separately moved component heads. -/
def Frame (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6) (W : ℕ)
    (c : Configuration) : Prop :=
  (∀ t : Track, t.1 ≠ 7 → t.1 ≠ parameterPair i → c.head t = h t ∧ c.cell t = m t) ∧
  (∀ b, c.cell (7, b) = wordCell (List.replicate W true) b) ∧
  (∀ b, 0 ≤ c.head (7, b) ∧ c.head (7, b) ≤ W + 1) ∧
  (∀ b, 0 ≤ c.head (parameterPair i, b) ∧ c.head (parameterPair i, b) ≤ W + 1)

/-- Static field succession; the sixth field returns to the halted control. -/
def next (i : Fin 6) : Control :=
  if h : i.val < 5 then .pad ⟨i.val + 1, by omega⟩ 0 else .halt

/-- A physical padding sweep preserves the original digits, leaves the successor blank,
and returns all four selected heads to home. -/
theorem pad_one (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6) (W : ℕ)
    (bs : List Bool) (hlen : bs.length ≤ W) :
    ∃ T : ℕ, T ≤ 14 * W + 11 ∧
      run (configuration m h i W bs 0 (.pad i 0)) T =
        configuration m h i W (bs ++ List.replicate (W - bs.length) false) 0 (next i) ∧
      ∀ t ≤ T, Frame m h i W (run (configuration m h i W bs 0 (.pad i 0)) t) := by
  have configExt {a b : Configuration} (hc : a.control=b.control)
      (hh : a.head=b.head) (hm : a.cell=b.cell) : a=b := by
    cases a
    cases b
    cases hc
    cases hh
    cases hm
    rfl
  have hi7 : parameterPair i ≠ 7 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [parameterPair] at hv
    have := i.isLt
    omega
  have h7i : (7 : Fin 9) ≠ parameterPair i := Ne.symm hi7
  let cfg (word : List Bool) (j : ℤ) (s : Fin 16) :=
    configuration m h i W word j (.pad i s)
  have ruler (j : ℕ) (hj : 0 < j) (hjW : j ≤ W) :
      wordCell (List.replicate W true) false j = true ∧
      wordCell (List.replicate W true) true j = true := by
    simp [wordCell, hj, Nat.ne_of_gt hj, List.getElem?_replicate, hjW,
      show j - 1 < W by omega]
  have homeO : wordCell (List.replicate W true) false 0 = false := by simp [wordCell]
  have homeV : wordCell (List.replicate W true) true 0 = true := by simp [wordCell]
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
  have appendMemory (word : List Bool) :
      Function.update
        (Function.update (memory m i W word) (parameterPair i, false)
          (Function.update (wordCell word false) (word.length + 1) true))
        (parameterPair i, true)
        (Function.update (wordCell word true) (word.length + 1) false) =
          memory m i W (word ++ [false]) := by
    funext t z
    rcases t with ⟨p, b⟩
    by_cases hp : p = parameterPair i
    · subst p
      cases b
      · simpa [memory, Function.update_apply, hi7] using congrFun (extend word false false).symm z
      · simpa [memory, Function.update_apply, hi7] using congrFun (extend word false true).symm z
    · simp [memory, Function.update_apply, hp]
  have join (a b : ℕ) (x y : Configuration) (he : run x a = y)
      (hx : ∀ t ≤ a, Frame m h i W (run x t))
      (hy : ∀ t ≤ b, Frame m h i W (run y t)) :
      ∀ t ≤ b + a, Frame m h i W (run x t) := by
    intro t ht
    by_cases hta : t ≤ a
    · exact hx t hta
    · have ht' : t = (t - a) + a := by omega
      rw [ht']
      simp only [run, Function.iterate_add_apply]
      change Frame m h i W (run (run x a) (t - a))
      rw [he]
      exact hy _ (by omega)
  have old (word : List Bool) (j : ℕ) (hj : j < word.length) (hjW : j < W) :
      run (cfg word j 0) 7 = cfg word (j + 1) 0 ∧
      ∀ t ≤ 7, Frame m h i W (run (cfg word j 0) t) := by
    obtain ⟨ro, rv⟩ := ruler (j + 1) (by omega) (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at ro rv
    have hp : 0 < (j : ℤ) + 1 := by omega
    have bo : wordCell word false ((j : ℤ) + 1) = true := by
      simp [wordCell, ne_of_gt hp, hp, show j + 1 ≤ word.length by omega]
    constructor
    · simp only [run, show 7 = 1+1+1+1+1+1+1 from rfl,
        Function.iterate_succ_apply, Function.iterate_zero_apply]
      apply configExt <;>
        simp [cfg, configuration, step, program, heads, memory, ro, rv, bo, hi7, h7i,
          Function.update_apply]
      funext t
      rcases t with ⟨p, b⟩
      by_cases h7 : p = 7 <;> by_cases hpi : p = parameterPair i <;> cases b <;>
        simp [heads, Function.update_apply, h7, hpi, hi7, h7i]
    · intro t ht
      interval_cases t <;>
        simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
          heads, memory, ro, rv, bo, hi7, h7i, Function.update_apply] <;> constructor
      all_goals solve
        | (rintro ⟨p, b⟩ h7 hpi
           simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
             heads, memory, Function.update_apply, ro, rv, bo, hi7, h7i, h7, hpi])
        | (refine ⟨?_, ?_, ?_⟩ <;> intro b <;> cases b <;>
            simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
              heads, memory, Function.update_apply, ro, rv, bo, hi7, h7i] <;> omega)
  have fresh (word : List Bool) (hjW : word.length < W) :
      run (cfg word word.length 0) 9 = cfg (word ++ [false]) (word.length + 1) 0 ∧
      ∀ t ≤ 9, Frame m h i W (run (cfg word word.length 0) t) := by
    obtain ⟨ro, rv⟩ := ruler (word.length + 1) (by omega) (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at ro rv
    have hp : 0 < (word.length : ℤ) + 1 := by omega
    have bo : wordCell word false ((word.length : ℤ) + 1) = false := by
      simp [wordCell, ne_of_gt hp, hp]
    constructor
    · simp only [run, show 9 = 1+1+1+1+1+1+1+1+1 from rfl,
        Function.iterate_succ_apply, Function.iterate_zero_apply]
      apply configExt
      · simp [cfg, configuration, step, program, heads, memory, ro, rv, bo, hi7, h7i,
          Function.update_apply]
      · simp [cfg, configuration, step, program, heads, memory, ro, rv, bo, hi7, h7i,
          Function.update_apply]
        funext t
        rcases t with ⟨p, b⟩
        by_cases h7 : p = 7 <;> by_cases hpi : p = parameterPair i <;> cases b <;>
          simp [heads, Function.update_apply, h7, hpi, hi7, h7i]
      · simpa [cfg, configuration, step, program, heads, memory, ro, rv, bo, hi7, h7i,
          Function.update_apply] using appendMemory word
    · intro t ht
      interval_cases t <;>
        simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
          heads, memory, ro, rv, bo, hi7, h7i, Function.update_apply] <;> constructor
      all_goals solve
        | (rintro ⟨p, b⟩ h7 hpi
           simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
             heads, memory, Function.update_apply, ro, rv, bo, hi7, h7i, h7, hpi])
        | (refine ⟨?_, ?_, ?_⟩ <;> intro b <;> cases b <;>
            simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
              heads, memory, Function.update_apply, ro, rv, bo, hi7, h7i] <;> omega)
  have finish (word : List Bool) :
      run (cfg word W 0) 5 = cfg word (W + 1) 9 ∧
      ∀ t ≤ 5, Frame m h i W (run (cfg word W 0) t) := by
    have hp : 0 < (W : ℤ) + 1 := by omega
    have ro : wordCell (List.replicate W true) false ((W : ℤ) + 1) = false := by
      simp [wordCell, ne_of_gt hp, hp]
    constructor
    · simp only [run, show 5 = 1+1+1+1+1 from rfl,
        Function.iterate_succ_apply, Function.iterate_zero_apply]
      apply configExt <;>
        simp [cfg, configuration, step, program, heads, memory, ro, hi7, h7i,
          Function.update_apply]
      funext t
      rcases t with ⟨p, b⟩
      by_cases h7 : p = 7 <;> by_cases hpi : p = parameterPair i <;> cases b <;>
        simp [heads, Function.update_apply, h7, hpi, hi7, h7i]
    · intro t ht
      interval_cases t <;>
        simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
          heads, memory, ro, hi7, h7i, Function.update_apply] <;> constructor
      all_goals solve
        | (rintro ⟨p, b⟩ h7 hpi
           simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
             heads, memory, Function.update_apply, ro, hi7, h7i, h7, hpi])
        | (refine ⟨?_, ?_, ?_⟩ <;> intro b <;> cases b <;>
            simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
              heads, memory, Function.update_apply, ro, hi7, h7i] <;> omega)
  have cfgSafe (word : List Bool) (j : ℕ) (hj : j ≤ W + 1) (s : Fin 16) :
      Frame m h i W (cfg word j s) := by
    constructor
    · rintro ⟨p, b⟩ h7 hpi
      simp [cfg, configuration, heads, memory, h7, hpi]
    · refine ⟨?_, ?_, ?_⟩ <;> intro b <;> cases b <;>
        simp [cfg, configuration, heads, memory, hi7, h7i] <;> omega
  have rewind (word : List Bool) (j : ℕ) (hj : j ≤ W) :
      run (cfg word (j + 1) 9) (5 * (j + 1) + 1) =
        configuration m h i W word 0 (next i) ∧
      ∀ t ≤ 5 * (j + 1) + 1, Frame m h i W (run (cfg word (j + 1) 9) t) := by
    induction j with
    | zero =>
      constructor
      · simp only [run, show 5 * (0 + 1) + 1 = 1+1+1+1+1+1 from rfl,
          Function.iterate_succ_apply, Function.iterate_zero_apply]
        apply configExt <;>
          simp [cfg, configuration, step, program, heads, memory, homeO, homeV,
            hi7, h7i, next, Function.update_apply]
        funext t
        rcases t with ⟨p, b⟩
        by_cases h7 : p = 7 <;> by_cases hpi : p = parameterPair i <;> cases b <;>
          simp [heads, Function.update_apply, h7, hpi, hi7, h7i]
      · intro t ht
        interval_cases t <;>
        simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
          heads, memory, homeO, homeV, hi7, h7i, Function.update_apply] <;> constructor
        all_goals solve
          | (rintro ⟨p, b⟩ h7 hpi
             simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
               heads, memory, homeO, homeV, Function.update_apply, hi7, h7i, h7, hpi])
          | (refine ⟨?_, ?_, ?_⟩ <;> intro b <;> cases b <;>
              simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
                heads, memory, homeO, homeV, Function.update_apply, hi7, h7i] <;> omega)
    | succ j ih =>
      obtain ⟨he, hs⟩ := ih (by omega)
      obtain ⟨ro, rv⟩ := ruler (j + 1) (by omega) hj
      simp only [Nat.cast_add, Nat.cast_one] at ro rv
      have five : run (cfg word (j + 1 + 1) 9) 5 = cfg word (j + 1) 9 := by
        simp only [run, show 5 = 1+1+1+1+1 from rfl,
          Function.iterate_succ_apply, Function.iterate_zero_apply]
        apply configExt <;>
          simp [cfg, configuration, step, program, heads, memory, ro, hi7, h7i,
            Function.update_apply]
        funext t
        rcases t with ⟨p, b⟩
        by_cases h7 : p = 7 <;> by_cases hpi : p = parameterPair i <;> cases b <;>
          simp [heads, Function.update_apply, h7, hpi, hi7, h7i] <;> omega
      have fiveSafe : ∀ t ≤ 5, Frame m h i W (run (cfg word (j + 1 + 1) 9) t) := by
        intro t ht
        interval_cases t <;>
          simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
            heads, memory, ro, hi7, h7i, Function.update_apply] <;> constructor
        all_goals solve
          | (rintro ⟨p, b⟩ h7 hpi
             simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
               heads, memory, Function.update_apply, ro, hi7, h7i, h7, hpi])
          | (refine ⟨?_, ?_, ?_⟩ <;> intro b <;> cases b <;>
              simp [run, Function.iterate_succ_apply, cfg, configuration, step, program,
                heads, memory, Function.update_apply, ro, hi7, h7i] <;> omega)
      constructor
      · have ht : 5 * (j + 1 + 1) + 1 = (5 * (j + 1) + 1) + 5 := by omega
        rw [ht]
        change run (run (cfg word (j + 1 + 1) 9) 5) (5 * (j + 1) + 1) = _
        rw [five]
        exact he
      · have hall := join 5 (5 * (j + 1) + 1) _ _ five fiveSafe hs
        intro t ht
        exact hall t (by omega)
  have existing (j : ℕ) (hj : j ≤ bs.length) :
      run (cfg bs 0 0) (7 * j) = cfg bs j 0 ∧
      ∀ t ≤ 7 * j, Frame m h i W (run (cfg bs 0 0) t) := by
    induction j with
    | zero =>
      refine ⟨rfl, ?_⟩
      intro t ht
      have : t = 0 := by omega
      subst t
      exact cfgSafe bs 0 (by omega) 0
    | succ j ih =>
      obtain ⟨he, hs⟩ := ih (by omega)
      obtain ⟨hn, hns⟩ := old bs j (by omega) (by omega)
      constructor
      · have ht : 7 * (j + 1) = 7 + 7 * j := by omega
        rw [ht]
        simp only [run, Function.iterate_add_apply]
        change run (run (cfg bs 0 0) (7 * j)) 7 = _
        rw [he]
        simpa only [Nat.cast_add, Nat.cast_one] using hn
      · have hall := join (7 * j) 7 _ _ he hs hns
        intro t ht
        exact hall t (by omega)
  have padding (k : ℕ) (hk : bs.length + k ≤ W) :
      run (cfg bs bs.length 0) (9 * k) =
        cfg (bs ++ List.replicate k false) (bs.length + k) 0 ∧
      ∀ t ≤ 9 * k, Frame m h i W (run (cfg bs bs.length 0) t) := by
    induction k with
    | zero =>
      constructor
      · simp [run, cfg]
      · intro t ht
        have : t = 0 := by omega
        subst t
        exact cfgSafe bs bs.length (by omega) 0
    | succ k ih =>
      obtain ⟨he, hs⟩ := ih (by omega)
      obtain ⟨hn, hns⟩ := fresh (bs ++ List.replicate k false) (by simp; omega)
      simp only [List.length_append, List.length_replicate, Nat.cast_add] at hn hns
      constructor
      · have ht : 9 * (k + 1) = 9 + 9 * k := by omega
        rw [ht]
        simp only [run, Function.iterate_add_apply]
        change run (run (cfg bs bs.length 0) (9 * k)) 9 = _
        rw [he]
        simpa [List.replicate_succ', List.append_assoc, Nat.cast_add, Nat.cast_one,
          Int.add_assoc] using hn
      · have hall := join (9 * k) 9 _ _ he hs hns
        intro t ht
        exact hall t (by omega)
  let result := bs ++ List.replicate (W - bs.length) false
  obtain ⟨he, hes⟩ := existing bs.length (by omega)
  obtain ⟨hp, hps⟩ := padding (W - bs.length) (by omega)
  have hwidth : (bs.length : ℤ) + ((W - bs.length : ℕ) : ℤ) = W := by omega
  change run (cfg bs bs.length 0) (9 * (W - bs.length)) =
    cfg result ((bs.length : ℤ) + ((W - bs.length : ℕ) : ℤ)) 0 at hp
  rw [hwidth] at hp
  obtain ⟨hf, hfs⟩ := finish result
  obtain ⟨hr, hrs⟩ := rewind result W (by omega)
  let T := ((5 * (W + 1) + 1 + 5) + 9 * (W - bs.length)) + 7 * bs.length
  refine ⟨T, by dsimp [T]; omega, ?_, ?_⟩
  · dsimp [T]
    simp only [run, Function.iterate_add_apply]
    change run (run (run (run (cfg bs 0 0) (7 * bs.length))
      (9 * (W - bs.length))) 5) (5 * (W + 1) + 1) = _
    rw [he, hp, hf]
    simpa only [Nat.cast_add, Nat.cast_one] using hr
  · have hs1 := join 5 (5 * (W + 1) + 1) _ _ hf hfs
      (by simpa only [Nat.cast_add, Nat.cast_one] using hrs)
    have hs2 := join (9 * (W - bs.length)) (5 * (W + 1) + 1 + 5) _ _ hp hps hs1
    exact join (7 * bs.length) _ _ _ he hes hs2

end D5.S0.Computability.Coding.PhysicalParserPadding
