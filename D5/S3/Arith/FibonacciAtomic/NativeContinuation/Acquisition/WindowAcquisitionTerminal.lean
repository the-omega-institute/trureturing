/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionTerminal
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionTerminal
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Paid terminal arithmetic and persistent visited-cell resource estimates. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.WindowAcquisitionPrefixes

namespace PhysicalWindowContinuation
noncomputable def finiteCode {α : Type} [Fintype α] [DecidableEq α] (a : α) : List Bool :=
  List.ofFn fun i : Fin (Fintype.card α) => decide ((Fintype.equivFin α).symm i = a)

theorem finiteCode_length {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    (finiteCode a).length = Fintype.card α := by simp [finiteCode]

theorem finiteCode_injective {α : Type} [Fintype α] [DecidableEq α] :
    Function.Injective (finiteCode (α := α)) := by
  intro a b he
  have h := congrArg (fun l : List Bool => l[(Fintype.equivFin α a).val]?) he
  simpa [finiteCode] using h.symm

noncomputable def instructionCode : Instruction → List Bool
  | .read t f => [false,false] ++ finiteCode t ++ finiteCode Symbol.blank ++
      (List.ofFn fun i : Fin (Fintype.card Symbol) =>
        finiteCode (f ((Fintype.equivFin Symbol).symm i))).flatten
  | .write t b k => [false,true] ++ finiteCode t ++ finiteCode b ++
      (List.replicate (Fintype.card Symbol) (finiteCode k)).flatten
  | .move t right k => [true,false] ++ finiteCode t ++ finiteCode (Symbol.unit right) ++
      (List.replicate (Fintype.card Symbol) (finiteCode k)).flatten
  | .halt => [true,true] ++ finiteCode sourceTrack ++ finiteCode Symbol.blank ++
      (List.replicate (Fintype.card Symbol) (finiteCode Control.done)).flatten

noncomputable def programCode : List Bool :=
  (List.ofFn fun i : Fin (Fintype.card Control) =>
    instructionCode (program ((Fintype.equivFin Control).symm i))).flatten

def suppliedPositions (w : List Window) (t : Track) : Finset ℤ :=
  if t = sourceTrack then (Finset.range (w.length+1)).image Int.ofNat else {0}

def visitedPositions (w : List Window) (e : Bool) (n : ℕ) (t : Track) : Finset ℤ :=
  suppliedPositions w t ∪
    (Finset.range (n+1)).image (fun k => (run (initial w e) k).head t)

noncomputable def chargedBits (w : List Window) (e : Bool) (n : ℕ) : ℕ :=
  programCode.length + (finiteCode (run (initial w e) n).control).length +
    ∑ t : Track, ((visitedPositions w e n t).card * Fintype.card Symbol +
      (D5.S0.Computability.Coding.PhysicalSixParser.headDescription
        (run (initial w e) n |>.head t)).length)

theorem frame_heads (source : ℤ → Symbol) (H W : ℕ) (c : Configuration)
    (hH : H ≤ W) (hf : Frame source H W c) (t : Track) :
    0 ≤ c.head t ∧ c.head t ≤ W := by
  obtain ⟨_,ho,hs0,hs1,hw0,hw1⟩ := hf
  by_cases hw : t = workTrack
  · subst t
    exact ⟨hw0,hw1⟩
  by_cases hs : t = sourceTrack
  · subst t
    exact ⟨hs0,by omega⟩
  have hh := (ho t hw hs).1
  exact ⟨by omega,by omega⟩

theorem visitedPositions_bound (w : List Window) (e : Bool) (n W : ℕ)
    (hW : w.length ≤ W)
    (hh : ∀ k ≤ n, ∀ t, 0 ≤ (run (initial w e) k).head t ∧
      (run (initial w e) k).head t ≤ W) (t : Track) :
    (visitedPositions w e n t).card ≤ W+1 := by
  have hsub : visitedPositions w e n t ⊆ (Finset.range (W+1)).image Int.ofNat := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · by_cases hs : t = sourceTrack
      · simp only [suppliedPositions,hs,↓reduceIte,Finset.mem_image] at hz
        obtain ⟨k,hk,rfl⟩ := hz
        exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hk; omega),rfl⟩
      · have hz0 : z = 0 := by simpa [suppliedPositions,hs] using hz
        subst z
        exact Finset.mem_image.mpr ⟨0,by simp,rfl⟩
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h0,h1⟩ := hh k (by have := Finset.mem_range.mp hk; omega) t
      refine Finset.mem_image.mpr ⟨(run (initial w e) k |>.head t).toNat,?_,?_⟩
      · apply Finset.mem_range.mpr
        omega
      · exact Int.toNat_of_nonneg h0
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans (by simp))

theorem prefix_charged_bound (w : List Window) (e : Bool) (T : ℕ)
    (hf : ∀ n ≤ T, Frame (inputSource w e) w.length (3*w.length+5)
      (run (initial w e) n)) :
    ∀ n ≤ T, chargedBits w e n ≤
      (programCode.length + Fintype.card Control + 64*(Fintype.card Symbol+1)) *
        (w.length+1) := by
  intro n hn
  have hheads : ∀ k ≤ n, ∀ t, 0 ≤ (run (initial w e) k).head t ∧
      (run (initial w e) k).head t ≤ 3*w.length+5 := by
    intro k hk t
    exact frame_heads _ w.length (3*w.length+5) _ (by omega)
      (hf k (hk.trans hn)) t
  have hterm : ∀ t : Track,
      (visitedPositions w e n t).card * Fintype.card Symbol +
        (D5.S0.Computability.Coding.PhysicalSixParser.headDescription
          (run (initial w e) n |>.head t)).length ≤
      (3*w.length+6)*Fintype.card Symbol + (3*w.length+7) := by
    intro t
    have hv := visitedPositions_bound w e n (3*w.length+5) (by omega) hheads t
    have hm := Nat.mul_le_mul_right (Fintype.card Symbol) hv
    rw [show 3*w.length+5+1 = 3*w.length+6 by omega] at hm
    obtain ⟨h0,h1⟩ := hheads n (by rfl) t
    simp only [D5.S0.Computability.Coding.PhysicalSixParser.headDescription,
      List.length_append,List.length_cons,List.length_replicate,List.length_nil]
    have habs : (run (initial w e) n |>.head t).natAbs ≤ 3*w.length+5 := by omega
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Track))
    (fun t _ => hterm t)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at hsum
  simp only [chargedBits,finiteCode_length]
  nlinarith only [hsum, Nat.zero_le (programCode.length+Fintype.card Control)]

namespace Terminal

def hasN (bs : List Bits) : Bool := bs.any (fun b => b.2.2.2)

def sweep : Fin 5 → List Bits → List Bits × Fin 5
  | c, [] => ([], c)
  | c, b :: bs =>
      let one := finishTransfer c b
      let rest := sweep one.2 bs
      (one.1 :: rest.1, rest.2)

theorem sweep_length (c : Fin 5) (bs : List Bits) :
    (sweep c bs).1.length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [sweep, ih]

theorem scan_three (source : ℤ → Symbol) (p : ℤ) (pre suf : List Bits)
    (b : Bits) (carry : Fin 5) (seen : Bool) :
    run (boundary source p (pre ++ b :: suf) (pre.length + 1)
      (.finishScan carry seen)) 3 =
    boundary source p (pre ++ (finishTransfer carry b).1 :: suf) (pre.length + 2)
      (.finishScan (finishTransfer carry b).2 (seen || (finishTransfer carry b).1.2.2.2)) := by
  simp only [run, show 3 = 1 + 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · simp [step, program, boundary, word_read]
  · simp [step, program, boundary, word_read]
    funext t
    by_cases hw : t = workTrack
    · simp [hw]
      omega
    · simp [hw]
  · simp [step, program, boundary, word_read]
    funext t z
    by_cases hw : t = workTrack
    · subst t
      simpa [boundary, Function.update_apply] using
        congrFun (word_replace pre suf b (finishTransfer carry b).1) z
    · simp [hw]

theorem scan_prefix (source : ℤ → Symbol) (p : ℤ) (pre bs : List Bits)
    (carry : Fin 5) (seen : Bool) :
    run (boundary source p (pre ++ bs) (pre.length + 1)
      (.finishScan carry seen)) (3 * bs.length) =
    boundary source p (pre ++ (sweep carry bs).1) (pre.length + bs.length + 1)
      (.finishScan (sweep carry bs).2 (seen || hasN (sweep carry bs).1)) := by
  induction bs generalizing carry seen pre with
  | nil => simp [sweep, run, hasN]
  | cons b bs ih =>
    rw [show 3 * (b :: bs).length = 3 * bs.length + 3 by simp; omega]
    rw [run, Function.iterate_add_apply]
    change run (run _ 3) (3 * bs.length) = _
    rw [scan_three]
    have next := ih (pre ++ [(finishTransfer carry b).1]) (finishTransfer carry b).2
      (seen || (finishTransfer carry b).1.2.2.2)
    simpa [List.append_assoc, sweep, hasN, List.length_append, Nat.add_assoc,
      Int.add_assoc, Int.add_left_comm, Int.add_comm, Bool.or_assoc] using next

theorem scan_three_safe (source : ℤ → Symbol) (p : ℤ) (pre suf : List Bits)
    (b : Bits) (carry : Fin 5) (seen : Bool) (L : ℕ)
    (hL : pre.length + 1 ≤ L) :
    ∀ t ≤ 3, Safe source p L
      (run (boundary source p (pre ++ b :: suf) (pre.length + 1)
        (.finishScan carry seen)) t) := by
  intro t ht
  interval_cases t
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Safe, step, program, boundary, word_read, Function.update_apply,
      workTrack, sourceTrack]
    refine ⟨?_, by omega, by omega⟩
    intro t hw hs
    simp [hw, hs]

theorem scan_prefix_safe (source : ℤ → Symbol) (p : ℤ) (pre bs : List Bits)
    (carry : Fin 5) (seen : Bool) (L : ℕ) (hL : pre.length + bs.length ≤ L) :
    ∀ t ≤ 3 * bs.length, Safe source p L
      (run (boundary source p (pre ++ bs) (pre.length + 1)
        (.finishScan carry seen)) t) := by
  induction bs generalizing carry seen pre with
  | nil =>
    intro t ht
    have he : t = 0 := by simpa using ht
    subst t
    rw [List.append_nil]
    exact boundary_safe source p pre (pre.length + 1)
      (.finishScan carry seen) L (by omega) (by simp at hL; omega)
  | cons b bs ih =>
    intro t ht
    by_cases hsmall : t ≤ 3
    · exact scan_three_safe source p pre bs b carry seen L
        (by simp at hL; omega) t hsmall
    · have he : t = (t - 3) + 3 := by omega
      rw [he, run, Function.iterate_add_apply]
      change Safe source p L (run (run _ 3) (t - 3))
      rw [scan_three]
      have next := ih (pre ++ [(finishTransfer carry b).1]) (finishTransfer carry b).2
        (seen || (finishTransfer carry b).1.2.2.2)
        (by simp only [List.length_append, List.length_singleton]
            simp only [List.length_cons] at hL
            omega) (t - 3) (by simp at ht; omega)
      simpa [List.append_assoc, Int.add_assoc] using next

def flush : ℕ → Fin 5 → List Bits × Fin 5
  | 0, c => ([], c)
  | n + 1, c => if c != 0 then
      let one := finishTransfer c zeros
      let rest := flush n one.2
      (one.1 :: rest.1, rest.2)
    else ([], c)

theorem flush_length (fuel : ℕ) (carry : Fin 5) :
    (flush fuel carry).1.length ≤ fuel := by
  induction fuel generalizing carry with
  | zero => simp [flush]
  | succ fuel ih =>
    simp only [flush]
    split
    · simpa using Nat.succ_le_succ (ih (finishTransfer carry zeros).2)
    · simp

theorem flush_three_zero : ∀ carry : Fin 5, (flush 3 carry).2 = 0 := by decide

theorem scan_blank_three (source : ℤ → Symbol) (p : ℤ) (pre : List Bits)
    (carry : Fin 5) (seen : Bool) (ha : carry ≠ 0) :
    run (boundary source p pre (pre.length + 1) (.finishScan carry seen)) 3 =
    boundary source p (pre ++ [(finishTransfer carry zeros).1]) (pre.length + 2)
      (.finishScan (finishTransfer carry zeros).2 (seen || (finishTransfer carry zeros).1.2.2.2)) := by
  simp only [run, show 3 = 1 + 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · simp [step, program, boundary, word_blank, ha]
  · simp [step, program, boundary, word_blank, ha]
    funext t
    by_cases hw : t = workTrack
    · simp [hw]
      omega
    · simp [hw]
  · simp [step, program, boundary, word_blank, ha]
    funext t z
    by_cases hw : t = workTrack
    · subst t
      simpa [Function.update_apply] using
        congrFun (word_append pre (finishTransfer carry zeros).1) z
    · simp [hw]

theorem scan_blank_safe (source : ℤ → Symbol) (p : ℤ) (pre : List Bits)
    (carry : Fin 5) (seen : Bool) (ha : carry ≠ 0) (L : ℕ) (hL : pre.length + 1 ≤ L) :
    ∀ t ≤ 3, Safe source p L
      (run (boundary source p pre (pre.length + 1) (.finishScan carry seen)) t) := by
  intro t ht
  interval_cases t
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Safe, step, program, boundary, word_blank, ha, Function.update_apply,
      workTrack, sourceTrack]
    repeat' apply And.intro
    all_goals first | (intro t hw hs; simp [hw, hs]) | omega

theorem scan_flush (source : ℤ → Symbol) (p : ℤ) (pre : List Bits)
    (carry : Fin 5) (seen : Bool) (fuel L : ℕ)
    (hstop : (flush fuel carry).2 = 0) (hL : pre.length + fuel ≤ L) :
    ∃ T : ℕ, T ≤ 3 * fuel + 1 ∧
      run (boundary source p pre (pre.length + 1) (.finishScan carry seen)) T =
        boundary source p (pre ++ (flush fuel carry).1)
          (pre.length + (flush fuel carry).1.length + 1)
          (.finishRewindMove (seen || hasN (flush fuel carry).1)) ∧
      ∀ t ≤ T, Safe source p L
        (run (boundary source p pre (pre.length + 1) (.finishScan carry seen)) t) := by
  induction fuel generalizing pre carry seen with
  | zero =>
    have ha : carry = 0 := hstop
    refine ⟨1, by omega, ?_, ?_⟩
    · simp [flush, run, step, program, boundary, word_blank, ha, hasN]
    · intro t ht
      interval_cases t
      all_goals
        simp [Safe, run, step, program, boundary, word_blank, ha,
          workTrack, sourceTrack]
        repeat' apply And.intro
        all_goals first | (intro t hw hs; simp [hw, hs]) | omega
  | succ fuel ih =>
    by_cases ha : carry ≠ 0
    · have hstop' : (flush fuel (finishTransfer carry zeros).2).2 = 0 := by
        simpa [flush, ha] using hstop
      obtain ⟨T, hT, he, hs⟩ := ih (pre ++ [(finishTransfer carry zeros).1])
        (finishTransfer carry zeros).2 (seen || (finishTransfer carry zeros).1.2.2.2) hstop'
        (by simp only [List.length_append, List.length_singleton]; omega)
      have hthree := scan_blank_three source p pre carry seen ha
      have hh : (pre ++ [(finishTransfer carry zeros).1]).length = pre.length + 1 := by simp
      have he' : run (boundary source p pre (pre.length + 1)
          (.finishScan carry seen)) (T + 3) =
          boundary source p (pre ++ (flush (fuel + 1) carry).1)
            (pre.length + (flush (fuel + 1) carry).1.length + 1)
            (.finishRewindMove (seen || hasN (flush (fuel + 1) carry).1)) := by
        rw [run, Function.iterate_add_apply]
        change run (run _ 3) T = _
        rw [hthree]
        simpa [flush, ha, hasN, Bool.or_assoc, List.append_assoc, hh, Int.add_assoc, Int.add_left_comm,
          Int.add_comm] using he
      refine ⟨T + 3, by omega, he', ?_⟩
      apply safe_join source p L 3 T _ _ hthree
      · exact scan_blank_safe source p pre carry seen ha L (by omega)
      · simpa [hh, Int.add_assoc] using hs
    · have ha' : carry = 0 := by simpa using ha
      refine ⟨1, by omega, ?_, ?_⟩
      · simp [flush, run, step, program, boundary, word_blank, ha',hasN]
      · intro t ht
        interval_cases t
        all_goals
          simp [Safe, run, step, program, boundary, word_blank, ha',
            workTrack, sourceTrack]
          repeat' apply And.intro
          all_goals first | (intro t hw hs; simp [hw, hs]) | omega

theorem rewind_two (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (j : ℕ) (positive : Bool) (hj : j < bs.length) :
    run (boundary source p bs (j + 1) (.finishRewind positive)) 2 =
      boundary source p bs j (.finishRewind positive) := by
  simp only [run, show 2 = 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · simp [step, program, boundary, word_get, hj]
  · simp [step, program, boundary, word_get, hj]
    funext t
    by_cases hw : t = workTrack
    · simp [hw]
    · simp [hw]
  · simp [step, program, boundary, word_get, hj]

theorem rewind_two_safe (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (j : ℕ) (positive : Bool) (hj : j < bs.length) (L : ℕ) (hL : j ≤ L) :
    ∀ t ≤ 2, Safe source p L
      (run (boundary source p bs (j + 1) (.finishRewind positive)) t) := by
  intro t ht
  interval_cases t
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Safe, step, program, boundary, word_get, hj, Function.update_apply,
      workTrack, sourceTrack]
    repeat' apply And.intro
    all_goals first | (intro t hw hs; simp [hw, hs]) | omega

theorem rewind_all (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (j : ℕ) (positive : Bool) (hj : j ≤ bs.length) (L : ℕ) (hL : j ≤ L) :
    run (boundary source p bs j (.finishRewind positive)) (2 * j + 1) =
      boundary source p bs 0 (if positive then .done else .reject) ∧
    ∀ t ≤ 2 * j + 1, Safe source p L
      (run (boundary source p bs j (.finishRewind positive)) t) := by
  induction j with
  | zero =>
    constructor
    · simp [run, step, program, boundary, word]
    · intro t ht
      interval_cases t
      all_goals
        simp [Safe, run, step, program, boundary, word, workTrack, sourceTrack]
        repeat' apply And.intro
        all_goals first | (intro t hw hs; simp [hw, hs]) | omega
  | succ j ih =>
    have htwo := rewind_two source p bs j positive (by omega)
    obtain ⟨he, hs⟩ := ih (by omega) (by omega)
    constructor
    · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega,
        run, Function.iterate_add_apply]
      change run (run _ 2) (2 * j + 1) = _
      simp only [Nat.cast_add, Nat.cast_one]
      rw [htwo]
      exact he
    · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]
      simpa only [Nat.cast_add, Nat.cast_one] using
        safe_join source p L 2 (2 * j + 1) _ _ htwo
          (rewind_two_safe source p bs j positive (by omega) L (by omega)) hs

def finished (carry : Fin 5) (bs : List Bits) : List Bits :=
  let scanned := sweep carry bs
  scanned.1 ++ (flush 3 scanned.2).1

theorem scan_return (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (carry : Fin 5) (seen : Bool) :
    ∃ T : ℕ, T ≤ 5 * bs.length + 18 ∧
      run (boundary source p bs 1 (.finishScan carry seen)) T =
        boundary source p (finished carry bs) 0
          (if seen || hasN (finished carry bs) then .done else .reject) ∧
      (finished carry bs).length ≤ bs.length + 3 ∧
      ∀ t ≤ T, Safe source p (bs.length + 3)
        (run (boundary source p bs 1 (.finishScan carry seen)) t) := by
  let mid := (sweep carry bs).1
  let rem := (sweep carry bs).2
  let tail := (flush 3 rem).1
  have hm : mid.length = bs.length := sweep_length carry bs
  have ht : tail.length ≤ 3 := flush_length 3 rem
  have hout : finished carry bs = mid ++ tail := rfl
  have hseen : (seen || hasN mid || hasN tail) = (seen || hasN (finished carry bs)) := by
    simp only [hout,hasN,List.any_append,Bool.or_assoc]
  have ho : (finished carry bs).length ≤ bs.length + 3 := by
    rw [hout, List.length_append, hm]
    omega
  have first := scan_prefix source p [] bs carry seen
  have firstSafe := scan_prefix_safe source p [] bs carry seen (bs.length + 3)
    (by simp)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at first firstSafe
  obtain ⟨t, htime, hflush, hflushSafe⟩ := scan_flush source p mid rem (seen || hasN mid) 3
    (bs.length + 3) (flush_three_zero rem) (by omega)
  have flushEnd :
      run (boundary source p mid (bs.length + 1) (.finishScan rem (seen || hasN mid))) t =
        boundary source p (finished carry bs) ((finished carry bs).length + 1)
          (.finishRewindMove (seen || hasN (finished carry bs))) := by
    simpa only [hout, hasN, List.any_append, Bool.or_assoc, List.length_append, Nat.cast_add, hm] using hflush
  have flushSafe : ∀ n ≤ t, Safe source p (bs.length + 3)
      (run (boundary source p mid (bs.length + 1) (.finishScan rem (seen || hasN mid))) n) := by
    simpa only [hm] using hflushSafe
  let out := finished carry bs
  let positive := seen || hasN out
  have turn :
      run (boundary source p out (out.length + 1) (.finishRewindMove positive)) 1 =
        boundary source p out out.length (.finishRewind positive) := by
    apply config_ext
    · rfl
    · funext k
      simp [run, step, program, boundary, Function.update_apply]
      by_cases hk : k = workTrack <;> simp [hk]
    · rfl
  have turnSafe : ∀ n ≤ 1, Safe source p (bs.length + 3)
      (run (boundary source p out (out.length + 1) (.finishRewindMove positive)) n) := by
    intro n hn
    interval_cases n
    all_goals
      simp [Safe, run, step, program, boundary, Function.update_apply,
        workTrack, sourceTrack]
      repeat' apply And.intro
      all_goals first | (intro k hw hs; simp [hw, hs]) | (dsimp [out] at *; omega)
  obtain ⟨rewindEnd, rewindSafe⟩ := rewind_all source p out out.length positive
    (by rfl) (bs.length + 3) ho
  let T := (2 * out.length + 1) + (1 + (t + 3 * bs.length))
  refine ⟨T, by dsimp [T, out]; omega, ?_, ho, ?_⟩
  · dsimp [T]
    simp only [run, Function.iterate_add_apply]
    change run (run (run (run _ (3 * bs.length)) t) 1) (2 * out.length + 1) = _
    rw [first, flushEnd, turn]
    exact rewindEnd
  · have s1 := safe_join source p (bs.length + 3) (3 * bs.length) t
      _ _ first firstSafe flushSafe
    have e1 : run (boundary source p bs 1 (.finishScan carry seen))
        (t + 3 * bs.length) =
        boundary source p out (out.length + 1) (.finishRewindMove positive) := by
      rw [run, Function.iterate_add_apply]
      change run (run _ (3 * bs.length)) t = _
      rw [first]
      exact flushEnd
    have s2 := safe_join source p (bs.length + 3) (t + 3 * bs.length) 1
      _ _ e1 s1 turnSafe
    have e2 : run (boundary source p bs 1 (.finishScan carry seen))
        (1 + (t + 3 * bs.length)) =
        boundary source p out out.length (.finishRewind positive) := by
      rw [run, Function.iterate_add_apply]
      change run (run _ (t + 3 * bs.length)) 1 = _
      rw [e1]
      exact turn
    exact safe_join source p (bs.length + 3) (1 + (t + 3 * bs.length))
      (2 * out.length + 1) _ _ e2 s2 rewindSafe

theorem transfer_values : ∀ (c : Fin 5) (b : Bits),
    (finishTransfer c b).1.1 = b.1 ∧
    (finishTransfer c b).1.2.1 = b.2.1 ∧
    (finishTransfer c b).1.2.2.1 = b.2.2.1 ∧
    (finishTransfer c b).1.2.2.2.toNat + 2 * (finishTransfer c b).2.val =
      2 * b.1.toNat + 3 * b.2.1.toNat + c.val := by decide

theorem sweep_values (c : Fin 5) (bs : List Bits) :
    value1 (sweep c bs).1 = value1 bs ∧
    value2 (sweep c bs).1 = value2 bs ∧
    valueCount (sweep c bs).1 = valueCount bs ∧
    valueN (sweep c bs).1 + 2 ^ bs.length * (sweep c bs).2.val =
      2 * value1 bs + 3 * value2 bs + c.val := by
  induction bs generalizing c with
  | nil => simp [sweep,value1,value2,valueCount,valueN,bitValue]
  | cons b bs ih =>
    obtain ⟨h1,h2,hk,hn⟩ := ih (finishTransfer c b).2
    obtain ⟨t1,t2,tk,tn⟩ := transfer_values c b
    simp only [sweep,List.length_cons,pow_succ,
      value1,value2,valueCount,valueN,bitValue,List.map_cons,Nat.ofDigits_cons] at *
    simp only [t1,t2,tk]
    exact ⟨by omega,by omega,by omega,by nlinarith only [hn,tn]⟩

theorem flush_values (fuel : ℕ) (c : Fin 5) (hstop : (flush fuel c).2 = 0) :
    value1 (flush fuel c).1 = 0 ∧
    value2 (flush fuel c).1 = 0 ∧
    valueCount (flush fuel c).1 = 0 ∧
    valueN (flush fuel c).1 = c.val := by
  induction fuel generalizing c with
  | zero =>
    have hc : c = 0 := hstop
    simp [flush,hc,value1,value2,valueCount,valueN,bitValue]
  | succ fuel ih =>
    by_cases hc : c ≠ 0
    · have hs : (flush fuel (finishTransfer c zeros).2).2 = 0 := by
        simpa [flush,hc] using hstop
      obtain ⟨h1,h2,hk,hn⟩ := ih (finishTransfer c zeros).2 hs
      obtain ⟨t1,t2,tk,tn⟩ := transfer_values c zeros
      have hflush : flush (fuel+1) c =
          ((finishTransfer c zeros).1 :: (flush fuel (finishTransfer c zeros).2).1,
            (flush fuel (finishTransfer c zeros).2).2) := by simp [flush,hc]
      rw [hflush]
      simp only [value1,value2,valueCount,valueN,bitValue,List.map_cons,Nat.ofDigits_cons]
      simp only [t1,t2,tk]
      simp only [value1,value2,valueCount,valueN,bitValue] at h1 h2 hk hn
      dsimp [zeros] at *
      exact ⟨by omega,by omega,by omega,by omega⟩
    · have hz : c = 0 := by simpa using hc
      simp [flush,hz,value1,value2,valueCount,valueN,bitValue]

theorem finished_values (c : Fin 5) (bs : List Bits) :
    value1 (finished c bs) = value1 bs ∧
    value2 (finished c bs) = value2 bs ∧
    valueCount (finished c bs) = valueCount bs ∧
    valueN (finished c bs) = 2 * value1 bs + 3 * value2 bs + c.val := by
  obtain ⟨h1,h2,hk,hn⟩ := sweep_values c bs
  obtain ⟨f1,f2,fk,fn⟩ := flush_values 3 (sweep c bs).2 (flush_three_zero _)
  simp only [finished,value1,value2,valueCount,valueN,bitValue_append,sweep_length] at *
  rw [f1,f2,fk,fn]
  simpa using And.intro h1 (And.intro h2 (And.intro hk hn))

theorem hasN_iff_pos (bs : List Bits) : hasN bs = true ↔ 0 < valueN bs := by
  induction bs with
  | nil => simp [hasN,valueN,bitValue]
  | cons b bs ih =>
    simp only [hasN,List.any_cons,Bool.or_eq_true,valueN,bitValue,List.map_cons,
      Nat.ofDigits_cons] at *
    cases hb : b.2.2.2 <;> simp_all


end Terminal
end PhysicalWindowContinuation
