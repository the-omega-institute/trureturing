/- GID: D5/S0/Computability/WindowAcquisitionPrefixes
   generality: I
   mirror-B: D5/B/S0/Computability/WindowAcquisitionPrefixes
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Actual input prefixes preserve original Horner columns, seams and counters. -/

import D5.S0.Computability.WindowAcquisitionCore

namespace PhysicalWindowContinuation
def bitValue (pick : Bits → Bool) (bs : List Bits) : ℕ :=
  Nat.ofDigits 2 (bs.map (fun b => (pick b).toNat))

def value1 := bitValue Prod.fst
def value2 := bitValue (fun b : Bits => b.2.1)
def valueCount := bitValue (fun b : Bits => b.2.2.1)
def valueN := bitValue (fun b : Bits => b.2.2.2)

theorem transfer_conservation : ∀ (c : Carry) (b : Bits),
    (transfer c b).1.1.toNat + 2 * (transfer c b).2.first.val =
      b.1.toNat + 2 * b.2.1.toNat + c.first.val ∧
    (transfer c b).1.2.1.toNat + 2 * (transfer c b).2.second.val =
      2 * b.1.toNat + 3 * b.2.1.toNat + c.second.val ∧
    (transfer c b).1.2.2.1.toNat + 2 * (transfer c b).2.count.toNat =
      b.2.2.1.toNat + c.count.toNat := by decide

theorem sweep_conservation (c : Carry) (bs : List Bits) :
    value1 (sweep c bs).1 + 2 ^ bs.length * (sweep c bs).2.first.val =
      value1 bs + 2 * value2 bs + c.first.val ∧
    value2 (sweep c bs).1 + 2 ^ bs.length * (sweep c bs).2.second.val =
      2 * value1 bs + 3 * value2 bs + c.second.val ∧
    valueCount (sweep c bs).1 + 2 ^ bs.length * (sweep c bs).2.count.toNat =
      valueCount bs + c.count.toNat := by
  induction bs generalizing c with
  | nil => simp [sweep, value1, value2, valueCount, bitValue]
  | cons b bs ih =>
    obtain ⟨h1,h2,hk⟩ := ih (transfer c b).2
    obtain ⟨t1,t2,tk⟩ := transfer_conservation c b
    simp only [sweep, List.length_cons, pow_succ,
      value1, value2, valueCount, bitValue, List.map_cons, Nat.ofDigits_cons] at *
    exact ⟨by nlinarith only [h1,t1], by nlinarith only [h2,t2],
      by nlinarith only [hk,tk]⟩

theorem inactive_values : ∀ c : Carry, active c = false →
    c.first.val = 0 ∧ c.second.val = 0 ∧ c.count.toNat = 0 := by decide

theorem flush_conservation (fuel : ℕ) (c : Carry)
    (hstop : active (flush fuel c).2 = false) :
    value1 (flush fuel c).1 = c.first.val ∧
    value2 (flush fuel c).1 = c.second.val ∧
    valueCount (flush fuel c).1 = c.count.toNat := by
  induction fuel generalizing c with
  | zero =>
    obtain ⟨h1,h2,hk⟩ := inactive_values c hstop
    simp [flush, value1, value2, valueCount, bitValue, h1,h2,hk]
  | succ fuel ih =>
    by_cases ha : active c = true
    · have hs : active (flush fuel (transfer c zeros).2).2 = false := by
        simpa [flush, ha] using hstop
      obtain ⟨h1,h2,hk⟩ := ih (transfer c zeros).2 hs
      obtain ⟨t1,t2,tk⟩ := transfer_conservation c zeros
      simp only [flush, ha, ↓reduceIte, value1, value2, valueCount, bitValue, List.map_cons, Nat.ofDigits_cons]
      simp only [value1, value2, valueCount, bitValue] at h1 h2 hk
      dsimp [zeros] at *
      exact ⟨by omega, by omega, by omega⟩
    · have hn : active c = false := by cases hh : active c <;> simp_all
      obtain ⟨h1,h2,hk⟩ := inactive_values c hn
      simp [flush, hn, value1, value2, valueCount, bitValue, h1,h2,hk]

theorem bitValue_append (pick : Bits → Bool) (as bs : List Bits) :
    bitValue pick (as ++ bs) = bitValue pick as + 2 ^ as.length * bitValue pick bs := by
  simpa only [bitValue,List.map_append,List.length_map] using
    (Nat.ofDigits_append (b := 2)
      (l1 := as.map (fun b => (pick b).toNat))
      (l2 := bs.map (fun b => (pick b).toNat)))

theorem updated_values (c : Carry) (bs : List Bits) :
    value1 (updated c bs) = value1 bs + 2 * value2 bs + c.first.val ∧
    value2 (updated c bs) = 2 * value1 bs + 3 * value2 bs + c.second.val ∧
    valueCount (updated c bs) = valueCount bs + c.count.toNat := by
  obtain ⟨h1,h2,hk⟩ := sweep_conservation c bs
  obtain ⟨f1,f2,fk⟩ := flush_conservation 3 (sweep c bs).2
    (flush_three_inactive (sweep c bs).2)
  simp only [updated, value1, value2, valueCount, bitValue_append,
    sweep_length] at *
  rw [f1,f2,fk]
  exact ⟨h1,h2,hk⟩

def Frame (source : ℤ → Symbol) (H W : ℕ) (c : Configuration) : Prop :=
  c.cell sourceTrack = source ∧
  (∀ t, t ≠ workTrack → t ≠ sourceTrack →
    c.head t = 0 ∧ c.cell t = fun _ => .blank) ∧
  0 ≤ c.head sourceTrack ∧ c.head sourceTrack ≤ H ∧
  0 ≤ c.head workTrack ∧ c.head workTrack ≤ W

theorem safe_frame (source : ℤ → Symbol) (p : ℤ) (L H W : ℕ)
    (c : Configuration) (hp : 0 ≤ p) (hpH : p ≤ H) (hL : L + 1 ≤ W)
    (hs : Safe source p L c) : Frame source H W c := by
  rcases hs with ⟨hm,hh,ht,h0,h1⟩
  exact ⟨hm,ht,by omega,by omega,h0,by omega⟩

theorem frame_join (source : ℤ → Symbol) (H W a b : ℕ)
    (x y : Configuration) (he : run x a = y)
    (hx : ∀ t ≤ a, Frame source H W (run x t))
    (hy : ∀ t ≤ b, Frame source H W (run y t)) :
    ∀ t ≤ b + a, Frame source H W (run x t) := by
  intro t ht
  by_cases hta : t ≤ a
  · exact hx t hta
  · rw [show t = (t - a) + a by omega, run, Function.iterate_add_apply]
    change Frame source H W (run (run x a) (t - a))
    rw [he]
    exact hy _ (by omega)

def windowCarry (w : Window) : Carry :=
  ⟨(displacement w).1, (displacement w).2, true⟩

theorem source_enter (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous : Bool) (w : Window) (hr : source p = .window w)
    (hg : (previous && high w) = false) :
    run (boundary source p bs 0 (.source previous)) 2 =
      boundary source p bs 1 (.scan (low w) (windowCarry w)) := by
  have hnot : ¬ (previous = true ∧ high w = true) := by
    intro ⟨h1,h2⟩
    simp [h1,h2] at hg
  simp only [run, show 2 = 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · simp [step, program, boundary, hr, hnot, workTrack, sourceTrack, windowCarry]
  · funext t
    simp [step, program, boundary, hr, hnot, Function.update_apply, workTrack, sourceTrack]
    by_cases hw : t = 1 <;> by_cases hs : t = 0 <;> simp_all
  · simp [step, program, boundary, hr, hnot, workTrack, sourceTrack]

theorem source_advance (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous : Bool) :
    run (boundary source p bs 0 (.sourceMove previous)) 1 =
      boundary source (p + 1) bs 0 (.source previous) := by
  apply config_ext
  · rfl
  · funext t
    simp [run, step, program, boundary, Function.update_apply, workTrack, sourceTrack]
    by_cases hs : t = 0 <;> by_cases hw : t = 1 <;> simp_all
  · rfl



theorem source_enter_safe (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous : Bool) (w : Window) (hr : source p = .window w)
    (hg : (previous && high w) = false) :
    ∀ n ≤ 2, Safe source p (bs.length + 3)
      (run (boundary source p bs 0 (.source previous)) n) := by
  have hnot : ¬ (previous = true ∧ high w = true) := by
    intro ⟨h1,h2⟩
    simp [h1,h2] at hg
  intro n hn
  interval_cases n
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Safe, step, program, boundary, hr, hnot, Function.update_apply,
      workTrack, sourceTrack]
    repeat' apply And.intro
    all_goals first | (intro t hw hs; simp [hw,hs]) | omega

theorem source_advance_frame (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous : Bool) (H W : ℕ) (hp : 0 ≤ p) (hH : p + 1 ≤ H) :
    ∀ n ≤ 1, Frame source H W
      (run (boundary source p bs 0 (.sourceMove previous)) n) := by
  intro n hn
  interval_cases n
  all_goals
    simp [Frame, run, step, program, boundary, Function.update_apply,
      workTrack, sourceTrack]
    refine ⟨?_,by omega,by omega⟩
    intro t hw hs
    simp [hw,hs]

theorem one_window_run (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous : Bool) (w : Window) (H W : ℕ)
    (hr : source p = .window w) (hg : (previous && high w) = false)
    (hp : 0 ≤ p) (hH : p + 1 ≤ H) (hW : bs.length + 4 ≤ W) :
    ∃ T : ℕ, T ≤ 5 * bs.length + 21 ∧
      run (boundary source p bs 0 (.source previous)) T =
        boundary source (p + 1) (updated (windowCarry w) bs) 0 (.source (low w)) ∧
      (updated (windowCarry w) bs).length ≤ bs.length + 3 ∧
      ∀ n ≤ T, Frame source H W
        (run (boundary source p bs 0 (.source previous)) n) := by
  obtain ⟨T,hT,he,hb,hs⟩ := update_scan_return source p bs (low w) (windowCarry w)
  have hstart := source_enter source p bs previous w hr hg
  have hmove := source_advance source p (updated (windowCarry w) bs) (low w)
  have e1 : run (boundary source p bs 0 (.source previous)) (T + 2) =
      boundary source p (updated (windowCarry w) bs) 0 (.sourceMove (low w)) := by
    rw [run,Function.iterate_add_apply]
    change run (run _ 2) T = _
    rw [hstart]
    exact he
  refine ⟨1 + (T + 2),by omega,?_,hb,?_⟩
  · rw [run,Function.iterate_add_apply]
    change run (run _ (T + 2)) 1 = _
    rw [e1]
    exact hmove
  · apply frame_join source H W (T + 2) 1 _ _ e1
    · apply frame_join source H W 2 T _ _ hstart
      · intro n hn
        exact safe_frame source p (bs.length+3) H W _ hp (by omega) hW
          (source_enter_safe source p bs previous w hr hg n hn)
      · intro n hn
        exact safe_frame source p (bs.length+3) H W _ hp (by omega) hW (hs n hn)
    · exact source_advance_frame source p (updated (windowCarry w) bs) (low w)
        H W hp hH

def Legal : Bool → List Window → Prop
  | _, [] => True
  | previous, w :: ws => (previous && high w) = false ∧ Legal (low w) ws

def columnsAfter (bs : List Bits) (w : List Window) : List Bits :=
  w.foldl (fun old letter => updated (windowCarry letter) old) bs

def seamAfter (previous : Bool) (w : List Window) : Bool :=
  w.foldl (fun _ letter => low letter) previous

theorem windows_run (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous : Bool) (w : List Window) (H W : ℕ)
    (hr : ∀ j : ℕ, (hj : j < w.length) → source (p + j) = .window w[j])
    (hg : Legal previous w) (hp : 0 ≤ p)
    (hH : p + w.length ≤ H) (hW : bs.length + 3 * w.length + 4 ≤ W) :
    ∃ T : ℕ, T ≤ w.length * (5 * W + 21) ∧
      run (boundary source p bs 0 (.source previous)) T =
        boundary source (p + w.length) (columnsAfter bs w) 0
          (.source (seamAfter previous w)) ∧
      (columnsAfter bs w).length ≤ bs.length + 3 * w.length ∧
      ∀ n ≤ T, Frame source H W
        (run (boundary source p bs 0 (.source previous)) n) := by
  induction w generalizing p bs previous with
  | nil =>
    refine ⟨0,by simp,by simp [run,columnsAfter,seamAfter],by simp [columnsAfter],?_⟩
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    apply safe_frame source p 0 H W _ hp (by simpa using hH) (by omega)
    exact boundary_safe source p bs 0 (.source previous) 0 (by omega) (by omega)
  | cons a w ih =>
    obtain ⟨T1,hT1,he1,hlen1,hs1⟩ := one_window_run source p bs previous a H W
      (by
        have hx := hr 0 (by simp)
        change source (p + 0) = Symbol.window a at hx
        simpa only [Int.add_zero] using hx) hg.1 hp
      (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hH; omega)
      (by simp only [List.length_cons] at hW; omega)
    have hr' : ∀ j : ℕ, (hj : j < w.length) → source (p + 1 + j) = .window w[j] := by
      intro j hj
      have h := hr (j+1) (by simpa using Nat.succ_lt_succ hj)
      simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm] using h
    obtain ⟨T2,hT2,he2,hlen2,hs2⟩ := ih (p+1) (updated (windowCarry a) bs)
      (low a) hr' hg.2 (by omega)
      (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hH; omega)
      (by simp only [List.length_cons] at hW; omega)
    refine ⟨T2+T1,?_,?_,?_,?_⟩
    · have hlen : bs.length ≤ W := by omega
      have hlocal : T1 ≤ 5 * W + 21 := by omega
      calc T2 + T1 ≤ w.length * (5 * W + 21) + (5 * W + 21) :=
          Nat.add_le_add hT2 hlocal
        _ = (a :: w).length * (5 * W + 21) := by simp only [List.length_cons]; ring
    · rw [run,Function.iterate_add_apply]
      change run (run _ T1) T2 = _
      rw [he1]
      simpa [columnsAfter,seamAfter,Int.add_assoc,Int.add_comm,Int.add_left_comm]
        using he2
    · simpa only [columnsAfter,List.foldl_cons,List.length_cons] using
        (show (columnsAfter (updated (windowCarry a) bs) w).length ≤
          bs.length + 3 * (w.length + 1) by omega)
    · exact frame_join source H W T1 T2 _ _ he1 hs1 hs2



def inputSource (w : List Window) (e : Bool) (z : ℤ) : Symbol :=
  if 0 ≤ z then ((w.map Symbol.window ++ [.unit e])[z.toNat]?).getD .blank
  else .blank

theorem initialization (w : List Window) (e : Bool) :
    run (initial w e) 4 = boundary (inputSource w e) 0 [zeros] 0 (.source false) := by
  simp only [run, show 4 = 1 + 1 + 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · rfl
  · funext t
    by_cases hw : t = workTrack <;> by_cases hs : t = sourceTrack <;>
      simp_all [step,program,initial,boundary,workTrack,sourceTrack]
  · funext t z
    by_cases hw : t = workTrack
    · subst t
      by_cases h0 : z = 0
      · simp [step,program,initial,boundary,word,h0,
          workTrack,sourceTrack]
      by_cases h1 : z = 1
      · simp [step,program,initial,boundary,word,h1,
          workTrack,sourceTrack]
      by_cases hp : 0 < z
      · have hn : z.toNat - 1 ≠ 0 := by omega
        simp [step,program,initial,boundary,word,h0,h1,hp,hn,
          workTrack,sourceTrack]
      · simp [step,program,initial,boundary,word,h0,h1,hp,
          workTrack,sourceTrack]
    · by_cases hs : t = sourceTrack
      · subst t
        simp [step,program,initial,boundary,inputSource,
          workTrack,sourceTrack]
      · simp [step,program,initial,boundary,hw,hs]

theorem initialization_frame (w : List Window) (e : Bool) (H W : ℕ)
    (hW : 1 ≤ W) :
    ∀ n ≤ 4, Frame (inputSource w e) H W (run (initial w e) n) := by
  intro n hn
  interval_cases n
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Frame, step, program, initial, Function.update_apply,
      workTrack,sourceTrack]
    repeat' apply And.intro
    all_goals first | (intro t hw hs; simp [hw,hs]) |
      (funext z; simp [inputSource]) | omega

theorem columnsAfter_count (bs : List Bits) (w : List Window) :
    valueCount (columnsAfter bs w) = valueCount bs + w.length := by
  induction w generalizing bs with
  | nil => simp [columnsAfter]
  | cons a w ih =>
    simpa [columnsAfter,List.foldl_cons,windowCarry,Bool.toNat_true,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using (ih (updated (windowCarry a) bs)).trans
        (congrArg (fun n => n + w.length) (updated_values (windowCarry a) bs).2.2)

theorem input_prefix_run (pre suf : List Window) (e : Bool)
    (hg : Legal false pre) :
    ∃ T : ℕ, T ≤ 4 + pre.length * (15 * (pre ++ suf).length + 46) ∧
      run (initial (pre ++ suf) e) T =
        boundary (inputSource (pre ++ suf) e) pre.length
          (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre)) ∧
      valueCount (columnsAfter [zeros] pre) = pre.length ∧
      (columnsAfter [zeros] pre).length ≤ 1 + 3 * pre.length ∧
      ∀ n ≤ T, Frame (inputSource (pre ++ suf) e)
        (pre ++ suf).length (3 * (pre ++ suf).length + 5)
        (run (initial (pre ++ suf) e) n) := by
  have hr : ∀ j : ℕ, (hj : j < pre.length) →
      inputSource (pre ++ suf) e (0 + j) = .window pre[j] := by
    intro j hj
    simp [inputSource,List.map_append,List.getElem?_append,hj]
  obtain ⟨T,hT,he,hb,hs⟩ := windows_run (inputSource (pre ++ suf) e) 0 [zeros]
    false pre (pre ++ suf).length (3 * (pre ++ suf).length + 5) hr hg
    (by omega) (by simp) (by simp; omega)
  refine ⟨T + 4,?_,?_,?_,by simpa using hb,?_⟩
  · have hh : pre.length * (5 * (3 * (pre ++ suf).length + 5) + 21) =
        pre.length * (15 * (pre ++ suf).length + 46) := by ring
    rw [hh] at hT
    omega
  · rw [run,Function.iterate_add_apply]
    change run (run _ 4) T = _
    rw [initialization]
    simpa using he
  · simpa [valueCount,bitValue, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil,zeros] using columnsAfter_count [zeros] pre
  · exact frame_join (inputSource (pre ++ suf) e) (pre ++ suf).length
      (3 * (pre ++ suf).length + 5) 4 T _ _ (initialization (pre ++ suf) e)
      (initialization_frame (pre ++ suf) e _ _ (by omega)) hs



namespace Original
open D5.S3.Arith.FibonacciAtomic
abbrev Letter := LiteralWindowEnd.Window

def letter : Window → Letter
  | .zero => .zero
  | .low => .low
  | .middle => .middle
  | .both => .ends
  | .high => .high

def pair (bs : List Bits) : ℕ × ℕ := (value1 bs,value2 bs)

def numericStep (c : ℕ × ℕ) (b : Letter) : ℕ × ℕ :=
  GraftAffineClosure.step (GraftAffineClosure.step (GraftAffineClosure.step c)) +
    NativeContinuation.NullReplyFiber.bitComposition b

theorem update_pair (b : Window) (bs : List Bits) :
    pair (updated (windowCarry b) bs) = numericStep (pair bs) (letter b) := by
  obtain ⟨h1,h2,_⟩ := updated_values (windowCarry b) bs
  cases b <;> apply Prod.ext
  all_goals
    simp only [pair,numericStep,letter,GraftAffineClosure.step,
      NativeContinuation.NullReplyFiber.bitComposition,LiteralWindowEnd.bits,
      D5.S3.Arith.ZeckendorfFutureKernel.value,windowCarry,displacement,
      Prod.mk_add_mk,Fin.val_zero,Fin.val_one] at *
    simp_all only [Bool.false_eq_true,↓reduceIte,zero_add,add_zero]
    all_goals omega

theorem columns_pair (bs : List Bits) (w : List Window) :
    pair (columnsAfter bs w) = (w.map letter).foldl numericStep (pair bs) := by
  induction w generalizing bs with
  | nil => rfl
  | cons a w ih =>
    simp only [columnsAfter,List.foldl_cons,List.map_cons]
    rw [← update_pair]
    exact ih (updated (windowCarry a) bs)

theorem original_composition (w : List Window) :
    pair (columnsAfter [zeros] w) = NativeContinuation.JointLaw.composition (w.map letter) := by
  change pair (columnsAfter [zeros] w) = (w.map letter).foldl numericStep (0,0)
  simpa only [pair,value1,value2,bitValue, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil,zeros,Bool.toNat_false,mul_zero,add_zero]
    using columns_pair [zeros] w

theorem original_legal (s : Bool) (w : List Window) :
    Legal s w ↔ D5.S3.Arith.ZeckendorfFutureKernel.legal s
      (NativeContinuation.NullReplyFiber.highBits (w.map letter)) := by
  induction w generalizing s with
  | nil => simp [Legal,NativeContinuation.NullReplyFiber.highBits,
      D5.S3.Arith.ZeckendorfFutureKernel.legal]
  | cons a w ih =>
    have hi := ih (low a)
    cases s <;> cases a <;>
      simp [Legal,letter,low,high,NativeContinuation.NullReplyFiber.highBits,
        LiteralWindowEnd.bits,D5.S3.Arith.ZeckendorfFutureKernel.legal]
    all_goals simpa [NativeContinuation.NullReplyFiber.highBits,low,LiteralWindowEnd.bits] using hi

theorem source_prefix_registers (pre suf : List Window) (e : Bool)
    (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false
      (NativeContinuation.NullReplyFiber.highBits ((pre ++ suf).map letter))) :
    ∃ T : ℕ, T ≤ 4 + pre.length * (15 * (pre ++ suf).length + 46) ∧
      run (initial (pre ++ suf) e) T =
        boundary (inputSource (pre ++ suf) e) pre.length
          (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre)) ∧
      pair (columnsAfter [zeros] pre) =
        NativeContinuation.JointLaw.composition (pre.map letter) ∧
      valueCount (columnsAfter [zeros] pre) = pre.length ∧
      (columnsAfter [zeros] pre).length ≤ 1 + 3 * pre.length ∧
      ∀ n ≤ T, Frame (inputSource (pre ++ suf) e)
        (pre ++ suf).length (3 * (pre ++ suf).length + 5)
        (run (initial (pre ++ suf) e) n) := by
  have hpre : D5.S3.Arith.ZeckendorfFutureKernel.legal false
      (NativeContinuation.NullReplyFiber.highBits (pre.map letter)) := by
    rw [List.map_append,NativeContinuation.NullReplyFiber.highBits,List.flatMap_append]
      at hg
    exact (D5.S3.Arith.ZeckendorfFutureKernel.legal_append _ _ false).mp hg |>.1
  obtain ⟨T,hT,he,hc,hb,hs⟩ := input_prefix_run pre suf e ((original_legal false pre).mpr hpre)
  exact ⟨T,hT,he,original_composition pre,hc,hb,hs⟩

/-- The existing numeral theorem is applied to the reached physical column. -/
theorem physical_numeral_correspondence (w : List Window) (e : Bool) :
    (D5.S1.Digit.GoldenBase4IntervalMachine.fibPair
      (NativeContinuation.JointLaw.digits (w.map letter) ++ [if e then 1 else 0])).1 =
        2 * value1 (columnsAfter [zeros] w) +
          3 * value2 (columnsAfter [zeros] w) + e.toNat := by
  rw [D5.S1.Digit.GoldenBase4IntervalMachine.fibPair_append_digit,
    NativeContinuation.JointLaw.composition_coordinates,
    ← original_composition]
  cases e <;> simp [pair,GraftAffineClosure.step] <;> ring

end Original

theorem unit_enter (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous e : Bool) (hr : source p = .unit e)
    (hg : (previous && e) = false) :
    run (boundary source p bs 0 (.source previous)) 2 =
      boundary source p bs 1 (.finishScan (if e then 1 else 0) false) := by
  have hnot : ¬ (previous = true ∧ e = true) := by
    intro ⟨h1,h2⟩
    simp [h1,h2] at hg
  simp only [run,show 2 = 1+1 from rfl,
    Function.iterate_succ_apply,Function.iterate_zero_apply]
  apply config_ext
  · simp [step,program,boundary,hr,hnot,workTrack,sourceTrack]
  · funext t
    simp [step,program,boundary,hr,hnot,Function.update_apply,workTrack,sourceTrack]
    by_cases hw : t = 1 <;> by_cases hs : t = 0 <;> simp_all
  · simp [step,program,boundary,hr,hnot,workTrack,sourceTrack]

theorem unit_enter_safe (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous e : Bool) (hr : source p = .unit e)
    (hg : (previous && e) = false) :
    ∀ n ≤ 2, Safe source p (bs.length+3)
      (run (boundary source p bs 0 (.source previous)) n) := by
  have hnot : ¬ (previous = true ∧ e = true) := by
    intro ⟨h1,h2⟩
    simp [h1,h2] at hg
  intro n hn
  interval_cases n
  all_goals
    simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
    simp [Safe,step,program,boundary,hr,hnot,Function.update_apply,workTrack,sourceTrack]
    repeat' apply And.intro
    all_goals first | (intro t hw hs; simp [hw,hs]) | omega

namespace Original
open D5.S3.Arith.FibonacciAtomic

theorem original_flag (s : Bool) (w : List Window) :
    D5.S3.Arith.ZeckendorfFutureKernel.flag s
      (NativeContinuation.NullReplyFiber.highBits (w.map letter)) = seamAfter s w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    have hi := ih (low a)
    cases a <;>
      simpa [NativeContinuation.NullReplyFiber.highBits,List.flatMap_cons,
        LiteralWindowEnd.bits,letter,D5.S3.Arith.ZeckendorfFutureKernel.flag,
        seamAfter,low] using hi

theorem legal_with_unit (s : Bool) (w : List Window) (e : Bool) :
    D5.S3.Arith.ZeckendorfFutureKernel.legal s
      (NativeContinuation.NullReplyFiber.highBits (w.map letter) ++ [e]) ↔
    Legal s w ∧ (seamAfter s w && e) = false := by
  rw [D5.S3.Arith.ZeckendorfFutureKernel.legal_append,original_flag,
    ← original_legal]
  cases e <;> cases hs : seamAfter s w <;>
    simp [D5.S3.Arith.ZeckendorfFutureKernel.legal]

theorem source_unit_entry (w : List Window) (e : Bool)
    (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false
      (NativeContinuation.NullReplyFiber.highBits (w.map letter) ++ [e])) :
    ∃ T : ℕ, T ≤ 6 + w.length * (15*w.length+46) ∧
      run (initial w e) T = boundary (inputSource w e) w.length
        (columnsAfter [zeros] w) 1 (.finishScan (if e then 1 else 0) false) ∧
      pair (columnsAfter [zeros] w) = NativeContinuation.JointLaw.composition (w.map letter) ∧
      valueCount (columnsAfter [zeros] w) = w.length ∧
      (columnsAfter [zeros] w).length ≤ 1+3*w.length ∧
      ∀ n ≤ T, Frame (inputSource w e) w.length (3*w.length+5)
        (run (initial w e) n) := by
  obtain ⟨hlegal,hguard⟩ := (legal_with_unit false w e).mp hg
  obtain ⟨T,hT,he,hcount,hlen,hs⟩ := input_prefix_run w [] e hlegal
  simp only [List.append_nil] at hT he hs
  have hr : inputSource w e (w.length : ℤ) = .unit e := by
    simp [inputSource]
  have henter := unit_enter (inputSource w e) w.length (columnsAfter [zeros] w)
    (seamAfter false w) e hr hguard
  refine ⟨2+T,by omega,?_,original_composition w,hcount,hlen,?_⟩
  · rw [run,Function.iterate_add_apply]
    change run (run _ T) 2 = _
    rw [he]
    exact henter
  · apply frame_join (inputSource w e) w.length (3*w.length+5) T 2 _ _ he hs
    intro n hn
    exact safe_frame (inputSource w e) w.length ((columnsAfter [zeros] w).length+3)
      w.length (3*w.length+5) _ (by omega) (by omega) (by omega)
      (unit_enter_safe (inputSource w e) w.length (columnsAfter [zeros] w)
        (seamAfter false w) e hr hguard n hn)

end Original
end PhysicalWindowContinuation
