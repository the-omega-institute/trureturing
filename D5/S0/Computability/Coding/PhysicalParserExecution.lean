/- GID: D5/S0/Computability/Coding/PhysicalParserExecution
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/PhysicalParserExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Size]
   utility: none
   digest: A complete physical six-field run with exact return frame and all-preword resource bounds. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import D5.S0.Computability.Coding.PhysicalParserField
import D5.S0.Computability.Coding.PhysicalParserPadding

namespace D5.S0.Computability.Coding.PhysicalParserExecution
open PhysicalSixParser

/-- The complete physical contract, with an explicitly framed injective address description. -/
theorem parser_frame_resources : Contract ∧
    (∀ x y : ℤ, headDescription x <+: headDescription y → x = y) ∧
    (∀ q : List Bool, ∀ n : ℕ,
      (run (initial q) n).head (0,true)=0 ∧
      (run (initial q) n).cell (0,false)=rawCell q) := by
  have configExt {a b : Configuration} (hc : a.control=b.control)
      (hh : a.head=b.head) (hm : a.cell=b.cell) : a=b := by
    cases a
    cases b
    cases hc
    cases hh
    cases hm
    rfl
  have unchanged (c : Configuration) :
      (step c).head (0,true)=c.head (0,true) ∧
      (step c).cell (0,false)=c.cell (0,false) := by
    have hp (i : Fin 6) : parameterPair i ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      simp [parameterPair] at hv
    cases hc : c.control with
    | init p => simp [step,program,hc,Function.update_apply]
    | start => simp [step,program,hc,Function.update_apply]
    | header i k =>
      rcases k with ⟨k,hk⟩
      interval_cases k <;> simp [step,program,hc,Function.update_apply,hp i,Ne.symm (hp i)]
    | payload i k =>
      rcases k with ⟨k,hk⟩
      interval_cases k <;> simp [step,program,hc,Function.update_apply,hp i,Ne.symm (hp i)]
    | consume next => simp [step,program,hc,Function.update_apply]
    | count next k =>
      rcases k with ⟨k,hk⟩
      interval_cases k <;> simp [step,program,hc,Function.update_apply]
    | sourceRewind k =>
      rcases k with ⟨k,hk⟩
      interval_cases k <;> simp [step,program,hc,Function.update_apply]
    | pad i k =>
      rcases k with ⟨k,hk⟩
      interval_cases k <;> simp [step,program,hc,Function.update_apply,hp i,Ne.symm (hp i)]
    | halt => simp [step,program,hc]
    | sink => simp [step,program,hc]
  have sourceInvariant : ∀ q : List Bool, ∀ n : ℕ,
      (run (initial q) n).head (0,true)=0 ∧
      (run (initial q) n).cell (0,false)=rawCell q := by
    intro q n
    induction n with
    | zero => simp [run,initial]
    | succ n ih =>
      simp only [run,Function.iterate_succ_apply']
      obtain ⟨hh,hc⟩ := unchanged (run (initial q) n)
      exact ⟨hh.trans ih.1,hc.trans ih.2⟩
  have address : ∀ x y : ℤ, headDescription x <+: headDescription y → x = y := by
    intro x y hp
    have hl := hp.length_le
    simp only [headDescription, List.length_append, List.length_cons,
      List.length_replicate, List.length_singleton] at hl
    have habs : x.natAbs = y.natAbs := by
      by_contra hn
      have hlt : x.natAbs < y.natAbs := by omega
      have hg := hp.getElem (i := x.natAbs + 1) (by simp [headDescription])
      simp [headDescription, List.getElem_append, hlt] at hg
    have sign := hp.getElem (i := 0) (by simp [headDescription])
    simp [headDescription] at sign
    cases x <;> cases y <;> simp_all <;> omega
  refine ⟨?_, address, sourceInvariant⟩
  let K := programDescription.length + Fintype.card Control
  refine ⟨256, K + 198, by omega, by omega, ?_⟩
  intro P A R B E C hP hA hR hB hE hC hPA hRB
  let v : Fin 6 → ℕ := ![P,A,R,B,E,C]
  let q := source v
  let s := q.length
  let words := List.ofFn (fun i => code (v i))
  let preword (k : ℕ) := (words.take k).flatten
  let consumed (k : ℕ) := (preword k).length
  let buffers (k : ℕ) : Track → ℤ → Bool := fun (p,b) =>
    if p = 0 then if b then fun z => decide (z=0) else rawCell q
    else if hp : 1 ≤ p.val ∧ p.val ≤ 6 then
      wordCell (if p.val ≤ k then (v ⟨p.val-1, by omega⟩).bits else []) b
    else wordCell [] b
  let control (k : ℕ) : Control :=
    if hk : k < 6 then .header ⟨k,hk⟩ 0 else .count .finish 0
  let phase (k : ℕ) := PhysicalParserTally.configuration (buffers k)
    (fun t => if t = (0,false) then (consumed k : ℤ)+1 else 0)
    (consumed k) (consumed k).bits 0 (control k)
  let Safe (c : Configuration) := ∀ t : Track, 0 ≤ c.head t ∧ c.head t ≤ (s:ℤ)+3
  have appendRun (x : Configuration) (a b : ℕ) :
      run x (b+a) = run (run x a) b := Function.iterate_add_apply step b a x
  have join (a b : ℕ) (x y : Configuration) (he : run x a = y)
      (hx : ∀ t ≤ a, Safe (run x t)) (hy : ∀ t ≤ b, Safe (run y t)) :
      ∀ t ≤ b+a, Safe (run x t) := by
    intro t ht
    by_cases hta : t ≤ a
    · exact hx t hta
    · rw [show t=(t-a)+a by omega]
      simp only [run, Function.iterate_add_apply]
      change Safe (run (run x a) (t-a))
      rw [he]
      exact hy _ (by omega)
  have prefixNext (i : Fin 6) : preword (i.val+1) = preword i.val ++ code (v i) := by
    change (words.take (i.val+1)).flatten = (words.take i.val).flatten ++ code (v i)
    rw [List.take_succ_eq_append_getElem (by simpa only [words,List.length_ofFn] using i.isLt)]
    simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      words,List.getElem_ofFn]
  have splitSource (i : Fin 6) :
      q = (preword i.val ++ code (v i)) ++ (words.drop (i.val+1)).flatten := by
    rw [← prefixNext]
    change words.flatten = (words.take (i.val+1)).flatten ++ (words.drop (i.val+1)).flatten
    rw [← List.flatten_append,List.take_append_drop]
  have consumedNext (i : Fin 6) : consumed (i.val+1) = consumed i.val + 2*(v i).bits.length+1 := by
    change (preword (i.val+1)).length = (preword i.val).length + 2*(v i).bits.length+1
    rw [prefixNext]
    simp only [List.length_append,code,List.length_replicate,List.length_cons,List.length_reverse]
    omega
  have consumedBound (k : ℕ) : consumed k ≤ s := by
    have he : q = preword k ++ (words.drop k).flatten := by
      change words.flatten = (words.take k).flatten ++ (words.drop k).flatten
      rw [← List.flatten_append,List.take_append_drop]
    have hh := congrArg List.length he
    simp only [List.length_append] at hh
    change (preword k).length ≤ q.length
    omega
  have emptyBuffer (i : Fin 6) :
      PhysicalParserField.memory (buffers i.val) i [] = buffers i.val := by
    funext t z
    rcases t with ⟨p,b⟩
    by_cases hp : p = parameterPair i
    · subst p
      simp [PhysicalParserField.memory, buffers, parameterPair,
        show ¬i.val+1 ≤ i.val by omega, show ¬i.val+1 = 0 by omega,
        show i.val+1 ≤ 6 by omega]
    · simp [PhysicalParserField.memory, hp]
  have fullBuffer (i : Fin 6) :
      PhysicalParserField.memory (buffers i.val) i (v i).bits = buffers (i.val+1) := by
    funext t z
    rcases t with ⟨p,b⟩
    by_cases hp : p = parameterPair i
    · subst p
      have idx : (⟨(i.val+1)-1, by omega⟩ : Fin 6) = i := by apply Fin.ext; simp
      simp [PhysicalParserField.memory, buffers, parameterPair,
        show ¬i.val+1 = 0 by omega, show i.val+1 ≤ 6 by omega, idx]
    · have hpv : p.val ≠ i.val+1 := by
        intro he
        apply hp
        apply Fin.ext
        exact he
      have he : (p.val ≤ i.val+1) = (p.val ≤ i.val) := by apply propext; omega
      simp [PhysicalParserField.memory, buffers, hp, he]
  have fieldHeads (i : Fin 6) (n : ℕ) :
      PhysicalParserField.heads (fun _=>0) i n 0 =
        (fun t => if t=(0,false) then (n:ℤ)+1 else 0) := by
    funext t
    simp [PhysicalParserField.heads]
  have fieldStep (i : Fin 6) : ∃ T : ℕ,
      T ≤ (2*(v i).bits.length+1)*(8*s+20)+2 ∧
      run (phase i.val) T = phase (i.val+1) ∧
      ∀ t ≤ T, Safe (run (phase i.val) t) := by
    have hr (k : ℕ) (hk : k < 2*(v i).bits.reverse.length+1) :
        buffers i.val (0,false) ((consumed i.val:ℤ)+k+1) =
          (List.replicate (v i).bits.reverse.length true ++ false :: (v i).bits.reverse)[k]?.getD false := by
      have hp : 0 < (consumed i.val:ℤ)+k+1 := by omega
      have hidx : ((consumed i.val:ℤ)+k+1).toNat-1 = consumed i.val+k := by omega
      have hcode : k < (code (v i)).length := by
        simp only [List.length_reverse] at hk
        simp only [code,List.length_append,List.length_replicate,List.length_cons,List.length_reverse]
        omega
      simp only [buffers, Fin.isValue, Bool.false_eq_true, ↓reduceIte]
      rw [rawCell, if_pos hp, hidx, splitSource i]
      rw [List.getElem?_append_left (by simp only [List.length_append]; change (preword i.val).length+k < _; omega)]
      rw [List.getElem?_append_right (by change (preword i.val).length ≤ (preword i.val).length+k; omega)]
      simp only [consumed,Nat.add_sub_cancel_left,code,List.length_reverse]
    obtain ⟨T,hT,he,hs⟩ := PhysicalParserField.parse_field (buffers i.val) (fun _=>0) i
      (consumed i.val) s (v i).bits.reverse
      (by simpa only [List.length_reverse, ← consumedNext] using consumedBound (i.val+1)) hr
    have startEq : PhysicalParserField.configuration (buffers i.val) (fun _=>0) i
        (consumed i.val) [] 0 (.header i 0) = phase i.val := by
      simp [PhysicalParserField.configuration, emptyBuffer, fieldHeads, phase, control, i.isLt]
    have nextEq : PhysicalParserField.next i = control (i.val+1) := by
      by_cases hi : i.val<5
      · simp [PhysicalParserField.next,control,hi,show i.val+1<6 by omega]
      · simp [PhysicalParserField.next,control,hi,show ¬i.val+1<6 by omega]
    have endEq : PhysicalParserField.configuration (buffers i.val) (fun _=>0) i
        (consumed i.val+2*(v i).bits.reverse.length+1) (v i).bits.reverse.reverse 0
        (PhysicalParserField.next i) = phase (i.val+1) := by
      simp [PhysicalParserField.configuration, fullBuffer, fieldHeads, phase,
        List.length_reverse, List.reverse_reverse, ← consumedNext, nextEq]
    rw [startEq, endEq] at he
    rw [startEq] at hs
    refine ⟨T, by simpa using hT, he, ?_⟩
    intro t ht v'
    obtain ⟨hc,hh,hb⟩ := hs t ht
    by_cases hv : v' = (0,false) ∨ v'.1=parameterPair i ∨ v'.1=7 ∨ v'.1=8
    · obtain ⟨hl,hu⟩ := hb v' hv
      constructor <;> omega
    · have hv' := not_or.mp hv
      have hs' := not_or.mp hv'.2
      have hs'' := not_or.mp hs'.2
      rw [hh v' hv'.1 hs'.1 hs''.1 hs''.2]
      dsimp [Safe]
      constructor <;> omega
  have parseAll (k : ℕ) (hk : k ≤ 6) : ∃ T : ℕ,
      T ≤ consumed k*(8*s+20)+2*k ∧ run (phase 0) T = phase k ∧
      ∀ t ≤ T, Safe (run (phase 0) t) := by
    induction k with
    | zero =>
      refine ⟨0, by simp [consumed, preword], rfl, ?_⟩
      intro t ht
      have : t=0 := by omega
      subst t
      intro ⟨p,b⟩
      cases b <;> simp [run, phase, consumed, preword, PhysicalParserTally.configuration,
        PhysicalParserTally.heads] <;> (try split_ifs) <;> omega
    | succ k ih =>
      obtain ⟨T,hT,he,hs⟩ := ih (by omega)
      obtain ⟨U,hU,ue,us⟩ := fieldStep ⟨k,by omega⟩
      refine ⟨U+T, ?_, ?_, join T U _ _ he hs us⟩
      · rw [consumedNext ⟨k,by omega⟩]
        simp only [Fin.val_mk, Nat.add_mul, Nat.one_mul] at *
        omega
      · simp only [run, Function.iterate_add_apply]
        change run (run (phase 0) T) U = _
        rw [he]
        exact ue
  have initRun : run (initial q) 10 = phase 0 := by
    simp only [run, show 10=1+1+1+1+1+1+1+1+1+1 from rfl,
      Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [step,program,initial]
    apply configExt
    · simp [step, program, initial, phase, control,PhysicalParserTally.configuration]
    · funext t
      rcases t with ⟨⟨p,hp⟩,b⟩
      interval_cases p <;> cases b <;>
        simp [step, program, initial, phase, consumed, preword,
          PhysicalParserTally.configuration, PhysicalParserTally.heads, Function.update_apply]
    · funext t z
      rcases t with ⟨⟨p,hp⟩,b⟩
      interval_cases p <;> cases b <;>
        simp [step, program, initial, phase, buffers, consumed, preword,
          PhysicalParserTally.configuration, PhysicalParserTally.memory, wordCell, Function.update_apply]
  have initSafe : ∀ t ≤ 10, Safe (run (initial q) t) := by
    intro t ht v'
    interval_cases t <;>
      simp [run, Function.iterate_succ_apply, step, program, initial,Function.update_apply] <;>
      (try split_ifs) <;> omega
  have allConsumed : consumed 6 = s := by simp [consumed, preword, words, s, q, source,Nat.add_assoc]
  obtain ⟨TP,hTP,hPE,hPS⟩ := parseAll 6 (by omega)
  rw [allConsumed] at hTP
  let W := s+1
  let finalMemory := PhysicalParserTally.memory (buffers 6) W W.bits
  let beforeRewind : Configuration := ⟨.sourceRewind 0, rewindHeads (fun _=>0) W W W, finalMemory⟩
  obtain ⟨TC,hTC,hCE,hCS⟩ := PhysicalParserTally.count_one (buffers 6)
    (fun t => if t=(0,false) then (s:ℤ)+1 else 0) s s .finish
  have countStart : PhysicalParserTally.configuration (buffers 6)
      (fun t => if t=(0,false) then (s:ℤ)+1 else 0) s s.bits 0 (.count .finish 0) = phase 6 := by
    simp [phase, control, allConsumed]
  have countEnd : PhysicalParserTally.configuration (buffers 6)
      (fun t => if t=(0,false) then (s:ℤ)+1 else 0) (s+1) (s+1).bits 0 (resume .finish) =
      beforeRewind := by
    apply configExt
    · rfl
    · funext t
      rcases t with ⟨p,b⟩
      by_cases h7 : p=7 <;> by_cases h0 : p=0 <;> cases b <;>
        simp [PhysicalParserTally.configuration, PhysicalParserTally.heads,
          beforeRewind, rewindHeads, W, Function.update_apply, h7, h0]
    · rfl
  rw [countStart,countEnd] at hCE
  rw [countStart] at hCS
  have countSafe : ∀ t ≤ TC, Safe (run (phase 6) t) := by
    intro t ht v'
    obtain ⟨hf,hu,hb⟩ := hCS t ht
    rcases v' with ⟨p,b⟩
    by_cases h7 : p=7
    · subst p
      obtain ⟨hl,hh⟩ := hu b
      constructor <;> omega
    · by_cases h8 : p=8
      · subst p
        obtain ⟨hl,hh⟩ := hb b
        have hbnd : s.bits.length ≤ s := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
        constructor <;> omega
      · rw [(hf (p,b) h7 h8).1]
        dsimp only
        split_ifs <;> constructor <;> omega
  let afterRewind : Configuration := ⟨.pad 0 0, fun _=>0, finalMemory⟩
  obtain ⟨hRE,hRS⟩ := coupled_source_rewind finalMemory (fun _=>0) W (s+3) W
    (by simp [finalMemory, PhysicalParserTally.memory, wordCell])
    (by
      intro j hj hjW
      simp [finalMemory, PhysicalParserTally.memory, wordCell, hj, Nat.ne_of_gt hj,
        hjW, show j-1 < W by omega]) (by omega) (by dsimp [W]; omega)
  have rewindEnd : (⟨.pad 0 0, rewindHeads (fun _=>0) 0 0 0, finalMemory⟩ : Configuration) = afterRewind := by
    congr 1
    funext t
    simp [rewindHeads]
  change run beforeRewind (5*W+2) = _ at hRE
  rw [rewindEnd] at hRE
  change ∀ t ≤ 5*W+2, RewindFrame finalMemory (fun _=>0) (s+3) (run beforeRewind t) at hRS
  have rewindSafe : ∀ t ≤ 5*W+2, Safe (run beforeRewind t) := by
    intro t ht v'
    obtain ⟨r,o,z,hr,hro,hoz,hskew,hz,hh,hcell⟩ := hRS t ht
    rw [hh]
    simp [rewindHeads]
    split_ifs <;> constructor <;> omega
  have widthBound (i : Fin 6) : (v i).bits.length ≤ W := by
    have hn := consumedBound (i.val+1)
    rw [consumedNext] at hn
    dsimp [W]
    omega
  let padded (k : ℕ) : Track → ℤ → Bool := fun (p,b) =>
    if h7 : p=7 then wordCell (List.replicate W true) b
    else if h8 : p=8 then wordCell W.bits b
    else if h0 : p=0 then if b then fun z => decide (z=0) else rawCell q
    else wordCell
      ((v ⟨p.val-1, by have := p.isLt; simp only [Fin.ext_iff] at h7 h8 h0; omega⟩).bits ++
        List.replicate (if p.val≤k then W-(v ⟨p.val-1, by have := p.isLt; simp only [Fin.ext_iff] at h7 h8 h0; omega⟩).bits.length else 0) false) b
  let padControl (k : ℕ) : Control := if hk : k<6 then .pad ⟨k,hk⟩ 0 else .halt
  let padPhase (k : ℕ) : Configuration := ⟨padControl k,fun _=>0,padded k⟩
  have padEntry : padPhase 0 = afterRewind := by
    apply configExt
    · rfl
    · rfl
    · funext t z
      rcases t with ⟨p,b⟩
      by_cases h7 : p=7
      · subst p; simp [padPhase,padded,afterRewind,finalMemory,PhysicalParserTally.memory]
      · by_cases h8 : p=8
        · subst p; simp [padPhase,padded,afterRewind,finalMemory,PhysicalParserTally.memory]
        · by_cases h0 : p=0
          · subst p; simp [padPhase,padded,afterRewind,finalMemory,PhysicalParserTally.memory,buffers]
          · have hb : 1≤p.val ∧ p.val≤6 := by
              have := p.isLt
              simp only [Fin.ext_iff] at h7 h8 h0
              omega
            simp [padPhase,padded,afterRewind,finalMemory,PhysicalParserTally.memory,buffers,
              h7,h8,h0,hb.1,hb.2,show ¬p.val≤0 by omega]
  have padStep (i : Fin 6) : ∃ T : ℕ, T≤14*W+11 ∧
      run (padPhase i.val) T = padPhase (i.val+1) ∧
      ∀ t≤T, Safe (run (padPhase i.val) t) := by
    have hi0 : parameterPair i ≠ 0 := by intro he; have := congrArg Fin.val he; simp [parameterPair] at this
    have hi7 : parameterPair i ≠ 7 := by intro he; have := congrArg Fin.val he; simp [parameterPair] at this; have := i.isLt; omega
    have hi8 : parameterPair i ≠ 8 := by intro he; have := congrArg Fin.val he; simp [parameterPair] at this; have := i.isLt; omega
    have frameHeads : PhysicalParserPadding.heads (fun _=>0) i 0 = (fun _=>0) := by
      funext t; simp [PhysicalParserPadding.heads]
    have cells (b : Bool) :
        PhysicalParserPadding.memory (padded i.val) i W
          ((v i).bits ++ List.replicate (if b then W-(v i).bits.length else 0) false) =
        padded (i.val + b.toNat) := by
      funext t z
      rcases t with ⟨p,v'⟩
      by_cases h7 : p=7
      · subst p; simp [PhysicalParserPadding.memory,padded]
      · by_cases hpi : p=parameterPair i
        · subst p
          have idx : (⟨(i.val+1)-1, by omega⟩ : Fin 6) = i := by apply Fin.ext; simp
          cases b <;> simp [PhysicalParserPadding.memory,padded, hi0,hi7,hi8,
            show (parameterPair i).val=i.val+1 from rfl,
            show ¬i.val+1=0 by omega, show ¬i.val+1=7 by omega,
            show ¬i.val+1=8 by omega, show ¬i.val+1≤i.val by omega,idx]
        · have hval : p.val ≠ i.val+1 := by intro he; apply hpi; apply Fin.ext; exact he
          have heq : (p.val ≤ i.val+1) = (p.val ≤ i.val) := by apply propext; omega
          cases b <;> simp [PhysicalParserPadding.memory,padded,h7,hpi,heq]
    obtain ⟨T,hT,he,hs⟩ := PhysicalParserPadding.pad_one (padded i.val) (fun _=>0) i W (v i).bits (widthBound i)
    have startEq : PhysicalParserPadding.configuration (padded i.val) (fun _=>0) i W (v i).bits 0 (.pad i 0) = padPhase i.val := by
      apply configExt
      · simp [PhysicalParserPadding.configuration,padPhase,padControl,i.isLt]
      · exact frameHeads
      · simpa [PhysicalParserPadding.configuration,padPhase] using cells false
    have endEq : PhysicalParserPadding.configuration (padded i.val) (fun _=>0) i W
        ((v i).bits ++ List.replicate (W-(v i).bits.length) false) 0 (PhysicalParserPadding.next i) = padPhase (i.val+1) := by
      apply configExt
      · by_cases hi : i.val<5
        · simp [PhysicalParserPadding.configuration,PhysicalParserPadding.next,padPhase,padControl,
            hi,show i.val+1<6 by omega]
        · simp [PhysicalParserPadding.configuration,PhysicalParserPadding.next,padPhase,padControl,
            hi,show ¬i.val+1<6 by omega]
      · exact frameHeads
      · simpa [PhysicalParserPadding.configuration,padPhase] using cells true
    rw [startEq,endEq] at he
    rw [startEq] at hs
    refine ⟨T,hT,he,?_⟩
    intro t ht ⟨p,b⟩
    obtain ⟨hf,hm,hr,hb⟩ := hs t ht
    by_cases h7 : p=7
    · subst p; obtain ⟨hl,hh⟩ := hr b; dsimp only [W] at hh; constructor <;> omega
    · by_cases hpi : p=parameterPair i
      · subst p; obtain ⟨hl,hh⟩ := hb b; dsimp only [W] at hh; constructor <;> omega
      · rw [(hf (p,b) h7 hpi).1]; dsimp only; constructor <;> omega
  have padAll (k : ℕ) (hk : k≤6) : ∃ T : ℕ, T≤k*(14*W+11) ∧
      run (padPhase 0) T = padPhase k ∧ ∀ t≤T, Safe (run (padPhase 0) t) := by
    induction k with
    | zero =>
      refine ⟨0,by omega,rfl,?_⟩
      intro t ht v'
      have : t=0 := by omega
      subst t
      simp [run,padPhase]
      omega
    | succ k ih =>
      obtain ⟨T,hT,he,hs⟩ := ih (by omega)
      obtain ⟨U,hU,ue,us⟩ := padStep ⟨k,by omega⟩
      refine ⟨U+T,by simp only [Nat.add_mul,Nat.one_mul]; omega,?_,join T U _ _ he hs us⟩
      simp only [run,Function.iterate_add_apply]
      change run (run _ T) U = _
      rw [he]
      exact ue
  obtain ⟨TD,hTD,hDE,hDS⟩ := padAll 6 (by omega)
  rw [padEntry] at hDE hDS
  have returnedEq : padPhase 6 = returned v := by
    have hw : q.length+1=W := rfl
    have hq : source v=q := rfl
    apply configExt
    · rfl
    · rfl
    · funext t z
      rcases t with ⟨p,b⟩
      change padded 6 (p,b) z = (returned v).cell (p,b) z
      simp only [returned,hq,hw]
      by_cases h7 : p=7
      · subst p; simp [padded]
      · by_cases h8 : p=8
        · subst p; simp [padded]
        · by_cases h0 : p=0
          · subst p; simp [padded]
          · have hb : p.val≤6 := by
              have := p.isLt
              simp only [Fin.ext_iff] at h7 h8 h0
              omega
            simp only [padded,dif_neg h7,dif_neg h8,dif_neg h0,if_pos hb]
  rw [returnedEq] at hDE
  let T := (((TD+(5*W+2))+TC)+TP)+10
  have runEnd : run (initial q) T = returned v := by
    change run (initial q) ((((TD+(5*W+2))+TC)+TP)+10) = _
    rw [appendRun,initRun,appendRun,hPE,appendRun,hCE,appendRun,hRE,hDE]
  have allSafe : ∀ t≤T, Safe (run (initial q) t) := by
    have s1 := join (5*W+2) TD _ _ hRE rewindSafe hDS
    have s2 := join TC (TD+(5*W+2)) _ _ hCE countSafe s1
    have s3 := join TP ((TD+(5*W+2))+TC) _ _ hPE hPS s2
    exact join 10 _ _ _ initRun initSafe s3
  have visitedContained (n : ℕ) (hn : n≤T) (t : Track) :
      visited q t n ⊆ (Finset.range (s+4)).image Int.ofNat := by
    induction n with
    | zero =>
      intro z hz
      simp only [visited,initialVisited] at hz
      split_ifs at hz with ht
      · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr (by
          have := Finset.mem_range.mp ha; dsimp [s]; omega),rfl⟩
      · have hz0 : z=0 := by simpa using hz
        subst z
        exact Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr (by omega),rfl⟩
    | succ n ih =>
      rw [visited,Finset.insert_subset_iff]
      refine ⟨?_,ih (by omega)⟩
      obtain ⟨hl,hh⟩ := allSafe (n+1) hn t
      refine Finset.mem_image.mpr ⟨(run (initial q) (n+1)).head t |>.toNat,
        Finset.mem_range.mpr (by omega),Int.toNat_of_nonneg hl⟩
  have headLength (n : ℕ) (hn : n≤T) (t : Track) :
      (headDescription (run (initial q) n |>.head t)).length ≤ s+5 := by
    obtain ⟨hl,hh⟩ := allSafe n hn t
    simp only [headDescription,List.length_append,List.length_cons,List.length_replicate,
      List.length_singleton,List.length_nil]
    have he := Int.natAbs_of_nonneg hl
    omega
  have resource (n : ℕ) (hn : n≤T) : charge q n ≤ (K+198)*(s+1) := by
    have cells (t : Track) : (visited q t n).card ≤ s+4 := by
      exact (Finset.card_le_card (visitedContained n hn t)).trans
        (Finset.card_image_le.trans (by simp))
    calc
      charge q n = K + ∑ t : Track,
          ((visited q t n).card + (headDescription (run (initial q) n |>.head t)).length) := by
        simp [charge,K,controlDescription]
      _ ≤ K + ∑ _t : Track, (2*s+9) :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun t _ => by
          have hc := cells t
          have hh := headLength n hn t
          omega)) K
      _ = K+18*(2*s+9) := by simp [Track,Fintype.card_prod]
      _ ≤ (K+198)*(s+1) := by simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega
  have timeBound : T ≤ 256*(s+1)^2 := by
    have hbnd : s.bits.length ≤ s := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    have hcoarse : T ≤ s*(8*s+20)+97*s+193 := by
      dsimp only [T,W]
      dsimp only [W] at hTD
      omega
    have hparse : s*(8*s+20) ≤ 28*(s+1)^2 := by
      have hh := Nat.mul_le_mul (show s≤s+1 by omega) (show 8*s+20≤28*(s+1) by omega)
      simpa [pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
    have hsq : s+1≤(s+1)^2 := by
      have hh := Nat.mul_le_mul_left (s+1) (show 1≤s+1 by omega)
      simpa [pow_two] using hh
    have hr : 97*s+193 ≤ 228*(s+1)^2 := by
      exact (show 97*s+193≤228*(s+1) by omega).trans (Nat.mul_le_mul_left 228 hsq)
    omega
  refine ⟨T,runEnd,timeBound,resource,allSafe,?_⟩
  intro i
  apply Nat.size_le.mp
  rw [← Nat.size_eq_bits_len]
  exact widthBound i

end D5.S0.Computability.Coding.PhysicalParserExecution
