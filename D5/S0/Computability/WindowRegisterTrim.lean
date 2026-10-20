/- GID: D5/S0/Computability/WindowRegisterTrim
   generality: I
   mirror-B: D5/B/S0/Computability/WindowRegisterTrim
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Arbitrary-length high-zero trimming and paid rewinds normalize binary tapes. -/

import D5.S0.Computability.WindowRegisterCore

namespace PhysicalWindowContinuation.RegisterHandoff

/-- Rewind a target register, preserving its delimiter and every other tape. -/
theorem target_rewind (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) (xs : List Bool) (p : ℤ) (k L : ℕ)
    (hk : k ≤ xs.length) (hp : 0 ≤ p) (hpL : p ≤ L+1) (hL : xs.length ≤ L+1) :
    run (config m h j bs (xs.map Symbol.unit ++ [.window .zero]) p k (.rewind j))
      (2*k+1) =
      config m h j bs (xs.map Symbol.unit ++ [.window .zero]) p 0 (.packedRewindMove j) ∧
    ∀ n ≤ 2*k+1, Frame m h j bs L
      (run (config m h j bs (xs.map Symbol.unit ++ [.window .zero]) p k (.rewind j)) n) := by
  have ht := target_ne_work j
  induction k with
  | zero =>
    refine ⟨by simp [run,step,program,config,tape,ht.symm],?_⟩
    intro n hn
    interval_cases n
    all_goals
      simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
      simp [step,program,config,tape,ht.symm]
      exact config_frame _ _ _ _ _ _ _ _ _ hp hpL (by omega) (by omega)
  | succ k ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    have hr : tape (xs.map Symbol.unit ++ [.window .zero]) (k+1) = .unit xs[k] := by
      have hh : k<xs.length := by omega
      have hpz : 0<(k:ℤ)+1 := by omega
      simp [tape,ne_of_gt hpz,hpz,List.getElem?_append,hh]
    have htwo : run (config m h j bs (xs.map Symbol.unit ++ [.window .zero]) p (k+1)
        (.rewind j)) 2 =
        config m h j bs (xs.map Symbol.unit ++ [.window .zero]) p k (.rewind j) := by
      simp only [run,show 2=1+1 from rfl,Function.iterate_succ_apply,
        Function.iterate_zero_apply]
      apply config_ext
      · simp [step,program,config,hr]
      · simp [step,program,config,hr]
      · simp [step,program,config,hr]
    obtain ⟨he,hf⟩ := ih (by omega)
    refine ⟨?_,?_⟩
    · rw [show 2*(k+1)+1=(2*k+1)+2 by omega,run,Function.iterate_add_apply]
      change run (run _ 2) (2*k+1)=_
      rw [htwo]
      exact he
    · rw [show 2*(k+1)+1=(2*k+1)+2 by omega]
      apply frame_join m h j bs L 2 (2*k+1) _ _ htwo
      · intro n hn
        interval_cases n
        all_goals
          simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
          simp [Frame,step,program,config,ht,ht.symm,hr,Function.update_apply]
          refine ⟨?_,by omega⟩
          intro t hw hj
          simp [hw,hj]
      · exact hf

end PhysicalWindowContinuation.RegisterHandoff

namespace PhysicalWindowContinuation.RegisterHandoff

/-- Clearing high zero cells, emitting a delimiter, and rewinding are all paid. -/
theorem trim_run (m h j bs) (xs : List Bool) (p : ℤ) (L : ℕ)
    (hp : 0 ≤ p) (hpL : p ≤ L+1) (hL : xs.length ≤ L) :
    ∃ T : ℕ, T ≤ 5*xs.length+12 ∧
      run (config m h j bs (xs.map Symbol.unit) p xs.length (.trim j)) T =
        config m h j bs ((normalized xs).map Symbol.unit ++ [.window .zero])
          p 0 (.packedRewindMove j) ∧
      ∀ n ≤ T, Frame m h j bs L
        (run (config m h j bs (xs.map Symbol.unit) p xs.length (.trim j)) n) := by
  have ht := target_ne_work j
  induction xs using List.reverseRecOn with
  | nil =>
    have he : run (config m h j bs [] p 0 (.trim j)) 6 =
        config m h j bs ([false].map Symbol.unit ++ [.window .zero]) p 1 (.rewind j) := by
      simp only [run,show 6=1+1+1+1+1+1 from rfl,
        Function.iterate_succ_apply,Function.iterate_zero_apply]
      apply config_ext
      · simp [step,program,config,tape]
      · simp [step,program,config,tape,Function.update_apply]
      · simp [step,program,config,tape,Function.update_apply]
        funext t z
        by_cases hj : t=target j
        · subst t
          by_cases hz0 : z=0
          · subst z; simp [tape,Function.update_apply]
          by_cases hz1 : z=1
          · subst z; simp [tape,Function.update_apply]
          by_cases hz2 : z=2
          · subst z; simp [tape,Function.update_apply]
          by_cases hpz : 0<z
          · have hzlen : 2 ≤ z.toNat-1 := by omega
            have hn : ([Symbol.unit false,Symbol.window .zero][z.toNat-1]?)=none := by
              apply List.getElem?_eq_none
              simpa using hzlen
            simp [tape,Function.update_apply,hz0,hz1,hz2,hpz,hn]
          · simp [tape,Function.update_apply,hz0,hz1,hz2,hpz]
        · simp [hj,Function.update_apply]
    obtain ⟨hr,hf⟩ := target_rewind m h j bs [false] p 1 L (by simp) hp hpL (by simp)
    refine ⟨9,by simp,?_,?_⟩
    · change run (config m h j bs [] p 0 (.trim j)) (3+6)=_
      rw [run,Function.iterate_add_apply]
      change run (run _ 6) 3=_
      rw [he]
      simpa [normalized,stripped] using hr
    · change ∀ n≤3+6, _
      apply frame_join m h j bs L 6 3 _ _ he
      · intro n hn
        interval_cases n
        all_goals
          simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
          simp [Frame,step,program,config,tape,ht,ht.symm,Function.update_apply]
          refine ⟨?_,by omega⟩
          intro t hw hj
          simp [hw,hj]
      · exact hf
  | append_singleton xs b ih =>
    simp only [List.length_append,List.length_singleton] at hL
    cases b
    · have hthree : run (config m h j bs ((xs++[false]).map Symbol.unit)
          p (xs++[false]).length (.trim j)) 3 =
          config m h j bs (xs.map Symbol.unit) p xs.length (.trim j) := by
        have hr : tape (xs.map Symbol.unit ++ [.unit false]) (xs.length+1)=.unit false := by
          simpa [List.map_append] using tape_read (xs.map Symbol.unit) [] (.unit false)
        simp only [run,show 3=1+1+1 from rfl,Function.iterate_succ_apply,
          Function.iterate_zero_apply]
        apply config_ext
        · simp [step,program,config,hr]
        · simp [step,program,config,hr]
        · simp [step,program,config,hr]
          funext t z
          by_cases hj : t=target j
          · subst t
            simpa [List.map_append,Function.update_apply] using
              congrFun (tape_erase (xs.map Symbol.unit) (.unit false)) z
          · simp [hj,Function.update_apply]
      obtain ⟨T,hT,he,hf⟩ := ih (by simp at hL; omega)
      refine ⟨T+3,by simp at hL ⊢; omega,?_,?_⟩
      · rw [run,Function.iterate_add_apply]
        change run (run _ 3) T=_
        rw [hthree]
        simpa [normalized_false] using he
      · apply frame_join m h j bs L 3 T _ _ hthree
        · intro n hn
          have hr : tape (xs.map Symbol.unit ++ [.unit false]) (xs.length+1)=.unit false := by
            simpa [List.map_append] using tape_read (xs.map Symbol.unit) [] (.unit false)
          interval_cases n
          all_goals
            simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
            simp [Frame,step,program,config,ht,ht.symm,hr,List.length_append,
              Function.update_apply]
            refine ⟨?_,by omega⟩
            intro t hw hj
            simp [hw,hj]
        · exact hf
    · have hfour : run (config m h j bs ((xs++[true]).map Symbol.unit)
          p (xs++[true]).length (.trim j)) 4 =
          config m h j bs ((xs++[true]).map Symbol.unit ++ [.window .zero])
            p (xs++[true]).length (.rewind j) := by
        have hr : tape (xs.map Symbol.unit ++ [.unit true]) (xs.length+1)=.unit true := by
          simpa [List.map_append] using tape_read (xs.map Symbol.unit) [] (.unit true)
        simp only [run,show 4=1+1+1+1 from rfl,Function.iterate_succ_apply,
          Function.iterate_zero_apply]
        apply config_ext
        · simp [step,program,config,hr]
        · simp [step,program,config,hr]
        · simp [step,program,config,hr]
          funext t z
          by_cases hj : t=target j
          · subst t
            simpa [Function.update_apply] using
              congrFun (tape_append ((xs++[true]).map Symbol.unit) (.window .zero)) z
          · simp [hj,Function.update_apply]
      obtain ⟨hr,hf⟩ := target_rewind m h j bs (xs++[true]) p (xs++[true]).length L
        (by rfl) hp hpL (by simp; omega)
      refine ⟨(2*(xs++[true]).length+1)+4,by omega,?_,?_⟩
      · rw [run,Function.iterate_add_apply]
        change run (run _ 4) (2*(xs++[true]).length+1)=_
        rw [hfour]
        simpa [normalized_true] using hr
      · apply frame_join m h j bs L 4 (2*(xs++[true]).length+1) _ _ hfour
        · intro n hn
          have hr : tape (xs.map Symbol.unit ++ [.unit true]) (xs.length+1)=.unit true := by
            simpa [List.map_append] using tape_read (xs.map Symbol.unit) [] (.unit true)
          interval_cases n
          all_goals
            simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
            simp [Frame,step,program,config,ht,ht.symm,hr,List.length_append,
              Function.update_apply]
            refine ⟨?_,by omega⟩
            intro t hw hj
            simp [hw,hj]
        · exact hf

end PhysicalWindowContinuation.RegisterHandoff

namespace PhysicalWindowContinuation.RegisterHandoff

theorem packed_rewind (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) (xs : List Symbol) (k L : ℕ)
    (hk : k ≤ bs.length) (hL : bs.length ≤ L) :
    run (config m h j bs xs k 0 (.packedRewind j)) (2*k+1) =
      config m h j bs xs 0 0 (.laneDone j) ∧
    ∀ n ≤ 2*k+1, Frame m h j bs L
      (run (config m h j bs xs k 0 (.packedRewind j)) n) := by
  have ht := target_ne_work j
  induction k with
  | zero =>
    refine ⟨by simp [run,step,program,config,word,ht.symm],?_⟩
    intro n hn
    interval_cases n
    all_goals
      simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
      simp [step,program,config,word,ht.symm]
      exact config_frame _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  | succ k ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    have hr : word bs (k+1) = .column bs[k] := word_get bs k (by omega)
    have htwo : run (config m h j bs xs (k+1) 0 (.packedRewind j)) 2 =
        config m h j bs xs k 0 (.packedRewind j) := by
      simp only [run,show 2=1+1 from rfl,Function.iterate_succ_apply,
        Function.iterate_zero_apply]
      apply config_ext
      · simp [step,program,config,ht.symm,hr]
      · simp [step,program,config,ht.symm,hr]
        funext t
        by_cases hw : t=workTrack <;> by_cases hj : t=target j <;>
          simp_all [Function.update_apply]
        all_goals omega
      · simp [step,program,config,ht.symm,hr]
    obtain ⟨he,hf⟩ := ih (by omega)
    refine ⟨?_,?_⟩
    · rw [show 2*(k+1)+1=(2*k+1)+2 by omega,run,Function.iterate_add_apply]
      change run (run _ 2) (2*k+1)=_
      rw [htwo]
      exact he
    · rw [show 2*(k+1)+1=(2*k+1)+2 by omega]
      apply frame_join m h j bs L 2 (2*k+1) _ _ htwo
      · intro n hn
        interval_cases n
        all_goals
          simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
          simp [Frame,step,program,config,ht,ht.symm,hr,Function.update_apply]
          refine ⟨?_,by omega⟩
          intro t hw hj
          simp [hw,hj]
      · exact hf

end PhysicalWindowContinuation.RegisterHandoff

namespace PhysicalWindowContinuation.RegisterHandoff

theorem copy_to_trim (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) :
    run (config m h j bs [] 1 1 (.scan j)) (4*bs.length+2) =
      config m h j bs ((bs.map (select j)).map Symbol.unit)
        (bs.length+1) bs.length (.trim j) ∧
    ∀ n ≤ 4*bs.length+2, Frame m h j bs bs.length
      (run (config m h j bs [] 1 1 (.scan j)) n) := by
  have ht := target_ne_work j
  obtain ⟨hc,hf⟩ := copy_prefix m h j [] bs bs.length (by simp)
  simp only [List.nil_append,List.map_nil,List.length_nil,Int.natCast_zero,zero_add] at hc hf
  have he : run (config m h j bs ((bs.map (select j)).map Symbol.unit)
      (bs.length+1) (bs.length+1) (.scan j)) 2 =
      config m h j bs ((bs.map (select j)).map Symbol.unit)
        (bs.length+1) bs.length (.trim j) := by
    simp only [run,show 2=1+1 from rfl,Function.iterate_succ_apply,
      Function.iterate_zero_apply]
    apply config_ext
    · simp [step,program,config,ht.symm,word_blank]
    · simp [step,program,config,ht.symm,word_blank]
    · simp [step,program,config,ht.symm,word_blank]
  refine ⟨?_,?_⟩
  · rw [show 4*bs.length+2=2+4*bs.length by omega,run,Function.iterate_add_apply]
    change run (run _ (4*bs.length)) 2=_
    rw [hc]
    exact he
  · rw [show 4*bs.length+2=2+4*bs.length by omega]
    apply frame_join m h j bs bs.length (4*bs.length) 2 _ _ hc hf
    intro n hn
    interval_cases n
    all_goals
      simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
      simp [Frame,step,program,config,ht,ht.symm,word_blank,Function.update_apply]
      refine ⟨?_,by omega⟩
      intro t hw hj
      simp [hw,hj]

/-- A selected packed lane is physically copied, normalized, delimited and parked.
The packed source head is also returned to its home marker. -/
theorem canonical_lane_phase (m : Track → ℤ → Symbol) (h : Track → ℤ)
    (j : Lane) (bs : List Bits) :
    ∃ T : ℕ, T ≤ 11*bs.length+16 ∧
      run (config m h j bs [] 1 1 (.scan j)) T =
        config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
          0 0 (.laneDone j) ∧
      (∀ n ≤ T, Frame m h j bs bs.length
        (run (config m h j bs [] 1 1 (.scan j)) n)) ∧
      Nat.ofDigits 2 ((normalized (bs.map (select j))).map Bool.toNat)=bitValue (select j) bs ∧
      (normalized (bs.map (select j))=[false] ∨
        ∃ pre, normalized (bs.map (select j))=pre++[true]) := by
  have hnonneg : (0 : ℤ) ≤ bs.length := Int.natCast_nonneg _
  have hnext : (0 : ℤ) ≤ bs.length + 1 := by omega
  have hbound : (bs.length : ℤ) ≤ bs.length + 1 := by omega
  have htarget : (0 : ℤ) ≤ bs.length + 2 := by omega
  have ht := target_ne_work j
  obtain ⟨hcopy,fcopy⟩ := copy_to_trim m h j bs
  obtain ⟨u,hu,htrim,ftrim⟩ := trim_run m h j bs (bs.map (select j))
    (bs.length+1) bs.length (by omega) (by omega) (by simp)
  simp only [List.length_map] at hu htrim ftrim
  have hrewindMove : run (config m h j bs
      ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
      (bs.length+1) 0 (.packedRewindMove j)) 1 =
      config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
        bs.length 0 (.packedRewind j) := by
    apply config_ext
    · simp [run,step,program,config]
    · simp [run,step,program,config,ht.symm]
      funext t
      by_cases hw : t=workTrack <;> by_cases hj : t=target j <;>
        simp [Function.update_apply, hw, hj, ht, ht.symm]
      all_goals omega
    · simp [run,step,program,config]
  obtain ⟨hrewind,frewind⟩ := packed_rewind m h j bs
    ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
    bs.length bs.length (by rfl) (by rfl)
  have fmove : ∀ n≤1, Frame m h j bs bs.length
      (run (config m h j bs
        ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
        (bs.length+1) 0 (.packedRewindMove j)) n) := by
    intro n hn
    interval_cases n
    · simpa only [run,Function.iterate_zero_apply] using
        config_frame m h j bs
          ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
          (bs.length+1) 0 (.packedRewindMove j) bs.length
          hnext le_rfl le_rfl htarget
    · rw [hrewindMove]
      have hframe := config_frame m h j bs
        ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
        bs.length 0 (.packedRewind j) bs.length
        hnonneg hbound le_rfl htarget
      exact hframe
  have hend : run (config m h j bs
      ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
      (bs.length+1) 0 (.packedRewindMove j)) (2*bs.length+2) =
      config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
        0 0 (.laneDone j) := by
    rw [show 2*bs.length+2=(2*bs.length+1)+1 by omega,run,Function.iterate_add_apply]
    change run (run _ 1) (2*bs.length+1)=_
    rw [hrewindMove]
    exact hrewind
  have fend : ∀ n≤2*bs.length+2, Frame m h j bs bs.length
      (run (config m h j bs
        ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
        (bs.length+1) 0 (.packedRewindMove j)) n) := by
    rw [show 2*bs.length+2=(2*bs.length+1)+1 by omega]
    exact frame_join m h j bs bs.length 1 (2*bs.length+1) _ _ hrewindMove fmove frewind
  have hfirst : run (config m h j bs [] 1 1 (.scan j)) (u+(4*bs.length+2)) =
      config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
        (bs.length+1) 0 (.packedRewindMove j) := by
    rw [run,Function.iterate_add_apply]
    change run (run _ (4*bs.length+2)) u=_
    rw [hcopy]
    exact htrim
  have ffirst := frame_join m h j bs bs.length (4*bs.length+2) u _ _ hcopy fcopy ftrim
  refine ⟨(2*bs.length+2)+(u+(4*bs.length+2)),by omega,?_,?_,?_,normalized_shape _⟩
  · rw [run,Function.iterate_add_apply]
    change run (run _ (u+(4*bs.length+2))) (2*bs.length+2)=_
    rw [hfirst]
    exact hend
  · exact frame_join m h j bs bs.length (u+(4*bs.length+2)) (2*bs.length+2)
      _ _ hfirst ffirst fend
  · simpa [bitValue,List.map_map,Function.comp_def] using normalized_value (bs.map (select j))

end PhysicalWindowContinuation.RegisterHandoff

namespace PhysicalWindowContinuation.RegisterHandoff

def entry (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane) : PortConfig :=
  ⟨.home j,h,m⟩

/-- The target marker and both head advances are made by three local actions. -/
theorem initialize_register (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) (hw : h workTrack=0) (hj : h (target j)=0)
    (mw : m workTrack=word bs) (mj : m (target j)=fun _=>.blank) :
    run (entry m h j) 3 = config m h j bs [] 1 1 (.scan j) ∧
    ∀ n≤3, Frame m h j bs bs.length (run (entry m h j) n) := by
  have ht := target_ne_work j
  refine ⟨?_,?_⟩
  · simp only [run,show 3=1+1+1 from rfl,Function.iterate_succ_apply,
      Function.iterate_zero_apply]
    apply config_ext
    · simp [step,program,entry,config]
    · simp [step,program,entry,config,hw,hj,ht.symm]
      funext t
      by_cases hew : t=workTrack <;> by_cases hej : t=target j <;>
        simp_all [Function.update_apply]
    · simp [step,program,entry,config,hw,hj,ht.symm]
      funext t z
      by_cases he : t=target j
      · subst t
        simp [Function.update_apply,mj,tape]
      · by_cases hew : t=workTrack
        · subst t
          simp [Function.update_apply,he,mw]
        · simp [Function.update_apply,he,hew]
  · intro n hn
    interval_cases n
    all_goals
      simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
      simp [Frame,step,program,entry,hw,hj,mw,ht,ht.symm,Function.update_apply]
      try omega
      all_goals
        refine ⟨?_,by omega⟩
        intro t htw htj
        simp [htw,htj]

/-- One fresh canonical register is acquired from a selected actual packed lane. -/
theorem one_register (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) (hw : h workTrack=0) (hj : h (target j)=0)
    (mw : m workTrack=word bs) (mj : m (target j)=fun _=>.blank) :
    ∃ T : ℕ, T ≤ 32*(bs.length+1) ∧
      run (entry m h j) T =
        config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
          0 0 (.laneDone j) ∧
      (∀ n≤T, Frame m h j bs bs.length (run (entry m h j) n)) ∧
      Nat.ofDigits 2 ((normalized (bs.map (select j))).map Bool.toNat)=bitValue (select j) bs ∧
      (normalized (bs.map (select j))=[false] ∨
        ∃ pre, normalized (bs.map (select j))=pre++[true]) := by
  obtain ⟨he,hf⟩  := initialize_register m h j bs hw hj mw mj
  obtain ⟨T,hT,hr,hfr,hv,hs⟩ := canonical_lane_phase m h j bs
  refine ⟨T+3,by omega,?_,frame_join m h j bs bs.length 3 T _ _ he hf hfr,hv,hs⟩
  rw [run,Function.iterate_add_apply]
  change run (run _ 3) T=_
  rw [he]
  exact hr

end PhysicalWindowContinuation.RegisterHandoff
