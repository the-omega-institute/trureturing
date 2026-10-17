/- GID: D5/S0/Computability/WindowRegisterComposition
   generality: I
   mirror-B: D5/B/S0/Computability/WindowRegisterComposition
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Four canonical registers share one finite visited interval. -/

import D5.S0.Computability.WindowRegisterTrim

namespace PhysicalWindowContinuation.RegisterHandoff

def register (bs : List Bits) (j : Lane) : ℤ → Symbol :=
  tape ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])

def memory (m : Track → ℤ → Symbol) (bs : List Bits) : ℕ → Track → ℤ → Symbol
  | 0 => m
  | k+1 => if hk : k<4 then
      Function.update (memory m bs k) (target ⟨k,hk⟩) (register bs ⟨k,hk⟩)
    else memory m bs k

def startAt (m : Track → ℤ → Symbol) (h : Track → ℤ) (bs : List Bits) (k : ℕ) : PortConfig where
  control := if hk : k<4 then .home ⟨k,hk⟩ else .done
  head := h
  cell := memory m bs k

def Heads (W : ℕ) (c : PortConfig) : Prop := ∀ t, 0≤c.head t ∧ c.head t≤W

theorem frame_heads (m h j bs L W c) (hf : Frame m h j bs L c)
    (hW : L+2 ≤ W) (hh : ∀ t, 0≤h t ∧ h t≤W) : Heads W c := by
  intro t
  obtain ⟨_,ho,hw0,hw1,hj0,hj1⟩ := hf
  by_cases hw : t=workTrack
  · subst t; exact ⟨hw0,by omega⟩
  by_cases hj : t=target j
  · subst t; exact ⟨hj0,by omega⟩
  rw [(ho t hw hj).2]
  exact hh t

theorem heads_join (W a b x y) (he : run x a=y)
    (hx : ∀ n≤a, Heads W (run x n)) (hy : ∀ n≤b, Heads W (run y n)) :
    ∀ n≤b+a, Heads W (run x n) := by
  intro n hn
  by_cases hna : n≤a
  · exact hx n hna
  · rw [show n=(n-a)+a by omega,run,Function.iterate_add_apply]
    change Heads W (run (run x a) (n-a))
    rw [he]
    exact hy _ (by omega)

theorem target_injective : Function.Injective target := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  simp only [target] at this
  omega

theorem memory_work (m bs k) : memory m bs k workTrack=m workTrack := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold memory
    split
    · rw [Function.update_of_ne (target_ne_work _).symm,ih]
    · exact ih

theorem memory_fresh (m bs k) (j : Lane) (hk : k≤j.val) :
    memory m bs k (target j)=m (target j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk4 : k<4 := by have := j.isLt; omega
    have hne : target j ≠ target ⟨k,hk4⟩ := by
      intro he
      have hval : j.val=k := congrArg Fin.val (target_injective he)
      omega
    rw [memory,dif_pos hk4,Function.update_of_ne hne]
    exact ih (by omega)

theorem memory_written (m bs k) (hk : k≤4) (j : Lane) (hj : j.val<k) :
    memory m bs k (target j)=register bs j := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hk4 : k<4 := by omega
    rw [memory,dif_pos hk4]
    by_cases he : j.val=k
    · have hje : j=⟨k,hk4⟩ := Fin.ext he
      subst j
      simp
    · have hne : target j ≠ target ⟨k,hk4⟩ := by
        intro hh
        exact he (congrArg Fin.val (target_injective hh))
      rw [Function.update_of_ne hne]
      exact ih (by omega) (by omega)

theorem configuration_settled (m : Track → ℤ → Symbol) (h : Track → ℤ)
    (j : Lane) (bs : List Bits) (hw : h workTrack=0) (hj : h (target j)=0)
    (mw : m workTrack=word bs) :
    config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero])
      0 0 (.laneDone j) =
      (⟨.laneDone j,h,Function.update m (target j) (register bs j)⟩ : PortConfig) := by
  apply config_ext
  · rfl
  · funext t
    by_cases ht : t=target j
    · subst t; simp [config,hj]
    · by_cases htw : t=workTrack
      · subst t; simp [config,ht,hw]
      · simp [config,Function.update_apply,ht,htw]
  · funext t z
    by_cases ht : t=target j
    · subst t; rfl
    · by_cases htw : t=workTrack
      · subst t; simp [config,register,ht,mw]
      · simp [config,register,Function.update_apply,ht,htw]

theorem lane_transition (m : Track → ℤ → Symbol) (h : Track → ℤ)
    (bs : List Bits) (k : ℕ) (hk : k<4) :
    run (⟨.laneDone ⟨k,hk⟩,h,memory m bs (k+1)⟩ : PortConfig) 1 =
      startAt m h bs (k+1) := by
  by_cases hn : k+1<4 <;> simp [run,step,program,startAt,hn]

theorem all_registers (m : Track → ℤ → Symbol) (h : Track → ℤ)
    (bs : List Bits) (W : ℕ) (hW : bs.length+2 ≤ W)
    (hh : ∀ t,0≤h t ∧ h t≤W) (hw : h workTrack=0)
    (hj : ∀ j : Lane,h (target j)=0)
    (mw : m workTrack=word bs) (mj : ∀ j : Lane,m (target j)=fun _=>.blank) :
    ∃ T : ℕ, T≤128*(bs.length+1)+4 ∧
      run (entry m h 0) T=startAt m h bs 4 ∧
      program (startAt m h bs 4).control=.halt ∧
      (∀ n≤T,Heads W (run (entry m h 0) n)) ∧
      ∀ j : Lane,(startAt m h bs 4).cell (target j)=register bs j := by
  have hprefix : ∀ k≤4, ∃ T : ℕ,T≤k*(32*(bs.length+1)+1) ∧
      run (entry m h 0) T=startAt m h bs k ∧
      ∀ n≤T,Heads W (run (entry m h 0) n) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨0,by omega,by simp [run,entry,startAt,memory],?_⟩
      intro n hn
      have he : n=0 := by omega
      subst n
      exact hh
    | succ k ih =>
      have hk4 : k<4 := by omega
      obtain ⟨t,ht,he,hf⟩ := ih (by omega)
      obtain ⟨u,hu,hr,hfr,_,_⟩ := one_register (memory m bs k) h ⟨k,hk4⟩ bs hw
        (hj _) (by rw [memory_work,mw]) (by rw [memory_fresh _ _ _ _ (Nat.le_refl k),mj])
      have hsettle := configuration_settled (memory m bs k) h ⟨k,hk4⟩ bs hw
        (hj _) (by rw [memory_work,mw])
      rw [hsettle] at hr
      have hr' : run (entry (memory m bs k) h ⟨k,hk4⟩) u =
          (⟨.laneDone ⟨k,hk4⟩,h,memory m bs (k+1)⟩ : PortConfig) := by
        simpa [memory,hk4] using hr
      have hstart : startAt m h bs k=entry (memory m bs k) h ⟨k,hk4⟩ := by
        simp [startAt,entry,hk4]
      have hsecond : run (startAt m h bs k) (1+u)=startAt m h bs (k+1) := by
        rw [hstart,run,Function.iterate_add_apply]
        change run (run _ u) 1=_
        rw [hr']
        exact lane_transition m h bs k hk4
      have fsecond : ∀ n≤1+u,Heads W (run (startAt m h bs k) n) := by
        rw [hstart]
        apply heads_join W u 1 _ _ hr'
        · intro n hn
          exact frame_heads _ _ _ _ _ _ _ (hfr n hn) hW hh
        · intro n hn
          interval_cases n
          · exact hh
          · rw [lane_transition]
            exact hh
      refine ⟨(1+u)+t,?_,?_,heads_join W t (1+u) _ _ he hf fsecond⟩
      · have hmul : (k+1)*(32*(bs.length+1)+1)=
            k*(32*(bs.length+1)+1)+(32*(bs.length+1)+1) := by ring
        omega
      · rw [run,Function.iterate_add_apply]
        change run (run _ t) (1+u)=_
        rw [he]
        exact hsecond
  obtain ⟨T,hT,hr,hf⟩ := hprefix 4 (by omega)
  refine ⟨T,by omega,hr,by simp [startAt,program],hf,?_⟩
  intro j
  exact memory_written m bs 4 (by omega) j j.isLt

end PhysicalWindowContinuation.RegisterHandoff
