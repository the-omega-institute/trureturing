/- GID: D5/S0/Computability/WindowRegisterResources
   generality: I
   mirror-B: D5/B/S0/Computability/WindowRegisterResources
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Canonical binary endpoint and all-prefix persistent space accounting. -/

import D5.S0.Computability.WindowRegisterProgram

namespace PhysicalWindowContinuation.CanonicalAcquisition
open RegisterHandoff

/-- A literal canonical binary tape and its parked head. -/
def RegisterRep (c : Config) (j : Lane) (v : ℕ) : Prop :=
  c.head (target j) = 0 ∧ ∃ bs : List Bool,
    (bs = [false] ∨ ∃ pre, bs = pre ++ [true]) ∧
    Nat.ofDigits 2 (bs.map Bool.toNat) = v ∧
    c.cell (target j) = tape (bs.map Symbol.unit ++ [.window .zero])

def packedEnd (w : List Window) (e : Bool) : Configuration :=
  boundary (inputSource w e) w.length (Original.finalColumns w e) 0 .done

def registerEnd (w : List Window) (e : Bool) : Config :=
  port (startAt (packedEnd w e).cell (packedEnd w e).head (Original.finalColumns w e) 4)

theorem packed_heads (w : List Window) (e : Bool) :
    ∀ t, 0 ≤ (packedEnd w e).head t ∧ (packedEnd w e).head t ≤ 3*w.length+6 := by
  intro t
  simp only [packedEnd,boundary]
  split_ifs <;> omega

theorem packed_port (w : List Window) (e : Bool)
    (hlen : (Original.finalColumns w e).length ≤ 3*w.length+4) :
    ∃ u : ℕ, u ≤ 128*((Original.finalColumns w e).length+1)+4 ∧
      run (base (packedEnd w e)) (u+1) = registerEnd w e ∧
      program (registerEnd w e).control = .halt ∧
      (∀ n ≤ u+1, ∀ t, 0 ≤ (run (base (packedEnd w e)) n).head t ∧
        (run (base (packedEnd w e)) n).head t ≤ 3*w.length+6) ∧
      ∀ j : Lane, (registerEnd w e).cell (target j) = register (Original.finalColumns w e) j := by
  have hw : (packedEnd w e).head workTrack=0 := by simp [packedEnd,boundary]
  have hj : ∀ j : Lane, (packedEnd w e).head (target j)=0 := by
    intro j
    simp [packedEnd,boundary,target_ne_work,target_ne_source]
  have mw : (packedEnd w e).cell workTrack=word (Original.finalColumns w e) := by
    simp [packedEnd,boundary]
  have mj : ∀ j : Lane, (packedEnd w e).cell (target j)=fun _=>.blank := by
    intro j
    simp [packedEnd,boundary,target_ne_work,target_ne_source]
  obtain ⟨u,hu,he,hh,hf,hregs⟩ := all_registers
    (packedEnd w e).cell (packedEnd w e).head (Original.finalColumns w e) (3*w.length+6)
    (by omega) (packed_heads w e) hw hj mw mj
  have hstart : run (base (packedEnd w e)) 1 =
      port (entry (packedEnd w e).cell (packedEnd w e).head 0) := by
    rfl
  refine ⟨u,hu,?_,?_,?_,hregs⟩
  · rw [run,Function.iterate_add_apply]
    change run (run _ 1) u=_
    rw [hstart,run_port,he]
    rfl
  · rfl
  · intro n hn t
    by_cases hz : n=0
    · subst n; exact packed_heads w e t
    · rw [show n=(n-1)+1 by omega,run,Function.iterate_add_apply]
      change (0 ≤ (run (run (base (packedEnd w e)) 1) (n-1)).head t ∧
        (run (run (base (packedEnd w e)) 1) (n-1)).head t ≤ 3*w.length+6)
      rw [hstart,run_port]
      simpa [port] using hf (n-1) (by omega) t

theorem register_rep (w : List Window) (e : Bool) (j : Lane) :
    RegisterRep (registerEnd w e) j
      (bitValue (select j) (Original.finalColumns w e)) := by
  refine ⟨?_,normalized ((Original.finalColumns w e).map (select j)),normalized_shape _,?_,?_⟩
  · simp [registerEnd,port,startAt,packedEnd,boundary,target_ne_work,target_ne_source]
  · simpa only [bitValue,List.map_map,Function.comp_def] using normalized_value
      ((Original.finalColumns w e).map (select j))
  · exact memory_written _ _ 4 (by omega) j j.isLt

/-- Literal head bounds compose at the actual paid seam. -/
theorem heads_join (W a b : ℕ) (x y : Config) (he : run x a=y)
    (hx : ∀ n ≤ a, ∀ t, 0 ≤ (run x n).head t ∧ (run x n).head t ≤ W)
    (hy : ∀ n ≤ b, ∀ t, 0 ≤ (run y n).head t ∧ (run y n).head t ≤ W) :
    ∀ n ≤ b+a, ∀ t, 0 ≤ (run x n).head t ∧ (run x n).head t ≤ W := by
  intro n hn t
  by_cases hna : n ≤ a
  · exact hx n hna t
  · rw [show n=(n-a)+a by omega,run,Function.iterate_add_apply]
    change (0 ≤ (run (run x a) (n-a)).head t ∧
      (run (run x a) (n-a)).head t ≤ W)
    rw [he]
    exact hy _ (by omega) t

noncomputable def actionCode : Action → List Bool
  | .read t f => [false,false] ++ finiteCode t ++ finiteCode Symbol.blank ++
      (List.ofFn fun i : Fin (Fintype.card Symbol) =>
        finiteCode (f ((Fintype.equivFin Symbol).symm i))).flatten
  | .write t b k => [false,true] ++ finiteCode t ++ finiteCode b ++
      (List.replicate (Fintype.card Symbol) (finiteCode k)).flatten
  | .move t right k => [true,false] ++ finiteCode t ++ finiteCode (Symbol.unit right) ++
      (List.replicate (Fintype.card Symbol) (finiteCode k)).flatten
  | .halt => [true,true] ++ finiteCode sourceTrack ++ finiteCode Symbol.blank ++
      (List.replicate (Fintype.card Symbol) (finiteCode (α := State) (.inr .done))).flatten

noncomputable def code : List Bool :=
  (List.ofFn fun i : Fin (Fintype.card State) =>
    actionCode (program ((Fintype.equivFin State).symm i))).flatten

def visited (w : List Window) (e : Bool) (n : ℕ) (t : Track) : Finset ℤ :=
  suppliedPositions w t ∪
    (Finset.range (n+1)).image (fun k => (run (initial w e) k).head t)

noncomputable def charged (w : List Window) (e : Bool) (n : ℕ) : ℕ :=
  code.length + (finiteCode (run (initial w e) n).control).length +
    ∑ t : Track, ((visited w e n t).card * Fintype.card Symbol +
      (D5.S0.Computability.Coding.PhysicalSixParser.headDescription
        (run (initial w e) n |>.head t)).length)

theorem visited_bound (w : List Window) (e : Bool) (n W : ℕ)
    (hW : w.length ≤ W)
    (hh : ∀ k ≤ n, ∀ t, 0 ≤ (run (initial w e) k).head t ∧
      (run (initial w e) k).head t ≤ W) (t : Track) :
    (visited w e n t).card ≤ W+1 := by
  have hsub : visited w e n t ⊆ (Finset.range (W+1)).image Int.ofNat := by
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

theorem charged_bound (w : List Window) (e : Bool) (T : ℕ)
    (hf : ∀ n ≤ T, ∀ t, 0 ≤ (run (initial w e) n).head t ∧
      (run (initial w e) n).head t ≤ 3*w.length+6) :
    ∀ n ≤ T, charged w e n ≤
      (code.length + Fintype.card State + 80*(Fintype.card Symbol+1)) *
        (w.length+1) := by
  intro n hn
  have hheads : ∀ k ≤ n, ∀ t, 0 ≤ (run (initial w e) k).head t ∧
      (run (initial w e) k).head t ≤ 3*w.length+6 := by
    intro k hk t
    exact hf k (hk.trans hn) t
  have hterm : ∀ t : Track,
      (visited w e n t).card * Fintype.card Symbol +
        (D5.S0.Computability.Coding.PhysicalSixParser.headDescription
          (run (initial w e) n |>.head t)).length ≤
      (3*w.length+7)*Fintype.card Symbol + (3*w.length+8) := by
    intro t
    have hv := visited_bound w e n (3*w.length+6) (by omega) hheads t
    have hm := Nat.mul_le_mul_right (Fintype.card Symbol) hv
    rw [show 3*w.length+6+1 = 3*w.length+7 by omega] at hm
    obtain ⟨h0,h1⟩ := hheads n (by rfl) t
    simp only [D5.S0.Computability.Coding.PhysicalSixParser.headDescription,
      List.length_append,List.length_cons,List.length_replicate,List.length_nil]
    have habs : (run (initial w e) n |>.head t).natAbs ≤ 3*w.length+6 := by omega
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Track))
    (fun t _ => hterm t)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at hsum
  simp only [charged,finiteCode_length]
  nlinarith only [hsum, Nat.zero_le (code.length+Fintype.card State)]

end PhysicalWindowContinuation.CanonicalAcquisition
