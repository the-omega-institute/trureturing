/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BasePositionMemory
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BasePositionMemory
   mirror-E: none(waiver:exact-marker-selection-memory)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity.marked_prefix_rigidity_and_charge; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: Path length fixes parity and the state stores the last two signed digits. -/

/-
proof_shape: content (base_path_position_memory)
escape_witness: Arbitrary-length path induction reconstructs parity and both sliding digit windows.
admission_basis: escape-witness
Direct frozen dependencies: none; the base arithmetic modules share this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseLastSignMemory
import D5.S1.Words.Palindromes.PeriodDoubling.BaseQArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.BaseClassStreams
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open BaseCertificates

/-- Parity, endpoint bits and the last two emitted digits are exact path observations. -/
theorem base_path_position_memory (charge : Bool) {s t : Fin 1492}
    {xs : List (ℤ × ℤ × ℤ × ℤ)} (hs : s ∈ (baseAutomaton charge).start)
    (p : (baseAutomaton charge).Path s t xs) :
    (baseTable t.val).1[1]?.getD 0 = (((xs.length+1)%2 : ℕ) : ℤ) ∧
    (baseTable t.val).1[2]?.getD 0 = (baseTable s.val).1[2]?.getD 0 ∧
    (baseTable t.val).1[3]?.getD 0 = (baseTable s.val).1[3]?.getD 0 ∧
    ∀ output : Bool,
      let ds := pathOutputs (fun _ _ (q : Fin 1492) =>
        (baseTable q.val).1[if output then 12 else 10]?.getD 0) p
      (baseTable t.val).1[if output then 12 else 10]?.getD 0 = ds.reverse[0]?.getD 0 ∧
      (baseTable t.val).1[if output then 13 else 11]?.getD 0 = ds.reverse[1]?.getD 0 ∧
      (baseTable t.val).1[if output then 17 else 16]?.getD 0 =
        (ds.filter (fun z => z != 0)).getLast?.getD 0 := by
  have checked (i : ℕ) (hi : i<1492) :
      chargeRowCheck i=true ∧ memoryRowCheck i=true ∧ classRowCheck i=true := by
    have blocks : ∀ b : Fin 47,
        ((List.range (min 32 (1492-32*b.val))).all (fun k =>
          chargeRowCheck (32*b.val+k) && memoryRowCheck (32*b.val+k) && classRowCheck (32*b.val+k)))=true := by
      intro b; fin_cases b <;> decide
    have hb:=blocks ⟨i/32,by omega⟩
    have hk : i%32 ∈ List.range (min 32 (1492-32*(i/32))) := by
      simp only [List.mem_range];omega
    have hh:=List.all_eq_true.mp hb (i%32) hk
    simpa only [show 32*(i/32)+i%32=i by omega,Bool.and_eq_true,and_assoc] using hh
  have row (s q : Fin 1492) (a : ℤ × ℤ × ℤ × ℤ)
      (he : q ∈ (baseAutomaton charge).step s a) :
      (baseTable q.val).1[1]?.getD 0=1-(baseTable s.val).1[1]?.getD 0 ∧
      (baseTable q.val).1[2]?.getD 0=(baseTable s.val).1[2]?.getD 0 ∧
      (baseTable q.val).1[3]?.getD 0=(baseTable s.val).1[3]?.getD 0 ∧
      (baseTable q.val).1[11]?.getD 0=(baseTable s.val).1[10]?.getD 0 ∧
      (baseTable q.val).1[13]?.getD 0=(baseTable s.val).1[12]?.getD 0 := by
    obtain ⟨hc,hm,hl⟩:=checked s.val s.isLt
    have hc:=of_decide_eq_true (List.all_eq_true.mp hc (q.val,a) he)
    have hm:=of_decide_eq_true (List.all_eq_true.mp hm (q.val,a) he)
    have hl:=of_decide_eq_true (List.all_eq_true.mp hl (q.val,a) he)
    exact ⟨hc.1,hm.1,hm.2.1,hl.1,hl.2.1⟩
  have go {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton charge).Path s t xs) (k : ℕ)
      (hp : (baseTable s.val).1[1]?.getD 0=(((k+1)%2 : ℕ) : ℤ)) :
      (baseTable t.val).1[1]?.getD 0=(((k+xs.length+1)%2 : ℕ) : ℤ) ∧
      (baseTable t.val).1[2]?.getD 0=(baseTable s.val).1[2]?.getD 0 ∧
      (baseTable t.val).1[3]?.getD 0=(baseTable s.val).1[3]?.getD 0 ∧
      ∀ (output : Bool) (past : List ℤ),
        (baseTable s.val).1[if output then 12 else 10]?.getD 0=past.reverse[0]?.getD 0 →
        (baseTable s.val).1[if output then 13 else 11]?.getD 0=past.reverse[1]?.getD 0 →
        let ds := pathOutputs (fun _ _ (q : Fin 1492) =>
          (baseTable q.val).1[if output then 12 else 10]?.getD 0) p
        (baseTable t.val).1[if output then 12 else 10]?.getD 0=(past++ds).reverse[0]?.getD 0 ∧
        (baseTable t.val).1[if output then 13 else 11]?.getD 0=(past++ds).reverse[1]?.getD 0 := by
    induction p generalizing k with
    | nil s =>
      refine ⟨by simpa using hp,rfl,rfl,?_⟩
      intro output past h0 h1
      simpa only [pathOutputs,List.append_nil] using And.intro h0 h1
    | cons q s t a xs he p ih =>
      obtain ⟨hpar,h2,h3,h11,h13⟩:=row s q a he
      have hnext : (baseTable q.val).1[1]?.getD 0=((((k+1)+1)%2 : ℕ) : ℤ) := by
        rw [hpar,hp];omega
      obtain ⟨htpar,ht2,ht3,htmem⟩:=ih (k+1) hnext
      refine ⟨by simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using htpar,ht2.trans h2,ht3.trans h3,?_⟩
      intro output past h0 h1
      let d := (baseTable q.val).1[if output then 12 else 10]?.getD 0
      have hh0 : (baseTable q.val).1[if output then 12 else 10]?.getD 0=
          (past++[d]).reverse[0]?.getD 0 := by
        simp only [List.reverse_append,List.reverse_singleton,List.singleton_append,
          List.getElem?_cons_zero,Option.getD_some,d]
      have hh1 : (baseTable q.val).1[if output then 13 else 11]?.getD 0=
          (past++[d]).reverse[1]?.getD 0 := by
        simp only [List.reverse_append,List.reverse_singleton,List.singleton_append,
          List.getElem?_cons_succ]
        cases output
        · exact h11.trans h0
        · exact h13.trans h0
      have hh:=htmem output (past++[d]) hh0 hh1
      simpa only [pathOutputs,List.append_assoc,List.singleton_append] using hh
  have hi : s.val<7 := by
    change ([0,1,2,3,4,5,6] : List ℕ).contains s.val=true at hs
    simp only [List.contains_eq_mem,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hs
    omega
  have src : (baseTable s.val).1[1]?.getD 0=1 ∧
      (∀ output : Bool, (baseTable s.val).1[if output then 12 else 10]?.getD 0=0 ∧
        (baseTable s.val).1[if output then 13 else 11]?.getD 0=0) := by
    have h : ∀ i : Fin 7, (baseTable i.val).1[1]?.getD 0=1 ∧
        (∀ output : Bool, (baseTable i.val).1[if output then 12 else 10]?.getD 0=0 ∧
          (baseTable i.val).1[if output then 13 else 11]?.getD 0=0) := by
      intro i; fin_cases i <;> refine ⟨by decide,?_⟩ <;> intro output <;> cases output <;> decide
    exact h ⟨s.val,hi⟩
  obtain ⟨h1,h2,h3,hmem⟩:=go p 0 (by simpa using src.1)
  refine ⟨by simpa using h1,h2,h3,?_⟩
  intro output
  obtain ⟨h0,h1⟩:=hmem output [] (by simpa using (src.2 output).1) (by simpa using (src.2 output).2)
  exact ⟨h0,h1,base_path_last_sign charge output hs p⟩
end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_position_memory
