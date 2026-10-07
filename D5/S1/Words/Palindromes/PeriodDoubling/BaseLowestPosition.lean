/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseLowestPosition
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseLowestPosition
   mirror-E: none(waiver:literal-base-digit-order)
   anchors: []
   utility: none
   digest: Tight accepted base paths emit no output digit before their first input digit. -/

/-
proof_shape: content (base_path_lowest_order)
escape_witness: Product-path reconstruction and first-sign memory induction exclude earlier output coefficients.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.MinimumPathRealization
import D5.S1.Words.Palindromes.PeriodDoubling.BaseQArithmetic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open BaseCertificates MinimumPositionCertificate

theorem base_path_lowest_order {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ (baseAutomaton true).start) (ht : t ∈ (baseAutomaton true).accept)
    (p : (baseAutomaton true).Path s t xs) (hf : pathCharge (fun _ a _ => a.1) p=1) :
    ∀ i : ℕ, (pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p)[i]?.getD 0 ≠ 0 →
      ∃ k : ℕ, k ≤ i ∧ (pathOutputs (fun _ _ q => (baseTable q.val).1[10]?.getD 0) p)[k]?.getD 0 ≠ 0 := by
  have checked (i : ℕ) (hi : i < 1492) : memoryRowCheck i=true := by
    have blocks : ∀ b : Fin 24,
      ((List.range (min 64 (1492-64*b.val))).all (fun k => memoryRowCheck (64*b.val+k)))=true := by
      intro b
      fin_cases b <;> decide
    have hb:=blocks ⟨i/64,by omega⟩
    have hk : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range];omega
    simpa only [show 64*(i/64)+i%64=i by omega] using List.all_eq_true.mp hb (i%64) hk
  let event : Fin 1492 → Fin 1492 → Bool := fun s q =>
    (baseTable s.val).1[14]?.getD 0 == 0 && (baseTable q.val).1[10]?.getD 0 == 0 &&
    (baseTable q.val).1[12]?.getD 0 != 0
  have noevents : (pathOutputs (fun s _ q => event s q) p).any id=false := by
    obtain ⟨u,v,hu,hus,hvt,⟨pm⟩,hflag⟩:=minimum_path_realization hs p
    by_contra hh
    have htflag : (minimumTable v.val).2.1=true := by
      rw [hflag]
      exact Bool.eq_true_of_not_eq_false hh
    have hacc : v ∈ minimumAutomaton.accept := by
      change ((minimumTable v.val).2.1 && baseTerminal (baseTable (minimumTable v.val).1).1 &&
        ((baseTable (minimumTable v.val).1).1[18]?.getD 0 == 0))=true
      rw [hvt,htflag]
      exact ht
    have hb:=minimum_accepted_bound hu hacc pm
    have label_sum {M : NFA (ℤ × ℤ × ℤ × ℤ) (Fin 1492)} {s t : Fin 1492}
        {xs : List (ℤ × ℤ × ℤ × ℤ)} (p : M.Path s t xs) :
        pathCharge (fun _ a _ => a.1) p=(xs.map Prod.fst).sum := by
      induction p with
      | nil => rfl
      | cons q s t a xs he p ih => simpa only [pathCharge,List.map_cons,List.sum_cons,ih]
    have label_sum_min {s t : Fin 1710} {xs : List (ℤ × ℤ × ℤ × ℤ)}
        (p : minimumAutomaton.Path s t xs) :
        pathCharge (fun _ a _ => a.1) p=(xs.map Prod.fst).sum := by
      induction p with
      | nil => rfl
      | cons q s t a xs he p ih => simpa only [pathCharge,List.map_cons,List.sum_cons,ih]
    rw [label_sum_min pm,← label_sum p,hf] at hb
    omega
  have order {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton true).Path s t xs)
      (hm : (baseTable s.val).1[14]?.getD 0=0)
      (hno : (pathOutputs (fun s _ q => event s q) p).any id=false) :
      ∀ i : ℕ, (pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p)[i]?.getD 0 ≠ 0 →
        ∃ k : ℕ, k ≤ i ∧ (pathOutputs (fun _ _ q => (baseTable q.val).1[10]?.getD 0) p)[k]?.getD 0 ≠ 0 := by
    induction p with
    | nil s => intro i hi;simpa [pathOutputs] using hi
    | cons q s t a xs he p ih =>
      have hspl : event s q=false ∧ (pathOutputs (fun s _ q => event s q) p).any id=false := by
        simpa only [pathOutputs,List.any_cons,id_eq,Bool.or_eq_false_iff] using hno
      intro i hi
      by_cases hdn : (baseTable q.val).1[10]?.getD 0=0
      · have hr:=checked s.val s.isLt
        dsimp [memoryRowCheck] at hr
        have hrow:=of_decide_eq_true (List.all_eq_true.mp hr (q.val,a) he)
        have hqm : (baseTable q.val).1[14]?.getD 0=0 := by
          simpa only [hm,if_true,hdn] using hrow.2.2.1
        have hdj : (baseTable q.val).1[12]?.getD 0=0 := by
          have hh:=hspl.1
          simp only [event,hm,hdn,beq_self_eq_true,Bool.true_and,bne_eq_false_iff_eq] at hh
          exact hh
        cases i with
        | zero => simpa [pathOutputs,hdj] using hi
        | succ i =>
          have hi' : (pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p)[i]?.getD 0 ≠ 0 := by
            simpa only [pathOutputs,List.getElem?_cons_succ] using hi
          obtain ⟨k,hk,hkn⟩:=ih hqm hspl.2 i hi'
          refine ⟨k+1,by omega,?_⟩
          simpa only [pathOutputs,List.getElem?_cons_succ] using hkn
      · exact ⟨0,Nat.zero_le _,by simpa only [pathOutputs,List.getElem?_cons_zero,Option.getD_some] using hdn⟩
  have hsource : (baseTable s.val).1[14]?.getD 0=0 := by
    have hslt : s.val < 7 := by
      change ([0,1,2,3,4,5,6] : List ℕ).contains s.val=true at hs
      simp only [List.contains_eq_mem,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hs
      omega
    have hsmall : ∀ k : Fin 7, (baseTable k.val).1[14]?.getD 0=0 := by
      intro k;fin_cases k <;> decide
    exact hsmall ⟨s.val,hslt⟩
  exact order p hsource noevents

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_lowest_order
