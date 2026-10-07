/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseLastSignMemory
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseLastSignMemory
   mirror-E: none(waiver:literal-base-last-sign-memory)
   anchors: []
   utility: none
   digest: Each base-path last-sign memory is its stream's most recent nonzero coefficient. -/

/-
proof_shape: content (base_path_last_sign)
escape_witness: Complete edge checks and path induction reconstruct the last nonzero emitted sign.
admission_basis: escape-witness
Direct frozen dependencies: none; BaseChargeArithmetic is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseChargeArithmetic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open BaseCertificates

theorem base_path_last_sign (charge output : Bool) {s t : Fin 1492}
    {xs : List (ℤ × ℤ × ℤ × ℤ)} (hs : s ∈ (baseAutomaton charge).start)
    (p : (baseAutomaton charge).Path s t xs) :
    (baseTable t.val).1[if output then 17 else 16]?.getD 0 =
      (List.filter (fun z : ℤ => z != 0)
        (pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[if output then 12 else 10]?.getD 0) p)).getLast?.getD 0 := by
  have checked (i : ℕ) (hi : i < 1492) : chargeRowCheck i=true := by
    have blocks : ∀ b : Fin 24,
      ((List.range (min 64 (1492-64*b.val))).all (fun k => chargeRowCheck (64*b.val+k)))=true := by
      intro b
      fin_cases b <;> decide
    have hb:=blocks ⟨i/64,by omega⟩
    have hk : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range];omega
    simpa only [show 64*(i/64)+i%64=i by omega] using List.all_eq_true.mp hb (i%64) hk
  have go {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton charge).Path s t xs) :
      (baseTable t.val).1[if output then 17 else 16]?.getD 0 =
        (List.filter (fun z : ℤ => z != 0)
          (pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[if output then 12 else 10]?.getD 0) p)).getLast?.getD
            ((baseTable s.val).1[if output then 17 else 16]?.getD 0) := by
    induction p with
    | nil s => rfl
    | cons q s t a xs he p ih =>
      have hr:=checked s.val s.isLt
      dsimp [chargeRowCheck] at hr
      have hrow:=of_decide_eq_true (List.all_eq_true.mp hr (q.val,a) he)
      have hm : (baseTable q.val).1[if output then 17 else 16]?.getD 0 =
          if (baseTable q.val).1[if output then 12 else 10]?.getD 0=0 then
            (baseTable s.val).1[if output then 17 else 16]?.getD 0 else
            (baseTable q.val).1[if output then 12 else 10]?.getD 0 := by
        cases output
        · exact hrow.2.1
        · exact hrow.2.2.1
      rw [ih,hm]
      simp only [pathOutputs,List.filter_cons,bne_iff_ne]
      by_cases hd : (baseTable q.val).1[if output then 12 else 10]?.getD 0=0
      · simp [hd]
      · simp only [if_neg hd]
        rw [if_pos hd,List.getLast?_cons]
        rfl
  have hsrc : (baseTable s.val).1[if output then 17 else 16]?.getD 0=0 := by
    have hslt : s.val < 7 := by
      change ([0,1,2,3,4,5,6] : List ℕ).contains s.val=true at hs
      simp only [List.contains_eq_mem,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hs
      omega
    have hh : ∀ i : Fin 7, (baseTable i.val).1[if output then 17 else 16]?.getD 0=0 := by
      intro i
      fin_cases i <;> cases output <;> decide
    exact hh ⟨s.val,hslt⟩
  simpa only [hsrc] using go p

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_last_sign
