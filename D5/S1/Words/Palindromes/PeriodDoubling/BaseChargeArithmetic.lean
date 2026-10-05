/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseChargeArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseChargeArithmetic
   mirror-E: none(waiver:unbounded-signed-charge-reconstruction)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: The q edge charges count alternating position weights and changes of nonzero signs. -/

/-
proof_shape: content (base_path_charge_reconstruction)
escape_witness: Complete charge-update checks and path induction reconstruct the signed-stream sum.
admission_basis: escape-witness
Direct frozen dependencies: none; BaseSignedStreams is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseSignedStreams

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

/-- Position weights and successive nonzero-sign changes, with an incoming sign. -/
def digitStreamCharge (par previous : ℤ) : List ℤ → ℤ
  | [] => 0
  | d::ds =>
    (if d = 0 then 0 else 1+2*par+
      (Bool.toNat (previous != 0 && previous != d) : ℤ)) +
    digitStreamCharge (1-par) (if d = 0 then previous else d) ds

private def chargeRowCheck (i : ℕ) : Bool :=
  let S := (baseTable i).1
  (baseTable i).2.1.all fun e =>
    let T := (baseTable e.1).1
    let dn := T[10]?.getD 0
    let dj := T[12]?.getD 0
    decide (T[1]?.getD 0 = 1-S[1]?.getD 0 ∧
      T[16]?.getD 0 = (if dn=0 then S[16]?.getD 0 else dn) ∧
      T[17]?.getD 0 = (if dj=0 then S[17]?.getD 0 else dj) ∧
      e.2.2.1 =
        (if dj=0 then 0 else 1+2*(S[1]?.getD 0)+
          (Bool.toNat (S[17]?.getD 0 != 0 && S[17]?.getD 0 != dj) : ℤ)) -
        (if dn=0 then 0 else 1+2*(S[1]?.getD 0)+
          (Bool.toNat (S[16]?.getD 0 != 0 && S[16]?.getD 0 != dn) : ℤ)))

private def chargeBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => chargeRowCheck (start+k)

/-- Every finite path's q charges are the exact difference of its two stream charges. -/
theorem base_path_charge_reconstruction (charge : Bool)
    {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (p : (baseAutomaton charge).Path s t xs) :
    pathCharge (fun _ a _ => a.2.1) p =
      digitStreamCharge ((baseTable s.val).1[1]?.getD 0)
        ((baseTable s.val).1[17]?.getD 0)
        (pathOutputs (fun _ _ q => (baseTable q.val).1[12]?.getD 0) p) -
      digitStreamCharge ((baseTable s.val).1[1]?.getD 0)
        ((baseTable s.val).1[16]?.getD 0)
        (pathOutputs (fun _ _ q => (baseTable q.val).1[10]?.getD 0) p) := by
  have checked (i : ℕ) (hi : i<1492) : chargeRowCheck i = true := by
    have blocks : ∀ b : Fin 24,
        chargeBlockCheck (64*b.val) (min 64 (1492-64*b.val)) = true := by
      intro b
      fin_cases b <;> decide
    have hb := blocks ⟨i/64,by omega⟩
    dsimp [chargeBlockCheck] at hb
    have hm : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range]
      omega
    have hh := List.all_eq_true.mp hb (i%64) hm
    simpa only [show 64*(i/64)+i%64=i by omega] using hh
  induction p with
  | nil s => simp [pathCharge,pathOutputs,digitStreamCharge]
  | cons q s t a xs hstep p ih =>
    have hm : (q.val,a) ∈ (baseTable s.val).2.1 := hstep
    have hh := List.all_eq_true.mp (checked s.val s.isLt) (q.val,a) hm
    dsimp only [chargeRowCheck] at hh
    obtain ⟨hpar,hn,hj,hq⟩ := of_decide_eq_true hh
    simp only [pathCharge,pathOutputs,digitStreamCharge]
    rw [ih,hpar,hn,hj,hq]
    ring

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_charge_reconstruction
