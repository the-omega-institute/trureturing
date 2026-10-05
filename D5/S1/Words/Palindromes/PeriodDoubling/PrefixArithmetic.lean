/- GID: D5/S1/Words/Palindromes/PeriodDoubling/PrefixArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/PrefixArithmetic
   mirror-E: none(waiver:marked-prefix-product-arithmetic-realization)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixTable
   digest: Marker-product paths preserve the exact signed-weight difference of encoded halves. -/

/-
proof_shape: content (prefix_path_signed_weight_difference)
escape_witness: The finite projection reconstructs base paths and preserves every arithmetic label.
admission_basis: escape-witness
Direct frozen dependencies: none; BaseArithmetic and MarkedPrefixCertificates share this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPrefixCertificates
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates MarkedPrefixCertificates

private def projectionRowCheck (charge : Bool) (i : ℕ) : Bool :=
  let s : Fin 4262 := ⟨i % 4262, Nat.mod_lt _ (by decide)⟩
  let b : Fin 1492 := ⟨((prefixTable s.val).1[0]?.getD 0).toNat % 1492, Nat.mod_lt _ (by decide)⟩
  letI : Decidable (s ∈ (prefixAutomaton charge).start) := by unfold prefixAutomaton; dsimp; infer_instance
  letI : Decidable (s ∈ (prefixAutomaton charge).accept) := by unfold prefixAutomaton; dsimp; infer_instance
  letI : Decidable (b ∈ (baseAutomaton true).start) := by unfold baseAutomaton; dsimp; infer_instance
  letI : Decidable (b ∈ (baseAutomaton true).accept) := by unfold baseAutomaton; dsimp; infer_instance
  decide (((prefixTable s.val).1[0]?.getD 0).toNat < 1492 ∧
    (s ∈ (prefixAutomaton charge).start → b ∈ (baseAutomaton true).start) ∧
    (s ∈ (prefixAutomaton charge).accept → b ∈ (baseAutomaton true).accept)) &&
    ((prefixTable s.val).2.1).all fun e =>
      (((prefixTable e.1).1[0]?.getD 0).toNat % 1492, e.2) ∈ (baseTable b.val).2.1

private def projectionBlockCheck (charge : Bool) (start count : ℕ) : Bool :=
  (List.range count).all fun k => projectionRowCheck charge (start+k)

/-- Every marker-product path retains the signed-weight meaning of its arithmetic labels. -/
theorem prefix_path_signed_weight_difference (charge : Bool) {s t : Fin 4262} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ (prefixAutomaton charge).start) (ht : t ∈ (prefixAutomaton charge).accept)
    (p : (prefixAutomaton charge).Path s t xs) :
    pathCharge (fun _ a _ => a.1) p =
      (signedWeight (xs.foldr (fun a x => a.2.2.1+2*x) 0 +
        ((baseTable ((prefixTable s.val).1[0]?.getD 0).toNat).1[2]?.getD 0)) : ℤ) -
      (signedWeight (xs.foldr (fun a x => a.2.2.2+2*x) 0 +
        ((baseTable ((prefixTable s.val).1[0]?.getD 0).toNat).1[3]?.getD 0)) : ℤ) := by
  classical
  have checked (i : ℕ) (hi : i<4262) : projectionRowCheck charge i = true := by
    have blocks : ∀ b : Fin 67,
      projectionBlockCheck charge (64*b.val) (min 64 (4262-64*b.val)) = true := by
      intro b
      fin_cases b <;> cases charge <;> decide
    have h := blocks ⟨i/64,by omega⟩
    dsimp [projectionBlockCheck] at h
    have hk : i%64 ∈ List.range (min 64 (4262-64*(i/64))) := by
      simp only [List.mem_range]; omega
    have hh := List.all_eq_true.mp h (i%64) hk
    simpa only [show 64*(i/64)+i%64=i by omega] using hh
  let B : Fin 4262 → Fin 1492 := fun i =>
    ⟨((prefixTable i.val).1[0]?.getD 0).toNat%1492, Nat.mod_lt _ (by decide)⟩
  have row (i : Fin 4262) : ((prefixTable i.val).1[0]?.getD 0).toNat < 1492 ∧
      (i ∈ (prefixAutomaton charge).start → B i ∈ (baseAutomaton true).start) ∧
      (i ∈ (prefixAutomaton charge).accept → B i ∈ (baseAutomaton true).accept) ∧
      ∀ e ∈ (prefixTable i.val).2.1,
        (((prefixTable e.1).1[0]?.getD 0).toNat%1492, e.2) ∈ (baseTable (B i).val).2.1 := by
    have h := checked i.val i.isLt
    simp only [projectionRowCheck, Nat.mod_eq_of_lt i.isLt, Bool.and_eq_true] at h
    have hprops := of_decide_eq_true h.1
    have hp : ((prefixTable i.val).1[0]?.getD 0).toNat < 1492 ∧
      (i ∈ (prefixAutomaton charge).start → B i ∈ (baseAutomaton true).start) ∧
      (i ∈ (prefixAutomaton charge).accept → B i ∈ (baseAutomaton true).accept) := by
      simpa only [Nat.mod_eq_of_lt i.isLt, B] using hprops
    refine ⟨hp.1,hp.2.1,hp.2.2,?_⟩
    intro e he
    have hall := List.all_eq_true.mp h.2
    have hh := of_decide_eq_true (hall e he)
    simpa only [Nat.mod_eq_of_lt i.isLt, B] using hh
  have lift {s t : Fin 4262} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (prefixAutomaton charge).Path s t xs) :
      ∃ q : (baseAutomaton true).Path (B s) (B t) xs,
        pathCharge (fun _ a _ => a.1) q = pathCharge (fun _ a _ => a.1) p := by
    induction p with
    | nil s => exact ⟨NFA.Path.nil (B s),rfl⟩
    | cons q s t a xs hstep p ih =>
      obtain ⟨p',hp'⟩ := ih
      have hm : (q.val,a) ∈ (prefixTable s.val).2.1 := hstep
      have hedge := (row s).2.2.2 (q.val,a) hm
      refine ⟨NFA.Path.cons (B q) (B s) (B t) a xs hedge p',?_⟩
      simpa only [pathCharge,hp']
  obtain ⟨q,hq⟩ := lift p
  have h := base_path_signed_weight_difference true ((row s).2.1 hs) ((row t).2.2.1 ht) q
  rw [hq] at h
  simpa only [B, Nat.mod_eq_of_lt (row s).1] using h

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.prefix_path_signed_weight_difference
