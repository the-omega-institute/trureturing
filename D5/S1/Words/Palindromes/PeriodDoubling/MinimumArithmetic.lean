/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MinimumArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MinimumArithmetic
   mirror-E: none(waiver:minimum-position-product-arithmetic-realization)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimumTable
   digest: Lowest-position product paths preserve the exact signed-weight difference. -/

/-
proof_shape: content (minimum_path_signed_weight_difference)
escape_witness: The checked finite projection lifts every product path with its arithmetic labels intact.
admission_basis: escape-witness
Direct frozen dependencies: none; BaseArithmetic and MinimumPositionCertificate share this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.MinimumPositionCertificate
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates MinimumPositionCertificate

private def projectionRowCheck (i : ℕ) : Bool :=
  let s : Fin 1710 := ⟨i % 1710, Nat.mod_lt _ (by decide)⟩
  let b : Fin 1492 := ⟨(minimumTable s.val).1 % 1492, Nat.mod_lt _ (by decide)⟩
  letI : Decidable (s ∈ minimumAutomaton.start) := by unfold minimumAutomaton; dsimp; infer_instance
  letI : Decidable (s ∈ minimumAutomaton.accept) := by unfold minimumAutomaton; dsimp; infer_instance
  letI : Decidable (b ∈ (baseAutomaton true).start) := by unfold baseAutomaton; dsimp; infer_instance
  letI : Decidable (b ∈ (baseAutomaton true).accept) := by unfold baseAutomaton; dsimp; infer_instance
  decide ((minimumTable s.val).1 < 1492 ∧
    (s ∈ minimumAutomaton.start → b ∈ (baseAutomaton true).start) ∧
    (s ∈ minimumAutomaton.accept → b ∈ (baseAutomaton true).accept)) &&
    ((minimumTable s.val).2.2.1).all fun e =>
      ((minimumTable e.1).1 % 1492, e.2) ∈ (baseTable b.val).2.1

private def projectionBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => projectionRowCheck (start+k)

/-- The lowest-position product preserves the exact arithmetic meaning of f weights. -/
theorem minimum_path_signed_weight_difference {s t : Fin 1710} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ minimumAutomaton.start) (ht : t ∈ minimumAutomaton.accept)
    (p : minimumAutomaton.Path s t xs) :
    pathCharge (fun _ a _ => a.1) p =
      (signedWeight (xs.foldr (fun a x => a.2.2.1+2*x) 0 +
        ((baseTable (minimumTable s.val).1).1[2]?.getD 0)) : ℤ) -
      (signedWeight (xs.foldr (fun a x => a.2.2.2+2*x) 0 +
        ((baseTable (minimumTable s.val).1).1[3]?.getD 0)) : ℤ) := by
  classical
  have checked (i : ℕ) (hi : i<1710) : projectionRowCheck i = true := by
    have blocks : ∀ b : Fin 27,
      projectionBlockCheck (64*b.val) (min 64 (1710-64*b.val)) = true := by
      intro b
      fin_cases b <;> decide
    have h := blocks ⟨i/64,by omega⟩
    dsimp [projectionBlockCheck] at h
    have hk : i%64 ∈ List.range (min 64 (1710-64*(i/64))) := by
      simp only [List.mem_range]; omega
    have hh := List.all_eq_true.mp h (i%64) hk
    simpa only [show 64*(i/64)+i%64=i by omega] using hh
  let B : Fin 1710 → Fin 1492 := fun i =>
    ⟨(minimumTable i.val).1%1492, Nat.mod_lt _ (by decide)⟩
  have row (i : Fin 1710) : (minimumTable i.val).1 < 1492 ∧
      (i ∈ minimumAutomaton.start → B i ∈ (baseAutomaton true).start) ∧
      (i ∈ minimumAutomaton.accept → B i ∈ (baseAutomaton true).accept) ∧
      ∀ e ∈ (minimumTable i.val).2.2.1,
        ((minimumTable e.1).1%1492, e.2) ∈ (baseTable (B i).val).2.1 := by
    have h := checked i.val i.isLt
    simp only [projectionRowCheck, Nat.mod_eq_of_lt i.isLt, Bool.and_eq_true] at h
    have hprops := of_decide_eq_true h.1
    have hp : (minimumTable i.val).1 < 1492 ∧
      (i ∈ minimumAutomaton.start → B i ∈ (baseAutomaton true).start) ∧
      (i ∈ minimumAutomaton.accept → B i ∈ (baseAutomaton true).accept) := by
      simpa only [Nat.mod_eq_of_lt i.isLt, B] using hprops
    refine ⟨hp.1,hp.2.1,hp.2.2,?_⟩
    intro e he
    have hall := List.all_eq_true.mp h.2
    have hh := of_decide_eq_true (hall e he)
    simpa only [Nat.mod_eq_of_lt i.isLt, B] using hh
  have lift {s t : Fin 1710} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : minimumAutomaton.Path s t xs) :
      ∃ q : (baseAutomaton true).Path (B s) (B t) xs,
        pathCharge (fun _ a _ => a.1) q = pathCharge (fun _ a _ => a.1) p := by
    induction p with
    | nil s => exact ⟨NFA.Path.nil (B s),rfl⟩
    | cons q s t a xs hstep p ih =>
      obtain ⟨p',hp'⟩ := ih
      have hm : (q.val,a) ∈ (minimumTable s.val).2.2.1 := hstep
      have hedge := (row s).2.2.2 (q.val,a) hm
      refine ⟨NFA.Path.cons (B q) (B s) (B t) a xs hedge p',?_⟩
      simpa only [pathCharge,hp']
  obtain ⟨q,hq⟩ := lift p
  have h := base_path_signed_weight_difference true ((row s).2.1 hs) ((row t).2.2.1 ht) q
  rw [hq] at h
  simpa only [B, Nat.mod_eq_of_lt (row s).1] using h

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.minimum_path_signed_weight_difference
