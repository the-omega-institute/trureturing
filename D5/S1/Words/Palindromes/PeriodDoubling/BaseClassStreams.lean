/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams
   mirror-E: none(waiver:unbounded-class-flag-semantics)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: Charge-mode accepted paths forbid opposite signed digits two positions apart. -/

/-
proof_shape: content (base_path_class_spacing)
escape_witness: Persistent violation-flag semantics and ordered three-digit path reconstruction.
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

private def classRowCheck (i : ℕ) : Bool :=
  let S := (baseTable i).1
  (baseTable i).2.1.all fun e =>
    let T := (baseTable e.1).1
    decide (T[11]?.getD 0 = S[10]?.getD 0 ∧
      T[13]?.getD 0 = S[12]?.getD 0 ∧
      T[10]?.getD 0 * S[11]?.getD 0 ≠ -1 ∧
      (T[18]?.getD 0 = 0 → S[18]?.getD 0 = 0 ∧
        T[12]?.getD 0 * S[13]?.getD 0 ≠ -1))
private def classBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => classRowCheck (start+k)
/-- Accepted charge-mode paths cannot have opposite signed digits two positions apart. -/
theorem base_path_class_spacing (output : Bool) {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (ht : t ∈ (baseAutomaton true).accept)
    (p : (baseAutomaton true).Path s t xs) :
    let ds := pathOutputs (fun _ _ q => (baseTable q.val).1[if output then 12 else 10]?.getD 0) p
    (ds.zip ds.tail).IsChain (fun a b => a.1*b.2 ≠ -1) := by
  have checked (i : ℕ) (hi : i<1492) : classRowCheck i = true := by
    have blocks : ∀ b : Fin 24,
      classBlockCheck (64*b.val) (min 64 (1492-64*b.val)) = true := by
      intro b; fin_cases b <;> decide
    have h := blocks ⟨i/64,by omega⟩
    dsimp [classBlockCheck] at h
    have hk : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range]; omega
    have hh := List.all_eq_true.mp h (i%64) hk
    simpa only [show 64*(i/64)+i%64=i by omega] using hh
  let digit : Fin 1492 → ℤ := fun q => (baseTable q.val).1[if output then 12 else 10]?.getD 0
  have edge (s q : Fin 1492) (a : ℤ × ℤ × ℤ × ℤ)
      (hstep : q ∈ (baseAutomaton true).step s a) :
      (baseTable q.val).1[11]?.getD 0 = (baseTable s.val).1[10]?.getD 0 ∧
      (baseTable q.val).1[13]?.getD 0 = (baseTable s.val).1[12]?.getD 0 ∧
      (baseTable q.val).1[10]?.getD 0 * (baseTable s.val).1[11]?.getD 0 ≠ -1 ∧
      ((baseTable q.val).1[18]?.getD 0 = 0 →
        (baseTable s.val).1[18]?.getD 0 = 0 ∧
        (baseTable q.val).1[12]?.getD 0 * (baseTable s.val).1[13]?.getD 0 ≠ -1) := by
    have hm : (q.val,a) ∈ (baseTable s.val).2.1 := hstep
    have h := List.all_eq_true.mp (checked s.val s.isLt) (q.val,a) hm
    dsimp only [classRowCheck] at h
    exact of_decide_eq_true h
  have invariant {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton true).Path s t xs)
      : (baseTable t.val).1[18]?.getD 0 = 0 →
      (baseTable s.val).1[18]?.getD 0 = 0 ∧
      ((pathOutputs (fun _ _ q => digit q) p).zip
        (pathOutputs (fun _ _ q => digit q) p).tail).IsChain (fun a b => a.1*b.2 ≠ -1) := by
    have flags {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
        (p : (baseAutomaton true).Path s t xs)
        : (baseTable t.val).1[18]?.getD 0 = 0 →
        (baseTable s.val).1[18]?.getD 0 = 0 := by
      induction p with
      | nil _ => exact id
      | cons q s t a xs hstep p ih =>
        intro hf
        exact ((edge s q a hstep).2.2.2 (ih hf)).1
    induction p with
    | nil s => intro hflag; exact ⟨hflag,by simp [pathOutputs]⟩
    | cons q s t a xs hstep p ih =>
      intro hflag
      obtain ⟨hq,ih⟩ := ih hflag
      have hs := (edge s q a hstep).2.2.2 hq
      refine ⟨hs.1,?_⟩
      cases p with
      | nil q => simp [pathOutputs]
      | cons r q t b ys hstep' p' =>
        cases p' with
        | nil r => exact List.IsChain.singleton _
        | cons u r t c zs hstep'' p'' =>
          apply List.isChain_cons_cons.mpr
          refine ⟨?_,ih⟩
          cases output
          · dsimp [digit]
            have he := (edge r u c hstep'').2.2.1
            have hp := (edge q r b hstep').1
            rw [hp] at he
            simpa [mul_comm] using he
          · dsimp [digit]
            have hu := flags p'' hflag
            have he := ((edge r u c hstep'').2.2.2 hu).2
            have hp := (edge q r b hstep').2.1
            rw [hp] at he
            simpa [mul_comm] using he
  have hflag : (baseTable t.val).1[18]?.getD 0=0 := by
    have ht' := ht
    simp only [baseAutomaton,Set.mem_ofPred_eq,Bool.and_eq_true] at ht'
    simpa only [beq_iff_eq, ite_true] using ht'.2
  exact (invariant p hflag).2

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_class_spacing
