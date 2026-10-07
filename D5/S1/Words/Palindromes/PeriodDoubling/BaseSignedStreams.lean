/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseSignedStreams
   mirror-E: none(waiver:unbounded-transducer-stream-realization)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.base_path_Q_semantics; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: Accepted paths emit sparse signed digits with their exact radix-two value. -/

/-
proof_shape: content (base_path_sparse_signed_digits)
escape_witness: Ordered digit reconstruction, nonadjacency, and radix-two telescoping for arbitrary paths.
admission_basis: escape-witness
Direct frozen dependencies: none; BaseCertificates is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseCertificates
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

/-- Ordered transition observations along a specific nondeterministic automaton path. -/
def pathOutputs {α σ β : Type*} {M : NFA α σ} (emit : σ → α → σ → β)
    {s t : σ} {xs : List α} : M.Path s t xs → List β
  | .nil _ => []
  | .cons q s _ a _ _ p => emit s a q :: pathOutputs emit p

private def streamRowCheck (i : ℕ) : Bool :=
  let S := (baseTable i).1
  ((baseTable i).2.1).all fun e =>
    let T := (baseTable e.1).1
    ([false,true] : List Bool).all fun output =>
      let d := T[if output then 12 else 10]?.getD 0
      let prev := S[if output then 12 else 10]?.getD 0
      let old := 2*(S[if output then 5 else 4]?.getD 0)+
        (S[if output then 7 else 6]?.getD 0)+(S[if output then 9 else 8]?.getD 0)
      let next := 2*(T[if output then 5 else 4]?.getD 0)+
        (T[if output then 7 else 6]?.getD 0)+(T[if output then 9 else 8]?.getD 0)
      let bit := if output then e.2.2.2.2 else e.2.2.2.1
      decide ((d=-1 ∨ d=0 ∨ d=1) ∧ (prev=0 ∨ d=0) ∧
        2*bit+old = d+2*next ∧ (i<7 → d=0) ∧ (bit=0 ∨ bit=1))

private def streamBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => streamRowCheck (start+k)

/-- Accepted base paths emit sparse signed digits representing twice the rounded half. -/
theorem base_path_sparse_signed_digits (charge output : Bool) {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ (baseAutomaton charge).start) (ht : t ∈ (baseAutomaton charge).accept)
    (p : (baseAutomaton charge).Path s t xs) :
    (∀ z ∈ pathOutputs (fun _ _ q => (baseTable q.val).1[if output then 12 else 10]?.getD 0) p,
      z=-1 ∨ z=0 ∨ z=1) ∧
    (pathOutputs (fun _ _ q => (baseTable q.val).1[if output then 12 else 10]?.getD 0) p).IsChain
      (fun a b => a=0 ∨ b=0) ∧
    (pathOutputs (fun _ _ q => (baseTable q.val).1[if output then 12 else 10]?.getD 0) p).foldr
      (fun z acc => z+2*acc) 0 =
      2*(xs.foldr (fun a acc => (if output then a.2.2.2 else a.2.2.1)+2*acc) 0 +
        (baseTable s.val).1[if output then 3 else 2]?.getD 0) ∧
    (pathOutputs (fun _ _ q => (baseTable q.val).1[if output then 12 else 10]?.getD 0) p).head? = some 0 := by
  have checked (i : ℕ) (hi : i<1492) : streamRowCheck i = true := by
    have blocks : ∀ b : Fin 24,
      streamBlockCheck (64*b.val) (min 64 (1492-64*b.val)) = true := by
      intro b
      fin_cases b <;> decide
    have h := blocks ⟨i/64,by omega⟩
    dsimp [streamBlockCheck] at h
    have hk : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range]; omega
    have hh := List.all_eq_true.mp h (i%64) hk
    simpa only [show 64*(i/64)+i%64=i by omega] using hh
  let digit : Fin 1492 → ℤ := fun q => (baseTable q.val).1[if output then 12 else 10]?.getD 0
  let raw : List (ℤ × ℤ × ℤ × ℤ) → ℤ := fun xs => xs.foldr
    (fun a x => (if output then a.2.2.2 else a.2.2.1)+2*x) 0
  let R : Fin 1492 → List (ℤ × ℤ × ℤ × ℤ) → ℤ := fun s xs =>
    2*(raw xs+(baseTable s.val).1[if output then 5 else 4]?.getD 0)+
      (baseTable s.val).1[if output then 7 else 6]?.getD 0+
      (baseTable s.val).1[if output then 9 else 8]?.getD 0
  have edge (s q : Fin 1492) (a : ℤ × ℤ × ℤ × ℤ)
      (ha : q ∈ (baseAutomaton charge).step s a) :
      (digit q=-1 ∨ digit q=0 ∨ digit q=1) ∧
      (digit s=0 ∨ digit q=0) ∧
      (∀ xs, R s (a::xs) = digit q+2*R q xs) ∧
      (s.val<7 → digit q=0) := by
    have hm : (q.val,a) ∈ (baseTable s.val).2.1 := ha
    have h := checked s.val s.isLt
    dsimp only [streamRowCheck] at h
    have hq := List.all_eq_true.mp h (q.val,a) hm
    have ho : output ∈ ([false,true] : List Bool) := by cases output <;> simp
    have hd := of_decide_eq_true (List.all_eq_true.mp hq output ho)
    simp only [Prod.fst, Prod.snd] at hd
    refine ⟨hd.1,hd.2.1,?_,hd.2.2.2.1⟩
    intro xs
    dsimp [R,raw,digit]
    omega
  have coeff {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton charge).Path s t xs) :
      ∀ z ∈ pathOutputs (fun _ _ q => digit q) p, z=-1 ∨ z=0 ∨ z=1 := by
    induction p with
    | nil s => simp [pathOutputs]
    | cons q s t a xs hstep p ih =>
      intro z hz
      simp only [pathOutputs,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact (edge s q a hstep).1
      · exact ih z hz
  have sparse {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton charge).Path s t xs) :
      (pathOutputs (fun _ _ q => digit q) p).IsChain (fun a b => a=0 ∨ b=0) := by
    induction p with
    | nil s => simp [pathOutputs]
    | cons q s t a xs hstep p ih =>
      cases p with
      | nil q => exact List.IsChain.singleton _
      | cons r q t b ys hstep' p' =>
        exact List.isChain_cons_cons.mpr ⟨(edge q r b hstep').2.1, ih⟩
  have value {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton charge).Path s t xs) :
      (pathOutputs (fun _ _ q => digit q) p).foldr (fun z acc => z+2*acc) 0 =
        R s xs - 2^xs.length * R t [] := by
    induction p with
    | nil s => simp [pathOutputs]
    | cons q s t a xs hstep p ih =>
      simp only [pathOutputs,List.foldr_cons,List.length_cons,pow_succ,ih]
      rw [(edge s q a hstep).2.2.1 xs]
      ring
  have ht' := ht
  simp only [baseAutomaton,Set.mem_ofPred_eq,Bool.and_eq_true] at ht'
  have flush := ht'.1
  simp only [baseTerminal,Bool.and_eq_true,List.all_eq_true] at flush
  have hc (k : ℕ) (hk : k ∈ ([4,5,6,7,8,9] : List ℕ)) :
      (baseTable t.val).1[k]?.getD 0=0 := by
    have h := flush.2 k hk
    simpa only [beq_iff_eq] using h
  have hfinal : R t [] = 0 := by
    cases output <;> simp [R,raw,hc 4 (by simp),hc 5 (by simp),hc 6 (by simp),
      hc 7 (by simp),hc 8 (by simp),hc 9 (by simp)]
  have hs' : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 ∨ s.val=4 ∨ s.val=5 ∨ s.val=6 := by
    change ([0,1,2,3,4,5,6] : List ℕ).contains s.val = true at hs
    simpa using hs
  have hsource : R s xs = 2*(raw xs+(baseTable s.val).1[if output then 3 else 2]?.getD 0) := by
    rcases hs' with h | h | h | h | h | h | h <;> cases output <;> dsimp [R] <;> rw [h] <;> norm_num [baseTable]
  have hf := value p
  rw [hfinal,hsource] at hf
  simp only [mul_zero,sub_zero] at hf
  have hhead : (pathOutputs (fun _ _ q => digit q) p).head? = some 0 := by
    cases p with
    | nil s =>
      have hc4 := hc 4 (by simp)
      have hc5 := hc 5 (by simp)
      have hrel := flush.1
      simp only [beq_iff_eq] at hrel
      rcases hs' with h | h | h | h | h | h | h <;> rw [h] at hc4 hc5 hrel <;> norm_num [baseTable] at *
    | cons q s t a ys hstep p =>
      have hslt : s.val<7 := by omega
      have he := (edge s q a hstep).2.2.2 hslt
      simpa only [pathOutputs,List.head?_cons] using congrArg some he
  exact ⟨coeff p,sparse p,hf,hhead⟩

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_sparse_signed_digits
