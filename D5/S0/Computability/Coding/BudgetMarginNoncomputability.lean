/- GID: D5/S0/Computability/Coding/BudgetMarginNoncomputability
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/BudgetMarginNoncomputability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-support budget programs admit no uniform positive-margin or optimal-mass algorithm. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce
import Mathlib.Tactic

open Nat.Partrec (Code)
open Nat.Partrec.Code

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace D5.S0.Computability.Coding.BudgetMarginNoncomputability

private def seen (c : Code) (n : ℕ) : Bool := (evaln n c 0).isSome

private def first (c : Code) (n : ℕ) : Bool := seen c n && !(seen c (n - 1))

private def pulse (d : ℕ) (c : Code) (n : ℕ) : ℕ :=
  bif first c n then d^n - 1 else 0

private theorem prim_seen : Primrec fun q : Code × ℕ => seen q.1 q.2 :=
  Primrec.option_isSome.comp <| primrec_evaln.comp
    ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0))

private theorem prim_first : Primrec fun q : Code × ℕ => first q.1 q.2 :=
  Primrec.and.comp prim_seen (Primrec.not.comp <|
    prim_seen.comp (Primrec.fst.pair <| Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))

private theorem prim_pulse (d : ℕ) : Primrec fun q : Code × ℕ => pulse d q.1 q.2 := by
  apply Primrec.cond prim_first _ (Primrec.const 0)
  exact Primrec.nat_sub.comp
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const d) Primrec.snd)
    (Primrec.const 1)

private theorem exists_compiler (d : ℕ) : ∃ compile : Code → Code,
    Computable compile ∧ ∀ c n, eval (compile c) n = Part.some (pulse d c n) := by
  have hc : Computable fun k : ℕ => pulse d (Denumerable.ofNat Code k.unpair.1) k.unpair.2 :=
    (prim_pulse d).to_comp.comp
      (((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair)).pair
        (Computable.snd.comp Computable.unpair))
  obtain ⟨q, hq⟩ := exists_code.mp (Partrec.nat_iff.mp hc.partrec)
  refine ⟨fun c => curry q (Encodable.encode c),
    primrec₂_curry.to_comp.comp (Computable.const q) Computable.encode, ?_⟩
  intro c n
  simpa only [eval_curry, hq, PFun.coe_val, Nat.unpair_pair, Denumerable.ofNat_encode]

private theorem seen_mono (c : Code) {n m : ℕ} (h : n ≤ m) : seen c n = true → seen c m = true := by
  simp only [seen, Option.isSome_iff_exists]
  rintro ⟨x, hx⟩
  exact ⟨x, evaln_mono h hx⟩

private theorem first_pos (c : Code) {n : ℕ} (h : first c n = true) : 0 < n := by
  cases n with
  | zero => simp [first, seen, evaln] at h
  | succ n => omega

private theorem first_unique (c : Code) {n m : ℕ} (hn : first c n = true) (hm : first c m = true) : n = m := by
  simp only [first, Bool.and_eq_true] at hn hm
  rcases lt_trichotomy n m with h | h | h
  · have hh := seen_mono c (show n ≤ m-1 by omega) hn.1
    cases he : seen c (m-1) <;> simp_all
  · exact h
  · have hh := seen_mono c (show m ≤ n-1 by omega) hm.1
    cases he : seen c (n-1) <;> simp_all

private theorem support_subsingleton (d : ℕ) (c : Code) : (Function.support (pulse d c)).Subsingleton := by
  intro n hn m hm
  have hn' : first c n = true := by
    cases h : first c n <;> simp_all [Function.mem_support, pulse]
  have hm' : first c m = true := by
    cases h : first c m <;> simp_all [Function.mem_support, pulse]
  exact first_unique c hn' hm'

private theorem no_cutoff : ¬ ∃ A : Code →. ℕ, Partrec A ∧
    ∀ c, ∃ N ∈ A c, ∀ k, first c k = true → k ≤ N := by
  rintro ⟨A, hA, hs⟩
  let cutoff : Code → ℕ := fun c => Classical.choose (hs c)
  have hcut : Computable cutoff := hA.of_eq_tot (fun c => (Classical.choose_spec (hs c)).1)
  have hb : Computable fun c => seen c (cutoff c) :=
    prim_seen.to_comp.comp (Computable.id.pair hcut)
  apply ComputablePred.halting_problem 0
  have hbp : ComputablePred (fun c => seen c (cutoff c) = true) :=
    ⟨inferInstance, by simpa using hb⟩
  apply hbp.of_eq
  intro c
  constructor
  · intro h
    simp only [seen, Option.isSome_iff_exists] at h
    obtain ⟨x, hx⟩ := h
    exact (evaln_sound hx).1
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨n, hn⟩ := evaln_complete.mp hx
    have hex : ∃ n, seen c n = true := ⟨n, by simp [seen, Option.isSome_iff_exists]; exact ⟨x, hn⟩⟩
    let t := Nat.find hex
    have ht : first c t = true := by
      have hseen : seen c t = true := Nat.find_spec hex
      have hpos : 0 < t := by
        by_contra hh
        have ht0 : t = 0 := by omega
        rw [ht0] at hseen
        simp [seen, evaln] at hseen
      have hprev : seen c (t-1) = false := by
        have := Nat.find_min hex (show t-1 < t by omega)
        cases hv : seen c (t-1) <;> simp_all
      simp [first, hseen, hprev]
    exact seen_mono c ((Classical.choose_spec (hs c)).2 t ht) (Nat.find_spec hex)


private theorem first_halts (c : Code) {n : ℕ} (h : first c n = true) : (eval c 0).Dom := by
  have h' : seen c n = true := by
    simp only [first, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h'
  exact (evaln_sound hx).1

private theorem pulse_shape (d : ℕ) (c : Code) {n : ℕ} (h : first c n = true) :
    ∀ k, pulse d c k = if k = n then d^n - 1 else 0 := by
  intro k
  by_cases hkn : k = n
  · subst k; simp [pulse, h]
  · have hk : first c k = false := by
      cases hh : first c k
      · rfl
      · exact (hkn (first_unique c hh h)).elim
    simp [pulse, hk, hkn]


end D5.S0.Computability.Coding.BudgetMarginNoncomputability
