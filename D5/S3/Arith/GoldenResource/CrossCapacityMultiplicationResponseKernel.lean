/- GID: D5/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All multiplication responses across capacity boxes are classified by remaining capacities, squarefreeness, and parity. -/

import D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel
import Mathlib.Algebra.Ring.Commute

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.CrossCapacityMultiplicationResponseKernel

open D5.S0.Rewriting.GuardedBoxPaths
open D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Two states in possibly different capacity boxes agree on all multiplication words. -/
def EqPlusAll (A : P → ℕ) (a : State A) (B : P → ℕ) (b : State B) : Prop :=
  (Setoid.ker (plusAllObservation (P := P))).r ⟨A, a⟩ ⟨B, b⟩

/-- Agreement on every multiplication word is equivalent to equal remaining capacities,
with either two nonsquarefree states or two squarefree states of equal total parity
whose coordinates agree wherever the remaining capacity is positive. -/
theorem eq_plus_all_iff (A B : P → ℕ) (a : State A) (b : State B) :
    EqPlusAll A a B b ↔ remaining A a.val = remaining B b.val ∧
      ((¬ SF a.val ∧ ¬ SF b.val) ∨
        (SF a.val ∧ SF b.val ∧ (∑ p, a.val p) % 2 = (∑ p, b.val p) % 2 ∧
          ∀ p, 0 < remaining A a.val p → a.val p = b.val p)) := by
  classical
  have guard (A : P → ℕ) : ∀ (w : List P) (c : P → ℕ), (∀ p, c p ≤ A p) →
      (eval A c (w.map (fun p => (p, true))) ≠ none ↔
        ∀ p, c p + w.count p ≤ A p) := by
    intro w
    induction w with
    | nil => intro c hc; simpa [eval] using hc
    | cons q w ih =>
      intro c hc
      by_cases hg : c q < A q
      · have hu : ∀ p, Function.update c q (c q + 1) p ≤ A p := by
          intro p
          by_cases hp : p = q
          · subst p; simp only [Function.update_self]; omega
          · simpa [Function.update_of_ne hp] using hc p
        simp only [List.map_cons, eval, step, if_true, hg, Option.bind_some]
        rw [ih _ hu]
        constructor <;> intro hw p
        · have hpw := hw p
          by_cases hp : p = q
          · subst p; simp only [Function.update_self, List.count_cons_self] at *; omega
          · simpa [Function.update_of_ne hp, List.count_cons_of_ne (Ne.symm hp)] using hpw
        · have hpw := hw p
          by_cases hp : p = q
          · subst p; simp only [Function.update_self, List.count_cons_self] at *; omega
          · simpa [Function.update_of_ne hp, List.count_cons_of_ne (Ne.symm hp)] using hpw
      · simp only [List.map_cons, eval, step, if_true, hg, if_false, Option.bind_none,
          ne_eq, not_true_eq_false, false_iff]
        intro hw
        have hpw := hw q
        simp only [List.count_cons_self] at hpw
        omega
  have endpoint (A : P → ℕ) (c d : P → ℕ) (w : List P)
      (he : eval A c (w.map (fun p => (p, true))) = some d) :
      d = fun p => c p + w.count p := by
    funext p
    have hec := endpoint_counts A c d (w.map (fun p => (p, true))) he p
    have hup : (w.map (fun p => (p, true))).count (p, true) = w.count p :=
      List.count_map_of_injective w (fun p => (p, true))
        (fun _ _ heq => congrArg Prod.fst heq) p
    have hdown : (w.map (fun p => (p, true))).count (p, false) = 0 := by
      apply List.count_eq_zero.mpr
      simp
    rw [hup, hdown] at hec
    omega
  have read (A : P → ℕ) (c : State A) (w : List P) :
      plusAllObservation ⟨A, c⟩ w =
        if ∀ p, c.val p + w.count p ≤ A p then
          some (mu (fun p => c.val p + w.count p)) else none := by
    unfold plusAllObservation response
    cases he : eval A c.val (w.map (fun p => (p, true))) with
    | none =>
      have hn : ¬ ∀ p, c.val p + w.count p ≤ A p := by
        intro hg
        exact (guard A w c.val c.property).mpr hg he
      simp [hn]
    | some d =>
      have hg := (guard A w c.val c.property).mp (by rw [he]; simp)
      rw [endpoint A c.val d w he]
      simp [hg]
  have repeat_test (A : P → ℕ) (c : State A) (p : P) (n : ℕ) :
      plusAllObservation ⟨A, c⟩ (List.replicate n p) ≠ none ↔ n ≤ A p - c.val p := by
    have fit : (∀ q, c.val q + (List.replicate n p).count q ≤ A q) ↔
        n ≤ A p - c.val p := by
      constructor
      · intro hf
        have hp := hf p
        simp only [List.count_replicate_self] at hp
        omega
      · intro hn q
        by_cases hq : q = p
        · subst q; simp only [List.count_replicate_self]; have := c.property p; omega
        · simpa [List.count_replicate, Ne.symm hq] using c.property q
    rw [read]
    by_cases hf : ∀ q, c.val q + (List.replicate n p).count q ≤ A q
    · simp [hf, fit.mp hf]
    · have hn : ¬ n ≤ A p - c.val p := fun hn => hf (fit.mpr hn)
      simp [hf, hn]
  have mu_nonzero (c : P → ℕ) : mu c ≠ 0 ↔ SF c := by
    by_cases hc : SF c <;> simp [mu, hc]
  have parity_sign (m n : ℕ) :
      (-1 : ℤ) ^ m = (-1 : ℤ) ^ n ↔ m % 2 = n % 2 := by
    rw [neg_one_pow_eq_pow_mod_two m, neg_one_pow_eq_pow_mod_two n]
    have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm <;> rcases hn with hn | hn <;> simp [hm, hn]
  have zero_one (C D : P → ℕ) (c : State C) (d : State D)
      (hc : SF c.val) (p : P) (hcp : c.val p = 0) (hdp : d.val p = 1)
      (hC : c.val p < C p) (hD : d.val p < D p) :
      plusAllObservation ⟨C, c⟩ [p] ≠ plusAllObservation ⟨D, d⟩ [p] := by
    have hcsf : SF (Function.update c.val p (c.val p + 1)) := by
      intro q
      by_cases hq : q = p
      · subst q; simp [hcp]
      · simpa [Function.update_of_ne hq] using hc q
    have hdnsf : ¬ SF (Function.update d.val p (d.val p + 1)) := by
      intro hs
      have hp := hs p
      simp [hdp] at hp
    simp [plusAllObservation, response, eval, step, hC, hD, mu, hcsf, hdnsf]
  change (plusAllObservation ⟨A, a⟩ = plusAllObservation ⟨B, b⟩) ↔ _
  constructor
  · intro he
    have hmu : mu a.val = mu b.val := by
      simpa [plusAllObservation, response, eval] using congrFun he []
    have sf_iff : SF a.val ↔ SF b.val := by
      rw [← mu_nonzero, ← mu_nonzero, hmu]
    have hr : remaining A a.val = remaining B b.val := by
      funext p
      have tests (n : ℕ) : (n ≤ A p - a.val p ↔ n ≤ B p - b.val p) := by
        rw [← repeat_test A a p n, ← repeat_test B b p n,
          congrFun he (List.replicate n p)]
      have hab := (tests (A p - a.val p)).mp le_rfl
      have hba := (tests (B p - b.val p)).mpr le_rfl
      exact Nat.le_antisymm hab hba
    refine ⟨hr, ?_⟩
    by_cases ha : SF a.val
    · have hb := sf_iff.mp ha
      refine Or.inr ⟨ha, hb, ?_, ?_⟩
      · apply (parity_sign _ _).mp
        simpa [mu, ha, hb] using hmu
      · intro p hp
        have hAp : a.val p < A p := by
          change 0 < A p - a.val p at hp
          omega
        have hBp : b.val p < B p := by
          rw [hr] at hp
          change 0 < B p - b.val p at hp
          omega
        by_contra hne
        have hap := ha p
        have hbp := hb p
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact zero_one A B a b ha p (by omega) (by omega) hAp hBp
            (congrFun he [p])
        · exact zero_one B A b a hb p (by omega) (by omega) hBp hAp
            (congrFun he [p]).symm
    · exact Or.inl ⟨ha, fun hb => ha (sf_iff.mpr hb)⟩
  · rintro ⟨hr, hbranch⟩
    funext w
    have fit : (∀ p, a.val p + w.count p ≤ A p) ↔
        ∀ p, b.val p + w.count p ≤ B p := by
      apply forall_congr'
      intro p
      have hp := congrFun hr p
      simp only [remaining] at hp
      have haA := a.property p
      have hbB := b.property p
      omega
    rw [read, read]
    by_cases hf : ∀ p, a.val p + w.count p ≤ A p
    · rw [if_pos hf, if_pos (fit.mp hf)]
      congr 1
      rcases hbranch with ⟨ha, hb⟩ | ⟨ha, hb, hpar, hab⟩
      · have zero (c : P → ℕ) (hc : ¬ SF c) :
            mu (fun p => c p + w.count p) = 0 := by
          have hn : ¬ SF (fun p => c p + w.count p) := by
            intro hs
            apply hc
            intro p
            have hp := hs p
            change c p + w.count p ≤ 1 at hp
            omega
          simp [mu, hn]
        rw [zero a.val ha, zero b.val hb]
      · have immobile (p : P) (hp : ¬ 0 < remaining A a.val p) : w.count p = 0 := by
          have hfp := hf p
          change ¬ 0 < A p - a.val p at hp
          omega
        have sf_end : SF (fun p => a.val p + w.count p) ↔
            SF (fun p => b.val p + w.count p) := by
          constructor <;> intro hs p
          · by_cases hp : 0 < remaining A a.val p
            · change b.val p + w.count p ≤ 1
              rw [← hab p hp]
              exact hs p
            · simpa [immobile p hp] using hb p
          · by_cases hp : 0 < remaining A a.val p
            · change a.val p + w.count p ≤ 1
              rw [hab p hp]
              exact hs p
            · simpa [immobile p hp] using ha p
        by_cases hsa : SF (fun p => a.val p + w.count p)
        · rw [mu, mu, if_pos hsa, if_pos (sf_end.mp hsa)]
          apply (parity_sign _ _).mpr
          simp only [Finset.sum_add_distrib]
          omega
        · have hsb : ¬ SF (fun p => b.val p + w.count p) := fun h => hsa (sf_end.mpr h)
          simp [mu, hsa, hsb]
    · rw [if_neg hf, if_neg (fun h => hf (fit.mpr h))]

end D5.S3.Arith.GoldenResource.CrossCapacityMultiplicationResponseKernel
