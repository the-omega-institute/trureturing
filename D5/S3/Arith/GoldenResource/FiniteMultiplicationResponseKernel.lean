/- GID: D5/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite multiplication responses separate squarefree states and classify other states by truncated remaining capacities. -/

import D5.S0.Rewriting.GuardedBoxPaths
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Int.Defs

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel

open D5.S0.Rewriting.GuardedBoxPaths

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A state is a natural coordinate vector bounded by its capacity vector. -/
abbrev State (A : P → ℕ) := {a : P → ℕ // ∀ p, a p ≤ A p}

/-- A located state records both its capacity vector and its bounded coordinates. -/
abbrev Located (P : Type*) := Σ A : P → ℕ, {a : P → ℕ // ∀ p, a p ≤ A p}

/-- A squarefree coordinate vector has every coordinate at most one. -/
def SF (a : P → ℕ) : Prop := ∀ p, a p ≤ 1

/-- Squarefreeness of a finite coordinate vector is decidable. -/
instance (a : P → ℕ) : Decidable (SF a) :=
  inferInstanceAs (Decidable (∀ p, a p ≤ 1))

/-- The signed readout is the parity sign on squarefree vectors and zero otherwise. -/
def mu (a : P → ℕ) : ℤ := if SF a then (-1 : ℤ) ^ (∑ p, a p) else 0

/-- Remaining capacity is the coordinatewise natural difference from the capacity. -/
def remaining (A a : P → ℕ) : P → ℕ := fun p => A p - a p

/-- The finite horizon truncates each remaining capacity at the horizon. -/
def truncRemaining (A a : P → ℕ) (h : ℕ) : P → ℕ :=
  fun p => min (remaining A a p) h

/-- A word returns its endpoint readout on success and the distinct failure value otherwise. -/
def response (x : Located P) (w : List (Instruction P)) : Option ℤ :=
  (eval x.1 x.2.val w).map mu

/-- Multiplication words increase the coordinate named by each letter. -/
def plusAllObservation (x : Located P) : List P → Option ℤ :=
  fun w => response x (w.map (fun p => (p, true)))

/-- A finite observation records responses to every multiplication word within its horizon. -/
def plusObservation (h : ℕ) (x : Located P) : {w : List P // w.length ≤ h} → Option ℤ :=
  fun w => plusAllObservation x w.val

/-- Two located states are equivalent when their finite multiplication observations agree. -/
def EqPlus (A : P → ℕ) (a : State A) (B : P → ℕ) (b : State B) (h : ℕ) : Prop :=
  (Setoid.ker (plusObservation (P := P) h)).r ⟨A, a⟩ ⟨B, b⟩


/-- At every positive horizon, squarefree states are singletons and the other states
are equivalent exactly when their truncated remaining capacity vectors agree. -/
theorem eq_plus_iff (A : P → ℕ) (a b : State A) (h : ℕ) (hh : 1 ≤ h) :
    EqPlus A a A b h ↔ a = b ∨
      (¬ SF a.val ∧ ¬ SF b.val ∧ truncRemaining A a.val h = truncRemaining A b.val h) := by
  classical
  have guard : ∀ (w : List P) (c : P → ℕ), (∀ p, c p ≤ A p) →
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
  have endpoint (c d : P → ℕ) (w : List P)
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
  have read (c : State A) (w : List P) :
      plusAllObservation ⟨A, c⟩ w =
        if ∀ p, c.val p + w.count p ≤ A p then
          some (mu (fun p => c.val p + w.count p)) else none := by
    unfold plusAllObservation response
    cases he : eval A c.val (w.map (fun p => (p, true))) with
    | none =>
      have hn : ¬ ∀ p, c.val p + w.count p ≤ A p := by
        intro hg
        exact (guard w c.val c.property).mpr hg he
      simp [hn]
    | some d =>
      have hg := (guard w c.val c.property).mp (by rw [he]; simp)
      rw [endpoint c.val d w he]
      simp [hg]
  have mu_nonzero (c : P → ℕ) : mu c ≠ 0 ↔ SF c := by
    by_cases hc : SF c
    · simp [mu, hc]
    · simp [mu, hc]
  have obs : EqPlus A a A b h ↔ ∀ (w : List P), w.length ≤ h →
      plusAllObservation ⟨A, a⟩ w = plusAllObservation ⟨A, b⟩ w := by
    change (plusObservation h ⟨A, a⟩ = plusObservation h ⟨A, b⟩) ↔ _
    constructor
    · intro he w hw; exact congrFun he ⟨w, hw⟩
    · intro he; funext w; exact he w.val w.property
  have repeat_test (c : State A) (p : P) (n : ℕ) :
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
  have zero_one (c d : State A) (hc : SF c.val) (p : P)
      (hcp : c.val p = 0) (hdp : d.val p = 1) :
      plusAllObservation ⟨A, c⟩ [p] ≠ plusAllObservation ⟨A, d⟩ [p] := by
    have hAc : c.val p < A p := by have := d.property p; omega
    have hcsf : SF (Function.update c.val p (c.val p + 1)) := by
      intro q
      by_cases hq : q = p
      · subst q; simp [hcp]
      · simpa [Function.update_of_ne hq] using hc q
    have hdnsf : ¬ SF (Function.update d.val p (d.val p + 1)) := by
      intro hs
      have hp := hs p
      simp [hdp] at hp
    by_cases hAd : d.val p < A p
    · simp [plusAllObservation, response, eval, step, hAc, hAd, mu, hcsf, hdnsf]
    · simp [plusAllObservation, response, eval, step, hAc, hAd]
  rw [obs]
  constructor
  · intro he
    have hmu : mu a.val = mu b.val := by
      simpa [plusAllObservation, response, eval] using he [] (by simp)
    have sf_iff : SF a.val ↔ SF b.val := by
      rw [← mu_nonzero, ← mu_nonzero, hmu]
    by_cases ha : SF a.val
    · left
      have hb := sf_iff.mp ha
      apply Subtype.ext
      funext p
      by_contra hp
      have hap := ha p
      have hbp := hb p
      have hw := he [p] (by simpa using hh)
      rcases lt_or_gt_of_ne hp with hlt | hgt
      · exact zero_one a b ha p (by omega) (by omega) hw
      · exact zero_one b a hb p (by omega) (by omega) hw.symm
    · right
      refine ⟨ha, fun hb => ha (sf_iff.mpr hb), ?_⟩
      funext p
      have tests (n : ℕ) (hn : n ≤ h) :
          (n ≤ A p - a.val p ↔ n ≤ A p - b.val p) := by
        rw [← repeat_test a p n, ← repeat_test b p n,
          he (List.replicate n p) (by simpa using hn)]
      have hab := (tests (min (A p - a.val p) h) (min_le_right _ _)).mp
        (min_le_left _ _)
      have hba := (tests (min (A p - b.val p) h) (min_le_right _ _)).mpr
        (min_le_left _ _)
      simp only [truncRemaining, remaining]
      omega
  · rintro (hab | ⟨ha, hb, hr⟩)
    · subst b; intro w hw; rfl
    · intro w hw
      have fit : (∀ p, a.val p + w.count p ≤ A p) ↔
          ∀ p, b.val p + w.count p ≤ A p := by
        have each (p : P) : (a.val p + w.count p ≤ A p) ↔
            b.val p + w.count p ≤ A p := by
          have hp := congrFun hr p
          simp only [truncRemaining, remaining] at hp
          have hc : w.count p ≤ h := List.count_le_length.trans hw
          have haA := a.property p
          have hbA := b.property p
          omega
        exact forall_congr' each
      have zero (c : State A) (hc : ¬ SF c.val) :
          mu (fun p => c.val p + w.count p) = 0 := by
        have hn : ¬ SF (fun p => c.val p + w.count p) := by
          intro hs
          apply hc
          intro p
          have hp := hs p
          change c.val p + w.count p ≤ 1 at hp
          omega
        simp [mu, hn]
      rw [read, read, zero a ha, zero b hb]
      by_cases hf : ∀ p, a.val p + w.count p ≤ A p
      · simp [hf, fit.mp hf]
      · have hfb : ¬ ∀ p, b.val p + w.count p ≤ A p := fun hfb => hf (fit.mpr hfb)
        simp [hf, hfb]

end D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel
