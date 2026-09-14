/- GID: D5/S3/Arith/GoldenResource/SignedFiniteMultiplicationResponseKernel
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/SignedFiniteMultiplicationResponseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite multiplication and division responses classify states by squarefree distance and truncated two-sided guards. -/

import D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel
import D5.S0.Rewriting.GuardedBoxPaths
import Mathlib.Algebra.Ring.Commute

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.Arith.GoldenResource.SignedFiniteMultiplicationResponseKernel

open D5.S0.Rewriting.GuardedBoxPaths
open D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The defect counts the divisions needed to make every coordinate at most one. -/
def defect (a : P → ℕ) : ℕ := ∑ p, (a p - 1)

/-- The guard code records both distances to each coordinate boundary up to the horizon. -/
def guardCode (A a : P → ℕ) (h : ℕ) : P → ℕ × ℕ :=
  fun p => (min (a p) h, min (A p - a p) h)

/-- A signed observation records responses to all multiplication and division words within its horizon. -/
def signedObservation (h : ℕ) (x : Located P) :
    {w : List (Instruction P) // w.length ≤ h} → Option ℤ :=
  fun w => response x w.val

/-- Two states agree when all signed responses within the finite horizon agree. -/
def EqSigned (A : P → ℕ) (a : State A) (B : P → ℕ) (b : State B) (h : ℕ) : Prop :=
  (Setoid.ker (signedObservation (P := P) h)).r ⟨A, a⟩ ⟨B, b⟩

/-- At a positive horizon, exactly the distinct states beyond squarefree distance with equal
truncated two-sided guards have identical multiplication and division responses. -/
theorem eq_signed_iff (A : P → ℕ) (a b : State A) (h : ℕ) (hh : 1 ≤ h) :
    EqSigned A a A b h ↔ a = b ∨
      (h < defect a.val ∧ h < defect b.val ∧ guardCode A a.val h = guardCode A b.val h) := by
  classical
  have obs (c d : State A) : EqSigned A c A d h ↔
      ∀ w : List (Instruction P), w.length ≤ h → response ⟨A, c⟩ w = response ⟨A, d⟩ w := by
    change (signedObservation h ⟨A, c⟩ = signedObservation h ⟨A, d⟩) ↔ _
    constructor
    · intro he w hw; exact congrFun he ⟨w, hw⟩
    · intro he; funext w; exact he w.val w.property
  have div_guard : ∀ (w : List P) (c : P → ℕ),
      eval A c (w.map (fun p => (p, false))) ≠ none ↔ ∀ p, w.count p ≤ c p := by
    intro w
    induction w with
    | nil => intro c; simp [eval]
    | cons q w ih =>
      intro c
      by_cases hg : 0 < c q
      · simp only [List.map_cons, eval, step, Bool.false_eq_true, ↓reduceIte, hg,
          Option.bind_some]
        rw [ih]
        constructor <;> intro hw p
        · have hpw := hw p
          by_cases hp : p = q
          · subst p; simp only [Function.update_self, List.count_cons_self] at *; omega
          · simpa [Function.update_of_ne hp, List.count_cons_of_ne (Ne.symm hp)] using hpw
        · have hpw := hw p
          by_cases hp : p = q
          · subst p; simp only [Function.update_self, List.count_cons_self] at *; omega
          · simpa [Function.update_of_ne hp, List.count_cons_of_ne (Ne.symm hp)] using hpw
      · simp only [List.map_cons, eval, step, Bool.false_eq_true, ↓reduceIte, hg,
          Option.bind_none, ne_eq, not_true_eq_false, false_iff]
        intro hw
        have hpw := hw q
        simp only [List.count_cons_self] at hpw
        omega
  have div_endpoint (c d : P → ℕ) (w : List P)
      (he : eval A c (w.map (fun p => (p, false))) = some d) (p : P) :
      d p + w.count p = c p := by
    have hec := endpoint_counts A c d (w.map (fun p => (p, false))) he p
    have hdown : (w.map (fun p => (p, false))).count (p, false) = w.count p :=
      List.count_map_of_injective w (fun p => (p, false))
        (fun _ _ heq => congrArg Prod.fst heq) p
    have hup : (w.map (fun p => (p, false))).count (p, true) = 0 := by
      apply List.count_eq_zero.mpr
      simp
    rw [hup, hdown] at hec
    omega
  have repeat_test (c : State A) (p : P) (n : ℕ) :
      response ⟨A, c⟩ ((List.replicate n p).map (fun p => (p, false))) ≠ none ↔ n ≤ c.val p := by
    have fit : (∀ q, (List.replicate n p).count q ≤ c.val q) ↔ n ≤ c.val p := by
      constructor
      · intro hf; simpa using hf p
      · intro hn q
        by_cases hq : q = p
        · subst q; simpa using hn
        · simp [List.count_replicate, Ne.symm hq]
    simpa [response] using (div_guard (List.replicate n p) c.val).trans fit
  have recover (c d : State A) (he : EqSigned A c A d h) :
      guardCode A c.val h = guardCode A d.val h := by
    have hw := (obs c d).mp he
    have hp : EqPlus A c A d h := by
      change plusObservation h ⟨A, c⟩ = plusObservation h ⟨A, d⟩
      funext w
      exact hw (w.val.map (fun p => (p, true))) (by simpa using w.property)
    have hr : truncRemaining A c.val h = truncRemaining A d.val h := by
      rcases (eq_plus_iff A c d h hh).mp hp with heq | ⟨_, _, hr⟩
      · subst d; rfl
      · exact hr
    funext p
    apply Prod.ext
    · have tests (n : ℕ) (hn : n ≤ h) : (n ≤ c.val p ↔ n ≤ d.val p) := by
        rw [← repeat_test c p n, ← repeat_test d p n,
          hw ((List.replicate n p).map (fun p => (p, false))) (by simpa using hn)]
      have hab := (tests (min (c.val p) h) (min_le_right _ _)).mp (min_le_left _ _)
      have hba := (tests (min (d.val p) h) (min_le_right _ _)).mpr (min_le_left _ _)
      change min (c.val p) h = min (d.val p) h
      omega
    · exact congrFun hr p
  have root_word (c : P → ℕ) : ∃ w : List P,
      w.length = defect c ∧ ∀ p, w.count p = c p - 1 := by
    refine ⟨Finset.univ.toList.flatMap (fun p => List.replicate (c p - 1) p), ?_, ?_⟩
    · simp [List.length_flatMap, Finset.sum_map_toList, defect]
    · intro p
      simp [List.count_flatMap, Function.comp_def, List.count_replicate,
        Finset.sum_map_toList]
  have near_le (c d : State A) (he : EqSigned A c A d h) (hc : defect c.val ≤ h) :
      ∀ p, d.val p ≤ c.val p := by
    have hg := recover c d he
    obtain ⟨w, hwlen, hwcount⟩ := root_word c.val
    have hwfit : ∀ p, w.count p ≤ c.val p := by intro p; rw [hwcount]; omega
    obtain ⟨e, heval⟩ : ∃ e, eval A c.val (w.map (fun p => (p, false))) = some e :=
      Option.ne_none_iff_exists'.mp ((div_guard w c.val).mpr hwfit)
    have hesf : SF e := by
      intro p
      have hp := div_endpoint c.val e w heval p
      rw [hwcount] at hp
      omega
    have hemu : mu e ≠ 0 := by simp [mu, hesf]
    have heobs := (obs c d).mp he (w.map (fun p => (p, false))) (by simpa [hwlen] using hc)
    have deval : eval A d.val (w.map (fun p => (p, false))) ≠ none := by
      intro hn
      simp [response, heval, hn] at heobs
    obtain ⟨f, hfval⟩ := Option.ne_none_iff_exists'.mp deval
    have hfsf : SF f := by
      have hmf : mu e = mu f := by simpa [response, heval, hfval] using heobs
      by_contra hn
      exact hemu (hmf.trans (by simp [mu, hn]))
    intro p
    have hp := div_endpoint d.val f w hfval p
    rw [hwcount] at hp
    have hf := hfsf p
    by_cases hz : c.val p = 0
    · have hg0 := congrArg Prod.fst (congrFun hg p)
      change min (c.val p) h = min (d.val p) h at hg0
      omega
    · omega
  have near_eq (c d : State A) (he : EqSigned A c A d h) (hc : defect c.val ≤ h) : c = d := by
    have hdle := near_le c d he hc
    have hd : defect d.val ≤ h := (Finset.sum_le_sum (fun p _ =>
      Nat.sub_le_sub_right (hdle p) 1)).trans hc
    have hsym : EqSigned A d A c h := by
      change signedObservation h ⟨A, d⟩ = signedObservation h ⟨A, c⟩
      exact he.symm
    have hcle := near_le d c hsym hd
    apply Subtype.ext
    funext p
    exact Nat.le_antisymm (hcle p) (hdle p)
  have far_zero (c : State A) (hc : h < defect c.val) (w : List (Instruction P))
      (hw : w.length ≤ h) (e : P → ℕ) (he : eval A c.val w = some e) : mu e = 0 := by
    have hn : ¬ SF e := by
      intro hs
      have hdist := (path_lower_bound A c.val e w ⟨c.property, he⟩).2.2.1
      have hdef : defect c.val ≤ distance c.val e := by
        apply Finset.sum_le_sum
        intro p _
        have hp := hs p
        have ha := Int.le_natAbs (a := (c.val p : ℤ) - (e p : ℤ))
        rw [show (c.val p : ℤ) - e p = -((e p : ℤ) - c.val p) by omega,
          Int.natAbs_neg] at ha
        omega
      omega
    simp [mu, hn]
  have guard_sync : ∀ (w : List (Instruction P)) (n : ℕ) (c d : State A),
      w.length ≤ n → guardCode A c.val n = guardCode A d.val n →
      (eval A c.val w = none ↔ eval A d.val w = none) := by
    intro w
    induction w with
    | nil => intro n c d hw hg; simp [eval]
    | cons s w ih =>
      intro n c d hw hg
      have hn : 1 ≤ n := by simp only [List.length_cons] at hw; omega
      have htail : w.length ≤ n - 1 := by simp only [List.length_cons] at hw; omega
      have codes (p : P) : min (c.val p) n = min (d.val p) n ∧
          min (A p - c.val p) n = min (A p - d.val p) n := by
        exact Prod.mk.inj (congrFun hg p)
      rcases s with ⟨q, up⟩
      have hq := codes q
      have hcA := c.property q
      have hdA := d.property q
      cases up with
      | false =>
        by_cases hcg : 0 < c.val q
        · have hdg : 0 < d.val q := by omega
          let c' : State A := ⟨Function.update c.val q (c.val q - 1), by
            intro p
            by_cases hp : p = q
            · subst p; simp only [Function.update_self]; omega
            · simpa [Function.update_of_ne hp] using c.property p⟩
          let d' : State A := ⟨Function.update d.val q (d.val q - 1), by
            intro p
            by_cases hp : p = q
            · subst p; simp only [Function.update_self]; omega
            · simpa [Function.update_of_ne hp] using d.property p⟩
          have hg' : guardCode A c'.val (n - 1) = guardCode A d'.val (n - 1) := by
            funext p
            have hp := codes p
            have hcp := c.property p
            have hdp := d.property p
            by_cases heq : p = q
            · subst p
              simp only [guardCode, c', d', Function.update_self]
              congr 1 <;> omega
            · simp only [guardCode, c', d', Function.update_of_ne heq]
              congr 1 <;> omega
          simpa only [eval, step, Bool.false_eq_true, ↓reduceIte, hcg, hdg,
            Option.bind_some] using ih (n - 1) c' d' htail hg'
        · have hdg : ¬ 0 < d.val q := by omega
          simp [eval, step, hcg, hdg]
      | true =>
        by_cases hcg : c.val q < A q
        · have hdg : d.val q < A q := by omega
          let c' : State A := ⟨Function.update c.val q (c.val q + 1), by
            intro p
            by_cases hp : p = q
            · subst p; simp only [Function.update_self]; omega
            · simpa [Function.update_of_ne hp] using c.property p⟩
          let d' : State A := ⟨Function.update d.val q (d.val q + 1), by
            intro p
            by_cases hp : p = q
            · subst p; simp only [Function.update_self]; omega
            · simpa [Function.update_of_ne hp] using d.property p⟩
          have hg' : guardCode A c'.val (n - 1) = guardCode A d'.val (n - 1) := by
            funext p
            have hp := codes p
            have hcp := c.property p
            have hdp := d.property p
            by_cases heq : p = q
            · subst p
              simp only [guardCode, c', d', Function.update_self]
              congr 1 <;> omega
            · simp only [guardCode, c', d', Function.update_of_ne heq]
              congr 1 <;> omega
          simpa only [eval, step, ↓reduceIte, hcg, hdg,
            Option.bind_some] using ih (n - 1) c' d' htail hg'
        · have hdg : ¬ d.val q < A q := by omega
          simp [eval, step, hcg, hdg]
  rw [obs]
  constructor
  · intro he
    have heq : EqSigned A a A b h := (obs a b).mpr he
    by_cases hab : a = b
    · exact Or.inl hab
    · refine Or.inr ⟨?_, ?_, recover a b heq⟩
      · by_contra hn
        exact hab (near_eq a b heq (by omega))
      · by_contra hn
        have hsym : EqSigned A b A a h := by
          change signedObservation h ⟨A, b⟩ = signedObservation h ⟨A, a⟩
          exact heq.symm
        exact hab (near_eq b a hsym (by omega)).symm
  · rintro (hab | ⟨ha, hb, hg⟩)
    · subst b; intro w hw; rfl
    · intro w hw
      have hsync := guard_sync w h a b hw hg
      cases hea : eval A a.val w with
      | none => simp [response, hea, hsync.mp hea]
      | some e =>
        cases heb : eval A b.val w with
        | none => have := hsync.mpr heb; rw [hea] at this; contradiction
        | some f => simp [response, hea, heb, far_zero a ha w hw e hea, far_zero b hb w hw f heb]

end D5.S3.Arith.GoldenResource.SignedFiniteMultiplicationResponseKernel
