/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdReturns
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdReturns
   mirror-E: none(waiver:source-bound-mechanical-return-classification)
   anchors: []
   utility: none
   digest: Return classification is registered at the physical return-word source operands. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdReturns
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold D5.S1.Words.Mechanical D5.S1.Words.Complexity
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdReturns
noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ alpha rho => lowerMechanicalWord alpha rho) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 → Irrational alpha →
    ∀ {n : ℕ} (w : Fin n → Bool), BispecialFactor (lowerMechanicalWord alpha alpha) w →
    ∃ r s : List Bool,
      0 < r.length ∧ 0 < s.length ∧
      (r.count true * s.count false + 1 = s.count true * r.count false ∨
        s.count true * r.count false + 1 = r.count true * s.count false) ∧
      (∀ b, r.count b + s.count b = (List.ofFn w).count b + 1) ∧
      ∀ i j, AdjacentOccurrences (lowerMechanicalWord alpha alpha) w i j →
        List.ofFn (wordFactor (lowerMechanicalWord alpha alpha) (j - i) i) = r ∨
        List.ofFn (wordFactor (R.readout () alpha alpha) (j - i) i) = s

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨@mechanical_bispecial_returns, bad, ?_⟩
    intro h
    let alpha := Real.sqrt 2 - 1
    let u := lowerMechanicalWord alpha alpha
    let w : Fin 1 → Bool := fun _ => false
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have hlo : 2 / 5 < alpha := by dsimp [alpha]; nlinarith
    have hhi : alpha < 3 / 7 := by dsimp [alpha]; nlinarith
    have ha0 : 0 < alpha := by linarith
    have ha1 : alpha < 1 := by linarith
    have hai : Irrational alpha := by
      simpa [alpha] using irrational_sqrt_two.sub_ratCast 1
    have floors : ∀ k : ℕ, k ≤ 7 →
        ⌊(k : ℝ) * alpha⌋ = (if k ≤ 2 then 0 else if k ≤ 4 then 1 else 2 : ℤ) := by
      intro k hk
      interval_cases k <;> norm_num [Int.floor_eq_iff] <;> constructor <;> nlinarith
    have letters : ∀ i : ℕ, i ≤ 5 → u i = (i = 1 || i = 3) := by
      intro i hi
      have f1 := floors (i + 1) (by omega)
      have f2 := floors (i + 2) (by omega)
      have hid : lowerMechanicalLetter alpha alpha i =
          (if i + 2 ≤ 2 then 0 else if i + 2 ≤ 4 then 1 else 2 : ℤ) -
            (if i + 1 ≤ 2 then 0 else if i + 1 ≤ 4 then 1 else 2 : ℤ) := by
        unfold lowerMechanicalLetter
        rw [show alpha + ((i + 1 : ℕ) : ℝ) * alpha = ((i + 2 : ℕ) : ℝ) * alpha by
          push_cast; ring,
        show alpha + (i : ℝ) * alpha = ((i + 1 : ℕ) : ℝ) * alpha by
          push_cast; ring, f1, f2]
      simp only [u, lowerMechanicalWord, hid]
      interval_cases i <;> norm_num
    have hw : BispecialFactor u w := by
      refine ⟨⟨2, 5, by omega, by omega, ?_, ?_, ?_⟩, ⟨0, 4, ?_, ?_, ?_⟩⟩
      all_goals first
        | (funext k; fin_cases k; norm_num [wordFactor, w, letters])
        | norm_num [letters]
    have hadj : AdjacentOccurrences u w 4 5 := by
      refine ⟨by omega, ?_, ?_, ?_⟩
      · funext k
        fin_cases k
        norm_num [wordFactor, w, letters]
      · funext k
        fin_cases k
        norm_num [wordFactor, w, letters]
      · intro k hk hk'
        omega
    have hadj2 : AdjacentOccurrences u w 0 2 := by
      refine ⟨by omega, ?_, ?_, ?_⟩
      · funext k
        fin_cases k
        norm_num [wordFactor, w, letters]
      · funext k
        fin_cases k
        norm_num [wordFactor, w, letters]
      · intro k hk hk' he
        have he1 : k = 1 := by omega
        subst k
        have hh := congrFun he (0 : Fin 1)
        norm_num [wordFactor, w, letters] at hh
    obtain ⟨r, s, _, _, hd, hc, ht⟩ := h ha0 ha1 hai w hw
    have hf := hc false
    have htrue := hc true
    have hret := ht 4 5 hadj
    have hret2 := ht 0 2 hadj2
    norm_num [w, List.ofFn_succ, List.ofFn_zero] at hf htrue
    change List.ofFn (wordFactor u (5 - 4) 4) = r ∨ _ at hret
    change List.ofFn (wordFactor u (2 - 0) 0) = r ∨ _ at hret2
    norm_num [bad, realize, wordFactor, List.ofFn_succ, List.ofFn_zero, letters]
      at hret hret2
    rcases hret with he | he
    · subst r
      rcases hret2 with he2 | he2
      · simp at he2
      · subst s
        norm_num at htrue
    · subst s
      norm_num at hf hd
      omega
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · intro h
        let alpha := Real.sqrt 2 - 1
        let u := lowerMechanicalWord alpha alpha
        let w : Fin 1 → Bool := fun _ => false
        have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have hs0 := Real.sqrt_nonneg (2 : ℝ)
        have hlo : 2 / 5 < alpha := by dsimp [alpha]; nlinarith
        have hhi : alpha < 3 / 7 := by dsimp [alpha]; nlinarith
        have ha0 : 0 < alpha := by linarith
        have ha1 : alpha < 1 := by linarith
        have hai : Irrational alpha := by
          simpa [alpha] using irrational_sqrt_two.sub_ratCast 1
        have floors : ∀ k : ℕ, k ≤ 7 →
            ⌊(k : ℝ) * alpha⌋ = (if k ≤ 2 then 0 else if k ≤ 4 then 1 else 2 : ℤ) := by
          intro k hk
          interval_cases k <;> norm_num [Int.floor_eq_iff] <;> constructor <;> nlinarith
        have letters : ∀ i : ℕ, i ≤ 5 → u i = (i = 1 || i = 3) := by
          intro i hi
          have f1 := floors (i + 1) (by omega)
          have f2 := floors (i + 2) (by omega)
          have hid : lowerMechanicalLetter alpha alpha i =
              (if i + 2 ≤ 2 then 0 else if i + 2 ≤ 4 then 1 else 2 : ℤ) -
                (if i + 1 ≤ 2 then 0 else if i + 1 ≤ 4 then 1 else 2 : ℤ) := by
            unfold lowerMechanicalLetter
            rw [show alpha + ((i + 1 : ℕ) : ℝ) * alpha = ((i + 2 : ℕ) : ℝ) * alpha by
              push_cast; ring,
            show alpha + (i : ℝ) * alpha = ((i + 1 : ℕ) : ℝ) * alpha by
              push_cast; ring, f1, f2]
          simp only [u, lowerMechanicalWord, hid]
          interval_cases i <;> norm_num
        have hw : BispecialFactor u w := by
          refine ⟨⟨2, 5, by omega, by omega, ?_, ?_, ?_⟩, ⟨0, 4, ?_, ?_, ?_⟩⟩
          all_goals first
            | (funext k; fin_cases k; norm_num [wordFactor, w, letters])
            | norm_num [letters]
        have hadj : AdjacentOccurrences u w 4 5 := by
          refine ⟨by omega, ?_, ?_, ?_⟩
          · funext k
            fin_cases k
            norm_num [wordFactor, w, letters]
          · funext k
            fin_cases k
            norm_num [wordFactor, w, letters]
          · intro k hk hk'
            omega
        have hadj2 : AdjacentOccurrences u w 0 2 := by
          refine ⟨by omega, ?_, ?_, ?_⟩
          · funext k
            fin_cases k
            norm_num [wordFactor, w, letters]
          · funext k
            fin_cases k
            norm_num [wordFactor, w, letters]
          · intro k hk hk' he
            have he1 : k = 1 := by omega
            subst k
            have hh := congrFun he (0 : Fin 1)
            norm_num [wordFactor, w, letters] at hh
        obtain ⟨r, s, _, _, hd, hc, ht⟩ := h ha0 ha1 hai w hw
        have hf := hc false
        have htrue := hc true
        have hret := ht 4 5 hadj
        have hret2 := ht 0 2 hadj2
        norm_num [w, List.ofFn_succ, List.ofFn_zero] at hf htrue
        change List.ofFn (wordFactor u (5 - 4) 4) = r ∨ _ at hret
        change List.ofFn (wordFactor u (2 - 0) 0) = r ∨ _ at hret2
        norm_num [bad, realize, wordFactor, List.ofFn_succ, List.ofFn_zero, letters]
          at hret hret2
        rcases hret with he | he
        · subst r
          rcases hret2 with he2 | he2
          · simp at he2
          · subst s
            norm_num at htrue
        · subst s
          norm_num at hf hd
          omega
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1 / 3, 1 / 3, 0, ?_⟩
    intro he
    have hh := congrFun he 1
    norm_num [actual, realize, lowerMechanicalWord, lowerMechanicalLetter] at hh

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdReturns
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body",
      "arg", "body", "arg", "arg", "arg", "arg", "body", "body", "body", "arg", "fn",
      "arg", "arg", "fn", "fn", "arg", "fn"]
    functionOperand := true }] }

register_information_theorem mechanical_bispecial_returns in arena
  readout via
    (realize signature (fun _ alpha rho => lowerMechanicalWord alpha rho) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdReturns
