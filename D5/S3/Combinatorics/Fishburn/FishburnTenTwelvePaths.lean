/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTwelvePaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTwelvePaths
   mirror-E: none(waiver:positive-insertion-path-realization)
   anchors: []
   utility: none
   digest: Positive insertion histories are reconstructed uniquely from their state transitions. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTwelveSuccession

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTwelvePaths

open D5.S3.Combinatorics FishburnDefs FishburnTenTwelveSuccession

def PositiveHistory : ℕ → List ℕ → ℕ → Type
  | _, _, 0 => PUnit
  | n, p, steps + 1 =>
    (site : {site : ℕ // 0 < site ∧ site ≤ p.length ∧
      p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]}) ×
      PositiveHistory (n + 1) (p.insertIdx site.val (n + 1)) steps

def Walk : Label → ℕ → Type
  | _, 0 => PUnit
  | .A, steps + 1 => Walk .C steps
  | .B, steps + 1 => Walk .B steps
  | .C, steps + 1 => Walk .C steps ⊕ Walk .D steps
  | .D, steps + 1 => Walk .D steps ⊕ Walk .B steps

theorem positive_history_walk (steps n : ℕ) (p : List ℕ) (hpositive : 1 ≤ n)
    (hparent : p ∈ avoiders n [[1, 2, 4, 3], [3, 1, 2, 4]])
    (first extra : ℕ) (hfirst : 0 < first) (hfe : first ≤ extra)
    (hextent : extra ≤ p.length) (hone : p.getD (first - 1) 0 = 1)
    (hcuts : ∀ gap, gap ≤ p.length →
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
        gap = 0 ∨ gap = first ∨ first < extra ∧ gap = extra))
    (hmaximum : first < extra → ∃ maximum, first ≤ maximum ∧ maximum < extra ∧
      p.getD maximum 0 = n) :
    Nonempty (PositiveHistory n p steps ≃ Walk (label n p first extra) steps) := by
  classical
  induction steps generalizing n p first extra with
  | zero => exact ⟨Equiv.refl PUnit⟩
  | succ steps ih =>
    have hsite : first ≤ p.length := by omega
    have hactive := (hcuts first hsite).mpr (Or.inr (Or.inl rfl))
    obtain ⟨_, hfirstchild, hextrachild⟩ :=
      full_succession n p hpositive hparent first extra hfirst hfe hextent hone
        hcuts hmaximum
    obtain ⟨nextfirst, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmax, hnfirst,
      hnlabel⟩ := hfirstchild
    let firstCode := Classical.choice (ih (n + 1) (p.insertIdx first (n + 1))
      (by omega) hactive nextfirst nextextra hnf hnfe hnb hnone hncut hnmax)
    have hfirstCode : Nonempty (PositiveHistory (n + 1) (p.insertIdx first (n + 1))
        steps ≃ Walk
          (if label n p first extra = .A ∨ label n p first extra = .C then .C else .B)
          steps) := by
      rw [← hnlabel]
      exact ⟨firstCode⟩
    have hextraCode (hlt : first < extra) :
        Nonempty (PositiveHistory (n + 1) (p.insertIdx extra (n + 1)) steps ≃
          Walk .D steps) := by
      have hextraactive := (hcuts extra hextent).mpr (Or.inr (Or.inr ⟨hlt, rfl⟩))
      obtain ⟨nextfirst, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmax, _, _,
        hnlabel⟩ := hextrachild hlt
      rw [← hnlabel]
      exact ih (n + 1) (p.insertIdx extra (n + 1)) (by omega) hextraactive
        nextfirst nextextra hnf hnfe hnb hnone hncut hnmax
    let firstSite : {site : ℕ // 0 < site ∧ site ≤ p.length ∧
        p.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]} :=
      ⟨first, hfirst, hsite, hactive⟩
    have hsingle (heq : extra = first) :
        Nonempty (PositiveHistory n p (steps + 1) ≃
          PositiveHistory (n + 1) (p.insertIdx first (n + 1)) steps) := by
      have hsiteeq (site : ℕ) (hp : 0 < site ∧ site ≤ p.length ∧
          p.insertIdx site (n + 1) ∈
            avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]) : site = first := by
        have hc := (hcuts site hp.2.1).mp hp.2.2
        rcases hc with hz | hf | ⟨hlt, _⟩ <;> omega
      refine ⟨{
        toFun := fun history => by
          rcases history with ⟨⟨site, hp⟩, tail⟩
          have he := hsiteeq site hp
          subst site
          exact tail
        invFun := fun tail => ⟨firstSite, tail⟩
        left_inv := ?_
        right_inv := ?_ }⟩
      · rintro ⟨⟨site, hp⟩, tail⟩
        have he := hsiteeq site hp
        subst site
        rfl
      · intro tail
        rfl
    have hdouble (hlt : first < extra) :
        Nonempty (PositiveHistory n p (steps + 1) ≃
          (PositiveHistory (n + 1) (p.insertIdx first (n + 1)) steps ⊕
            PositiveHistory (n + 1) (p.insertIdx extra (n + 1)) steps)) := by
      let extraSite : {site : ℕ // 0 < site ∧ site ≤ p.length ∧
          p.insertIdx site (n + 1) ∈
            avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]} :=
        ⟨extra, by omega, hextent,
          (hcuts extra hextent).mpr (Or.inr (Or.inr ⟨hlt, rfl⟩))⟩
      have hsiteeq (site : ℕ) (hp : 0 < site ∧ site ≤ p.length ∧
          p.insertIdx site (n + 1) ∈
            avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]])
          (hne : site ≠ first) : site = extra := by
        have hc := (hcuts site hp.2.1).mp hp.2.2
        rcases hc with hz | hf | ⟨_, he⟩
        · omega
        · exact False.elim (hne hf)
        · exact he
      refine ⟨{
        toFun := fun history => by
          rcases history with ⟨⟨site, hp⟩, tail⟩
          by_cases he : site = first
          · subst site
            exact Sum.inl tail
          · have hextra := hsiteeq site hp he
            subst site
            exact Sum.inr tail
        invFun := fun code => match code with
          | Sum.inl tail => ⟨firstSite, tail⟩
          | Sum.inr tail => ⟨extraSite, tail⟩
        left_inv := ?_
        right_inv := ?_ }⟩
      · rintro ⟨⟨site, hp⟩, tail⟩
        by_cases he : site = first
        · subst site
          simp only [dite_true]
          rfl
        · have hextra := hsiteeq site hp he
          subst site
          simp only [dif_neg (by omega : extra ≠ first)]
          rfl
      · intro code
        cases code with
        | inl tail => simp only [firstSite, dite_true]
        | inr tail => simp only [extraSite, dif_neg (by omega : extra ≠ first)]
    have htwo (hlabel : label n p first extra = .A ∨ label n p first extra = .B) :
        extra = first := by
      by_contra hne
      have hlt : first < extra := by omega
      rcases hlabel with hl | hl
      all_goals
        unfold label at hl
        rw [if_pos hlt] at hl
        split_ifs at hl
    have hthree (hlabel : label n p first extra = .C ∨ label n p first extra = .D) :
        first < extra := by
      by_contra hnot
      rcases hlabel with hl | hl
      all_goals
        unfold label at hl
        rw [if_neg hnot] at hl
        split_ifs at hl
    generalize hl : label n p first extra = current at hfirstCode ⊢
    cases current with
    | A =>
      have heq := htwo (Or.inl hl)
      have hc : (if Label.A = .A ∨ Label.A = .C then Label.C else .B) = .C := by decide
      rw [hc] at hfirstCode
      exact ⟨(Classical.choice (hsingle heq)).trans (Classical.choice hfirstCode)⟩
    | B =>
      have heq := htwo (Or.inr hl)
      have hc : (if Label.B = .A ∨ Label.B = .C then Label.C else .B) = .B := by decide
      rw [hc] at hfirstCode
      exact ⟨(Classical.choice (hsingle heq)).trans (Classical.choice hfirstCode)⟩
    | C =>
      have hlt := hthree (Or.inl hl)
      have hc : (if Label.C = .A ∨ Label.C = .C then Label.C else .B) = .C := by decide
      rw [hc] at hfirstCode
      exact ⟨(Classical.choice (hdouble hlt)).trans
        (Equiv.sumCongr (Classical.choice hfirstCode) (Classical.choice (hextraCode hlt)))⟩
    | D =>
      have hlt := hthree (Or.inr hl)
      have hc : (if Label.D = .A ∨ Label.D = .C then Label.C else .B) = .B := by decide
      rw [hc] at hfirstCode
      exact ⟨((Classical.choice (hdouble hlt)).trans
        (Equiv.sumCongr (Classical.choice hfirstCode)
          (Classical.choice (hextraCode hlt)))).trans (Equiv.sumComm _ _)⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTwelvePaths
