/- GID: D5/S3/Combinatorics/ErdosGrahamOrderGadget
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ErdosGrahamOrderGadget
   mirror-E: none(waiver:direct-Lean-proof-of-order-gadget-impossibility)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Every Erdos-Graham order gadget at scale at least sixteen is impossible. -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ErdosGrahamOrderGadget

/-- The dyadic block `(M, 2M]`. -/
def block (M : ℕ) : Finset ℕ := Finset.Icc (M + 1) (2 * M)

/-- No three-term arithmetic progression in the block is monotone in rank. -/
def APFree (M : ℕ) (rank : ℕ → ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ block M → b ∈ block M → c ∈ block M →
    a < b → b < c → a + c = 2 * b →
    ¬(rank a < rank b ∧ rank b < rank c) ∧
      ¬(rank c < rank b ∧ rank b < rank a)

/-- The attacks from `15` and `16` force every in-block guard before its bottom. -/
def Guards (M : ℕ) (rank : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, (x = 15 ∨ x = 16) → ∀ j : ℕ, 1 ≤ j → j ≤ x / 2 →
    rank (2 * M + 2 * j - x) < rank (M + j)

/-- Feasibility of the order gadget at scale `M`. -/
def OrderGadget (M : ℕ) : Prop :=
  ∃ rank : ℕ → ℕ,
    Set.InjOn rank (block M) ∧ APFree M rank ∧ Guards M rank

private lemma ladder_phase_of_first_edge {M : ℕ} {rank : ℕ → ℕ}
    (hinj : Set.InjOn rank (block M)) (hfree : APFree M rank)
    {s d r p : ℕ} (hd : 0 < d) (_hr : 1 ≤ r)
    (hmem : ∀ i : ℕ, i ≤ r → s + d * i ∈ block M) (hp : p < 2)
    (hfirst :
      (p = 0 ∧ rank (s + d * 0) < rank (s + d * 1)) ∨
        (p = 1 ∧ rank (s + d * 1) < rank (s + d * 0))) :
    ∀ i : ℕ, i ≤ r → i % 2 = p →
      (0 < i → rank (s + d * i) < rank (s + d * (i - 1))) ∧
        (i < r → rank (s + d * i) < rank (s + d * (i + 1))) := by
  have midpoint_rule_r1 : ∀ {a b c : ℕ}, a ∈ block M → b ∈ block M → c ∈ block M →
      a < b → b < c → a + c = 2 * b → rank a < rank b → rank c < rank b := by
    intro a b c ha hb hc hab hbc hap hr
    have hne : rank c ≠ rank b := by
      intro h
      have : c = b := hinj hc hb h
      omega
    have hnot := (hfree a b c ha hb hc hab hbc hap).1
    omega
  have midpoint_rule_r4 : ∀ {a b c : ℕ}, a ∈ block M → b ∈ block M → c ∈ block M →
      a < b → b < c → a + c = 2 * b → rank b < rank a → rank b < rank c := by
    intro a b c ha hb hc hab hbc hap hr
    have hne : rank c ≠ rank b := by
      intro h
      have : c = b := hinj hc hb h
      omega
    have hnot := (hfree a b c ha hb hc hab hbc hap).2
    omega
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hir hip
      by_cases hi0 : i = 0
      · subst i
        constructor
        · omega
        · intro _
          rcases hfirst with hfirst | hfirst
          · simpa using hfirst.2
          · omega
      by_cases hi1 : i = 1
      · subst i
        have hp1 : p = 1 := by omega
        have hleft : rank (s + d * 1) < rank (s + d * 0) := by
          rcases hfirst with hfirst | hfirst
          · omega
          · exact hfirst.2
        constructor
        · intro _
          exact hleft
        · intro h1r
          have h0 : s + d * 0 < s + d * 1 := by nlinarith
          have h1 : s + d * 1 < s + d * 2 := by nlinarith
          have hap : (s + d * 0) + (s + d * 2) = 2 * (s + d * 1) := by ring
          exact midpoint_rule_r4 (hmem 0 (by omega)) (hmem 1 (by omega))
            (hmem 2 (by omega)) h0 h1 hap hleft
      have hi2 : 2 ≤ i := by omega
      have hidx : i = (i - 2) + 2 := by omega
      have hpar : (i - 2) % 2 = p := by omega
      have hprev := ih (i - 2) (by omega) (by omega) hpar
      have hprev_right :
          rank (s + d * (i - 2)) < rank (s + d * (i - 2 + 1)) :=
        hprev.2 (by omega)
      have him1 : i - 2 + 1 = i - 1 := by omega
      have hmid : s + d * (i - 2 + 1) = s + d * (i - 2) + d := by ring
      have hright : s + d * i = s + d * (i - 2) + 2 * d := by
        calc
          s + d * i = s + d * ((i - 2) + 2) := congrArg (fun n => s + d * n) hidx
          _ = s + d * (i - 2) + 2 * d := by ring
      have ha_lt : s + d * (i - 2) < s + d * (i - 2 + 1) := by nlinarith
      have hb_lt : s + d * (i - 2 + 1) < s + d * i := by
        rw [hmid, hright]
        omega
      have hap :
          (s + d * (i - 2)) + (s + d * i) = 2 * (s + d * (i - 2 + 1)) := by
        rw [hmid, hright]
        ring
      have hleft_raw : rank (s + d * i) < rank (s + d * (i - 2 + 1)) :=
        midpoint_rule_r1 (hmem (i - 2) (by omega))
          (hmem (i - 2 + 1) (by omega)) (hmem i hir) ha_lt hb_lt hap hprev_right
      have hleft : rank (s + d * i) < rank (s + d * (i - 1)) := by
        simpa only [him1] using hleft_raw
      constructor
      · exact fun _ => hleft
      · intro hir'
        have hi : i = (i - 1) + 1 := by omega
        have hcenter : s + d * i = s + d * (i - 1) + d := by
          calc
            s + d * i = s + d * ((i - 1) + 1) := congrArg (fun n => s + d * n) hi
            _ = s + d * (i - 1) + d := by ring
        have hnext : s + d * (i + 1) = s + d * i + d := by ring
        have ha_lt' : s + d * (i - 1) < s + d * i := by
          rw [hcenter]
          omega
        have hb_lt' : s + d * i < s + d * (i + 1) := by
          rw [hnext]
          omega
        have hap' :
            (s + d * (i - 1)) + (s + d * (i + 1)) = 2 * (s + d * i) := by
          rw [hnext, hcenter]
          ring
        exact midpoint_rule_r4 (hmem (i - 1) (by omega)) (hmem i hir)
          (hmem (i + 1) (by omega)) ha_lt' hb_lt' hap' hleft

private lemma flood_outward {M : ℕ} {rank : ℕ → ℕ}
    (hinj : Set.InjOn rank (block M)) (hfree : APFree M rank)
    {s g r c q p k : ℕ} (hg : g = 2 ∨ g = 4)
    (hmem : ∀ i : ℕ, i ≤ r → s + g * i ∈ block M) (hc : c ∈ block M)
    (hcenter : 2 * c = 2 * s + g * q) (hq : q % 2 = 1) (hp : p < 2)
    (hphase : ∀ i : ℕ, i ≤ r → i % 2 = p →
      (0 < i → rank (s + g * i) < rank (s + g * (i - 1))) ∧
        (i < r → rank (s + g * i) < rank (s + g * (i + 1))))
    (hkr : k ≤ r) (hkq : k ≤ q) (hkmir : q - k ≤ r)
    (hseed : rank c < rank (s + g * k)) :
    ∀ i : ℕ, i ≤ r → i ≤ q → q - i ≤ r → rank c < rank (s + g * i) := by
  have midpoint_rule_r2 : ∀ {a b c : ℕ}, a ∈ block M → b ∈ block M → c ∈ block M →
      a < b → b < c → a + c = 2 * b → rank b < rank c → rank b < rank a := by
    intro a b c ha hb hc hab hbc hap hr
    have hne : rank a ≠ rank b := by
      intro h
      have : a = b := hinj ha hb h
      omega
    have hnot := (hfree a b c ha hb hc hab hbc hap).1
    omega
  have midpoint_rule_r4 : ∀ {a b c : ℕ}, a ∈ block M → b ∈ block M → c ∈ block M →
      a < b → b < c → a + c = 2 * b → rank b < rank a → rank b < rank c := by
    intro a b c ha hb hc hab hbc hap hr
    have hne : rank c ≠ rank b := by
      intro h
      have : c = b := hinj hc hb h
      omega
    have hnot := (hfree a b c ha hb hc hab hbc hap).2
    omega
  have mirror_outward : ∀ {i : ℕ}, i ≤ r → i ≤ q → q - i ≤ r →
      rank c < rank (s + g * i) → rank c < rank (s + g * (q - i)) := by
    intro i hi hiq hmir hrel
    have hiadd : i + (q - i) = q := by omega
    have hpair : (s + g * i) + (s + g * (q - i)) = 2 * c := by
      calc
        (s + g * i) + (s + g * (q - i)) = 2 * s + g * (i + (q - i)) := by ring
        _ = 2 * s + g * q := by rw [hiadd]
        _ = 2 * c := hcenter.symm
    have hne : s + g * i ≠ c := by
      intro heq
      rcases hg with rfl | rfl <;> omega
    by_cases hil : s + g * i < c
    · have hcr : c < s + g * (q - i) := by omega
      exact midpoint_rule_r4 (hmem i hi) hc (hmem (q - i) hmir) hil hcr hpair hrel
    · have hcl : c < s + g * i := by omega
      have hrc : s + g * (q - i) < c := by omega
      exact midpoint_rule_r2 (hmem (q - i) hmir) hc (hmem i hi) hrc hcl (by omega) hrel
  have stepDown : ∀ j : ℕ, 0 < j → j ≤ r → j ≤ q → q - j ≤ r →
      q - (j - 1) ≤ r → rank c < rank (s + g * j) →
      rank c < rank (s + g * (j - 1)) := by
    intro j hjpos hjr hjq hjmir htargetMir hrel
    have hrelMir := mirror_outward hjr hjq hjmir hrel
    by_cases hjp : j % 2 = p
    · exact lt_trans hrel ((hphase j hjr hjp).1 hjpos)
    · have hmpar : (q - j) % 2 = p := by omega
      have hmright : q - j < r := by omega
      have hedge := (hphase (q - j) hjmir hmpar).2 hmright
      have hindex : q - (j - 1) = q - j + 1 := by omega
      have hfar : rank c < rank (s + g * (q - (j - 1))) := by
        rw [hindex]
        exact lt_trans hrelMir hedge
      have hback := mirror_outward htargetMir (by omega) (by omega) hfar
      have hbackIndex : q - (q - (j - 1)) = j - 1 := by omega
      simpa only [hbackIndex] using hback
  have stepUp : ∀ j : ℕ, j < r → j < q → q - j ≤ r →
      q - (j + 1) ≤ r → rank c < rank (s + g * j) →
      rank c < rank (s + g * (j + 1)) := by
    intro j hjr hjq hjmir htargetMir hrel
    have hrelMir := mirror_outward (by omega) (by omega) hjmir hrel
    by_cases hjp : j % 2 = p
    · exact lt_trans hrel ((hphase j (by omega) hjp).2 hjr)
    · have hmpar : (q - j) % 2 = p := by omega
      have hmpos : 0 < q - j := by omega
      have hedge := (hphase (q - j) hjmir hmpar).1 hmpos
      have hindex : q - (j + 1) = q - j - 1 := by omega
      have hfar : rank c < rank (s + g * (q - (j + 1))) := by
        rw [hindex]
        exact lt_trans hrelMir hedge
      have hback := mirror_outward htargetMir (by omega) (by omega) hfar
      have hbackIndex : q - (q - (j + 1)) = j + 1 := by omega
      simpa only [hbackIndex] using hback
  have down : ∀ n : ℕ, n ≤ k → k - n ≤ r → k - n ≤ q → q - (k - n) ≤ r →
      rank c < rank (s + g * (k - n)) := by
    intro n hn
    induction n with
    | zero =>
        intro _ _ _
        simpa using hseed
    | succ n ih =>
        intro hnr hnq hnmir
        have hnle : n ≤ k := by omega
        have hprevR : k - n ≤ r := by omega
        have hprevQ : k - n ≤ q := by omega
        have hprevMir : q - (k - n) ≤ r := by omega
        have hprev := ih hnle hprevR hprevQ hprevMir
        have hstep := stepDown (k - n) (by omega) hprevR hprevQ hprevMir
          (by omega) hprev
        have heq : k - n - 1 = k - (n + 1) := by omega
        simpa only [heq] using hstep
  have up : ∀ n : ℕ, k + n ≤ r → k + n ≤ q → q - (k + n) ≤ r →
      rank c < rank (s + g * (k + n)) := by
    intro n
    induction n with
    | zero =>
        intro _ _ _
        simpa using hseed
    | succ n ih =>
        intro hnr hnq hnmir
        have hprevR : k + n ≤ r := by omega
        have hprevQ : k + n ≤ q := by omega
        have hprevMir : q - (k + n) ≤ r := by omega
        have hprev := ih hprevR hprevQ hprevMir
        exact stepUp (k + n) (by omega) (by omega) hprevMir (by omega) hprev
  intro i hir hiq himir
  by_cases hik : i ≤ k
  · have h := down (k - i) (by omega) (by omega) (by omega) (by omega)
    have heq : k - (k - i) = i := by omega
    simpa only [heq] using h
  · have h := up (i - k) (by omega) (by omega) (by omega)
    have heq : k + (i - k) = i := by omega
    simpa only [heq] using h

private theorem four_flood_cycle {M : ℕ} {rank : ℕ → ℕ}
    (hinj : Set.InjOn rank (block M)) (hfree : APFree M rank)
    {c d tc bc td bd s2 r2 sc rc sd rd : ℕ}
    (hd : d = c + 2)
    (hblocks :
      M + 1 ≤ c ∧ c ≤ 2 * M ∧ M + 1 ≤ d ∧ d ≤ 2 * M ∧
      1 ≤ r2 ∧ M + 1 ≤ s2 ∧ s2 + 2 * r2 ≤ 2 * M ∧
      1 ≤ rc ∧ M + 1 ≤ sc ∧ sc + 4 * rc ≤ 2 * M ∧
      1 ≤ rd ∧ M + 1 ≤ sd ∧ sd + 4 * rd ≤ 2 * M)
    (hc2 :
      2 * c = 2 * s2 + 2 * (c - s2) ∧ (c - s2) % 2 = 1 ∧
      (c - 1 - s2) / 2 ≤ r2 ∧ (c - 1 - s2) / 2 ≤ c - s2 ∧
      c - s2 - (c - 1 - s2) / 2 ≤ r2 ∧
      (tc - s2) / 2 ≤ r2 ∧ (tc - s2) / 2 ≤ c - s2 ∧
      c - s2 - (tc - s2) / 2 ≤ r2 ∧
      s2 + 2 * ((c - 1 - s2) / 2) = c - 1 ∧
      s2 + 2 * ((tc - s2) / 2) = tc)
    (hd2 :
      2 * d = 2 * s2 + 2 * (d - s2) ∧ (d - s2) % 2 = 1 ∧
      (d - 1 - s2) / 2 ≤ r2 ∧ (d - 1 - s2) / 2 ≤ d - s2 ∧
      d - s2 - (d - 1 - s2) / 2 ≤ r2 ∧
      (td - s2) / 2 ≤ r2 ∧ (td - s2) / 2 ≤ d - s2 ∧
      d - s2 - (td - s2) / 2 ≤ r2 ∧
      s2 + 2 * ((d - 1 - s2) / 2) = d - 1 ∧
      s2 + 2 * ((td - s2) / 2) = td)
    (hc4 :
      2 * c = 2 * sc + 4 * ((c - sc) / 2) ∧ (c - sc) / 2 % 2 = 1 ∧
      (c - sc) / 2 ≤ rc ∧ (d - sc) / 4 ≤ rc ∧
      (d - sc) / 4 ≤ (c - sc) / 2 ∧
      (c - sc) / 2 - (d - sc) / 4 ≤ rc ∧ sc = bc ∧
      sc + 4 * ((d - sc) / 4) = d)
    (hd4 :
      2 * d = 2 * sd + 4 * ((d - sd) / 2) ∧ (d - sd) / 2 % 2 = 1 ∧
      (d - sd) / 2 ≤ rd ∧ (c - sd) / 4 ≤ rd ∧
      (c - sd) / 4 ≤ (d - sd) / 2 ∧
      (d - sd) / 2 - (c - sd) / 4 ≤ rd ∧ sd = bd ∧
      sd + 4 * ((c - sd) / 4) = c)
    (hcPrev : rank c < rank (c - 1)) (hdPrev : rank d < rank (d - 1))
    (hcGuard : rank tc < rank bc) (hdGuard : rank td < rank bd) : False := by
  rcases hblocks with
    ⟨hcL, hcU, hdL, hdU, hr2, hs2L, hs2U, hrc, hscL, hscU, hrd, hsdL, hsdU⟩
  have hcMem : c ∈ block M := by simp only [block, Finset.mem_Icc]; omega
  have hdMem : d ∈ block M := by simp only [block, Finset.mem_Icc]; omega
  have hmem2 : ∀ i : ℕ, i ≤ r2 → s2 + 2 * i ∈ block M := by
    intro i hi
    simp only [block, Finset.mem_Icc]
    omega
  have hmemc : ∀ i : ℕ, i ≤ rc → sc + 4 * i ∈ block M := by
    intro i hi
    simp only [block, Finset.mem_Icc]
    omega
  have hmemd : ∀ i : ℕ, i ≤ rd → sd + 4 * i ∈ block M := by
    intro i hi
    simp only [block, Finset.mem_Icc]
    omega
  have phase : ∀ {s g r : ℕ}, 0 < g → 1 ≤ r →
      (∀ i : ℕ, i ≤ r → s + g * i ∈ block M) →
      ∃ p : ℕ, p < 2 ∧ ∀ i : ℕ, i ≤ r → i % 2 = p →
        (0 < i → rank (s + g * i) < rank (s + g * (i - 1))) ∧
          (i < r → rank (s + g * i) < rank (s + g * (i + 1))) := by
    intro s g r hg hr hmem
    have hne : rank (s + g * 0) ≠ rank (s + g * 1) := by
      intro h
      have heq := hinj (hmem 0 (by omega)) (hmem 1 (by omega)) h
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨0, by omega, ladder_phase_of_first_edge hinj hfree hg hr hmem
        (by omega) (Or.inl ⟨rfl, hlt⟩)⟩
    · exact ⟨1, by omega, ladder_phase_of_first_edge hinj hfree hg hr hmem
        (by omega) (Or.inr ⟨rfl, hgt⟩)⟩
  rcases phase (s := s2) (g := 2) (r := r2) (by omega) hr2 hmem2 with
    ⟨p2, hp2, hphase2⟩
  rcases phase (s := sc) (g := 4) (r := rc) (by omega) hrc hmemc with
    ⟨pc, hpc, hphasec⟩
  rcases phase (s := sd) (g := 4) (r := rd) (by omega) hrd hmemd with
    ⟨pd, hpd, hphased⟩
  rcases hc2 with ⟨hcCenter, hcOdd, hkcR, hkcQ, hkcMir, hicR, hicQ, hicMir,
    hkcEq, hicEq⟩
  have hcTopRaw := flood_outward hinj hfree (s := s2) (g := 2) (r := r2)
    (c := c) (q := c - s2) (p := p2) (k := (c - 1 - s2) / 2) (Or.inl rfl)
    hmem2 hcMem hcCenter hcOdd hp2 hphase2 hkcR hkcQ hkcMir
    (by rw [hkcEq]; exact hcPrev) ((tc - s2) / 2) hicR hicQ hicMir
  have hcTop : rank c < rank tc := by rwa [hicEq] at hcTopRaw
  have hcBottom : rank c < rank bc := lt_trans hcTop hcGuard
  rcases hc4 with ⟨hc4Center, hc4Odd, hqcR, hciR, hciQ, hciMir, hscEq, hciEq⟩
  have hcDRaw := flood_outward hinj hfree (s := sc) (g := 4) (r := rc)
    (c := c) (q := (c - sc) / 2) (p := pc) (k := 0) (Or.inr rfl)
    hmemc hcMem hc4Center hc4Odd hpc hphasec (by omega) (by omega) hqcR
    (by simpa only [Nat.mul_zero, Nat.add_zero, hscEq] using hcBottom)
    ((d - sc) / 4) hciR hciQ hciMir
  have hcD : rank c < rank d := by rwa [hciEq] at hcDRaw
  rcases hd2 with ⟨hdCenter, hdOdd, hkdR, hkdQ, hkdMir, hidR, hidQ, hidMir,
    hkdEq, hidEq⟩
  have hdTopRaw := flood_outward hinj hfree (s := s2) (g := 2) (r := r2)
    (c := d) (q := d - s2) (p := p2) (k := (d - 1 - s2) / 2) (Or.inl rfl)
    hmem2 hdMem hdCenter hdOdd hp2 hphase2 hkdR hkdQ hkdMir
    (by rw [hkdEq]; exact hdPrev) ((td - s2) / 2) hidR hidQ hidMir
  have hdTop : rank d < rank td := by rwa [hidEq] at hdTopRaw
  have hdBottom : rank d < rank bd := lt_trans hdTop hdGuard
  rcases hd4 with ⟨hd4Center, hd4Odd, hqdR, hdiR, hdiQ, hdiMir, hsdEq, hdiEq⟩
  have hdCRaw := flood_outward hinj hfree (s := sd) (g := 4) (r := rd)
    (c := d) (q := (d - sd) / 2) (p := pd) (k := 0) (Or.inr rfl)
    hmemd hdMem hd4Center hd4Odd hpd hphased (by omega) (by omega) hqdR
    (by simpa only [Nat.mul_zero, Nat.add_zero, hsdEq] using hdBottom)
    ((c - sd) / 4) hdiR hdiQ hdiMir
  have hdC : rank d < rank c := by rwa [hdiEq] at hdCRaw
  exact (Nat.lt_asymm hcD hdC)

private theorem even_four_guards_impossible {M : ℕ} {rank : ℕ → ℕ}
    (hM : 16 ≤ M) (hEven : Even M) (hinj : Set.InjOn rank (block M))
    (hfree : APFree M rank) :
    ¬(rank (2 * M - 11) < rank (M + 2) ∧
      rank (2 * M - 7) < rank (M + 4) ∧
      rank (2 * M - 14) < rank (M + 1) ∧
      rank (2 * M - 10) < rank (M + 3)) := by
  have phase_dichotomy : ∀ {s d r : ℕ}, 0 < d → 1 ≤ r →
      (∀ i : ℕ, i ≤ r → s + d * i ∈ block M) →
      (∀ i : ℕ, i ≤ r → i % 2 = 0 →
        (0 < i → rank (s + d * i) < rank (s + d * (i - 1))) ∧
          (i < r → rank (s + d * i) < rank (s + d * (i + 1)))) ∨
      (∀ i : ℕ, i ≤ r → i % 2 = 1 →
        (0 < i → rank (s + d * i) < rank (s + d * (i - 1))) ∧
          (i < r → rank (s + d * i) < rank (s + d * (i + 1)))) := by
    intro s d r hd hr hmem
    have hne : rank (s + d * 0) ≠ rank (s + d * 1) := by
      intro h
      have heq := hinj (hmem 0 (by omega)) (hmem 1 (by omega)) h
      have : s + d * 0 < s + d * 1 := by nlinarith
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (ladder_phase_of_first_edge hinj hfree hd hr hmem (by omega)
        (Or.inl ⟨rfl, hlt⟩))
    · exact Or.inr (ladder_phase_of_first_edge hinj hfree hd hr hmem (by omega)
        (Or.inr ⟨rfl, hgt⟩))
  have zigzag : ∀ {s d r e : ℕ}, 0 < d → 1 ≤ r → e ≤ r →
      (∀ i : ℕ, i ≤ r → s + d * i ∈ block M) →
      ((0 < e ∧ rank (s + d * e) < rank (s + d * (e - 1))) ∨
        (e < r ∧ rank (s + d * e) < rank (s + d * (e + 1)))) →
      ∀ i : ℕ, i ≤ r → i % 2 = e % 2 →
        (0 < i → rank (s + d * i) < rank (s + d * (i - 1))) ∧
          (i < r → rank (s + d * i) < rank (s + d * (i + 1))) := by
    intro s d r e hd hr he hmem hseed
    rcases phase_dichotomy hd hr hmem with heven | hodd
    · have hep : e % 2 = 0 := by
        by_contra hep
        have hep1 : e % 2 = 1 := by omega
        rcases hseed with hseed | hseed
        · have hnpar : (e - 1) % 2 = 0 := by omega
          have hn := (heven (e - 1) (by omega) hnpar).2 (by omega)
          have heq : e - 1 + 1 = e := by omega
          rw [heq] at hn
          omega
        · have hnpar : (e + 1) % 2 = 0 := by omega
          have hn := (heven (e + 1) (by omega) hnpar).1 (by omega)
          have heq : e + 1 - 1 = e := by omega
          rw [heq] at hn
          omega
      intro i hir hip
      exact heven i hir (by omega)
    · have hep : e % 2 = 1 := by
        by_contra hep
        have hep0 : e % 2 = 0 := by omega
        rcases hseed with hseed | hseed
        · have hnpar : (e - 1) % 2 = 1 := by omega
          have hn := (hodd (e - 1) (by omega) hnpar).2 (by omega)
          have heq : e - 1 + 1 = e := by omega
          rw [heq] at hn
          omega
        · have hnpar : (e + 1) % 2 = 1 := by omega
          have hn := (hodd (e + 1) (by omega) hnpar).1 (by omega)
          have heq : e + 1 - 1 = e := by omega
          rw [heq] at hn
          omega
      intro i hir hip
      exact hodd i hir (by omega)
  intro hguards
  rcases hguards with ⟨ht11_b2, ht7_b4, ht14_b1, ht10_b3⟩
  rcases hEven with ⟨m, rfl⟩
  have hrootMem : ∀ i : ℕ, i ≤ m + m - 1 → m + m + 1 + 1 * i ∈ block (m + m) := by
    intro i hi
    simp only [block, Finset.mem_Icc]
    omega
  have ht11Mem : 2 * (m + m) - 11 ∈ block (m + m) := by
    simp only [block, Finset.mem_Icc]
    omega
  have ht10Mem : 2 * (m + m) - 10 ∈ block (m + m) := by
    simp only [block, Finset.mem_Icc]
    omega
  have hrootNe : rank (2 * (m + m) - 11) ≠ rank (2 * (m + m) - 10) := by
    intro heq
    have := hinj ht11Mem ht10Mem heq
    omega
  rcases lt_or_gt_of_ne hrootNe with hodd | heven
  · let c := m + m + 3 + 4 * ((m - 4) / 4)
    let d := c + 2
    have hrootSeed :
        rank (m + m + 1 + 1 * (m + m - 12)) <
          rank (m + m + 1 + 1 * (m + m - 12 + 1)) := by
      rw [show m + m + 1 + 1 * (m + m - 12) = 2 * (m + m) - 11 by omega]
      rw [show m + m + 1 + 1 * (m + m - 12 + 1) = 2 * (m + m) - 10 by omega]
      exact hodd
    have hroot := zigzag (s := m + m + 1) (d := 1)
      (r := m + m - 1) (e := m + m - 12) (by omega) (by omega) (by omega)
      hrootMem (Or.inr ⟨by omega, hrootSeed⟩)
    have hcPrev : rank c < rank (c - 1) := by
      have h := (hroot (c - (m + m + 1)) (by simp only [c]; omega)
        (by simp only [c]; omega)).1 (by simp only [c]; omega)
      rw [show m + m + 1 + 1 * (c - (m + m + 1)) = c by simp only [c]; omega] at h
      rw [show m + m + 1 + 1 * (c - (m + m + 1) - 1) = c - 1 by
        simp only [c]; omega] at h
      exact h
    have hdPrev : rank d < rank (d - 1) := by
      have h := (hroot (d - (m + m + 1)) (by simp only [d, c]; omega)
        (by simp only [d, c]; omega)).1 (by simp only [d, c]; omega)
      rw [show m + m + 1 + 1 * (d - (m + m + 1)) = d by
        simp only [d, c]; omega] at h
      rw [show m + m + 1 + 1 * (d - (m + m + 1) - 1) = d - 1 by
        simp only [d, c]; omega] at h
      exact h
    refine four_flood_cycle hinj hfree (c := c) (d := d)
      (tc := 2 * (m + m) - 14) (bc := m + m + 1)
      (td := 2 * (m + m) - 10) (bd := m + m + 3)
      (s2 := m + m + 2) (r2 := (m + m - 2) / 2)
      (sc := m + m + 1) (rc := (m + m - 1) / 4)
      (sd := m + m + 3) (rd := (m + m - 3) / 4)
      ?_ ?_ ?_ ?_ ?_ ?_ hcPrev hdPrev ht14_b1 ht10_b3
    all_goals simp only [c, d] <;> (repeat' apply And.intro) <;>
      (first | omega | trivial)
  · let c := m + m + 4 + 4 * ((m - 5) / 4)
    let d := c + 2
    have hrootSeed :
        rank (m + m + 1 + 1 * (m + m - 11)) <
          rank (m + m + 1 + 1 * (m + m - 11 - 1)) := by
      rw [show m + m + 1 + 1 * (m + m - 11) = 2 * (m + m) - 10 by omega]
      rw [show m + m + 1 + 1 * (m + m - 11 - 1) = 2 * (m + m) - 11 by omega]
      exact heven
    have hroot := zigzag (s := m + m + 1) (d := 1)
      (r := m + m - 1) (e := m + m - 11) (by omega) (by omega) (by omega)
      hrootMem (Or.inl ⟨by omega, hrootSeed⟩)
    have hcPrev : rank c < rank (c - 1) := by
      have h := (hroot (c - (m + m + 1)) (by simp only [c]; omega)
        (by simp only [c]; omega)).1 (by simp only [c]; omega)
      rw [show m + m + 1 + 1 * (c - (m + m + 1)) = c by simp only [c]; omega] at h
      rw [show m + m + 1 + 1 * (c - (m + m + 1) - 1) = c - 1 by
        simp only [c]; omega] at h
      exact h
    have hdPrev : rank d < rank (d - 1) := by
      have h := (hroot (d - (m + m + 1)) (by simp only [d, c]; omega)
        (by simp only [d, c]; omega)).1 (by simp only [d, c]; omega)
      rw [show m + m + 1 + 1 * (d - (m + m + 1)) = d by
        simp only [d, c]; omega] at h
      rw [show m + m + 1 + 1 * (d - (m + m + 1) - 1) = d - 1 by
        simp only [d, c]; omega] at h
      exact h
    refine four_flood_cycle hinj hfree (c := c) (d := d)
      (tc := 2 * (m + m) - 11) (bc := m + m + 2)
      (td := 2 * (m + m) - 7) (bd := m + m + 4)
      (s2 := m + m + 1) (r2 := (m + m - 2) / 2)
      (sc := m + m + 2) (rc := (m + m - 2) / 4)
      (sd := m + m + 4) (rd := (m + m - 4) / 4)
      ?_ ?_ ?_ ?_ ?_ ?_ hcPrev hdPrev ht11_b2 ht7_b4
    all_goals simp only [c, d] <;> (repeat' apply And.intro) <;>
      (first | omega | trivial)

private theorem odd_four_guards_impossible {M : ℕ} {rank : ℕ → ℕ}
    (hM : 17 ≤ M) (hOdd : Odd M) (hinj : Set.InjOn rank (block M))
    (hfree : APFree M rank) :
    ¬(rank (2 * M - 13) < rank (M + 1) ∧
      rank (2 * M - 9) < rank (M + 3) ∧
      rank (2 * M - 12) < rank (M + 2) ∧
      rank (2 * M - 8) < rank (M + 4)) := by
  have phase_dichotomy : ∀ {s d r : ℕ}, 0 < d → 1 ≤ r →
      (∀ i : ℕ, i ≤ r → s + d * i ∈ block M) →
      (∀ i : ℕ, i ≤ r → i % 2 = 0 →
        (0 < i → rank (s + d * i) < rank (s + d * (i - 1))) ∧
          (i < r → rank (s + d * i) < rank (s + d * (i + 1)))) ∨
      (∀ i : ℕ, i ≤ r → i % 2 = 1 →
        (0 < i → rank (s + d * i) < rank (s + d * (i - 1))) ∧
          (i < r → rank (s + d * i) < rank (s + d * (i + 1)))) := by
    intro s d r hd hr hmem
    have hne : rank (s + d * 0) ≠ rank (s + d * 1) := by
      intro h
      have heq := hinj (hmem 0 (by omega)) (hmem 1 (by omega)) h
      have : s + d * 0 < s + d * 1 := by nlinarith
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (ladder_phase_of_first_edge hinj hfree hd hr hmem (by omega)
        (Or.inl ⟨rfl, hlt⟩))
    · exact Or.inr (ladder_phase_of_first_edge hinj hfree hd hr hmem (by omega)
        (Or.inr ⟨rfl, hgt⟩))
  have zigzag : ∀ {s d r e : ℕ}, 0 < d → 1 ≤ r → e ≤ r →
      (∀ i : ℕ, i ≤ r → s + d * i ∈ block M) →
      ((0 < e ∧ rank (s + d * e) < rank (s + d * (e - 1))) ∨
        (e < r ∧ rank (s + d * e) < rank (s + d * (e + 1)))) →
      ∀ i : ℕ, i ≤ r → i % 2 = e % 2 →
        (0 < i → rank (s + d * i) < rank (s + d * (i - 1))) ∧
          (i < r → rank (s + d * i) < rank (s + d * (i + 1))) := by
    intro s d r e hd hr he hmem hseed
    rcases phase_dichotomy hd hr hmem with heven | hodd
    · have hep : e % 2 = 0 := by
        by_contra hep
        have hep1 : e % 2 = 1 := by omega
        rcases hseed with hseed | hseed
        · have hnpar : (e - 1) % 2 = 0 := by omega
          have hn := (heven (e - 1) (by omega) hnpar).2 (by omega)
          have heq : e - 1 + 1 = e := by omega
          rw [heq] at hn
          omega
        · have hnpar : (e + 1) % 2 = 0 := by omega
          have hn := (heven (e + 1) (by omega) hnpar).1 (by omega)
          have heq : e + 1 - 1 = e := by omega
          rw [heq] at hn
          omega
      intro i hir hip
      exact heven i hir (by omega)
    · have hep : e % 2 = 1 := by
        by_contra hep
        have hep0 : e % 2 = 0 := by omega
        rcases hseed with hseed | hseed
        · have hnpar : (e - 1) % 2 = 1 := by omega
          have hn := (hodd (e - 1) (by omega) hnpar).2 (by omega)
          have heq : e - 1 + 1 = e := by omega
          rw [heq] at hn
          omega
        · have hnpar : (e + 1) % 2 = 1 := by omega
          have hn := (hodd (e + 1) (by omega) hnpar).1 (by omega)
          have heq : e + 1 - 1 = e := by omega
          rw [heq] at hn
          omega
      intro i hir hip
      exact hodd i hir (by omega)
  intro hguards
  rcases hguards with ⟨ht13_b1, ht9_b3, ht12_b2, ht8_b4⟩
  rcases hOdd with ⟨m, rfl⟩
  have hrootMem : ∀ i : ℕ, i ≤ 2 * m → 2 * m + 2 + i ∈ block (2 * m + 1) := by
    intro i hi
    simp only [block, Finset.mem_Icc]
    omega
  have ht13Mem : 2 * (2 * m + 1) - 13 ∈ block (2 * m + 1) := by
    simp only [block, Finset.mem_Icc]
    omega
  have ht12Mem : 2 * (2 * m + 1) - 12 ∈ block (2 * m + 1) := by
    simp only [block, Finset.mem_Icc]
    omega
  have hrootNe :
      rank (2 * (2 * m + 1) - 13) ≠ rank (2 * (2 * m + 1) - 12) := by
    intro heq
    have := hinj ht13Mem ht12Mem heq
    omega
  rcases lt_or_gt_of_ne hrootNe with hodd | heven
  · let c := 2 * m + 5 + 4 * ((m - 4) / 4)
    let d := c + 2
    have hrootSeed :
        rank (2 * m + 2 + (2 * m - 13)) <
          rank (2 * m + 2 + (2 * m - 13 + 1)) := by
      rw [show 2 * m + 2 + (2 * m - 13) = 2 * (2 * m + 1) - 13 by omega]
      rw [show 2 * m + 2 + (2 * m - 13 + 1) = 2 * (2 * m + 1) - 12 by omega]
      exact hodd
    have hroot := zigzag (s := 2 * m + 2) (d := 1)
      (r := 2 * m) (e := 2 * m - 13) (by omega) (by omega) (by omega)
      (by simpa only [one_mul, Nat.add_assoc] using hrootMem)
      (Or.inr ⟨by omega, by simpa only [one_mul, Nat.add_assoc] using hrootSeed⟩)
    have hcPrev : rank c < rank (c - 1) := by
      have h := (hroot (c - (2 * m + 2)) (by simp only [c]; omega)
        (by simp only [c]; omega)).1 (by simp only [c]; omega)
      rw [show 2 * m + 2 + 1 * (c - (2 * m + 2)) = c by simp only [c]; omega] at h
      rw [show 2 * m + 2 + 1 * (c - (2 * m + 2) - 1) = c - 1 by
        simp only [c]; omega] at h
      exact h
    have hdPrev : rank d < rank (d - 1) := by
      have h := (hroot (d - (2 * m + 2)) (by simp only [d, c]; omega)
        (by simp only [d, c]; omega)).1 (by simp only [d, c]; omega)
      rw [show 2 * m + 2 + 1 * (d - (2 * m + 2)) = d by
        simp only [d, c]; omega] at h
      rw [show 2 * m + 2 + 1 * (d - (2 * m + 2) - 1) = d - 1 by
        simp only [d, c]; omega] at h
      exact h
    refine four_flood_cycle hinj hfree (c := c) (d := d)
      (tc := 2 * (2 * m + 1) - 12) (bc := 2 * m + 3)
      (td := 2 * (2 * m + 1) - 8) (bd := 2 * m + 5)
      (s2 := 2 * m + 2) (r2 := m)
      (sc := 2 * m + 3) (rc := (2 * m - 1) / 4)
      (sd := 2 * m + 5) (rd := (2 * m - 3) / 4)
      ?_ ?_ ?_ ?_ ?_ ?_ hcPrev hdPrev ht12_b2 ht8_b4
    all_goals simp only [c, d] <;> (repeat' apply And.intro) <;>
      (first | omega | trivial)
  · let c := 2 * m + 4 + 4 * ((m - 3) / 4)
    let d := c + 2
    have hrootSeed :
        rank (2 * m + 2 + (2 * m - 12)) <
          rank (2 * m + 2 + (2 * m - 12 - 1)) := by
      rw [show 2 * m + 2 + (2 * m - 12) = 2 * (2 * m + 1) - 12 by omega]
      rw [show 2 * m + 2 + (2 * m - 12 - 1) = 2 * (2 * m + 1) - 13 by omega]
      exact heven
    have hroot := zigzag (s := 2 * m + 2) (d := 1)
      (r := 2 * m) (e := 2 * m - 12) (by omega) (by omega) (by omega)
      (by simpa only [one_mul, Nat.add_assoc] using hrootMem)
      (Or.inl ⟨by omega, by simpa only [one_mul, Nat.add_assoc] using hrootSeed⟩)
    have hcPrev : rank c < rank (c - 1) := by
      have h := (hroot (c - (2 * m + 2)) (by simp only [c]; omega)
        (by simp only [c]; omega)).1 (by simp only [c]; omega)
      rw [show 2 * m + 2 + 1 * (c - (2 * m + 2)) = c by simp only [c]; omega] at h
      rw [show 2 * m + 2 + 1 * (c - (2 * m + 2) - 1) = c - 1 by
        simp only [c]; omega] at h
      exact h
    have hdPrev : rank d < rank (d - 1) := by
      have h := (hroot (d - (2 * m + 2)) (by simp only [d, c]; omega)
        (by simp only [d, c]; omega)).1 (by simp only [d, c]; omega)
      rw [show 2 * m + 2 + 1 * (d - (2 * m + 2)) = d by
        simp only [d, c]; omega] at h
      rw [show 2 * m + 2 + 1 * (d - (2 * m + 2) - 1) = d - 1 by
        simp only [d, c]; omega] at h
      exact h
    refine four_flood_cycle hinj hfree (c := c) (d := d)
      (tc := 2 * (2 * m + 1) - 13) (bc := 2 * m + 2)
      (td := 2 * (2 * m + 1) - 9) (bd := 2 * m + 4)
      (s2 := 2 * m + 3) (r2 := m - 1)
      (sc := 2 * m + 2) (rc := m / 2)
      (sd := 2 * m + 4) (rd := (2 * m - 2) / 4)
      ?_ ?_ ?_ ?_ ?_ ?_ hcPrev hdPrev ht13_b1 ht9_b3
    all_goals simp only [c, d] <;> (repeat' apply And.intro) <;>
      (first | omega | trivial)

/-- No order gadget exists at any scale at least sixteen. -/
def claim : Prop := ∀ M : ℕ, 16 ≤ M → ¬ OrderGadget M

theorem result : claim := by
  intro M hM hGadget
  rcases hGadget with ⟨rank, hinj, hfree, hguards⟩
  rcases Nat.even_or_odd M with hEven | hOdd
  · apply even_four_guards_impossible hM hEven hinj hfree
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hguards 15 (Or.inl rfl) 2 (by omega) (by omega)
    · simpa using hguards 15 (Or.inl rfl) 4 (by omega) (by omega)
    · simpa using hguards 16 (Or.inr rfl) 1 (by omega) (by omega)
    · simpa using hguards 16 (Or.inr rfl) 3 (by omega) (by omega)
  · have hM17 : 17 ≤ M := by
      rcases hOdd with ⟨m, hm⟩
      omega
    apply odd_four_guards_impossible hM17 hOdd hinj hfree
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hguards 15 (Or.inl rfl) 1 (by omega) (by omega)
    · simpa using hguards 15 (Or.inl rfl) 3 (by omega) (by omega)
    · simpa using hguards 16 (Or.inr rfl) 2 (by omega) (by omega)
    · simpa using hguards 16 (Or.inr rfl) 4 (by omega) (by omega)

end D5.S3.Combinatorics.ErdosGrahamOrderGadget
