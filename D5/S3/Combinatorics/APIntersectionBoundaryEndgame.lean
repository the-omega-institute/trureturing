/- GID: D5/S3/Combinatorics/APIntersectionBoundaryEndgame
   generality: G
   mirror-B: D5/B/S3/Combinatorics/APIntersectionBoundaryEndgame
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Finset.Card, mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Boundary single-difference AP-intersection families have at most choose N 2 plus one members. -/

import D5.S3.Combinatorics.APIntersectionBoundaryEndgameDefs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.APIntersectionBoundaryEndgame

/-- Distinct members cannot share a two-point code. -/
private lemma pair_code_separate {N d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d)
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hinter : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).Nonempty ∧ IsAP (S ∩ T))
    (hlong : ∀ S ∈ F, 4 ≤ S.card → IsAP S)
    (havoid : ∀ S ∈ F, 1 ∉ S → 4 ≤ S.card ∧ IsAPDiff d S)
    {S T : Finset ℕ} (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    {p : Finset ℕ} (hcS : code N d S = some (Sum.inr p))
    (hcT : code N d T = some (Sum.inr p)) : False := by
  classical
  have avoiderForm : ∀ {U : Finset ℕ}, U ⊆ Finset.Icc 1 N → 1 ∉ U →
      IsAPDiff d U → 2 ≤ avoiderStart d U ∧ 0 < U.card ∧
        U = apRange (avoiderStart d U) d U.card ∧
        avoiderStart d U + (U.card - 1) * d ≤ N := by
    intro U hU hone hap
    let a := avoiderStart d U
    have hs : ∃ n : ℕ, 0 < n ∧ U = apRange a d n := by
      simpa only [a, avoiderStart, dif_pos hap, apRange] using Classical.choose_spec hap
    obtain ⟨n, hn, hUform⟩ := hs
    have haU : a ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨0, by simpa using hn, by simp⟩
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hU haU)).1
    have ha2 : 2 ≤ a := by
      by_contra h
      have hval : a = 1 := by omega
      exact hone (hval ▸ haU)
    have hc : U.card = n := by
      rw [hUform]
      unfold apRange
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)
    have hlast : a + (n - 1) * d ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨n - 1, by simp only [Finset.mem_range]; omega, rfl⟩
    exact ⟨ha2, by omega, by simpa [hc] using hUform,
      by simpa [hc] using (Finset.mem_Icc.mp (hU hlast)).2⟩
  have throughForm : ∀ {U : Finset ℕ}, U ⊆ Finset.Icc 1 N → 1 ∈ U →
      IsAP U → 0 < throughStep U ∧ U = apRange 1 (throughStep U) U.card := by
    intro U hU hone hap
    have hs : 0 < throughStep U ∧ IsAPDiff (throughStep U) U := by
      unfold throughStep
      simpa only [dif_pos hap] using Classical.choose_spec hap
    obtain ⟨a, n, hn, hUform⟩ := hs.2
    have haU : a ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨0, by simpa using hn, by simp⟩
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hU haU)).1
    have h1a : a ≤ 1 := by
      have hmem : 1 ∈ (Finset.range n).image (fun i => a + i * throughStep U) := by
        rw [← hUform]
        exact hone
      obtain ⟨i, hi, hval⟩ := Finset.mem_image.mp hmem
      omega
    have ha : a = 1 := by omega
    subst a
    change U = apRange 1 (throughStep U) n at hUform
    have hc : U.card = n := by
      rw [hUform]
      unfold apRange
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact Nat.mul_right_cancel hs.1 (Nat.add_left_cancel hij)
    exact ⟨hs.1, by simpa [hc] using hUform⟩
  have smallPair : ∀ {U A : Finset ℕ}, U ∈ F → A ∈ F → 1 ∈ U → 1 ∉ A →
      ((U.erase 1) ∩ A).Nonempty := by
    intro U A hU hA hone havoidA
    have hne : U ≠ A := by
      intro heq
      exact havoidA (heq ▸ hone)
    obtain ⟨z, hz⟩ := (hinter _ hU _ hA hne).1
    refine ⟨z, Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hz).2⟩⟩
    exact Finset.mem_erase.mpr ⟨by
      intro heq
      exact havoidA (heq ▸ (Finset.mem_inter.mp hz).2), (Finset.mem_inter.mp hz).1⟩
  have external : ∀ {a m : ℕ}, 0 < m → 2 ≤ a - d →
      Disjoint ({a - d, a + m * d} : Finset ℕ) (apRange a d m) := by
    intro a m hm hl
    rw [Finset.disjoint_left]
    intro z hz hzA
    obtain ⟨i, hi, hzi⟩ : ∃ i < m, z = a + i * d := by
      simpa [apRange, eq_comm] using hzA
    have hmul := Nat.mul_le_mul_right d (show i ≤ m - 1 by omega)
    have hrel : a + (m - 1) * d + d = a + m * d := by
      calc
        _ = a + (m - 1 + 1) * d := by rw [Nat.add_mul, one_mul]; omega
        _ = a + m * d := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> omega
  have pairRecover : ∀ {a b d m n : ℕ}, 0 < d → 0 < m → 0 < n →
      2 ≤ a - d → 2 ≤ b - d →
      ({a - d, a + m * d} : Finset ℕ) = {b - d, b + n * d} →
      apRange a d m = apRange b d n := by
    intro a b d m n hd hm hn hla hlb heq
    have haOrder : a - d < a + m * d := by omega
    have hbOrder : b - d < b + n * d := by omega
    have hleft : a - d = b - d := by
      have hx : a - d ∈ ({b - d, b + n * d} : Finset ℕ) := by rw [← heq]; simp
      have hy : a + m * d ∈ ({b - d, b + n * d} : Finset ℕ) := by rw [← heq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with h | h <;> rcases hy with h' | h' <;> omega
    have hright : a + m * d = b + n * d := by
      have hy : a + m * d ∈ ({b - d, b + n * d} : Finset ℕ) := by rw [← heq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h <;> omega
    have hab : a = b := by omega
    subst b
    have hmn : m = n := Nat.mul_right_cancel hd (Nat.add_left_cancel hright)
    subst n
    rfl
  have terminalRecover : ∀ {d e n m : ℕ}, 0 < d → 0 < e → 4 ≤ n → 4 ≤ m →
      ({1 + (n - 2) * d, 1 + (n - 1) * d} : Finset ℕ) =
        {1 + (m - 2) * e, 1 + (m - 1) * e} →
      apRange 1 d n = apRange 1 e m := by
    intro d e n m hd he hn hm hpair
    have hnrel : (n - 2) * d + d = (n - 1) * d := by
      calc
        (n - 2) * d + d = (n - 2 + 1) * d := by rw [Nat.add_mul, one_mul]
        _ = _ := by congr 1; omega
    have hmrel : (m - 2) * e + e = (m - 1) * e := by
      calc
        (m - 2) * e + e = (m - 2 + 1) * e := by rw [Nat.add_mul, one_mul]
        _ = _ := by congr 1; omega
    have hno : 1 + (n - 2) * d < 1 + (n - 1) * d := by omega
    have hmo : 1 + (m - 2) * e < 1 + (m - 1) * e := by omega
    have hx : 1 + (n - 2) * d = 1 + (m - 2) * e := by
      have h1 : 1 + (n - 2) * d ∈ ({1 + (m - 2) * e, 1 + (m - 1) * e} : Finset ℕ) := by
        rw [← hpair]
        simp
      have h2 : 1 + (n - 1) * d ∈ ({1 + (m - 2) * e, 1 + (m - 1) * e} : Finset ℕ) := by
        rw [← hpair]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      rcases h1 with h | h <;> rcases h2 with h' | h' <;> omega
    have hy : 1 + (n - 1) * d = 1 + (m - 1) * e := by
      have h2 : 1 + (n - 1) * d ∈ ({1 + (m - 2) * e, 1 + (m - 1) * e} : Finset ℕ) := by
        rw [← hpair]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      rcases h2 with h | h <;> omega
    have hde : d = e := by omega
    subst e
    have hnm : n - 1 = m - 1 := Nat.mul_right_cancel hd (by omega :
      (n - 1) * d = (m - 1) * d)
    have hnm' : n = m := by omega
    subst m
    rfl
  have pair_cases (U : Finset ℕ) (hc : code N d U = some (Sum.inr p)) :
      (1 ∈ U ∧ U.card = 3 ∧ p = U.erase 1) ∨
      (1 ∈ U ∧ 4 ≤ U.card ∧
        p = {1 + (U.card - 2) * throughStep U, 1 + (U.card - 1) * throughStep U}) ∨
      (1 ∉ U ∧ 2 ≤ avoiderStart d U - d ∧ avoiderStart d U + U.card * d ≤ N ∧
        p = {avoiderStart d U - d, avoiderStart d U + U.card * d}) := by
    by_cases hone : 1 ∈ U
    · by_cases h1 : U.card = 1
      · simp [code, hone, h1] at hc
      by_cases h2 : U.card = 2
      · simp only [code, if_pos hone, if_neg h1, if_pos h2] at hc
        cases hc
      by_cases h3 : U.card = 3
      · left
        have hp : p = U.erase 1 := by
          simpa only [code, if_pos hone, if_neg h1, if_neg h2, if_pos h3,
            Option.some.injEq, Sum.inr.injEq] using hc.symm
        exact ⟨hone, h3, hp⟩
      · right; left
        have hpos : 0 < U.card := Finset.card_pos.mpr ⟨1, hone⟩
        have hfour : 4 ≤ U.card := by omega
        have hp : p = {1 + (U.card - 2) * throughStep U,
            1 + (U.card - 1) * throughStep U} := by
          simpa only [code, if_pos hone, if_neg h1, if_neg h2, if_neg h3,
            Option.some.injEq, Sum.inr.injEq] using hc.symm
        exact ⟨hone, hfour, hp⟩
    · by_cases hl : 2 ≤ avoiderStart d U - d
      · by_cases hr : avoiderStart d U + U.card * d ≤ N
        · right; right
          have hp : p = {avoiderStart d U - d, avoiderStart d U + U.card * d} := by
            simpa only [code, if_neg hone, if_pos hl, if_pos hr,
              Option.some.injEq, Sum.inr.injEq] using hc.symm
          exact ⟨hone, hl, hr, hp⟩
        · simp only [code, if_neg hone, if_pos hl, if_neg hr] at hc
          cases hc
      · by_cases hr : avoiderStart d U + U.card * d ≤ N
        · simp only [code, if_neg hone, if_neg hl, if_pos hr] at hc
          cases hc
        · simp only [code, if_neg hone, if_neg hl, if_neg hr] at hc
          cases hc
  have meet := (hinter S hS T hT hne).1
  rcases pair_cases S hcS with hst | hsl | hsa
  · rcases pair_cases T hcT with htt | htl | hta
    · obtain ⟨honeS, hcardS, hpS⟩ := hst
      obtain ⟨honeT, hcardT, hpT⟩ := htt
      have herase : S.erase 1 = T.erase 1 := hpS.symm.trans hpT
      exact hne (calc
        S = insert 1 (S.erase 1) := (Finset.insert_erase honeS).symm
        _ = insert 1 (T.erase 1) := by rw [herase]
        _ = T := Finset.insert_erase honeT)
    · obtain ⟨honeS, hcardS, hpS⟩ := hst
      obtain ⟨honeT, hcardT, hpT⟩ := htl
      obtain ⟨hstepT, hnormT⟩ := throughForm (hsub T hT) honeT
        (hlong T hT hcardT)
      exact triple_terminal_separate hstepT hcardT hS hT honeS hcardS hnormT
        (hpS.symm.trans hpT) hinter
    · obtain ⟨honeS, hcardS, hpS⟩ := hst
      obtain ⟨honeT, hlT, hrT, hpT⟩ := hta
      obtain ⟨_, hapT⟩ := havoid T hT honeT
      obtain ⟨haT, hposT, hnormT, hlastT⟩ := avoiderForm (hsub T hT) honeT hapT
      have hmeet' := smallPair hS hT honeS honeT
      have hdis := external hposT hlT
      let aT := avoiderStart d T
      let mT := T.card
      change p = {aT - d, aT + mT * d} at hpT
      change T = apRange aT d mT at hnormT
      change Disjoint ({aT - d, aT + mT * d} : Finset ℕ) (apRange aT d mT) at hdis
      have hdis' : Disjoint p T := by
        rw [hpT, hnormT]
        exact hdis
      have hsub' : S.erase 1 = p := hpS.symm
      rw [hsub'] at hmeet'
      obtain ⟨z, hz⟩ := hmeet'
      exact Finset.disjoint_left.mp hdis' (Finset.mem_inter.mp hz).1
        (Finset.mem_inter.mp hz).2
  · rcases pair_cases T hcT with htt | htl | hta
    · obtain ⟨honeS, hcardS, hpS⟩ := hsl
      obtain ⟨honeT, hcardT, hpT⟩ := htt
      obtain ⟨hstepS, hnormS⟩ := throughForm (hsub S hS) honeS
        (hlong S hS hcardS)
      exact triple_terminal_separate hstepS hcardS hT hS honeT hcardT hnormS
        (hpT.symm.trans hpS) hinter
    · obtain ⟨honeS, hcardS, hpS⟩ := hsl
      obtain ⟨honeT, hcardT, hpT⟩ := htl
      obtain ⟨hstepS, hnormS⟩ := throughForm (hsub S hS) honeS
        (hlong S hS hcardS)
      obtain ⟨hstepT, hnormT⟩ := throughForm (hsub T hT) honeT
        (hlong T hT hcardT)
      have hrec := terminalRecover hstepS hstepT hcardS hcardT
        (hpS.symm.trans hpT)
      exact hne (hnormS.trans (hrec.trans hnormT.symm))
    · obtain ⟨honeS, hcardS, hpS⟩ := hsl
      obtain ⟨honeT, hlT, hrT, hpT⟩ := hta
      obtain ⟨hstepS, hnormS⟩ := throughForm (hsub S hS) honeS
        (hlong S hS hcardS)
      obtain ⟨haT, hposT, hnormT, hlastT⟩ := avoiderForm (hsub T hT) honeT
        (havoid T hT honeT).2
      have hdis := terminal_avoider_disjoint hd hstepS hposT hcardS hlT
        (hpS.symm.trans hpT)
      have hdis' : Disjoint S T := by rw [hnormS, hnormT]; exact hdis
      obtain ⟨z, hz⟩ := meet
      exact Finset.disjoint_left.mp hdis' (Finset.mem_inter.mp hz).1
        (Finset.mem_inter.mp hz).2
  · rcases pair_cases T hcT with htt | htl | hta
    · obtain ⟨honeS, hlS, hrS, hpS⟩ := hsa
      obtain ⟨honeT, hcardT, hpT⟩ := htt
      obtain ⟨_, hapS⟩ := havoid S hS honeS
      obtain ⟨haS, hposS, hnormS, hlastS⟩ := avoiderForm (hsub S hS) honeS hapS
      have hmeet' := smallPair hT hS honeT honeS
      have hdis := external hposS hlS
      let aS := avoiderStart d S
      let mS := S.card
      change p = {aS - d, aS + mS * d} at hpS
      change S = apRange aS d mS at hnormS
      change Disjoint ({aS - d, aS + mS * d} : Finset ℕ) (apRange aS d mS) at hdis
      have hdis' : Disjoint p S := by rw [hpS, hnormS]; exact hdis
      have hsub' : T.erase 1 = p := hpT.symm
      rw [hsub'] at hmeet'
      obtain ⟨z, hz⟩ := hmeet'
      exact Finset.disjoint_left.mp hdis' (Finset.mem_inter.mp hz).1
        (Finset.mem_inter.mp hz).2
    · obtain ⟨honeS, hlS, hrS, hpS⟩ := hsa
      obtain ⟨honeT, hcardT, hpT⟩ := htl
      obtain ⟨haS, hposS, hnormS, hlastS⟩ := avoiderForm (hsub S hS) honeS
        (havoid S hS honeS).2
      obtain ⟨hstepT, hnormT⟩ := throughForm (hsub T hT) honeT
        (hlong T hT hcardT)
      have hdis := terminal_avoider_disjoint hd hstepT hposS hcardT hlS
        (hpT.symm.trans hpS)
      have hdis' : Disjoint S T := by rw [hnormS, hnormT]; exact hdis.symm
      obtain ⟨z, hz⟩ := meet
      exact Finset.disjoint_left.mp hdis' (Finset.mem_inter.mp hz).1
        (Finset.mem_inter.mp hz).2
    · obtain ⟨honeS, hlS, hrS, hpS⟩ := hsa
      obtain ⟨honeT, hlT, hrT, hpT⟩ := hta
      obtain ⟨haS, hposS, hnormS, hlastS⟩ := avoiderForm (hsub S hS) honeS
        (havoid S hS honeS).2
      obtain ⟨haT, hposT, hnormT, hlastT⟩ := avoiderForm (hsub T hT) honeT
        (havoid T hT honeT).2
      have hrec := pairRecover hd hposS hposT hlS hlT (hpS.symm.trans hpT)
      exact hne (hnormS.trans (hrec.trans hnormT.symm))

/-- The resource code is injective on a boundary single-difference family. -/
private lemma code_injective {N d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d)
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hinter : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).Nonempty ∧ IsAP (S ∩ T))
    (hlong : ∀ S ∈ F, 4 ≤ S.card → IsAP S)
    (havoid : ∀ S ∈ F, 1 ∉ S → 4 ≤ S.card ∧ IsAPDiff d S) :
    Set.InjOn (code N d) F := by
  intro S hS T hT heq
  by_contra hne
  cases hc : code N d S with
  | none =>
      have ht : code N d T = none := by rw [hc] at heq; exact heq.symm
      exact none_code_separate hd hsub hinter havoid hS hT hne hc ht
  | some v =>
      cases v with
      | inl x =>
          have ht : code N d T = some (Sum.inl x) := by rw [hc] at heq; exact heq.symm
          exact point_code_separate hd hsub hinter havoid hS hT hne hc ht
      | inr p =>
          have ht : code N d T = some (Sum.inr p) := by rw [hc] at heq; exact heq.symm
          exact pair_code_separate hd hsub hinter hlong havoid hS hT hne hc ht

theorem result : claim := by
  intro N d F hd hsub hinter hlong havoid
  classical
  have avoiderForm : ∀ {U : Finset ℕ}, U ⊆ Finset.Icc 1 N → 1 ∉ U →
      IsAPDiff d U → 2 ≤ avoiderStart d U ∧ 0 < U.card ∧
        U = apRange (avoiderStart d U) d U.card ∧
        avoiderStart d U + (U.card - 1) * d ≤ N := by
    intro U hU hone hap
    let a := avoiderStart d U
    have hs : ∃ n : ℕ, 0 < n ∧ U = apRange a d n := by
      simpa only [a, avoiderStart, dif_pos hap, apRange] using Classical.choose_spec hap
    obtain ⟨n, hn, hUform⟩ := hs
    have haU : a ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨0, by simpa using hn, by simp⟩
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hU haU)).1
    have ha2 : 2 ≤ a := by
      by_contra h
      have hval : a = 1 := by omega
      exact hone (hval ▸ haU)
    have hc : U.card = n := by
      rw [hUform]
      unfold apRange
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)
    have hlast : a + (n - 1) * d ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨n - 1, by simp only [Finset.mem_range]; omega, rfl⟩
    exact ⟨ha2, by omega, by simpa [hc] using hUform,
      by simpa [hc] using (Finset.mem_Icc.mp (hU hlast)).2⟩
  have throughForm : ∀ {U : Finset ℕ}, U ⊆ Finset.Icc 1 N → 1 ∈ U →
      IsAP U → 0 < throughStep U ∧ U = apRange 1 (throughStep U) U.card := by
    intro U hU hone hap
    have hs : 0 < throughStep U ∧ IsAPDiff (throughStep U) U := by
      unfold throughStep
      simpa only [dif_pos hap] using Classical.choose_spec hap
    obtain ⟨a, n, hn, hUform⟩ := hs.2
    have haU : a ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨0, by simpa using hn, by simp⟩
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hU haU)).1
    have h1a : a ≤ 1 := by
      have hmem : 1 ∈ (Finset.range n).image (fun i => a + i * throughStep U) := by
        rw [← hUform]
        exact hone
      obtain ⟨i, hi, hval⟩ := Finset.mem_image.mp hmem
      omega
    have ha : a = 1 := by omega
    subst a
    change U = apRange 1 (throughStep U) n at hUform
    have hc : U.card = n := by
      rw [hUform]
      unfold apRange
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact Nat.mul_right_cancel hs.1 (Nat.add_left_cancel hij)
    exact ⟨hs.1, by simpa [hc] using hUform⟩
  have hm : Set.MapsTo (code N d) F (targets N) := by
    intro S hS
    classical
    let V := vertices N
    have hsubS := hsub S hS
    by_cases hone : 1 ∈ S
    · by_cases hc1 : S.card = 1
      · simp [code, hone, hc1, targets]
      by_cases hc2 : S.card = 2
      · have hscard : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
        have herase : (S.erase 1).card = 1 := by
          rw [Finset.card_erase_of_mem hone]
          omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp herase
        have hxe : x ∈ S.erase 1 := by rw [hx]; simp
        have hxS : x ∈ S := (Finset.mem_erase.mp hxe).2
        have hxne : x ≠ 1 := (Finset.mem_erase.mp hxe).1
        have hxlo : 2 ≤ x := by
          have := (Finset.mem_Icc.mp (hsubS hxS)).1
          omega
        have hsupLo : 2 ≤ S.sup id :=
          hxlo.trans (by simpa using (Finset.le_sup (f := id) hxS))
        have hsupHi : S.sup id ≤ N :=
          Finset.sup_le_iff.mpr (by
            intro y hy
            exact (Finset.mem_Icc.mp (hsubS hy)).2)
        have hV : S.sup id ∈ V := Finset.mem_Icc.mpr ⟨hsupLo, hsupHi⟩
        simp only [code, if_pos hone, if_neg hc1, if_pos hc2]
        change some (Sum.inl (S.sup id)) ∈ targets N
        unfold targets
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_image.mpr ⟨S.sup id, hV, rfl⟩
      by_cases hc3 : S.card = 3
      · have hcard : (S.erase 1).card = 2 := by
          rw [Finset.card_erase_of_mem hone]
          omega
        have hV : S.erase 1 ⊆ V := by
          intro x hx
          have hx' := Finset.mem_erase.mp hx
          have hI := Finset.mem_Icc.mp (hsubS hx'.2)
          exact Finset.mem_Icc.mpr ⟨by omega, hI.2⟩
        have hp : S.erase 1 ∈ V.powersetCard 2 :=
          Finset.mem_powersetCard.mpr ⟨hV, hcard⟩
        simp only [code, if_pos hone, if_neg hc1, if_neg hc2, if_pos hc3]
        change some (Sum.inr (S.erase 1)) ∈ targets N
        unfold targets
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_image.mpr ⟨S.erase 1, hp, rfl⟩
      · have hcardPos : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
        have hfour : 4 ≤ S.card := by omega
        obtain ⟨hstep, hnormal⟩ := throughForm hsubS hone (hlong S hS hfour)
        let x := 1 + (S.card - 2) * throughStep S
        let y := 1 + (S.card - 1) * throughStep S
        have hxS : x ∈ S := by
          rw [hnormal]
          exact Finset.mem_image.mpr
            ⟨S.card - 2, by simp only [Finset.mem_range]; omega, rfl⟩
        have hyS : y ∈ S := by
          rw [hnormal]
          exact Finset.mem_image.mpr
            ⟨S.card - 1, by simp only [Finset.mem_range]; omega, rfl⟩
        have hxy : x < y := by
          have hrel : (S.card - 2) * throughStep S + throughStep S =
              (S.card - 1) * throughStep S := by
            have h : S.card - 2 + 1 = S.card - 1 := by omega
            calc
              _ = (S.card - 2 + 1) * throughStep S := by rw [Nat.add_mul, one_mul]
              _ = _ := by rw [h]
          dsimp [x, y]
          omega
        have hprodPos : 0 < (S.card - 2) * throughStep S := Nat.mul_pos (by omega) hstep
        have hxlow : 2 ≤ x := by dsimp [x]; omega
        have hp : ({x, y} : Finset ℕ) ∈ V.powersetCard 2 := by
          apply Finset.mem_powersetCard.mpr
          constructor
          · intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · have hI := Finset.mem_Icc.mp (hsubS hxS)
              exact Finset.mem_Icc.mpr ⟨hxlow, hI.2⟩
            · have hI := Finset.mem_Icc.mp (hsubS hyS)
              exact Finset.mem_Icc.mpr ⟨hxlow.trans (Nat.le_of_lt hxy), hI.2⟩
          · simp [ne_of_lt hxy]
        simp only [code, if_pos hone, if_neg hc1, if_neg hc2, if_neg hc3]
        change some (Sum.inr ({x, y} : Finset ℕ)) ∈ targets N
        unfold targets
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_image.mpr ⟨{x, y}, hp, rfl⟩
    · obtain ⟨hfour, hap⟩ := havoid S hS hone
      obtain ⟨ha, hpos, hnormal, hlast⟩ := avoiderForm hsubS hone hap
      let a := avoiderStart d S
      have haN : a ≤ N := by
        have h := Nat.le_add_right a ((S.card - 1) * d)
        omega
      by_cases hl : 2 ≤ a - d
      · have hlV : a - d ∈ V := Finset.mem_Icc.mpr ⟨hl, by omega⟩
        by_cases hr : a + S.card * d ≤ N
        · have hrV : a + S.card * d ∈ V := Finset.mem_Icc.mpr ⟨by omega, hr⟩
          have hpair : ({a - d, a + S.card * d} : Finset ℕ) ∈ V.powersetCard 2 := by
            apply Finset.mem_powersetCard.mpr
            constructor
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact hlV
              · exact hrV
            · simp [show a - d ≠ a + S.card * d by omega]
          change 2 ≤ avoiderStart d S - d at hl
          change avoiderStart d S + S.card * d ≤ N at hr
          simp only [code, if_neg hone, if_pos hl, if_pos hr]
          change some (Sum.inr ({a - d, a + S.card * d} : Finset ℕ)) ∈ targets N
          unfold targets
          apply Finset.mem_insert.mpr
          right
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_image.mpr ⟨{a - d, a + S.card * d}, hpair, rfl⟩
        · change 2 ≤ avoiderStart d S - d at hl
          change ¬ avoiderStart d S + S.card * d ≤ N at hr
          simp only [code, if_neg hone, if_pos hl, if_neg hr]
          change some (Sum.inl (a - d)) ∈ targets N
          unfold targets
          apply Finset.mem_insert.mpr
          right
          apply Finset.mem_union.mpr
          left
          exact Finset.mem_image.mpr ⟨a - d, hlV, rfl⟩
      · by_cases hr : a + S.card * d ≤ N
        · have hrV : a + S.card * d ∈ V := Finset.mem_Icc.mpr ⟨by omega, hr⟩
          change ¬ 2 ≤ avoiderStart d S - d at hl
          change avoiderStart d S + S.card * d ≤ N at hr
          simp only [code, if_neg hone, if_neg hl, if_pos hr]
          change some (Sum.inl (a + S.card * d)) ∈ targets N
          unfold targets
          apply Finset.mem_insert.mpr
          right
          apply Finset.mem_union.mpr
          left
          exact Finset.mem_image.mpr ⟨a + S.card * d, hrV, rfl⟩
        · change ¬ 2 ≤ avoiderStart d S - d at hl
          change ¬ avoiderStart d S + S.card * d ≤ N at hr
          simp only [code, if_neg hone, if_neg hl, if_neg hr]
          change none ∈ targets N
          simp [targets]
  have hinj := code_injective hd hsub hinter hlong havoid
  have targetBound : (targets N).card ≤ N.choose 2 + 1 := by
    classical
    let V := vertices N
    let points : Finset (Option (ℕ ⊕ Finset ℕ)) :=
      V.image (fun x => some (Sum.inl x))
    let pairs : Finset (Option (ℕ ⊕ Finset ℕ)) :=
      (V.powersetCard 2).image (fun p => some (Sum.inr p))
    have hcardV : V.card = N - 1 := by simp [V, vertices]
    have hcardPairs : (V.powersetCard 2).card = (N - 1).choose 2 := by
      rw [Finset.card_powersetCard, hcardV]
    have hsum : (N - 1) + (N - 1).choose 2 = N.choose 2 := by
      cases N with
      | zero => simp
      | succ n =>
          simp [Nat.choose_succ_succ, Nat.choose_one_right]
    have h1 : points.card ≤ V.card := Finset.card_image_le
    have h2 : pairs.card ≤ (V.powersetCard 2).card := Finset.card_image_le
    have h3 := Finset.card_union_le points pairs
    have h4 := Finset.card_insert_le none (points ∪ pairs)
    change (insert none (points ∪ pairs)).card ≤ N.choose 2 + 1
    omega
  exact (Finset.card_le_card_of_injOn (code N d) hm hinj).trans
    targetBound

#print axioms result

end D5.S3.Combinatorics.APIntersectionBoundaryEndgame
