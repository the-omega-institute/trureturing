/- GID: D5/S3/Estimation/DecisionRisk/LocalCARDeficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/LocalCARDeficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local CAR substitutions preserve pair readouts and have exact directed deficiencies. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Cast
noncomputable section
open scoped BigOperators ENNReal
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker
namespace D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
abbrev Block (A : Type*) := {B : Finset A // B.Nonempty}
noncomputable instance blockFintype {A : Type*} [Fintype A] : Fintype (Block A) :=
  Fintype.ofFinite (Block A)
def experiment {A : Type*} [DecidableEq A] (w : Block A → ℝ) (i : A) (B : Block A) : ℝ :=
  if i ∈ B.1 then w B else 0
def direction {A : Type*} [DecidableEq A] (U : Finset A) (B : Block A) : ℝ :=
  if B.1 = U then 1 else
    if B.1 ⊆ U ∧ B.1.card = 1 then (U.card : ℝ) - 2 else
      if B.1 ⊆ U ∧ B.1.card = 2 then -1 else 0

def plus {A : Type*} [DecidableEq A] (w : Block A → ℝ) (U : Finset A) (a : ℝ) : Block A → ℝ :=
  fun B => w B + a * direction U B

/-- Local CAR substitution preserves all pair summaries and has both exact directed
half-L1 deficiencies, with one attaining kernel in each direction for every state.
The lower bounds quantify over all stochastic kernels on all nonempty blocks. -/
theorem result {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (U : Finset A) (hm : 3 ≤ U.card) (a : ℝ) (ha : 0 ≤ a)
    (w : Block A → ℝ) (hw : ∀ B, 0 ≤ w B)
    (hrow : ∀ i, ∑ B, experiment w i B = 1)
    (hcap : ∀ B : Block A, B.1 ⊆ U → B.1.card = 2 → a ≤ w B) :
    let v := plus w U a
    let ep := a * ((U.card : ℝ) - 2) / (U.card : ℝ)
    let em := a * ((U.card : ℝ) - 2) / 2
    (∀ B, 0 ≤ v B) ∧
    (∀ i, ∑ B, experiment v i B = 1) ∧
    (∀ i j : A, i ≠ j →
      (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then v B else 0) =
      (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then w B else 0)) ∧
    finiteDeficiency (experiment w) (experiment v) = ENNReal.ofReal ep ∧
    finiteDeficiency (experiment v) (experiment w) = ENNReal.ofReal em ∧
    ∃ KP KM : FiniteMarkovKernel (Block A) (Block A),
      (∀ i, totalVariation (experiment w i) (channelOutput KP.1 (experiment v i)) =
        if i ∈ U then ep else 0) ∧
      (∀ i, totalVariation (experiment v i) (channelOutput KM.1 (experiment w i)) =
        if i ∈ U then em else 0) ∧
      (∀ K : FiniteMarkovKernel (Block A) (Block A),
        ep ≤ uniformSimulationError (experiment w) (experiment v) K) ∧
      (∀ K : FiniteMarkovKernel (Block A) (Block A),
        em ≤ uniformSimulationError (experiment v) (experiment w) K) := by
  classical
  let m : ℝ := U.card
  have hmR : 3 ≤ m := by dsimp [m]; exact_mod_cast hm
  have hm0 : 0 < m := by linarith only [hmR]
  have hm1 : 0 < m - 1 := by linarith only [hmR]
  have hm2 : 0 < m - 2 := by linarith only [hmR]
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  let u : Block A := ⟨U, hUne⟩
  let sing : A → Block A := fun i => ⟨{i}, Finset.singleton_nonempty i⟩
  let pair : Block A → Prop := fun B => B.1 ⊆ U ∧ B.1.card = 2
  let small : Block A → Prop := fun B => B.1 ⊆ U ∧ B.1.card = 1
  let q := (Finset.univ : Finset (Block A)).filter pair
  have hqsum (f : Finset A → ℝ) :
      (∑ B ∈ q, f B.1) = ∑ B ∈ U.powersetCard 2, f B := by
    apply Finset.sum_bij (fun B _ => B.1)
    · exact fun B hB => Finset.mem_powersetCard.mpr (Finset.mem_filter.mp hB).2
    · exact fun B hB C hC h => Subtype.ext h
    · intro B hB
      have hB' := Finset.mem_powersetCard.mp hB
      have hn : B.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨⟨B, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB'⟩, rfl⟩
    · exact fun B hB => rfl
  have hqcard : (q.card : ℝ) = m * (m - 1) / 2 := by
    have hnat : q.card = U.card.choose 2 := by
      have h := hqsum (fun _ => 1)
      simpa using h
    rw [hnat]
    simpa [m] using (show (U.card.choose 2 : ℝ) = m * (m - 1) / 2 by
      rw [Nat.cast_choose_two])
  have hqinc (i : A) (hi : i ∈ U) :
      (∑ B ∈ q, if i ∈ B.1 then (1 : ℝ) else 0) = m - 1 := by
    rw [hqsum (fun B => if i ∈ B then (1 : ℝ) else 0)]
    rw [← Finset.sum_filter]
    have hf : (U.powersetCard 2).filter (fun B => i ∈ B) =
        (U.powersetCard 2).filter (fun B => {i} ⊆ B) := by simp
    rw [hf, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_filter_powersetCard_subset {i} U 2 (by simpa using hi) (by simp)]
    simp [m, Nat.cast_sub (by omega : 1 ≤ U.card)]
  have hqboth (i j : A) (hi : i ∈ U) (hj : j ∈ U) (hij : i ≠ j) :
      (∑ B ∈ q, if i ∈ B.1 ∧ j ∈ B.1 then (1 : ℝ) else 0) = 1 := by
    rw [hqsum (fun B => if i ∈ B ∧ j ∈ B then (1 : ℝ) else 0)]
    rw [← Finset.sum_filter]
    have hf : (U.powersetCard 2).filter (fun B => i ∈ B ∧ j ∈ B) =
        (U.powersetCard 2).filter (fun B => {i,j} ⊆ B) := by
      ext B
      simp [Finset.insert_subset_iff]
    rw [hf, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_filter_powersetCard_subset {i,j} U 2 (by simp [Finset.insert_subset_iff, hi,hj]) (Finset.card_le_two)]
    simp [hij]
  have hqincAll (i : A) :
      (∑ B ∈ q, if i ∈ B.1 then (1 : ℝ) else 0) = if i ∈ U then m - 1 else 0 := by
    by_cases hi : i ∈ U
    · simpa [hi] using hqinc i hi
    · simp only [hi, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro B hB
      have hp := (Finset.mem_filter.mp hB).2
      simp [show i ∉ B.1 from fun h => hi (hp.1 h)]
  have hsmall (f : Block A → ℝ) :
      (∑ B, if small B then f B else 0) = ∑ j ∈ U, f (sing j) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun B hB => B.2.choose)
    · exact fun B hB => (Finset.mem_filter.mp hB).2.1 B.2.choose_spec
    · intro B hB C hC h
      apply Subtype.ext
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hB).2.2
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hC).2.2
      have hb' : B.2.choose = b := by simpa [hb] using B.2.choose_spec
      have hc' : C.2.choose = c := by simpa [hc] using C.2.choose_spec
      exact hb.trans ((congrArg (fun x : A => ({x} : Finset A)) (hb'.symm.trans (h.trans hc'))).trans hc.symm)
    · intro j hj
      refine ⟨sing j, ?_, ?_⟩
      · simp [small, sing, hj]
      · exact Finset.mem_singleton.mp ((sing j).2.choose_spec)
    · intro B hB
      congr 1
      apply Subtype.ext
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hB).2.2
      have hb' : B.2.choose = b := by simpa [hb] using B.2.choose_spec
      simpa [sing, hb'] using hb
  have hps (B : Block A) : ¬(pair B ∧ small B) := by
    dsimp [pair, small]
    omega
  have hpu : ¬ pair u := by dsimp [pair,u]; omega
  have hsu : ¬ small u := by dsimp [small,u]; omega
  have hsingU (i : A) : sing i ≠ u := by
    intro h
    have hh := congrArg (fun B : Block A => B.1.card) h
    simp [sing,u] at hh
    omega
  let r : Block A → ℝ := fun B => if pair B then a else 0
  let t : Block A → ℝ := fun B => (if B = u then a else 0) +
    (if small B then a * (m - 2) else 0)
  let b : Block A → ℝ := fun B => w B - r B
  let v : Block A → ℝ := fun B => b B + t B
  have hr0 (B : Block A) : 0 ≤ r B := by dsimp [r]; split <;> positivity
  have hb0 (B : Block A) : 0 ≤ b B := by
    dsimp [b,r]
    split
    · next h => exact sub_nonneg.mpr (hcap B h.1 h.2)
    · simpa using hw B
  have ht0 (B : Block A) : 0 ≤ t B :=
    add_nonneg (ite_nonneg ha le_rfl) (ite_nonneg (mul_nonneg ha hm2.le) le_rfl)
  have hv0 (B : Block A) : 0 ≤ v B := add_nonneg (hb0 B) (ht0 B)
  have hrrow (i : A) :
      (∑ B, experiment r i B) = if i ∈ U then a * (m - 1) else 0 := by
    have he : (∑ B, experiment r i B) =
        a * ∑ B ∈ q, if i ∈ B.1 then (1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
      simp only [q, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro B _
      simp only [experiment,r]
      split_ifs <;> ring
    rw [he, hqincAll]
    split_ifs <;> ring
  have htrow (i : A) :
      (∑ B, experiment t i B) = if i ∈ U then a * (m - 1) else 0 := by
    have he : (∑ B, experiment t i B) =
        (if i ∈ U then a else 0) +
          ∑ B, if small B then (if i ∈ B.1 then a * (m - 2) else 0) else 0 := by
      calc
        _ = (∑ B : Block A, if B = u then (if i ∈ U then a else 0) else 0) +
            ∑ B : Block A, if small B then (if i ∈ B.1 then a * (m - 2) else 0) else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro B _
          by_cases hB : B = u
          · subst B; simp [experiment,t,u]; split_ifs <;> ring
          · simp only [experiment,t,hB,↓reduceIte,zero_add]
            split_ifs <;> ring
        _ = _ := by simp
    rw [he, hsmall (fun B => if i ∈ B.1 then a * (m-2) else 0)]
    simp [sing]
    split_ifs <;> ring
  have hvrow (i : A) : ∑ B, experiment v i B = 1 := by
    have he : (∑ B, experiment v i B) =
        (∑ B, experiment w i B) - (∑ B, experiment r i B) +
          ∑ B, experiment t i B := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro B _
      simp only [experiment,v,b]
      split_ifs <;> ring
    rw [he,hrow,hrrow,htrow]
    ring
  have hsinginj : Function.Injective sing := by
    intro i j h
    have hh := congrArg Subtype.val h
    simpa [sing] using hh
  have hsmallD (B : Block A) (x : ℝ) :
      (∑ j ∈ U, if B = sing j then x else 0) = if small B then x else 0 := by
    by_cases hs : small B
    · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hs.2
      have hBj : B = sing j := Subtype.ext hj
      have hjU : j ∈ U := hs.1 (by simp [hj])
      subst B
      simp only [hs, ↓reduceIte, hsinginj.eq_iff]
      simp [hjU]
    · simp only [hs, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro j hj
      have hne : B ≠ sing j := by
        intro h
        subst B
        exact hs (by simp [small,sing,hj])
      simp [hne]
  let P : Block A → ℝ := fun C => if pair C then 2 / (m * (m - 1)) else 0
  let S : A → Block A → ℝ := fun j C => if pair C ∧ j ∈ C.1 then 1 / (m - 1) else 0
  have hP0 (C : Block A) : 0 ≤ P C := by dsimp [P]; split <;> positivity
  have hS0 (j : A) (C : Block A) : 0 ≤ S j C := by dsimp [S]; split <;> positivity
  have hPsum : ∑ C, P C = 1 := by
    dsimp only [P]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    change (q.card : ℝ) * (2 / (m * (m - 1))) = 1
    rw [hqcard]
    field_simp
  have hSsum (j : A) (hj : j ∈ U) : ∑ C, S j C = 1 := by
    have he : (∑ C, S j C) = (1 / (m-1)) *
        ∑ C ∈ q, if j ∈ C.1 then (1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
      simp only [q, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro C _
      dsimp [S]
      by_cases hp : pair C <;> by_cases hc : j ∈ C.1 <;> simp only [hp,hc, and_self, and_false, false_and, and_true,↓reduceIte,mul_zero,mul_one]
    rw [he,hqinc j hj]
    field_simp
  let fP : Block A → Block A → ℝ := fun B C =>
    (if B = u then a * P C else 0) +
    ∑ j ∈ U, if B = sing j then a * (m - 2) * S j C else 0
  have hfP0 (B C : Block A) : 0 ≤ fP B C :=
    add_nonneg (ite_nonneg (mul_nonneg ha (hP0 C)) le_rfl)
      (Finset.sum_nonneg fun j hj =>
        ite_nonneg (mul_nonneg (mul_nonneg ha hm2.le) (hS0 j C)) le_rfl)
  have hfPsum (B : Block A) : ∑ C, fP B C = t B := by
    simp only [fP, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    have he : (∑ j ∈ U, ∑ C, if B = sing j then a * (m - 2) * S j C else 0) =
        ∑ j ∈ U, if B = sing j then a * (m - 2) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : B = sing j
      · simp only [h, ↓reduceIte, ← Finset.mul_sum, hSsum j hj, mul_one]
      · simp [h]
    rw [he,hsmallD]
    dsimp [t]
    congr 1
    by_cases h : B = u
    · simp [h, ← Finset.mul_sum,hPsum]
    · simp [h]
  have hfPout (i : A) (C : Block A) :
      (∑ B, if i ∈ B.1 then fP B C else 0) =
        if i ∈ U then a * P C + a * (m-2) * S i C else 0 := by
    have he : (∑ B, if i ∈ B.1 then fP B C else 0) =
        (∑ B, if B = u then (if i ∈ U then a * P C else 0) else 0) +
        ∑ B, ∑ j ∈ U, if B = sing j then (if i = j then a*(m-2)*S j C else 0) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro B _
      dsimp [fP]
      by_cases hi : i ∈ B.1
      · simp only [hi, ↓reduceIte]
        congr 1
        · by_cases h : B = u
          · subst B; simp only [u] at hi ⊢; simp only [hi,↓reduceIte]
          · simp [h]
        · apply Finset.sum_congr rfl
          intro j hj
          by_cases h : B = sing j
          · subst B; simp only [sing,Finset.mem_singleton] at hi ⊢; simp only [hi,↓reduceIte]
          · simp [h]
      · simp only [hi, ↓reduceIte]
        have hfirst : (if B = u then (if i ∈ U then a * P C else 0) else 0) = 0 := by
          by_cases h : B = u
          · subst B; simp only [u] at hi ⊢; simp only [hi,↓reduceIte]
          · simp [h]
        rw [hfirst, zero_add]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        by_cases h : B = sing j
        · subst B; simp only [sing,Finset.mem_singleton] at hi ⊢; simp only [hi,↓reduceIte]
        · simp [h]
    rw [he,Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
    split_ifs <;> ring
  have makeKernel (x : Block A → ℝ) (hx : ∀ B, 0 ≤ x B)
      (f : Block A → Block A → ℝ) (hf : ∀ B C, 0 ≤ f B C)
      (hs : ∀ B, ∑ C, f B C = x B) :
      ∃ K : FiniteMarkovKernel (Block A) (Block A),
        ∀ B C, x B * K.1 B C = f B C := by
    have hz (B C : Block A) (h : x B = 0) : f B C = 0 := by
      apply le_antisymm _ (hf B C)
      have hh := Finset.single_le_sum (fun D (_ : D ∈ (Finset.univ : Finset (Block A))) => hf B D)
        (Finset.mem_univ C)
      simpa [hs,h] using hh
    let K : Block A → Block A → ℝ := fun B C =>
      if x B = 0 then (if B = C then 1 else 0) else f B C / x B
    have hK : IsRowStochastic K := by
      constructor
      · intro B C
        dsimp [K]
        split_ifs
        · norm_num
        · exact le_rfl
        · exact div_nonneg (hf B C) (hx B)
      · intro B
        by_cases h : x B = 0
        · simp [K,h]
        · simp [K,h,← Finset.sum_div,hs]
    refine ⟨⟨K,hK⟩, ?_⟩
    intro B C
    dsimp [K]
    by_cases h : x B = 0
    · simp [h,hz B C h]
    · simp only [h,↓reduceIte]
      field_simp
  let FP : Block A → Block A → ℝ := fun B C =>
    (if B = C then b B else 0) + fP B C
  have hFP0 (B C : Block A) : 0 ≤ FP B C :=
    add_nonneg (ite_nonneg (hb0 B) le_rfl) (hfP0 B C)
  have hFPsum (B : Block A) : ∑ C, FP B C = v B := by
    simp [FP,Finset.sum_add_distrib,hfPsum,v]
  obtain ⟨KP,hKP⟩ := makeKernel v hv0 FP hFP0 hFPsum
  have hKPout (i : A) (C : Block A) :
      channelOutput KP.1 (experiment v i) C = experiment b i C +
        (if i ∈ U then a * P C + a*(m-2)*S i C else 0) := by
    have he : channelOutput KP.1 (experiment v i) C =
        ∑ B, if i ∈ B.1 then FP B C else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      dsimp only [experiment]
      split_ifs
      · exact hKP B C
      · ring
    rw [he]
    have he' : (∑ B, if i ∈ B.1 then FP B C else 0) =
        experiment b i C + ∑ B, if i ∈ B.1 then fP B C else 0 := by
      calc
        _ = (∑ B, if B = C then experiment b i C else 0) +
            ∑ B, if i ∈ B.1 then fP B C else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro B _
          dsimp [FP,experiment]
          by_cases h : B = C
          · subst B
            by_cases hi : i ∈ C.1 <;> simp only [hi,↓reduceIte,add_zero]
          · by_cases hi : i ∈ B.1 <;> simp only [h,hi,↓reduceIte,zero_add,add_zero]
        _ = _ := by simp
    rw [he',hfPout]
  let eP := a * (m-2) / m
  let dP := a * (m-2) / (m*(m-1))
  let xP := a * 2 / (m*(m-1))
  have hdP : 0 ≤ dP := div_nonneg (mul_nonneg ha hm2.le) (mul_nonneg hm0.le hm1.le)
  have hxP : 0 ≤ xP := div_nonneg (mul_nonneg ha (by norm_num)) (mul_nonneg hm0.le hm1.le)
  have hPdiff (i : A) (C : Block A) :
      experiment w i C - channelOutput KP.1 (experiment v i) C =
        if i ∈ U then (if pair C then (if i ∈ C.1 then dP else -xP) else 0) else 0 := by
    rw [hKPout]
    dsimp [experiment,b,r,P,S]
    by_cases hi : i ∈ U
    · by_cases hp : pair C
      · by_cases hc : i ∈ C.1
        · simp [hi,hp,hc,dP,xP]
          field_simp
          ring
        · simp [hi,hp,hc,dP,xP]
          ring
      · simp [hi,hp]
    · have hn : pair C → i ∉ C.1 := fun hp hc => hi (hp.1 hc)
      by_cases hp : pair C
      · simp [hi,hp,hn hp]
      · simp [hi,hp]
  have hPTV (i : A) :
      totalVariation (experiment w i) (channelOutput KP.1 (experiment v i)) =
        if i ∈ U then eP else 0 := by
    unfold totalVariation
    simp only [hPdiff]
    by_cases hi : i ∈ U
    · simp only [hi,↓reduceIte]
      have he : (∑ C : Block A, |if pair C then (if i ∈ C.1 then dP else -xP) else 0|) =
          (q.card : ℝ) * xP + (m-1) * (dP-xP) := by
        calc
          _ = (∑ C ∈ q, (xP + (if i ∈ C.1 then (1:ℝ) else 0) * (dP-xP))) := by
            simp only [q,Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro C _
            split_ifs <;> simp only [abs_of_nonneg hdP, abs_neg, abs_of_nonneg hxP, abs_zero, one_mul,zero_mul,add_zero] <;> ring
          _ = _ := by
            rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
              ← Finset.sum_mul,hqinc i hi]
      rw [he,hqcard]
      dsimp [eP,dP,xP]
      field_simp
      ring
    · simp [hi]
  have hqboth' (i j : A) (hi : i ∈ U) (hj : j ∈ U) :
      (∑ B ∈ q, if i ∈ B.1 ∧ j ∈ B.1 then (1 : ℝ) else 0) =
        if i = j then m-1 else 1 := by
    by_cases hij : i = j
    · subst j; simpa using hqinc i hi
    · simpa [hij] using hqboth i j hi hj hij
  let cM := a*(m-2)/(2*(m-1))
  let eM := a*(m-2)/2
  have hcM : 0 ≤ cM := div_nonneg (mul_nonneg ha hm2.le) (mul_nonneg (by norm_num) hm1.le)
  have heM : 0 ≤ eM := div_nonneg (mul_nonneg ha hm2.le) (by norm_num)
  let fM : Block A → Block A → ℝ := fun B C => if pair B then
    (if C = u then a/(m-1) else 0) +
      ∑ j ∈ U, if j ∈ B.1 ∧ C = sing j then cM else 0
    else 0
  have hfM0 (B C : Block A) : 0 ≤ fM B C :=
    ite_nonneg (add_nonneg (ite_nonneg (div_nonneg ha hm1.le) le_rfl)
      (Finset.sum_nonneg fun j hj => ite_nonneg hcM le_rfl)) le_rfl
  have hfMsum (B : Block A) : ∑ C, fM B C = r B := by
    by_cases hp : pair B
    · simp only [fM,r,hp,↓reduceIte,Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      have he : (∑ j ∈ U, ∑ C : Block A, if j ∈ B.1 ∧ C = sing j then cM else 0) =
          2*cM := by
        calc
          _ = ∑ j ∈ U, if j ∈ B.1 then cM else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases h : j ∈ B.1 <;> simp [h]
          _ = _ := by
            rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr hp.1]
            simp [hp.2]
      rw [he]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
      dsimp [cM]
      field_simp
      ring
    · simp [fM,r,hp]
  have hfMout (i : A) (C : Block A) :
      (∑ B, if i ∈ B.1 then fM B C else 0) = if i ∈ U then
        (if C = u then a else 0) +
          ∑ j ∈ U, if C = sing j then (if i = j then eM else cM) else 0
        else 0 := by
    by_cases hi : i ∈ U
    · simp only [hi,↓reduceIte]
      have he : (∑ B, if i ∈ B.1 then fM B C else 0) =
          (∑ B ∈ q, (if i ∈ B.1 then (1:ℝ) else 0) * (if C=u then a/(m-1) else 0)) +
          ∑ j ∈ U, (∑ B ∈ q, if i ∈ B.1 ∧ j ∈ B.1 then (1:ℝ) else 0) *
            (if C = sing j then cM else 0) := by
        rw [show (∑ j ∈ U, (∑ B ∈ q, if i ∈ B.1 ∧ j ∈ B.1 then (1:ℝ) else 0) *
            (if C = sing j then cM else 0)) =
            ∑ B ∈ q, ∑ j ∈ U, (if i ∈ B.1 ∧ j ∈ B.1 then (1:ℝ) else 0) *
              (if C = sing j then cM else 0) by simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]]
        rw [← Finset.sum_add_distrib]
        simp only [q,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro B _
        by_cases hp : pair B
        · by_cases hib : i ∈ B.1
          · simp only [fM,hp,hib,↓reduceIte,one_mul,true_and]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hjB : j ∈ B.1 <;> by_cases hC : C=sing j <;> simp [hjB,hC]
          · simp [fM,hp,hib]
        · simp [fM,hp]
      rw [he,← Finset.sum_mul,hqinc i hi]
      congr 1
      · by_cases h : C=u <;> simp only [h,↓reduceIte,mul_zero]
        field_simp
      · apply Finset.sum_congr rfl
        intro j hj
        rw [hqboth' i j hi hj]
        by_cases h : C = sing j <;> by_cases hij : i=j <;>
          simp only [h,hij,↓reduceIte,mul_zero,one_mul]
        dsimp [eM,cM]
        field_simp
    · simp only [hi,↓reduceIte]
      apply Finset.sum_eq_zero
      intro B _
      by_cases hib : i ∈ B.1
      · have hp : ¬pair B := fun h => hi (h.1 hib)
        simp [fM,hib,hp]
      · simp [hib]
  let FM : Block A → Block A → ℝ := fun B C =>
    (if B = C then b B else 0) + fM B C
  have hFM0 (B C : Block A) : 0 ≤ FM B C :=
    add_nonneg (ite_nonneg (hb0 B) le_rfl) (hfM0 B C)
  have hFMsum (B : Block A) : ∑ C, FM B C = w B := by
    simp [FM,Finset.sum_add_distrib,hfMsum,b]
  obtain ⟨KM,hKM⟩ := makeKernel w hw FM hFM0 hFMsum
  have hKMout (i : A) (C : Block A) :
      channelOutput KM.1 (experiment w i) C = experiment b i C +
        (if i ∈ U then (if C = u then a else 0) +
          ∑ j ∈ U, if C = sing j then (if i = j then eM else cM) else 0 else 0) := by
    have he : channelOutput KM.1 (experiment w i) C =
        ∑ B, if i ∈ B.1 then FM B C else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      dsimp only [experiment]
      split_ifs
      · exact hKM B C
      · ring
    rw [he]
    have he' : (∑ B, if i ∈ B.1 then FM B C else 0) =
        experiment b i C + ∑ B, if i ∈ B.1 then fM B C else 0 := by
      calc
        _ = (∑ B, if B = C then experiment b i C else 0) +
            ∑ B, if i ∈ B.1 then fM B C else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro B _
          dsimp [FM,experiment]
          by_cases h : B = C
          · subst B
            by_cases hi : i ∈ C.1 <;> simp only [hi,↓reduceIte,add_zero]
          · by_cases hi : i ∈ B.1 <;> simp only [h,hi,↓reduceIte,zero_add,add_zero]
        _ = _ := by simp
    rw [he',hfMout]
  have htcoord (i : A) (C : Block A) : experiment t i C =
      if i ∈ U then (if C=u then a else 0) +
        (if C=sing i then a*(m-2) else 0) else 0 := by
    have he : (if small C then (if i ∈ C.1 then a*(m-2) else 0) else 0) =
        if i ∈ U ∧ C=sing i then a*(m-2) else 0 := by
      by_cases hs : small C
      · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hs.2
        have hjU : j ∈ U := hs.1 (by simp [hj])
        have he : C=sing j := Subtype.ext hj
        subst C
        simp only [hs,↓reduceIte,sing,Finset.mem_singleton]
        by_cases hij : i=j
        · subst j; simp [hjU]
        · have hne : (⟨{j},Finset.singleton_nonempty j⟩ : Block A) ≠ ⟨{i},Finset.singleton_nonempty i⟩ := by
            intro h; have hh := congrArg Subtype.val h
            exact hij (by simpa using hh.symm)
          simp [hij,hne]
      · have hn : i ∈ U → C ≠ sing i := by
          intro hi h
          subst C
          exact hs (by simp [small,sing,hi])
        by_cases hi : i ∈ U <;> simp [hs,hi,hn]
    have he' : experiment t i C =
        (if i ∈ U ∧ C=u then a else 0) +
          (if small C then (if i ∈ C.1 then a*(m-2) else 0) else 0) := by
      by_cases hC : C=u
      · subst C
        simp only [experiment,t,hsu,↓reduceIte,add_zero]
        change (if i ∈ U then a else 0) = if i ∈ U ∧ True then a else 0
        simp
      · dsimp only [experiment,t]; simp only [hC,↓reduceIte,zero_add,and_false]
        split_ifs <;> ring
    rw [he',he]
    by_cases hi : i ∈ U <;> simp only [hi,true_and,false_and,↓reduceIte,zero_add]
  have hMdiff (i : A) (C : Block A) :
      experiment v i C - channelOutput KM.1 (experiment w i) C =
        if i ∈ U then (if C=sing i then eM else 0) -
          ∑ j ∈ U, if i ≠ j ∧ C=sing j then cM else 0 else 0 := by
    rw [hKMout]
    have hv : experiment v i C = experiment b i C + experiment t i C := by
      dsimp only [experiment,v]; split_ifs <;> ring
    rw [hv,htcoord]
    by_cases hi : i ∈ U
    · simp only [hi,↓reduceIte]
      have hs : (∑ j ∈ U, if C=sing j then (if i=j then eM else cM) else 0) =
          (if C=sing i then eM else 0) + ∑ j ∈ U, if i ≠ j ∧ C=sing j then cM else 0 := by
        calc
          _ = (∑ j ∈ U, if i=j then (if C=sing i then eM else 0) else 0) +
              ∑ j ∈ U, if i ≠ j ∧ C=sing j then cM else 0 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : i=j
            · subst j; simp
            · simp [hij]
          _ = _ := by simp [hi]
      rw [hs]
      dsimp only [eM]
      split_ifs <;> ring
    · simp [hi]
  have hMTV (i : A) :
      totalVariation (experiment v i) (channelOutput KM.1 (experiment w i)) =
        if i ∈ U then eM else 0 := by
    unfold totalVariation
    simp only [hMdiff]
    by_cases hi : i ∈ U
    · simp only [hi,↓reduceIte]
      have habs (C : Block A) :
          |(if C=sing i then eM else 0) - ∑ j ∈ U, if i ≠ j ∧ C=sing j then cM else 0| =
          (if C=sing i then eM else 0) + ∑ j ∈ U, if i ≠ j ∧ C=sing j then cM else 0 := by
        by_cases hC : C=sing i
        · subst C
          have hz : (∑ j ∈ U, if i ≠ j ∧ sing i=sing j then cM else 0)=0 := by
            simp [hsinginj.eq_iff]
          simp [hz,abs_of_nonneg heM]
        · have hs : 0 ≤ ∑ j ∈ U, if i ≠ j ∧ C=sing j then cM else 0 := by
            apply Finset.sum_nonneg; intro j hj; split_ifs <;> positivity
          simp [hC,abs_of_nonneg hs]
      simp only [habs,Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      have hs : (∑ j ∈ U, ∑ C : Block A, if i ≠ j ∧ C=sing j then cM else 0) = (m-1)*cM := by
        calc
          _ = ∑ j ∈ U, if i=j then 0 else cM := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : i=j <;> simp [hij]
          _ = _ := by
            rw [Finset.sum_ite]
            simp [eq_comm,Finset.filter_ne,Finset.card_erase_of_mem hi,m,Nat.cast_sub (by omega : 1 ≤ U.card)]
      rw [hs]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
      dsimp only [eM,cM]
      field_simp
      ring
    · simp [hi]
  let I : Block A → Finset A := fun B => B.1 ∩ U
  let k : Block A → ℝ := fun B => (I B).card
  have hk0 (B : Block A) : 0 ≤ k B := Nat.cast_nonneg _
  let s : Block A → ℝ := fun B => 2 / max 2 (k B)
  have hs0 (B : Block A) : 0 ≤ s B := div_nonneg (by norm_num) ((le_max_left _ _).trans' (by norm_num))
  have hs1 (B : Block A) : s B ≤ 1 := by
    apply (div_le_one (by exact lt_of_lt_of_le (by norm_num) (le_max_left (2:ℝ) (k B)))).mpr
    exact le_max_left _ _
  have hks (B : Block A) : k B * s B ≤ 2 := by
    dsimp only [s]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by exact lt_of_lt_of_le (by norm_num) (le_max_left (2:ℝ) (k B)))).mpr
    nlinarith only [le_max_right (2:ℝ) (k B)]
  let ellP : A → Block A → ℝ := fun i C =>
    if i ∈ U then 1 - (if i ∈ C.1 then s C else 0) else 0
  let costP : Block A → ℝ := fun B => max (k B - 2) 0
  have hellP (i : A) (C : Block A) : 0 ≤ ellP i C ∧ ellP i C ≤ 1 := by
    dsimp only [ellP]
    split_ifs <;> constructor <;> linarith only [hs0 C,hs1 C]
  have hPcost (B C : Block A) : costP B ≤ ∑ i ∈ I B, ellP i C := by
    have he : (∑ i ∈ I B, ellP i C) = k B - ((I B ∩ C.1).card : ℝ) * s C := by
      calc
        _ = ∑ i ∈ I B, (1 - (if i ∈ C.1 then s C else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [ellP, (Finset.mem_inter.mp hi).2,↓reduceIte]
        _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_ite_mem]; simp [k]
    have hcount : ((I B ∩ C.1).card : ℝ) ≤ k C := by
      apply Nat.cast_le.mpr
      exact Finset.card_le_card fun i hi =>
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).2,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).2⟩
    apply max_le
    · rw [he]
      have hh := (mul_le_mul_of_nonneg_right hcount (hs0 C)).trans (hks C)
      linarith only [hh]
    · exact Finset.sum_nonneg fun i hi => (hellP i C).1
  have hPeq (B : Block A) : (∑ i ∈ I B, ellP i B) = costP B := by
    have he : (∑ i ∈ I B, ellP i B) = k B * (1 - s B) := by
      calc
        _ = ∑ i ∈ I B, (1 - s B) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [ellP,(Finset.mem_inter.mp hi).1,(Finset.mem_inter.mp hi).2,↓reduceIte]
        _ = _ := by simp [k]; ring
    rw [he]
    dsimp only [costP,s]
    by_cases hk : k B ≤ 2
    · rw [max_eq_left hk,max_eq_right (by linarith only [hk])]
      norm_num
    · have hk' : 2 ≤ k B := le_of_not_ge hk
      rw [max_eq_right hk',max_eq_left (by linarith only [hk'])]
      field_simp
  let ellM : A → Block A → ℝ := fun i C => if i ∈ U then
    (if (I C).card = 1 then (if i ∈ C.1 then 0 else 1) else 1/2) else 0
  let costM : Block A → ℝ := fun B => if (I B).card ≤ 1 then 0 else k B / 2
  have hellM (i : A) (C : Block A) : 0 ≤ ellM i C ∧ ellM i C ≤ 1 := by
    dsimp only [ellM]; split_ifs <;> norm_num
  have hMcost (B C : Block A) : costM B ≤ ∑ i ∈ I B, ellM i C := by
    by_cases hB : (I B).card ≤ 1
    · simp only [costM,hB,↓reduceIte]
      exact Finset.sum_nonneg fun i hi => (hellM i C).1
    · have hkB : 2 ≤ k B := by dsimp [k]; exact_mod_cast (show 2 ≤ (I B).card by omega)
      simp only [costM,hB,↓reduceIte]
      by_cases hC : (I C).card = 1
      · have he : (∑ i ∈ I B, ellM i C) = k B - ((I B ∩ C.1).card : ℝ) := by
          calc
            _ = ∑ i ∈ I B, (1 - if i ∈ C.1 then (1:ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp only [ellM,(Finset.mem_inter.mp hi).2,hC,↓reduceIte]
              split_ifs <;> ring
            _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_ite_mem]; simp [k]
        have hn : (I B ∩ C.1).card ≤ 1 := by
          rw [← hC]
          exact Finset.card_le_card fun i hi =>
            Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).2,
              (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).2⟩
        have hnR : ((I B ∩ C.1).card : ℝ) ≤ 1 := by exact_mod_cast hn
        rw [he]
        linarith only [hnR,hkB]
      · have he : (∑ i ∈ I B, ellM i C) = k B / 2 := by
          calc
            _ = ∑ i ∈ I B, (1/2 : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp only [ellM,(Finset.mem_inter.mp hi).2,hC,↓reduceIte]
            _ = _ := by simp [k,div_eq_mul_inv]
        exact le_of_eq he.symm
  have hMeq (B : Block A) : (∑ i ∈ I B, ellM i B) = costM B := by
    by_cases h0 : (I B).card = 0
    · have hz := Finset.card_eq_zero.mp h0
      simp [hz,costM]
    · by_cases h1 : (I B).card = 1
      · have hz : (∑ i ∈ I B, ellM i B)=0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp only [ellM,(Finset.mem_inter.mp hi).1,(Finset.mem_inter.mp hi).2,h1,↓reduceIte]
        rw [hz]; simp [costM,h1]
      · have hn : ¬(I B).card ≤ 1 := by omega
        simp only [costM,hn,↓reduceIte]
        calc
          _ = ∑ i ∈ I B, (1/2 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [ellM,(Finset.mem_inter.mp hi).2,h1,↓reduceIte]
          _ = _ := by simp [k,div_eq_mul_inv]
  have hcut (B : Block A) (f : A → ℝ) :
      (∑ i ∈ U, if i ∈ B.1 then f i else 0) = ∑ i ∈ I B, f i := by
    rw [Finset.sum_ite_mem]
    simp only [I,Finset.inter_comm]
  have hcostSwap (x : Block A → ℝ) (D : Block A → Block A → ℝ)
      (ell : A → Block A → ℝ) :
      (∑ i ∈ U, ∑ C, channelOutput D (experiment x i) C * ell i C) =
        ∑ B, x B * ∑ C, D B C * ∑ i ∈ I B, ell i C := by
    simp only [channelOutput,Finset.sum_mul]
    calc
      _ = ∑ i ∈ U, ∑ B : Block A, ∑ C : Block A,
          experiment x i B * D B C * ell i C := by
        exact Finset.sum_congr rfl fun i hi => Finset.sum_comm
      _ = ∑ B : Block A, ∑ i ∈ U, ∑ C : Block A,
          experiment x i B * D B C * ell i C := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        rw [Finset.sum_comm,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        rw [← mul_assoc, Finset.mul_sum]
        rw [← hcut B (fun i => (x B * D B C) * ell i C)]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [experiment]
        split_ifs <;> ring
  let ID : Block A → Block A → ℝ := fun B C => if B=C then 1 else 0
  have hID : IsRowStochastic ID := by
    constructor
    · intro B C; dsimp only [ID]; split_ifs <;> norm_num
    · intro B; simp [ID]
  have hIDout (x : Block A → ℝ) : channelOutput ID x = x := by
    funext C
    simp [ID,channelOutput]
  have htransport (x y : Block A → ℝ)
      (hx : ∀ B, 0 ≤ x B) (hy : ∀ B, 0 ≤ y B)
      (hxrow : ∀ i, ∑ B, experiment x i B = 1)
      (hyrow : ∀ i, ∑ B, experiment y i B = 1)
      (ell : A → Block A → ℝ) (c : Block A → ℝ)
      (hell : ∀ i C, 0 ≤ ell i C ∧ ell i C ≤ 1)
      (hc : ∀ B C, c B ≤ ∑ i ∈ I B, ell i C)
      (he : ∀ B, (∑ i ∈ I B, ell i B) = c B)
      (K : FiniteMarkovKernel (Block A) (Block A)) :
      (∑ B, x B * c B) - (∑ B, y B * c B) ≤
        m * uniformSimulationError (experiment y) (experiment x) K := by
    have hxs : IsRowStochastic (experiment x) :=
      ⟨fun i B => ite_nonneg (hx B) le_rfl, hxrow⟩
    have hys : IsRowStochastic (experiment y) :=
      ⟨fun i B => ite_nonneg (hy B) le_rfl, hyrow⟩
    have ht := bounded_loss_risk_stability_of_simulator
      (experiment x) (experiment y) K.1 ID ell
      (uniformSimulationError (experiment y) (experiment x) K)
      hxs hys K.2 hID hell le_rfl
    have ht' : ∀ i, (∑ C, channelOutput K.1 (experiment x i) C * ell i C) ≤
        (∑ C, experiment y i C * ell i C) +
          uniformSimulationError (experiment y) (experiment x) K := by
      simpa only [hIDout] using ht.2
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ U) => ht' i)
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
    rw [hcostSwap x K.1 ell] at hsum
    have htarget : (∑ i ∈ U, ∑ C, experiment y i C * ell i C) = ∑ B, y B * c B := by
      have hh := hcostSwap y ID ell
      simp only [hIDout] at hh
      rw [hh]
      apply Finset.sum_congr rfl
      intro B _
      congr 1
      simp [ID,he]
    rw [htarget] at hsum
    have hsrc : (∑ B, x B * c B) ≤
        ∑ B, x B * ∑ C, K.1 B C * ∑ i ∈ I B, ell i C := by
      apply Finset.sum_le_sum
      intro B _
      apply mul_le_mul_of_nonneg_left _ (hx B)
      calc
        c B = ∑ C, K.1 B C * c B := by rw [← Finset.sum_mul,K.2.2,one_mul]
        _ ≤ _ := Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hc B C) (K.2.1 B C)
    change _ ≤ m * _
    change _ ≤ _ + m * _ at hsum
    linarith only [hsrc,hsum]
  have hgap (c : Block A → ℝ) (cu cp : ℝ)
      (hu : c u = cu) (hs : ∀ j ∈ U, c (sing j) = 0)
      (hp : ∀ B, pair B → c B = cp) :
      (∑ B, v B * c B) - (∑ B, w B * c B) = a * cu - (q.card : ℝ) * a * cp := by
    have ht : (∑ B, t B * c B) = a * cu := by
      have he : (∑ B, t B * c B) =
          (∑ B, if B=u then a*c u else 0) +
          ∑ B, if small B then a*(m-2)*c B else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro B _
        dsimp only [t]
        by_cases hB : B=u
        · subst B; split_ifs <;> ring
        · simp only [hB,↓reduceIte,zero_add]; split_ifs <;> ring
      rw [he,hsmall (fun B => a*(m-2)*c B)]
      have hz : (∑ j ∈ U, a*(m-2)*c (sing j))=0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hs j hj,mul_zero]
      simp [hu,hz]
    have hr : (∑ B, r B * c B) = (q.card : ℝ)*a*cp := by
      calc
        _ = ∑ B ∈ q, a*cp := by
          simp only [q,Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro B _
          by_cases h : pair B <;> simp [r,h,hp B]
        _ = _ := by simp; ring
    have he : (∑ B, v B*c B) - (∑ B, w B*c B) =
        (∑ B, t B*c B) - (∑ B, r B*c B) := by
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro B _
      dsimp only [v,b]
      ring
    rw [he,ht,hr]
  have hkU : k u = m := by simp [k,I,u,m]
  have hkS (j : A) (hj : j ∈ U) : k (sing j) = 1 := by simp [k,I,sing,hj]
  have hkQ (B : Block A) (hB : pair B) : k B = 2 := by
    simp [k,I,Finset.inter_eq_left.mpr hB.1,hB.2]
  have hgapP : (∑ B, v B*costP B) - (∑ B, w B*costP B) = m*eP := by
    rw [hgap costP (m-2) 0]
    · dsimp [eP]; field_simp; ring
    · simp only [costP,hkU,max_eq_left hm2.le]
    · intro j hj; simp [costP,hkS j hj]
    · intro B hB; simp [costP,hkQ B hB]
  have hgapM : (∑ B, w B*costM B) - (∑ B, v B*costM B) = m*eM := by
    have hh := hgap costM (m/2) 1 (by
        simp [costM,I,u,k,m,show ¬U.card ≤ 1 by omega])
      (by intro j hj; simp [costM,I,sing,hj])
      (by intro B hB; simp [costM,I,Finset.inter_eq_left.mpr hB.1,hB.2,k])
    rw [hqcard] at hh
    dsimp only [eM]
    linear_combination -hh
  have hLowerP (K : FiniteMarkovKernel (Block A) (Block A)) :
      eP ≤ uniformSimulationError (experiment w) (experiment v) K := by
    have hh := htransport v w hv0 hw hvrow hrow ellP costP hellP hPcost hPeq K
    rw [hgapP] at hh
    exact le_of_mul_le_mul_left hh hm0
  have hLowerM (K : FiniteMarkovKernel (Block A) (Block A)) :
      eM ≤ uniformSimulationError (experiment v) (experiment w) K := by
    have hh := htransport w v hw hv0 hrow hvrow ellM costM hellM hMcost hMeq K
    rw [hgapM] at hh
    exact le_of_mul_le_mul_left hh hm0
  have hpairRead (i j : A) (hij : i ≠ j) :
      (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then v B else 0) =
        ∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then w B else 0 := by
    have hsmallzero (B : Block A) (hs : small B) : ¬(i ∈ B.1 ∧ j ∈ B.1) := by
      obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hs.2
      simp only [hl,Finset.mem_singleton]
      exact fun hh => hij (hh.1.trans hh.2.symm)
    have ht : (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then t B else 0) =
        if i ∈ U ∧ j ∈ U then a else 0 := by
      calc
        _ = ∑ B : Block A, if B=u then (if i ∈ U ∧ j ∈ U then a else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro B _
          by_cases hB : B=u
          · subst B
            simp only [t,hsu,↓reduceIte,add_zero,u]
          · dsimp only [t]
            simp only [hB,↓reduceIte,zero_add]
            by_cases hs : small B
            · simp only [hs,hsmallzero B hs,↓reduceIte]
            · simp only [hs,↓reduceIte,ite_self]
        _ = _ := by simp
    have hr : (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then r B else 0) =
        if i ∈ U ∧ j ∈ U then a else 0 := by
      have he : (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then r B else 0) =
          a * ∑ B ∈ q, if i ∈ B.1 ∧ j ∈ B.1 then (1:ℝ) else 0 := by
        rw [Finset.mul_sum]
        simp only [q,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro B _
        dsimp only [r]
        split_ifs <;> ring
      rw [he]
      by_cases hi : i ∈ U
      · by_cases hj : j ∈ U
        · rw [hqboth i j hi hj hij]; simp [hi,hj]
        · have hz : (∑ B ∈ q, if i ∈ B.1 ∧ j ∈ B.1 then (1:ℝ) else 0)=0 := by
            apply Finset.sum_eq_zero
            intro B hB
            have hnot : j ∉ B.1 := fun hb => hj ((Finset.mem_filter.mp hB).2.1 hb)
            simp only [hnot,and_false,↓reduceIte]
          simp [hz,hj]
      · have hz : (∑ B ∈ q, if i ∈ B.1 ∧ j ∈ B.1 then (1:ℝ) else 0)=0 := by
          apply Finset.sum_eq_zero
          intro B hB
          have hnot : i ∉ B.1 := fun hb => hi ((Finset.mem_filter.mp hB).2.1 hb)
          simp only [hnot,false_and,↓reduceIte]
        simp [hz,hi]
    have he : (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then v B else 0) =
        (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then w B else 0) -
        (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then r B else 0) +
        (∑ B : Block A, if i ∈ B.1 ∧ j ∈ B.1 then t B else 0) := by
      rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro B _
      dsimp only [v,b]
      by_cases hi : i ∈ B.1 ∧ j ∈ B.1
      · simp only [hi,and_self,↓reduceIte]
      · simp only [hi,↓reduceIte,sub_zero,add_zero]
    rw [he,hr,ht,sub_add_cancel]
  have heP0 : 0 ≤ eP := div_nonneg (mul_nonneg ha hm2.le) hm0.le
  have hErr (x y : Block A → ℝ) (K : FiniteMarkovKernel (Block A) (Block A))
      (e : ℝ) (he0 : 0 ≤ e)
      (he : ∀ i, totalVariation (experiment y i) (channelOutput K.1 (experiment x i)) =
        if i ∈ U then e else 0) : uniformSimulationError (experiment y) (experiment x) K = e := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rw [he]
      split_ifs
      · exact le_rfl
      · exact he0
    · obtain ⟨i,hi⟩ := hUne
      have hh := Finset.le_sup' (fun i => totalVariation (experiment y i) (channelOutput K.1 (experiment x i)))
        (Finset.mem_univ i)
      exact (show e = totalVariation (experiment y i) (channelOutput K.1 (experiment x i)) by
        rw [he,if_pos hi]).trans_le hh
  have hDefP : finiteDeficiency (experiment w) (experiment v) = ENNReal.ofReal eP := by
    exact le_antisymm ((iInf_le _ KP).trans_eq (by rw [hErr v w KP eP heP0 hPTV]))
      (le_iInf fun K => ENNReal.ofReal_le_ofReal (hLowerP K))
  have hDefM : finiteDeficiency (experiment v) (experiment w) = ENNReal.ofReal eM := by
    exact le_antisymm ((iInf_le _ KM).trans_eq (by rw [hErr w v KM eM heM hMTV]))
      (le_iInf fun K => ENNReal.ofReal_le_ofReal (hLowerM K))
  have hvEq : v = plus w U a := by
    funext B
    change w B - (if pair B then a else 0) +
      ((if B=u then a else 0) + (if small B then a*(m-2) else 0)) =
        w B + a*(if B.1=U then 1 else if small B then m-2 else if pair B then -1 else 0)
    by_cases hu : B=u
    · subst B
      simp only [hpu,hsu,↓reduceIte,sub_zero,add_zero,u]
      ring
    · have hu' : B.1 ≠ U := fun h => hu (Subtype.ext h)
      by_cases hp : pair B
      · have hs : ¬small B := fun h => hps B ⟨hp,h⟩
        simp only [hu,hu',hp,hs,↓reduceIte,zero_add,add_zero]
        ring
      · by_cases hs : small B
        · simp only [hu,hu',hp,hs,↓reduceIte,zero_add,sub_zero]
        · simp only [hu,hu',hp,hs,↓reduceIte,zero_add,sub_zero,add_zero,mul_zero]
  dsimp only
  rw [← hvEq]
  exact ⟨hv0,hvrow,hpairRead,hDefP,hDefM,KP,KM,hPTV,hMTV,hLowerP,hLowerM⟩
#print axioms result
end D5.S3.Estimation.DecisionRisk.LocalCARDeficiency
