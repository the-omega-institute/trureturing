/- GID: D5/S1/Words/AdmissibleWords/KBonacciActualSaturation
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciActualSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary words avoiding k ones have a sharp single-probe quotient threshold. -/

import D5.S0.Tower.DBonacci.Substitution
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciActualSaturation

open Polynomial Finset
open D5.S0.Tower.DBonacci.Names D5.S0.Tower.DBonacci.Substitution

/-- The original single-probe polynomial over the two-element coefficient ring. -/
def phi (a : ℕ) : (ZMod 2)[X] := X ^ a - ∑ j ∈ range a, X ^ j

/-- A coefficient vector is read with its constant coefficient first. -/
def vectorPolynomial {n : ℕ} (c : Fin n → ZMod 2) : (ZMod 2)[X] :=
  ∑ j : Fin n, monomial j.val (c j)

/-- Both false and true occupy one actual position, including all zero positions. -/
def wordPolynomial {n : ℕ} (w : Fin n → Bool) : (ZMod 2)[X] :=
  vectorPolynomial (fun j => if w j then 1 else 0)

/-- The accepted part of the exact-length observation image in the original quotient. -/
def actualImage (k a n : ℕ) : Set (AdjoinRoot (phi a)) :=
  {y | ∃ w : Fin n → Bool,
    DBonacciAdmissible k n w ∧ AdjoinRoot.mk (phi a) (wordPolynomial w) = y}

/-- The sharp threshold, with every padding zero charged as one bit. -/
def threshold (k a : ℕ) : ℕ :=
  if a < k then a else max (a + 1) (2 * a - 2 * k + 3)

/-- All fixed orders have exactly the stated sharp threshold in the original quotient. -/
theorem kbonacci_actual_saturation (k a : ℕ) (hk : 2 ≤ k) (ha : 2 ≤ a) :
    Nat.card (AdjoinRoot (phi a)) = 2 ^ a ∧
      ∀ n : ℕ, actualImage k a n = Set.univ ↔ threshold k a ≤ n := by
  classical
  have hphi : phi a = ∑ j ∈ range (a + 1), (X : (ZMod 2)[X]) ^ j := by
    simp only [phi, sum_range_succ]
    rw [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hmonic : (phi a).Monic := by
    rw [hphi]
    exact monic_geom_sum_X (by omega)
  have hdegree : (phi a).natDegree = a := by
    have hlow : (∑ j ∈ range a, (X : (ZMod 2)[X]) ^ j).degree < a := by
      simpa only [← Fin.sum_univ_eq_sum_range, C_1, one_mul] using
        degree_sum_fin_lt (fun _ : Fin a => (1 : ZMod 2))
    calc
      (phi a).natDegree = ((X : (ZMod 2)[X]) ^ a).natDegree :=
        natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (by simpa using hlow))
      _ = a := natDegree_X_pow a
  have hcard : Nat.card (AdjoinRoot (phi a)) = 2 ^ a := by
    rw [Nat.card_congr (AdjoinRoot.powerBasisAux' hmonic).equivFun.toEquiv,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin, hdegree]
  have hbinary : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by
    intro t
    rcases (show t.val = 0 ∨ t.val = 1 by have := t.val_lt; omega) with hz | ho
    · left
      calc
        t = (t.val : ZMod 2) := (ZMod.natCast_zmod_val t).symm
        _ = 0 := by rw [hz]; rfl
    · right
      calc
        t = (t.val : ZMod 2) := (ZMod.natCast_zmod_val t).symm
        _ = 1 := by rw [ho]; rfl
  have hcoeff : ∀ {m : ℕ} (c : Fin m → ZMod 2) (i : Fin m),
      (vectorPolynomial c).coeff i.val = c i := by
    intro m c i
    simp [vectorPolynomial, finsetSum_coeff, coeff_monomial, Fin.val_eq_val]
  have hphiCoeff : ∀ i : Fin (a + 1), (phi a).coeff i.val = 1 := by
    intro i
    rw [hphi]
    simp [finsetSum_coeff, coeff_X_pow, i.isLt]
  have hvectorDegree : ∀ {m : ℕ} (c : Fin m → ZMod 2), m ≤ a + 1 →
      (vectorPolynomial c).natDegree ≤ a := by
    intro m c hm
    apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_monomial_le _).trans (by have := i.isLt; omega)
  have hkernel : ∀ (c d : Fin (a + 1) → ZMod 2),
      AdjoinRoot.mk (phi a) (vectorPolynomial c) =
          AdjoinRoot.mk (phi a) (vectorPolynomial d) ↔
        c = d ∨ c = fun i => 1 - d i := by
    intro c d
    constructor
    · intro heq
      have hdiv := AdjoinRoot.mk_eq_mk.mp heq
      have hbound : (vectorPolynomial c - vectorPolynomial d).natDegree ≤
          (phi a).natDegree := by
        rw [hdegree]
        exact (natDegree_sub_le _ _).trans
          (max_le (hvectorDegree c le_rfl) (hvectorDegree d le_rfl))
      have hmultiple := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
        hmonic hdiv hbound
      rcases hbinary (vectorPolynomial c - vectorPolynomial d).leadingCoeff with hz | ho
      · left
        funext i
        have hi := congrArg (fun P : (ZMod 2)[X] => P.coeff i.val) hmultiple
        exact sub_eq_zero.mp (by simpa [hz, coeff_sub, hcoeff] using hi)
      · right
        funext i
        have hi := congrArg (fun P : (ZMod 2)[X] => P.coeff i.val) hmultiple
        have hsub : c i - d i = 1 := by simpa [ho, coeff_sub, hcoeff, hphiCoeff] using hi
        rw [sub_eq_iff_eq_add] at hsub
        simpa only [CharTwo.sub_eq_add] using hsub
    · rintro (rfl | rfl)
      · rfl
      · apply AdjoinRoot.mk_eq_mk.mpr
        have hsub : vectorPolynomial (fun i => 1 - d i) - vectorPolynomial d = phi a := by
          simp only [vectorPolynomial, ← sum_sub_distrib, ← monomial_sub]
          simp_rw [CharTwo.sub_eq_add, add_assoc, CharTwo.add_self_eq_zero, add_zero,
            monomial_one_right_eq_X_pow]
          simpa only [Fin.sum_univ_eq_sum_range] using hphi.symm
        rw [hsub]
  have hperiod : AdjoinRoot.root (phi a) ^ (a + 1) = 1 := by
    have hgeom := geom_sum_mul (X : (ZMod 2)[X]) (a + 1)
    rw [← hphi] at hgeom
    have hm := congrArg (AdjoinRoot.mk (phi a)) hgeom
    simp only [map_mul, map_sub, map_pow, map_one, AdjoinRoot.mk_self,
      AdjoinRoot.mk_X, zero_mul] at hm
    exact sub_eq_zero.mp hm.symm
  have hvectorSnoc : ∀ {m : ℕ} (c : Fin m → ZMod 2) (t : ZMod 2),
      vectorPolynomial (Fin.snoc c t) = vectorPolynomial c + monomial m t := by
    intro m c t
    simp [vectorPolynomial, Fin.sum_univ_castSucc]
  have hshortRep : ∀ y : AdjoinRoot (phi a),
      ∃ c : Fin a → ZMod 2, AdjoinRoot.mk (phi a) (vectorPolynomial c) = y := by
    have hraw : ∀ y : AdjoinRoot (phi a), ∃ c : Fin (phi a).natDegree → ZMod 2,
        AdjoinRoot.mk (phi a) (vectorPolynomial c) = y := by
      intro y
      let e := (AdjoinRoot.powerBasisAux' hmonic).equivFun
      refine ⟨e y, ?_⟩
      change e.symm (e y) = y
      exact e.symm_apply_apply y
    intro y
    obtain ⟨c, hc⟩ := hraw y
    refine ⟨fun i => c (Fin.cast hdegree.symm i), ?_⟩
    rw [← hc]
    apply congrArg (AdjoinRoot.mk (phi a))
    simpa [vectorPolynomial] using
      (Equiv.sum_comp (finCongr hdegree.symm)
        (fun i : Fin (phi a).natDegree => monomial i.val (c i)))
  have hrep : ∀ y : AdjoinRoot (phi a), ∃ c : Fin (a + 1) → ZMod 2,
      AdjoinRoot.mk (phi a) (vectorPolynomial c) = y := by
    intro y
    obtain ⟨c, hc⟩ := hshortRep y
    refine ⟨Fin.snoc c 0, ?_⟩
    simpa only [hvectorSnoc, monomial_zero_right, add_zero] using hc
  have hboolRep : ∀ {m : ℕ} (c : Fin m → ZMod 2),
      ∃ w : Fin m → Bool, wordPolynomial w = vectorPolynomial c := by
    intro m c
    refine ⟨fun i => decide (c i = 1), ?_⟩
    apply congrArg vectorPolynomial
    funext i
    rcases hbinary (c i) with hz | ho
    · simp [hz]
    · simp [ho]
  let fold : {m : ℕ} → (Fin m → Bool) → Fin (a + 1) → ZMod 2 :=
    fun {m} w j => ∑ i : Fin m,
      if i.val % (a + 1) = j.val then (if w i then 1 else 0) else 0
  have hmap : ∀ {m : ℕ} (c : Fin m → ZMod 2),
      AdjoinRoot.mk (phi a) (vectorPolynomial c) =
        ∑ i : Fin m, AdjoinRoot.of (phi a) (c i) * AdjoinRoot.root (phi a) ^ i.val := by
    intro m c
    simp [vectorPolynomial, ← C_mul_X_pow_eq_monomial]
  have hfold : ∀ {m : ℕ} (w : Fin m → Bool),
      AdjoinRoot.mk (phi a) (wordPolynomial w) =
        AdjoinRoot.mk (phi a) (vectorPolynomial (fold w)) := by
    intro m w
    rw [wordPolynomial, hmap, hmap]
    simp only [fold, map_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_eq_single ⟨i.val % (a + 1), Nat.mod_lt _ (by omega)⟩]
    · simp only [↓reduceIte]
      rw [pow_eq_pow_mod i.val hperiod]
    · intro j hj hne
      have hv : i.val % (a + 1) ≠ j.val := fun he => hne (Fin.ext he.symm)
      simp [hv]
    · simp
  have hsnoc : ∀ {m : ℕ} (w : Fin m → Bool),
      wordPolynomial (Fin.snoc w false) = wordPolynomial w := by
    intro m w
    simp [wordPolynomial, vectorPolynomial, Fin.sum_univ_castSucc]
  have hscan : ∀ (m fuel : ℕ) (v : ℕ → Bool), fuel ≤ k - 1 →
      (runAdmissible (k - 1) fuel m (fun i => v i.val) = true ↔
        (∀ s : ℕ, s + k ≤ m → ∃ j : ℕ, j < k ∧ v (s + j) = false) ∧
          (fuel < m → ∃ j : ℕ, j ≤ fuel ∧ v j = false)) := by
    intro m
    induction m with
    | zero =>
      intro fuel v hf
      simp only [runAdmissible, true_iff]
      constructor
      · intro s hs; omega
      · intro h; omega
    | succ m ih =>
      intro fuel v hf
      let tail : ℕ → Bool := fun i => v (i + 1)
      have ht : Fin.tail (fun i : Fin (m + 1) => v i.val) =
          (fun i : Fin m => tail i.val) := rfl
      cases hhead : v 0 with
      | false =>
        have hr : runAdmissible (k - 1) fuel (m + 1) (fun i => v i.val) =
            runAdmissible (k - 1) (k - 1) m (fun i => tail i.val) := by
          cases fuel <;> simp [runAdmissible, hhead, ht]
        rw [hr, ih (k - 1) tail le_rfl]
        constructor
        · rintro ⟨hnorun, hinitial⟩
          constructor
          · intro s hs
            cases s with
            | zero => exact ⟨0, by omega, hhead⟩
            | succ s =>
              obtain ⟨j, hj, hjfalse⟩ := hnorun s (by omega)
              exact ⟨j, hj, by simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using hjfalse⟩
          · intro h; exact ⟨0, by omega, hhead⟩
        · rintro ⟨hnorun, hinitial⟩
          constructor
          · intro s hs
            obtain ⟨j, hj, hjfalse⟩ := hnorun (s + 1) (by omega)
            exact ⟨j, hj, by simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hjfalse⟩
          · intro h
            obtain ⟨j, hj, hjfalse⟩ := hnorun 1 (by omega)
            exact ⟨j, by omega, by simpa [tail, Nat.add_comm] using hjfalse⟩
      | true =>
        cases fuel with
        | zero =>
          simp only [runAdmissible, Fin.val_zero, hhead, ↓reduceIte,
            Bool.false_eq_true, false_iff]
          rintro ⟨hnorun, hinitial⟩
          obtain ⟨j, hj, hjfalse⟩ := hinitial (by omega)
          have hjzero : j = 0 := by omega
          simp [hjzero, hhead] at hjfalse
        | succ fuel =>
          simp only [runAdmissible, Fin.val_zero, hhead, ↓reduceIte, ht]
          rw [ih fuel tail (by omega)]
          constructor
          · rintro ⟨hnorun, hinitial⟩
            constructor
            · intro s hs
              cases s with
              | zero =>
                obtain ⟨j, hj, hjfalse⟩ := hinitial (by omega)
                exact ⟨j + 1, by omega, by simpa [tail] using hjfalse⟩
              | succ s =>
                obtain ⟨j, hj, hjfalse⟩ := hnorun s (by omega)
                exact ⟨j, hj, by simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using hjfalse⟩
            · intro h
              obtain ⟨j, hj, hjfalse⟩ := hinitial (by omega)
              exact ⟨j + 1, by omega, hjfalse⟩
          · rintro ⟨hnorun, hinitial⟩
            constructor
            · intro s hs
              obtain ⟨j, hj, hjfalse⟩ := hnorun (s + 1) (by omega)
              exact ⟨j, hj, by simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using hjfalse⟩
            · intro h
              obtain ⟨j, hj, hjfalse⟩ := hinitial (by omega)
              have hjpos : 0 < j := by
                by_contra h
                have hjzero : j = 0 := by omega
                simp [hjzero, hhead] at hjfalse
              refine ⟨j - 1, by omega, ?_⟩
              simpa only [tail, Nat.sub_add_cancel hjpos] using hjfalse
  have hlegal : ∀ {m : ℕ} (w : Fin m → Bool),
      DBonacciAdmissible k m w ↔ ∀ s : ℕ, ∀ hs : s + k ≤ m,
        ∃ j : Fin k, w ⟨s + j.val, by omega⟩ = false := by
    intro m w
    let v : ℕ → Bool := fun i => if hi : i < m then w ⟨i, hi⟩ else false
    have hv : ∀ i : Fin m, v i.val = w i := by intro i; simp [v, i.isLt]
    have hdb : DBonacciAdmissible k m w ↔
        runAdmissible (k - 1) (k - 1) m w = true := by
      cases k with
      | zero => omega
      | succ maxTrue => rfl
    rw [hdb, ← show (fun i : Fin m => v i.val) = w from funext hv,
      hscan m (k - 1) v le_rfl]
    constructor
    · rintro ⟨hnorun, hinitial⟩ s hs
      obtain ⟨j, hj, hjfalse⟩ := hnorun s hs
      refine ⟨⟨j, hj⟩, ?_⟩
      simpa [v, show s + j < m by omega] using hjfalse
    · intro hnorun
      have hall : ∀ s : ℕ, s + k ≤ m → ∃ j : ℕ, j < k ∧ v (s + j) = false := by
        intro s hs
        obtain ⟨j, hj⟩ := hnorun s hs
        exact ⟨j.val, j.isLt, by simpa [v, show s + j.val < m by omega] using hj⟩
      refine ⟨hall, ?_⟩
      intro h
      obtain ⟨j, hj, hjfalse⟩ := hall 0 (by omega)
      exact ⟨j, by omega, by simpa using hjfalse⟩
  have hmono : Monotone (actualImage k a) := by
    apply monotone_nat_of_le_succ
    intro m y hy
    obtain ⟨w, hw, heq⟩ := hy
    refine ⟨Fin.snoc w false, admissible_snoc_false k m w hw, ?_⟩
    simpa only [hsnoc] using heq
  have hmin : ∀ m : ℕ, actualImage k a m = Set.univ → a ≤ m := by
    intro m hm
    have hsurj : Function.Surjective
        (fun w : Fin m → Bool => AdjoinRoot.mk (phi a) (wordPolynomial w)) := by
      intro y
      have hy : y ∈ actualImage k a m := by rw [hm]; trivial
      obtain ⟨w, hw, heq⟩ := hy
      exact ⟨w, heq⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [hcard, Nat.card_fun, Nat.card_fin] at hle
    have hbool : Nat.card Bool = 2 := by simp
    rw [hbool] at hle
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  have hsmall : a < k → ∀ m : ℕ,
      actualImage k a m = Set.univ ↔ a ≤ m := by
    intro hak m
    constructor
    · exact hmin m
    · intro ham
      apply Set.eq_univ_of_forall
      intro y
      apply hmono ham
      obtain ⟨c, hc⟩ := hshortRep y
      obtain ⟨w, hw⟩ := hboolRep c
      refine ⟨w, ?_, by rw [hw]; exact hc⟩
      cases k with
      | zero => omega
      | succ maxTrue =>
        exact runAdmissible_eq_true_of_length_le maxTrue maxTrue a w (by omega) le_rfl
  have hrun : ∀ {m : ℕ} (w : Fin m → Bool), ¬ DBonacciAdmissible k m w →
      ∃ s : ℕ, s + k ≤ m ∧
        ∀ i : Fin m, s ≤ i.val → i.val < s + k → w i = true := by
    intro m w hw
    rw [hlegal] at hw
    push Not at hw
    obtain ⟨s, hs, hbits⟩ := hw
    refine ⟨s, hs, ?_⟩
    intro i hsi his
    have hi := hbits ⟨i.val - s, by omega⟩
    have he : (⟨s + (i.val - s), by omega⟩ : Fin m) = i := by
      apply Fin.ext
      simp only
      omega
    rw [he] at hi
    exact Bool.eq_true_of_not_eq_false hi
  have hshortChoice : ∀ {m : ℕ} (w : Fin m → Bool), m < 2 * k →
      DBonacciAdmissible k m w ∨ DBonacciAdmissible k m (fun i => !(w i)) := by
    intro m w hm
    by_contra h
    push Not at h
    obtain ⟨s, hs, hones⟩ := hrun w h.1
    obtain ⟨t, ht, hzeros⟩ := hrun (fun i => !(w i)) h.2
    by_cases hst : s ≤ t
    · have hdis : s + k ≤ t := by
        by_contra hover
        let i : Fin m := ⟨t, by omega⟩
        have ho := hones i hst (by dsimp [i]; omega)
        have hz := hzeros i le_rfl (by dsimp [i]; omega)
        simp only [ho, Bool.not_true, Bool.false_eq_true] at hz
      omega
    · have hdis : t + k ≤ s := by
        by_contra hover
        let i : Fin m := ⟨s, by omega⟩
        have ho := hones i le_rfl (by dsimp [i]; omega)
        have hz := hzeros i (by dsimp [i]; omega) (by dsimp [i]; omega)
        simp only [ho, Bool.not_true, Bool.false_eq_true] at hz
      omega
  have hcomplement : ∀ w : Fin (a + 1) → Bool,
      AdjoinRoot.mk (phi a) (wordPolynomial (fun i => !(w i))) =
        AdjoinRoot.mk (phi a) (wordPolynomial w) := by
    intro w
    apply (hkernel _ _).mpr
    right
    funext i
    cases hw : w i <;> simp [hw, CharTwo.sub_eq_add]
  have hmiddleUpper : a ≤ 2 * k - 2 → actualImage k a (a + 1) = Set.univ := by
    intro ham
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨c, hc⟩ := hrep y
    obtain ⟨w, hw⟩ := hboolRep c
    have hobs : AdjoinRoot.mk (phi a) (wordPolynomial w) = y := by rw [hw]; exact hc
    rcases hshortChoice w (by omega) with hl | hl
    · exact ⟨w, hl, hobs⟩
    · exact ⟨fun i => !(w i), hl, (hcomplement w).trans hobs⟩
  have hvectorLess : ∀ {m : ℕ} (c : Fin m → ZMod 2),
      (vectorPolynomial c).degree < m := by
    intro m c
    simpa only [vectorPolynomial, ← C_mul_X_pow_eq_monomial] using degree_sum_fin_lt c
  have hshortInjective : ∀ c d : Fin a → ZMod 2,
      AdjoinRoot.mk (phi a) (vectorPolynomial c) =
        AdjoinRoot.mk (phi a) (vectorPolynomial d) → c = d := by
    intro c d heq
    have hd : (vectorPolynomial c - vectorPolynomial d).degree < (phi a).degree := by
      rw [degree_eq_natDegree hmonic.ne_zero, hdegree]
      exact (degree_sub_le _ _).trans_lt (max_lt (hvectorLess c) (hvectorLess d))
    have hp : vectorPolynomial c - vectorPolynomial d = 0 := by
      by_contra hn
      exact hmonic.not_dvd_of_degree_lt hn hd (AdjoinRoot.mk_eq_mk.mp heq)
    funext i
    have hi := congrArg (fun P : (ZMod 2)[X] => P.coeff i.val) hp
    exact sub_eq_zero.mp (by simpa only [coeff_sub, coeff_zero, hcoeff] using hi)
  have hmissingA : k ≤ a → actualImage k a a ≠ Set.univ := by
    intro hka hall
    let c : Fin a → ZMod 2 := fun i => if i.val < k then 1 else 0
    have hy : AdjoinRoot.mk (phi a) (vectorPolynomial c) ∈ actualImage k a a := by
      rw [hall]; trivial
    obtain ⟨w, hw, hobs⟩ := hy
    have heq := hshortInjective (fun i => if w i then 1 else 0) c hobs
    obtain ⟨j, hj⟩ := (hlegal w).mp hw 0 (by omega)
    have hi := congrFun heq (⟨j.val, by omega⟩ : Fin a)
    have hj' : w (⟨j.val, by omega⟩ : Fin a) = false := by
      simpa only [zero_add] using hj
    simp [c, j.isLt, hj'] at hi
  have hhighMin : k ≤ a → ∀ m : ℕ,
      actualImage k a m = Set.univ → a + 1 ≤ m := by
    intro hka m hm
    by_contra h
    apply hmissingA hka
    apply Set.eq_univ_of_forall
    intro y
    apply hmono (show m ≤ a by omega)
    rw [hm]; trivial
  have hsingleton : ∀ {m : ℕ} (w : Fin m → Bool) (j : Fin (a + 1)),
      ∀ hj : j.val < m, m ≤ j.val + (a + 1) →
        fold w j = (if w ⟨j.val, hj⟩ then 1 else 0) := by
    intro m w j hj hupper
    dsimp only [fold]
    rw [sum_eq_single (⟨j.val, hj⟩ : Fin m)]
    · simp [Nat.mod_eq_of_lt j.isLt]
    · intro i hi hne
      have hmod : i.val % (a + 1) ≠ j.val := by
        intro he
        have hdiv : i.val / (a + 1) = 0 := by
          by_contra h
          have hmul := Nat.mul_le_mul_left (a + 1)
            (Nat.one_le_iff_ne_zero.mpr h)
          have hdecomp := Nat.mod_add_div i.val (a + 1)
          rw [he] at hdecomp
          have := i.isLt
          omega
        have hdecomp := Nat.mod_add_div i.val (a + 1)
        simp only [he, hdiv, mul_zero, add_zero] at hdecomp
        exact hne (Fin.ext hdecomp.symm)
      simp only [if_neg hmod]
    · simp
  have hlongMissing : 2 * k - 1 ≤ a →
      actualImage k a (2 * (a + 1) - 2 * k) ≠ Set.univ := by
    intro hbig hall
    let b := a + 1
    let m := 2 * b - 2 * k
    have hb : 2 * k ≤ b := by dsimp [b]; omega
    have hm : b ≤ m := by dsimp [m]; omega
    let c : Fin (a + 1) → ZMod 2 := fun i => if b - k ≤ i.val then 1 else 0
    have hy : AdjoinRoot.mk (phi a) (vectorPolynomial c) ∈ actualImage k a m := by
      rw [hall]; trivial
    obtain ⟨w, hw, hobs⟩ := hy
    have heq := (hkernel (fold w) c).mp ((hfold w).symm.trans hobs)
    rcases heq with heq | heq
    · obtain ⟨j, hj⟩ := (hlegal w).mp hw (b - k) (by omega)
      let i : Fin (a + 1) := ⟨b - k + j.val, by dsimp [b] at *; omega⟩
      have hi : i.val < m := by dsimp [i]; omega
      have hone : fold w i = 1 := by
        have hc := congrFun heq i
        change fold w i = if b - k ≤ i.val then 1 else 0 at hc
        rw [if_pos (by dsimp [i]; omega)] at hc
        exact hc
      have hzero : w ⟨i.val, hi⟩ = false := by simpa only [i] using hj
      rw [hsingleton w i hi (by dsimp [i, m]; omega)] at hone
      have hz : (0 : ZMod 2) = 1 := by
        simpa only [hzero, Bool.false_eq_true, if_false] using hone
      exact zero_ne_one hz
    · obtain ⟨j, hj⟩ := (hlegal w).mp hw (b - 2 * k) (by omega)
      let i : Fin (a + 1) := ⟨b - 2 * k + j.val, by dsimp [b] at *; omega⟩
      have hi : i.val < m := by dsimp [i]; omega
      have hone : fold w i = 1 := by
        have hc := congrFun heq i
        change fold w i = 1 - (if b - k ≤ i.val then 1 else 0) at hc
        rw [if_neg (by dsimp [i]; omega), sub_zero] at hc
        exact hc
      have hzero : w ⟨i.val, hi⟩ = false := by simpa only [i] using hj
      rw [hsingleton w i hi (by dsimp [i, m]; omega)] at hone
      have hz : (0 : ZMod 2) = 1 := by
        simpa only [hzero, Bool.false_eq_true, if_false] using hone
      exact zero_ne_one hz
  let leading : (Fin (2 * k - 1) → Bool) → Prop := fun B =>
    ∀ i : Fin (k - 1), B ⟨i.val, by omega⟩ = true
  let trailing : (Fin (2 * k - 1) → Bool) → Prop := fun B =>
    ∀ i : Fin (k - 1), B ⟨k + i.val, by omega⟩ = true
  have hrepair : ∀ B : Fin (2 * k - 1) → Bool, leading B → trailing B →
      DBonacciAdmissible k (2 * k - 1) (fun i => !(B i)) ∧
        ¬ (leading (fun i => !(B i)) ∧ trailing (fun i => !(B i))) := by
    intro B hlead htrail
    have houtside : ∀ i : Fin (2 * k - 1), i.val ≠ k - 1 → B i = true := by
      intro i hi
      by_cases hleft : i.val < k - 1
      · exact hlead ⟨i.val, hleft⟩
      · have hright : k ≤ i.val := by omega
        have ht := htrail ⟨i.val - k, by have := i.isLt; omega⟩
        have he : (⟨k + (i.val - k), by omega⟩ : Fin (2 * k - 1)) = i := by
          apply Fin.ext; simp only; omega
        simpa only [he] using ht
    constructor
    · apply (hlegal _).mpr
      intro s hs
      by_cases hcenter : s = k - 1
      · refine ⟨⟨1, by omega⟩, ?_⟩
        have ho := houtside ⟨s + 1, by omega⟩ (by change s + 1 ≠ k - 1; omega)
        simp only [ho, Bool.not_true]
      · refine ⟨⟨0, by omega⟩, ?_⟩
        have ho := houtside ⟨s + 0, by omega⟩ (by change s + 0 ≠ k - 1; omega)
        simp only [ho, Bool.not_true]
    · rintro ⟨hlead', htrail'⟩
      have ho := houtside ⟨0, by omega⟩ (by change 0 ≠ k - 1; omega)
      have hc := hlead' ⟨0, by omega⟩
      simp only [ho, Bool.not_true, Bool.false_eq_true] at hc
  have hblockChoice : ∀ B : Fin (2 * k - 1) → Bool,
      (DBonacciAdmissible k (2 * k - 1) B ∧ ¬ (leading B ∧ trailing B)) ∨
        (DBonacciAdmissible k (2 * k - 1) (fun i => !(B i)) ∧
          ¬ (leading (fun i => !(B i)) ∧ trailing (fun i => !(B i)))) := by
    intro B
    rcases hshortChoice B (by omega) with hl | hl
    · by_cases hends : leading B ∧ trailing B
      · exact Or.inr (hrepair B hends.1 hends.2)
      · exact Or.inl ⟨hl, hends⟩
    · by_cases hends : leading (fun i => !(B i)) ∧ trailing (fun i => !(B i))
      · have hr := hrepair (fun i => !(B i)) hends.1 hends.2
        have he : (fun i => !(!(B i))) = B := by funext i; simp
        rw [he] at hr
        exact Or.inl hr
      · exact Or.inr ⟨hl, hends⟩
  have hlongUpper : 2 * k - 1 ≤ a →
      actualImage k a (2 * (a + 1) - 2 * k + 1) = Set.univ := by
    intro hbig
    let b := a + 1
    let u := b - 2 * k + 1
    have hb : 2 * k ≤ b := by dsimp [b]; omega
    have hu : 1 ≤ u := by dsimp [u]; omega
    have hub : u + (2 * k - 1) = b := by dsimp [u]; omega
    have hun : b + u = 2 * (a + 1) - 2 * k + 1 := by dsimp [b, u]; omega
    rw [← hun]
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨c, hc⟩ := hrep y
    obtain ⟨v, hv⟩ := hboolRep c
    have hobs : AdjoinRoot.mk (phi a) (wordPolynomial v) = y := by rw [hv]; exact hc
    let block : (Fin b → Bool) → Fin (2 * k - 1) → Bool :=
      fun w j => w ⟨u + j.val, by have := j.isLt; omega⟩
    obtain ⟨v, hobs, hB, hends⟩ : ∃ v : Fin b → Bool,
        AdjoinRoot.mk (phi a) (wordPolynomial v) = y ∧
          DBonacciAdmissible k (2 * k - 1) (block v) ∧
            ¬ (leading (block v) ∧ trailing (block v)) := by
      rcases hblockChoice (block v) with hl | hl
      · exact ⟨v, hobs, hl⟩
      · exact ⟨fun i => !(v i), (hcomplement v).trans hobs, hl⟩
    let e : ℕ := if leading (block v) then u % 2 else 0
    have he : e < 2 := by dsimp [e]; split_ifs <;> omega
    let W : Fin (b + u) → Bool := fun i =>
      if hi : i.val < u then
        if i.val % 2 = e then v ⟨i.val, by omega⟩ else false
      else if hi : i.val < b then v ⟨i.val, hi⟩
      else if (i.val - b) % 2 = e then false else v ⟨i.val - b, by omega⟩
    have hE : ∀ i : Fin (b + u), i.val < u → W i = true → i.val % 2 = e := by
      intro i hi hbit
      by_contra hp
      simp [W, hi, hp] at hbit
    have hF : ∀ i : Fin (b + u), b ≤ i.val → W i = true →
        (i.val - b) % 2 ≠ e := by
      intro i hi hbit hp
      have hnotE : ¬ i.val < u := by omega
      have hnotB : ¬ i.val < b := by omega
      simp [W, hnotE, hnotB, hp] at hbit
    have hWB : ∀ j : Fin (2 * k - 1),
        W ⟨u + j.val, by have := j.isLt; omega⟩ = block v j := by
      intro j
      have hnotE : ¬ u + j.val < u := by omega
      have hinB : u + j.val < b := by have := j.isLt; omega
      simp [W, block, hnotE, hinB]
    have hleftZero : leading (block v) → W ⟨u - 1, by omega⟩ = false := by
      intro hlead
      have hp : (u - 1) % 2 ≠ u % 2 := by omega
      simp [W, e, hlead, show u - 1 < u by omega, hp]
    have hrightZero : trailing (block v) → W ⟨b, by omega⟩ = false := by
      intro htrail
      have hnlead : ¬ leading (block v) := fun hlead => hends ⟨hlead, htrail⟩
      simp [W, e, hnlead, show ¬ b < u by omega]
    have hWlegal : DBonacciAdmissible k (b + u) W := by
      by_contra hw
      obtain ⟨s, hs, hbits⟩ := hrun W hw
      by_cases hleft : s < u
      · have hlast : s = u - 1 := by
          by_contra h
          let i : Fin (b + u) := ⟨s, by omega⟩
          let j : Fin (b + u) := ⟨s + 1, by omega⟩
          have hp := hE i hleft (hbits i le_rfl (by dsimp [i]; omega))
          have hq := hE j (by dsimp [j]; omega)
            (hbits j (by dsimp [j]; omega) (by dsimp [j]; omega))
          dsimp only [i, j] at hp hq
          omega
        have hlead : leading (block v) := by
          intro j
          rw [← hWB ⟨j.val, by have := j.isLt; omega⟩]
          apply hbits
          · change s ≤ u + j.val; have := j.isLt; omega
          · change u + j.val < s + k; have := j.isLt; omega
        have hone := hbits (⟨u - 1, by omega⟩ : Fin (b + u))
          (by change s ≤ u - 1; omega) (by change u - 1 < s + k; omega)
        rw [hleftZero hlead] at hone
        exact Bool.noConfusion hone
      · have hstart : u ≤ s := by omega
        by_cases hright : b < s + k
        · have hsB : s < b := by
            by_contra h
            let i : Fin (b + u) := ⟨s, by omega⟩
            let j : Fin (b + u) := ⟨s + 1, by omega⟩
            have hp := hF i (by dsimp [i]; omega)
              (hbits i le_rfl (by dsimp [i]; omega))
            have hq := hF j (by dsimp [j]; omega)
              (hbits j (by dsimp [j]; omega) (by dsimp [j]; omega))
            dsimp only [i, j] at hp hq
            omega
          have hend : s + k = b + 1 := by
            by_contra h
            let i : Fin (b + u) := ⟨b, by omega⟩
            let j : Fin (b + u) := ⟨b + 1, by omega⟩
            have hp := hF i le_rfl
              (hbits i (by dsimp [i]; omega) (by dsimp [i]; omega))
            have hq := hF j (by dsimp [j]; omega)
              (hbits j (by dsimp [j]; omega) (by dsimp [j]; omega))
            dsimp only [i, j] at hp hq
            omega
          have htrail : trailing (block v) := by
            intro j
            rw [← hWB ⟨k + j.val, by have := j.isLt; omega⟩]
            apply hbits
            · change s ≤ u + (k + j.val); have := j.isLt; omega
            · change u + (k + j.val) < s + k; have := j.isLt; omega
          have hone := hbits (⟨b, by omega⟩ : Fin (b + u))
            (by change s ≤ b; omega) (by change b < s + k; omega)
          rw [hrightZero htrail] at hone
          exact Bool.noConfusion hone
        · obtain ⟨j, hj⟩ := (hlegal (block v)).mp hB (s - u) (by omega)
          let q : Fin (2 * k - 1) := ⟨s - u + j.val, by omega⟩
          have hone := hbits (⟨u + q.val, by have := q.isLt; omega⟩ : Fin (b + u))
            (by dsimp [q]; omega) (by dsimp [q]; have := j.isLt; omega)
          rw [hWB q] at hone
          have hzero : block v q = false := hj
          rw [hzero] at hone
          exact Bool.noConfusion hone
    have htwoFold : ∀ j : Fin b,
        fold W j = (if W ⟨j.val, by have := j.isLt; omega⟩ then 1 else 0) +
          (if hj : j.val < u then
            (if W ⟨b + j.val, by omega⟩ then 1 else 0) else 0) := by
      intro j
      dsimp only [fold]
      rw [Fin.sum_univ_add]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      have hlowmod : ∀ i : Fin b, i.val % b = i.val :=
        fun i => Nat.mod_eq_of_lt i.isLt
      have hhighmod : ∀ i : Fin u, (b + i.val) % b = i.val := by
        intro i
        rw [Nat.add_mod]
        simp only [Nat.mod_self, zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
      change (∑ i : Fin b,
        if i.val % b = j.val then (if W (Fin.castAdd u i) then 1 else 0) else 0) +
          (∑ i : Fin u,
            if (b + i.val) % b = j.val then (if W (Fin.natAdd b i) then 1 else 0) else 0) = _
      simp only [hlowmod, hhighmod, Fin.val_eq_val, sum_ite_eq', mem_univ, if_true]
      congr 1
      by_cases hj : j.val < u
      · rw [dif_pos hj, sum_eq_single (⟨j.val, hj⟩ : Fin u)]
        · simp
        · intro i hi hne
          have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
          simp [hneval]
        · simp
      · rw [dif_neg hj]
        apply sum_eq_zero
        intro i hi
        have hneval : i.val ≠ j.val := by have := i.isLt; omega
        simp [hneval]
    have hfoldW : fold W = (fun j : Fin (a + 1) => if v j then 1 else 0) := by
      funext j
      rw [htwoFold j]
      by_cases hj : j.val < u
      · rw [dif_pos hj]
        have hnotE : ¬b + j.val < u := by omega
        have hnotB : ¬b + j.val < b := by omega
        by_cases hp : j.val % 2 = e
        · simp [W, hj, hnotE, hnotB, hp]
        · simp [W, hj, hnotE, hnotB, hp]
      · rw [dif_neg hj]
        simp [W, hj]
    refine ⟨W, hWlegal, ?_⟩
    rw [hfold, hfoldW]
    exact hobs
  refine ⟨hcard, ?_⟩
  intro n
  by_cases hak : a < k
  · simpa only [threshold, if_pos hak] using hsmall hak n
  by_cases hmiddle : a ≤ 2 * k - 2
  · have hN : threshold k a = a + 1 := by
      simp only [threshold, if_neg hak]
      omega
    rw [hN]
    constructor
    · exact hhighMin (by omega) n
    · intro hn
      apply Set.eq_univ_of_forall
      intro y
      apply hmono hn
      rw [hmiddleUpper hmiddle]; trivial
  have hbig : 2 * k - 1 ≤ a := by omega
  have hN : threshold k a = 2 * (a + 1) - 2 * k + 1 := by
    simp only [threshold, if_neg hak]
    omega
  rw [hN]
  constructor
  · intro hn
    by_contra h
    apply hlongMissing hbig
    apply Set.eq_univ_of_forall
    intro y
    apply hmono (show n ≤ 2 * (a + 1) - 2 * k by omega)
    rw [hn]; trivial
  · intro hn
    apply Set.eq_univ_of_forall
    intro y
    apply hmono hn
    rw [hlongUpper hbig]; trivial

end D5.S1.Words.AdmissibleWords.KBonacciActualSaturation
