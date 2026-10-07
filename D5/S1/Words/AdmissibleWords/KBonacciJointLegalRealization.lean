/- GID: D5/S1/Words/AdmissibleWords/KBonacciJointLegalRealization
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciJointLegalRealization
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Legal Boolean realization of joint finite-ring polynomial observations. -/

import D5.S1.Words.ClosedRunStarts
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciJointLegalRealization

open Finset Polynomial
open D5.S0.Tower.DBonacci.Names D5.S1.Words.ClosedRunStarts

/-- Every common polynomial observation has one scanner-legal Boolean realization
with a counted length bound, a zero tail, and trivial phase in the product quotient. -/
theorem kbonacci_joint_legal_realization (k d r : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d)
    (_hr : 1 ≤ r) (a : Fin r → ℕ) (_ha : Function.Injective a)
    (ha : ∀ i, 2 ≤ a i) :
    let Phi := fun b => (X ^ b - ∑ j ∈ range b, X ^ j : (ZMod d)[X])
    let F := ∏ i : Fin r, Phi (a i)
    let D := ∑ i : Fin r, a i
    let A := AdjoinRoot F
    let x : A := AdjoinRoot.root F
    let L := orderOf x
    let Pw := fun {n : ℕ} (w : Fin n → Bool) =>
      ∑ i : Fin n, monomial i.val (if w i then 1 else 0 : ZMod d)
    let O := fun P : (ZMod d)[X] => fun i : Fin r => P %ₘ Phi (a i)
    Nat.card A = d ^ D ∧ IsUnit x ∧ 1 ≤ L ∧ L ≤ d ^ D ∧
    (∃ T : ℕ, L ∣ T ∧ D + k ≤ T) ∧
    (∀ T : ℕ, L ∣ T → D + k ≤ T → ∀ P : (ZMod d)[X],
      ∃ (n : ℕ) (w : Fin n → Bool),
        DBonacciAdmissible k n w ∧ O (Pw w) = O P ∧
        k ≤ n ∧ n ≤ T * (D * (d - 1) + 1) ∧
        (∀ i : Fin n, n - k ≤ i.val → w i = false) ∧ x ^ n = 1) ∧
    Set.range O = {y | ∃ (n : ℕ) (w : Fin n → Bool),
      DBonacciAdmissible k n w ∧ O (Pw w) = y} := by
  classical
  dsimp only
  have : NeZero d := ⟨by omega⟩
  have : Fact (1 < d) := ⟨by omega⟩
  let Phi := fun b => (X ^ b - ∑ j ∈ range b, X ^ j : (ZMod d)[X])
  let F := ∏ i : Fin r, Phi (a i)
  let D := ∑ i : Fin r, a i
  let A := AdjoinRoot F
  let x : A := AdjoinRoot.root F
  let L := orderOf x
  let Pw := fun {n : ℕ} (w : Fin n → Bool) =>
    ∑ i : Fin n, monomial i.val (if w i then 1 else 0 : ZMod d)
  let O := fun P : (ZMod d)[X] => fun i : Fin r => P %ₘ Phi (a i)
  have hlow : ∀ i, (∑ j ∈ range (a i), (X : (ZMod d)[X]) ^ j).degree < a i := by
    intro i
    simpa only [← Fin.sum_univ_eq_sum_range, C_1, one_mul] using
      degree_sum_fin_lt (fun _ : Fin (a i) => (1 : ZMod d))
  have hmonic : ∀ i, (Phi (a i)).Monic := fun i => monic_X_pow_sub (hlow i)
  have hdeg : ∀ i, (Phi (a i)).natDegree = a i := by
    intro i
    exact (natDegree_eq_of_degree_eq
      (degree_sub_eq_left_of_degree_lt (by simpa using hlow i))).trans (natDegree_X_pow _)
  have hF : F.Monic := monic_prod_of_monic univ _ (fun i _ => hmonic i)
  have hD : F.natDegree = D := by
    dsimp [F, D]
    rw [natDegree_prod_of_monic univ (fun i : Fin r => Phi (a i))
      (fun i _ => hmonic i)]
    exact sum_congr rfl (fun i _ => hdeg i)
  have hc : ∀ i, (Phi (a i)).coeff 0 = -1 := by
    intro i
    have hp : 0 < a i := by have := ha i; omega
    simp [Phi, finsetSum_coeff, coeff_X_pow, hp.ne, hp]
  have hconst : F.coeff 0 = (-1 : ZMod d) ^ r := by
    dsimp [F]
    rw [coeff_zero_prod]
    simp_rw [hc]
    simp
  have hcard : Nat.card A = d ^ D := by
    rw [Nat.card_congr (AdjoinRoot.powerBasisAux' hF).equivFun.toEquiv,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin, hD]
  let : Finite A := Finite.of_equiv (Fin F.natDegree → ZMod d)
    (AdjoinRoot.powerBasisAux' hF).equivFun.toEquiv.symm
  have hunit : IsUnit x := by
    have he := congrArg (AdjoinRoot.mk F) (X_mul_divX_add F)
    simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.mk_self] at he
    have hu : IsUnit (AdjoinRoot.of F (F.coeff 0)) := by
      rw [hconst]
      exact ((isUnit_one.neg).pow r).map (AdjoinRoot.of F)
    have hm : x * AdjoinRoot.mk F F.divX = -AdjoinRoot.of F (F.coeff 0) := by
      exact eq_neg_of_add_eq_zero_left he
    exact isUnit_of_mul_isUnit_left (hm.symm ▸ hu.neg)
  have hL : 1 ≤ L := hunit.isOfFinOrder.orderOf_pos
  have hLbound : L ≤ d ^ D := (orderOf_le_card (x := x)).trans_eq hcard
  have hT : ∃ T : ℕ, L ∣ T ∧ D + k ≤ T := by
    refine ⟨L * (D + k), dvd_mul_right _ _, ?_⟩
    simpa only [one_mul] using Nat.mul_le_mul_right (D + k) hL
  have hreal : ∀ T : ℕ, L ∣ T → D + k ≤ T → ∀ P : (ZMod d)[X],
      ∃ (n : ℕ) (w : Fin n → Bool),
        DBonacciAdmissible k n w ∧ O (Pw w) = O P ∧
        k ≤ n ∧ n ≤ T * (D * (d - 1) + 1) ∧
        (∀ i : Fin n, n - k ≤ i.val → w i = false) ∧ x ^ n = 1 := by
    intro T hLT hDT P
    have hxT : x ^ T = 1 := orderOf_dvd_iff_pow_eq_one.mp hLT
    let C := P %ₘ F
    let c := fun j : Fin D => (C.coeff j.val).val
    let N := ∑ j : Fin D, c j
    let Token := (j : Fin D) × Fin (c j)
    let e : Token ≃ Fin N := Fintype.equivFinOfCardEq (by simp [Token, N])
    let j := fun s : Fin N => (e.symm s).1
    let n := T * (N + 1)
    have hnk : k ≤ n := by dsimp [n]; nlinarith
    have hslot : ∀ s : Fin N, (s.val + 1) * T + (j s).val + k < n := by
      intro s
      have hs := Nat.mul_le_mul_right T (Nat.succ_le_of_lt s.isLt)
      have hj := (j s).isLt
      dsimp [n]
      nlinarith
    let pos : Fin N → Fin n := fun s =>
      ⟨(s.val + 1) * T + (j s).val, by have := hslot s; omega⟩
    have hsep : ∀ s t : Fin N, s.val < t.val → (pos s).val + k < (pos t).val := by
      intro s t hst
      have hmul := Nat.mul_le_mul_right T (show s.val + 2 ≤ t.val + 1 by omega)
      have hj := (j s).isLt
      dsimp [pos]
      nlinarith
    have hinj : Function.Injective pos := by
      intro s t he
      apply Fin.ext
      have hv := congrArg Fin.val he
      rcases lt_trichotomy s.val t.val with hlt | heq | hgt
      · have := hsep s t hlt; omega
      · exact heq
      · have := hsep t s hgt; omega
    have hnear : ∀ s t : Fin N, (pos t).val ≠ (pos s).val + 1 := by
      intro s t he
      rcases lt_trichotomy s.val t.val with hlt | heq | hgt
      · have := hsep s t hlt; omega
      · have hst : s = t := Fin.ext heq
        subst t
        omega
      · have := hsep t s hgt; omega
    let w := fun i : Fin n => decide (∃ s : Fin N, pos s = i)
    have hw : ∀ i : Fin n, w i = true ↔ ∃ s : Fin N, pos s = i := by
      intro i
      simp [w]
    have hlegal : DBonacciAdmissible k n w := by
      apply (closed_word_run_start_equivalence n k (by omega) hnk w).1.mpr
      intro b hb
      let i : Fin n := ⟨b, by have := hb.1; omega⟩
      let i' : Fin n := ⟨b + 1, by have := hb.1; omega⟩
      obtain ⟨s, hs⟩ := (hw i).mp (hb.2 i (by simp [i]) (by simp [i]; omega))
      obtain ⟨t, ht⟩ := (hw i').mp (hb.2 i' (by simp [i']) (by simp [i']; omega))
      apply hnear s t
      simp [hs, ht, i, i']
    have htail : ∀ i : Fin n, n - k ≤ i.val → w i = false := by
      intro i hi
      apply Bool.eq_false_iff.mpr
      intro hit
      obtain ⟨s, hs⟩ := (hw i).mp hit
      have hv := congrArg Fin.val hs
      have hbound := hslot s
      change (pos s).val + k < n at hbound
      omega
    have hN : N ≤ D * (d - 1) := by
      calc
        N ≤ ∑ _j : Fin D, (d - 1) := sum_le_sum (fun (j : Fin D) _ => by
          have hv := (C.coeff j.val).val_lt
          dsimp [c]
          omega)
        _ = D * (d - 1) := by simp
    have hpoly : Pw w = ∑ s : Fin N, monomial (pos s).val (1 : ZMod d) := by
      calc
        Pw w = ∑ i : Fin n,
            if i ∈ univ.image pos then monomial i.val (1 : ZMod d) else 0 := by
          apply sum_congr rfl
          intro i _
          have hmem : i ∈ univ.image pos ↔ ∃ s : Fin N, pos s = i := by simp
          by_cases hi : ∃ s : Fin N, pos s = i <;> simp [w, hmem, hi]
        _ = ∑ i ∈ univ.image pos, monomial i.val (1 : ZMod d) := by
          rw [sum_ite_mem_eq]
        _ = ∑ s : Fin N, monomial (pos s).val (1 : ZMod d) :=
          sum_image (fun s _ t _ he => hinj he)
    have hpower : ∀ s : Fin N, x ^ (pos s).val = x ^ (j s).val := by
      intro s
      change x ^ ((s.val + 1) * T + (j s).val) = _
      rw [Nat.mul_comm (s.val + 1) T, pow_add, pow_mul, hxT, one_pow, one_mul]
    have hsum : AdjoinRoot.mk F (Pw w) =
        ∑ j : Fin D, AdjoinRoot.of F (C.coeff j.val) * x ^ j.val := by
      calc
        AdjoinRoot.mk F (Pw w) = ∑ s : Fin N, x ^ (j s).val := by
          rw [hpoly]
          simp only [map_sum, ← C_mul_X_pow_eq_monomial, map_pow,
            AdjoinRoot.mk_X, map_one, one_mul]
          exact sum_congr rfl (fun s _ => hpower s)
        _ = ∑ t : Token, x ^ t.1.val :=
          Equiv.sum_comp e.symm (fun t : Token => x ^ t.1.val)
        _ = ∑ j : Fin D, AdjoinRoot.of F (C.coeff j.val) * x ^ j.val := by
          rw [Fintype.sum_sigma]
          apply sum_congr rfl
          intro j _
          have hz : AdjoinRoot.of F (C.coeff j.val) = (c j : A) := by
            calc
              AdjoinRoot.of F (C.coeff j.val) =
                  AdjoinRoot.of F ((C.coeff j.val).val : ZMod d) :=
                congrArg (AdjoinRoot.of F) (ZMod.natCast_zmod_val _).symm
              _ = (c j : A) := map_natCast _ _
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hz]
    have hCP : AdjoinRoot.mk F C = AdjoinRoot.mk F P := by
      exact AdjoinRoot.mk_leftInverse hF (AdjoinRoot.mk F P)
    have hcoeff : (∑ j : Fin D, monomial j.val (C.coeff j.val)) = C := by
      exact sum_modByMonic_coeff hF (by rw [← hD]; exact degree_le_natDegree)
    have hobs : AdjoinRoot.mk F (Pw w) = AdjoinRoot.mk F P := by
      calc
        AdjoinRoot.mk F (Pw w) =
            ∑ j : Fin D, AdjoinRoot.of F (C.coeff j.val) * x ^ j.val := hsum
        _ = AdjoinRoot.mk F (∑ j : Fin D, monomial j.val (C.coeff j.val)) := by
          simp only [map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
            AdjoinRoot.mk_C, AdjoinRoot.mk_X]
          rfl
        _ = AdjoinRoot.mk F C := congrArg (AdjoinRoot.mk F) hcoeff
        _ = AdjoinRoot.mk F P := hCP
    have hO : O (Pw w) = O P := by
      funext i
      apply modByMonic_eq_of_dvd_sub (hmonic i)
      exact dvd_trans (dvd_prod_of_mem (fun i : Fin r => Phi (a i)) (mem_univ i))
        (AdjoinRoot.mk_eq_mk.mp hobs)
    refine ⟨n, w, hlegal, hO, hnk, ?_, htail, ?_⟩
    · exact Nat.mul_le_mul_left T (Nat.add_le_add_right hN 1)
    · simp [n, pow_mul, hxT]
  refine ⟨hcard, hunit, hL, hLbound, hT, hreal, ?_⟩
  ext y
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨T, hLT, hDT⟩ := hT
    obtain ⟨n, w, hw, ho, _⟩ := hreal T hLT hDT P
    exact ⟨n, w, hw, ho⟩
  · rintro ⟨n, w, _, ho⟩
    exact ⟨Pw w, ho⟩

end D5.S1.Words.AdmissibleWords.KBonacciJointLegalRealization
