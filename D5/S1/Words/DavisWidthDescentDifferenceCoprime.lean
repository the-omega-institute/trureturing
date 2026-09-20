/- GID: D5/S1/Words/DavisWidthDescentDifferenceCoprime
   generality: G
   mirror-B: D5/B/S1/Words/DavisWidthDescentDifferenceCoprime
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Laurent, mathlib/module/Mathlib.GroupTheory.Perm.Fin, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Coprime width descent differences equal a shifted Eulerian polynomial. -/
/- proof_shape: result: content
   escape_witness: cyclic_reindexing_sum; cyclic_descent_distribution
   admission_basis: open-problem-resolution (issue #9085; Proved)
   Direct frozen dependencies: none (pinned Mathlib only) -/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

namespace D5.S1.Words.DavisWidthDescentDifferenceCoprime

open Equiv LaurentPolynomial

noncomputable section

/-- Width-`k` descents of `σ ∈ S_n` (positions `0..n−1`): the number of `i` with
`i + k < n` and `σ i > σ (i + k)`. -/
def widthDescents {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    ∃ h : i.val + k < n, σ ⟨i.val + k, h⟩ < σ i).card

/-- The Eulerian polynomial as the descent generating function
`F_m^{des}(q) = Σ_{τ∈S_m} q^{des τ}` (identified with `A_m` by MacMahon, page 2). -/
def eulerian (m : ℕ) : LaurentPolynomial ℤ :=
  ∑ τ : Equiv.Perm (Fin m), LaurentPolynomial.T (widthDescents 1 τ : ℤ)

/-- `G_{n,k}(q) = Σ_{σ∈S_n} q^{des_k(σ) − des_{n−k}(σ)}`. -/
def G (n k : ℕ) : LaurentPolynomial ℤ :=
  ∑ σ : Equiv.Perm (Fin n),
    LaurentPolynomial.T ((widthDescents k σ : ℤ) - widthDescents (n - k) σ)

private def cdes {n : ℕ} (τ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun j : Fin n => τ (finRotate n j) < τ j).card

/-- Conjecture 9 as printed: for `1 ≤ k < n` with `gcd(k, n) = 1`,
`G_{n,k}(q) = n q^{1−k} A_{n−1}(q)`. -/
def claim : Prop := ∀ n k : ℕ, 1 ≤ k → k < n → Nat.Coprime k n →
  G n k = (n : LaurentPolynomial ℤ) * LaurentPolynomial.T (1 - (k : ℤ)) * eulerian (n - 1)

/-- Multiplication by `k` modulo `n`, transported from the corresponding unit of `ZMod n`. -/
private def rho (n k : ℕ) (hn : 0 < n) (hkn : Nat.Coprime k n) : Equiv.Perm (Fin n) :=
  letI : NeZero n := ⟨hn.ne'⟩
  (ZMod.finEquiv n).toEquiv |>.trans
    (ZMod.unitOfCoprime k hkn).mulRight |>.trans
      (ZMod.finEquiv n).symm.toEquiv

private lemma rho_rotate (n k : ℕ) (hn : 0 < n) (hk : k < n) (hkn : Nat.Coprime k n)
    (j : Fin n) :
    rho n k hn hkn (finRotate n j) = finCycle ⟨k, hk⟩ (rho n k hn hkn j) := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply (ZMod.finEquiv n).injective
  simp [rho, finRotate_apply, finCycle_apply, ZMod.coe_unitOfCoprime, add_mul]
  apply ZMod.val_injective n
  simp [ZMod.val_natCast_of_lt hk]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rfl

private def cyclicKDescents {n : ℕ} (k : ℕ) (hk : k < n)
    (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => σ (finCycle ⟨k, hk⟩ i) < σ i).card

private lemma cdes_rho (n k : ℕ) (hn : 0 < n) (hk : k < n) (hkn : Nat.Coprime k n)
    (σ : Equiv.Perm (Fin n)) :
    cdes ((rho n k hn hkn).trans σ) = cyclicKDescents k hk σ := by
  apply Finset.card_equiv (rho n k hn hkn)
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change σ (rho n k hn hkn (finRotate n j)) < σ (rho n k hn hkn j) ↔ _
  rw [rho_rotate n k hn hk hkn j]

private def wrapEquiv (n k : ℕ) (hk : k < n) :
    Fin k ≃ {i : Fin n // ¬i.val + k < n} where
  toFun i := by
    refine ⟨⟨i.val + (n - k), by omega⟩, ?_⟩
    simp only
    omega
  invFun i := ⟨i.val.val - (n - k), by omega⟩
  left_inv i := by
    apply Fin.ext
    simp only
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    omega

private def lowIndex (n k : ℕ) (hk : k < n) (i : Fin k) : Fin n :=
  ⟨i.val, lt_trans i.isLt hk⟩

private def wrapInv (n k : ℕ) (hk : k < n) (i : Fin n)
    (hi : ¬i.val + k < n) : Fin k :=
  (wrapEquiv n k hk).symm ⟨i, hi⟩

private lemma cyclic_nonwrap_card (n k : ℕ) (hk : k < n)
    (σ : Equiv.Perm (Fin n)) :
    ((Finset.univ.filter fun i : Fin n => σ (finCycle ⟨k, hk⟩ i) < σ i).filter
      fun i => i.val + k < n).card = widthDescents k σ := by
  unfold widthDescents
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hdesc, hi⟩
    exact ⟨hi, by
      simpa only [finCycle_apply, Fin.add_def, Nat.mod_eq_of_lt hi] using hdesc⟩
  · rintro ⟨hi, hdesc⟩
    exact ⟨by
      simpa only [finCycle_apply, Fin.add_def, Nat.mod_eq_of_lt hi] using hdesc, hi⟩

private lemma cyclic_wrap_card (n k : ℕ) (hk : k < n) (σ : Equiv.Perm (Fin n)) :
    ((Finset.univ.filter fun i : Fin n => σ (finCycle ⟨k, hk⟩ i) < σ i).filter
      fun i => ¬i.val + k < n).card =
      (Finset.univ.filter fun i : Fin k =>
        σ (lowIndex n k hk i) < σ (wrapEquiv n k hk i).val).card := by
  let s := (Finset.univ.filter fun i : Fin n => σ (finCycle ⟨k, hk⟩ i) < σ i).filter
    fun i => ¬i.val + k < n
  let t := Finset.univ.filter fun i : Fin k =>
    σ (lowIndex n k hk i) < σ (wrapEquiv n k hk i).val
  have hcycle (i : Fin k) :
      finCycle ⟨k, hk⟩ (wrapEquiv n k hk i).val =
        ⟨i.val, lt_trans i.isLt hk⟩ := by
    apply Fin.ext
    simp only [finCycle_apply, Fin.add_def, wrapEquiv, Equiv.coe_fn_mk]
    simp [Nat.add_assoc, Nat.sub_add_cancel hk.le,
      Nat.mod_eq_of_lt (lt_trans i.isLt hk)]
  apply Finset.card_bij
    (s := s) (t := t)
    (fun i hi => wrapInv n k hk i (by
      have hmem : σ (finCycle ⟨k, hk⟩ i) < σ i ∧ ¬i.val + k < n := by
        simpa [s] using hi
      exact hmem.2))
  · intro i hi
    have hmem := (by simpa [s] using hi :
      σ (finCycle ⟨k, hk⟩ i) < σ i ∧ ¬i.val + k < n)
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    have hwrap : (wrapEquiv n k hk (wrapInv n k hk i hmem.2)).val = i :=
      congrArg Subtype.val ((wrapEquiv n k hk).apply_symm_apply ⟨i, hmem.2⟩)
    rw [← hwrap] at hmem
    rw [hcycle] at hmem
    simpa [lowIndex] using hmem.1
  · intro i₁ hi₁ i₂ hi₂ h
    have h₁ := (by simpa [s] using hi₁ :
      σ (finCycle ⟨k, hk⟩ i₁) < σ i₁ ∧ ¬i₁.val + k < n)
    have h₂ := (by simpa [s] using hi₂ :
      σ (finCycle ⟨k, hk⟩ i₂) < σ i₂ ∧ ¬i₂.val + k < n)
    have := congrArg (fun j => (wrapEquiv n k hk j).val) h
    have hw₁ : (wrapEquiv n k hk (wrapInv n k hk i₁ h₁.2)).val = i₁ :=
      congrArg Subtype.val ((wrapEquiv n k hk).apply_symm_apply ⟨i₁, h₁.2⟩)
    have hw₂ : (wrapEquiv n k hk (wrapInv n k hk i₂ h₂.2)).val = i₂ :=
      congrArg Subtype.val ((wrapEquiv n k hk).apply_symm_apply ⟨i₂, h₂.2⟩)
    simpa only [hw₁, hw₂] using this
  · intro i hi
    refine ⟨(wrapEquiv n k hk i).val, ?_, ?_⟩
    · have hdesc : σ (finCycle ⟨k, hk⟩ (wrapEquiv n k hk i).val) <
          σ (wrapEquiv n k hk i).val := by
        rw [hcycle]
        change σ (lowIndex n k hk i) < σ (wrapEquiv n k hk i).val
        simpa [t] using hi
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hdesc, (wrapEquiv n k hk i).property⟩
    · simp [wrapInv]

private lemma width_complement_card (n k : ℕ) (hk : k < n)
    (σ : Equiv.Perm (Fin n)) :
    widthDescents (n - k) σ =
      (Finset.univ.filter fun i : Fin k =>
        σ (wrapEquiv n k hk i).val < σ (lowIndex n k hk i)).card := by
  unfold widthDescents
  symm
  let t := Finset.univ.filter fun i : Fin k =>
    σ (wrapEquiv n k hk i).val < σ (lowIndex n k hk i)
  let s := Finset.univ.filter fun i : Fin n =>
    ∃ h : i.val + (n - k) < n, σ ⟨i.val + (n - k), h⟩ < σ i
  apply Finset.card_bij
    (s := t) (t := s)
    (fun i _ => lowIndex n k hk i)
  · intro i hi
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    have hb : (lowIndex n k hk i).val + (n - k) < n := by
      simp [lowIndex]
      omega
    refine ⟨hb, ?_⟩
    have hdesc := (by simpa [t] using hi :
      σ (wrapEquiv n k hk i).val < σ (lowIndex n k hk i))
    convert hdesc using 1 <;> apply congrArg σ <;> apply Fin.ext <;> rfl
  · intro i₁ hi₁ i₂ hi₂ h
    apply Fin.ext
    simpa [lowIndex] using congrArg Fin.val h
  · intro i hi
    rcases (by simpa [s] using hi) with ⟨hbound, hdesc⟩
    let j : Fin k := ⟨i.val, by omega⟩
    refine ⟨j, ?_, ?_⟩
    · simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      convert hdesc using 1 <;> apply congrArg σ <;> apply Fin.ext <;> rfl
    · apply Fin.ext
      rfl

private lemma cyclic_wrap_add_width (n k : ℕ) (hk : k < n)
    (σ : Equiv.Perm (Fin n)) :
    ((Finset.univ.filter fun i : Fin n => σ (finCycle ⟨k, hk⟩ i) < σ i).filter
      fun i => ¬i.val + k < n).card + widthDescents (n - k) σ = k := by
  rw [cyclic_wrap_card n k hk σ, width_complement_card n k hk σ]
  let p := fun i : Fin k => σ (lowIndex n k hk i) < σ (wrapEquiv n k hk i).val
  have hlow_ne (i : Fin k) : lowIndex n k hk i ≠ (wrapEquiv n k hk i).val := by
    intro h
    have := congrArg Fin.val h
    simp only [lowIndex, wrapEquiv, Equiv.coe_fn_mk] at this
    omega
  have hcompl :
      (Finset.univ.filter fun i : Fin k =>
        σ (wrapEquiv n k hk i).val < σ (lowIndex n k hk i)) =
        Finset.univ.filter fun i => ¬p i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p]
    have hne : σ (lowIndex n k hk i) ≠ σ (wrapEquiv n k hk i).val :=
      σ.injective.ne (hlow_ne i)
    omega
  rw [hcompl]
  simpa using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k))) p

private lemma cyclicK_add_width_complement (n k : ℕ) (hk : k < n)
    (σ : Equiv.Perm (Fin n)) :
    cyclicKDescents k hk σ + widthDescents (n - k) σ = widthDescents k σ + k := by
  let s := Finset.univ.filter fun i : Fin n => σ (finCycle ⟨k, hk⟩ i) < σ i
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s) (fun i : Fin n => i.val + k < n)
  have hnon := cyclic_nonwrap_card n k hk σ
  have hwrap := cyclic_wrap_add_width n k hk σ
  change (s.filter fun i => i.val + k < n).card = widthDescents k σ at hnon
  change (s.filter fun i => ¬i.val + k < n).card + widthDescents (n - k) σ = k at hwrap
  change (s.filter fun i => i.val + k < n).card +
      (s.filter fun i => ¬i.val + k < n).card = s.card at hsplit
  unfold cyclicKDescents
  change s.card + widthDescents (n - k) σ = widthDescents k σ + k
  omega

/-- W1: multiplication by a coprime width reindexes the positions into one cycle. -/
private theorem cyclic_reindexing (n k : ℕ) (h1k : 1 ≤ k) (hk : k < n)
    (hkn : Nat.Coprime k n) (σ : Equiv.Perm (Fin n)) :
    (widthDescents k σ : ℤ) - widthDescents (n - k) σ =
      (cdes ((rho n k (lt_of_lt_of_le h1k hk.le) hkn).trans σ) : ℤ) - k := by
  rw [cdes_rho n k (lt_of_lt_of_le h1k hk.le) hk hkn]
  have hcount := cyclicK_add_width_complement n k hk σ
  omega

private def precomposeEquiv {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := ρ.trans σ
  invFun τ := ρ.symm.trans τ
  left_inv σ := by ext i; simp
  right_inv τ := by ext i; simp

/-- The sum-level conclusion of W1. -/
private theorem cyclic_reindexing_sum (n k : ℕ) (h1k : 1 ≤ k) (hk : k < n)
    (hkn : Nat.Coprime k n) :
    G n k = LaurentPolynomial.T (-(k : ℤ)) *
      ∑ τ : Equiv.Perm (Fin n), LaurentPolynomial.T (cdes τ : ℤ) := by
  let hn : 0 < n := lt_of_lt_of_le h1k hk.le
  let e := precomposeEquiv (rho n k hn hkn)
  unfold G
  calc
    (∑ σ : Equiv.Perm (Fin n),
        LaurentPolynomial.T ((widthDescents k σ : ℤ) - widthDescents (n - k) σ)) =
        ∑ σ : Equiv.Perm (Fin n),
          LaurentPolynomial.T ((cdes (e σ) : ℤ) - k) := by
            apply Finset.sum_congr rfl
            intro σ _
            exact congrArg LaurentPolynomial.T (cyclic_reindexing n k h1k hk hkn σ) |>.trans <|
              by rfl
    _ = ∑ τ : Equiv.Perm (Fin n), LaurentPolynomial.T ((cdes τ : ℤ) - k) := by
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = LaurentPolynomial.T (-(k : ℤ)) *
        ∑ τ : Equiv.Perm (Fin n), LaurentPolynomial.T (cdes τ : ℤ) := by
      simp_rw [sub_eq_add_neg, LaurentPolynomial.T_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      rw [mul_comm]

private def extendLast {m : ℕ} (π : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  π.extendDomain (finSuccAboveEquiv (Fin.last m))

private lemma perm_fix_last_lt {m : ℕ} (τ : Equiv.Perm (Fin (m + 1)))
    (hτ : τ (Fin.last m) = Fin.last m) (i : Fin m) :
    (τ i.castSucc).val < m := by
  apply Fin.val_lt_last
  intro h
  have : i.castSucc = Fin.last m := τ.injective (h.trans hτ.symm)
  exact Fin.ne_of_lt i.castSucc_lt_last this

private def restrictLast {m : ℕ} (τ : Equiv.Perm (Fin (m + 1)))
    (hτ : τ (Fin.last m) = Fin.last m) : Equiv.Perm (Fin m) where
  toFun i := ⟨(τ i.castSucc).val, perm_fix_last_lt τ hτ i⟩
  invFun i := ⟨(τ.symm i.castSucc).val, perm_fix_last_lt τ.symm
    ((τ.symm_apply_eq).2 hτ.symm) i⟩
  left_inv i := by
    apply Fin.ext
    change (τ.symm (⟨(τ i.castSucc).val, _⟩ : Fin m).castSucc).val = i.val
    have hcast : (⟨(τ i.castSucc).val, perm_fix_last_lt τ hτ i⟩ : Fin m).castSucc =
        τ i.castSucc := by
      apply Fin.ext
      rfl
    rw [hcast, τ.symm_apply_apply]
    rfl
  right_inv i := by
    apply Fin.ext
    change (τ (⟨(τ.symm i.castSucc).val, _⟩ : Fin m).castSucc).val = i.val
    have hcast : (⟨(τ.symm i.castSucc).val,
        perm_fix_last_lt τ.symm ((τ.symm_apply_eq).2 hτ.symm) i⟩ : Fin m).castSucc =
        τ.symm i.castSucc := by
      apply Fin.ext
      rfl
    rw [hcast, τ.apply_symm_apply]
    rfl

@[simp] private lemma restrictLast_extendLast {m : ℕ} (π : Equiv.Perm (Fin m)) :
    restrictLast (extendLast π) (by
      apply Equiv.Perm.extendDomain_apply_not_subtype
      simp) = π := by
  ext i
  change (extendLast π i.castSucc).val = (π i).val
  have hcast : extendLast π i.castSucc = (π i).castSucc := by
    rw [show i.castSucc = ((finSuccAboveEquiv (Fin.last m)) i).val by
      simp [finSuccAboveEquiv_apply]]
    change π.extendDomain (finSuccAboveEquiv (Fin.last m))
        ((finSuccAboveEquiv (Fin.last m)) i).val = _
    rw [Equiv.Perm.extendDomain_apply_image]
    simp [finSuccAboveEquiv_apply]
  rw [hcast]
  rfl

private lemma extendLast_restrictLast {m : ℕ} (τ : Equiv.Perm (Fin (m + 1)))
    (hτ : τ (Fin.last m) = Fin.last m) :
    extendLast (restrictLast τ hτ) = τ := by
  ext i
  by_cases hi : i = Fin.last m
  · subst i
    rw [hτ]
    have hfix : extendLast (restrictLast τ hτ) (Fin.last m) = Fin.last m := by
      apply Equiv.Perm.extendDomain_apply_not_subtype
      simp
    exact congrArg Fin.val hfix
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    have hcast : extendLast (restrictLast τ hτ) j.castSucc =
        ((restrictLast τ hτ) j).castSucc := by
      rw [show j.castSucc = ((finSuccAboveEquiv (Fin.last m)) j).val by
        simp [finSuccAboveEquiv_apply]]
      change (restrictLast τ hτ).extendDomain (finSuccAboveEquiv (Fin.last m))
          ((finSuccAboveEquiv (Fin.last m)) j).val = _
      rw [Equiv.Perm.extendDomain_apply_image]
      simp [finSuccAboveEquiv_apply]
    rw [hcast]
    rfl

private theorem cdes_extendLast {m : ℕ} (hm : 0 < m) (π : Equiv.Perm (Fin m)) :
    cdes (extendLast π) = widthDescents 1 π + 1 := by
  have hcast (i : Fin m) : extendLast π i.castSucc = (π i).castSucc := by
    rw [show i.castSucc = ((finSuccAboveEquiv (Fin.last m)) i).val by
      simp [finSuccAboveEquiv_apply]]
    change π.extendDomain (finSuccAboveEquiv (Fin.last m))
        ((finSuccAboveEquiv (Fin.last m)) i).val = _
    rw [Equiv.Perm.extendDomain_apply_image]
    simp [finSuccAboveEquiv_apply]
  have hlastFixed : extendLast π (Fin.last m) = Fin.last m := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simp
  let s := Finset.univ.filter fun j : Fin (m + 1) =>
    extendLast π (finRotate (m + 1) j) < extendLast π j
  have hlast : Fin.last m ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [finRotate_last, hlastFixed]
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    change extendLast π 0 < Fin.last (r + 1)
    apply Fin.lt_last_iff_ne_last.mpr
    change extendLast π (0 : Fin (r + 1)).castSucc ≠ Fin.last (r + 1)
    rw [hcast]
    exact Fin.ne_of_lt (π 0).castSucc_lt_last
  have herase : (s.erase (Fin.last m)).card = widthDescents 1 π := by
    unfold widthDescents
    apply Finset.card_bij
      (s := s.erase (Fin.last m))
      (t := Finset.univ.filter fun i : Fin m =>
        ∃ h : i.val + 1 < m, π ⟨i.val + 1, h⟩ < π i)
      (fun j hj => Fin.castLT j (Fin.val_lt_last (by simpa using (Finset.ne_of_mem_erase hj))))
    · intro j hj
      have hjmem : j ∈ s := Finset.mem_of_mem_erase hj
      have hjlast : j ≠ Fin.last m := by simpa using Finset.ne_of_mem_erase hj
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hjlast
      simp only [Fin.castLT_castSucc, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
      rw [show finRotate (m + 1) i.castSucc =
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ by
        apply Fin.ext
        simpa using congrArg Fin.val (finRotate_of_lt i.isLt)] at hjmem
      by_cases hi : i.val + 1 < m
      · refine ⟨hi, ?_⟩
        have hnext : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (m + 1)) =
            (⟨i.val + 1, hi⟩ : Fin m).castSucc := by
          apply Fin.ext
          rfl
        rw [hnext, hcast] at hjmem
        rw [hcast] at hjmem
        exact Fin.castSucc_lt_castSucc_iff.mp hjmem
      · have hieq : i.val + 1 = m := by omega
        have hnext : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (m + 1)) = Fin.last m := by
          apply Fin.ext
          simp [hieq]
        rw [hnext, hlastFixed] at hjmem
        have hcur : extendLast π i.castSucc < Fin.last m :=
          Fin.lt_last_iff_ne_last.mpr (by
            rw [hcast]
            exact Fin.ne_of_lt (π i).castSucc_lt_last)
        omega
    · intro j₁ hj₁ j₂ hj₂ h
      apply Fin.ext
      simpa using congrArg Fin.val h
    · intro i hi
      rcases (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi) with
        ⟨hibound, hidesc⟩
      refine ⟨i.castSucc, ?_, ?_⟩
      · apply Finset.mem_erase.mpr
        constructor
        · simp
        · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show finRotate (m + 1) i.castSucc =
              ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ by
            apply Fin.ext
            simpa using congrArg Fin.val (finRotate_of_lt i.isLt)]
          have hnext : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (m + 1)) =
              (⟨i.val + 1, hibound⟩ : Fin m).castSucc := by
            apply Fin.ext
            rfl
          rw [hnext, hcast]
          rw [hcast]
          exact Fin.castSucc_lt_castSucc_iff.mpr hidesc
      · apply Fin.ext
        rfl
  unfold cdes
  change s.card = _
  rw [← Finset.card_erase_add_one hlast, herase]

private theorem cdes_precompose_finCycle {n : ℕ} (a : Fin n)
    (τ : Equiv.Perm (Fin n)) :
    cdes ((finCycle a).trans τ) = cdes τ := by
  have hcommute (j : Fin n) :
      finCycle a (finRotate n j) = finRotate n (finCycle a j) := by
    haveI : NeZero n := j.neZero
    simp only [finCycle_apply, finRotate_apply]
    ac_rfl
  apply Finset.card_equiv (finCycle a)
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change τ (finCycle a (finRotate n j)) < τ (finCycle a j) ↔ _
  rw [hcommute]

private def rotationShift {m : ℕ} (r : Fin (m + 1)) : Fin (m + 1) :=
  Fin.last m - r

private def fromCyclePair {m : ℕ} (x : Fin (m + 1) × Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) :=
  (finCycle (rotationShift x.1)).trans (extendLast x.2)

@[simp] private lemma fromCyclePair_symm_last {m : ℕ}
    (x : Fin (m + 1) × Equiv.Perm (Fin m)) :
    (fromCyclePair x).symm (Fin.last m) = x.1 := by
  apply (fromCyclePair x).injective
  rw [Equiv.apply_symm_apply]
  symm
  change extendLast x.2 (finCycle (rotationShift x.1) x.1) = Fin.last m
  have hcycle : finCycle (rotationShift x.1) x.1 = Fin.last m := by
    simp [finCycle_apply, rotationShift]
  rw [hcycle]
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp

private def normalizedCycle {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) :
    Equiv.Perm (Fin (m + 1)) :=
  (finCycle (rotationShift (τ.symm (Fin.last m)))).symm.trans τ

@[simp] private lemma normalizedCycle_last {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) :
    normalizedCycle τ (Fin.last m) = Fin.last m := by
  change τ ((finCycle (rotationShift (τ.symm (Fin.last m)))).symm (Fin.last m)) = _
  have hrotate :
      (finCycle (rotationShift (τ.symm (Fin.last m)))).symm (Fin.last m) =
        τ.symm (Fin.last m) := by
    apply (finCycle (rotationShift (τ.symm (Fin.last m)))).symm_apply_eq.mpr
    symm
    simp [finCycle_apply, rotationShift]
  rw [hrotate, Equiv.apply_symm_apply]

private def cycleDecompose {m : ℕ} :
    Equiv.Perm (Fin (m + 1)) ≃ Fin (m + 1) × Equiv.Perm (Fin m) where
  toFun τ := (τ.symm (Fin.last m), restrictLast (normalizedCycle τ) (normalizedCycle_last τ))
  invFun := fromCyclePair
  left_inv τ := by
    change fromCyclePair
      (τ.symm (Fin.last m), restrictLast (normalizedCycle τ) (normalizedCycle_last τ)) = τ
    unfold fromCyclePair
    rw [extendLast_restrictLast]
    unfold normalizedCycle
    ext i
    simp
  right_inv x := by
    apply Prod.ext
    · exact fromCyclePair_symm_last x
    · rcases x with ⟨r, π⟩
      change restrictLast (normalizedCycle (fromCyclePair (r, π)))
        (normalizedCycle_last (fromCyclePair (r, π))) = π
      have hnorm : normalizedCycle (fromCyclePair (r, π)) = extendLast π := by
        unfold normalizedCycle
        rw [fromCyclePair_symm_last]
        unfold fromCyclePair
        ext i
        simp
      ext i
      change (normalizedCycle (fromCyclePair (r, π)) i.castSucc).val = (π i).val
      rw [Equiv.congr_fun hnorm i.castSucc]
      have hcast : extendLast π i.castSucc = (π i).castSucc := by
        rw [show i.castSucc = ((finSuccAboveEquiv (Fin.last m)) i).val by
          simp [finSuccAboveEquiv_apply]]
        change π.extendDomain (finSuccAboveEquiv (Fin.last m))
            ((finSuccAboveEquiv (Fin.last m)) i).val = _
        rw [Equiv.Perm.extendDomain_apply_image]
        simp [finSuccAboveEquiv_apply]
      rw [hcast]
      rfl

/-- W2, with the necessary sharp hypothesis `2 ≤ n` (the proposed `1 ≤ n` version is false). -/
private theorem cyclic_descent_distribution (n : ℕ) (hn : 2 ≤ n) :
    (∑ τ : Equiv.Perm (Fin n), LaurentPolynomial.T (cdes τ : ℤ)) =
      (n : LaurentPolynomial ℤ) * LaurentPolynomial.T 1 * eulerian (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : 0 < m := by omega
  have hweight (x : Fin (m + 1) × Equiv.Perm (Fin m)) :
      cdes (fromCyclePair x) = widthDescents 1 x.2 + 1 := by
    exact (cdes_precompose_finCycle (rotationShift x.1) (extendLast x.2)).trans
      (cdes_extendLast hm x.2)
  calc
    (∑ τ : Equiv.Perm (Fin (m + 1)), LaurentPolynomial.T (cdes τ : ℤ)) =
        ∑ x : Fin (m + 1) × Equiv.Perm (Fin m),
          LaurentPolynomial.T (cdes (fromCyclePair x) : ℤ) := by
      apply Fintype.sum_equiv cycleDecompose
      intro τ
      exact congrArg (fun ξ => LaurentPolynomial.T (cdes ξ : ℤ))
        (cycleDecompose.symm_apply_apply τ).symm
    _ = ∑ x : Fin (m + 1) × Equiv.Perm (Fin m),
          LaurentPolynomial.T ((widthDescents 1 x.2 : ℤ) + 1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hweight x]
      norm_cast
    _ = ((m + 1 : ℕ) : LaurentPolynomial ℤ) * LaurentPolynomial.T 1 * eulerian m := by
      rw [Fintype.sum_prod_type]
      simp_rw [LaurentPolynomial.T_add]
      simp only [eulerian]
      calc
        (∑ _ : Fin (m + 1), ∑ π : Equiv.Perm (Fin m),
            LaurentPolynomial.T (widthDescents 1 π : ℤ) * LaurentPolynomial.T 1) =
            (m + 1) • (∑ π : Equiv.Perm (Fin m),
              LaurentPolynomial.T (widthDescents 1 π : ℤ) * LaurentPolynomial.T 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ = ((m + 1 : ℕ) : LaurentPolynomial ℤ) * LaurentPolynomial.T 1 *
            ∑ π : Equiv.Perm (Fin m), LaurentPolynomial.T (widthDescents 1 π : ℤ) := by
          rw [nsmul_eq_mul, ← Finset.sum_mul]
          ac_rfl

/-- Conjecture 9 holds. -/
theorem result : claim := by
  intro n k h1k hk hkn
  have h2n : 2 ≤ n := by omega
  rw [cyclic_reindexing_sum n k h1k hk hkn,
    cyclic_descent_distribution n h2n]
  calc
    LaurentPolynomial.T (-(k : ℤ)) *
          ((n : LaurentPolynomial ℤ) * LaurentPolynomial.T 1 * eulerian (n - 1)) =
        (n : LaurentPolynomial ℤ) *
          (LaurentPolynomial.T (-(k : ℤ)) * LaurentPolynomial.T 1) * eulerian (n - 1) := by
      ac_rfl
    _ = (n : LaurentPolynomial ℤ) * LaurentPolynomial.T (1 - (k : ℤ)) *
          eulerian (n - 1) := by
      rw [← LaurentPolynomial.T_add]
      congr 3
      omega

end

end D5.S1.Words.DavisWidthDescentDifferenceCoprime
