/- GID: D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation
   generality: I
   mirror-B: D5/B/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation
   mirror-E: none(waiver:finite-certificate-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.claim; result=D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.result; claim=D5/S3/PrimeForms/TerminalPortFiveSplitCompatibilityRefutation.claim
   digest: The terminal port (14,3,5) with unit zeros at every prime admits no distinct five-prime point, refuting the broad joint compatibility claim. -/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace D5.S3.PrimeForms.TerminalPortFiveSplitCompatibilityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

def Terminal (R c p : Nat) : Prop :=
  0 < R ∧ 0 < c ∧ p.Prime ∧ c * p = R + 1

def form (R c : Nat) (x : Fin 5 → Nat) : Int :=
  (c : Int) * ∏ i : Fin 5, (x i : Int) -
    (R : Int) * ∑ i : Fin 5, ∏ j ∈ Finset.univ.erase i, (x j : Int) - 1

def localUnits (R c : Nat) : Prop :=
  ∀ ell : Nat, ell.Prime → ∃ x : Fin 5 → ZMod ell,
    (∀ i, x i ≠ 0) ∧
      (c : ZMod ell) * ∏ i : Fin 5, x i -
        (R : ZMod ell) * ∑ i : Fin 5, ∏ j ∈ Finset.univ.erase i, x j - 1 = 0

def primePoint (R c p : Nat) : Prop :=
  ∃ x : Fin 5 → Nat,
    (∀ i, (x i).Prime ∧ p < x i) ∧
      (∀ i j, i ≠ j → x i ≠ x j) ∧ form R c x = 0

def claim : Prop :=
  ∃ A : Nat → Nat → Nat → Prop,
    ∀ R c p : Nat, Terminal R c p → 4 < R → 3 < p →
      A R c p ∧ (A R c p → localUnits R c → primePoint R c p)

def deriv : List Nat → Nat
  | [] => 0
  | q :: xs => xs.prod + q * deriv xs

def Balance (R C : Nat) (xs : List Nat) : Prop :=
  C * xs.prod = R * deriv xs + 1

def search : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | 1, R, C, lo =>
      C ≠ 0 &&
        let q := (R + 1) / C
        (lo < q) && (C * q == R + 1)
  | n + 2, R, C, lo =>
      C ≠ 0 &&
        ((List.range ((((n + 2) * R) / C) + 1)).any fun q =>
          (lo < q) && ((n == 0) || q.Prime) && (R % q != 0) && R < C * q &&
            search (n + 1) (R * q) (C * q - R) q)

theorem result : ¬claim := by
  have deriv_pruning : ∀ (q : Nat) (xs : List Nat),
    (∀ t ∈ xs, q < t) → (∀ t ∈ xs, 0 < t) → xs ≠ [] →
    q * deriv xs < xs.length * xs.prod := by
    intro q xs hq hpos hne
    induction xs with
    | nil => contradiction
    | cons t ys ih =>
      simp only [deriv, List.length_cons, List.prod_cons]
      have hqt : q < t := hq t (by simp)
      have ht : 0 < t := hpos t (by simp)
      have hprod : 0 < ys.prod := by
        exact List.prod_pos (by intro u hu; exact hpos u (by simp [hu]))
      by_cases hy : ys = []
      · subst ys
        simp [deriv] at *
        omega
      · have hbound := ih (by intro u hu; exact hq u (by simp [hu]))
            (by intro u hu; exact hpos u (by simp [hu])) hy
        nlinarith [mul_lt_mul_of_pos_left hbound ht,
          mul_lt_mul_of_pos_right hqt hprod]

  have balance_step : ∀ (R C q : Nat) (xs : List Nat),
    0 < R → 0 < q → (∀ t ∈ xs, 0 < t) → Balance R C (q :: xs) →
    R < C * q ∧ Balance (R * q) (C * q - R) xs := by
    intro R C q xs hR hq hpos hb
    have hp : 0 < xs.prod :=
      List.prod_pos (by intro u hu; exact hpos u hu)
    have heq : C * q * xs.prod = R * (xs.prod + q * deriv xs) + 1 := by
      simpa [Balance, deriv, mul_assoc] using hb
    have hgt : R < C * q := by
      by_contra hnot
      have hle : C * q ≤ R := by omega
      have hleMul : C * q * xs.prod ≤ R * xs.prod :=
        Nat.mul_le_mul_right xs.prod hle
      have hupper : R * xs.prod ≤ R * (xs.prod + q * deriv xs) :=
        Nat.mul_le_mul_left R (Nat.le_add_right _ _)
      omega
    refine ⟨hgt, ?_⟩
    have hsub : C * q - R + R = C * q := Nat.sub_add_cancel (by omega)
    dsimp [Balance]
    nlinarith [hsub]

  have balance_pruning : ∀ (R C q : Nat) (xs : List Nat),
    0 < R → 0 < q → (∀ t ∈ xs, q < t) →
    (∀ t ∈ xs, 0 < t) → xs ≠ [] → Balance R C (q :: xs) →
    C * q ≤ (xs.length + 1) * R := by
    intro R C q xs hR hq hqt hpos hne hb
    have hp : 0 < xs.prod :=
      List.prod_pos (by intro u hu; exact hpos u hu)
    have hderiv := deriv_pruning q xs hqt hpos hne
    have heq : C * q * xs.prod = R * (xs.prod + q * deriv xs) + 1 := by
      simpa [Balance, deriv, mul_assoc] using hb
    have hmul : R * (q * deriv xs + 1) ≤ R * (xs.length * xs.prod) :=
      Nat.mul_le_mul_left R (by omega)
    have hone : R * (q * deriv xs) + 1 ≤ R * (q * deriv xs + 1) := by
      nlinarith
    nlinarith

  have deriv_perm : ∀ {xs ys : List Nat}, xs.Perm ys → deriv xs = deriv ys := by
    intro xs ys h
    induction h with
    | nil => rfl
    | @cons x l₁ l₂ hp ih =>
      simp only [deriv]
      rw [hp.prod_eq, ih]
    | @swap x y l =>
      simp only [deriv, List.prod_cons]
      ring
    | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

  have form_balance : ∀ (R C : Nat) (x : Fin 5 → Nat),
    form R C x = 0 ↔ Balance R C [x 0, x 1, x 2, x 3, x 4] := by
    intro R C x
    have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
    have h1 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 1 = {0, 2, 3, 4} := by decide
    have h2 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 2 = {0, 1, 3, 4} := by decide
    have h3 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 3 = {0, 1, 2, 4} := by decide
    have h4 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 4 = {0, 1, 2, 3} := by decide
    simp [form, Balance, deriv, huniv, h1, h2, h3, h4]
    constructor
    · intro h
      have hInt : (C : Int) * (x 0 * x 1 * x 2 * x 3 * x 4 : Nat) =
          (R : Int) * (x 1 * x 2 * x 3 * x 4 +
            x 0 * x 2 * x 3 * x 4 + x 0 * x 1 * x 3 * x 4 +
            x 0 * x 1 * x 2 * x 4 + x 0 * x 1 * x 2 * x 3 : Nat) + 1 := by
        push_cast at h ⊢
        linear_combination h
      have hNat : C * (x 0 * x 1 * x 2 * x 3 * x 4) =
          R * (x 1 * x 2 * x 3 * x 4 +
            x 0 * x 2 * x 3 * x 4 + x 0 * x 1 * x 3 * x 4 +
            x 0 * x 1 * x 2 * x 4 + x 0 * x 1 * x 2 * x 3) + 1 := by
        exact_mod_cast hInt
      nlinarith [hNat]
    · intro h
      have hNat : C * (x 0 * x 1 * x 2 * x 3 * x 4) =
          R * (x 1 * x 2 * x 3 * x 4 +
            x 0 * x 2 * x 3 * x 4 + x 0 * x 1 * x 3 * x 4 +
            x 0 * x 1 * x 2 * x 4 + x 0 * x 1 * x 2 * x 3) + 1 := by
        nlinarith [h]
      have hInt : (C : Int) * (x 0 * x 1 * x 2 * x 3 * x 4 : Nat) =
          (R : Int) * (x 1 * x 2 * x 3 * x 4 +
            x 0 * x 2 * x 3 * x 4 + x 0 * x 1 * x 3 * x 4 +
            x 0 * x 1 * x 2 * x 4 + x 0 * x 1 * x 2 * x 3 : Nat) + 1 := by
        exact_mod_cast hNat
      push_cast at hInt ⊢
      nlinarith [hInt]

  have local_units14 : localUnits 14 3 := by
    intro ell hp
    letI : Fact ell.Prime := ⟨hp⟩
    by_cases h5 : ell = 5
    · subst ell
      let x : Fin 5 → ZMod 5 := ![1, 1, -1, 3, 2]
      refine ⟨x, ?_, ?_⟩
      · intro i
        fin_cases i <;> decide +kernel +revert
      · decide +kernel +revert
    · let x : Fin 5 → ZMod ell := ![5, 1, -1, 1, -1]
      have hfive : (5 : ZMod ell) ≠ 0 := by
        intro hz
        have hdiv : ell ∣ 5 := (ZMod.natCast_eq_zero_iff 5 ell).mp hz
        exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hdiv)
      refine ⟨x, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [x, hfive]
      · have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
        have h1 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 1 = {0, 2, 3, 4} := by decide
        have h2 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 2 = {0, 1, 3, 4} := by decide
        have h3 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 3 = {0, 1, 2, 4} := by decide
        have h4 : ({0, 1, 2, 3, 4} : Finset (Fin 5)).erase 4 = {0, 1, 2, 3} := by decide
        simp [huniv, h1, h2, h3, h4, x]
        ring

  have search_complete : ∀ (R C lo : Nat) (xs : List Nat),
    0 < R → 0 < C → Balance R C xs → xs.SortedLT →
    (∀ q ∈ xs, q.Prime) → (∀ q ∈ xs, lo < q) → xs ≠ [] →
    search xs.length R C lo = true := by
    intro R C lo xs hR hC hb hs hprime hlow hne
    induction xs generalizing R C lo with
    | nil => contradiction
    | cons q ys ih =>
      have hqprime : q.Prime := hprime q (by simp)
      have hqpos : 0 < q := hqprime.pos
      have hloq : lo < q := hlow q (by simp)
      have hnotdiv : ¬q ∣ R := by
        intro hdiv
        have hleft : q ∣ C * (q :: ys).prod := by
          simp only [List.prod_cons]
          exact ⟨C * ys.prod, by ring⟩
        have hright : q ∣ R * deriv (q :: ys) :=
          dvd_mul_of_dvd_left hdiv _
        rw [hb] at hleft
        have hone : q ∣ (R * deriv (q :: ys) + 1) - R * deriv (q :: ys) :=
          Nat.dvd_sub hleft hright
        have hone' : q ∣ 1 := by simpa using hone
        exact hqprime.ne_one (Nat.dvd_one.mp hone')
      have hmod : R % q ≠ 0 := by
        intro hzero
        exact hnotdiv (Nat.dvd_of_mod_eq_zero hzero)
      have hysprime : ∀ t ∈ ys, t.Prime := by
        intro t ht
        exact hprime t (by simp [ht])
      have hyspos : ∀ t ∈ ys, 0 < t := by
        intro t ht
        exact (hysprime t ht).pos
      have hysSorted : ys.SortedLT := by
        exact (List.sortedLT_iff_pairwise.mp hs).tail.sortedLT
      have hqys : ∀ t ∈ ys, q < t := by
        intro t ht
        exact (List.pairwise_cons.mp (List.sortedLT_iff_pairwise.mp hs)).1 t ht
      cases ys with
      | nil =>
        have heq : C * q = R + 1 := by
          simpa [Balance, deriv] using hb
        have hquot : (R + 1) / C = q := by
          rw [← heq, Nat.mul_div_cancel_left q (by omega)]
        simpa [search, hC.ne', hquot, hloq, hqprime, heq]
      | cons t rest =>
        have hysne : (t :: rest) ≠ [] := by simp
        obtain ⟨hgt, hupdated⟩ := balance_step R C q (t :: rest) hR hqpos hyspos hb
        have hbound := balance_pruning R C q (t :: rest)
          hR hqpos hqys hyspos hysne hb
        have hqupper : q ≤ ((t :: rest).length + 1) * R / C := by
          apply (Nat.le_div_iff_mul_le hC).2
          simpa [mul_comm] using hbound
        have hnext : search (t :: rest).length (R * q) (C * q - R) q = true := by
          apply ih (R := R * q) (C := C * q - R) (lo := q)
            (by positivity) (by omega) hupdated hysSorted hysprime hqys hysne
        change (C ≠ 0 &&
          (List.range ((((t :: rest).length + 1) * R) / C + 1)).any
            (fun u => (lo < u) && ((rest.length == 0) || u.Prime) &&
              (R % u != 0) &&
              R < C * u &&
              search (t :: rest).length (R * u) (C * u - R) u)) = true
        simp only [Bool.and_eq_true]
        constructor
        · simp [hC.ne']
        · apply List.any_eq_true.mpr
          refine ⟨q, List.mem_range.mpr (by omega), ?_⟩
          simp [hloq, hqprime, hgt, hmod]
          simpa only [List.length_cons] using hnext

  have no_prime_point14 : ¬primePoint 14 3 5 := by
    rintro ⟨x, hp, hdistinct, hform⟩
    let raw : List Nat := List.ofFn x
    let sorted : List Nat := raw.mergeSort (fun a b => decide (a ≤ b))
    have hinj : Function.Injective x := by
      intro i j heq
      by_contra hij
      exact hdistinct i j hij heq
    have hnodup : raw.Nodup := List.nodup_ofFn_ofInjective hinj
    have hperm : sorted.Perm raw := List.mergeSort_perm raw _
    have hstrict : sorted.SortedLT :=
      (List.sortedLE_mergeSort (l := raw)).sortedLT_of_nodup
        (hperm.nodup_iff.mpr hnodup)
    have hrawPrime : ∀ q ∈ raw, q.Prime := by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact (hp i).1
    have hrawLow : ∀ q ∈ raw, 5 < q := by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact (hp i).2
    have hsortedPrime : ∀ q ∈ sorted, q.Prime := by
      intro q hq
      exact hrawPrime q (hperm.mem_iff.mp hq)
    have hsortedLow : ∀ q ∈ sorted, 5 < q := by
      intro q hq
      exact hrawLow q (hperm.mem_iff.mp hq)
    have hrawBalance : Balance 14 3 raw := by
      simpa [raw, List.ofFn_succ] using (form_balance 14 3 x).mp hform
    have hsortedBalance : Balance 14 3 sorted := by
      dsimp [Balance] at hrawBalance ⊢
      rw [hperm.prod_eq, deriv_perm hperm]
      exact hrawBalance
    have hlength : sorted.length = 5 := by
      rw [hperm.length_eq]
      simp [raw]
    have hne : sorted ≠ [] := by
      intro he
      simp [he] at hlength
    have hfound : search 5 14 3 5 = true := by
      simpa only [hlength] using
        (search_complete 14 3 5 sorted (by norm_num) (by norm_num)
          hsortedBalance hstrict hsortedPrime hsortedLow hne)
    have hnegative : search 5 14 3 5 = false := by decide +kernel
    simp [hnegative] at hfound

  intro h
  obtain ⟨A, hjoint⟩ := h
  have hterminal : Terminal 14 3 5 := by norm_num [Terminal]
  obtain ⟨hA, huse⟩ := hjoint 14 3 5 hterminal (by norm_num) (by norm_num)
  exact no_prime_point14 (huse hA local_units14)

#print axioms result

end D5.S3.PrimeForms.TerminalPortFiveSplitCompatibilityRefutation
