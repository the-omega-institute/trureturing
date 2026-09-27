/- GID: D5/S0/Certificates/MercaResidueSumEvenOrderRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/MercaResidueSumEvenOrderRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.claim; result=D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.result; claim=D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.claim
   digest: Refutes Merca Conjecture 1 at (a, m) = (2, 15). -/

/- Formalization classification:
   proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9191)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.GroupTheory.OrderOfElement

namespace D5.S0.Certificates.MercaResidueSumEvenOrderRefutation

/-- `Σ_{i=1}^{ord_m(a)} (a^i mod m)` with `%` the least non-negative remainder
(page 2) and `ord_m(a)` the paper's multiplicative order (page 17) -- pinned
Mathlib's `orderOf (a : ZMod m)`: the least positive `n` with `a^n ≡ 1 (mod m)`,
`0` when no such `n` exists. -/
noncomputable def residueSum (m a : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 (orderOf (a : ZMod m)), a ^ i % m

/-- Conjecture 1 as printed (both sides doubled to stay in `ℕ`; `ord` even makes
`m·ord/2` an integer). -/
def claim : Prop :=
  ∀ a m : ℕ, 0 < a → 0 < m → Nat.Coprime a m → Nat.Coprime (a - 1) m →
    Even (orderOf (a : ZMod m)) →
      2 * residueSum m a = m * orderOf (a : ZMod m)

/-- Conjecture 1 is false at `(a, m) = (2, 15)`: the sum is `15`, the right side `30`. -/
theorem result : ¬ claim := by
  have hord : orderOf (2 : ZMod 15) = 4 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    cases m with
    | zero => exact (Nat.lt_irrefl 0 hpos).elim
    | succ m =>
        cases m with
        | zero => decide
        | succ m =>
            cases m with
            | zero => decide
            | succ m =>
                cases m with
                | zero => decide
                | succ m =>
                    intro _
                    exact (Nat.not_lt_zero m)
                      (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm))))
  have hsum : residueSum 15 2 = 15 := by
    unfold residueSum
    have h2 : ((2 : ℕ) : ZMod 15) = (2 : ZMod 15) := by rfl
    rw [h2, hord]
    decide
  have heven : Even (orderOf (2 : ZMod 15)) := by
    rw [hord]
    exact ⟨2, by decide⟩
  have hne :
      2 * residueSum 15 2 ≠ 15 * orderOf (2 : ZMod 15) := by
    simp [hsum, hord]
  intro hclaim
  have h2 : ((2 : ℕ) : ZMod 15) = (2 : ZMod 15) := by rfl
  have heven' : Even (orderOf ((2 : ℕ) : ZMod 15)) := by simpa [h2] using heven
  have heq := hclaim 2 15 (by decide) (by decide) (by decide) (by decide) heven'
  exact hne (by simpa [h2] using heq)

example :
    orderOf (2 : ZMod 15) = 4 ∧ residueSum 15 2 = 15 := by
  have hord : orderOf (2 : ZMod 15) = 4 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    cases m with
    | zero => exact (Nat.lt_irrefl 0 hpos).elim
    | succ m =>
        cases m with
        | zero => decide
        | succ m =>
            cases m with
            | zero => decide
            | succ m =>
                cases m with
                | zero => decide
                | succ m =>
                    intro _
                    exact (Nat.not_lt_zero m)
                      (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm))))
  have hsum : residueSum 15 2 = 15 := by
    unfold residueSum
    have h2 : ((2 : ℕ) : ZMod 15) = (2 : ZMod 15) := by rfl
    rw [h2, hord]
    decide
  exact ⟨hord, hsum⟩

example :
    0 < (2 : ℕ) ∧ 0 < (15 : ℕ) ∧ Nat.Coprime 2 15 ∧ Nat.Coprime (2 - 1) 15 ∧
      Even (orderOf (2 : ZMod 15)) := by
  have hord : orderOf (2 : ZMod 15) = 4 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    cases m with
    | zero => exact (Nat.lt_irrefl 0 hpos).elim
    | succ m =>
        cases m with
        | zero => decide
        | succ m =>
            cases m with
            | zero => decide
            | succ m =>
                cases m with
                | zero => decide
                | succ m =>
                    intro _
                    exact (Nat.not_lt_zero m)
                      (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm))))
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rw [hord]
  exact ⟨2, by decide⟩

example :
    orderOf (3 : ZMod 7) = 6 ∧ residueSum 7 3 = 21 ∧
      2 * residueSum 7 3 = 7 * orderOf (3 : ZMod 7) := by
  have hord : orderOf (3 : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    cases m with
    | zero => exact (Nat.lt_irrefl 0 hpos).elim
    | succ m =>
        cases m with
        | zero => decide
        | succ m =>
            cases m with
            | zero => decide
            | succ m =>
                cases m with
                | zero => decide
                | succ m =>
                    cases m with
                    | zero => decide
                    | succ m =>
                        cases m with
                        | zero => decide
                        | succ m =>
                            intro _
                            exact (Nat.not_lt_zero m)
                              (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                                  (Nat.lt_of_succ_lt_succ
                                    (Nat.lt_of_succ_lt_succ hm))))))
  have hsum : residueSum 7 3 = 21 := by
    unfold residueSum
    have h3 : ((3 : ℕ) : ZMod 7) = (3 : ZMod 7) := by rfl
    rw [h3, hord]
    decide
  exact ⟨hord, hsum, by simp [hord, hsum]⟩

#print axioms result

end D5.S0.Certificates.MercaResidueSumEvenOrderRefutation
