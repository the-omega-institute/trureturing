/- GID: D5/S3/Arith/Divisors/ErdosNicolas/FiniteChecker
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/Base00.chunk_checked
   digest: Sound complete divisor certificates for the strong induction target. -/

import D5.S3.Arith.Divisors.ErdosNicolas.PairChecker
import D5.S3.Arith.Divisors.ErdosNicolas.DivisorChecker

/-! Reflection bridges for complete integer certificates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

/-- A certificate contains a number, a factorization and its entire sorted divisor table. -/
structure NumberCertificate where
  number : ℕ
  factors : List (ℕ × ℕ)
  divisors : List ℕ

/-- All arithmetic in this checker is natural-number arithmetic. -/
def checkGood (Q : ℕ) (c : NumberCertificate) : Bool :=
  decide (0 < Q) && checkDivisors c.number c.factors c.divisors &&
    if c.number ∈ exceptions then
      decide (Q * c.divisors.length < pairLower Q c.divisors ∧
        7 * pairUpper Q c.divisors < 8 * Q * c.divisors.length)
    else decide (pairUpper Q c.divisors < Q * c.divisors.length)

/-- Reflection into the exact strengthened target, including both exceptional bounds. -/
theorem checkGood_sound {Q : ℕ} {c : NumberCertificate} (h : checkGood Q c = true) :
    Good c.number := by
  unfold checkGood at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hQ', hd⟩, hbound⟩ := h
  obtain ⟨hs, he, ht⟩ := checkDivisors_sound hd
  unfold Good
  split_ifs with hn
  · rw [if_pos hn] at hbound
    obtain ⟨hl, hu⟩ := of_decide_eq_true hbound
    exact exceptional_of_pairBounds hQ' hs.nodup he ht hl hu
  · rw [if_neg hn] at hbound
    exact hHat_lt_of_pairUpper hQ' hs.nodup he ht (of_decide_eq_true hbound)

/-- A block has consecutive targets; interval coverage follows from its length. -/
def checkGoodBlock (Q : ℕ) : ℕ → List NumberCertificate → Bool
  | _, [] => true
  | start, c :: cs =>
      decide (c.number = start) && checkGood Q c && checkGoodBlock Q (start + 1) cs

theorem checkGoodBlock_append (Q start : ℕ) (xs ys : List NumberCertificate) :
    checkGoodBlock Q start (xs ++ ys) =
      (checkGoodBlock Q start xs && checkGoodBlock Q (start + xs.length) ys) := by
  induction xs generalizing start with
  | nil => simp [checkGoodBlock]
  | cons c xs ih =>
    simp [checkGoodBlock, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Bool.and_assoc]

theorem checkGoodBlock_sound {Q start : ℕ} {cs : List NumberCertificate}
    (h : checkGoodBlock Q start cs = true) :
    ∀ n, start ≤ n → n < start + cs.length → Good n := by
  induction cs generalizing start with
  | nil => intro n hn hlast; simp only [List.length_nil, Nat.add_zero] at hlast; omega
  | cons c cs ih =>
    simp only [checkGoodBlock, Bool.and_eq_true, decide_eq_true_eq] at h
    intro n hn hlast
    by_cases he : n = start
    · subst n
      rw [← h.1.1]
      exact checkGood_sound h.1.2
    · apply ih h.2 n <;> simp only [List.length_cons] at hlast <;> omega

/-- Nonconsecutive blocks certify every explicitly listed integer. -/
private theorem checkGoodList_sound {Q : ℕ} {cs : List NumberCertificate}
    (h : cs.all (checkGood Q) = true) :
    ∀ c ∈ cs, Good c.number := by
  intro c hc
  exact checkGood_sound ((List.all_eq_true.mp h) c hc)

/-- The exact set of target integers in a certificate block. -/
def certifiedValues (cs : List NumberCertificate) : Finset ℕ :=
  (cs.map NumberCertificate.number).toFinset

theorem good_of_mem_certifiedValues {Q n : ℕ} {cs : List NumberCertificate}
    (h : cs.all (checkGood Q) = true) (hn : n ∈ certifiedValues cs) : Good n := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
  exact checkGoodList_sound h c hc

#print axioms checkGood_sound
#print axioms checkGoodBlock_sound

end D5.S3.Arith.ErdosNicolas
