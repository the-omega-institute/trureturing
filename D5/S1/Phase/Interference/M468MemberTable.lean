/- GID: D5/S1/Phase/Interference/M468MemberTable
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/M468MemberTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The m468 side column comes from the frozen Jacobi selector; 469 composite. -/

import D5.S1.Phase.Interference.ZolotarevSelector
import D5.S1.Phase.SeatTowerArithmetic

namespace D5.S1.Phase.Interference.M468MemberTable

open scoped NumberTheorySymbols

def m468 : ℕ := 468

def m468Successor : ℕ := m468 + 1

/- The phase classifier is independent of the frozen Jacobi column. -/
def m468PsiSelector (psi : ℤ) : Prop := psi % 24 = 0

instance : DecidablePred m468PsiSelector := by
  intro psi
  unfold m468PsiSelector
  infer_instance

theorem m468PsiSelector_iff_even_quotient (psi q : ℤ) (hPsi : psi = 12 * q) :
    m468PsiSelector psi ↔ Even q := by
  rw [m468PsiSelector, ← Int.dvd_iff_emod_eq_zero]
  exact D5.S1.Phase.SeatTowerArithmetic.twenty_four_dvd_iff_even_quotient psi q hPsi

inductive M468Side
  | same
  | different

/- This is the split-factor column of the frozen Jacobi selector, evaluated at
   the m=468 beta datum. It is independent of the mod-24 classifier. -/
def m468Beta : ℤ := -384

def m468SelectorValue (p : ℕ) : ℤ := J(m468Beta | p)

def m468SideOfSplitPrime (p : ℕ) : M468Side :=
  if m468SelectorValue p = 1 then M468Side.same else M468Side.different

theorem m468_selector_at_seven : m468SelectorValue 7 = 1 := by
  rw [m468SelectorValue, m468Beta, jacobiSym.mod_left]
  change J(1 | 7) = 1
  simp

theorem m468_selector_at_sixty_seven : m468SelectorValue 67 = -1 := by
  rw [m468SelectorValue, m468Beta, jacobiSym.mod_left]
  change J(18 | 67) = -1
  rw [show (18 : Int) = 2 * 3 ^ 2 by norm_num, jacobiSym.mul_left,
    jacobiSym.sq_one' (by norm_num : (3 : Int).gcd 67 = 1), mul_one,
    jacobiSym.at_two (by decide : Odd 67), ZMod.χ₈_nat_eq_if_mod_eight]
  norm_num

theorem m468_side_at_seven : m468SideOfSplitPrime 7 = M468Side.same := by
  simp [m468SideOfSplitPrime, m468_selector_at_seven]

theorem m468_side_at_sixty_seven :
    m468SideOfSplitPrime 67 = M468Side.different := by
  simp [m468SideOfSplitPrime, m468_selector_at_sixty_seven]

def m468SplitPrime (p : ℕ) : Prop := p = 7 ∨ p = 67

/- The two rows are the finite successor-side member table. In particular, the
   table does not mention the Jacobi selector values used to define side. -/
def m468PhaseMember (p : ℕ) (psi : ℤ) : Prop :=
  (p = 7 ∧ psi % 24 = 0) ∨ (p = 67 ∧ psi % 24 = 12)

def m468SplitPrimeSameSide (p : ℕ) (psi : ℤ)
    (_hPsi : (12 : ℤ) ∣ psi) : Prop :=
  m468SplitPrime p ∧ m468SideOfSplitPrime p = M468Side.same

def m468SplitPrimeDifferentSide (p : ℕ) (psi : ℤ)
    (_hPsi : (12 : ℤ) ∣ psi) : Prop :=
  m468SplitPrime p ∧ m468SideOfSplitPrime p = M468Side.different

theorem m468_split_prime_same_side_iff
    (p : ℕ) (psi : ℤ) (hPsi : (12 : ℤ) ∣ psi)
    (hMember : m468PhaseMember p psi) :
  m468SplitPrimeSameSide p psi hPsi ↔ psi % 24 = 0 := by
  rcases hMember with ⟨rfl, hZero⟩ | ⟨rfl, hTwelve⟩
  · simp [m468SplitPrimeSameSide, m468SplitPrime, m468_side_at_seven, hZero]
  · simp [m468SplitPrimeSameSide, m468SplitPrime, m468_side_at_sixty_seven,
      hTwelve]

theorem m468_split_prime_different_side_iff
    (p : ℕ) (psi : ℤ) (hPsi : (12 : ℤ) ∣ psi)
    (hMember : m468PhaseMember p psi) :
  m468SplitPrimeDifferentSide p psi hPsi ↔ psi % 24 = 12 := by
  rcases hMember with ⟨rfl, hZero⟩ | ⟨rfl, hTwelve⟩
  · simp [m468SplitPrimeDifferentSide, m468SplitPrime, m468_side_at_seven,
      hZero]
  · simp [m468SplitPrimeDifferentSide, m468SplitPrime,
      m468_side_at_sixty_seven, hTwelve]

theorem m468_split_prime_characterization
    (p : ℕ) (psi : ℤ) (hPsi : (12 : ℤ) ∣ psi)
    (hMember : m468PhaseMember p psi) :
    (m468SplitPrimeSameSide p psi hPsi ↔ psi % 24 = 0) ∧
      (m468SplitPrimeDifferentSide p psi hPsi ↔ psi % 24 = 12) := by
  exact ⟨m468_split_prime_same_side_iff p psi hPsi hMember,
    m468_split_prime_different_side_iff p psi hPsi hMember⟩

/- The zero-only column is the frozen selector value on every proper prime
   divisor. It is not defined by primality. -/
def m468ZeroOnlyProperty : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ m468Successor → p ≠ m468Successor →
    m468SelectorValue p = 0

theorem m468_zero_only_iff_successor_prime :
    m468ZeroOnlyProperty ↔ Nat.Prime m468Successor := by
  constructor
  · intro hZeroOnly
    by_contra hComposite
    have hDiv : 7 ∣ m468Successor := by norm_num [m468Successor, m468]
    have hp7 : Nat.Prime 7 := by decide
    have hNe : 7 ≠ m468Successor := by norm_num [m468Successor, m468]
    have hZero := hZeroOnly 7 hp7 hDiv hNe
    rw [m468_selector_at_seven] at hZero
    norm_num at hZero
  · intro hPrime p hp hDiv hNe
    rcases (Nat.dvd_prime hPrime).mp hDiv with hOne | hSelf
    · exact (hp.ne_one hOne).elim
    · exact (hNe hSelf).elim

theorem m468_successor_factorization :
    m468Successor = 7 * 67 := by
  norm_num [m468Successor, m468]

theorem m468_successor_split_prime_witness :
    Nat.Prime 7 ∧ 7 ∣ m468Successor ∧ 7 ≠ m468Successor := by
  exact ⟨by decide, by norm_num [m468Successor, m468],
    by norm_num [m468Successor, m468]⟩

theorem m468_successor_not_prime : ¬Nat.Prime m468Successor := by
  intro hPrime
  have hDiv : 7 ∣ m468Successor := by norm_num [m468Successor, m468]
  rcases (Nat.dvd_prime hPrime).mp hDiv with hOne | hSelf
  · norm_num at hOne
  · norm_num [m468Successor, m468] at hSelf

theorem m468_zero_only_anti_vacuity_witness :
    Nat.Prime 7 ∧ 7 ∣ m468Successor ∧
      7 ≠ 1 ∧ 7 ≠ m468Successor ∧ m468SelectorValue 7 = 1 := by
  have hPrime : Nat.Prime 7 := by decide
  have hDiv : 7 ∣ m468Successor := by norm_num [m468Successor, m468]
  exact ⟨hPrime, hDiv, by decide, by norm_num [m468Successor, m468],
    m468_selector_at_seven⟩

theorem m468_zero_only_fails : ¬m468ZeroOnlyProperty := by
  rw [m468_zero_only_iff_successor_prime]
  exact m468_successor_not_prime

theorem m468_zolotarev_selector_bridge
    (beta gamma0 d : ℤ)
    (hIdentity : 4 * beta * gamma0 ≡ -1 [ZMOD d]) :
    J(2 * gamma0 | d.natAbs) =
      J(2 | d.natAbs) * J(-1 | d.natAbs) * J(beta | d.natAbs) := by
  exact D5.S1.Phase.Interference.ZolotarevSelector.zolotarev_selector_congruence
    beta gamma0 d hIdentity

end D5.S1.Phase.Interference.M468MemberTable
