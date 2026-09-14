/- GID: D5/S0/Certificates/KarttunenGcdTotientPositionRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/KarttunenGcdTotientPositionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Totient, mathlib/module/Mathlib.Tactic.Simproc.Factors]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.claim; result=D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.result; claim=D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.claim
   digest: The value 60 refutes Karttunen's A089966 characterization of A129598 differences. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Simproc.Factors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S0.Certificates.KarttunenGcdTotientPositionRefutation

/-!
OEIS A129598 is defined by `a(n) = n * A111089(n)`, where A111089 is the
greatest prime factor. Antti Karttunen's comment of 2007-05-01 conjectures
that A129598 differs from A050399 exactly at the positions in A089966.

The value `60` refutes only that proposed position characterization. Here
`a(60) = 300`, but `gcd(300, phi(300)) = 20`, while the least preimage
`b(60)` must itself have gcd-totient value `60`. Thus `a(60) != b(60)`.
On the other hand, `60` is not in A089966: it has three distinct prime
factors, while its greatest prime factor modulo its least is `5 % 2 = 1`.
-/

/-- The gcd-totient map used to define OEIS A050399. -/
def g (m : ℕ) : ℕ :=
  Nat.gcd m (Nat.totient m)

/-- The greatest prime factor, with value `0` when there is no prime factor. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.getLastD 0

/-- OEIS A129598, including its exceptional initial value. -/
def a (n : ℕ) : ℕ :=
  if n = 1 then 2 else n * greatestPrimeFactor n

/-- OEIS A050399: the least positive preimage under `g`, or `0` if none exists. -/
noncomputable def b (n : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ m : ℕ, 0 < m ∧ g m = n then Nat.find h else 0

/-- The literal membership predicate for OEIS A089966. -/
def inA089966 (n : ℕ) : Prop :=
  n = 1 ∨
    (0 < n ∧ n.primeFactors.card = greatestPrimeFactor n % n.minFac)

/-- Karttunen's proposed exact characterization of the differing positions. -/
def claim : Prop :=
  ∀ n : ℕ, 1 < n → ((a n ≠ b n) ↔ inA089966 n)

/-- The value `60` differs from A050399 but is not a member of A089966. -/
theorem result : ¬ claim := by
  intro hclaim
  have hpf : Nat.primeFactorsList 60 = [2, 2, 3, 5] := by simp
  have ha : a 60 = 300 := by
    change (if 60 = 1 then 2 else 60 * (Nat.primeFactorsList 60).getLastD 0) = 300
    rw [hpf]
    decide
  have hga : g (a 60) = 20 := by
    rw [ha]
    decide
  have hex : ∃ m : ℕ, 0 < m ∧ g m = 60 := by
    exact ⟨900, by decide, by decide⟩
  have hb : 0 < b 60 ∧ g (b 60) = 60 := by
    rw [b, dif_pos hex]
    exact Nat.find_spec hex
  have hne : a 60 ≠ b 60 := by
    intro hab
    have heqg : g (a 60) = g (b 60) := congrArg g hab
    have hfalse : (20 : ℕ) = 60 := hga.symm.trans (heqg.trans hb.2)
    exact (show (20 : ℕ) ≠ 60 by decide) hfalse
  have hnotmem : ¬ inA089966 60 := by
    change ¬ (60 = 1 ∨ (0 < 60 ∧ (Nat.primeFactorsList 60).toFinset.card =
      (Nat.primeFactorsList 60).getLastD 0 % Nat.minFac 60))
    rw [hpf]
    decide
  exact hnotmem ((hclaim 60 (by decide)).mp hne)

#print axioms g
#print axioms greatestPrimeFactor
#print axioms a
#print axioms b
#print axioms inA089966
#print axioms claim
#print axioms result

end D5.S0.Certificates.KarttunenGcdTotientPositionRefutation
