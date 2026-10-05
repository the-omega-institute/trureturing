/- GID: D5/S3/Combinatorics/AdditiveCodes/AdditiveExtensionDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AdditiveCodes/AdditiveExtensionDefs
   mirror-E: none(waiver:alderson-problems-nine-two-nine-three-statement-definition)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.GaloisField, mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Alderson's Problems 9.2 and 9.3 on extendable but additively maximal additive codes. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.InformationTheory.Hamming

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.AdditiveCodes.AdditiveExtensionDefs

/-! Fixed public statements: T. L. Alderson, *On the Maximality of Additive Codes*,
    arXiv:2607.22297v1, Section 9. "Problem 9.2. Extend Theorem 6.6 to non-square, non-prime
    q." (first sentence; Theorem 6.6 gives, for square q, an extendable additive
    (n, 2, d)_{q²/q}-code with no additive extension) and "Problem 9.3. For which triples
    (q, m, k) with m ≥ 3 do extendable, additively maximal additive (n, k, d)_{q^m/q}-codes
    exist? Does the construction of Section 7 generalize to all q (with m = 3, k = 2), or to
    m ≥ 4?" (the row q = 2).
    Section 1: for n ≥ k an (n, k, d)-code over an alphabet of size Q is a set of Q^k words of
    length n with minimum distance d; an (n + 1, k, d + 1)-code is an extension of the code
    obtained by deleting a fixed coordinate; an additive (n, k, d)_{q^m/q}-code is an
    (n, k, d)-code in GF(q^m)^n that is a GF(q)-subspace; an additive extension is an extension
    that is itself additive, and a code with no additive extension is additively maximal.
    Every notion uses only equality of symbols and the GF(q)-linear structure of GF(q^m),
    so the alphabet is recorded as the GF(q)-space `Fin m → F`; a coordinate permutation
    moves the deleted coordinate to the last one. -/

variable {A : Type*} [DecidableEq A]

/-- `C` has minimum Hamming distance exactly `d`. -/
def MinDistance {n : ℕ} (C : Finset (Fin n → A)) (d : ℕ) : Prop :=
  (∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) ∧
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d

/-- An `(n, k, d)`-code over the alphabet `A`: `|A|^k` words of length `n ≥ k`, minimum
distance `d`. -/
def IsCode {n : ℕ} (C : Finset (Fin n → A)) (k d : ℕ) : Prop :=
  k ≤ n ∧ C.card = Nat.card A ^ k ∧ MinDistance C d

/-- `D` is an extension of the `(n, k, d)`-code `C`: an `(n + 1, k, d + 1)`-code whose words
punctured at the last coordinate are exactly the words of `C`. -/
def IsExtension {n : ℕ} (C : Finset (Fin n → A)) (D : Finset (Fin (n + 1) → A))
    (k d : ℕ) : Prop :=
  IsCode C k d ∧ IsCode D k (d + 1) ∧ D.image Fin.init = C

/-- A code over the alphabet `Fin m → F` is additive: its words form an `F`-subspace. -/
def IsAdditive {F : Type*} [Field F] {m n : ℕ} (C : Finset (Fin n → Fin m → F)) : Prop :=
  ∃ S : Submodule F (Fin n → Fin m → F), (S : Set (Fin n → Fin m → F)) = C

/-- An extendable, additively maximal additive `(n, k, d)_{q^m/q}`-code over `F = GF(q)`. -/
def ExtendableAdditivelyMaximal {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}
    (C : Finset (Fin n → Fin m → F)) (k d : ℕ) : Prop :=
  IsCode C k d ∧ IsAdditive C ∧ (∃ D, IsExtension C D k d) ∧
    ¬ ∃ D, IsExtension C D k d ∧ IsAdditive D

open Classical in
/-- Problem 9.2, first sentence: every non-square, non-prime `q = p^e` (`e ≥ 3` odd) carries
an extendable, additively maximal additive `(n, 2, d)_{q²/q}`-code. -/
def claimNonsquare : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 3 ≤ e → Odd e →
    ∃ n d : ℕ, ∃ C : Finset (Fin n → Fin 2 → GaloisField p e),
      ExtendableAdditivelyMaximal C 2 d

/-- Problem 9.3, the row `q = 2`: for `m ≥ 3` and `k ≥ 1`, an extendable, additively maximal
additive `(n, k, d)_{2^m/2}`-code exists exactly when `k ≥ 2`. -/
def claimBinary : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ k : ℕ, 0 < k →
    ((∃ n d : ℕ, ∃ C : Finset (Fin n → Fin m → ZMod 2),
      ExtendableAdditivelyMaximal C k d) ↔ 2 ≤ k)

end D5.S3.Combinatorics.AdditiveCodes.AdditiveExtensionDefs
