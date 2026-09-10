# Deb--Sokal Conjecture 1.4(c): refutation of the printed clause

## Abstract

The printed non-real-zero clause of Deb--Sokal Conjecture 1.4(c) is false: the eligible row (r,n) = (3,3) has only real zeros.

Bishal Deb and Alan D. Sokal, Higher-order Stirling cycle and subset triangles: Total positivity, continued fractions and real-rootedness, arXiv:2507.18959v1, printed page 10, assert that the subset row polynomials have non-real complex zeros for r >= 3 and n >= 3. The formal claim universally quantifies over exactly that range. It does not exclude (3,3). The other clauses concerning r = 1,2 and log-concavity are not used.

**Theorem 1.1 (The printed universal non-real-zero clause is false).**

Lean statement: `D5/S0/Certificates/DebSokalConjectureFourRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/DebSokalConjectureFourRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficients are defined by Lemma 1.1(b), equation (1.14), and the row polynomial by equation (1.18). Recomputing the third row at r = 3 gives 0, 1, 35, 280, agreeing with Appendix A.2 on printed page 47. Thus s_(3,3)(x) = x(1 + 35x + 280x^2). Its quadratic discriminant is 35^2 - 4*280 = 105 > 0. The kernel checks the recurrence calculation and uses Mathlib's discriminant and complex-square lemmas to exclude every non-real zero. No floating-point arithmetic or table assumption is used.

Provenance of the counterexample fact: literature-attested. Deb's 2023 UCL PhD thesis, Enumerative combinatorics, continued fractions and total positivity, section 6.5, printed page 281, explicitly says that s_(3,3) has real zeroes and s_(3,4) has complex zeroes. The thesis is available at https://discovery.ucl.ac.uk/10179955/1/BishalDeb_PhDThesis_Final.pdf. This is a formal refutation of the printed 2025 statement, not the discovery of a new counterexample. FromRepo describes the local formal derivation: no matching Library note exists for the LibraryNoteRef required by FromLiterature, and this implementation does not add an L-plane note.

Corollary 7.3 on printed page 40 proves non-real zeros for r >= 4 and n >= 3; the immediately following r = 3 computational evidence starts at n >= 4. That suggests an intended restriction at r = 3; this module does not assert that the restricted proposition is false. A literature check on 2026-09-10 found only arXiv v1. The author's research page says Accepted for publication at SIAM Journal on Discrete Mathematics, but a readable final journal text was not obtained. Whether it changes n >= 3 to n >= 4 remains ASSUMED-UNVERIFIED.

## References

- Truth anchor: `D5/S0/Certificates/DebSokalConjectureFourRefutation.result`
