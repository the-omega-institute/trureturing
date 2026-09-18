# Bradshaw Conjecture 20 probe

## Preregistered falsifiable predictions

Recorded before source retrieval, searches, computation, or Lean execution.

1. An independently written Python arithmetic derivative D and generalized Collatz map C will reproduce the paper's printed initial solution lists: (a,b)=(5,3): 12419, 20171, 37727, 134579; (7,1): 429 only in the paper's stated search range; (7,5): 29831, 38051, 76331.
2. At (a,b,n)=(17,7,125), D(C(n))=C(D(n)), and 125 is not squarefree.
3. The preregistered claim agrees clause by clause with the source, with the explicitly requested restriction 1 <= n.
4. The expected proof shape is bind-only, with admission_basis open-problem-resolution. A successful Lean refutation must construct an admissible arithmetic derivative and derive its witness values from the four defining properties.

Success requires independent source fidelity, the Python anchors and witness, and a Lean proof with no sorry, no native_decide, no new axioms, and only the standard axiom closure. Source mismatch ends this attempt with revise; unfinished verification is abstain.

## Status

Predictions recorded. Checks have not run.

## Source fidelity

Independently retrieved the JIS PDF from the supplied URL (215463 bytes); third-party material remains in runner scratch. Printed page 3, Section 2, defines D : N -> N by D(0)=0, D(1)=0, prime values 1, and the product rule for every m,n. Printed page 16 gives the odd/even branches of C and the sole parameter condition a congruent to b modulo 2. Conjecture 20 asserts squarefreeness of every commuting input.

Issue #8643 matches each of these clauses. The extra hypothesis 1 <= n is explicit in the preregistration: it weakens the source claim, so its refutation implies a refutation of the source. The witness uses positive odd a=17, b=7 with b<a, so does not exploit an unstated zero-parameter convention. Quantification over admissible D implements the source characterization; the Lean proof must exhibit one to exclude vacuity. Minor locator correction: the four defining properties are on printed page 3 (not page 2).

## Independent Python result

`python3 probe/check_bradshaw.py` exited 0. The independently implemented prime-power contribution sieve reproduced all five complete printed lists over 1 <= n <= 10^7, including the sole (7,1) solution 429. A separate trial-factor formula agreed on D(0..9999). Full lists, sieve bounds, and elapsed time are retained in `python-results.json`.

At (17,7,125): D(125)=75, C(125)=1066, D(1066)=641=C(75), D(75)=55, and 125 has factorization 5^3. Both preregistered numerical predictions passed. These are computational checks, not a replacement for the Lean existence and refutation proofs.

PDF SHA-256: `5d2579130e5a88b1f3aec05d6d00d0e9876c85db42846fb05c76572a2aaed6bd`.
