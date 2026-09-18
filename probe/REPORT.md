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
