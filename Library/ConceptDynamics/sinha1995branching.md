---
bibkey: sinha1995branching
authors: Rakesh Kumar Sinha
year: 1995
title: Some Topics in Parallel Computation and Branching Programs
doi: null
url: https://dada.cs.washington.edu/research/tr/1995/08/UW-CSE-95-08-02.pdf
claim: Theorem 3.29 supplies chain modular arithmetic programs of size O(log^3 L / (log log L log log log L)) for integer threshold problems on intervals of length L, uniformly in the specified threshold.
strata_touched:
  - D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts
license: citation-only
triage: anchor
---

# Modular chains for integer thresholds

University of Washington doctoral dissertation, Department of Computer
Science and Engineering, technical report UW-CSE-95-08-02 (1995).
The directly inspected primary source is the university-hosted dissertation
PDF. Printed page numbers below differ from PDF page numbers by eleven.

## Verified primary scope

Proposition 3.10, printed pp. 28–29, gives a modular router: for a positive
integer modulus q, a scan of n Boolean variables routes input position s
to output position (s + input weight) modulo q. Its n + 1 levels each
have q nodes. Definitions 3.14–3.15, printed p. 31, define acyclic modular
arithmetic programs, their positive moduli, input/output positions, fixed
connections, designated source, sink separation and size as the sum of
box moduli.

Lemma 3.16 and its proof, printed pp. 31–32, replace each modular box by
the scan router and identify connected output/input nodes. They give the
reported Boolean branching-program size bound (n + 1)S for a supplied
program of modular size S separating the two relevant weight sets.
Definition 3.17, printed p. 32, requires nonterminal outputs of each box
to connect to inputs of the next box in a chain. Corollary 3.18, printed
pp. 32–33, gives the corresponding oblivious Boolean branching program.

Definition 3.25, printed p. 38, defines the integer threshold problem:
separate the t smallest integers of an interval from its other integers.
Corollary 3.27 and Proposition 3.28, printed pp. 39–40, supply the interval
reduction and modulus estimates used in Theorem 3.29. That theorem and its
proof, printed p. 41, supply modular chain size

$$
O\!\left(\frac{\log^3 L}
                   {\log\log L\,\log\log\log L}\right)
$$

for any fixed threshold problem on an interval of length L. The implicit
size constant and finite base-case cutoff are uniform in the interval and
specified threshold; modulus choices use interval length. The proof
combines a size contribution of order
log-squared L divided by log-log L with a reduction of unresolved interval
length to at most 8L divided by log-log L, and a constant-size base case.
This is a supplied classical theorem, not a repository discovery.

On printed p. 42, the discussion accompanying Theorem 3.32 identifies exact
division for two boxes and credits it as the basis of Lupanov's earlier
construction of order n to the power three-halves for majority. The two-box
method and its historical ownership remain classical. No independent
inspection of Lupanov's original article is asserted here.

## Native consumer and limits

Sections 29–33 of
[Native prescribed-code acquisition](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md)
use these suppliers for the already prescribed threshold code with its
original complete entries, fixed reader and entire unbounded actual tree
fiber. A selected branch reply is the Boolean one; alpha, beta and absent
are zero. This is a fixed edge-label correspondence, not a new native
query service.

The native consumer separately proves its full-source profile handling,
counts all box/position/residue configurations, composes each box's final
paid edge with its fixed connection or original-entry latch, and pays every
native query at its absolute literal length. Its nS + 4 + r installed-state
count and its nb + 1 and bW_A + 3 execution upper bounds are deductions in
that consumer. They are not stated as dissertation results about native
source acquisition, lawful entry, authentication, isolation or physical
resource prices. Only b at most S follows here for the box count from the
positive-modulus assumption; no sharper scan-count theorem is imported.

The source supplies upper constructions. It gives no unrestricted native
installed-state optimum or optimum at simultaneous minimum native execution
budgets. The journal article associated with DOI 10.1006/jcss.1997.1530 is
not an inspected theorem premise of this note or of the native consumer.

## Source and license boundary

- [University-hosted dissertation, UW-CSE-95-08-02](https://dada.cs.washington.edu/research/tr/1995/08/UW-CSE-95-08-02.pdf).

This is an original citation-only summary and bibliographic record. No
external PDF, extracted text or other full-text source is copied into the
repository. No Lean/kernel verification is asserted by this note.
