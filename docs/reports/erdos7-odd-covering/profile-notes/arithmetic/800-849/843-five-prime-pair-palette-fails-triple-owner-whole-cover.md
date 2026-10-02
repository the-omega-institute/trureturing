# A five-prime pair palette cannot be a triple-owned whole cover

Fix the distinct odd divisor-closed palette

\[
D=\{3,5,7,11,13\}\cup\{pq:p,q\in\{3,5,7,11,13\},\ p<q\}.
\]

Its least common multiple is

\[
Q=3\cdot5\cdot7\cdot11\cdot13=15015>10000,
\]

and its reciprocal mass is

\[
\sum_{d\in D}\frac1d=\frac{1279}{1155}>1.
\]

Thus the finite branch is outside the known `lcm <= 10000` obstruction and is
not rejected by the elementary reciprocal-mass test.

For each modulus \(d\), introduce Boolean variables \(R_{d,a}\) for
\(a\in\mathbb Z/d\mathbb Z\), with exactly one selected residue.  The finite
SAT instance contains:

1. one coverage clause for every \(x\in\mathbb Z/Q\mathbb Z\), requiring at least one selected class to contain \(x\);
2. for every pair \(d,e\in D\) with \(\gcd(d,e)>1\), and every \(x\), the implication
   \[
   R_{d,x\bmod d}\land R_{e,x\bmod e}
   \Longrightarrow
   \bigvee_{f\in D\setminus\{d,e\}}R_{f,x\bmod f}.
   \]
   This is exactly the requirement that every point in a non-coprime pair
   intersection have at least three owners.

No private-point or irredundancy assumption is included.  Therefore an UNSAT
result already rules out the weaker whole-cover-plus-triple-owner condition for
this fixed palette.

The generated formula has 613 residue variables, 598 sequential-counter
variables, and 767,559 clauses.  Two independent PySAT backends both return
`UNSAT`:

| backend | result |
| --- | --- |
| `cadical153` | `UNSAT` |
| `glucose4` | `UNSAT` |

The exact formula construction and deterministic output are in
[`five_prime_pair_triple_owner_unsat.py`](../../../frontier/cover-geometry/five-prime-pair-triple-owner-unsat/five_prime_pair_triple_owner_unsat.py)
and
[`five_prime_pair_triple_owner_unsat.json`](../../../frontier/cover-geometry/five-prime-pair-triple-owner-unsat/five_prime_pair_triple_owner_unsat.json).
The run used `python-sat` 1.9.dev15.  The SAT run has no DRAT proof artifact;
the two-backend result is a finite computational certificate, not a Lean
proof.

This rules out one `Q=15015` divisor-closed branch in which all non-coprime
collisions are at least triple-owned.  It does not prove that every odd
cover has an exact two-owner non-coprime point, and it does not settle
unrestricted Erdős #7.
