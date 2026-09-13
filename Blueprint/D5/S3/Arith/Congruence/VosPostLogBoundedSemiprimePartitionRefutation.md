# The OEIS A100952 Log-Bounded Semiprime-Partition Conjecture

## Abstract

A residue-class obstruction refutes the log-bounded partition conjecture in A100952.

**Definition 1.1 (A log-bounded prime-plus-semiprime representation).**

$$\forall m \in \mathrm{Nat},\; (\operatorname{Rep}\left(m\right)) \Leftrightarrow ((\exists p \in \mathrm{Nat}, q \in \mathrm{Nat}, r \in \mathrm{Nat},\; (\operatorname{Prime}\left(p\right)) \land ((\operatorname{Prime}\left(q\right)) \land ((\operatorname{Prime}\left(r\right)) \land ((m = p + q \cdot r) \land ((p : \mathrm{Real}) \le \operatorname{log}\left((\operatorname{min}\left(q, r\right) : \mathrm{Real})\right)))))))$$

*Formalization.* `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.Rep` (`✓ std3`).

*Citation.* Jonathan Vos Post; Reinhard Zumkeller (2004). *OEIS A100952, Numbers that cannot be written as p*q+r with three distinct primes p, q and r*. URL: <https://oeis.org/A100952>.

*Commentary.*

The three variables p, q, and r are natural primes. The inequality casts p and min(q,r) to real numbers and uses Real.log, the natural logarithm. Equal semiprime factors q and r are allowed.

**Definition 1.2 (The eventual log-bounded partition conjecture).**

$$(claim) \Leftrightarrow ((\exists B \in \mathrm{Nat},\; (60 \le B) \land (\forall m \in \mathrm{Nat},\; (B < m) \Rightarrow (\operatorname{Rep}\left(m\right)))))$$

*Formalization.* `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.claim` (`✓ std3`).

*Citation.* Jonathan Vos Post; Reinhard Zumkeller (2004). *OEIS A100952, Numbers that cannot be written as p*q+r with three distinct primes p, q and r*. URL: <https://oeis.org/A100952>.

*Commentary.*

This is the source's allowance for a threshold larger than sixty: some natural B at least sixty works for every natural m above B.

**Theorem 1.3 (The eventual conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a100952-log-bounded-semiprime-partition-refutation` (refuted) by `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a100952-log-bounded-semiprime-partition-refutation","declaration_gid":"D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jonathan Vos Post; Reinhard Zumkeller (2004). *OEIS A100952, Numbers that cannot be written as p*q+r with three distinct primes p, q and r*. URL: <https://oeis.org/A100952>.

*Commentary.*

Every number 6t+5 fails. The logarithmic estimate first forces q and r above three; parity then forces p=2; divisibility by three finally forces q=3 or r=3, a contradiction. The completeness conjecture for A100952 is untouched.

## References

- Truth anchor: `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.Rep`
- Truth anchor: `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.claim`
- Truth anchor: `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.result`
