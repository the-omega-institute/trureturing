# Northeast ears and terminal patterns

## Abstract

Northeast ears and terminal patterns.

**Definition 1.1 (The classical forbidden pattern).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Local.pattern`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Local.pattern` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

The permutation of six zero-based values is [2, 4, 0, 5, 1, 3], corresponding to the classical one-based pattern 351624.

**Definition 1.2 (Terminal 3412).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Local.Terminal`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Local.Terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For a permutation pi of Fin n and a finite set S of positions, a terminal pattern consists of a < b < c < d in S with pi(c) < pi(d) < pi(a) < pi(b). Every position of S is at most d and every value in S is at most pi(b).

**Definition 1.3 (Fresh terminal patterns).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Local.Fresh`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Local.Fresh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

A fresh terminal 3412 has the additional properties that every old position is at most b or equals c or d, and every old value is at most pi(d) or occurs at a or b. Thus b,c,d are the last three positions and pi(d),pi(a),pi(b) are the largest three values.

**Definition 1.4 (Northeast double ears).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Local.Double`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Local.Double` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

Two new positions u,v and distinct old attachments x,y satisfy u < x < v and pi(v) < pi(y) < pi(u). Every old point except x lies left of u; every old value except pi(y) lies below pi(v). Neither new position belongs to S.

**Definition 1.5 (The fresh state after a double ear).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Local.fresh`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Local.fresh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

After a northeast double ear, the points y,u,x,v form a fresh terminal 3412 in S union {u,v}.

**Theorem 1.6 (The forbidden six-point configuration).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Local.forces`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Local.forces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

If a terminal 3412 occurs in S and a northeast double ear can be added, the whole permutation contains 351624. The six selected positions are a,b,c,u,d,v. Their values increase in the order c,d,a,v,b,u. The terminal maximum and rightmost point are exactly the two old attachment points.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Local.Double`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Local.Fresh`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Local.Terminal`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Local.forces`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Local.fresh`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Local.pattern`
- Dependency: [D5/S1/Words/Patterns/DerangementRatioNonconvergence](../../../S1/Words/Patterns/DerangementRatioNonconvergence.md)
