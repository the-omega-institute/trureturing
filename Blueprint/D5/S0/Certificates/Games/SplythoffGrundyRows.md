# Splythoff Nim: all Grundy values in every row and column

## Abstract

Every Splythoff Nim row and column contains each Sprague–Grundy value exactly once.

**Definition 1.1 (Single, double and split moves).**

$$\forall (p: \mathrm{Nat} \times \mathrm{Nat}), \forall (q: \mathrm{Nat} \times \mathrm{Nat}), (\operatorname{splythoffMove}\left(p, q\right)) \Leftrightarrow (((q.1 < p.1) \land (q.2 = p.2)) \lor (((q.1 = p.1) \land (q.2 < p.2)) \lor ((\exists (k: \mathrm{Nat}), (1 \le k) \land ((k \le \operatorname{min}\left(p.1, p.2\right)) \land (q = (p.1 - k, p.2 - k)))) \lor ((1 \le \operatorname{min}\left(p.1, p.2\right)) \land (q.1 + q.2 = \operatorname{max}\left(p.1, p.2\right) - \operatorname{min}\left(p.1, p.2\right))))))$$

*Formalization.* `D5/S0/Certificates/Games/SplythoffGrundyRows.splythoffMove` (`✓ std3`).

*Citation.* Robbert Fokkink; Dan Rust (2024). *Queen reflections: a modification of Wythoff Nim*. DOI: [10.1007/s00182-022-00824-1](https://doi.org/10.1007/s00182-022-00824-1). URL: <https://arxiv.org/abs/1904.08339>.

*Commentary.*

Section 2 (arXiv v2, printed page 4) states: "We modify Wythoff Nim by allowing the additional option of a split. If a player takes an equal number of counters from both piles and only one pile remains, then he can split the remaining pile into two." It also states: "A split is only allowed after taking counters from both piles. It is not allowed to take all counters from a single pile and then split." The first two clauses reduce a single pile, the third removes the same positive number k from both piles, and the fourth distributes the remainder after removing the smaller positive pile. Pile sizes include zero; subtraction is natural-number truncated subtraction.

**Definition 1.2 (The finite set of followers).**

$$\forall (p: \mathrm{Nat} \times \mathrm{Nat}), \operatorname{followers}\left(p\right) = \operatorname{Finset}.\operatorname{filter}(\operatorname{splythoffMove}\left(p\right), \operatorname{Finset}.\operatorname{product}(\operatorname{Finset}.\operatorname{range}(\operatorname{max}\left(p.1, p.2\right) + 1), \operatorname{Finset}.\operatorname{range}(\operatorname{max}\left(p.1, p.2\right) + 1)))$$

*Formalization.* `D5/S0/Certificates/Games/SplythoffGrundyRows.followers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robbert Fokkink; Dan Rust (2024). *Queen reflections: a modification of Wythoff Nim*. DOI: [10.1007/s00182-022-00824-1](https://doi.org/10.1007/s00182-022-00824-1). URL: <https://arxiv.org/abs/1904.08339>.

*Commentary.*

Every follower coordinate is at most the larger starting pile. Filtering this finite rectangle by splythoffMove therefore retains exactly the legal followers, including all allowed splits.

**Definition 1.3 (Recursive Sprague–Grundy values).**

$$\forall (x: \mathrm{Nat}), \forall (y: \mathrm{Nat}), \operatorname{grundy}\left(x, y\right) = \operatorname{mex}\left(\operatorname{List}.\operatorname{toFinset}(\operatorname{List}.\operatorname{map}((\operatorname{fun} (q: \{z: \mathrm{Nat} \times \mathrm{Nat} \mid z \in \operatorname{followers}\left((x, y)\right)\}) \mapsto \operatorname{grundy}\left(\operatorname{val}\left(q\right).1, \operatorname{val}\left(q\right).2\right)), \operatorname{Finset}.\operatorname{toList}(\operatorname{Finset}.\operatorname{attach}(\operatorname{followers}\left((x, y)\right)))))\right)$$

*Formalization.* `D5/S0/Certificates/Games/SplythoffGrundyRows.grundy` (`✓ std3`).

*Citation.* Robbert Fokkink; Dan Rust (2024). *Queen reflections: a modification of Wythoff Nim*. DOI: [10.1007/s00182-022-00824-1](https://doi.org/10.1007/s00182-022-00824-1). URL: <https://arxiv.org/abs/1904.08339>.

*Commentary.*

The mex operation is the least natural number absent from a finite set. The definition maps every attached follower to its recursively computed value and takes mex after converting the list to a finite set. Every legal move decreases the sum of the two pile sizes, which makes this recursion well founded. The subtype variable q carries its membership proof; val(q) is its ordered pair.

**Definition 1.4 (The row and column statement).**

$$(claim) \Leftrightarrow ((\forall (x: \mathrm{Nat}), \forall (g: \mathrm{Nat}), \exists! (y: \mathrm{Nat}), \operatorname{grundy}\left(x, y\right) = g) \land (\forall (y: \mathrm{Nat}), \forall (g: \mathrm{Nat}), \exists! (x: \mathrm{Nat}), \operatorname{grundy}\left(x, y\right) = g))$$

*Formalization.* `D5/S0/Certificates/Games/SplythoffGrundyRows.claim` (`✓ std3`).

*Citation.* Robbert Fokkink; Dan Rust (2024). *Queen reflections: a modification of Wythoff Nim*. DOI: [10.1007/s00182-022-00824-1](https://doi.org/10.1007/s00182-022-00824-1). URL: <https://arxiv.org/abs/1904.08339>.

*Commentary.*

Section 9 (arXiv v2, printed page 16) states: "For Splythoff Nim, it appears that every row or column contains each Sprague-Grundy value once and no more. We do not have a proof for that." A row fixes x and a column fixes y. In both clauses g ranges over every natural number, including zero; the exclamation mark denotes existence of exactly one coordinate.

**Theorem 1.5 (A finite bound for each row occurrence).**

$$\forall (x: \mathrm{Nat}), \forall (g: \mathrm{Nat}), \exists (y: \mathrm{Nat}), (\operatorname{grundy}\left(x, y\right) = g) \land (y \le 5 \cdot x + 2 \cdot g + 3)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/SplythoffGrundyRows.row_exists_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robbert Fokkink; Dan Rust (2024). *Queen reflections: a modification of Wythoff Nim*. DOI: [10.1007/s00182-022-00824-1](https://doi.org/10.1007/s00182-022-00824-1). URL: <https://arxiv.org/abs/1904.08339>.

*Commentary.*

For fixed x and g, a column carrying g occurs by 5x+2g+3. Equal-valued unordered pairs share no coordinate unless they are the same pair. There is at most one equal-coordinate pair of value g. Consequently the distinct sums of value-g split targets up to M number at most floor((M+2)/2). Ordinary vertical and double obstructions number at most 2x, and values below g occupy at most g columns. A window of length M=2g+4x+3 cannot be covered by these three bounds.

**Theorem 1.6 (Every value occurs exactly once).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/SplythoffGrundyRows.result` (`✓ std3`). ∎

*Resolves.* `Problems/fokkink-rust-2024-splythoff-grundy-rows` (proved) by `D5/S0/Certificates/Games/SplythoffGrundyRows.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fokkink-rust-2024-splythoff-grundy-rows","declaration_gid":"D5/S0/Certificates/Games/SplythoffGrundyRows.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robbert Fokkink; Dan Rust (2024). *Queen reflections: a modification of Wythoff Nim*. DOI: [10.1007/s00182-022-00824-1](https://doi.org/10.1007/s00182-022-00824-1). URL: <https://arxiv.org/abs/1904.08339>.

*Commentary.*

The finite row bound supplies existence. Single moves between distinct positions of one row force different Grundy values, supplying uniqueness. Swapping the two pile sizes preserves all legal moves and their Grundy values, so the same conclusion holds for columns. The separate question about reflected diagonals remains open.

## References

- Truth anchor: `D5/S0/Certificates/Games/SplythoffGrundyRows.claim`
- Truth anchor: `D5/S0/Certificates/Games/SplythoffGrundyRows.followers`
- Truth anchor: `D5/S0/Certificates/Games/SplythoffGrundyRows.grundy`
- Truth anchor: `D5/S0/Certificates/Games/SplythoffGrundyRows.result`
- Truth anchor: `D5/S0/Certificates/Games/SplythoffGrundyRows.row_exists_bound`
- Truth anchor: `D5/S0/Certificates/Games/SplythoffGrundyRows.splythoffMove`
- Dependency: [D5/S0/Certificates/Games/CrimGrundyRefutation](CrimGrundyRefutation.md)
