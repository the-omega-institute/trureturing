# Concrete completion decompositions

## Abstract

Literal P13 continuations retain the complete ranked vertex word at every height.

**Definition 1.1 (Closing vertices).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.closingCount`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.closingCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The closing count records every future closure, irrespective of its rank.

**Definition 1.2 (Opening vertices).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingCount`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The opening count records every future opening.

**Theorem 1.3 (Partition of the vertices).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.vertex_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.vertex_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A word has length equal to its opening count plus its closing count.

**Theorem 1.4 (Endpoint balance).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.continuation_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.continuation_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Every accepted suffix closes exactly the old survivors, pending openings and future openings.

**Theorem 1.5 (Bounds on literal ranks).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.continuation_rank_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.continuation_rank_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Every closing rank in an accepted suffix is less than its total number of future closures.

**Definition 1.6 (Literal completions).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.Completion`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.Completion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A completion is a finite word accepted from the given base with zero pending openings and with exactly d closing vertices. Acceptance requires no unfinished endpoint at the end.

**Theorem 1.7 (Derived finite support).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A completion from s has s.size at most d, exactly d minus s.size openings, length twice d minus s.size, and every closing rank below d. These bounds follow from acceptance.

**Theorem 1.8 (Finiteness of the literal carrier).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Each completion embeds into a fixed length tuple of opening letters and closing ranks below d. Thus its carrier is finite.

**Definition 1.9 (Single block counts).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.c`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.c` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The number c(m,d) counts literal completions from S(m).

**Definition 1.10 (Normalized block counts).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.g`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.g` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The number g(a,b,d) counts literal completions from blocks(a,b). Empty blocks are deleted, so g(a,0,d) equals c(a,d) and g(0,b,d) equals c(b,d).

**Theorem 1.11 (Impossible endpoint balances).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_count_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_count_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A base with more old survivors than future closures has no completion.

**Theorem 1.12 (Single block support).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.c_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.c_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The count c(m,d) vanishes for m greater than d.

**Definition 1.13 (A run of openings).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingRun`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The word consists of k successive opening vertices.

**Theorem 1.14 (Additive closing count).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.closingCount_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.closingCount_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Concatenation adds the closing counts of the two literal words.

**Theorem 1.15 (Opening runs contain no closures).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingRun_closingCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingRun_closingCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A run of opening vertices contributes zero to the closing count.

**Theorem 1.16 (Pending opening transitions).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.accept_openingRun`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.accept_openingRun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Reading a run of n openings increases the separate pending count by exactly n.

**Theorem 1.17 (Parsing the first closure).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.first_closure_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.first_closure_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Any word with a positive closing count begins with a run of openings followed by its first closing letter and a remaining suffix.

**Theorem 1.18 (Unique first closure parsing).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.first_closure_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.first_closure_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The initial opening count, first closing rank and suffix are uniquely determined by the literal word.

**Definition 1.19 (Descending forced prefix).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For opening multiplicities t1 through ta, the prefix is U to the power t1 followed by rank a minus one, through U to the power ta followed by rank zero.

**Theorem 1.20 (Legal forced transitions).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix_accept`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix_accept` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For b positive, reading this prefix from blocks(a,b) with a equal to the multiplicity list length is equivalent to acceptance of the remaining word from S(b plus the sum of the multiplicities).

**Theorem 1.21 (Exhaustive forced closure parsing).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix_exhaustive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix_exhaustive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Every accepted word from blocks(a,b), with b positive, consists of such a prefix with exactly a forced closures, followed by an accepted single block suffix.

**Definition 1.22 (Weak compositions of openings).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.OpeningMultiplicities`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.OpeningMultiplicities` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A weak composition is a natural valued function on Fin(a) whose sum is t.

**Definition 1.23 (Finite prefix and suffix data).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.ForcedData`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.ForcedData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The data consists of t at most d, a weak composition into a opening counts, and a concrete completion from S(b+t) with d-a closures.

**Definition 1.24 (Bijection on literal two block completions).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedCompletionEquiv`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedCompletionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For b positive, the finite prefix data and literal completions from blocks(a,b) are equivalent. The inverse exhausts the forced first block. If d is less than a the data is empty, because its suffix would have a positive base and zero closures.

**Theorem 1.25 (Finite forced closure count).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Completions.g_forced_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Completions.g_forced_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For b positive, g(a,b,d) is the sum over t from zero to d of choose(a+t-1,t) times c(b+t,d-a). The weak compositions use the symmetric power carrier, and impossible terms vanish by endpoint balance.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.Completion`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.ForcedData`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.OpeningMultiplicities`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.accept_openingRun`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.c`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.c_support`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.closingCount`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.closingCount_append`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_bounds`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_count_zero`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.completion_finite`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.continuation_balance`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.continuation_rank_bound`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.first_closure_exists`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.first_closure_unique`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedCompletionEquiv`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix_accept`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.forcedPrefix_exhaustive`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.g`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.g_forced_sum`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingCount`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingRun`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.openingRun_closingCount`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Completions.vertex_count`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Correspondence](P13Correspondence.md)
