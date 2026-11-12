# Ordinary ascent CatalanRank

## Abstract

Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.

**Theorem 1.1 (sites shape).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.sites_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.sites_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For a nonempty actual avoiding word, every admissible site is at most the last value or equals the fresh upper bound. Combined with last_mem_sites and fresh_mem_sites, these are the two largest sites.

**Theorem 1.2 (sites append).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.sites_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.sites_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

On an actual nonempty avoiding prefix and a legal appended value x, the complete new site set consists of the old sites at most x and the new fresh upper bound.

**Definition 1.3 (rank).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The zero-based rank of a value is the number of admissible sites strictly below it.

**Theorem 1.4 (card sites append).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_sites_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_sites_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Appending a legal value of rank i to an actual nonempty avoiding prefix gives exactly i+2 legal sites. Descent, repetition and fresh ascent are all included.

**Theorem 1.5 (rank lt card).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank_lt_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank_lt_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The rank of an actual site lies in the finite rank interval.

**Theorem 1.6 (rank strictMono).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank_strictMono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

If x is an actual site and x<y, then the number of sites below x is strictly smaller than the number below y.

**Definition 1.7 (rankedSites).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rankedSites`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rankedSites` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Ranking is a genuine equivalence from actual admissible sites to the finite interval of their ranks. Its inverse un-ranks actual letters.

**Definition 1.8 (unrank).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Inverse ranking on the actual finite rank interval, with a default zero only outside that interval.

**Theorem 1.9 (unrank spec).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

At every valid rank, unranking returns an actual admissible value with exactly that rank.

**Theorem 1.10 (unrank rank).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Unranking the rank of an actual admissible letter returns the same letter.

**Theorem 1.11 (card sites le).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_sites_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_sites_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For a nonempty word, the number of auxiliary sites is at most length plus one.

**Theorem 1.12 (singleton word).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.singleton_word`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.singleton_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

A singleton word satisfies the actual ordinary Catalan-pair predicate exactly when its value is zero.

**Theorem 1.13 (root sites).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.root_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.root_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The unique nonempty root zero has the two sites zero and one. This initial condition is consumed by the code invariant.

**Definition 1.14 (eastCode).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Read actual letters from left to right. At a letter following a prefix of length m, record m minus that letter's rank in the prefix site set. The initial zero records zero.

**Theorem 1.15 (eastCode append).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Appending a letter appends exactly the length-minus-rank code entry.

**Theorem 1.16 (eastCode length).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_length`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The rank-complement code has exactly the same length as the original word.

**Theorem 1.17 (eastCode valid).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For an actual avoiding word, the code is a nondecreasing inversion sequence. For a nonempty word, its site count plus the last code entry is length plus one. The invariant is proved at every producer.

**Definition 1.18 (fromEastCode).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Starting from zero, reconstruct each next letter by unranking prefix length minus the new east count in the actual current site set.

**Theorem 1.19 (fromEastCode append).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The inverse construction retains the unique initial zero and appends the unranked value at each later code entry.

**Theorem 1.20 (fromEastCode eastCode).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_eastCode`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_eastCode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Encoding an actual ordinary avoiding word and then reconstructing gives the original word, including the empty word.

**Theorem 1.21 (fromEastCode valid).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For every nondecreasing inversion sequence, reconstruction is an actual ordinary Catalan-pair word of the same length, and encoding recovers the original inversion sequence.

**Theorem 1.22 (mem catalan avoiders).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.mem_catalan_avoiders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.mem_catalan_avoiders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The literal two-pattern finite length class is precisely length equality and the CatalanWord predicate.

**Definition 1.23 (catalanMonoEquiv).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.catalanMonoEquiv`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.catalanMonoEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Actual ordinary 10-1,20-1 avoiders of length n are equivalent to nondecreasing inversion sequences of length n. Both inverses and all carrier predicates are proved; this intermediate class is not assumed to equal the avoiding words.

**Definition 1.24 (dyckEquiv).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Compose the actual-word rank equivalence with the existing monoDyckEquiv on its exact nondecreasing inversion-sequence domain. The result is an equivalence with actual Mathlib Dyck words of semilength n, including n=0.

**Theorem 1.25 (dyckEquiv forward).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv_forward`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The forward Dyck list is exactly the existing dyckSteps encoding of the proved rank-complement code.

**Theorem 1.26 (dyckEquiv inverse).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The inverse reads counts of preceding downsteps using the existing eastCounts and reconstructs the actual ordinary word by inverse ranks.

**Theorem 1.27 (card catalan avoiders).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_catalan_avoiders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_catalan_avoiders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For every n including zero, the actual ordinary words avoiding literal 10-1 and 20-1 have cardinality catalan n. This uses the constructed equivalence and the existing Mathlib Catalan cardinality.

## References

- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_catalan_avoiders`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_sites_append`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.card_sites_le`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.catalanMonoEquiv`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv_forward`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.dyckEquiv_inverse`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_append`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_length`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.eastCode_valid`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_append`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_eastCode`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.fromEastCode_valid`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.mem_catalan_avoiders`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank_lt_card`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rank_strictMono`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.rankedSites`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.root_sites`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.singleton_word`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.sites_append`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.sites_shape`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank_rank`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.unrank_spec`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck](../InversionSeq/InversionSeq152Dyck.md)
- Dependency: [D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites](OrdinaryAscentCatalanSites.md)
