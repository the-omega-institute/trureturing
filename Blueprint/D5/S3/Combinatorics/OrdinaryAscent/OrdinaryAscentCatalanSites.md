# Ordinary ascent CatalanSites

## Abstract

Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.

**Definition 1.1 (CatalanWord).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.CatalanWord`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.CatalanWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The ordinary-word predicate together with literal avoidance of 10-1 and 20-1. It is distinct from the pair 02-1,12-0.

**Definition 1.2 (sites).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.sites`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.sites` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The values from zero through one plus the ascent count, with each half-open descent interval (next value,previous value] removed. For empty prefixes this auxiliary set does not encode the unique ordinary first letter.

**Theorem 1.3 (mem sites).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.mem_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.mem_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Membership is exactly the ascent upper bound and, at every adjacent pair, either being at most the second value or strictly greater than the first.

**Theorem 1.4 (catalan append iff).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.catalan_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.catalan_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For a nonempty prefix, the extension is an actual Catalan-pair word precisely when the prefix is such a word and the appended value belongs to its computed sites.

**Theorem 1.5 (fresh mem sites).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.fresh_mem_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.fresh_mem_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For an ordinary word, one plus the ascent count is a legal site and strictly exceeds every already used entry.

**Theorem 1.6 (last mem sites).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.last_mem_sites`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.last_mem_sites` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For a nonempty actual Catalan-pair word, its last value remains an admissible site.

**Theorem 1.7 (mem sites append).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.mem_sites_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.mem_sites_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For a nonempty prefix, the next site exclusions consist of the old exclusions and exactly the new adjacent-pair exclusion, together with the updated ascent bound.

## References

- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.CatalanWord`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.catalan_append_iff`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.fresh_mem_sites`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.last_mem_sites`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.mem_sites`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.mem_sites_append`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.sites`
- Dependency: [D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics](OrdinaryAscentSemantics.md)
