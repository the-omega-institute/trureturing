# Ordinary ascent CatalanStatistics

## Abstract

Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.

**Theorem 1.1 (rank fresh).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.rank_fresh`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.rank_fresh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The fresh upper bound occupies the largest actual rank: its rank plus one is the site count.

**Theorem 1.2 (asc eastCode).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.asc_eastCode`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.asc_eastCode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For every actual avoiding word, the sum of the strict ascent counts of the word and its east-count code is length minus one.

**Theorem 1.3 (peaks dyckSteps).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.peaks_dyckSteps`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.peaks_dyckSteps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For the existing east-count step encoding, if every code entry is strictly below the final size, the number of adjacent UD peaks is zero for an empty code and one plus its strict ascent count otherwise.

**Theorem 1.4 (dyckEquiv peaks).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.dyckEquiv_peaks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.dyckEquiv_peaks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The actual Dyck image has exactly n minus the ordinary word's ascent count many adjacent UD peaks.

**Definition 1.5 (ascentPeakEquiv).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.ascentPeakEquiv`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.ascentPeakEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For r<n, restrict the actual equivalence to words with r ascents and Dyck words with n-r peaks. The inverse recovers the exact ascent statistic.

**Theorem 1.6 (narayana ascents).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.narayana_ascents`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.narayana_ascents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For r<n, n times the actual number of length-n ordinary words avoiding 10-1,20-1 with r ascents equals choose(n,r) choose(n,r+1). The positive-size and positive-peak hypotheses of the licensed supplier are discharged explicitly.

**Theorem 1.7 (Insertion and rightmost-up deletion).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.dyckEquiv_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.dyckEquiv_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For a nonempty actual parent and an actual one-letter child, let i be the appended letter's zero-based admissible rank. The parent path is Q followed by i downsteps, and the child path is Q followed by one upstep and i+1 downsteps. Thus deleting the rightmost upstep and its following downstep recovers the parent.

## References

- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.asc_eastCode`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.ascentPeakEquiv`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.dyckEquiv_insert`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.dyckEquiv_peaks`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.narayana_ascents`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.peaks_dyckSteps`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.rank_fresh`
- Dependency: [D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana](DyckNarayana.md)
- Dependency: [D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank](OrdinaryAscentCatalanRank.md)
