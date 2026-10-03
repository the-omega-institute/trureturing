# Actual Real Interval Sums

## Abstract

Actual supported interval sums used in natural classification and endpoint recovery.

**Theorem 1.1 (Actual monomorphisms bound birth/death window counts).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_death_window_count`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_death_window_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

For finite occurrence families and an actual natural map injective at every real time, the number of source intervals born by s and dying in (t,u] is at most the corresponding target number, for s <= t <= u. The upper cut u may be infinity; this version uses the birth image without an artificial arrow to an infinite-time object. Extend window coordinates into the source at s and t. Naturality at s -> t and, for finite u, t -> u puts their actual images in the target birth-image and death-kernel intersection. Restriction to the target window is injective, so the existing finrank comparison gives the count bound. No occurrence injection or quantitative endpoint bound is assumed.

**Theorem 1.2 (Actual epimorphisms bound surviving birth-window counts).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_birth_window_count`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_birth_window_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

For an actual natural map surjective at every real time and r <= s <= t, the target number of intervals born in (r,s] and surviving t is at most the source number. Lift target window coordinates at s. Split the lifted source vector at t into the recent-birth coordinates and the actual image from r. Naturality makes the latter invisible in the target recent-birth quotient. The resulting coordinate map is surjective; the existing surjective finrank comparison gives the count bound. Infinite deaths are included. Ordered occurrence injections, their composition, sandwiches and stability are not conclusions of this theorem.

**Theorem 1.3 (Monomorphism matching by increasing-birth ordinals).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_ordered_occurrence_injection`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_ordered_occurrence_injection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Fix a bijective increasing-birth enumeration of each death class in both finite families, including the essential class. An actual natural map injective at every real time gives an occurrence embedding preserving death and class ordinal, with target birth at most source birth. A finite real sample isolates each death class from the actual window inequality. The first k+1 source occurrences force the target occurrence of ordinal k to exist and be born in time. The enumeration retains tied occurrences separately. With a shared intermediate enumeration, ordinal preservation forces classwise composition; no arbitrary Hall matching is selected.

**Theorem 1.4 (Epimorphism matching by decreasing-death ordinals).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_ordered_occurrence_injection`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_ordered_occurrence_injection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Fix a bijective decreasing-death enumeration of each birth class, with infinity first and a fixed order of tied occurrences. An actual natural map surjective at every real time gives a target-to-source occurrence embedding preserving birth and class ordinal, with target death at most source death. An earlier cutoff isolates the birth class, and a later finite sample isolates all survivors at a finite or infinite death threshold. Their actual window count forces the ordinal-k source occurrence to survive long enough. Shared intermediate ordinals force epimorphism-class composition. Quantitative estimates additionally require actual kernel or cokernel conditions; exact stability is not an assertion of this injection.

**Theorem 1.5 (Cokernel birth trims bound the fixed monomorphism matching).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_cokernel_trim_estimates`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_cokernel_trim_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Fix the increasing-birth enumerations in every death fiber and an ordinal-preserving occurrence injection for an actual natural monomorphism. For every nonnegative eta, assume that the actual target structure-map image from t to t+eta lies in the morphism's range at t+eta. Shift the birth of every target interval by eta and retain precisely the positive-length trims, including all essential intervals. Their coordinate inclusion at t has exactly the range of the target arrow from t-eta to t. Lift it through the actual monomorphism using its range equivalence. Cancellation proves naturality, and zero extension proves injectivity. A long target occurrence of ordinal k supplies k+1 trimmed occurrences, so their images force the same fixed ordinal-k image occurrence to exist and have birth at most target birth plus eta. A matched short occurrence satisfies the bound by positivity and equal death. Every long target occurrence is covered, every essential is covered without subtracting infinity, and eta zero forces full coverage and equal births.

**Theorem 1.6 (Kernel death trims bound the fixed epimorphism matching).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_kernel_trim_estimates`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_kernel_trim_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Fix decreasing-death enumerations in every birth fiber and an ordinal-preserving occurrence injection for an actual natural epimorphism. For every nonnegative eta, assume its actual kernel at t is contained in the kernel of the source arrow to t+eta. Retain intervals longer than eta, move each finite death left by eta and leave infinite deaths infinite. The canonical coordinate quotient is surjective and its kernel equals that actual structure-map kernel. The kernel inclusion permits the quotient lift; the surjective kernel-quotient equivalence factors it through the epimorphism. Its evaluation equation proves surjectivity, and precomposition with the original surjection proves naturality. Long source prefixes force coverage and a trimmed source death at most the paired image death for the already fixed injection. Short matched bars satisfy this by positivity. Finite source deaths are at most image death plus eta. Essential death is equivalent on paired occurrences and all source essentials are covered. Eta zero forces full source coverage and equality of deaths.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_birth_window_count`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_kernel_trim_estimates`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.epi_ordered_occurrence_injection`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_cokernel_trim_estimates`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_death_window_count`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.mono_ordered_occurrence_injection`
