# Actual Real Interval Sums

## Abstract

Actual supported interval sums used in natural classification and endpoint recovery.

**Definition 1.1 (Positive finite or essential intervals).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.IntervalFamily`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.IntervalFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

An occurrence has a real birth and a death in WithTop(Real), strictly greater than birth. Infinity is allowed. Repeated intervals retain separate occurrences.

**Definition 1.2 (The actual supported coordinate subspace).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalSpace`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

At time r this is the subspace of K-valued occurrence coordinates that vanish unless birth <= r < death. The field is arbitrary.

**Definition 1.3 (The actual structure map).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalArrow`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalArrow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

For s <= t, retain source coordinates whose deaths are strictly above t and kill the others. The output lies in the supported subspace at t.

**Definition 1.4 (A real persistence functor).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalSum`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

The supported spaces and actual arrows form a functor from the real preorder to ModuleCat. Identity and composition hold at exact birth/death points, zero spaces and infinite tails. The substantive classification and arbitrary competing-decomposition uniqueness proof is in RealDecomposition.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.IntervalFamily`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalArrow`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalSpace`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.intervalSum`
