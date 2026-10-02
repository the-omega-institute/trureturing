# Consecutive Arrows and Right-Continuous Real Cells

## Abstract

Arbitrary consecutive arrows and increasing real breakpoints define actual persistence modules.

**Definition 1.1 (Raw consecutive arrows).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.FiniteChain`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.FiniteChain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

The input is an arbitrary finite sequence of bundled K-vector spaces and adjacent linear maps, including length zero. No composite laws or classifier are assumed.

**Definition 1.2 (Keep the last actual object).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.paddedObject`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.paddedObject` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

For a nonempty sequence, natural indices beyond the input retain the actual last object. For an empty sequence all objects are zero.

**Definition 1.3 (Identity padding, not a terminal zero).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.paddedArrow`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.paddedArrow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Use the given adjacent arrow while a next vertex exists. Afterwards use the identity on the retained object, transported only through object equalities.

**Definition 1.4 (Actual composites from the pinned supplier).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.chainFunctor`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.chainFunctor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Functor.ofSequence supplies composites and their laws. Restrict to Fin(n) and use copyObj to recover the original objects exactly; no composition theorem is reproved.

**Definition 1.5 (The finite diagram used by the split construction).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.chainDiagram`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.chainDiagram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

The actual composite linear maps and the supplied functor laws form Diagram K V.

**Definition 1.6 (A single zero prefix object).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.zeroPrefixObject`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.zeroPrefixObject` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Bottom is a zero vector space; an ordinary finite index carries its original space.

**Definition 1.7 (Extend the actual diagram by zero on the left).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.zeroPrefix`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.zeroPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

From bottom use the zero map. Between actual vertices use their actual composites. There is no object after the last finite index.

**Definition 1.8 (Strictly increasing real input points).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.Breakpoints`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.Breakpoints` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

The finite grid stores real times and strict monotonicity. An empty grid is allowed.

**Definition 1.9 (The last breakpoint at or before a real time).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.cell`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.cell` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

The finite supremum in WithBot(Fin(n)) selects the last eligible index. It is bottom before the first breakpoint and everywhere for an empty grid.

**Definition 1.10 (Monotone real cells).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.cellFunctor`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.cellFunctor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Increasing real time can only add eligible indices, giving a monotone selector functor.

**Definition 1.11 (The actual right-continuous extension).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.realModule`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.realModule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Compose the cell selector with the zero-prefix diagram. Cells include their left breakpoint. The last actual object continues for all later real times.

**Definition 1.12 (Positive intervals from the constructed finite basis).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.realFamily`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/RealExtension.realFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

Birth is the basis birth breakpoint. Death is the next breakpoint after the last supported vertex when one exists, and infinity otherwise. Ordered basis supports and strict breakpoint monotonicity prove positivity. These are necessary objects; no new theorem content is credited to coordinate or sequence adapters.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.Breakpoints`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.FiniteChain`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.cell`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.cellFunctor`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.chainDiagram`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.chainFunctor`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.paddedArrow`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.paddedObject`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.realFamily`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.realModule`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.zeroPrefix`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/RealExtension.zeroPrefixObject`
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition](FiniteIntervalDecomposition.md)
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit](FiniteIntervalSplit.md)
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness](RealIntervalUniqueness.md)
