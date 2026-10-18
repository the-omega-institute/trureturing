# Class-C Admissible Sites

## Abstract

Admissible values of class-C inversion prefixes have an exact sorted-site succession.

Inversion-sequence entries are nonnegative and satisfy the zero-based bound at their positions. Pattern ranks alone are shifted to the positive letters used by ranked occurrences. The four patterns here are 211, 212, 221 and 321; they differ from the class-A quadruple at its fourth pattern. The derivation uses the native ranked occurrence relation. The cited Callan–Mansour source supplies the inversion-sequence and pattern context; the admissible-site arguments below are derived here.

**Definition 1.1 (Class-C patterns).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.patterns`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.patterns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The pattern list consists exactly of 211, 212, 221 and 321.

**Definition 1.2 (Append safety).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.Safe`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.Safe` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For any word w and natural value x, safety means that w followed by x avoids every class-C pattern. This predicate does not impose the inversion-sequence bound.

**Definition 1.3 (Exclusion by an ordered pair).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.ForbiddenTriple`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.ForbiddenTriple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

An ordered pair with values a and b excludes a subsequent x precisely when a is greater than b and either x is at most b or x equals a, or when a equals b and x is smaller than a.

**Definition 1.4 (Maximum entry).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.maximum`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.maximum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The maximum is the fold of the natural maximum operation with initial value zero.

**Theorem 1.5 (Exact append criterion).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.safe_append_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/ClassCSites.safe_append_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every finite natural word w and natural x, appending x is safe if and only if w already avoids class C and every pair of positions i less than j less than the length of w fails to exclude x. A newly created forbidden occurrence must end at the appended position; the converse constructs the corresponding ranked occurrence.

**Theorem 1.6 (Exact update of safety).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.safe_update`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/ClassCSites.safe_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Let w be any nonempty natural word and suppose appending x is safe. For every natural y, appending y after x is safe exactly when y was safe after w and satisfies the following condition. If x is below the maximum of w, y must be greater than x and absent from w. If x equals the maximum, y must be at least that maximum. If x is a new maximum, no additional condition is imposed. Old exclusions therefore persist in all three cases.

**Definition 1.7 (Old admissible values).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.admissible`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The old admissible values are the safe naturals from zero through the maximum, retained as a finite set.

**Definition 1.8 (Sorted numeric sites).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.values`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.values` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The admissible values are listed in increasing order without duplicates. Keeping their numeric identities permits inversion of the choice correspondence.

**Definition 1.9 (Seen and unused labels).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.label`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.label` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

A value has label S when it occurs in the current word and label U otherwise.

**Definition 1.10 (Sorted site word).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.siteWord`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.siteWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Map the seen-or-unused label over the sorted admissible-value list. Repeated labels retain their distinct positions.

**Theorem 1.11 (Succession of sorted site words).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.site_word_succession`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/ClassCSites.site_word_succession` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every nonempty natural word w and safe appended x, a lower choice leaves a word of U labels, one for each old admissible unused value greater than x. Repeating the maximum leaves the single site S. A new maximum leaves the old site word followed by x minus the old maximum minus one U labels and one S label. These statements concern safety independently of the inversion bound.

**Definition 1.12 (Numeric choice decoder).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.choiceValue`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.choiceValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

An old choice is a position in the sorted value list and decodes to that value. A new choice has index j from zero through the slack minus one and decodes to the old maximum plus j plus one.

**Definition 1.13 (Bijection with legal appends).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.choiceEquiv`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.choiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every nonempty class-C-avoiding inversion sequence, the disjoint sum of old-site positions and slack indices is equivalent to the type of natural appends satisfying both safety and the bound by the current length. The inverse selects the unique sorted index of an old admissible value or the offset of a new maximum. All positions remain distinct even when child states agree.

**Definition 1.14 (Actual prefix state).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.stateOf`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.stateOf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For a nonempty inversion sequence, the state consists of its sorted site word, length minus maximum as positive slack, and the Boolean safety of its maximum. If that maximum is admissible, it is the final sorted site and has label S.

**Definition 1.15 (Formal lower state).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.lowerState`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.lowerState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every natural k and positive slack s, the formal lower state has k unused sites and no repeat flag. Such states are defined independently of actual-prefix reachability.

**Definition 1.16 (Formal repeat state).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.repeatState`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.repeatState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every positive slack s, the formal repeat state has one seen site and a true repeat flag.

**Definition 1.17 (Labelled child transition).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.child`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.child` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

Each old position is a separate choice. If the repeat flag is true and that position is final, its child is the repeat state with slack increased by one. Every other old choice has the lower state whose number of sites counts U labels strictly to its right, also with slack increased by one. A new choice with zero-based index j appends j unused labels and one seen label, and decreases the slack by j.

**Definition 1.18 (Choice coordinates of the actual state).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.liftChoice`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCSites.liftChoice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The numeric site's index and the corresponding site-word index agree because labelling preserves list length. Slack indices are unchanged.

**Theorem 1.19 (Native state-transition correspondence).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCSites.native_succession`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/ClassCSites.native_succession` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every nonempty class-C-avoiding inversion sequence and every labelled choice, append its decoded numeric value. The resulting word is again an inversion sequence, and its actual state equals the formal child of the original actual state at that choice. The equality includes the complete site word, positive slack and repeat flag. The final old position repeats exactly when its numeric value is the maximum; lower-site multiplicities count unused positions strictly to the right.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.ForbiddenTriple`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.Safe`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.admissible`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.child`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.choiceEquiv`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.choiceValue`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.label`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.liftChoice`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.lowerState`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.maximum`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.native_succession`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.patterns`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.repeatState`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.safe_append_iff`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.safe_update`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.siteWord`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.site_word_succession`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.stateOf`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCSites.values`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs](InversionSeqOccurs.md)
