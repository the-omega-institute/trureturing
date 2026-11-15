# Literal extensions and unique parents

## Abstract

Actual ordinary ascent words with literal adjacent-pair avoidance and exact boundary conditions.

**Definition 1.1 (CanAppend).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.CanAppend`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.CanAppend` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The exact ordinary ascent bound, including the empty-root bound zero, together with exclusion of every new literal occurrence at the appended value.

**Theorem 1.2 (append_avoiders_iff).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.append_avoiders_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.append_avoiders_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

For every subset of the thirteen patterns and every length n, appending a letter gives an actual length n+1 avoider exactly when its parent is an actual length n avoider and the exact extension conditions hold.

**Theorem 1.3 (parent_admission).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.parent_admission`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.parent_admission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Taking the length-n prefix of an actual length n+1 avoider and its final value gives an actual parent and a legal extension, including n=0.

**Definition 1.4 (extensionEquiv).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.extensionEquiv`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.extensionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

A genuine equivalence between actual length n+1 avoiders and pairs of an actual length-n parent and a legal appended value. Its inverse is literal concatenation, and both inverse identities are proved. No equivalence between different pattern classes is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.CanAppend`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.append_avoiders_iff`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.extensionEquiv`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.parent_admission`
- Dependency: [D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics](OrdinaryAscentSemantics.md)
