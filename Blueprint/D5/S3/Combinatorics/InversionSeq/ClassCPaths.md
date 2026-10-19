# Class-C Continuation Paths

## Abstract

Finite labelled paths of coherent site states are equivalent to actual native prefix extensions.

Every position of the site word and every new-maximum index labels its own branch. Equal child states therefore preserve the multiplicity of their incoming choices. The construction applies to all coherent formal states, including those not realized by a prefix. Its interpretation by numeric words is established separately for nonempty native inversion prefixes avoiding the four class-C patterns.

**Definition 1.1 (Labelled continuation paths).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.Path`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCPaths.Path` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

At depth zero the path type is a singleton. At depth r plus one, a path consists of one labelled choice and a depth-r path from its formal child. This dependent finite type retains the chosen branch at every step.

**Definition 1.2 (Finite continuation count).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.phi`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCPaths.phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every depth and coherent state, the continuation count is the natural cardinality of the finite labelled path type.

**Definition 1.3 (Formal repeat-state continuation count).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.b`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCPaths.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every depth r and positive slack s, b is the continuation count from the single seen site with the repeat flag. It is defined on every such formal state independently of actual-prefix reachability.

**Definition 1.4 (Actual numeric suffixes).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.Extensions`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCPaths.Extensions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

An extension of a valid nonempty prefix q at depth r is a list u of length r such that q followed by u lies in the native avoider set at total length q.length plus r. Both position-dependent inversion bounds and all four ranked-pattern exclusions are retained.

**Definition 1.5 (Constructor and decoder correspondence).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.extensionEquiv`

*Formalization.* `D5/S3/Combinatorics/InversionSeq/ClassCPaths.extensionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every valid nonempty prefix and every depth, actual numeric suffixes are equivalent to labelled formal paths from its actual state. Splitting a nonempty suffix selects its first legal value and its remaining suffix; joining prepends that value. Prefix deletion preserves native avoidance and the inversion bound. The sorted-value choice bijection and the native one-step state equality then transport the constructor recursively. Both inverse laws are proved.

**Theorem 1.6 (Cardinality of actual continuations).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.native_continuation_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/ClassCPaths.native_continuation_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

For every valid nonempty prefix q and every natural depth r, the cardinality of its actual extension type equals the depth-r path count of its actual state. Finiteness of the actual extensions follows from the explicit equivalence to finite labelled paths. The equality uses the constructor and decoder correspondence rather than a state-sufficiency assumption.

**Theorem 1.7 (Native empty and root counts).**

Lean statement: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.native_avoider_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/InversionSeq/ClassCPaths.native_avoider_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan, Toufik Mansour (2023). *Inversion Sequences Avoiding Quadruple Length-3 Patterns*. DOI: [10.5281/zenodo.8399694](https://doi.org/10.5281/zenodo.8399694). URL: <https://math.colgate.edu/~integers/x78/x78.pdf>.

*Commentary.*

The native class-C avoider set at length zero contains exactly the empty word and has cardinality one. For every natural n, its cardinality at length n plus one equals b at depth n and slack one. Every positive-length inversion sequence begins with zero. Deleting that first zero and reattaching it gives inverse maps between whole avoiders and the actual suffixes of the prefix consisting of zero. This prefix has one seen admissible site, positive slack one and a true repeat flag. The result identifies the actual cardinality with finite labelled paths. The all-depth affine invariant, path injections with complement cardinalities and nonnegative differences, both universal a/b recurrences, the class-A/B equality and generating-series identities remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.Extensions`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.Path`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.b`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.extensionEquiv`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.native_avoider_counts`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.native_continuation_count`
- Truth anchor: `D5/S3/Combinatorics/InversionSeq/ClassCPaths.phi`
- Dependency: [D5/S3/Combinatorics/InversionSeq/ClassCSites](ClassCSites.md)
