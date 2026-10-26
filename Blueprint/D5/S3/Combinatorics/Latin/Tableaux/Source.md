# Source for Latin tableaux

## Abstract

Literal source Latin tableaux: Source

Daugherty et al., arXiv:2610.29291v1, Conjecture 6.3 asks for the full count of Latin tableaux of shape (k,k-1,...,5,4,3,3) for every integer k at least five. Cells and integer symbols retain their fixed identities, and the prescribed symbol multiplicities are those of the conjugate partition.

**Definition 1.1 (Fixed source cells).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.Cells`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.Cells` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The dependent cell type keeps every row and column position, including the two distinct bottom rows of length three.

**Definition 1.2 (Unrestricted integer fillings).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.Filling`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.Filling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

A filling assigns an arbitrary integer to every fixed source cell. No bounded-symbol assumption enters the source definition.

**Definition 1.3 (The exact conjectural shape).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.shape`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.shape` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

For k at least five this is (k,k-1,...,5,4,3,3), in the source order.

**Definition 1.4 (The full conjugate type).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.conjugate`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.conjugate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The multiplicity of an integer s is the number of rows of length at least s when s is positive, and zero otherwise.

**Definition 1.5 (Literal source Latin tableaux).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.SourceLatin`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.SourceLatin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Every row and column is injective, and the multiplicity equation is imposed for every integer symbol. This is the unreduced count of Definition 2.5 and Section 4.

**Definition 1.6 (The literal source count).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.LT`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.LT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Nat.card of the entire subtype of unrestricted integer fillings satisfying SourceLatin. Finiteness is subsequently proved.

**Definition 1.7 (Actual row symbols).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.rowSymbols`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.rowSymbols` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The finite image of the filling on a single fixed row.

**Theorem 1.8 (Conjugate type forces row saturation).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.source_row_symbols`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Source.source_row_symbols` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Strong induction on symbols and exact multiplicity quotas prove that every row has exactly the integers 1 through its length. This is proved from the full type condition, rather than assumed.

**Definition 1.9 (Equivalent row formulation).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.RowLatin`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.RowLatin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Rows are injective and have the full initial interval of integer symbols, and columns remain injective.

**Theorem 1.10 (Both directions of source correspondence).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.source_iff_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Source.source_iff_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The converse counts occurrences by an explicit bijection with rows containing the symbol, recovering the conjugate multiplicities for all integers.

**Definition 1.11 (Finite carrier with actual integer interpretation).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.FiniteLatin`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.FiniteLatin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

A row of length m uses Fin m; its integer interpretation is value plus one. Fixed positions are preserved.

**Definition 1.12 (Reversible unrestricted-to-finite correspondence).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.sourceEquiv`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Source.sourceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Explicit inverse functions give an equivalence between all source integer tableaux and FiniteLatin. Equal-length rows and all fixed integer symbols remain distinct.

**Theorem 1.13 (Source finiteness).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Source.source_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Source.source_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Transport finiteness along sourceEquiv. The finite carrier is justified by a reversible correspondence, not substituted for the source objects.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.Cells`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.Filling`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.FiniteLatin`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.LT`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.RowLatin`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.SourceLatin`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.conjugate`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.rowSymbols`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.shape`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.sourceEquiv`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.source_finite`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.source_iff_rows`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Source.source_row_symbols`
