# Four exact distance bins

## Abstract

Four exact distance bins

For an arbitrary landmark subset, let a_u be its original-vertex bit, b_uv its selected-midpoint bit, d_u its selected incident-midpoint count, A its original total and M its midpoint total. The four bin counts satisfy H0=a_u+b_uv, H1+b_uv=a_v+d_u, H2+a_u+a_v+b_uv=A+d_v and H3+d_u+d_v=M+b_uv. All equations use integers and preserve the exact counts at empty classes and at n=3.

**Definition 1.1 (originalBit).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.originalBit`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.originalBit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The original-vertex selection bit is the integer indicator of membership in the landmark set.

**Definition 1.2 (midpointBit).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointBit`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointBit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The midpoint selection bit is the integer indicator of membership in the landmark set.

**Definition 1.3 (originalTotal).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.originalTotal`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.originalTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The integer total counts selected originals.

**Definition 1.4 (midpointTotal).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointTotal`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The integer total counts selected midpoints.

**Definition 1.5 (selectedDegree).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.selectedDegree`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.selectedDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The selected degree counts selected midpoint vertices incident with an original.

**Definition 1.6 (bin).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.bin`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.bin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

A bin counts selected vertices at one actual edge distance, using integer-valued indicators.

**Theorem 1.7 (bin eq count).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.bin_eq_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.bin_eq_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The integer bin is the natural multiset multiplicity embedded in the integers.

**Theorem 1.8 (midpointBit swap).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointBit_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointBit_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The same selected midpoint bit is obtained in either endpoint order.

**Theorem 1.9 (histogram).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.histogram`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.histogram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

The four exact integer equations follow by summing the proved pointwise distance classes over every selected landmark.

**Theorem 1.10 (profile eq of histogram).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.profile_eq_of_histogram`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.profile_eq_of_histogram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero (2026). *Multiset resolvability parameters in graphs: A survey with new results and open problems*. URL: <https://arxiv.org/pdf/2607.10311v1>.

*Commentary.*

Four equal integer bins give equal actual distance multisets for the two incidence edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.bin`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.bin_eq_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.histogram`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointBit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointBit_swap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.midpointTotal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.originalBit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.originalTotal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.profile_eq_of_histogram`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.selectedDegree`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles](CompleteSubdivisionProfiles.md)
