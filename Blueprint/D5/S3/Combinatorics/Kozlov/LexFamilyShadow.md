# Lexicographic compression of uniform families

## Abstract

Lexicographic initial segments minimize upper shadows. The componentwise inequality combines this with the cost-minimizing greedy split.

**Definition 1.1 (Lexicographic precedence).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.LexLT`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.LexLT` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The first element in the symmetric difference belongs to the earlier set.

**Definition 1.2 (Lexicographic initial segments).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.IsLexInit`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.IsLexInit` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

All faces have one common size and the family contains every earlier face of that size.

**Lemma 1.3 (Lexicographic precedence is strict).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_irrefl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_irrefl` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A witness of precedence must belong to one set and be absent from the other.

**Lemma 1.4 (The empty family is initial).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_empty` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

It has no member requiring a predecessor.

**Lemma 1.5 (Every zero-degree family is initial).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_of_sized_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_of_sized_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The only candidate face in degree zero is the empty set.

**Lemma 1.6 (A full layer is initial).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_powersetCard`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_powersetCard` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every earlier face of that degree already belongs to the full layer.

**Lemma 1.7 (Shadow of a full layer).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.upShadow_powersetCard`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.upShadow_powersetCard` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A face one degree higher has a predecessor obtained by deleting any one of its elements.

**Definition 1.8 (Embed a face and adjoin zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Shift the ground elements up by one and adjoin zero.

**Definition 1.9 (Embed a face avoiding zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Shift every element up by one.

**Lemma 1.10 (Zero is adjoined).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.zero_mem_c0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.zero_mem_c0` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The first embedding includes zero by insertion.

**Lemma 1.11 (Successor membership after adjoining zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.succ_mem_c0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.succ_mem_c0` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

An index other than zero belongs to the image exactly when its predecessor belongs to the original face.

**Lemma 1.12 (The shifted face avoids zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.zero_notMem_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.zero_notMem_lift` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

All images of the shift are successors.

**Lemma 1.13 (Successor membership after shifting).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.succ_mem_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.succ_mem_lift` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Membership of a successor in the shifted image reads membership of its predecessor.

**Lemma 1.14 (Recover the face from the zero-containing embedding).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_injective` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Read successor membership to recover the original face.

**Lemma 1.15 (Recover the face from the shifted embedding).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_injective` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Read membership on successor coordinates.

**Lemma 1.16 (The two embeddings are disjoint).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_ne_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_ne_lift` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The first image contains zero and the second avoids it.

**Lemma 1.17 (The reverse disjointness comparison).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_ne_c0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_ne_c0` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The image avoiding zero differs from every image containing zero.

**Lemma 1.18 (The embedding that adjoins zero increases size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_c0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_c0` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Zero is outside the shifted image and gives one extra element.

**Lemma 1.19 (The shift preserves size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_lift` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The shift is injective.

**Lemma 1.20 (Split a face at zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.cases_c0_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.cases_c0_lift` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Separate the zero-membership case and invert the shift on the successor part.

**Lemma 1.21 (Erasing the adjoined zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_erase_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_erase_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The remaining elements form the shifted image.

**Lemma 1.22 (Erase a successor from the zero-containing face).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_erase_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_erase_succ` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Erase its predecessor before embedding and adjoining zero.

**Lemma 1.23 (Erase a successor from the shifted face).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_erase_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_erase_succ` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

This is the shift of the face with the predecessor erased.

**Definition 1.24 (The part containing zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Remove zero and reverse the shift in the subfamily of faces that contain zero.

**Definition 1.25 (The part avoiding zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Reverse the shift in the subfamily of faces that avoid zero.

**Lemma 1.26 (Membership in the zero-containing part).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_top`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_top` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Test whether the face obtained by shifting and adjoining zero belongs to the family.

**Lemma 1.27 (Membership in the zero-avoiding part).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_bot` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Test whether the shifted face belongs to the family.

**Definition 1.28 (The zero-containing embedding).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0Emb`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0Emb` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Package the injective map that adjoins zero.

**Definition 1.29 (The zero-avoiding embedding).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.liftEmb`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.liftEmb` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Package the injective shift map.

**Lemma 1.30 (Reconstruct a family from the two parts).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.eq_glue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.eq_glue` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every face lies in exactly the part determined by its zero membership.

**Lemma 1.31 (Recover the zero-containing part).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top_glue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top_glue` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Map the two parts back and use the fact that the second image avoids zero.

**Lemma 1.32 (Recover the zero-avoiding part).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot_glue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot_glue` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Map the two parts back and use the fact that the first image contains zero.

**Lemma 1.33 (Size of the reconstructed family).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_glue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_glue` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The two injective images are disjoint.

**Lemma 1.34 (Split the cardinality at zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_top_add_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_top_add_bot` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply disjoint reconstruction to the two halves of a family.

**Lemma 1.35 (Shadow faces containing zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top_upShadow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top_upShadow` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Either the predecessor already contained zero or the newly added element was zero. These give the shadow of the first part and the entire second part.

**Lemma 1.36 (Shadow faces avoiding zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot_upShadow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot_upShadow` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A predecessor of a zero-avoiding face also avoids zero. Shifting commutes with forming those extensions.

**Lemma 1.37 (Lex order inside the first part).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_c0_c0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_c0_c0` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Zero is shared and comparisons are preserved by the shift.

**Lemma 1.38 (Lex order inside the second part).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_lift_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_lift_lift` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every differing element is a successor and the shift preserves order.

**Lemma 1.39 (Zero-containing faces come first).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_c0_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_c0_lift` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Zero is the least element and occurs only in the first face.

**Lemma 1.40 (No reverse comparison across the split).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.not_lexLT_lift_c0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.not_lexLT_lift_c0` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Zero defeats any candidate precedence from the zero-avoiding face.

**Lemma 1.41 (Initial segments across the zero split).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_succ_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_succ_iff` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The two parts must be initial and a nonempty second part forces a full first part. The lex comparison across zero gives both directions.

**Theorem 1.42 (Lexicographic shadows are initial and have the recursive size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexInit_upShadow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexInit_upShadow` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Induct on the ground set using the two shadow identities. The full first block controls the transition into the second block.

**Theorem 1.43 (Realize every feasible initial-segment size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.exists_isLexInit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.exists_isLexInit` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Split at the first capacity, construct the two initial segments on the smaller ground set and glue them.

**Definition 1.44 (Complement and reverse the ground order).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Take the complementary face and reverse its indices. This converts the lex upper-shadow problem to a colex lower-shadow problem.

**Lemma 1.45 (Membership under complement and reversal).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_phi` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The reversed index is absent from the original face exactly when the index belongs to the transformed face.

**Lemma 1.46 (Complement and reversal are involutive).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_phi` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Reversing the ground index twice and complementing twice restore each membership test.

**Lemma 1.47 (Invert complement and reversal).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_injective` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Both operations are invertible.

**Lemma 1.48 (Complementary degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_phi` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The image has the ambient size minus the original face size.

**Lemma 1.49 (Translate lex precedence to colex).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_iff_colex`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_iff_colex` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Reversal sends the first differing index to the last and complement switches its membership.

**Lemma 1.50 (Membership under the change of variables).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_image_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_image_phi` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A face lies in the image exactly when an original face maps to it.

**Lemma 1.51 (Adding a point becomes deletion).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_insert` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Complement and reversal turn insertion of an absent point into removal of its reversed index.

**Lemma 1.52 (Exchange upper and lower shadows).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.shadow_image_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.shadow_image_phi` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

An original one-point extension corresponds to deletion of the reversed point. Invert the map for the converse.

**Lemma 1.53 (Transport initial segments to colex).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isInitSeg_image_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isInitSeg_image_phi` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the order comparison and complementary degree to reconstruct a predecessor in the original lex family.

**Theorem 1.54 (Lex segments minimize upper shadows).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.kk_lex`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.kk_lex` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Move by complement and reversal to colex and apply the pinned Kruskal-Katona inequality for lower shadows.

**Theorem 1.55 (The numerical lower bound for a uniform shadow).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.thm_kk_rank1`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.thm_kk_rank1` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Choose a lex segment of the same size and evaluate its minimum shadow by the recursive count.

**Definition 1.56 (A family of the indicated degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.Component`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.Component` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For nonnegative degree the family is uniform. A negative-degree component is empty.

**Lemma 1.57 (The capacity bound for a component).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_le` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The family sits inside a full binomial layer or is empty.

**Lemma 1.58 (The minimum shadow bound for a component).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.costZ_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.costZ_le` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the one-family Kruskal-Katona inequality and handle the empty negative-degree case.

**Theorem 1.59 (The greedy lex list minimizes the total shadow).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.module_shadow_ge_greedy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.module_shadow_ge_greedy` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Bound each component by its rank-one minimum, then use the block exchange to bound their summed cost by the greedy allocation.

**Theorem 1.60 (Realize the greedy allocation by families).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.exists_lexInit_components`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.exists_lexInit_components` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Build a lex-initial segment of the assigned size at each nonnegative degree and put the empty family at negative degrees.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.Component`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.IsLexInit`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.LexLT`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot_glue`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.bot_upShadow`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0Emb`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_erase_succ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_erase_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_injective`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.c0_ne_lift`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_c0`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_glue`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_lift`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_phi`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.card_top_add_bot`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.cases_c0_lift`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.costZ_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.eq_glue`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.exists_isLexInit`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.exists_lexInit_components`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isInitSeg_image_phi`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_empty`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_of_sized_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_powersetCard`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.isLexInit_succ_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.kk_lex`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexInit_upShadow`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_c0_c0`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_c0_lift`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_iff_colex`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_irrefl`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lexLT_lift_lift`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.liftEmb`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_erase_succ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_injective`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.lift_ne_c0`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_bot`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_image_phi`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_phi`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.mem_top`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.module_shadow_ge_greedy`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.not_lexLT_lift_c0`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_injective`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_insert`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.phi_phi`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.shadow_image_phi`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.succ_mem_c0`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.succ_mem_lift`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.thm_kk_rank1`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top_glue`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.top_upShadow`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.upShadow_powersetCard`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.zero_mem_c0`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexFamilyShadow.zero_notMem_lift`
- Dependency: [D5/S3/Combinatorics/Kozlov/LexGreedySplit](LexGreedySplit.md)
