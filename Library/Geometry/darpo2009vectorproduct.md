---
bibkey: darpo2009vectorproduct
authors: Erik Darpö
year: 2009
title: Vector product algebras
doi: 10.1112/blms/bdp066
url: https://arxiv.org/abs/0810.5464v1
claim: Theorem 1 classifies vector product algebras with their compatible nondegenerate symmetric bilinear form; this is distinct from equivariance under the full special orthogonal group.
strata_touched: []
license: citation-only
triage: anchor
---

# Vector products and the full rotation hypothesis

Darpö, *Vector product algebras*, Bulletin of the London Mathematical Society 41(5), 898–902. The arXiv record identifies the journal reference and DOI; the primary preprint is https://arxiv.org/pdf/0810.5464v1.

The preprint's introduction defines an antisymmetric product with invariant inner-product pairing and the product-norm identity. Theorem 1 allows dimensions 0, 1, 3 and 7 and classifies isomorphism by the bilinear form. It does not assert that the seven-dimensional product is equivariant under every element of SO(7).

The FIB boundary volume uses this as a classical intermediate input in §§5 and 8. Its stricter full-SO condition and its fixed-input leakage optimization are separate computations. The octonion two-generator result is already sourced by `Library/VertexAlgebra/vanekeren2020atomicmonstercompletion.md` and owner §32.2; Baez's Artin locator is node2, whereas the cross-product and G2 locator is node14.

## Octonion coordinates for permission-dependent responses

John C. Baez, *The Octonions*, Bulletin of the American Mathematical Society 39 (2002), 145–205, DOI [10.1090/S0273-0979-01-00934-X](https://doi.org/10.1090/S0273-0979-01-00934-X), [arXiv:math/0105155](https://arxiv.org/abs/math/0105155). The author's [§2.2, node5](https://math.ucr.edu/home/baez/octonions/node5.html) supplies the classical Cayley–Dickson construction; [node2](https://math.ucr.edu/home/baez/octonions/node2.html) supplies alternativity and Artin's two-generator fact; [§4.1, node14](https://math.ucr.edu/home/baez/octonions/node14.html) supplies the octonion automorphism and cross-product background. The volume matches its Fano table by conjugating the second quaternion coordinate relative to Baez’s displayed pair convention; multiplication parentheses remain fixed.

The FIB boundary volume §§38–39 uses quaternion multiplication and the common unit-quaternion action as intermediate algebra, then proves its own finite tuple response classification for single-occurrence and reusable inputs and for one fixed shared exterior anchor. Neither those classical tools nor a generic Gram/orbit argument is presented as a new standalone theorem. The classification retains the actual joint source domain and the conditions for guards and metadata; it does not identify the full octonion carrier with native FIB reachability.

## Causal acquisition and initial-state identification

Mihály Petreczky, Laurent Bako and Jan H. van Schuppen, *Realization theory of discrete-time linear switched systems*, [arXiv:1103.1343v2](https://arxiv.org/pdf/1103.1343v2), Definition 6 and Remark 6. Definition 6 tests equality for all input/switching words; Remark 6 distinguishes experiments with different switching sequences from collecting data along one switching sequence. These are the relevant quantifiers for the FIB boundary volume §40. The paper's finite-mode realization and identification results do not supply the volume's exterior controls, same-initial-state return, copies, or numerical acquisition bounds.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2), Definitions 12, 17 and 20 and Figure 3. The definitions specify adaptive tests and separation by observed traces from candidate starting states. Figure 3 gives a system with no full adaptive distinguishing graph: every first choice merges a pair that still needs distinguishing. This is initial-state identification, rather than merely learning the later current state. The volume's octonion blind line is proved from its own chronological source/update contract; no finite automaton theorem or length bound is transferred to the continuous carrier.

Yuan Wang and Eduardo D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM Journal on Control and Optimization 33(4), 1102–1126 (1995), DOI [10.1137/S0363012993246828](https://doi.org/10.1137/S0363012993246828), [author-hosted primary reprint](https://www.sontaglab.org/FTPDIR/orders_ioequations_state_space_dimensions_wang_sontag_reprint_siam1995.pdf), §5.1 and Theorem 5.3. The discrete-time universal-input theorem assumes analytic, reversible and observable dynamics; reversible here means each fixed-control state map is one-to-one, not an executable reset or inverse permission. On the full octonion carrier every nonzero destructive map satisfies $A_u u=0$, so it fails that injectivity hypothesis. This remains true for the separately supplied mixed map $A_{c+d}$; its two-update recovery uses retained observations, not invertibility of that map. The theorem does not authorize combining counterfactual input words into a single destructive history.
