# `ZeroData` Hilbert Presentation Transport

## Abstract

Every valid `ZeroData` is a duplicate-free exhaustive presentation of the same multiplicity-aware nontrivial zeta-zero spectrum. This node lifts the unique zero-preserving reindexing through the analytic-multiplicity fibers and then to a unitary map between the corresponding `ell^2` spaces.

## Main result

For presentations `Z` and `Z'`, the unitary `T_{Z,Z'}` satisfies

\[
T_{Z,Z'}J_Z=J_{Z'}T_{Z,Z'},
\qquad
T_{Z,Z'}U_Z=U_{Z'}T_{Z,Z'},
\]

and

\[
[T\psi,T\phi]_{J_{Z'}}=[\psi,\phi]_{J_Z}.
\]

Thus mirror symmetry, Cayley dynamics, and the Krein form are independent of the choice-based natural-number presentation.

## Truth anchors

- `zeroCoordinatePresentationEquiv_mirror`
- `zeroHilbertPresentationUnitary_intertwines_mirror`
- `zeroHilbertPresentationUnitary_intertwines_cayley`
- `zeroHilbertPresentationUnitary_preserves_krein`
- `zeroData_hilbert_presentation_transport_spec`
