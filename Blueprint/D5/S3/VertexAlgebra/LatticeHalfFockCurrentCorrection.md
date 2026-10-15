# The full charged correction commutes with source partial derivatives

The Lean identities and their source-bound registration candidates await compilation, axiom-closure checks and exact binding validation. No kernel acceptance or completed registration is asserted here. This companion is a source-only draft; canonical Scribe rendering remains pending.

LatticeData has arbitrary finite rank and a symmetric integral Gram matrix with even diagonal. Rank zero, degenerate and indefinite forms remain in scope. Every charge, oscillator index, finite oscillator polynomial and natural correction shift retains its original domain; there is no occupation or order cutoff.

The operator is exactly the original Corr. Its correctionWord has the original singletonPolynomial, pairPolynomial and pairDerivation; no neutral substitution or alternative correction map is used.

## Adding one exponent adds one labelled occurrence

Lean candidate: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.occurrences_cons`

For every lattice D, index i and finitely supported natural exponent e, the list i :: occurrences(D,e) permutes occurrences(D,e + single(i,1)). The multiset equality retains repeated occurrences. This enumeration identity supplies the monomial step of correctionLift_X_mul.

## Multiplication by a source variable becomes the original insertion

Lean candidate: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_X_mul`

For every D, charge a, index i and oscillator polynomial p, correctionLift(D,a)(p X_i) equals insertion(D,a,i)(correctionLift(D,a)(p)). The lift uses the monomial basis and the original correctionWord. Polynomial induction reduces multiplication to occurrence insertion, and correctionWord_permutation removes the dependence on occurrence order.

## Source partial derivatives commute with the polynomial correction lift

Lean candidate: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.correctionLift_partial`

For every D, charge a, index i and oscillator polynomial p, partial_(some i)(correctionLift(D,a)(p)) equals correctionLift(D,a)(partial_i(p)). Ordinary source partials annihilate the singleton and pair coefficients, commute with pairDerivation, and differentiate insertion by its retained-variable term plus insertion of the derivative. Polynomial induction then gives the unrestricted lift identity.

## The full charged correction commutes with source partial derivatives

Lean candidate: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial`

The source derivative at any ordinary index commutes coefficientwise through Corr for every charge, polynomial and correction shift. The proof establishes partial_pairDerivation and partial_insertion on the actual correction polynomial, retaining the charged singleton and pair constants, and then passes through optionEquivLeft.

The singleton coefficient at source weight one is the actual negative charge pairing divided by two. The pair coefficients retain pairScalar and both halfBinomial factors. They are constants for the source partial derivative, not deleted terms. Passing through optionEquivLeft and extracting each shift coefficient gives Corr_partial. The original frequency-weighted current law still requires the actual charge zero mode.

Each of the four public identities has a candidate source-bound Contract.Registration with an exact source-equivalence bridge, a positive law, a rejected whole-family intervention, role sensitivity and actual observational dependence. The existing paired Corr_partial readout and its equivalence bridge are retained. The two obligation abbreviations are types, not registrations. No compiled registration or declared_validated binding evidence is supplied. Finite roles impose no finiteness on parameters, states or outputs; variation is over whole families, so zero and degenerate fibers are retained. The unknown continuation records only an unresolved residual.

These are repository derivations of classical twisted lattice correction identities with FLM background, with no literature novelty claim. The next operator step is the original frequency-weighted Corr current identity with its charge zero mode. This unit does not establish arbitrary-ground closed scalar evaluation, native all-state BPZ integration, full twisted Jacobi, or the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives.

## References

- Source attribution for all four candidates: repository-derived, with FLM background.
- Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).
- Candidate declaration anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection.Corr_partial`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
