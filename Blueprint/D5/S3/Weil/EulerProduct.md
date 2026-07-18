# Euler Windows and Single-Address Heat

## Theorem: Finite Euler windows have only the local denominator lattice

Provenance: `literature-attested` via `D5/L/apostol1976introduction` (`lit/apostol1976introduction`)

Statement: `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus` `✓ std3`

A finite Euler product is nonzero exactly on the locus where every local denominator is nonzero, and the complementary denominator-zero locus is the union of the imaginary lattices indexed by its primes. Lean totalizes inversion with zero inverse equal to zero, so the zero-free clause is deliberately restricted to the regular locus; no pole order or numerical window certificate is asserted.

## Definition: The single-address reading is the von Mangoldt weight

Provenance: `literature-attested` via `D5/L/apostol1976introduction` (`lit/apostol1976introduction`)

Statement: `D5/S3/Weil/EulerProduct.single_address_reading_spec` `✓ std3`

Under the value map from a one-prime ledger state to a natural prime power, a nonzero exponent at p reads log p, while every non-prime-power value reads zero. This is the classical von Mangoldt coefficient in the repository's single-address coordinates.

## Proposition: The logarithmic derivative is the single-address heat trace

Provenance: `literature-attested` via `D5/L/apostol1976introduction` (`lit/apostol1976introduction`)

Statement: `D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative` `✓ std3`

In the convergence half-plane with real part greater than one, the L-series of the single-address reading equals minus the derivative of the classical zeta function divided by the zeta function. The statement adds no continuation beyond that half-plane.

## Remark: Journal and ledger readings

Provenance: `repo-derived`

Statement: `D5/S3/Weil/EulerProduct.single_address_reading_spec` `✓ std3`

Ordering terms by generated value resembles a chronological journal, while grouping powers by prime address resembles a classified ledger. The single-address theorem supplies the local weight behind that analogy; it does not formalize heat-time cosmology or a theta functional equation.

## Remark: Finite Euler windows do not create global zeros

Provenance: `repo-derived`

Statement: `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus` `✓ std3`

Every regular finite Euler window is nonzero, so no finite set of local factors realizes a nontrivial global zero. This supports only a finite-versus-tail boundary; collective-mode, prime-deletion, dense-phase, and equal-loudness interpretations are not proved here.

## Remark: Sum and product are two views of zeta

Provenance: `repo-derived`

Statement:

$$
\mathit{zetaSum} = \mathit{zetaProduct}
$$

The source calls the Dirichlet sum the start-reading direction, obtained by expanding and additively enumerating n^(-s), and calls the Euler product the terminal-reading direction, obtained by taking local factors along prime coordinate axes. Their equality is read as the analytic form of unique factorization and of a dual completion square; a truncated comparison is recorded as agreeing up to its tail. The sum view supports continuation through Mellin and theta methods and therefore sees zeros at long range, while the product view resolves local prime atoms. The explicit formula is the exchange rate between those views. The theta symmetry t <-> 1/t is then read as their mirror, with a source check to 1e-12; its fixed point t = 1 corresponds to real part one half and gives the claimed balance point. This explains why the line is structurally selected, but explicitly does not imply that every zero lies on it.

## Remark: The pole is not an off-line zero

Provenance: `repo-derived`

Statement:

$$
\mathit{zetaResidue} = 1
$$

The source separates two proposed gaps. Noncompactness is an unavoidable proved feature, independent of the Riemann hypothesis and needed as a conservation outlet; an off-line zero is a conjectural defect that may not exist. Noncompactness is not said to create such a zero, only to make its exclusion harder. The unavoidable opening is assigned instead to the unique simple pole at s = 1. Every individual Euler factor is finite there, so no single prime owns the divergence; the infinity of primes and the noncompact axis own it jointly. The source records a three-scale Mertens check of product growth like exp(gamma)*log(P) and a residue-one check to 1e-9. Its final single-outlet picture is explicitly not a theorem: one noncompact place, one simple pole, and conjecturally no off-line zeros are interpreted as concentrating the unavoidable opening at the official pole, leaving an off-line zero as an opening that should not be present.
