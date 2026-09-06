# Discrete-time balanced truncation: ordered cuts and strict stability

## Verified locator

Igor Pontes Duff and Patrick Kürschner, *Numerical computation and new output bounds for time-limited balanced truncation of discrete-time systems*, Linear Algebra and its Applications 623 (2021), 367–397. DOI: `10.1016/j.laa.2020.09.029`.

The proof comparison uses the publicly accessible author preprint `arXiv:1902.01652v1`, submitted 5 February 2019: https://arxiv.org/abs/1902.01652v1 and https://arxiv.org/pdf/1902.01652 . Section 3.2.1, printed page 8, distinguishes stability preservation by ordinary infinite-horizon discrete BT for stable full systems from the time-limited variant. Its Proposition 3.1 gives a sufficient condition for the latter, with a residual-corrected Stein matrix and a controllability assumption. The page was visually checked; its proposition is not the exact signature of the new Lean theorem.

András Varga, *Balanced truncation model reduction of periodic systems*, Proceedings of the 39th IEEE Conference on Decision and Control (2000), 2379–2384. Author-hosted PDF: https://elib.dlr.de/11634/1/varga_cdc2000p2.pdf . Section 3, equations (9)–(11) and Theorem 1, on the third PDF page, supplies square-root balancing and a combined stability-and-minimality theorem for periodic systems after a partition with separated retained and discarded weights. The new modules do not formalize this periodic theorem.

The first publication's journal metadata is also listed by its author at https://sites.google.com/view/patrickkuerschner/home/publications . These locators were inspected on 6 September 2026.

## Matching mathematical objects

The repository uses real, finite-dimensional, discrete-time systems with zero initial state. Its exact infinite Gramians are built from the actual matrices. The state transformation is written `x = T z`, with inverse `S`, so the transformed matrices are `S A T`, `S B`, and `C T`. This is the inverse convention to papers that write the balanced state as `T x`; the underlying construction is identical after renaming the inverse.

`OrderedBalancedCoordinates` sorts the true weights in descending order and applies the same permutation to the columns of `T` and rows of `S`. `ordered_hankel_schmidt` connects that sorted output to the previously constructed whole-half-line Hankel operator. The proof does not substitute finite-window singular values for the infinite singular spectrum.

## Stability proof and the role of a gap

`DiscreteSteinCompressionStability.principal_truncation_spectrum_lt_one` has explicit premises: a positive diagonal `D`, the real inequality `A^T D A + C^T C <= D`, and joint injectivity of all actual full-system future readouts. Its conclusion uses the standard complex spectrum of the actual principal block: every pole has modulus strictly below one.

For a complex retained eigenvector, extend it by zero. The full diagonal energy splits into retained and discarded terms. The discrete Stein inequality bounds the eigenvalue modulus by one. Modulus exactly one forces both the discarded state action and output to vanish, so the zero extension is an unobservable eigenvector of the full system. Full observation excludes it. Real and imaginary parts explicitly transfer the real hypotheses to all complex eigenvectors.

This proof requires no strict singular-value gap. The omitted term `A21^* D2 A21` is essential to the argument. The result concerns strict stability, not reduced minimality, and is not transferred without proof to continuous-time Lyapunov inequalities or time-limited Gramians. The no-gap stability statement agrees with the infinite-horizon distinction in Duff and Kürschner; their time-limited Proposition 3.1 has different premises and is not imported as an axiom.

A concrete tied-weight example separates stability from minimality: `A=[[0,1],[0,0]]`, `B=[[0],[1]]`, `C=[[1,0]]` has exact `P=Q=I`. Retaining the first coordinate yields `Ar=[0]`, `Br=[0]`, `Cr=[1]`. It is strictly stable and uncontrollable. This example is checked with exact rational arithmetic in the companion regression; the universal stability assertion comes from the candidate Lean proof.

## Source-to-formalization map

| Mathematical step | Repository declaration |
| --- | --- |
| Descending weights with an actual coordinate permutation | `OrderedBalancedCoordinates.reindexCoordinates`, `retained_weight_ge_discarded` |
| Complexified discrete Stein argument | `DiscreteSteinCompressionStability.complex_observability_stein` |
| Exclusion of boundary eigenvalues of the actual cut | `DiscreteSteinCompressionStability.principal_truncation_eigenvalue_lt_one` |
| Strict standard complex-spectrum conclusion | `DiscreteSteinCompressionStability.principal_truncation_spectrum_lt_one` |
| Sorted weights retain genuine infinite Hankel semantics | `OrderedStableBalancedTruncation.ordered_hankel_schmidt` |
| One original-system construction with stability and both error bounds | `OrderedStableBalancedTruncation.ordered_stable_reduction` |

All module paths begin `D5/S3/Observer/Hankel/`. These sources formalize a classical mechanism and its repository integration; there is no claim of a new error constant, historical priority, a new periodic theorem, or an executed numerical balancing algorithm. Lean kernel acceptance and Scribe emission were not performed in this authoring environment.
