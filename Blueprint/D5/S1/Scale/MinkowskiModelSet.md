# Golden Minkowski Model Set

## Definition: Minkowski lattice, window, and labeled model set

Provenance: `literature-attested` via `D5/L/baakefrankgrimm2021three` (`lit/baakefrankgrimm2021three`)

Statement: `D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec` `✓ std3`

The physical and conjugate embeddings give an injective diagonal range. An internal-space window selects physical projections, and the labeled extension pairs selected points with their joint golden coordinates.

## Remark: Value and code geometries

Provenance: `literature-attested` via `D5/L/baakefrankgrimm2021three` (`lit/baakefrankgrimm2021three`)

Statement: `D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec` `✓ std3`

The same carrier admits a lattice-like value reading and a cut-and-project code reading. The internal window justifies calling the code geometry a model set; it does not by itself provide a Bloch decomposition, a spectral gap theorem, or a periodic classifier for the code layer.

## Remark: Off-diagonal load and diagonal blindness

Provenance: `repo-derived`

Statement:

$$
\mathit{Zqc} \ne \mathit{zeta}
$$

The source assigns the two-sided code genuine load only away from the diagonal: its cited off-diagonal results are reported to fail under replacement encodings. The classical zeta diagonal is instead code-blind whenever it is reached only through diagonal decomposition. Whether an off-diagonal invariant can return analytic information to that diagonal remains explicitly open as O-5.

## Remark: Trace-map program and the missing hyperbolicity engine

Provenance: `repo-derived`

Statement:

$$
x_{k + 1} = 2 \cdot x_{k} \cdot x_{k - 1} - x_{k - 2}
$$

The proposed O-5 route matches four pieces with the Fibonacci Hamiltonian trace map: a three-term recurrence with x(k+1) = 2*x(k)*x(k-1) - x(k-2), multiplicative closure with the SL2 trace identity, the involution J with the Fricke invariant surface, and convergence of W_K orbits with bounded-orbit spectral classification. On that reading, each Zqc axis component is encoded by an explicit finite-dimensional polynomial dynamical system carrying a conserved quantity. Transferring hyperbolicity far enough to read continuation and zero information from orbit asymptotics is the remaining open part, not a conclusion of this remark.

## Remark: Scaled zero images need an independent engine

Provenance: `repo-derived`

Statement:

$$
\frac{\mathit{rho}}{a \cdot \varphi^{2} + b \cdot \varphi^{3}}
$$

In the source cascade, every zeta zero rho produces the image lattice rho/(a*phi^2 + b*phi^3) whenever the corresponding exponent is nonzero. The leading scale ratio is phi, and the band endpoints interlace pole and critical images, with 1/(2*phi^3) as the stated left endpoint. This self-similar overlay is only a rearrangement of identities built from zeta, so without new input it gives no compressed zero argument. Its positive use is conditional: genuinely independent control of one quasiperiodic band, for example trace-map hyperbolicity, would constrain an entire family of phi-scaled zeta segments. The recursive skeleton is present; the independent engine is still O-5.

## Remark: Window parity becomes a congruence pattern

Provenance: `repo-derived`

Statement:

$$
\left\lfloor\varphi^{3}\right\rfloor = 4
$$

The four source words {1}, {3}, {4}, and {2,4} classify complete internal-window coverage on the a = 1 fiber: b = 0,1,2,3 occurs once and then stops, so this is a finite window pattern rather than a cyclic congruence. The number four is the capacity floor(phi^3), not modulus four, while parity is genuine. Dividing by a Witt factor of the form 1-v^2 makes an even window length terminate, as for length four, and makes an odd length alternate forever, as for length three with the nontrivial Z/2 character (-1)^k. Thus Witt inversion translates window data into a congruence pattern, and the reported cascade chirality is traced to even-versus-odd window length.

## Remark: The continuation wall is a transported boundary

Provenance: `repo-derived`

Statement:

$$
\mathit{continuationWall} \ne \mathit{zeroLine}
$$

The cyclotomic Estermann-Kurokawa mechanism relies on explicit control of polynomial-factor zeros. For irrational exponents the source replaces that input by two obligations: scaled independence of zeta zeros on the zero side and Hecke-Mahler zero avoidance on the axis side. Excluding those two failure channels unconditionally is the outstanding N-4 subaccount of O-5. The source then separates three geometries: the proved code spectrum on a circle, the conjectural zeta-zero spectrum on a line, and a conditional continuation wall on an axis whose bricks are transported critical zeros. The no-door reading of that wall is another projection of scaled zero independence. This dictionary rearranges zeta information and supplies no independent zero input; its new content is the claimed boundary of Zqc as an analytic object. A second independent derivation of the full exponent table is also recorded as passing without a new audit exception.
