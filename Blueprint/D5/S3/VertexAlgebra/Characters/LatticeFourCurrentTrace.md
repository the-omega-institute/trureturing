# Finite Four-Current Trace

## Abstract

Finite four-current traces on the original complete energy grades.

**Definition 1.1 (Ten labeled partial matchings).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.PM4`

*Formalization.* `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.PM4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The slots are Fin 4. There is one empty matching, six single-edge matchings, and three two-edge matchings. Every edge is ordered by its two slot labels; different edges remain distinct when their frequencies coincide.

**Definition 1.2 (Labeled edge sets).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.edges`

*Formalization.* `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.edges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each partial matching has its literal finite set of ordered pairs of distinct slots. The edge assignments in the coefficient are functions on this set, including its empty domain.

**Definition 1.3 (Original finite four-current cycle trace).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.actualFourCurrentCycleTrace`

*Formalization.* `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.actualFourCurrentCycleTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original LatticeData D with positive-definite real Gram matrix, every i : Fin 4 → Fin D.rank and every n : Fin 4 → Nat, the trace is the finite complex LinearMap.trace on the original grade n(0) of B0 composed with B1 composed with B2 composed with B3. Here Ba is the literal existing actualCurrentBlock D (i(a)) (n(a)) (n(a+1)), with cyclic indices. The rightmost block acts first. All charge and oscillator labels of each full grade remain in the domain, and the current-label domain retains rank zero.

**Definition 1.4 (Bounded ten-matching coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.boundedFourCurrentCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.boundedFourCurrentCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient sums over the positive charge cutoff, the ten labeled matchings, bounded positive frequencies, two arc choices, bounded windings, and bounded residual grade, with guarded full-grade equalities and signed Gram and zero-mode factors.

The internal source bridge identifies this literal four-block composition with the restriction and projection of the original neutral-mode word, using the original all-integer energy homogeneity theorem. Positivity proves that every negative original grade is zero. Finite rectangular trace cyclicity therefore applies across signed grades without an infinite trace or an imposed truncation.

For a word of total mode zero, the finite Heisenberg commutator gives T(N)-T(N-ell) as the three labeled contractions against the corresponding original two-mode word traces. For positive ell, a finite telescoping sum runs from k=0 through floor(N/ell); its terminal trace vanishes on a negative grade. A cyclic rotation is proved directly for the original four blocks. The remaining two-mode word is identified with the original two-block trace when both grades are nonnegative, and is zero when its intermediate grade is negative. The all-zero-mode trace is computed on the original full fiber as the charge-cutoff sum of the four charge weights times ordinary oscillator multiplicity.

**Theorem 1.5 (Exact bounded finite four-current trace).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.actual_four_current_grade_trace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.actual_four_current_grade_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original LatticeData D, positive-definite real Gram matrix hD, current labels i : Fin 4 → Fin D.rank, and natural full-energy grades n : Fin 4 → Nat, actualFourCurrentCycleTrace D hD i n equals boundedFourCurrentCoefficient D hD i n. Write Q(beta)=chargeEnergy(beta).toNat, h_a(beta)=bilinear(unitCharge(i(a)),beta), and p_D(t)=Nat.card(IntegerFiber D t). The coefficient sums beta over positiveChargeCutoff D hD min(n), and M over the ten labeled partial matchings. Each edge e=(a,b), a<b, has an independent frequency ell_e from 1 through max(n), an arc choice A_e equal to {a+1,...,b} or its complement, and winding k_e from 0 through min(n). The residual t runs from 0 through min(n). A summand is zero unless every j satisfies n(j)=Q(beta)+t+sum_e ell_e(k_e+indicator(j in A_e)). Otherwise it is p_D(t) times the product of h_a(beta) over unpaired slots, times the product of ell_e G(i(a),i(b)) over edges. The empty matching has one empty assignment. Frequencies may repeat and cross Gram entries retain their signs.

The arc difference equals the signed mode at each endpoint. The guarded grade equations therefore determine each positive frequency and its arc orientation uniquely. Their value at the initial grade is the creation delay plus the sum of winding energies. The two-edge assignment is bijective with an ordered pair of winding coordinates even at equal frequencies; no factorial or unlabeled count is used. The three leading-annihilator contractions are exactly the three possible labeled partners, with either two residual zero modes or the residual nonzero pair. Energy support proves that charge, winding, and residual bounds can be enlarged and restricted without adding a nonzero term. A nonconstant cyclic grade quadruple has a positive step after rotation; a constant quadruple uses the original zero-mode basis trace.

This structural identity is uniform in arbitrary natural grades and original lattice data; it is not a bounded enumeration of fixed inputs. Four-point joint absolute convergence, thermal summation, modularity, sewing, Monster realization, and the full string/AdS program remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.PM4`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.actualFourCurrentCycleTrace`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.boundedFourCurrentCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.edges`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.actual_four_current_grade_trace`
- Dependency: [D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingRotation](FourCurrent/MatchingRotation.md)
