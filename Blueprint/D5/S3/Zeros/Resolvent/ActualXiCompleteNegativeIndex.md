# Complete actual xi negative index

## Abstract

Complete actual xi ordinary-square negative index, distinct off-line quartets, and all finite derivative Hankel matrices.

**Theorem 1.1 (Complete quartet count).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_negative_index`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_negative_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete polynomial-space negative index equals the ENat cardinality of the actual off-line quartet representatives. Reconstruction holds for every x, while strict negativity is required only when x is nonzero. The support argument retains the empty family k=0 and imposes no condition on E(0). This index identity neither proves RH nor assumes it.

The consumed common_support_of_linear_map helper factors any real-linear T from Fin(k) coordinates through Polynomial.ofFn(N+1), independently of energy and injectivity. Set p_j=T(Pi.single j 1) and N=sup_j natDegree(p_j). The existing Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt reconstructs each basis image, and LinearMap.pi_ext extends the equality to every vector using Pi.single j r = r times Pi.single j 1. Injectivity of T then gives injectivity of its coefficient map; nonzero-vector negativity transports through reconstruction. Conversely, compose a finite coefficient map with Polynomial.ofFn and use Polynomial.injective_ofFn. This gives equality of negative ranks for an arbitrary energy, including the zero-dimensional case.

ActualEnergy retains the entire positive-height spectrum, the ordinary complex square, and all analytic multiplicities as weights. ActualCoefficientEnergy uses the original xiCoefficient derivatives at indices a+b, which is precisely the existing even-shift actual_xi_hankel_identity with m=0. Polynomial.ofFn_eq_sum_monomial supplies polynomial evaluation. Both directions of actual_negativeIndex_eq_matrix_sup explicitly rewrite via actual_coefficient_energy_identity. ActualMatrixNegativeIndex is the supremum over N of negativeIndex(actualCoefficientEnergy N), on the real coordinate space Fin(N+1).

QuartetRepresentative consists of positive-height zeros with real part greater than 1/2. The existing actual conjugation sends a zero to 1-conj(zero), so its real part is 1-Re(zero). This separates every representative from the conjugate of every representative at the index level, as the integer-family supplier requires. For a nonreal node, node_real_iff excludes the critical line; right-half-plane indices are representatives, and left-half-plane indices are conjugates of representatives by the actual tau_involutive theorem. No arbitrary permutation-inverse assumption is used.

For finite representatives, first install Fintype.ofFinite and enumerate the whole subtype. The generic negativeIndex_le consumes only exhaustive coverage and nonnegative real-node weights after the selector. A conjugation-fixed node has imaginary part zero by congrArg Complex.im, so node_real_positive supplies the weight sign. For the lower bound, Subtype.val_injective composed with the representative embedding gives selector injectivity. The existing integer-family supplier returns N, U, negativity only for nonzero real combinations, and injection of A(t)(a)=sum_j t_j U(j,a). Explicit cast and sum commutations identify the combined polynomial evaluation; the actual energy identity transfers its negativity. The negative polynomial-space witness is Polynomial.ofFn composed with A, not A alone.

The finite counting branch uses matching exhaustive upper and embedded-family lower bounds, including cardinality zero. In the infinite branch, explicitly obtain Infinite from not Finite, choose every finite embedding with Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card at the empty set, and apply ENat.eq_top_iff_forall_ge. Each rank contributes to the complete-lattice supremum via le_sSup. Distinct quartets count negative directions; analytic multiplicities do not multiply the count.

ActualXiIntegerCriterion supplies node_large_finite and weight_ne_zero at their original owner, with their statements and proofs preserved. CountableHankelNegativeIndex consumes square_summable at CountableHankelNegativeWitness. The upper argument permits repeated nodes and selectors; the actual lower construction uses distinct folded nodes and the original all-real injectivity of the integer coefficient map. No interpolation proof is copied.

**Theorem 1.2 (Supremum of finite derivative Hankel indices).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_derivative_hankel_index`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_derivative_hankel_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative-Hankel endpoint states that the supremum of all finite actual derivative Hankel negative indices equals ENat.card QuartetRepresentative. It consumes actual_negativeIndex_eq_matrix_sup and actual_complete_negative_index, so the reconstruction and actual-energy joins are part of the final proof chain. Together the endpoints retain complete actual index = quartet count = finite-matrix index supremum, in zero, finite, and infinite cases, without an RH premise or a modulus-square replacement.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_derivative_hankel_index`
- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_negative_index`
- Dependency: [D5/S3/Constants/Moments/CountableHankelIntegerFamily](../../Constants/Moments/CountableHankelIntegerFamily.md)
- Dependency: [D5/S3/Constants/Moments/CountableHankelNegativeIndex](../../Constants/Moments/CountableHankelNegativeIndex.md)
- Dependency: [D5/S3/Weil/ZetaLinear/ExactStickyReduction](../../Weil/ZetaLinear/ExactStickyReduction.md)
- Dependency: [D5/S3/Zeros/Resolvent/ActualXiDictionary](ActualXiDictionary.md)
- Dependency: [D5/S3/Zeros/Resolvent/ActualXiIntegerCriterion](ActualXiIntegerCriterion.md)
