using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class ActualXiCompleteNegativeIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncompiled source attempt: complete actual xi ordinary-square negative index, distinct off-line quartets, and all finite derivative Hankel matrices.",
        H("Complete actual xi negative-index source attempt"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-xi-complete-negative-index"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_negative_index"),
                H("Complete quartet count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This document accompanies uncompiled Lean proof attempts. The preserved source37754 has a rejected intermediate statement: negativity cannot hold at every vector. The repair asserts reconstruction for every x and strict negativity only when x is nonzero. It retains the empty family k=0 and imposes no condition on E(0). No Lean, kernel, RH, or official acceptance is asserted.")),
                    Paragraph(Text(
                        "The consumed common_support_of_linear_map helper factors any real-linear T from Fin(k) coordinates through Polynomial.ofFn(N+1), independently of energy and injectivity. Set p_j=T(Pi.single j 1) and N=sup_j natDegree(p_j). The existing Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt reconstructs each basis image, and LinearMap.pi_ext extends the equality to every vector using Pi.single j r = r times Pi.single j 1. Injectivity of T then gives injectivity of its coefficient map; nonzero-vector negativity transports through reconstruction. Conversely, compose a finite coefficient map with Polynomial.ofFn and use Polynomial.injective_ofFn. This gives equality of negative ranks for an arbitrary energy, including the zero-dimensional case.")),
                    Paragraph(Text(
                        "ActualEnergy retains the entire positive-height spectrum, the ordinary complex square, and all analytic multiplicities as weights. ActualCoefficientEnergy uses the original xiCoefficient derivatives at indices a+b, which is precisely the existing even-shift actual_xi_hankel_identity with m=0. Polynomial.ofFn_eq_sum_monomial supplies polynomial evaluation. Both directions of actual_negativeIndex_eq_matrix_sup explicitly rewrite via actual_coefficient_energy_identity. ActualMatrixNegativeIndex is the supremum over N of negativeIndex(actualCoefficientEnergy N), on the real coordinate space Fin(N+1).")),
                    Paragraph(Text(
                        "QuartetRepresentative consists of positive-height zeros with real part greater than 1/2. The existing actual conjugation sends a zero to 1-conj(zero), so its real part is 1-Re(zero). This separates every representative from the conjugate of every representative at the index level, as the integer-family supplier requires. For a nonreal node, node_real_iff excludes the critical line; right-half-plane indices are representatives, and left-half-plane indices are conjugates of representatives by the actual tau_involutive theorem. No arbitrary permutation-inverse assumption is used.")),
                    Paragraph(Text(
                        "For finite representatives, first install Fintype.ofFinite and enumerate the whole subtype. The generic negativeIndex_le consumes only exhaustive coverage and nonnegative real-node weights after the selector. A conjugation-fixed node has imaginary part zero by congrArg Complex.im, so node_real_positive supplies the weight sign. For the lower bound, Subtype.val_injective composed with the representative embedding gives selector injectivity. The immutable reviewed integer-family supplier returns N, U, negativity only for nonzero real combinations, and injection of A(t)(a)=sum_j t_j U(j,a). Explicit cast and sum commutations identify the combined polynomial evaluation; the actual energy identity transfers its negativity. The negative polynomial-space witness is Polynomial.ofFn composed with A, not A alone.")),
                    Paragraph(Text(
                        "The finite counting branch uses matching exhaustive upper and embedded-family lower bounds, including cardinality zero. In the infinite branch, explicitly obtain Infinite from not Finite, choose every finite embedding with Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card at the empty set, and apply ENat.eq_top_iff_forall_ge. Each rank contributes to the complete-lattice supremum via le_sSup. Distinct quartets count negative directions; analytic multiplicities do not multiply the count.")),
                    Paragraph(Text(
                        "Canonical compilation remains pending. ActualXiIntegerCriterion owns the existing private node_large_finite and weight_ne_zero proofs; later same-core integration must expose these at their owner without copying proofs. CountableHankelNegativeIndex is still an uncompiled staged upper-bound supplier and consumes square_summable at CountableHankelNegativeWitness. This source-only repair changes neither owner, the immutable family, nor any core or partition."))
                )
            ),
            Describe.Lean(
                DescribeId.Create("actual-xi-complete-derivative-hankel-index"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex.actual_complete_derivative_hankel_index"),
                H("Supremum of finite derivative Hankel indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The second uncompiled endpoint states that the supremum of all finite actual derivative Hankel negative indices equals ENat.card QuartetRepresentative. It consumes actual_negativeIndex_eq_matrix_sup and actual_complete_negative_index, so the reconstruction and actual-energy joins are part of the final source chain. Together the endpoints retain complete actual index = quartet count = finite-matrix index supremum, in zero, finite, and infinite cases, without an RH premise or a modulus-square replacement."))
                )
            )
        )
    ));
}
