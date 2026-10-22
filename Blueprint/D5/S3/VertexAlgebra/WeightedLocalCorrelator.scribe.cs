using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class WeightedLocalCorrelatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/WeightedLocalCorrelator.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair-dependent locality gives a common array with finite signed total-exponent slices.",
        H("Weighted Local Correlators on Arbitrary Inputs"),
        Blocks(
            Paragraph(Text("Let V be a complex vector space, v any vector, P any linear "
                + "endomorphism, and A_i actual VertexOperator maps indexed by Fin N. "
                + "For each labelled pair i<j choose its own natural locality order k_ij, "
                + "so the k_ij-th coefficient difference annihilates the operator "
                + "commutator of A_i and A_j. The labels and orientations stay fixed. "
                + "Put Q=product over i<j of (z_i-z_j)^k_ij. For a labelled list l, "
                + "F_l(e) is P applied to the word of modes A_i[-e_i-1] acting on v, "
                + "where every exponent e_i is an integer. Multiplication by Q means "
                + "the existing finite polynomial convolution on coefficient distributions.")),
            Describe.Lean(
                DescribeId.Create("common-cleared-fields"),
                DeclarationHandle.Create(Prefix + "common_cleared_fields"),
                H("One cleared array, simultaneous lower bounds, and finite Laurent slices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("Suppose l has no repeated labels and contains every "
                        + "label. Then Q F_l equals Q F_r for every permutation r of l. "
                        + "To prove this, factor out the clearing polynomial of an adjacent "
                        + "pair. Locality kills the contextual commutator, including its "
                        + "arbitrary prefix and suffix. Induction on list permutations "
                        + "extends these adjacent exchanges to every ordering without "
                        + "cancelling Q in the full distribution space.")),
                    Paragraph(Text("For each label i, let b_i be the Hahn order of the "
                        + "actual series A_i(v). Move i to the far right. Its mode then "
                        + "acts directly on v, and pointwise lower truncation makes the "
                        + "coefficient zero when e_i<b_i. Every clearing difference "
                        + "preserves this lower bound. Permutation invariance transfers "
                        + "the bound back to the common array, so all coordinate bounds "
                        + "hold simultaneously. This uses the truncation of A_i on this "
                        + "particular v, with no bound uniform over all vectors.")),
                    Paragraph(Text("For any fixed integer total t, a nonzero coefficient "
                        + "has sum e_i=t and b_i<=e_i<=t-sum b_j+b_i. It therefore lies "
                        + "in a finite integer box. The conclusion is finite support on "
                        + "each total-exponent slice; it does not assert finite support "
                        + "of the entire array. Negative totals and negative coordinate "
                        + "bounds are included. When N is zero the exponent space has "
                        + "one element, the word is the identity and Q is one. No vacuum, "
                        + "creation law, energy grading, grade selector or uniform "
                        + "locality order is required.")),
                    Paragraph(Text("The lattice half-Fock specialization in "
                        + "actual_three_field_numerator uses N=3, V=ActualTensor D hu, "
                        + "A=threeFields D hu i a b gamma delta, v=x, P=1, "
                        + "orders=threeOrders D a b K and l=[0,1,2]. The fields are the "
                        + "current J and the two source slices A and B. Their three "
                        + "orders are vectorFrequencyBound D a+1, "
                        + "vectorFrequencyBound D b+1 and K. The locality premise is "
                        + "supplied by the two current/source identities and source/slice "
                        + "locality. The common array is exactly actualNumerator on the "
                        + "actual vector x; the permutation equality is reversed to "
                        + "identify each ordered cleared word with that array. The "
                        + "lower bounds and fixed-total finiteness clauses then apply "
                        + "directly, with arbitrary x and signed exponents.")),
                    Paragraph(Text("These bounds allow finite homogeneous Laurent windows "
                        + "of the same numerator. They do not identify complete actual "
                        + "nested Q residues with finite Taylor readouts. The three "
                        + "equalities in sameNumeratorCollisionBridge, for the fused "
                        + "residue and the two differently ordered nested residues, "
                        + "remain additional obligations. Supported extraction, outer "
                        + "completion and collision balance alone do not supply them. "
                        + "No Monster carrier identification or string-theory "
                        + "reconstruction follows from this common-array theorem."))),
                DescribeRole.Theorem))));
}
