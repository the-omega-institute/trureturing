using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class UniformGradedLocalCorrelatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/UniformGradedLocalCorrelator.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual graded local fields have a common finite homogeneous numerator.",
        H("Uniform Graded Local Correlators"),
        Blocks(
            Paragraph(Text("Let V be a complex vector space, Omega a vacuum, and "
                + "A_i actual VertexOperator maps with nonnegative integer weights h_i. "
                + "An energy endomorphism H annihilates Omega and satisfies "
                + "[H,A_i[-e-1]]=(h_i+e) A_i[-e-1] at every integer exponent. "
                + "Creation means A_i[n] Omega=0 for n at least zero. "
                + "The output selector P_d is an idempotent endomorphism satisfying "
                + "H P_d=P_d H=d P_d and fixing every vector of energy d. "
                + "The uniform order k is supplied by actual "
                + "pairwise locality of the operator commutators, independently of "
                + "the state on which they act.")),
            Describe.Lean(
                DescribeId.Create("uniform-graded-local-correlator"),
                DeclarationHandle.Create(Prefix + "uniform_graded_local_correlator"),
                H("A finite numerator for every insertion length and every ordering"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("For any list containing each label exactly once, "
                        + "the coefficient at exponent e is P_d applied to the successive "
                        + "actual modes A_i[-e_i-1] acting on Omega. Keep the labels fixed "
                        + "and put Q=product over i<j of (z_i-z_j)^k. Multiplication "
                        + "by Q is finite convolution in the full coefficient-distribution "
                        + "space. Pairwise locality clears adjacent exchanges, so Q times "
                        + "the coefficient distribution is the same for every permutation. "
                        + "No cancellation of Q in that distribution space is used.")),
                    Paragraph(Text("Moving label i to the rightmost position and applying "
                        + "creation eliminates every negative exponent in coordinate i. "
                        + "Each polynomial difference preserves this property. Energy "
                        + "covariance gives total exponent d minus the sum of the weights; "
                        + "the clearing factors raise it to D=d-sum h_i+k times the "
                        + "number of labelled pairs. Each nonzero numerator coefficient "
                        + "therefore has a nonnegative exponent vector of total degree D. "
                        + "Every coordinate is bounded by D, giving a finite box. "
                        + "The numerator is constructed as a Finsupp on natural exponent "
                        + "vectors with coefficients in V, rather than assuming its support.")),
                    Paragraph(Text("If every coefficient of one ordering lies in a fixed "
                        + "complex submodule W, each numerator coefficient lies in W: "
                        + "it is the finite sum of scalar multiples prescribed by Q. "
                        + "When D is negative the numerator is zero. For no insertions "
                        + "the word is the identity and Q is one; for one insertion "
                        + "there are no pair factors. Zero weights and locality order "
                        + "zero are included without exceptions.")),
                    Paragraph(Text("This statement applies to any actual family with these "
                        + "laws. Its application to the moonshine VOA requires that "
                        + "carrier, its field maps, energy and output projections. "
                        + "Rational collision expansions, associativity with spectators, "
                        + "Casimir expressions and the identification of Monster invariants "
                        + "are additional mathematical obligations."))),
                DescribeRole.Theorem))));
}
