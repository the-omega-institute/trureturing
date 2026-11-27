using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRAbsoluteValueHSDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hilbert–Schmidt estimates for operator absolute values and adjoints.",
        H("Absolute values in the Hilbert–Schmidt ideal"),
        Blocks(
            Paragraph(Text("The comparison of normalized covariance roots uses a Hilbert–Schmidt absolute-value bound. "
                + "It applies to the square-root perturbations in Eq. (71) of Satishchandran and Sorce.")),
            Entry("absolute-value", "opAbs", "Operator absolute value",
                "Take the positive square root of the adjoint times the operator.", DescribeRole.Definition),
            Entry("self-adjoint-contraction", "opAbs_sub_selfAdjoint", "Self-adjoint contraction",
                "For bounded self-adjoint operators with Hilbert–Schmidt difference, the difference of their "
                + "absolute values is Hilbert–Schmidt with squared norm at most that of the original difference. "
                + "In finite dimension, expand in a mixed pair of orthonormal eigenbases and apply the scalar "
                + "absolute-value contraction to each coefficient. The finite compressions converge strongly. "
                + "Uniform polynomial approximation preserves this convergence under absolute value, so each "
                + "finite column sum passes to the limit under the same bound."),
            Entry("dilation", "dilation", "Two-copy dilation",
                "On the Hilbert sum of two copies, the dilation applies the adjoint to the second coordinate "
                + "and the original operator to the first coordinate, giving the two output coordinates in that order.",
                DescribeRole.Definition),
            Entry("dilation-self-adjoint", "dilation_isSelfAdjoint", "Self-adjoint dilation",
                "The two off-diagonal blocks are adjoints, so the dilation is self-adjoint."),
            Entry("dilation-absolute-value", "opAbs_dilation_apply", "Absolute value of the dilation",
                "The two diagonal entries are the absolute values of the operator and its adjoint. They are "
                + "positive and their block diagonal square is the square of the dilation."),
            Entry("symmetric-estimate", "opAbs_sub_symmetric", "Symmetric squared estimate",
                "For two bounded operators with Hilbert–Schmidt difference, both absolute-value differences, "
                + "for the operators and for their adjoints, are Hilbert–Schmidt. The sum of their squared norms "
                + "is at most twice the squared norm of the original difference. Apply the self-adjoint contraction "
                + "to the dilations and split the column sums over the two copies."),
            Entry("general-estimate", "opAbs_sub", "Squared estimate for arbitrary operators",
                "The squared Hilbert–Schmidt norm of the difference of absolute values is at most twice that "
                + "of the difference of the operators, by nonnegativity of the adjoint contribution."),
            Entry("sharpness", "opAbs_sub_symmetric_sharp", "Equality on the complex line",
                "The identity and zero operators on the complex line have input squared norm one "
                + "and joint output squared norm two. Thus the factor in the symmetric estimate is attained."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
