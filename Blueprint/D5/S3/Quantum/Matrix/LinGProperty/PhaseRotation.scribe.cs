using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class PhaseRotationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit complex phases normalize the off-diagonal trace without changing the spectral problem.",
        H("Phase normalization"), Blocks(
        Item("block_posSemidef_phase", "Block positivity under a unit phase",
            "For every dimension and positive semidefinite block matrix with diagonal blocks A,B and off-diagonal blocks X,X adjoint, "
            + "every complex z of modulus one gives another positive semidefinite block matrix with off-diagonal blocks zX and its adjoint. "
            + "Conjugation by the block diagonal matrix diag(zI,I) gives this matrix exactly and leaves both diagonal blocks fixed."),
        Item("singularValuesSorted_phase", "Unit phases preserve singular values",
            "For every finite complex square matrix X, every complex z of modulus one and every decreasing singular-value index j, "
            + "the j-th singular values of zX and X coincide. This is the existing unitary invariance theorem applied to zI."),
        Item("exists_trace_phase", "Real nonnegative trace normalization",
            "For every finite complex square matrix X there is a complex z of modulus one such that tr(zX)=|tr(X)|. "
            + "The scalar polar-phase existence theorem includes zero trace. Trace linearity gives the matrix statement. "
            + "Together the three statements let the arithmetic singular-value argument use a real nonnegative trace without changing positivity or singular values."))));

    private static DocumentBlock Item(string name, string title, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
