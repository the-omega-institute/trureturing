using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.StolarskyMean;

internal sealed class SpectralDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/StolarskyMean/Spectral";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional negativity and positive subspaces determine the positive inertia of real symmetric matrices.",
        H("Positive eigenvalues and conditional negativity"), Blocks(
            Describe.Lean(DescribeId.Create("stolarsky-spectral-conditional-negativity"),
                DeclarationHandle.Create(Module + ".ConditionallyNegative"),
                H("Conditional negativity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The quadratic form is nonpositive for every real coefficient vector whose coordinates sum to zero. The dimension may be zero."))), DescribeRole.Definition),
            Theorem("numPosEig_eq_one", "One positive diagonal entry suffices", "A real symmetric conditionally negative matrix with at least one strictly positive diagonal entry has exactly one strictly positive eigenvalue. The sum-of-coordinates functional is injective on every positive definite subspace, so such a subspace has dimension at most one. If all eigenvalues were nonpositive, every diagonal entry would be nonpositive. These two bounds give the exact count."),
            Theorem("inClassA_of_conditionallyNegative", "Class A from conditional negativity", "A real symmetric matrix of nonzero size with strictly positive entries and conditional negativity belongs to class A. A diagonal entry supplies the positive direction, and the zero-sum hyperplane excludes any second positive direction."),
            Theorem("two_le_numPosEig_of_posDefOn", "Two positive directions force two positive eigenvalues", "For a real symmetric matrix, a subspace of dimension at least two on which the quadratic form is strictly positive away from zero forces at least two strictly positive eigenvalues. This is the positive-subspace dimension bound from Sylvester inertia theory."))));

    private static DocumentBlock Theorem(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("stolarsky-spectral-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
