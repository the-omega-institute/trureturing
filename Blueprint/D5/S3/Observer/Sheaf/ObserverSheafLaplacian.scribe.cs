using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Sheaf;

internal sealed class ObserverSheafLaplacianDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Sheaf/ObserverSheafLaplacian.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite observer coboundary yields a Hermitian Laplacian and zero Dirichlet energy exactly characterizes compatibility.",
        H("Finite Observer Sheaf Laplacian"),
        Blocks(
            Def("compatible", "MatrixCompatible", "Matrix compatibility",
                "A coordinate observer family is compatible when the coboundary matrix annihilates it."),
            Def("laplacian", "observerSheafLaplacian", "Observer sheaf Laplacian",
                "The degree-zero finite Laplacian is the adjoint coboundary multiplied by the coboundary."),
            Def("energy", "observerDirichletEnergy", "Observer Dirichlet energy",
                "The compatibility defect is measured by the sum of squared edge-defect norms."),
            Def("harmonic", "IsObserverHarmonic", "Observer harmonicity",
                "A local observer family is harmonic when the degree-zero Laplacian annihilates it."),
            Thm("hermitian", "observerSheafLaplacian_isHermitian", "The Laplacian is Hermitian",
                "Every adjoint-times-original finite coboundary matrix is Hermitian."),
            Thm("nonnegative", "observerDirichletEnergy_nonneg", "Dirichlet energy is nonnegative",
                "Every edge contributes a squared norm and the finite sum is nonnegative."),
            Thm("zero", "observerDirichletEnergy_eq_zero_iff", "Zero energy is compatibility",
                "The total edge-defect energy vanishes exactly when the coboundary annihilates the section."),
            Thm("factor", "observerSheafLaplacian_mulVec", "Laplacian action factors through defects",
                "Applying the Laplacian means first taking the coboundary and then applying its conjugate transpose."),
            Thm("harmonic", "matrixCompatible_implies_harmonic", "Compatible sections are harmonic",
                "Every zero-defect observer family lies in the kernel of the finite sheaf Laplacian."),
            Thm("converse", "harmonic_implies_matrixCompatible_of_adjoint_injective", "Injective adjoint gives the converse",
                "If the adjoint coboundary is injective, harmonicity forces the original edge defects to vanish.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Sheaf/FiniteObserverSheaf")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
