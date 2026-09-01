using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Dynamics.Koopman;

internal sealed class DiscreteKoopmanOperatorDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pullback along a discrete update is a contravariant linear Koopman operator with multiplicative eigenfunctions.",
        H("Discrete Koopman Operator"),
        Blocks(
            Def("operator", "discreteKoopmanOperator", "Discrete Koopman pullback",
                "A complex observable is pulled back by composition with the state update."),
            Def("iterate", "koopmanIterate", "Finite Koopman iterate",
                "The observable is pulled back along a finite iterate of the update."),
            Def("eigenfunction", "IsKoopmanEigenfunction", "Koopman eigenfunction",
                "One pullback scales the observable by one complex eigenvalue."),
            Thm("identity", "discreteKoopmanOperator_id", "Identity update gives identity pullback",
                "Pullback along the identity state map is the identity linear operator."),
            Thm("composition", "discreteKoopmanOperator_comp", "Pullback reverses composition",
                "Composing Koopman operators reverses the order of their state updates."),
            Thm("one", "discreteKoopmanOperator_one", "Constants are preserved",
                "Every discrete Koopman pullback fixes the constant unit observable."),
            Thm("product", "discreteKoopmanOperator_mul", "Observable products are preserved",
                "Pullback is multiplicative for pointwise products of observables."),
            Thm("eigen-product", "isKoopmanEigenfunction_mul", "Eigenfunctions multiply",
                "The product of two Koopman eigenfunctions has the product eigenvalue."),
            Thm("eigen-iterate", "koopmanIterate_eigenfunction", "Eigenfunction iterates are eigenvalue powers",
                "A depth-n pullback of an eigenfunction scales it by the nth eigenvalue power.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/QuantumStates/ObservableAlgebraClosureDuality")),
        ]));

    private static DocumentBlock.Describe Def(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
