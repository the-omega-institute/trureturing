using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuRankOneEndpointCliffordDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed endpoint acts diagonally on two-mode Pauli words.",
        H("Pauli eigenvectors of the Wu endpoint"),
        Blocks(
            Paragraph(Text("The sign in the entrywise formula makes the exponent depend on the Clifford degree of a word. The sixteen eigenvalue identities follow from the entry formula and the fixed Pauli matrix convention.")),
            Describe.Lean(DescribeId.Create("pauli-eigenvalue"), DeclarationHandle.Create(Owner + "A1_pauliWord"),
                H("Pauli eigenvalue formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each two-mode Pauli word of Clifford degree d is an eigenvector of the actual signed map with eigenvalue λᵈ."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("clifford-degree"), DeclarationHandle.Create(Owner + "cliffordDegree"),
                H("The degree of a Pauli word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The degree records the exponent for each of the sixteen Pauli words."))), DescribeRole.Definition))));
}
