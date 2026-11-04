using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FiniteActionTrivializationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteActionTrivialization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trivializing permutation coboundaries on the original fibre.", H("Trivializing permutation coboundaries on the original fibre"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"), DeclarationHandle.Create(Owner + "finiteFibreHomeomorph"),
                H("finiteFibreHomeomorph"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A continuous permutation-valued transfer changes only the original discrete fibre coordinate; its inverse uses the transfer itself."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result-1"), DeclarationHandle.Create(Owner + "finiteFibreHomeomorph_conjugacy"),
                H("finiteFibreHomeomorph_conjugacy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transfer equation conjugates the skew step to the base step times the identity on the original fibre."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-2"), DeclarationHandle.Create(Owner + "invariant_of_unitStep"),
                H("invariant_of_unitStep"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Invariance of a map under the integer generator implies invariance under every signed integer iterate."))), DescribeRole.Theorem)),
            [  ]));
}
