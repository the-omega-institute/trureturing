using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteLiteralBatch4Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLiteralBatch4";
    private const string Title = "Literal seven-site entry values at residue 4";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensiteliteralbatch4-literal-value-at-4"),
                DeclarationHandle.Create(Module + ".literal_value_at_4"),
                H("Observation entries at residue 4"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the field modulo 1009, at affine-line parameter 4 every Pauli observation entry equals the evaluation of its tabulated coefficient polynomial. Finite evaluation checks all pairs of Pauli indices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensiteliteralbatch4-literal-partial-at-4"),
                DeclarationHandle.Create(Module + ".literal_partial_at_4"),
                H("First partials at residue 4"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the field modulo 1009, at affine-line parameter 4 each of the five coordinate partials of each of the ten selected rows equals the evaluation of its tabulated coefficient polynomial. Square-zero evaluation supplies the literal partial values."))),
                DescribeRole.Theorem))));
}
