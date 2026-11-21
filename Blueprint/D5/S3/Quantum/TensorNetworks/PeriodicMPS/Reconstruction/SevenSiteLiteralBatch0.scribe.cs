using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteLiteralBatch0Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLiteralBatch0";
    private const string Title = "Literal seven-site entry values at residue 0";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensiteliteralbatch0-literal-value-at-0"),
                DeclarationHandle.Create(Module + ".literal_value_at_0"),
                H("Observation entries at residue 0"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the field modulo 1009, at affine-line parameter 0 every Pauli observation entry equals the evaluation of its tabulated coefficient polynomial. Finite evaluation checks all pairs of Pauli indices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensiteliteralbatch0-literal-partial-at-0"),
                DeclarationHandle.Create(Module + ".literal_partial_at_0"),
                H("First partials at residue 0"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the field modulo 1009, at affine-line parameter 0 each of the five coordinate partials of each of the ten selected rows equals the evaluation of its tabulated coefficient polynomial. Square-zero evaluation supplies the literal partial values."))),
                DescribeRole.Theorem))));
}
