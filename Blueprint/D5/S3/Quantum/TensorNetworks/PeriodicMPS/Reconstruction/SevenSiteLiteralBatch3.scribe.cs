using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteLiteralBatch3Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLiteralBatch3";
    private const string Title = "Literal seven-site entry values at residue 3";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensiteliteralbatch3-literal-value-at-3"),
                DeclarationHandle.Create(Module + ".literal_value_at_3"),
                H("Observation entries at residue 3"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the field modulo 1009, at affine-line parameter 3 every Pauli observation entry equals the evaluation of its tabulated coefficient polynomial. Finite evaluation checks all pairs of Pauli indices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensiteliteralbatch3-literal-partial-at-3"),
                DeclarationHandle.Create(Module + ".literal_partial_at_3"),
                H("First partials at residue 3"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the field modulo 1009, at affine-line parameter 3 each of the five coordinate partials of each of the ten selected rows equals the evaluation of its tabulated coefficient polynomial. Square-zero evaluation supplies the literal partial values."))),
                DescribeRole.Theorem))));
}
