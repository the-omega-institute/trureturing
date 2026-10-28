using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfContractionGramsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfContractionGrams";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact four Gram matrices",
        Blocks(
            Entry("grams_posSemidef", "Exact integer Gram positivity",
                "All four displayed eight by eight real integer matrices M00,M01,M10,M11 are PSD. Exact rational LDL factorizations reconstruct every entry. M00 includes its zero first row and column. The fixed coefficient dimension is independent of the physical matrix dimension."))));
    private static DocumentBlock Entry(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("hsfcontractiongrams-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
