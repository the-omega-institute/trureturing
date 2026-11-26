using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PuncturedCircuitSplitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PuncturedCircuitSplit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independent coordinates and the weighted pairs.",
        H("Splitting the Punctured Residue Equations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("punctured-forms-equiv"),
                DeclarationHandle.Create(Module + ".punctured_forms_equiv"),
                H("Product coordinates for the punctured form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A coordinate containing both weight directions is killed by the total size and both "
                    + "weights. A coordinate containing neither is killed by the total size alone. Subsets "
                    + "containing exactly one direction give pairs indexed by their common deletion. The "
                    + "omitted coefficient is the first coordinate of one particular pair."))),
                DescribeRole.Theorem))));
}
