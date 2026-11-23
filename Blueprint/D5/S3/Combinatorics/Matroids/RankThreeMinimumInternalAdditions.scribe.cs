using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeMinimumInternalAdditionsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fix the mixed lifted-line triples of a ternary row space with cyclic row size three times r.",
        H("The Least Internal Additions for an Extra Ternary Dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimum-internal-additions-lower-bound"),
                DeclarationHandle.Create(Module + ".internal_additions_lower_bound"),
                H("The extra dimension forces a minimum number of additions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the internal residue test permits the extra dimension, the total number of rows in basis coordinates is multiplied by three and each resulting fiber has size r. "
                    + "Apply the mixed-pair lower bound to the enlarged triple family. Subtracting the exact number of original mixed triples leaves at least r squared internal triples per original row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-internal-additions-attainment"),
                DeclarationHandle.Create(Module + ".exists_internal_additions_attaining"),
                H("Transversals on the residue fibers meet the bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Index each of the three residue classes by a cyclic coordinate of size r. In each row, choose one point from each class using two free cyclic coordinates and their negative sum. "
                    + "Every different-residue pair in a row then occurs exactly once. Both internal residue tests hold, while the original mixed triples are retained. "
                    + "There are exactly r squared additions per row. The indexing uses the residue fibers as sets and applies also when the cyclic row size is divisible by nine."))),
                DescribeRole.Theorem))));
}
