using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeInternalSizeSpectrumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact range of sizes of internal extensions follows from a finite packing problem in each residue class.",
        H("Attainable Numbers of Internal Triples"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("packing-number"),
                DeclarationHandle.Create(Module + ".packingNumber"),
                H("The packing number on a finite label set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The packing number is the maximum size of a family of three-element label sets in which each pair of distinct labels occurs in at most one member. The empty family is allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("size-spectrum"),
                DeclarationHandle.Create(Module + ".exact_size_spectrum"),
                H("The full interval of attainable sizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive row dimension and class size, the lifted pair-unique family of zero-sum triples on distinct rows covering every cross-row pair, and labellings preserving the actual residue modulo three. Add unordered triples of three distinct points within rows, preserving pair uniqueness and normalized potential dimension one more than the row dimension.")),
                    Paragraph(Text("The lower endpoint is the number of Latin cells across all rows. The upper endpoint adds the packing number times the number of row and residue-class pairs. Every integer between the endpoints occurs.")),
                    Paragraph(Text("The unordered blocks split into the Latin cells and disjoint transported packing families. For the upper bound, each class contributes at most the packing number. For attainability, put a maximum pack in each class and choose an arbitrary subset of the union of these packing blocks. Each class remains a valid partial Steiner system, so the realization theorem preserves the required dimension."))),
                DescribeRole.Theorem))));
}
