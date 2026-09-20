using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeEndpointRecoveryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint splitting inverts the selected odd-block construction.",
        H("Recovering endpoint selections"),
        Blocks(
            Paragraph(Text("The bijection is source Proposition 3.3(i)-(ii). The exact-range statement records the additional formal recovery criterion used for part (iii).")),
            Describe.Lean(
                DescribeId.Create("crown-odd-block-merge-bijective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.crownOddBlockMerge_bijective"),
                H("Bijection at every quotient size at least three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n at least two and k at least three, the actual odd-block merge map is bijective between selections producing k augmented blocks and connected compatible partitions with k blocks. Endpoint splitting provides the inverse and proves oddness of the recovered selected components."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-sided-merge-ccp-range-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery.twoSidedMergeCCP_range_iff"),
                H("The exact range before exceptional cases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For n at least two, an augmented connected compatible partition comes from odd-block merging exactly when its endpoints are separate and neither endpoint is related to every original vertex. This identifies the two exceptional two-block partitions."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers"))
        ]));
}
