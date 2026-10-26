using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class TengokuSubsetSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/tengoku2026subsetsums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multiset powerset records every occurrence of a subset sum.",
        H("Multiset subset sums"),
        Blocks(
            Describe.Lean(DescribeId.Create("subset-sums"), DeclarationHandle.Create(Prefix + "subsetSums"),
                H("The full occurrence spectrum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a multiset in an additive commutative monoid, sum each "
                    + "member of its multiset powerset, retaining all resulting occurrences."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("powerset-map"), DeclarationHandle.Create(Prefix + "powerset_map_eq"),
                H("Mapping and the powerset"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Mapping a function over every member of a multiset powerset "
                    + "equals the powerset of the mapped multiset, even for a noninjective function."))),
                DescribeRole.Theorem)),
        []));
}
