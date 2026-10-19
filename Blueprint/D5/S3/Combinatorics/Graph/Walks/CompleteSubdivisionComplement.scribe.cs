using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CompleteSubdivisionComplementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionComplement.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/farhan2026multiset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complementing all landmarks",
        H("Complementing all landmarks"),
        Blocks(
            Paragraph(Text("The full-vertex distance histogram is independent of the actual graph edge. Each selected bin plus its complementary bin equals that full bin. Hence a pair of edges has equal profiles for a landmark set exactly when it has equal profiles for its complement. Complementation flips every selection-matrix entry, including the diagonal.")),
            Describe.Lean(DescribeId.Create("complete-subdivision-complement-full-selected-degree"),
                DeclarationHandle.Create(Prefix + "full_selectedDegree"),
                H("full selectedDegree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("With all vertices selected, every original is incident with exactly n-1 selected midpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-complement-full-bins-equal"),
                DeclarationHandle.Create(Prefix + "full_bins_equal"),
                H("full bins equal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For the full vertex set, every actual graph edge has the same four distance-bin counts."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-complement-bin-add-compl"),
                DeclarationHandle.Create(Prefix + "bin_add_compl"),
                H("bin add compl"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A selected bin and its full-vertex complement sum to the corresponding full bin."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-complement-profile-compl-iff"),
                DeclarationHandle.Create(Prefix + "profile_compl_iff"),
                H("profile compl iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Equal profiles of actual graph edges are preserved and reflected by complementing all landmarks."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-complement-resolves-compl-iff"),
                DeclarationHandle.Create(Prefix + "resolves_compl_iff"),
                H("resolves compl iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A full-vertex landmark subset resolves exactly when its complement resolves."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-complement-selection-compl"),
                DeclarationHandle.Create(Prefix + "selection_compl"),
                H("selection compl"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Complementing the landmark set flips every matrix entry, including the diagonal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-complement-selection-row-compl"),
                DeclarationHandle.Create(Prefix + "selection_row_compl"),
                H("selection row compl"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Complementary row sums add to n."))), DescribeRole.Theorem))));
}
