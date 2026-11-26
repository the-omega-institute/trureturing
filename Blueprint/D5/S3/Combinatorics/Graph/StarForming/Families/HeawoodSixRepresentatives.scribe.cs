using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class HeawoodSixRepresentativesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");

    private const string Owner = "D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodSixRepresentatives.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every connected binary Heawood lift is represented by six explicit flag signings.",
        H("Six representatives of connected Heawood double covers"), Blocks(
        Describe.Lean(DescribeId.Create("exists-representative"),
            DeclarationHandle.Create(Owner + "exists_representative"),
            H("Connected signings have one of six representatives"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("Each connected lift of the fixed Heawood flag graph, given by an arbitrary binary signing, is isomorphic to at least one of the six specified signings.")),
                Paragraph(Text("Connectivity makes the flag gain nonzero. Its trace is zero by incidence. The matrix classification puts the gain into one of six conjugacy forms. Each listed signing realizes its corresponding form by a sum of flag outer products. The transport of conjugate gains gives the graph isomorphism."))),
            DescribeRole.Theorem),
        Paragraph(Text("Pairwise nonisomorphism of the six graphs under arbitrary graph isomorphisms is a separate question. Source: Heawood double-cover gain. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108")))));
}
