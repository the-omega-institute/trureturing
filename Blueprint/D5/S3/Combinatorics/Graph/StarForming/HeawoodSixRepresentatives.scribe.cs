using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodSixRepresentativesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/StarForming/HeawoodSixRepresentatives.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every connected binary Heawood lift is represented by six explicit flag signings.",
        H("Six representatives of connected Heawood double covers"), Blocks(
        Describe.Lean(DescribeId.Create("exists-representative"),
            DeclarationHandle.Create(Owner + "exists_representative"),
            H("Connected signings have one of six representatives"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Each connected lift of the fixed Heawood flag graph, given by an arbitrary binary signing, is isomorphic to at least one of the six displayed signings.")),
                Paragraph(Text("Connectivity makes the flag gain nonzero. Its trace is zero by incidence. The matrix classification puts the gain into one of six conjugacy forms. Each listed signing realizes its corresponding form by a sum of flag outer products. The transport of conjugate gains gives the graph isomorphism."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("exists-voltage-representative"),
            DeclarationHandle.Create(Owner + "exists_voltage_representative"),
            H("Connected edge-voltage lifts have the same representatives"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("An arbitrary binary edge voltage on the fixed Heawood graph gives the same classification when its two-sheet graph is connected. The existing voltage-to-signing graph isomorphism carries connectedness and composes with the classification."))),
            DescribeRole.Theorem),
        Paragraph(Text("The conclusion covers the connected graphs by six representatives. It makes no claim of pairwise nonisomorphism under all graph isomorphisms. Source: Heawood double-cover gain. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108")))));
}
