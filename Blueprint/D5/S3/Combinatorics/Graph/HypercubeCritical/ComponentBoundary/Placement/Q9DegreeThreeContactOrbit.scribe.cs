using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DegreeThreeContactOrbitDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DegreeThreeContactOrbit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cubic contact axis forces a simultaneous translation of both endpoints.",
        H("Coordinate translations at cubic contact axes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("translated-contact-of-three-partners"),
                DeclarationHandle.Create(Owner + "translated_contact_of_three_partners"),
                H("Forced translation of a contact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weighted exterior cancellation forces the contact to recur after both endpoints are toggled in the other two partner coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exterior-midpoint-directions"),
                DeclarationHandle.Create(Owner + "exterior_midpoint_directions"),
                H("The two directions through a contact midpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A shared midpoint with at most three candidate axes for one support has exactly two neighbors in that support by the parity of exterior degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-partner-contact-completes-square"),
                DeclarationHandle.Create(Owner + "three_partner_contact_completes_square"),
                H("Square completion from contact translations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the two incident axes both have exactly three partners, translated contacts and the midpoint rule complete a square through any two-edge walk along the incident edge."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoCenter"))
        ]));
}
