using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.DendriteObstruction;

internal sealed class DendriteObstructionArcGeometryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete compact hyperspace geometry for the persistence argument.",
        H("DendriteObstruction - Arc geometry"), Blocks(
        Describe.Lean(DescribeId.Create("continuous-compact-diam"),
            DeclarationHandle.Create(Owner + "continuous_compact_diam"),
            H("Continuous diameter"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every metric space X, diameter is a continuous real-valued function on the Vietoris space of nonempty compact subsets of X. The continuous hyperspace product K times K and the upper Vietoris conditions for the closed and open distance sublevel sets prove the two semicontinuity directions. Compactness makes the maximum pairwise distance attained, so the strict sublevel condition controls the actual diameter."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("compact-continua-ge"),
            DeclarationHandle.Create(Owner + "compact_continua_ge"),
            H("Compact family of large subcontinua"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a compact metric X and any real a, the nonempty compact connected subsets K with diameter at least a form a compact subset of NonemptyCompacts X. The connected members form a closed set: a disconnected compact limit admits a disjoint closed separation and therefore disjoint open neighborhoods, and the corresponding Vietoris neighborhood excludes every connected compactum. Intersecting this closed family with the closed diameter superlevel set gives the claimed compactness. These are purely static hyperspace facts consumed by CompactHistories; no recurrence or persistence is assumed."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("compact-continua-ge-in"),
            DeclarationHandle.Create(Owner + "compact_continua_ge_in"),
            H("Macroscopic continua in a closed set"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a compact metric X, real a and closed subset Y, the family of nonempty compact connected K contained in Y with diameter at least a is compact. Closed containment in the actual Vietoris hyperspace is intersected with compact_continua_ge. This is the family used to retain a macroscopic continuum under descending intersections of invariant compacta."))), DescribeRole.Theorem))));
}
