using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.DendriteObstruction;

internal sealed class DendriteObstructionStandardDendroidDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Standard dendroid geometry from arcwise connectedness and hereditary unicoherence.",
        H("DendriteObstruction - StandardDendroid"), Blocks(
        Describe.Lean(DescribeId.Create("arc-convex"),
            DeclarationHandle.Create(Owner + "arc_convex"),
            H("Subcontinua contain their joining arcs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("On a compact metric carrier, StandardDendroid states actual arcwise connectedness and hereditary unicoherence: the intersection of any two compact connected subsets is preconnected, including the empty case. The definition contains no dynamical, uniform packing or co-connected-opening field. Arcwise connectedness uses actual continuous injective parameterizations of the closed unit interval with prescribed distinct endpoints.")),
                Paragraph(Text("A compact connected subset containing the two endpoints of any embedded arc contains the whole arc. Hereditary unicoherence makes its intersection with the arc preconnected. Pulling back through the compact interval embedding gives a preconnected subset of the real interval containing both endpoints, hence the entire interval. EmbeddedArc.between_subset proves the order statement for arbitrary two parameters."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("static-arc-hull"),
            DeclarationHandle.Create(Owner + "staticArcHull"),
            H("The accepted history hull premise"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The standard arcwise connected and hereditarily unicoherent geometry supplies StaticArcHull: choose an arc between distinct endpoints and apply arc_convex to every compact connected set containing the endpoints. This is a direct consumed interface to CompactHistories, with no additional geometric assumption."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("arc-unique"),
            DeclarationHandle.Create(Owner + "arc_unique"),
            H("Uniqueness of the arc carrier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Any two embedded arcs with the same ordered endpoints have equal carriers, by applying arc_convex in both directions. This carrier uniqueness is consumed in the no-circle proof. It does not assert uniqueness of parameterization."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("no-circle"),
            DeclarationHandle.Create(Owner + "no_circle"),
            H("No embedded circle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every continuous map from AddCircle (1 : Real) to a standard dendroid fails to be injective. Under a hypothetical injection, the two oppositely parameterized semicircles give two embedded arcs with the same endpoints. Carrier uniqueness forces the first semicircle quarter point into the second semicircle, contradicting the actual AddCircle quotient coordinates."))), DescribeRole.Theorem))));
}
