using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class TypedPortTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/TypedPortTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite typed port routing has LL, HH and LH path types. Endpoint counting gives ell=2a+c and slack=2b+c. When actual-edge incidence and capacity ledgers satisfy 2C=ell+totalDegree and totalDegree+slack=2R, the signed defect C-R equals a-b.",
        H("Typed port transport and the defect identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("route-kind"),
                DeclarationHandle.Create(Prefix + "RouteKind"),
                H("Endpoint types"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("RouteKind distinguishes LL, HH and LH paths. The labels record endpoint types and do not identify a graph embedding or a choice of local pairing."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("route-endpoints"),
                DeclarationHandle.Create(Prefix + "RouteEndpoints"),
                H("Finite endpoint ledger"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("RouteEndpoints contains a finite path type, its endpoint kind, per-path left and slack terminal counts, and their totals. LL contributes (2,0), HH contributes (0,2), and LH contributes (1,1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("capacity-ledger"),
                DeclarationHandle.Create(Prefix + "CapacityLedger"),
                H("Incidence and capacity ledger"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CapacityLedger contains the actual-edge count C, capacity sum R, total degree, and terminal totals. The two ledger equations are 2C=ell+totalDegree and totalDegree+slack=2R."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("terminal-counts"),
                DeclarationHandle.Create(Prefix + "terminal_counts"),
                H("Endpoint counting"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite endpoint ledger forces ell=2 card(LL)+card(LH) and slack=2 card(HH)+card(LH)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("defect-identity"),
                DeclarationHandle.Create(Prefix + "defect_eq_route_difference"),
                H("Typed port defect identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If the endpoint totals of the route and capacity ledgers agree, then (C:R viewed in integers) satisfies C-R=card(LL)-card(HH). The proof combines the two endpoint counts with the incidence and capacity equations.")),
                    Paragraph(Text("The statement is the generic counting core of the port-routing defect identity. It does not claim that an arbitrary finite graph admits the geometric routing hypotheses used by a rectangular-grid application."))),
                DescribeRole.Theorem))));
}
