using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialMovingEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A truncated weighted binomial power sum has a geometric endpoint factor along every admissible slope sequence.",
        H("Moving Endpoint of a Binomial Power Sum"),
        Blocks(Describe.Lean(
            DescribeId.Create("moving-binomial-endpoint-geometric-factor"),
            DeclarationHandle.Create("D5/S3/AnalyticClosure/BinomialMovingEndpoint.moving_endpoint_sum"),
            H("Every endpoint sequence with an interior lower slope"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/byun2026unimodality")),
            Blocks(Paragraph(Text(
                "Fix a>0, a positive natural l, and 0<q<a/(1+a). For any "
                + "natural endpoint sequence r(m) with r(m)/m tending to q, "
                + "the sum of (choose(m,i) a^i)^l over 0<=i<=r(m), divided "
                + "by (choose(m,r(m)) a^r(m))^l, tends to "
                + "1/(1-(q/(a(1-q)))^l). The assumptions imply r(m)<=m "
                + "eventually; an all-m bound or an exact endpoint formula is "
                + "not required. Uniform geometric domination in the distance "
                + "from the endpoint justifies passage to the sum. This "
                + "repository formulation supplies an ingredient for the "
                + "published maximum conjecture, without selecting a maximizer."))),
            DescribeRole.Theorem))));
}
