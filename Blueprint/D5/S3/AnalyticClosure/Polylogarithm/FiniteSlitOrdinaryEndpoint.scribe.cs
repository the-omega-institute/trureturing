using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class FiniteSlitOrdinaryEndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary inverse coefficients are absolutely summable, with the actual branch endpoint as their total.",
        H("FiniteSlitOrdinaryEndpoint"), Blocks(
            Describe.Lean(DescribeId.Create("signed-prefix-endpoint"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Absolute summability with the signed finite prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("For every positive head, every positive-entry tail and positive ell, the original ordinary inverse coefficients are absolutely summable and have HasSum equal to endpoint. This endpoint is zeta(head,tail) to power minus ell for admissible head>1, and zero for head=1. The actual CompositionBanks endpoint theorem supplies both cases on the same source branch; the removable origin is preserved by FiniteSlitCompositionMoments.reciprocal.")),
                    Paragraph(Text("Choose N beyond the negative coefficient threshold. The shifted coefficients q(n)=-a(n+N) are nonnegative. For every finite window, their radially weighted partial sum is bounded by the full polynomial prefix minus the actual reciprocal. Passing to the radial endpoint gives a single finite bound for every unweighted partial sum. This proves summability of the shifted tail; adjoining the signed finite prefix gives absolute summability of the original sequence. Abel's theorem then identifies its total with the actual endpoint.")),
                    Paragraph(Text("Every sufficiently late partial sum through n strictly exceeds endpoint, because its omitted summable tail contains strictly negative coefficients. The proof retains all early coefficients. This supplies the exact first-partial-sum consequence; the remaining formal smoothing interfaces, positive radial lower bound for second sums, all fixed j and the strict admissible binomial excess are not claimed here. The full original Xu--Zhao problem remains open."))),
                DescribeRole.Theorem))));
}
