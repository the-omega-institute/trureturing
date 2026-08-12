using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PrimeCashflowCostDocument : IScribeDocumentDefinition
{
    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cumulative logarithmic length of a signed prime-event stream strictly increases at every nonzero event.",
        H("Strict Growth of Prime Cashflow Cost"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("event-length-is-logarithmic-prime-weighted-variation"),
                DeclarationHandle.Create("D5/S3/Analytic/PrimeCashflowCost.eventLength"),
                H("Event length is logarithmic prime-weighted variation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An event is a finitely supported integer-valued function on the primes. " +
                    "Its length sums the absolute real value of each signed coordinate, " +
                    "weighted by the logarithm of that prime."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("cashflow-cost-is-cumulative-event-length"),
                DeclarationHandle.Create("D5/S3/Analytic/PrimeCashflowCost.cashflowCost"),
                H("Cashflow cost is cumulative event length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cost at time t is the finite sum of event lengths at all " +
                    "natural-number times strictly before t."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("every-nonzero-event-has-positive-length"),
                DeclarationHandle.Create("D5/S3/Analytic/PrimeCashflowCost.eventLength_pos"),
                H("Every nonzero event has positive length"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("u"), Neq, D(0), Sp, Rightarrow, Sp, D(0), Lt,
                    Operatorname, Grp(F.Id("eventLength")), Open, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero finitely supported event has a nonzero coordinate at some " +
                    "prime. Its absolute value is positive, and the logarithm of every prime " +
                    "is positive, so that coordinate makes the finite sum positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cashflow-cost-strictly-increases-at-a-nonzero-event"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/PrimeCashflowCost.cashflow_cost_strict_at_event"),
                H("Cashflow cost strictly increases at a nonzero event"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("events"), Open, F.Id("t"), Close, Neq, D(0), Sp,
                    Rightarrow, Sp,
                    Operatorname, Grp(F.Id("cashflowCost")), Open,
                    F.Id("events"), Comma, F.Id("t"), Close, Lt,
                    Operatorname, Grp(F.Id("cashflowCost")), Open,
                    F.Id("events"), Comma, F.Id("t"), Plus, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Advancing from t to t+1 appends exactly the length of the event at t to " +
                    "the cumulative cost. The positivity theorem therefore gives strict " +
                    "growth whenever that event is nonzero."))),
                DescribeRole.Theorem))));
}
