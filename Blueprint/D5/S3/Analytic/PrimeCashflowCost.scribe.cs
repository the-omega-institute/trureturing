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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/PrimeCashflowCost",
            "The cumulative logarithmic length of a signed prime-event stream strictly increases at every nonzero event."),
        H("Strict Growth of Prime Cashflow Cost"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("event-length-is-logarithmic-prime-weighted-variation"),
                H("Event length is logarithmic prime-weighted variation"),
                LeanDefinition("D5/S3/Analytic/PrimeCashflowCost.eventLength"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "An event is a finitely supported integer-valued function on the primes. " +
                    "Its length sums the absolute real value of each signed coordinate, " +
                    "weighted by the logarithm of that prime."))),
                Disp(Seq(
                    Operatorname, Grp(F.Id("eventLength")), Open, F.Id("u"), Close, Eq,
                    Sum, Underscore, Grp(
                        F.Id("p"), InMacro, Operatorname, Grp(F.Id("support")),
                        Open, F.Id("u"), Close),
                    Vert, Sp, F.Id("u"), Underscore, Grp(F.Id("p")), Vert, Sp,
                    Operatorname, Grp(F.Id("log")), Open, F.Id("p"), Close))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("cashflow-cost-is-cumulative-event-length"),
                H("Cashflow cost is cumulative event length"),
                LeanDefinition("D5/S3/Analytic/PrimeCashflowCost.cashflowCost"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The cost at time t is the finite sum of event lengths at all " +
                    "natural-number times strictly before t."))),
                Disp(Seq(
                    Operatorname, Grp(F.Id("cashflowCost")), Open,
                    F.Id("events"), Comma, F.Id("t"), Close, Eq,
                    Sum, Underscore, Grp(F.Id("tau"), Lt, F.Id("t")),
                    Operatorname, Grp(F.Id("eventLength")), Open,
                    F.Id("events"), Open, F.Id("tau"), Close, Close))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("every-nonzero-event-has-positive-length"),
                H("Every nonzero event has positive length"),
                LeanTheorem("D5/S3/Analytic/PrimeCashflowCost.eventLength_pos"),
                Disp(Seq(
                    F.Id("u"), Neq, D(0), Sp, Rightarrow, Sp, D(0), Lt,
                    Operatorname, Grp(F.Id("eventLength")), Open, F.Id("u"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A nonzero finitely supported event has a nonzero coordinate at some " +
                    "prime. Its absolute value is positive, and the logarithm of every prime " +
                    "is positive, so that coordinate makes the finite sum positive.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("cashflow-cost-strictly-increases-at-a-nonzero-event"),
                H("Cashflow cost strictly increases at a nonzero event"),
                LeanTheorem(
                    "D5/S3/Analytic/PrimeCashflowCost.cashflow_cost_strict_at_event"),
                Disp(Seq(
                    F.Id("events"), Open, F.Id("t"), Close, Neq, D(0), Sp,
                    Rightarrow, Sp,
                    Operatorname, Grp(F.Id("cashflowCost")), Open,
                    F.Id("events"), Comma, F.Id("t"), Close, Lt,
                    Operatorname, Grp(F.Id("cashflowCost")), Open,
                    F.Id("events"), Comma, F.Id("t"), Plus, D(1), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Advancing from t to t+1 appends exactly the length of the event at t to " +
                    "the cumulative cost. The positivity theorem therefore gives strict " +
                    "growth whenever that event is nonzero.")))
            ))));
}
