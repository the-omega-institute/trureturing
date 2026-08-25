using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class ItineraryFirstDifferencePowerLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical complete itineraries determine the discounted discrete prediction distance.",
        H("Itinerary First Difference Power Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("itinerary-first-difference-determines-discounted-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometryLaws/ItineraryFirstDifferencePowerLaw."
                        + "itinerary_first_difference_power_law"),
                H("Itinerary first difference determines discounted distance"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Future indistinguishability is the canonical equality of complete "
                            + "readout itineraries. The distance is the existing discounted "
                            + "supremum using the discrete output discrepancy.")),
                    Paragraph(Text(
                        "Equal complete itineraries make every discrepancy term zero. If the "
                            + "states are distinguishable, the least separating time gives the "
                            + "largest nonzero discounted term.")),
                    Paragraph(Text(
                        "Both source clauses remain public: zero distance for canonically "
                            + "future-indistinguishable states and the exact first-difference "
                            + "power law for distinguishable states."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Apply(Formula name, params Formula[] arguments)
    {
        var content = new List<Formula> { name, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula tau = F.Id("tau");
        Formula readout = F.Id("q");
        Formula outputDistance = F.Id("discreteOutputDistance");
        Formula gamma = F.Id("gamma");
        Formula left = F.Id("y");
        Formula right = Seq(F.Id("y"), Apos);
        Formula time = F.Id("k");
        Formula relation = Apply("FutureIndistinguishable", tau, readout, left, right);
        Formula distance = Apply(
            "discountedPredictionDistance", tau, readout, outputDistance, gamma, left, right);
        Formula iterateLeft = Apply("iterate", tau, time, left);
        Formula iterateRight = Apply("iterate", tau, time, right);
        Formula readoutLeft = Apply(readout, iterateLeft);
        Formula readoutRight = Apply(readout, iterateRight);
        Formula separating = Seq(
            Exists, Sp, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            readoutLeft, Sp, Neq, Sp, readoutRight);
        Formula firstDifference = Seq(
            Min, OpenBrace, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp, Mid, Sp,
            readoutLeft, Sp, Neq, Sp, readoutRight, CloseBrace);
        Formula power = Seq(gamma, Caret, Grp(firstDifference));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, output, Comma, Sp,
            OpenBracket, Call("DecidableEq", output), CloseBracket, Comma, Sp,
            tau, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            gamma, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
            Open, D(0), Sp, Lt, Sp, gamma, Sp, Leq, Sp, D(1), Close,
            Rightarrow, RowBreak, Grp(),
            Forall, Sp, left, Comma, Sp, right, InMacro, Sp, state, Comma, RowBreak,
            Grp(Open, relation, Rightarrow, Sp, distance, Sp, Eq, Sp, D(0), Close),
            Sp, Land, RowBreak,
            Grp(Open, separating, Rightarrow, Sp, distance, Sp, Eq, Sp, power, Close), Dot));
    }
}
