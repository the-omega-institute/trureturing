using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class MultipleTestingFalsePositiveDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent repeated tests amplify false-positive risk, while every finite family obeys the union bound.",
        H("False Positives under Multiple Testing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("at-least-one-false-positive"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Experiment/MultipleTestingFalsePositive."
                        + "at_least_one_false_positive"),
                H("At least one false positive"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The outcome space, probability measure, finite family of measurable "
                            + "false-positive events, common single-test rate alpha, and number "
                            + "of tests k are public source primitives.")),
                    Paragraph(Text(
                        "Under mutual independence, the no-error intersection has probability "
                            + "(1-alpha)^k and its complementary union has probability "
                            + "1-(1-alpha)^k. The displayed family of search-wide rates is "
                            + "nondecreasing in k.")),
                    Paragraph(Text(
                        "For k at least two and 0 < alpha < 1, the search-wide probability is "
                            + "strictly larger than alpha. This is the formal obstruction to "
                            + "reporting only the most successful test while retaining the "
                            + "single-test threshold as the whole-search error rate.")),
                    Paragraph(Text(
                        "The final public conjunct does not assume independence: Mathlib's "
                            + "finite union bound gives probability at most k times alpha for "
                            + "every measurable family with the stated marginal rates.")),
                    Paragraph(Text(
                        "Pinned Mathlib exact hits compute independent intersections, "
                            + "probability complements, finite union bounds, constant products, "
                            + "and power monotonicity. No repository theorem packages all five "
                            + "source clauses."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Probability(Formula measure, Formula eventFormula) =>
        Call("Pr", measure, eventFormula);

    private static Formula SearchRate(Formula alpha, Formula attempts) =>
        Seq(Num(1), Sp, Minus, Sp,
            Seq(Grp(Num(1), Sp, Minus, Sp, alpha), Caret, Grp(attempts)));

    private static Formula TheoremFormula()
    {
        Formula outcome = F.Id("Omega");
        Formula measure = F.Id("mu");
        Formula attempts = F.Id("k");
        Formula alpha = F.Id("alpha");
        Formula events = F.Id("E");
        Formula index = F.Id("i");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula anyError = Call("iUnion", events);
        Formula noError = Call("iInterCompl", events);
        Formula anyProbability = Probability(measure, anyError);
        Formula exactClauses = Seq(
            Probability(measure, noError), Sp, Eq, Sp,
            Seq(Grp(Num(1), Sp, Minus, Sp, alpha), Caret, Grp(attempts)),
            Sp, Land, Sp, RowBreak, Grp(),
            anyProbability, Sp, Eq, Sp, SearchRate(alpha, attempts),
            Sp, Land, Sp, RowBreak, Grp(),
            Grp(Forall, Sp, m, Comma, Sp, n, Colon, Sp,
                Operatorname, Grp(F.Id("Nat")), Comma, Sp,
                m, Sp, Le, Sp, n, Sp, Rightarrow, Sp,
                SearchRate(alpha, m), Sp, Le, Sp, SearchRate(alpha, n)),
            Sp, Land, Sp, RowBreak, Grp(),
            Open, Grp(Num(2), Sp, Le, Sp, attempts, Sp, Land, Sp,
                Num(0), Sp, Lt, Sp, alpha, Sp, Land, Sp,
                alpha, Sp, Lt, Sp, Num(1)),
            Sp, Rightarrow, Sp, alpha, Sp, Lt, Sp, anyProbability, Close);
        Formula premises = Seq(
            Call("IsProbabilityMeasure", measure), Sp, Land, Sp,
            Grp(Forall, Sp, index, Colon, Sp, Call("Fin", attempts), Comma, Sp,
                Call("Measurable", Call("event", events, index)), Sp, Land, Sp,
                Probability(measure, Call("event", events, index)), Sp, Eq, Sp, alpha),
            Sp, Land, Sp, Num(0), Sp, Le, Sp, alpha,
            Sp, Land, Sp, alpha, Sp, Le, Sp, Num(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, outcome, Colon, Sp, Operatorname, Grp(F.Id("Type")),
            Comma, Sp, measure, Colon, Sp, Call("Measure", outcome),
            Comma, Sp, attempts, Colon, Sp, Operatorname, Grp(F.Id("Nat")),
            Comma, RowBreak, Grp(),
            alpha, Colon, Sp, Operatorname, Grp(F.Id("Real")),
            Comma, Sp, events, Colon, Sp,
            Call("Fin", attempts), Sp, To, Sp, Call("Set", outcome),
            Comma, RowBreak, Grp(),
            premises, Sp, Rightarrow, Sp, RowBreak, Grp(),
            Grp(Call("iIndepSet", events, measure), Sp, Rightarrow, Sp,
                Grp(exactClauses)),
            Sp, Land, Sp, RowBreak, Grp(),
            anyProbability, Sp, Le, Sp, attempts, Sp, Times, Sp, alpha, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
