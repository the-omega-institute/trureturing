using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class FiniteSuiteErrorSqueezeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/ErrorExponents/FiniteSuiteErrorSqueeze."
            + "finite_suite_error_squeeze";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Optimal equal-prior error for a finite independent suite is squeezed by its "
            + "Bhattacharyya evidence budget.",
        H("Finite-Suite Error Squeeze"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-suite-optimal-error-obeys-the-affinity-squeeze"),
            DeclarationHandle.Create(Declaration),
            H("Finite-suite optimal error obeys the affinity squeeze"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The suite law is the canonical windowLaw product of its coordinate laws. "
                        + "The equal-prior error is minimized over all decision events on the "
                        + "finite outcome-vector space, so the public quantity is an operational "
                        + "testing risk rather than a restatement of either bound.")),
                Paragraph(Text(
                    "The budget is the negative sum of the logarithms of the coordinate "
                        + "Bhattacharyya affinities. Exact affinity multiplicativity turns its "
                        + "exponential back into the joint-law affinity, while the sharp lower "
                        + "and upper estimates follow from the total-variation comparisons.")),
                Paragraph(Text(
                    "Every coordinate affinity is assumed strictly positive. This is the exact "
                        + "restriction needed for a finite real logarithmic budget: a zero "
                        + "affinity corresponds to infinite evidence, which cannot be represented "
                        + "by Lean's totalized real logarithm."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("Index");
        Formula outcomeType = F.Id("Outcome");
        Formula first = F.Id("p");
        Formula second = F.Id("q");
        Formula index = F.Id("i");
        Formula outcome = F.Id("a");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula lawType = new Formula.TypeArrow(
            indexType,
            new Formula.TypeArrow(outcomeType, reals));
        Formula firstAt = Call("p", index, outcome);
        Formula secondAt = Call("q", index, outcome);
        Formula localAffinity = Call(
            "bhattacharyya",
            Seq(first, Underscore, Grp(index)),
            Seq(second, Underscore, Grp(index)));
        Formula budget = Call("finiteSuiteBhattacharyyaBudget", first, second);
        Formula optimalError = Call("finiteSuiteOptimalError", first, second);
        Formula exponentialBudget = Exp(Seq(Minus, budget));
        Formula lowerRadicand = Seq(D(1), Minus, Exp(Seq(Minus, D(2), budget)));
        Formula lowerBound = new Formula.Fraction(
            Seq(D(1), Minus, Sqrt, Grp(lowerRadicand)),
            D(2));
        Formula upperBound = new Formula.Fraction(exponentialBudget, D(2));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, indexType, Comma, Sp, outcomeType, Colon, Sp, type, Comma),
            Seq(Grp(), OpenBracket, Call("Fintype", indexType), CloseBracket, Comma, Sp,
                OpenBracket, Call("DecidableEq", indexType), CloseBracket, Comma),
            Seq(Grp(), OpenBracket, Call("Fintype", outcomeType), CloseBracket, Comma),
            Seq(first, Comma, Sp, second, Colon, Sp, lawType, Comma),
            Seq(Open,
                Forall, Sp, index, Comma, Sp,
                Open, Forall, Sp, outcome, Comma, Sp, D(0), Sp, Leq, Sp, firstAt, Close,
                Sp, Land, Sp,
                Sum, Underscore, Grp(outcome), Sp, firstAt, Sp, Eq, Sp, D(1), Close,
                Sp, Land),
            Seq(Open,
                Forall, Sp, index, Comma, Sp,
                Open, Forall, Sp, outcome, Comma, Sp, D(0), Sp, Leq, Sp, secondAt, Close,
                Sp, Land, Sp,
                Sum, Underscore, Grp(outcome), Sp, secondAt, Sp, Eq, Sp, D(1), Close,
                Sp, Land),
            Seq(Open, Forall, Sp, index, Comma, Sp, D(0), Sp, Lt, Sp, localAffinity, Close,
                Sp, Rightarrow),
            Seq(lowerBound, Sp, Leq, Sp, optimalError, Sp, Land),
            Seq(optimalError, Sp, Leq, Sp, upperBound, Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname, Grp(F.Id(name)), Open
        };
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

    private static Formula Exp(Formula exponent) =>
        Seq(Operatorname, Grp(F.Id("exp")), Open, exponent, Close);
}
