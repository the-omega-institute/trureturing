using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class FiniteSuiteExtendedBudgetSqueezeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/ErrorExponents/FiniteSuiteExtendedBudgetSqueeze."
            + "finite_suite_error_squeeze_extended";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Optimal equal-prior error for a finite independent suite is squeezed by an "
            + "extended Bhattacharyya budget, including zero affinity.",
        H("Finite-Suite Extended-Budget Error Squeeze"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-suite-error-squeeze-includes-zero-affinity"),
            DeclarationHandle.Create(Declaration),
            H("Finite-suite error squeeze includes zero affinity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The suite law and optimal equal-prior error are the frozen windowLaw "
                        + "product and finiteSuiteOptimalError, so the tested quantity remains "
                        + "the operational minimum over all finite decision events.")),
                Paragraph(Text(
                    "The extended budget is the negative extended logarithm of the joint "
                        + "Bhattacharyya affinity. Its zero-affinity value is infinity, and "
                        + "bhattacharyyaBudgetDecay maps that endpoint to zero while agreeing "
                        + "with the ordinary exponential of the negative finite budget.")),
                Paragraph(Text(
                    "Consequently no positivity premise is needed. At zero affinity both "
                        + "displayed bounds reduce to zero, forcing the optimal error itself "
                        + "to be zero."))),
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
        Formula budget = Call("finiteSuiteExtendedBhattacharyyaBudget", first, second);
        Formula decay = Call("bhattacharyyaBudgetDecay", budget);
        Formula optimalError = Call("finiteSuiteOptimalError", first, second);
        Formula decaySquare = new Formula.Power(decay, Grp(D(2)));
        Formula lowerRadicand = Seq(D(1), Minus, decaySquare);
        Formula lowerBound = new Formula.Fraction(
            Seq(D(1), Minus, Sqrt, Grp(lowerRadicand)),
            D(2));
        Formula upperBound = new Formula.Fraction(decay, D(2));

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
}
