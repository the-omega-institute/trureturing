using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class MovingBoxCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Abel error and capacity of shrinking logarithmic prime boxes.",
        H("Moving logarithmic prime boxes"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-local-abel"),
                DeclarationHandle.Create(Prefix + "abs_primeInterval_card_sub_integral_le"),
                H("Finite local Abel bound"),
                StatementSource.FromAuthor(FiniteBound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write primeIntervalCard(y,z) for the cardinality of the primes in the real interval (y,z]. "
                    + "Subtract the Abel identities at the two endpoints and use the derivative of "
                    + "t/log(t) to subtract the main integral. The absolute errors at the two "
                    + "endpoints contribute E/log(y)+E/log(z). The integral of the nonnegative "
                    + "kernel 1/(t log(t)^2) contributes at most E(1/log(y)-1/log(z))."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moving-log-power-capacity"),
                DeclarationHandle.Create(Prefix + "primeInterval_moving_log_power_capacity"),
                H("Capacity at each fixed positive log power"),
                StatementSource.FromAuthor(Capacity()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both actual real endpoints, and hence the entire box, eventually lie in [P/2,2P]. "
                    + "Choose an integer N>a and apply the theta error estimate uniformly on this shell. "
                    + "The finite Abel error divided by the counting scale then tends to zero. "
                    + "Monotonicity of 1/log(t) squeezes the main integral between the box width "
                    + "divided by the two endpoint logarithms. Each logarithm is asymptotic to log(P). "
                    + "The normalized width tends to v-u by differentiating exp(tv)-exp(tu) at zero. "
                    + "Positive and reflected negative boxes both follow by choosing the fixed ordered endpoints u,v."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert, Sp);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Ln(Formula t) => Seq(Log, Open, t, Close);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Implies(Formula h, Formula body) =>
        new Formula.Logic(h, FormulaLogicOperator.Implies, body);
    private static Formula And(Formula h, Formula k) =>
        new Formula.Logic(h, FormulaLogicOperator.And, k);

    private static Formula FiniteBound()
    {
        var y = F.Id("y");
        var z = F.Id("z");
        var e = F.Id("E");
        var t = F.Id("t");
        var error = All("t", Implies(Seq(t, InMacro, Sp, OpenBracket, y, Comma, z, CloseBracket),
            Seq(Abs(Sub(Seq(Theta, Open, t, Close), t)), Leq, Sp, e)));
        var integral = Seq(Int, Underscore, Grp(y), Caret, Grp(z),
            Div(D(1), Ln(t)), Thin, F.Id("d"), Sp, t);
        var assumptions = And(Seq(D(2), Leq, Sp, y),
            And(Seq(y, Leq, Sp, z), Seq(Open, error, Close)));
        var bound = Seq(Abs(Sub(Call("primeIntervalCard", y, z), integral)),
            Leq, Sp, Div(Seq(D(2), e), Ln(y)));
        return Disp(All("y", All("z", All("E", Implies(assumptions, bound)))));
    }

    private static Formula Capacity()
    {
        var c = F.Id("C");
        var a = F.Id("a");
        var u = F.Id("u");
        var v = F.Id("v");
        var p = F.Id("P");
        var scale = Seq(c, Thin, new Formula.Power(Seq(Open, Ln(p), Close), a));
        Formula Endpoint(Formula w) => Seq(p, Thin, Exp, Open, Div(w, scale), Close);
        var limit = Seq(Lim, Underscore, Grp(p, To, Sp, Infty),
            Div(Call("primeIntervalCard", Endpoint(u), Endpoint(v)), Div(Div(p, Ln(p)), scale)),
            Eq, Sub(v, u));
        return Disp(All("C", All("a", All("u", All("v", Implies(
            And(Seq(D(0), Lt, c), And(Seq(D(0), Lt, a), Seq(u, Lt, v))), limit))))));
    }
}
