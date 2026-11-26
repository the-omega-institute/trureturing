using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusEvenCutoffShrinkingRateDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingRate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit error in the shrinking logarithmic width",
        H("The quantitative shrinking-width estimate"),
        Blocks(Describe.Lean(DescribeId.Create("signed-window-even-cutoff-shrinking-rate"),
            DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_shrinking_rate"),
            H("A logarithmic-square width bound for the original signed prime window"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Put q=m+1=2r, s=1/2−1/q, δ=1/q−1/(q+1) and c(m)=μ(q)q/(m s). "
                    + "F(m,u,L) is the original signed residual for exp(u), exp(u+L) divided by "
                    + "its power gap. S(r,u) is the real part of the sum over all actual zero "
                    + "occurrences of rootCoeff(r,k) exp((ρₖ−1/2)u/r), divided by s.")),
                Paragraph(Text("For shifts of size at most L, split the series at ordinate height "
                    + "1/L. The phase increment on the low side is bounded by the frequency times "
                    + "the shift. One factor of height cancels in the coefficient denominator. "
                    + "The truncated reciprocal moment bounds this part. On the high side the "
                    + "phase difference is at most two, and the inverse-square tail applies.")),
                Paragraph(Text("The normalized root increment equals the value of the centered "
                    + "signal at some point of the logarithmic window. The same modulus bounds "
                    + "the difference from the left endpoint. Dividing the even-cutoff expansion "
                    + "by the power gap retains its exponential arithmetic remainder."))),
            DescribeRole.Theorem))));

    private static Formula Domain(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Statement()
    {
        var m = Id("m");
        var r = Id("r");
        var u = Id("u");
        var width = Id("L");
        var threshold = Id("U");
        var c = Id("C");
        var k = Id("K");
        var zero = Num(0);

        var residual = new Formula.Absolute(Add(
            Add(Call("F", m, u, width), Call("c", m)),
            Multiply(Call("mu", r), Call("S", r, u))));
        var logFactor = Add(Num(1), Call("log", new Formula.Fraction(Num(1), width)));
        var widthError = Multiply(Multiply(c, width), Multiply(logFactor, logFactor));
        var arithmeticError = Multiply(k,
            Call("exp", new Formula.Negate(Multiply(Call("delta", m), u))));
        var windows = All("u", Domain("R"), All("L", Domain("R"),
            Imp(And(Le(threshold, u), And(Lt(zero, width), Le(width,
                new Formula.Fraction(Num(1), Num(4))))),
                Le(residual, Add(widthError, arithmeticError)))));
        var bounds = Exists("C", Domain("R"), Exists("K", Domain("R"),
            And(Lt(zero, c), And(Lt(zero, k), windows))));
        var orders = All("m", Domain("N"), All("r", Domain("N"),
            Imp(And(Le(Num(2), m), Equal(Add(m, Num(1)), Multiply(Num(2), r))), bounds)));
        return F.Disp(Imp(Id("RH"),
            Exists("U", Domain("R"), And(Lt(zero, threshold), orders))));
    }
}
