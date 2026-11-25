using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class WeightedTailFiniteWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-window weighted-tail estimate with a terminal defect",
        H("Weighted-tail bounds on a finite interval"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-tail-finite-window"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedTailFiniteWindow.neg_sqrt_mul_tail_le"),
                H("The normalized tail at the left endpoint"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a real kernel k integrable on (x, infinity), let Q be its tail "
                        + "and W its tail with logarithmic weight (1+log(t))/log(t)^2. "
                        + "Set a(t)=log(t)^2/(1+log(t)) and write v=a'. The terminal premise bounds "
                        + "Q(B)-a(B)W(B) from below. The coefficient D can be any real number.")),
                    Paragraph(Text("Apply weighted-tail inversion at x and B. The integrable vW term "
                        + "splits over (x,B] and (B,infinity). On (x,B], the weighted lower bound, "
                        + "0<=v(t)<=1/t and log(x)<=log(t) bound v(t)W(t) from below by "
                        + "(-A/log(x))*t^(-3/2). The exact mass of this power on (x,B] is "
                        + "2/sqrt(x)-2/sqrt(B). At x, the lower bound on a(x)W(x) contributes the "
                        + "factor log(x)/(1+log(x)). The integral contribution is zero at x=B."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);

    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Claim()
    {
        var k = F.Id("k");
        var x = F.Id("x");
        var t = F.Id("t");
        var upper = F.Id("B");
        var lowerCoefficient = F.Id("A");
        var defectCoefficient = F.Id("D");
        var sqrtX = Call("sqrt", x);
        var sqrtUpper = Call("sqrt", upper);
        var logX = Call("log", x);
        var window = All("t", Real, Imp(And(Le(x, t), Le(t, upper)),
            Le(new Formula.Fraction(new Formula.Negate(lowerCoefficient),
                Multiply(Call("sqrt", t), Call("log", t))), Call("W", t))));
        var defect = Le(new Formula.Fraction(new Formula.Negate(defectCoefficient), sqrtUpper),
            Subtract(Call("Q", upper), Multiply(Call("a", upper), Call("W", upper))));
        var finiteFactor = Multiply(new Formula.Fraction(D(2), logX),
            Seq(Open, Subtract(D(1), new Formula.Fraction(sqrtX, sqrtUpper)), Close));
        var coefficient = Add(new Formula.Fraction(logX, Add(D(1), logX)), finiteFactor);
        var conclusion = Le(Multiply(new Formula.Negate(sqrtX), Call("Q", x)),
            Add(Multiply(lowerCoefficient, Seq(Open, coefficient, Close)),
                new Formula.Fraction(Multiply(defectCoefficient, sqrtX), sqrtUpper)));
        var premises = Imp(Le(Call("exp", D(1)), x), Imp(Le(x, upper), Imp(Le(D(0), lowerCoefficient),
            Imp(Call("IntegrableOn", k, Call("Ioi", x)), Imp(window, Imp(defect, conclusion))))));
        return Disp(All("k", new Formula.TypeArrow(Real, Real),
            All("x", Real, All("B", Real, All("A", Real, All("D", Real, premises))))));
    }
}
