using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RootPrimitiveFourierDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootPrimitiveFourier";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative extraction of a matching frequency family",
        H("Frequency extraction for a summable exponential series"),
        Blocks(Describe.Lean(DescribeId.Create("spectral-fiber-average"),
            DeclarationHandle.Create(Owner + ".spectral_fiber_average"),
            H("The average recovers the sum over all matching indices"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write a(k) for the complex coefficients and v(k) for the complex "
                    + "modes. All modes and the tested mode w are purely imaginary. M(a) is the "
                    + "sum of the coefficient norms, and SummableNorm(a) asserts its summability. "
                    + "B(a,v,w) sums a(k) over every k with v(k)=w.")),
                Paragraph(Text("Avg(a,v,w,U,T) is the integral from U to U+T of the series "
                    + "with terms a(k) exp(v(k)u) multiplied by exp(−wu), divided by T. "
                    + "Integrable is Lebesgue interval integrability of the same integrand.")),
                Paragraph(Text("Every matching term is constant after modulation. The "
                    + "nonmatching series has modes v(k)−w at distance at least d from zero. "
                    + "Termwise integration bounds its interval integral by 2M(a)/d independently "
                    + "of U and T."))),
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

    private static Formula Statement()
    {
        var a = Id("a");
        var v = Id("v");
        var w = Id("w");
        var d = Id("d");
        var u = Id("U");
        var t = Id("T");
        var mode = Call("v", Id("k"));
        var family = new Formula.Power(Domain("C"), Domain("N"));
        var gaps = All("k", Domain("N"),
            Imp(NotEqual(mode, w), Le(d, new Formula.Norm(Subtract(mode, w)))));
        var imaginary = And(All("k", Domain("N"), Equal(Call("Re", mode), Num(0))),
            Equal(Call("Re", w), Num(0)));
        var result = And(Call("Integrable", a, v, w, u, t),
            Le(new Formula.Norm(Subtract(Call("Avg", a, v, w, u, t), Call("B", a, v, w))),
                new Formula.Fraction(Multiply(Call("M", a), new Formula.Fraction(Num(2), d)), t)));
        var lengths = All("U", Domain("R"), All("T", Domain("R"), Imp(Lt(Num(0), t), result)));
        var gapsAndLengths = All("d", Domain("R"), Imp(And(Lt(Num(0), d), gaps), lengths));
        var hypotheses = All("w", Domain("C"), Imp(And(Call("SummableNorm", a), imaginary),
            gapsAndLengths));
        return F.Disp(All("a", family, All("v", family, hypotheses)));
    }
}
