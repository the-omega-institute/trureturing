using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class BinaryEntropyLogIntegralDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/localproductabsorption");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-root binary entropy is exactly a positive logarithmic integral on the entire closed unit interval.",
        H("A Logarithmic Integral for Binary Entropy"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-entropy-sqrt-log-integral"),
                DeclarationHandle.Create("D5/S3/Entropy/BinaryEntropyLogIntegral.binEntropy_sqrt_log_integral"),
                H("The exact closed-domain integral"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every real x with 0<=x<=1, the actual natural-logarithm binary entropy "
                        + "binEntropy((1+sqrt(1-x))/2) is one quarter of the integral of "
                        + "log(1+x/s)/sqrt(1+s) on s>0. The theorem also asserts absolute Lebesgue integrability. "
                        + "There is no differentiability or positive-rank assumption at either x endpoint.")),
                    Paragraph(Text("For 0<x<=1 put r=sqrt(1-x) and y=sqrt(1+s). A continuous primitive at s=0 is "
                        + "J(s)=2ylog(s+x)-2slog(s)/(y+1)-4log(y+1)+2r(log(y+r)-log(y-r)). "
                        + "For s>0 its derivative is the displayed nonnegative integrand. The identities "
                        + "y^2=1+s and r^2=1-x cancel the rational derivative terms exactly.")),
                    Paragraph(Text("For s>0 the same primitive equals "
                        + "2ylog(1+x/s)+2r(log(y+r)-log(y-r))-2(log(y+1)-log(y-1)). "
                        + "The first term lies between zero and 2xy/s, which tends to zero. "
                        + "Each remaining logarithmic difference tends to zero. Hence J tends to zero at infinity. "
                        + "At s=0, J is minus four times binEntropy((1+r)/2). The nonnegative-derivative improper FTC "
                        + "proves absolute integrability and the integral identity together. At x=0 the integrand "
                        + "and entropy are both identically zero; at x=1 the same primitive permits r=0.")),
                    Paragraph(Text("This is an identity for Real.binEntropy itself. It supplies an analytic component "
                        + "of the product-absorption scalar proof. It does not prove that scalar inequality, "
                        + "the nonnegative logarithmic first moment, or a statement about density matrices or quantum channels. "
                        + "The local unpublished ordinary scalar input is the mathematical source; numerical checks and "
                        + "ordinary review conclusions are not used as formal authority."))), DescribeRole.Theorem))));

    private static Formula N(string name) => F.Id(name);
    private static Formula R() => Seq(Mathbb, Grp(N("R")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Integrand() => Frac(Call("log", Add(D(1), Frac(N("x"), N("s")))),
        Call("sqrt", Add(D(1), N("s"))));
    private static Formula Integral() => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(Infty), Sp,
        Integrand(), Sp, N("ds"));
    private static Formula Entropy() => Call("binEntropy", Frac(Add(D(1),
        Call("sqrt", Subtract(D(1), N("x")))), D(2)));
    private static Formula Statement() => Seq(Forall, Sp, Par(Seq(N("x"), Colon, Sp, R())), Comma, Sp,
        Imp(And(Le(D(0), N("x")), Le(N("x"), D(1))), And(
            Call("IntegrableOn", Seq(LambdaLower, Sp, Par(Seq(N("s"), Colon, Sp, R())),
                Sp, Mapsto, Sp, Integrand()), Seq(Open, D(0), Comma, Sp, Infty, Close)),
            Equal(Entropy(), Multiply(Frac(D(1), D(4)), Integral())))));
}
