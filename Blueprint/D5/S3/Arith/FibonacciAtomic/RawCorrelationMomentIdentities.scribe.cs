using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class RawCorrelationMomentIdentitiesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The heterogeneous first-window parameters are legal and have an exact finite disagreement mass and norm-gap identity.",
        H("Finite Heterogeneous Raw-Correlation Moments"),
        Blocks(
            Paragraph(Text(
                "For rho in (0,1/8], set H1=1-3rho, H2=L3=2rho. "
                + "The three coordinates are independent Bernoulli variables with these parameters. "
                + "The product expectation is the explicit sum over all eight Bool triples of the "
                + "disagreement indicator: it is one exactly when the first two coordinates differ "
                + "and the third coordinate is true. The theorem evaluates this finite law exactly. "
                + "For a positive channel strength alpha, the resulting raw-score mean is also evaluated.")),
            Describe.Lean(
                DescribeId.Create("raw-correlation-moment-identities"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Legal parameters and exact finite moments"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first six conjuncts state that H1, H2 and L3 are probabilities. "
                    + "The seventh is the exact disagreement mass d=2rho(1-5rho+12rho^2), "
                    + "the last is the squared-norm difference H2 L3-H1 L3=-2rho+10rho^2, "
                    + "and the score mean alpha/8 times their sum is 3alpha rho^3>0. "
                    + "The same finite sum gives the exact variance kappa_alpha d-9alpha^2rho^6."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula N(int value) => D(value.ToString(System.Globalization.CultureInfo.InvariantCulture)
        .Select(character => (byte)(character - '0')).ToArray());
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Sq(Formula a) => Seq(Par(a), Caret, Grp(N(2)));
    private static Formula Pow(Formula a, int exponent) =>
        Seq(Par(a), Caret, Grp(N(exponent)));

    private static Formula ResultFormula()
    {
        var rho = V("rho");
        var h1 = Call("H", N(1), rho);
        var h2 = Call("H", N(2), rho);
        var l3 = Call("L", N(3), rho);
        var d = Call("d", rho);
        var gap = Call("G", rho);
        var alpha = V("alpha");
        var score = Call("M", alpha, rho);
        var variance = Call("V", alpha, rho);
        var kap = Call("kappa", alpha);
        var bounds = new Formula.Aligned([
            Seq(N(0), Leq, h1, Leq, N(1), Sp, Land, Sp,
                N(0), Leq, h2, Leq, N(1), Sp, Land, Sp,
                N(0), Leq, l3, Leq, N(1), Sp, Land),
            Seq(d, Sp, Eq, Sp, Seq(N(2), rho, Par(Seq(N(1), Minus, N(5), rho, Plus,
                N(12), Sq(rho)))), Sp, Land),
            Seq(gap, Sp, Eq, Sp, Seq(Minus, N(2), rho, Plus, N(10), Sq(rho)), Sp, Land),
            Seq(score, Sp, Eq, Sp,
                Seq(Fraction(alpha, N(8)), Par(Seq(d, Plus, gap))), Sp, Land),
            Seq(score, Sp, Eq, Sp, Seq(N(3), alpha, rho, Sq(rho)), Sp, Land),
            Seq(variance, Sp, Eq, Sp, Seq(kap, d, Minus, N(9), Sq(alpha), Pow(rho, 6)), Sp, Land),
            Seq(N(0), Lt, score)
        ]);
        return Disp(Seq(Forall, Sp, rho, Comma, Sp, alpha, Sp, InMacro, Sp,
            Seq(Mathbb, Grp(V("R"))), Sp,
            Par(Seq(N(0), Lt, rho, Leq, Fraction(N(1), N(8)), Sp, Land, Sp,
                N(0), Lt, alpha)), Comma, Sp, bounds));
    }
}
