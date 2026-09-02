using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class JensenPolynomialObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/Jensen/JensenPolynomialObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Jensen polynomial tower turns failure of a real-zero criterion into a "
            + "negative coefficient or one finite nonhyperbolic witness.",
        H("Jensen Polynomial Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("jensen-polynomial"),
                DeclarationHandle.Create(Prefix + "jensenPolynomial"),
                H("Shifted Jensen polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For degree d and shift n, the polynomial sums choose(d,k) times "
                        + "gamma(n+k) times X^k over k from zero through d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("polynomial-hyperbolic"),
                DeclarationHandle.Create(Prefix + "PolynomialHyperbolic"),
                H("Polynomial hyperbolicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real polynomial is hyperbolic when every root after mapping its "
                        + "coefficients to the complex numbers has zero imaginary part."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("jensen-polynomial-obstruction"),
                DeclarationHandle.Create(Prefix + "jensen_polynomial_obstruction"),
                H("Failure has a negative coefficient or a nonhyperbolic Jensen witness"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exponential-series coefficients satisfy gamma(m)=m!a(m). The "
                            + "two supplied Jensen-Polya bridges say that RH makes every shifted "
                            + "Jensen polynomial hyperbolic, while nonnegative coefficients and "
                            + "a fully hyperbolic tower imply RH.")),
                    Paragraph(Text(
                        "If RH fails and no coefficient is negative, every coefficient is "
                            + "nonnegative. If no finite nonhyperbolic witness existed either, "
                            + "the reverse bridge would imply RH, a contradiction.")),
                    Paragraph(Text(
                        "The polynomial and hyperbolicity predicate are concrete Lean "
                            + "definitions. The deep Laguerre-Polya implications remain explicit "
                            + "hypotheses because neither this repository nor pinned Mathlib "
                            + "contains that analytic classification theorem."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula coefficient = F.Id("a");
        Formula gamma = F.GammaLower;
        Formula rh = F.Id("RH");
        Formula m = F.Id("m");
        Formula d = F.Id("d");
        Formula n = F.Id("n");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula gammaRelation = Seq(
            Forall, Sp, m, InMacro, natural, Comma, Sp,
            Apply(gamma, m), Sp, Eq, Sp, m, Bang, Sp,
            Apply(coefficient, m));
        Formula hyperbolicTower = Seq(
            Forall, Sp, d, Comma, Sp, n, InMacro, natural, Comma, Sp,
            Call("Hyperbolic", Call("J", gamma, d, n)));
        Formula nonnegative = Seq(
            Forall, Sp, m, InMacro, natural, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(coefficient, m));
        Formula forwardBridge = Seq(
            rh, Sp, Rightarrow, Sp, Open, hyperbolicTower, Close);
        Formula reverseBridge = Seq(
            Open, nonnegative, Close, Sp, Land, Sp,
            Open, hyperbolicTower, Close, Sp, Rightarrow, Sp, rh);
        Formula negativeWitness = Seq(
            Exists, Sp, m, InMacro, natural, Comma, Sp,
            Apply(coefficient, m), Sp, Lt, Sp, D(0));
        Formula badJensenWitness = Seq(
            Exists, Sp, d, Comma, Sp, n, InMacro, natural, Comma, Sp,
            Neg, Sp, Call("Hyperbolic", Call("J", gamma, d, n)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, coefficient, Comma, Sp, gamma, Colon, Sp,
                natural, Sp, To, Sp, real, Comma, Sp, rh, Colon, Sp,
                Seq(Operatorname, Grp(F.Id("Prop"))), Comma),
            Seq(
                Open, gammaRelation, Close, Sp, Land, Sp,
                Open, forwardBridge, Close, Sp, Land, Sp,
                Open, reverseBridge, Close, Sp, Rightarrow),
            Seq(
                Open, forwardBridge, Close, Sp, Land),
            Seq(
                Open, Neg, Sp, rh, Sp, Rightarrow, Sp,
                Open, negativeWitness, Close, Sp, Lor, Sp,
                Open, badJensenWitness, Close, Close, Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
