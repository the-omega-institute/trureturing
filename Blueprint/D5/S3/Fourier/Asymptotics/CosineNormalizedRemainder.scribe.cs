using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CosineNormalizedRemainderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform finite cosine-sum error estimate uses the actual cosine-integral tail and its Euler constant normalization.",
        H("A Uniform Cosine-Sum Remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-normalized-cosine-sum-remainder"),
                DeclarationHandle.Create(Module + "result"),
                H("One error constant for all positive frequencies and truncations"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is one positive real constant C, independent of both theta and N. "
                        + "For every real frequency 0<theta<=1 and every integer N>=1, "
                        + "the sum from k=1 to N differs from -log(theta)+Ci(N theta) "
                        + "by at most the displayed error. Here log is the natural logarithm "
                        + "and max(0,log(x)) is its positive part. The proof takes C=6.")),
                    Paragraph(Text(
                        "The function Ci is the real cosine integral defined by the absolutely "
                        + "convergent sine tail below for x>0. Integration by parts identifies "
                        + "this expression with the negative improper integral of cos(t)/t "
                        + "from x to infinity."),
                        Ref("D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral")),
                    new DocumentBlock.DisplayFormula(TailFormula()),
                    Paragraph(Text(
                        "Write q(t)=(cos(t)-1)/t, taking q(0)=0, and let Q(x) be its integral "
                        + "from 0 to x. First estimate g(t)=(cos(theta t)-1)/t, also extended "
                        + "by zero at the origin. The sinc identity makes g continuous there. "
                        + "For t>0, elementary trigonometric bounds give "
                        + "|g'(t)|<=6 theta^2/(1+theta t), while |g(t)|<=theta. "
                        + "The first Euler--Maclaurin formula, the bound 1/2 on its periodic "
                        + "Bernoulli factor, and the integral over the first unit interval "
                        + "give the following quadrature estimate.")),
                    new DocumentBlock.DisplayFormula(QuadratureFormula()),
                    Paragraph(Text(
                        "After the change of variables u=theta t, add the harmonic sum. "
                        + "Its difference from log(N)+gamma is positive and at most 1/(2N), "
                        + "where gamma is Euler's constant. This gives the desired error "
                        + "around gamma+log(N)+Q(N theta). It remains to identify this "
                        + "center with the actual cosine integral.")),
                    Paragraph(Text(
                        "Integration by parts in the sine tail shows that "
                        + "Ci(x)=Ci(1)+log(x)+Q(x)-Q(1) for x>0. The constant is determined "
                        + "analytically: for a>0, differentiation under an integrable "
                        + "exponential majorant evaluates the damped q integral.")),
                    new DocumentBlock.DisplayFormula(DampedFormula()),
                    Paragraph(Text(
                        "The derivative uses the exponential cosine integral "
                        + "a/(a^2+1); the integration constant is fixed by the limit as "
                        + "a tends to infinity. Scaling the logarithmic Gamma integral "
                        + "gives a times the integral of exp(-a t) log(t) equal to "
                        + "-gamma-log(a). Integration by parts also gives a times the "
                        + "Laplace integral of Q equal to the Laplace integral of q. "
                        + "Combining these identities produces the next equality.")),
                    new DocumentBlock.DisplayFormula(LaplaceFormula()),
                    Paragraph(Text(
                        "The positive-lattice square bound for Ci implies "
                        + "|Ci(t)|<=sqrt(K)/sqrt(t) for some K>0 and all t>0. "
                        + "Consequently the absolute value of the left side is at most "
                        + "sqrt(K) sqrt(a) Gamma(1/2), which tends to zero as a decreases "
                        + "to zero. The logarithmic term on the right also tends to zero. "
                        + "Thus Ci(1)-Q(1)=gamma, and the normalization follows."),
                        Ref("D5/S3/Fourier/Asymptotics/CosineIntegralLattice.result")),
                    new DocumentBlock.DisplayFormula(NormalizationFormula()),
                    Paragraph(Text(
                        "Substitute x=N theta and use log(N theta)=log(N)+log(theta). "
                        + "The quadrature error and the harmonic remainder sum to at most "
                        + "5 theta(1+max(0,log(N theta)))+1/(2N), which is bounded "
                        + "by the stated expression with C=6. The assertion concerns "
                        + "positive theta, including arbitrarily small positive frequencies, "
                        + "with no coupling condition between theta and N."))),
                DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Naturals => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Theta => F.Theta;
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Positive(Formula x) => Rel(F.D(0), FormulaRelationOperator.LessThan, x);
    private static Formula Le(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x, F.D(n));
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula Integral(Formula upper, Formula integrand) =>
        F.Seq(F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(upper), F.Sp,
            integrand, F.Sp, F.Id("d"), F.Id("t"));
    private static Formula Sum(Formula n, Formula summand) =>
        F.Seq(F.Sum, F.Underscore, F.Grp(F.Id("k"), F.Eq, F.D(1)),
            F.Caret, F.Grp(n), F.Sp, summand);
    private static Formula LogPart(Formula n) =>
        Add(F.D(1), Call("max", F.D(0), Call("log", Multiply(n, Theta))));
    private static Formula AllParameters(Formula body) =>
        F.Seq(F.Left, F.Open, F.Forall, F.Sp, Theta, F.Sp, F.InMacro, F.Sp, Reals,
            F.Comma, F.Sp, Implies(And(Positive(Theta), Le(Theta, F.D(1))),
                ForAll("N", Naturals, Implies(Le(F.D(1), F.Id("N")), body))), F.Right, F.Close);

    private static Formula TheoremFormula()
    {
        Formula c = F.Id("C"), n = F.Id("N"), k = F.Id("k");
        Formula sum = Sum(n, Div(Call("cos", Multiply(k, Theta)), k));
        Formula center = Add(Neg(Call("log", Theta)), Call("Ci", Multiply(n, Theta)));
        Formula bound = Multiply(c, Add(Div(F.D(1), n), Multiply(Theta, LogPart(n))));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("C"), Reals)],
            And(Positive(c), AllParameters(Le(Abs(Subtract(sum, center)), bound)))));
    }

    private static Formula TailFormula()
    {
        Formula x = F.Id("x"), t = F.Id("t");
        Formula tail = F.Seq(F.Int, F.Underscore, F.Grp(x), F.Caret, F.Grp(F.Infty),
            F.Sp, Div(Call("sin", t), Pow(t, 2)), F.Sp, F.Id("d"), t);
        return F.Disp(ForAll("x", Reals, Implies(Positive(x),
            Equal(Call("Ci", x), Subtract(Div(Call("sin", x), x), tail)))));
    }

    private static Formula QuadratureFormula()
    {
        Formula n = F.Id("N"), k = F.Id("k"), t = F.Id("t");
        Formula g(Formula x) => Div(Subtract(Call("cos", Multiply(Theta, x)), F.D(1)), x);
        Formula error = Abs(Subtract(Sum(n, g(k)), Integral(n, g(t))));
        return F.Disp(AllParameters(Le(error, Multiply(Multiply(F.D(5), Theta), LogPart(n)))));
    }

    private static Formula DampedFormula()
    {
        Formula a = F.Id("a"), t = F.Id("t");
        Formula integrand = Multiply(Call("exp", Neg(Multiply(a, t))),
            Div(Subtract(Call("cos", t), F.D(1)), t));
        Formula rhs = Subtract(Call("log", a), Div(Call("log", Add(Pow(a, 2), F.D(1))), F.D(2)));
        return F.Disp(ForAll("a", Reals, Implies(Positive(a), Equal(Integral(F.Infty, integrand), rhs))));
    }

    private static Formula LaplaceFormula()
    {
        Formula a = F.Id("a"), t = F.Id("t");
        Formula lhs = Multiply(a, Integral(F.Infty,
            Multiply(Call("exp", Neg(Multiply(a, t))), Call("Ci", t))));
        Formula rhs = Subtract(Subtract(Subtract(Call("Ci", F.D(1)), Call("Q", F.D(1))), F.GammaLower),
            Div(Call("log", Add(Pow(a, 2), F.D(1))), F.D(2)));
        return F.Disp(ForAll("a", Reals, Implies(Positive(a), Equal(lhs, rhs))));
    }

    private static Formula NormalizationFormula()
    {
        Formula x = F.Id("x"), t = F.Id("t");
        Formula rhs = Add(Add(F.GammaLower, Call("log", x)),
            Integral(x, Div(Subtract(Call("cos", t), F.D(1)), t)));
        return F.Disp(ForAll("x", Reals, Implies(Positive(x), Equal(Call("Ci", x), rhs))));
    }
}
