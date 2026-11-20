using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class DottieIterationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The equation cos(t) = t has exactly one real solution theta, and the cosine iteration converges to theta from every real start, geometrically from the second iterate on, with ratio of consecutive errors tending to -sin(theta) along every orbit that avoids theta.",
        H("Global convergence of the cosine iteration"),
        Blocks(
            Describe.Lean(DescribeId.Create("dottie-iteration-cos-iterate-tendsto"),
                DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/DottieIteration.cos_iterate_tendsto"),
                H("The cosine iteration converges to its unique real fixed point"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("All quantities are real and angles are in radians. In the formula cos^[n] denotes the n-fold composite of the cosine with itself, the zeroth composite being the identity, so cos^[n](x) is the n-th term of the orbit of the start x. The statement has four parts. There is a real number theta with 0 < theta < 1 such that a real t satisfies cos(t) = t exactly when t = theta. For every real start x the orbit cos^[n](x) tends to theta as n tends to infinity. From the second iterate on the error obeys the uniform bound |cos^[n+2](x) - theta| <= sin(1)^n (1 - theta) for every natural n, the same constant for all starts. If no term of the orbit equals theta, the ratio (cos^[n+1](x) - theta) / (cos^[n](x) - theta) of consecutive errors tends to -sin(theta).")),
                    Paragraph(Text("Existence of theta in (0, 1) and its uniqueness among positive solutions are taken from the inverse-series endpoint theorem of the neighbouring document on the rational inverse series. Uniqueness among all real solutions follows because a solution t equals cos(t) and hence lies in [-1, 1], and the cosine is positive on [-1, 0], so no solution is less than or equal to zero.")),
                    Paragraph(Text("The cosine maps [-1, 1] into [cos(1), 1], because it is even and decreasing on [0, 1]. Every first iterate lies in [-1, 1], so every second iterate lies in [cos(1), 1], and this interval is mapped into itself. For u and v in [0, 1] the identity cos(u) - cos(v) = -2 sin((u + v)/2) sin((u - v)/2), together with 0 <= sin((u + v)/2) <= sin(1) and |sin(s)| <= |s|, gives |cos(u) - cos(v)| <= sin(1) |u - v|. Applied along the orbit from the second iterate and to the fixed point theta, which also lies in [cos(1), 1], this gives |cos^[n+2](x) - theta| <= sin(1)^n |cos^[2](x) - theta|. Since cos(1) >= 1/2 and theta < 3/4, every point y of [cos(1), 1] satisfies |y - theta| <= 1 - theta, which yields the stated bound. Because 0 < sin(1) < 1, the bound tends to zero, and convergence of the orbit follows.")),
                    Paragraph(Text("The constant 1 - theta cannot be decreased: for x = pi/2 one has cos(pi/2) = 0 and cos(0) = 1, so cos^[2](pi/2) = 1 and the bound holds with equality at n = 0. The ratio sin(1) is a uniform rate, not the asymptotic one. The derivative of the cosine at theta is -sin(theta), and since sin(theta)^2 = 1 - theta^2 and sin(theta) > 0, its absolute value is sqrt(1 - theta^2), which is smaller than sin(1). Writing the ratio of consecutive errors as the difference quotient (cos(y) - cos(theta)) / (y - theta) at y = cos^[n](x), and using cos(theta) = theta, the convergence of the orbit to theta through points different from theta turns the derivative into the limit of the ratios. Along such an orbit the errors therefore eventually alternate in sign.")),
                    Paragraph(Text("The hypothesis that no term of the orbit equals theta cannot be removed from the last part. For the start x = -theta, evenness of the cosine gives cos(-theta) = theta, so every term from the first on equals theta. All later errors vanish; with the convention that division by zero gives zero, which the statement uses, the ratios are zero from n = 1 on and tend to 0, which differs from -sin(theta) because sin(theta) > 0. The same happens for every start of the form theta + 2 pi k or -theta + 2 pi k with an integer k.")),
                    Paragraph(Text("Numerically theta = 0.7390851332..., sin(theta) = 0.6736120291... and sin(1) = 0.8414709848...; these decimals are not part of the statement. The statement concerns the real cosine only: the iteration of the complex cosine on the complex plane is not claimed. The number theta is transcendental by the Lindemann-Weierstrass theorem; transcendence is not part of the statement. The global convergence of the real cosine iteration is classical: it is a contraction argument of Banach fixed-point type, and the limit theta is widely known as the Dottie number."))),
                DescribeRole.Theorem))));

    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Lt(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Eq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => Rel(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Minus(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Times(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula AtTop => Seq(Operatorname, Grp(F.Id("atTop")));
    private static Formula X => F.Id("x");
    private static Formula N => F.Id("n");

    /// <summary>cos^[k](x): the k-fold composite of the cosine applied to x.</summary>
    private static Formula Iterate(Formula k) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("cos")), Caret, Grp(OpenBracket, k, CloseBracket)), [X]);

    private static Formula Plus(Formula x, byte d) => Seq(x, Sp, F.Plus, Sp, D(d));

    private static Formula Statement()
    {
        Formula fixedPoints = All("t", Reals, Iff(Eq(Call("cos", F.Id("t")), F.Id("t")), Eq(F.Id("t"), Theta)));
        Formula convergence = Call("Tendsto", Seq(N, Sp, Mapsto, Sp, Iterate(N)), AtTop, Call("nhds", Theta));
        Formula rate = All("n", Naturals, Le(
            new Formula.Absolute(Minus(Iterate(Plus(N, 2)), Theta)),
            Times(new Formula.Power(Call("sin", D(1)), N), Minus(D(1), Theta))));
        Formula avoids = All("n", Naturals, Ne(Iterate(N), Theta));
        Formula ratio = Call("Tendsto",
            Seq(N, Sp, Mapsto, Sp, new Formula.Fraction(Minus(Iterate(Plus(N, 1)), Theta), Minus(Iterate(N), Theta))),
            AtTop, Call("nhds", new Formula.Negate(Call("sin", Theta))));
        Formula orbit = All("x", Reals, And(convergence, And(rate, Implies(avoids, ratio))));
        Formula body = And(Lt(D(0), Theta), And(Lt(Theta, D(1)), And(fixedPoints, orbit)));
        return Disp(Seq(Exists, Sp, Theta, Sp, InMacro, Sp, Reals, Comma, Sp, body));
    }
}
