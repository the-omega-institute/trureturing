using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class EnvelopeKMonotoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic moment envelope increases with the mean and decreases with total squared deviation, giving a bound from an upper mean budget and a variance floor.",
        H("The general moment envelope and its monotonicity"),
        Blocks(
            Paragraph(Text(
                "All coordinates and moment parameters are real, and k is a natural number. The variance parameter is the total squared deviation, without division by k. Use the following logarithmic function and radius parametrization.")),
            Paragraph(Math(Disp(Seq(Call("f", T), Sp, Eq, Sp,
                Log, Open, D(1), Minus, Exp, Open, Minus, T, Close, Close)))),
            Paragraph(Math(Disp(Seq(Call("g", K, M, R), Sp, Eq, Sp, RadiusValue(R))))),
            Describe.Lean(
                DescribeId.Create("general-moment-envelope"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK"),
                H("The envelope"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Define r as the square root of V divided by k(k-1), L as m-r, and H as m+(k-1)r. The value is f(H)+(k-1)f(L). Its positive domain is k at least two, m positive, and zero at most V strictly below k(k-1)m squared. On this domain both nodes are positive. The real logarithm and square root give a total real definition outside this domain as well."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("envelope-strict-increase-in-mean"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK_strictMono_mean"),
                H("Strict increase in the mean"),
                StatementSource.FromAuthor(MeanFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k at least two, assume m is positive, m is less than n, and V is below k(k-1)m squared. Increasing m to n moves both positive nodes strictly to the right. Since f is strictly increasing and k-1 is positive, the envelope strictly increases. This statement also holds for negative V under the total real square-root convention; no nonnegativity premise on V is needed for this comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radius-envelope-derivative"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/EnvelopeKMonotone.radius_envelope_hasDerivAt"),
                H("The derivative in the radius"),
                StatementSource.FromAuthor(DerivativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let k be at least two and let zero be at most r strictly less than m. The upper node has velocity k-1 and the lower node has velocity minus one. The chain rule therefore gives the derivative (k-1) times the difference of the derivatives of f at the upper and lower nodes. Differentiability is an ordinary two-sided statement, including at radius zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radius-envelope-strict-decrease"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/EnvelopeKMonotone.radius_envelope_strictAnti"),
                H("Strict decrease in the radius"),
                StatementSource.FromAuthor(RadiusFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real m and k at least two, g(k,m,r) is strictly decreasing on the half-open interval from zero to m. The assertion is vacuous if m is nonpositive. At an interior radius, the upper node exceeds the lower by kr. The second derivative of f is strictly negative on the positive half-line, so its first derivative strictly decreases. The displayed radius derivative is therefore strictly negative in the interior. Continuity at zero and the mean value theorem give strict decrease on the entire half-open interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("envelope-strict-decrease-in-variance"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK_strictAnti_variance"),
                H("Strict decrease in total squared deviation"),
                StatementSource.FromAuthor(VarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let k be at least two, m positive, and zero at most V strictly less than W strictly below k(k-1)m squared. The square root of V divided by k(k-1) is strictly smaller than the corresponding radius for W, and both radii lie between zero and m. Strict decrease in the radius gives the stated strict inequality. In particular, V may equal zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-coordinate-variance-domain"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/EnvelopeKMonotone.coordinate_variance_domain"),
                H("The domain for positive coordinates"),
                StatementSource.FromAuthor(CoordinateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let x be a positive real vector indexed by Fin k, with k at least two, and let m be its arithmetic mean. Its total squared deviation is nonnegative and strictly below k(k-1)m squared. The positive lower Hermite node gives a radius smaller than m; squaring and multiplying by the positive denominator gives the strict domain bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-mean-and-variance-floor-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/EnvelopeKMonotone.sum_logValue_le_psiK"),
                H("A bound from two moment budgets"),
                StatementSource.FromAuthor(BudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let x be a positive real vector on Fin k, with k at least two. Let its arithmetic mean be at most the positive upper budget M. Suppose v is at most the actual total squared deviation and is strictly below k(k-1)M squared. Then the logarithmic coordinate sum is at most psiK(k,M,v). Apply the Hermite bound at the actual moments, increase the mean to M, and decrease the radius to the one specified by v. No positive lower mean budget is needed. For v negative, the total real square root is zero, and the same weak radius comparison remains valid; the strict variance theorem retains its nonnegative domain."))),
                DescribeRole.Theorem))));

    private static Formula K => F.Id("k");
    private static Formula M => F.Id("m");
    private static Formula N => F.Id("n");
    private static Formula R => F.Id("r");
    private static Formula T => F.Id("t");
    private static Formula V => F.Id("V");
    private static Formula W => F.Id("W");
    private static Formula Upper => F.Id("M");
    private static Formula Floor => F.Id("v");
    private static Formula Den => Seq(K, Open, K, Minus, D(1), Close);
    private static Formula Square(Formula t) => Seq(Open, t, Close, Caret, Grp(D(2)));
    private static Formula Bound(Formula m) => Seq(Den, Square(m));
    private static Formula Psi(Formula m, Formula v) => Call("psiK", K, m, v);
    private static Formula LowerNode(Formula r) => Seq(M, Minus, r);
    private static Formula UpperNode(Formula r) => Seq(M, Plus, Open, K, Minus, D(1), Close, r);
    private static Formula RadiusValue(Formula r) => Seq(
        Call("f", UpperNode(r)), Plus, Open, K, Minus, D(1), Close, Call("f", LowerNode(r)));
    private static Formula RadiusDerivative() => Seq(Open, K, Minus, D(1), Close, Open,
        Call("deriv", F.Id("f"), UpperNode(R)), Minus,
        Call("deriv", F.Id("f"), LowerNode(R)), Close);
    private static Formula ForK(Formula body) => Seq(
        Forall, Sp, K, Colon, Sp, Call("Nat"), Comma, Sp, body);
    private static Formula ForReal(Formula names, Formula body) => Seq(
        Forall, Sp, names, Colon, Sp, Call("Real"), Comma, Sp, body);
    private static Formula ImpliesFrom(Formula premise, Formula result) => Seq(
        Open, premise, Close, Sp, Implies, Sp, result);
    private static Formula KAtLeastTwo => Seq(D(2), Sp, Le, Sp, K);
    private static Formula X(Formula i) => Call("x", i);
    private static Formula SumOver(Formula t) => Seq(
        Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, Call("Fin", K)), Sp, t);
    private static Formula Mean => Seq(Frac, Grp(SumOver(X(F.Id("i")))), Grp(K));
    private static Formula ActualVariance => SumOver(Square(Seq(X(F.Id("i")), Minus, Mean)));
    private static Formula ForVector(Formula body) => Seq(
        Forall, Sp, F.Id("x"), Colon, Sp, Call("Fin", K), Sp, To, Sp, Call("Real"), Comma, Sp, body);
    private static Formula Positive => Seq(Open,
        Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", K), Comma, Sp,
        D(0), Sp, Lt, Sp, X(F.Id("i")), Close);

    private static Formula DefinitionFormula() => Disp(ForK(ForReal(Seq(M, Comma, V, Comma, R), Seq(
        R, Sp, Eq, Sp, Sqrt, Grp(Frac, Grp(V), Grp(Den)), Sp, Implies, Sp,
        Psi(M, V), Sp, Eq, Sp, RadiusValue(R)))));
    private static Formula MeanFormula() => Disp(ForK(ForReal(Seq(M, Comma, N, Comma, V),
        ImpliesFrom(Seq(KAtLeastTwo, Sp, Land, Sp, D(0), Sp, Lt, Sp, M, Sp, Land, Sp,
            M, Sp, Lt, Sp, N, Sp, Land, Sp, V, Sp, Lt, Sp, Bound(M)),
            Seq(Psi(M, V), Sp, Lt, Sp, Psi(N, V))))));
    private static Formula DerivativeFormula() => Disp(ForK(ForReal(Seq(M, Comma, R),
        ImpliesFrom(Seq(KAtLeastTwo, Sp, Land, Sp, D(0), Sp, Le, Sp, R, Sp, Land, Sp,
            R, Sp, Lt, Sp, M), Call("HasDerivAt", Call("g", K, M), RadiusDerivative(), R)))));
    private static Formula RadiusFormula() => Disp(ForK(ForReal(M,
        ImpliesFrom(KAtLeastTwo, Call("StrictAntiOn", Call("g", K, M), Call("Ico", D(0), M))))));
    private static Formula VarianceFormula() => Disp(ForK(ForReal(Seq(M, Comma, V, Comma, W),
        ImpliesFrom(Seq(KAtLeastTwo, Sp, Land, Sp, D(0), Sp, Lt, Sp, M, Sp, Land, Sp,
            D(0), Sp, Le, Sp, V, Sp, Land, Sp, V, Sp, Lt, Sp, W, Sp, Land, Sp,
            W, Sp, Lt, Sp, Bound(M)), Seq(Psi(M, W), Sp, Lt, Sp, Psi(M, V))))));
    private static Formula CoordinateFormula() => Disp(ForK(ForVector(
        ImpliesFrom(Seq(KAtLeastTwo, Sp, Land, Sp, Positive), Seq(
            D(0), Sp, Le, Sp, ActualVariance, Sp, Land, Sp,
            ActualVariance, Sp, Lt, Sp, Bound(Mean))))));
    private static Formula BudgetFormula() => Disp(ForK(ForVector(ForReal(Seq(Upper, Comma, Floor),
        ImpliesFrom(Seq(KAtLeastTwo, Sp, Land, Sp, Positive, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Upper, Sp, Land, Sp, Mean, Sp, Le, Sp, Upper, Sp, Land, Sp,
            Floor, Sp, Le, Sp, ActualVariance, Sp, Land, Sp, Floor, Sp, Lt, Sp, Bound(Upper)),
            Seq(SumOver(Call("f", X(F.Id("i")))), Sp, Le, Sp, Psi(Upper, Floor)))))));
}
