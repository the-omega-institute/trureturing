using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class JensenHermiteScalingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/JensenHermiteScaling.";
    private static readonly LibraryNoteRef HermiteZeros =
        LibraryNoteRef.Create("D5/L/Analytic/nist2026dlmforthogonalzeros");
    private static Formula V(string name) => F.Id(name);
    private static Formula Norm(Formula value) => Seq(Lvert, Sp, value, Rvert, Sp);
    private static Formula Pow(Formula value, Formula power) => Seq(value, Caret, Grp(power));
    private static Formula Fr(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula D(Formula order, Formula point) => Call("D", order, V("F"), point);

    private static Formula DerivativeStatement() => Seq(
        Norm(D(V("b"), V("z"))), Le, Sp, Call("weightedNorm", V("a"), V("b"), V("R")));
    private static Formula TransformedStatement() => Call("HasSum",
        Seq(V("j"), Mapsto, Sp, Call("b", V("j")), Pow(V("z"), V("j"))),
        Seq(Minus, F.D(4), V("z"), D(F.D(2), V("z")), Minus, F.D(2), D(F.D(1), V("z"))));
    private static Formula WeightStatement() => Seq(
        Call("Summable", Seq(V("j"), Mapsto, Sp, Norm(Call("b", V("j"))), Pow(V("j"), V("L")),
            Pow(V("R"), V("j")))), Land, Sp, Call("weightedNorm", V("b"), V("L"), V("R")), Le, Sp, F.D(4), Call("weightedNorm", V("a"), Seq(V("L"), Plus, F.D(2)),
            Call("max", F.D(1), V("R"))));
    private static Formula HermiteStatement() => Seq(
        Call("He", V("v"), V("u")), Eq, Sum, Underscore, Grp(F.D(0), Le, Sp, V("r"), Le, Sp, Fr(V("v"), F.D(2))),
        Fr(Seq(Pow(Seq(Open, Minus, F.D(1), Close), V("r")), Seq(V("v"), Bang)),
            Seq(Pow(F.D(2), V("r")), Seq(V("r"), Bang), Seq(Open, V("v"), Minus, F.D(2), V("r"), Close, Bang))),
        Pow(V("u"), Seq(V("v"), Minus, F.D(2), V("r"))));
    private static Formula TaylorStatement() => Seq(
        Norm(Seq(D(V("k"), Seq(V("c"), Plus, V("y"))), Minus,
            Fr(Seq(D(V("v"), V("c")), Pow(V("y"), Seq(V("v"), Minus, V("k")))), Seq(Open, V("v"), Minus, V("k"), Close, Bang)))),
        Le, Sp, Fr(Seq(V("B"), Pow(Norm(V("y")), Seq(V("v"), Minus, V("k"), Plus, F.D(1)))),
            Seq(Open, V("v"), Minus, V("k"), Close, Bang)));
    private static Formula ScalingStatement() => Seq(
        Call("IsExactRealOrder", V("F"), V("tzero"), V("v")), Implies, Sp, Call("ScaledFunctionEstimate", V("F"), V("a"), V("tzero"), V("sigma"), V("v")));
    private static Formula ThresholdStatement() => new Formula.Aligned([
        Seq(V("T"), Eq, Call("max", F.D(1),
            Call("max", Seq(F.D(2), V("q")), Fr(Seq(V("tzero"), V("q")), V("sigma"))))),
        Seq(V("N"), Eq, Call("max", F.D(1), Call("NatCeil", Pow(V("T"), F.D(2))))),
        Seq(Forall, Sp, V("n"), Ge, Sp, V("N"), Comma, Sp, F.D(1), Le, Sp, V("n"), Land, Sp, F.D(1), Le, Sp, Call("sqrt", V("n")), Land, Sp, Fr(V("q"), Call("sqrt", V("n"))), Le, Sp, Fr(F.D(1), F.D(2)), Land, Sp, Fr(Seq(V("tzero"), V("q")), Call("sqrt", V("n"))), Le, Sp, V("sigma"))
    ]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire weighted coefficient series control every complex segment at an exact finite order.",
        H("Hermite local scaling"),
        Blocks(
            Paragraph(Text("Write D(k,F,z)=iteratedDeriv k F z, and b(j)=loweredCoefficients(a,j). The derivative, transformed-series, Taylor and scaling results assume HasSum(j -> a(j)*z^j,F(z)) for every complex z and summability of norm(a(j))*j^L*R^j for every natural L and every real R>=0. The transformed-weight result needs only the latter summability assumption. The Hermite coefficient identity and geometric threshold need neither assumption.")),
            Describe.Lean(DescribeId.Create("jensen-hermite-derivative-bound"),
                DeclarationHandle.Create(Prefix + "entire_derivative_bound"), H("Actual derivative bound"),
                StatementSource.FromAuthor(Disp(DerivativeStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume HasSum(j -> a(j) z^j, F(z)) at every complex z, and summability of norm(a(j))*j^L*R^j for every natural L and nonnegative real R. For R>=1 and norm(z)<=R, the actual b-th derivative has norm at most weightedNorm(a,b,R). Complex differentiation of uniformly summable monomial series establishes the derivative identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jensen-hermite-transformed-series"),
                DeclarationHandle.Create(Prefix + "lowered_series"), H("The transformed entire series"),
                StatementSource.FromAuthor(Disp(TransformedStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For b(j)=-(2j+2)(2j+1)a(j+1), the transformed function is -4z F''(z)-2F'(z). Both derivative series are shifted by one index after treating the vanished coefficient. The identity includes z=0 without division by z."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jensen-hermite-transformed-weights"),
                DeclarationHandle.Create(Prefix + "lowered_weighted_data"), H("All transformed weighted sums"),
                StatementSource.FromAuthor(Disp(WeightStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural L and nonnegative R, the majorant is 4*norm(a(j+1))*(j+1)^(L+2)*max(1,R)^(j+1). The omitted zero-index term of the original weighted sum is zero. This proves both summability and the displayed norm bound, including R=0 and L=0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jensen-hermite-normalization"),
                DeclarationHandle.Create(Prefix + "hermite_normalization"), H("The probabilists' normalization"),
                StatementSource.FromAuthor(Disp(HermiteStatement())), AssessedProvenance.FromRepo(HermiteZeros),
                Blocks(Paragraph(Text("The integer Hermite coefficient formula, the binomial factorial identity and the even double-factorial identity give this coefficient normalization. The equivalent expression uses correctionCoeff(r,2r)=1/(2^r*r!). Both parities and v=0 are included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jensen-hermite-scaling-threshold"),
                DeclarationHandle.Create(Prefix + "hermite_scaling_threshold"), H("An explicit geometric threshold"),
                StatementSource.FromAuthor(Disp(ThresholdStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real t0>0, sigma>0 and q>=2, NatCeil is the natural ceiling. This threshold simultaneously gives n>=1, sqrt(n)>=1, q/sqrt(n)<=1/2 and t0*q/sqrt(n)<=sigma for every later natural n. It requires no coefficient, analyticity or zero-order hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jensen-hermite-segment-taylor"),
                DeclarationHandle.Create(Prefix + "exact_order_taylor_bound"), H("Every complex segment"),
                StatementSource.FromAuthor(Disp(TaylorStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here c>0, sigma>0, k<=v, norm(y)<=sigma, F has exact order v at c, and B=weightedNorm(a,v+1,max(1,c+sigma)). The real parameter t traverses c+t*y for 0<=t<=1. Its m-th derivative is y^m D^(k+m)F(c+t*y), by complex differentiation and restriction to real scalars. The vector-valued Taylor bound leaves only the degree v-k term. The denominator (v-k)! is sufficient, including k=v and v=0. No cancellation by y occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jensen-hermite-scaled-estimate"),
                DeclarationHandle.Create(Prefix + "hermite_scaled_estimate"), H("Every order on the full complex disk"),
                StatementSource.FromAuthor(Disp(ScalingStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the actual entire HasSum and all weighted summability hypotheses above, with t0>0 and sigma>0. For each real q>=2, set T=max(1,max(2q,t0*q/sigma)) and N=max(1,ceil(T^2)). An explicit positive finite C bounds the original normalized error by C/sqrt(n) for every natural n>=N and every complex u with norm(u)<=q. The normalization is t0^v*D^vF(t0)/v!, divided by sqrt(n)^v, and is nonzero by exact order.")),
                    Paragraph(Text("Set K=v/2. For each finite correction pair r<=K,k<=2r, the normalized leading term has denominator sqrt(n)^(2r-k); only k=2r contributes to the Hermite polynomial. The Taylor error has denominator sqrt(n)^(2r-k+1). The coefficient remainder has denominator sqrt(n)^(2K+2-v), whose exponent is one or two. Positive coefficient norms bound the finite sum, and a positive unit is added to its constant.")),
                    Paragraph(Text("The complex disk includes its boundary, u=0 and moving zeros. The transformed branch uses its own coefficient sequence and its own nonzero exact-order derivative. The function estimate supplies no root enumeration, original boundary zero exclusion, compact-window exhaustion or RH conclusion."))),
                DescribeRole.Theorem))));
}
