using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class HermiteEnvelopeEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic Hermite bound is attained exactly at the moment nodes, with one upper coordinate when the variance is positive.",
        H("Equality in the Hermite envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-sign-left-of-double-node"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.negative_left_of_double_node"),
                H("Strict sign to the left of the double node"),
                StatementSource.FromAuthor(LeftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let x, L and H be real numbers with x less than L and L less than H. Let g be three times continuously differentiable on the real line. Suppose g vanishes at L and H, its derivative vanishes at L, and its third derivative is strictly positive throughout the open interval from x to H. Then g(x) is strictly negative. If g(x) were nonnegative, two mean value arguments would produce a nonnegative second derivative to the left of L. Two Rolle arguments produce a zero second derivative to the right of L, contradicting strict increase of the second derivative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hermite-envelope-equality-classification"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_equality"),
                H("Positive variance and the unique upper coordinate"),
                StatementSource.FromAuthor(EqualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be a natural number at least two and let x assign positive real coordinates to Fin k. Write m for their mean, V for their total squared deviation, r for the radius, and L and H for the two nodes.")),
                    Paragraph(Math(Disp(MomentDefinitions()))),
                    Paragraph(Math(Disp(FunctionDefinition()))),
                    Paragraph(Text(
                        "If V is positive, the sum attains the envelope if and only if every coordinate equals L or H. For coordinates at these nodes, the first moment forces exactly one coordinate to equal H and every other coordinate to equal L.")),
                    Paragraph(Text(
                        "Use the quadratic agreeing with f and its derivative at L and with f at H. Its sum is determined by the first two moments. At any positive coordinate below H other than the nodes, f is strictly below this quadratic: the interval remainder handles coordinates between the nodes, and the preceding strict sign handles coordinates to the left. The nonnegative differences sum to zero exactly when every difference is zero. Finally, counting the upper coordinates gives their count times H-L equal to H-L, so their count is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hermite-envelope-zero-variance"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_zero_variance"),
                H("Zero variance"),
                StatementSource.FromAuthor(ZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any natural k and real vector indexed by Fin k, use the same definitions of m, V, r, L and H. If V is zero, each nonnegative squared deviation is zero. Thus every coordinate equals m, both nodes equal m, and the logarithmic sum equals its envelope. This identity requires no positivity assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hermite-envelope-sharpness"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteEnvelopeEquality.hermite_envelope_sharpness"),
                H("Attainment for every feasible pair of moments"),
                StatementSource.FromAuthor(SharpnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Now prescribe a natural k at least two and real parameters m and V satisfying m positive and zero at most V strictly less than k(k-1)m squared. Define r, L and H from these parameters as follows.")),
                    Paragraph(Math(Disp(RadiusNodes()))),
                    Paragraph(Text(
                        "There is a positive real vector whose first sum is km, whose total squared deviation about m is V, and whose square sum is km squared plus V. It attains the logarithmic envelope and has one distinguished coordinate H and all other coordinates L. When V is zero the nodes coincide, so the distinguished index need not be unique.")),
                    Paragraph(Text(
                        "Choose index zero for H and put L at every other index. The radius is smaller than m, which proves positivity. Summing any function over this vector gives its value at H plus k-1 times its value at L. Applying this to the identity, centered square and square gives the required moments. The equality classification, including its zero variance case, then gives attainment. Together with the upper bound this proves optimality in the class of positive real vectors with the prescribed moments."))),
                DescribeRole.Theorem))));

    private static Formula K => F.Id("k");
    private static Formula M => F.Id("m");
    private static Formula V => F.Id("V");
    private static Formula L => F.Id("L");
    private static Formula U => F.Id("H");
    private static Formula X(Formula i) => Call("x", i);
    private static Formula Square(Formula t) => Seq(Open, t, Close, Caret, Grp(D(2)));
    private static Formula All(Formula i, Formula body) => Seq(
        Forall, Sp, i, Colon, Sp, Call("Fin", K), Comma, Sp, body);
    private static Formula SumOver(Formula t) => Seq(
        Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, Call("Fin", K)), Sp, t);
    private static Formula VectorQuantifier(Formula quantifier) => Seq(
        quantifier, Sp, F.Id("x"), Colon, Sp, Call("Fin", K), Sp, To, Sp, Call("Real"), Comma, Sp);
    private static Formula Positive() => All(F.Id("i"), Seq(D(0), Sp, Lt, Sp, X(F.Id("i"))));
    private static Formula Nodes() => All(F.Id("i"), Seq(Open,
        X(F.Id("i")), Sp, Eq, Sp, L, Sp, Lor, Sp, X(F.Id("i")), Sp, Eq, Sp, U, Close));
    private static Formula Prototype() => Seq(
        Exists, Sp, F.Id("j"), Colon, Sp, Call("Fin", K), Comma, Sp, Open,
        X(F.Id("j")), Sp, Eq, Sp, U, Sp, Land, Sp, Open,
        All(F.Id("i"), Seq(F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Implies, Sp,
            X(F.Id("i")), Sp, Eq, Sp, L)), Close, Close);
    private static Formula Attainment() => Seq(
        SumOver(Call("f", X(F.Id("i")))), Sp, Eq, Sp,
        Call("f", U), Plus, Open, K, Minus, D(1), Close, Call("f", L));
    private static Formula FunctionDefinition() => Seq(
        Call("f", F.Id("t")), Sp, Eq, Sp,
        Log, Open, D(1), Minus, Exp, Open, Minus, F.Id("t"), Close, Close);
    private static Formula RadiusNodes() => Seq(
        F.Id("r"), Sp, Eq, Sp, Sqrt, Grp(Frac, Grp(V), Grp(K, Open, K, Minus, D(1), Close)), Comma, Sp,
        L, Sp, Eq, Sp, M, Minus, F.Id("r"), Comma, Sp,
        U, Sp, Eq, Sp, M, Plus, Open, K, Minus, D(1), Close, F.Id("r"));
    private static Formula MomentDefinitions() => Seq(
        M, Sp, Eq, Sp, Frac, Grp(SumOver(X(F.Id("i")))), Grp(K), Comma, Sp,
        V, Sp, Eq, Sp, SumOver(Square(Seq(X(F.Id("i")), Minus, M))), Comma, Sp, RadiusNodes());

    private static Formula LeftFormula() => Disp(Seq(
        Forall, Sp, F.Id("x"), Comma, L, Comma, U, Colon, Sp, Call("Real"), Comma, Sp,
        Forall, Sp, F.Id("g"), Colon, Sp, Call("Real"), Sp, To, Sp, Call("Real"), Comma, Sp, Open,
        F.Id("x"), Sp, Lt, Sp, L, Sp, Land, Sp, L, Sp, Lt, Sp, U, Sp, Land, Sp,
        Call("ContDiff", Call("Real"), D(3), F.Id("g")), Sp, Land, Sp,
        Call("g", L), Sp, Eq, Sp, D(0), Sp, Land, Sp, Call("g", U), Sp, Eq, Sp, D(0), Sp, Land, Sp,
        Call("deriv", F.Id("g"), L), Sp, Eq, Sp, D(0), Sp, Land, Sp, Open,
        Forall, Sp, F.Id("t"), Sp, InMacro, Sp, Open, F.Id("x"), Comma, U, Close, Comma, Sp,
        D(0), Sp, Lt, Sp, Call("iteratedDeriv", D(3), F.Id("g"), F.Id("t")), Close, Close,
        Sp, Implies, Sp, Call("g", F.Id("x")), Sp, Lt, Sp, D(0)));

    private static Formula EqualityFormula() => Disp(Seq(
        Forall, Sp, K, Colon, Sp, Call("Nat"), Comma, Sp, VectorQuantifier(Forall), Open,
        D(2), Sp, Le, Sp, K, Sp, Land, Sp, Open, Positive(), Close, Sp, Land, Sp,
        D(0), Sp, Lt, Sp, V, Close, Sp, Implies, Sp, Open,
        Open, Attainment(), Sp, Iff, Sp, Open, Nodes(), Close, Close, Sp, Land, Sp,
        Open, Open, Nodes(), Close, Sp, Implies, Sp, Open, Prototype(), Close, Close, Close));

    private static Formula ZeroFormula() => Disp(Seq(
        Forall, Sp, K, Colon, Sp, Call("Nat"), Comma, Sp, VectorQuantifier(Forall),
        V, Sp, Eq, Sp, D(0), Sp, Implies, Sp, Open,
        Open, All(F.Id("i"), Seq(X(F.Id("i")), Sp, Eq, Sp, M)), Close, Sp, Land, Sp,
        L, Sp, Eq, Sp, M, Sp, Land, Sp, U, Sp, Eq, Sp, M, Sp, Land, Sp, Attainment(), Close));

    private static Formula SharpnessFormula() => Disp(Seq(
        Forall, Sp, K, Colon, Sp, Call("Nat"), Comma, Sp,
        Forall, Sp, M, Comma, V, Colon, Sp, Call("Real"), Comma, Sp, Open,
        D(2), Sp, Le, Sp, K, Sp, Land, Sp, D(0), Sp, Lt, Sp, M, Sp, Land, Sp,
        D(0), Sp, Le, Sp, V, Sp, Land, Sp, V, Sp, Lt, Sp,
        K, Open, K, Minus, D(1), Close, Square(M), Close, Sp, Implies, Sp,
        VectorQuantifier(Exists), Open, Open, Positive(), Close, Sp, Land, Sp,
        SumOver(X(F.Id("i"))), Sp, Eq, Sp, K, M, Sp, Land, Sp,
        SumOver(Square(Seq(X(F.Id("i")), Minus, M))), Sp, Eq, Sp, V, Sp, Land, Sp,
        SumOver(Square(X(F.Id("i")))), Sp, Eq, Sp, K, Square(M), Plus, V, Sp, Land, Sp,
        Open, Attainment(), Close, Sp, Land, Sp, Open, Prototype(), Close, Close));
}
