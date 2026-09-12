using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class QuadraticMajorantEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quadratic tangent interpolant bounds the logarithmic function on positive support up to its upper node, and its finite weighted sum depends only on mass, mean, and centered second moment.",
        H("A quadratic majorant and weighted moment comparison"),
        Blocks(
            Paragraph(Text(
                "Write f(t)=log(1-exp(-t)). All scalar parameters and weights are real. The index set I is any finite type; its cardinality need not equal k. A weighted sum means the sum over all i in I of w(i) times the displayed value. The parameter k is a natural number, and W denotes the weighted centered second moment, without division by the total mass.")),
            Paragraph(Math(Disp(Seq(Call("f", T), Eq,
                Log, Open, D(1), Minus, Exp, Open, Minus, T, Close, Close)))),
            Describe.Lean(
                DescribeId.Create("quadratic-majorant-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorantCoeff"),
                H("The quadratic coefficient"),
                StatementSource.FromAuthor(Disp(Seq(A, Eq, Frac,
                    Grp(Fn(U), Minus, Fn(L), Minus, Df(L), Open, U, Minus, L, Close),
                    Grp(Square(Seq(U, Minus, L)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real nodes L and H, this total real expression defines a. Its interpolation and sign properties below assume 0<L<H, so the denominator is strictly positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-majorant-polynomial"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant"),
                H("The tangent interpolant"),
                StatementSource.FromAuthor(Disp(Seq(P(T), Eq, Fn(L), Plus,
                    Df(L), Open, T, Minus, L, Close, Plus, A, Square(Seq(T, Minus, L))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real L, H, and t, define P(t) by the displayed formula, with a the coefficient above. It is quadratic in t and has derivative f'(L) at L."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("logarithmic-strict-tangent-estimate"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.logValue_sub_lt_tangent"),
                H("The strict tangent estimate"),
                StatementSource.FromAuthor(Disp(ImpliesFrom(NodeDomain,
                    Seq(Fn(U), Minus, Fn(L), Lt, Df(L), Open, U, Minus, L, Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume 0<L<H. The mean value theorem supplies c strictly between L and H whose derivative equals the secant slope. The first derivative of f strictly decreases on the positive half-line, since its second derivative is negative. Thus the secant slope is strictly less than f'(L); multiplication by H-L gives the estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant-coefficient-negative"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant_coeff_neg"),
                H("The coefficient is negative"),
                StatementSource.FromAuthor(Disp(ImpliesFrom(NodeDomain, Seq(A, Lt, D(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<L<H, the strict tangent estimate makes the numerator negative, and the squared distance in the denominator is positive. Hence a<0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant-interpolation-nodes"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant_at_nodes"),
                H("Equality at both nodes"),
                StatementSource.FromAuthor(Disp(ImpliesFrom(Seq(L, Lt, U),
                    Seq(P(L), Eq, Fn(L), Sp, Land, Sp, P(U), Eq, Fn(U))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real L<H, substitution gives P(L)=f(L). At H the quadratic coefficient cancels the squared node distance, giving P(H)=f(H). This equality requires only distinct ordered nodes, without a positivity assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-support-majorant"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.logValue_le_majorant"),
                H("The majorant on the positive interval"),
                StatementSource.FromAuthor(Disp(ImpliesFrom(Seq(NodeDomain, Sp, Land, Sp,
                    D(0), Lt, T, Sp, Le, Sp, U), Seq(Fn(T), Sp, Le, Sp, P(T))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume 0<L<H and 0<t<=H. The quadratic has zero third derivative, agrees with f in value and derivative at L, and agrees in value at H. The positive third derivative of f gives the Hermite majorant. The interval includes 0<t<L: the sign to the left of the double node follows from repeated mean value and Rolle arguments on the positive interval spanned by t, L, and H. At L and H equality holds. No bound beyond H is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-quadratic-three-moments"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_quadratic_sum"),
                H("A quadratic sum from three moments"),
                StatementSource.FromAuthor(Disp(Seq(SumOf(Call("p", X)), Eq,
                    Call("p", Seq(M, Plus, Open, K, Minus, D(1), Close, R)), Plus,
                    Open, K, Minus, D(1), Close, Call("p", Seq(M, Minus, R)), Plus,
                    F.Id("C"), Open, W, Minus, V, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here K, m, r, A, B, C, V, and W are arbitrary real numbers; weights may have either sign. Assume sum w(i)=K, sum w(i)x(i)=Km, sum w(i)(x(i)-m)^2=W, and V=K(K-1)r^2. Set p(t)=A+B(t-(m-r))+C(t-(m-r))^2. Then the displayed identity holds, with no positivity or cardinality requirement.")),
                    Paragraph(Text(
                        "The centered first moment is zero. Shifting the center from m to m-r gives weighted first moment Kr and weighted second moment W+Kr^2. Expanding p therefore gives KA+BKr+C(W+Kr^2). Evaluating at the prototype nodes m+(K-1)r and m-r, with masses one and K-1, yields the same expression plus C(V-W)."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the remaining statements, k is at least two, m>0, and 0<V<k(k-1)m^2. Set r=sqrt(V/(k(k-1))), L=m-r, and H=m+(k-1)r. These satisfy 0<L<H and V=k(k-1)r^2. The reference envelope is psiK(k,m,V)=f(H)+(k-1)f(L). Assume sum w(i)=k, sum w(i)x(i)=km, and sum w(i)(x(i)-m)^2=W.")),
            Describe.Lean(
                DescribeId.Create("weighted-majorant-exact-sum"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_majorant_sum"),
                H("The exact majorant sum"),
                StatementSource.FromAuthor(Disp(Seq(SumOf(P(X)), Eq, Corrected))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the reference domain and three moment equalities, apply the weighted quadratic identity with A=f(L), B=f'(L), and C=a. Interpolation replaces P(H)+(k-1)P(L) by psiK(k,m,V). The exact sum identity permits signed weights and arbitrary real support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-logarithmic-majorant-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_majorant_bound"),
                H("The weighted logarithmic bound"),
                StatementSource.FromAuthor(Disp(Seq(SumOf(Fn(X)), Sp, Le, Sp, Corrected))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In addition to the reference domain and moment equalities, assume every weight is nonnegative and every support point satisfies 0<x(i)<=H. Multiplying f(x(i))<=P(x(i)) by w(i), summing, and using the exact majorant sum gives the bound. The weighted variance W is not required to be in the domain of psiK(k,m,W); only the reference variance V appears as an envelope argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-envelope-variance-floor"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_le_psiK_of_variance_ge"),
                H("A variance floor removes the correction"),
                StatementSource.FromAuthor(Disp(ImpliesFrom(Seq(V, Sp, Le, Sp, W),
                    Seq(SumOf(Fn(X)), Sp, Le, Sp, Psi)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under all assumptions of the weighted logarithmic bound, additionally assume V<=W. Since a<0, the correction a(W-V) is nonpositive, so the weighted logarithmic sum is at most psiK(k,m,V). Equality of the variances is allowed."))),
                DescribeRole.Theorem))));

    private static Formula A => F.Id("a");
    private static Formula K => F.Id("K");
    private static Formula M => F.Id("m");
    private static Formula R => F.Id("r");
    private static Formula T => F.Id("t");
    private static Formula L => F.Id("L");
    private static Formula U => F.Id("H");
    private static Formula V => F.Id("V");
    private static Formula W => F.Id("W");
    private static Formula X => Call("x", F.Id("i"));
    private static Formula Fn(Formula t) => Call("f", t);
    private static Formula Df(Formula t) => Call("deriv", F.Id("f"), t);
    private static Formula P(Formula t) => Call("P", t);
    private static Formula Square(Formula t) => Seq(Open, t, Close, Caret, Grp(D(2)));
    private static Formula SumOf(Formula t) => Seq(Sum, Underscore,
        Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Call("w", F.Id("i")), Sp, t);
    private static Formula ImpliesFrom(Formula premise, Formula result) => Seq(
        Open, premise, Close, Sp, Implies, Sp, result);
    private static Formula NodeDomain => Seq(D(0), Lt, L, Lt, U);
    private static Formula Psi => Call("psiK", F.Id("k"), M, V);
    private static Formula Corrected => Seq(Psi, Plus, A, Open, W, Minus, V, Close);
}
