using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatInterpolationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Observer/Linear/ReflectingHeatInterpolation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chebyshev interpolation at the reflecting heat rates",
        H("Chebyshev interpolation at the reflecting heat rates"),
        Blocks(
            Paragraph(Text("The rates qⱼ and weights bⱼ are those of the finite strip lower bound. For j in Fin(n−1), the angle θⱼ is π(j+1)/n. Write Qₙ for the full nodal polynomial and Qₙⱼ for the one with the j-th node omitted. The signed product of gaps is Dⱼ. The reflecting-path critical crossover proof uses these quantities in equations (11)–(12) and (35)–(38).")),
            Claim("reflecting-nodal-polynomial", "nodalPolynomial_eq_chebyshev",
                "Monic Chebyshev nodal polynomial", Nodal(),
                "The affine change of variables takes the Chebyshev roots to the reflecting rates. The leading coefficient becomes one."),
            Claim("reflecting-nodal-derivative", "abs_nodalDerivative",
                "Exact normalization at each node", Derivative(),
                "Differentiate the Chebyshev sine identity on the reflecting grid. The omitted node factor gives the derivative of the full polynomial at that node."),
            Claim("reflecting-nodal-uniform-factors", "uniform_nodal_factors",
                "Uniform bounds through both edge modes", Uniform(),
                "The sine chord bound controls the smallest sine and the distances to both endpoints of the spectral interval."),
            Claim("reflecting-endpoint-normalization", "endpoint_normalization",
                "Normalization with the physical endpoint weight", Endpoint(),
                "The relation between the squared sine and the physical squared weight cancels the nodal derivative as in equation (12). The endpoint estimates bound the resulting factor below uniformly."),
            Claim("reflecting-nodal-imaginary-growth", "norm_omittedPolynomial_eval",
                "Growth of the omitted polynomial on the imaginary axis", Growth(),
                "The second-kind polynomial expands as a finite geometric sum in the outer Joukowski root. Removing a node supplies the exact distance in the denominator, including at zero frequency."),
            Paragraph(Text("The Fourier-side interpolant is "),
                Math(Seq(App(Psi, Z), Eq, App(Omitted, Seq(I, Sp, Z)), Sp, App(M, Z))),
                Text(". At −iqₖ the omitted polynomial is evaluated at qₖ. Mathlib’s Lagrange.eval_nodal gives the product of gaps on the diagonal, and Lagrange.eval_nodal_at_node gives zero off the diagonal.")),
            Paragraph(Math(NodeValue(J, Seq(Gap, Sp, App(M, MinNode(J))))), Text(" and "),
                Math(Seq(K, Neq, Sp, J, Sp, Rightarrow, Sp, NodeValue(K, D(0)))), Text(".")),
            Claim("reflecting-interpolant-l2-bound", "momentInterpolant_L2_bound",
                "Square-integrable envelope for the moment interpolant", L2(),
                "The multiplier envelope has inverse radius to power n, while the omitted polynomial has radius to power n−1. The remaining inverse radius controls the linear factor in frequency. Squaring gives two integrable Cauchy kernels. Their integrals and the lower bound on qⱼ give the uniform squared-norm estimate."))));

    private static DocumentBlock Claim(string id, string declaration, string heading, Formula statement,
        string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(heading), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static Formula N => F.Id("n");
    private static Formula J => F.Id("j");
    private static Formula K => F.Id("k");
    private static Formula W => F.Id("w");
    private static Formula Z => F.Id("z");
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula I => F.Id("i");
    private static Formula M => F.Id("M");
    private static Formula Q(Formula index) => Sub(F.Id("q"), index);
    private static Formula Weight => Sub(F.Id("b"), J);
    private static Formula Gap => Sub(F.Id("D"), J);
    private static Formula Omitted => Sub(F.Id("Q"), Seq(N, Comma, J));
    private static Formula Psi => Sub(F.Psi, Seq(N, Comma, J));
    private static Formula RealLine => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula FracOf(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula AbsOf(Formula value) => new Formula.Absolute(value);
    private static Formula Par(params Formula[] parts) => Seq(Open, Seq(parts), Close);
    private static Formula NMinusOne => Seq(N, Minus, D(1));
    private static Formula FourOverNSq => FracOf(D(4), Pow(N, D(2)));
    private static Formula RootEquation => Seq(Zeta, Plus, Pow(Zeta, Seq(Minus, D(1))),
        Eq, I, Sp, Omega, Minus, D(2));
    private static Formula RootConditions => Seq(Zeta, Neq, Sp, D(0), Sp, Land, Sp,
        RootEquation, Sp, Land, Sp, D(1), Le, Sp, AbsOf(Zeta));
    private static Formula MinNode(Formula k) => Seq(Minus, I, Sp, Q(k));

    private static Formula Nodal() => Disp(Seq(
        App(Sub(F.Id("Q"), N), W), Eq,
        Prod, Underscore, Grp(K, InMacro, Sp, App(F.Id("Fin"), NMinusOne)), Sp,
        Par(W, Minus, Q(K)), Eq, App(Sub(F.Id("U"), NMinusOne), FracOf(Seq(W, Minus, D(2)), D(2)))));

    private static Formula Derivative() => Disp(Seq(AbsOf(Gap), Eq, FracOf(N,
        Seq(D(2), Sp, Pow(Par(App(Sin, Sub(Theta, J))), D(2))))));

    private static Formula Uniform() => Disp(Seq(FracOf(N, D(2)), Le, Sp, AbsOf(Gap), Le, Sp,
        FracOf(Pow(N, D(3)), D(8)), Sp, Land, Sp, FourOverNSq, Le, Sp, Q(J), Sp, Land, Sp,
        FourOverNSq, Le, Sp, D(4), Minus, Q(J)));

    private static Formula Endpoint() => Disp(Seq(FracOf(N, Seq(Weight, Sp, AbsOf(Gap))), Eq,
        Q(J), Sp, Weight, Sp, Land, Sp, FourOverNSq, Le, Sp, Q(J), Sp, Weight));

    private static Formula Growth() => Disp(Seq(RootConditions, Sp, Rightarrow, Sp,
        AbsOf(App(Omitted, Seq(I, Sp, Omega))), Le, Sp,
        FracOf(Seq(N, Sp, Pow(AbsOf(Zeta), NMinusOne)),
            Seq(Sqrt, Grp(Pow(Q(J), D(2)), Plus, Pow(Omega, D(2)))))));

    private static Formula NodeValue(Formula k, Formula value) => Seq(App(Psi, MinNode(k)), Eq, value);

    private static Formula L2() => Disp(Seq(
        App(Seq(Operatorname, Grp(F.Id("Measurable"))), Seq(M, Rvert, Underscore, Grp(RealLine))),
        Sp, Land, Sp, Par(Forall, Sp, Omega, Comma, Sp, Exists, Sp, Zeta, Comma, Sp,
            RootConditions, Sp, Land, Sp, AbsOf(App(M, Omega)), Le, Sp,
            FracOf(Seq(A, Par(D(1), Plus, B, Sp, AbsOf(Omega))), Pow(AbsOf(Zeta), N))),
        RowBreak, Rightarrow, Sp, Psi, InMacro, Sp,
        App(Pow(F.Id("L"), D(2)), RealLine), Sp, Land, Sp,
        Int, Underscore, Grp(RealLine), Sp,
        Pow(AbsOf(App(Psi, Omega)), D(2)), Sp, F.Id("d"), Sp, Omega, Le, Sp,
        D(2), Pow(Par(N, A), D(2)), Sp, Pi,
        Par(FracOf(Pow(N, D(2)), D(4)), Plus, D(2), Pow(B, D(2)))));
}
