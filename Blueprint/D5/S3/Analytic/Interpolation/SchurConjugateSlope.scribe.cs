using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class SchurConjugateSlopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Interpolation/SchurConjugateSlope.";
    private static Formula G => F.Id("g");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula Z => F.Id("z");
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Functions => Seq(C, Sp, To, Sp, C);
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Eqn(Formula l, Formula r) => Seq(l, Sp, Eq, Sp, r);
    private static Formula S(Formula a) => Call("S", G, a, B);
    private static Formula I(Formula a) => Call("interpolant", G, a, B);
    private static Formula Hypotheses => Seq(Call("Entire", G), Sp, Land, Sp,
        D(0), Sp, Lt, Sp, B, Sp, Land, Sp,
        new Formula.Power(A, D(2)), Sp, Plus, Sp, new Formula.Power(B, D(2)), Sp, Le, Sp, D(1));
    private static Formula Bound(Formula l, Formula r) => Seq(Call("norm", Seq(l, Minus, r)),
        Sp, Le, Sp, Call("abs", A), Call("M", G));
    private static Formula Transport(Formula conclusion) => Disp(All("g", Functions,
        All("a", R, All("b", R, Seq(Hypotheses, Sp, Implies, Sp, conclusion)))));

    private static Formula U => Call("uniformError", A, B);
    private static Formula V => Call("V", G, A, B);
    private static Formula W => Call("W", A, B);
    private static Formula Interval => Call("Icc", Seq(Minus, D(1)), D(1));
    private static Formula Sharp => Seq(D(1), Plus, Call("abs", A));
    private static Formula Error(Formula x) => Call("actualError", G, A, B, x);
    private static Formula On(string v, Formula domain, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(v), Sp, InMacro, Sp, domain, Comma, Sp, body, Close);
    private static Formula Some(string v, Formula domain, Formula body) =>
        Seq(Open, Exists, Sp, F.Id(v), Sp, InMacro, Sp, domain, Comma, Sp, body, Close);
    private static Formula InnerAttainment => Seq(
        Call("Nonempty", V), Sp, Land, Sp, Call("BddAbove", V), Sp, Land, Sp,
        Some("z", Call("closedBall", D(0), D(1)), Eqn(Call("M", G), Call("normSecondDerivative", G, Z))),
        Sp, Land, Sp, Some("x", Interval, Eqn(Call("sSup", V), Error(F.Id("x")))));
    private static Formula QuadraticAttainment => Some("g", Call("E"), Seq(
        Eqn(G, Call("quadratic")), Sp, Land, Sp, Eqn(Call("M", G), D(1)), Sp, Land, Sp,
        Eqn(S(A), A), Sp, Land, Sp,
        All("x", R, Eqn(Error(F.Id("x")), Call("abs", Seq(F.Id("x"), Minus, A)))),
        Sp, Land, Sp, Eqn(Call("sSup", V), U), Sp, Land, Sp,
        Open, D(0), Sp, Le, Sp, A, Sp, Implies, Sp, Eqn(Error(Seq(Minus, D(1))), U), Close,
        Sp, Land, Sp, Open, A, Sp, Le, Sp, D(0), Sp, Implies, Sp, Eqn(Error(D(1)), U), Close,
        Sp, Land, Sp, Some("x", Interval,
            Eqn(Call("nodalDerivativeNorm", A, B), Call("normNodalDerivative", A, B, F.Id("x"))))));
    private static Formula CompleteStatement => Disp(All("a", R, All("b", R, Seq(
        D(0), Sp, Lt, Sp, B, Sp, Land, Sp, new Formula.Power(A, D(2)), Plus,
        new Formula.Power(B, D(2)), Sp, Le, Sp, D(1), Sp, Implies, Sp,
        Eqn(U, Sharp), Sp, Land, Sp,
        Eqn(U, Seq(Frac, Grp(D(1)), Grp(D(2)), Call("nodalDerivativeNorm", A, B))),
        Sp, Land, Sp, On("g", Call("E"), On("x", Interval,
            Seq(Error(F.Id("x")), Sp, Le, Sp, Sharp))), Sp, Land, Sp,
        Call("Nonempty", Call("E")), Sp, Land, Sp, On("g", Call("E"), InnerAttainment),
        Sp, Land, Sp, Call("Nonempty", W), Sp, Land, Sp, Call("BddAbove", W),
        Sp, Land, Sp, QuadraticAttainment))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire complex functions obey horizontal transport of their actual conjugate-pair divided differences on the closed unit disk.",
        H("Horizontal transport of conjugate-pair slopes"),
        Blocks(
            Entry("norm", "diskNorm", "The original closed-disk norm",
                Disp(All("g", Functions, Eqn(Call("M", G), Call("sSup", Call("normSecondDerivativeImageOfClosedUnitDisk", G))))),
                "M(g) is the real supremum of the norms of the complex second derivative over the closed unit disk. For entire g the image is nonempty and bounded, by continuity and compactness.", DescribeRole.Definition),
            Entry("slope", "slope", "The actual divided difference",
                Disp(All("g", Functions, All("a", R, All("b", R,
                    Eqn(S(A), Seq(Frac, Grp(Call("g", Seq(A, Plus, B, F.Id("i"))), Minus,
                        Call("g", Seq(A, Minus, B, F.Id("i")))), Grp(D(2), B, F.Id("i")))))))),
                "The two values are evaluated independently at a+ib and a-ib. No relation between those values is assumed. The denominator is nonzero when b>0.", DescribeRole.Definition),
            Entry("interpolant", "interpolant", "The original two-node Lagrange expression",
                Disp(All("g", Functions, All("a", R, All("b", R, All("z", C,
                    Eqn(Call("interpolant", G, A, B, Z), Seq(
                        Frac, Grp(Z, Minus, Open, A, Minus, B, F.Id("i"), Close), Grp(D(2), B, F.Id("i")),
                        Call("g", Seq(A, Plus, B, F.Id("i"))), Plus,
                        Frac, Grp(Open, A, Plus, B, F.Id("i"), Close, Minus, Z), Grp(D(2), B, F.Id("i")),
                        Call("g", Seq(A, Minus, B, F.Id("i")))))))))),
                "For b>0 the displayed affine polynomial interpolates g at the distinct conjugate nodes. The formula uses complex division.", DescribeRole.Definition),
            Entry("nodal", "nodalPolynomial", "The actual nodal polynomial",
                Disp(All("a", R, All("b", R, All("z", C,
                    Eqn(Call("nodalPolynomial", A, B, Z), Seq(
                        Seq(Open, Z, Minus, Open, A, Plus, B, F.Id("i"), Close, Close),
                        Seq(Open, Z, Minus, Open, A, Minus, B, F.Id("i"), Close, Close))))))),
                "The polynomial is the original product (z-(a+ib))(z-(a-ib)). Its derivative is 2(z-a), including for every nonreal unit-circle pair.", DescribeRole.Definition),
            Entry("nodal-norm", "nodalDerivativeNorm", "The original nodal derivative norm",
                Disp(All("a", R, All("b", R, Eqn(Call("nodalDerivativeNorm", A, B),
                    Call("sSup", Call("nodalDerivativeNormValues", A, B)))))),
                "The real supremum is over the norms of the actual complex derivative at real x in the closed interval [-1,1]. The value set is nonempty and bounded and its supremum is attained.", DescribeRole.Definition),
            Entry("derivative", "interpolant_deriv", "The Lagrange derivative",
                Disp(All("g", Functions, All("a", R, All("b", R, All("z", C,
                    Eqn(Call("deriv", I(A), Z), S(A))))))),
                "At every complex test point the derivative is the original divided difference. This identity is algebraic and does not require analyticity of g.", DescribeRole.Theorem),
            Entry("transport", "slope_transport", "Horizontal transport for every entire function",
                Transport(Bound(S(A), S(D(0)))),
                "Let g be entire, let a and b be real, b>0 and a squared plus b squared at most one. Then |S(g,a,b)-S(g,0,b)| <= |a| M(g). Both signs of a and all closed-segment endpoints are included. The derivative of g is M(g)-Lipschitz on the closed disk. At each horizontal coordinate s between zero and a, the vertical divided difference of g prime therefore has norm at most M(g). Applying the real mean value bound to the actual slope gives the estimate. There is no real-coefficient hypothesis and no use of conjugation of function values.", DescribeRole.Theorem),
            Entry("class", "entireClass", "The original entire-function class",
                Disp(All("g", Functions, Seq(Call("member", G, Call("E")), Sp, Iff, Sp,
                    Call("Entire", G), Sp, Land, Sp, Call("M", G), Sp, Le, Sp, D(1)))),
                "E consists of all complex-coefficient entire functions g with M(g) at most one. The norm is on the original closed disk.", DescribeRole.Definition),
            Entry("inner", "innerValues", "The inner value set",
                Disp(All("g", Functions, All("a", R, All("b", R,
                    Eqn(Call("V", G, A, B), Call("image", Call("actualError", G, A, B),
                        Call("Icc", Seq(Minus, D(1)), D(1)))))))),
                "V(g,a,b) is the image of the closed real interval [-1,1] under x mapped to the norm of g prime at x minus the actual Lagrange derivative at x.", DescribeRole.Definition),
            Entry("outer", "outerValues", "The outer value set",
                Disp(All("a", R, All("b", R, Eqn(Call("W", A, B),
                    Call("image", Call("innerSupremum", A, B), Call("E")))))),
                "W(a,b) is the image of the original entire-function class under g mapped to the real supremum of V(g,a,b).", DescribeRole.Definition),
            Entry("uniform", "uniformError", "The original nested uniform supremum",
                Disp(All("a", R, All("b", R, Eqn(Call("uniformError", A, B),
                    Call("sSup", Call("W", A, B)))))),
                "The supremum over g is outside the supremum over x, exactly as in Definition 9.1. No limit or supremum is interchanged.", DescribeRole.Definition),
            Entry("bounded", "original_suprema_bounded", "Bounded original suprema and an actual quadratic witness",
                Disp(All("a", R, All("b", R, Seq(
                    D(0), Sp, Lt, Sp, B, Sp, Land, Sp,
                    new Formula.Power(A, D(2)), Plus, new Formula.Power(B, D(2)), Sp, Le, Sp, D(1),
                    Sp, Implies, Sp, Call("Nonempty", Call("E")), Sp, Land, Sp,
                    Open, All("g", Functions, Seq(Call("member", G, Call("E")), Sp, Implies, Sp,
                        Call("Nonempty", Call("V", G, A, B)), Sp, Land, Sp,
                        Call("BddAbove", Call("V", G, A, B)), Sp, Land, Sp,
                        Open, Exists, Sp, Z, Sp, InMacro, Sp, Call("closedBall", D(0), D(1)), Comma, Sp,
                        Eqn(Call("M", G), Call("normSecondDerivative", G, Z)), Close, Sp, Land, Sp,
                        Exists, Sp, F.Id("x"), Sp, InMacro, Sp, Call("Icc", Seq(Minus, D(1)), D(1)), Comma, Sp,
                        Eqn(Call("sSup", Call("V", G, A, B)), Call("actualError", G, A, B, F.Id("x"))))), Close, Sp, Land, Sp,
                    Call("Nonempty", Call("W", A, B)), Sp, Land, Sp,
                    Call("BddAbove", Call("W", A, B)), Sp, Land, Sp,
                    D(1), Plus, Call("abs", A), Sp, Le, Sp, Call("uniformError", A, B), Sp, Land, Sp,
                    Call("uniformError", A, B), Sp, Le, Sp, D(2), Sp, Land, Sp,
                    Exists, Sp, G, Sp, InMacro, Sp, Call("E"), Comma, Sp,
                    Eqn(G, Call("quadratic")), Sp, Land, Sp,
                    Eqn(Call("M", G), D(1)), Sp, Land, Sp, Eqn(S(A), A), Sp, Land, Sp,
                    Open, All("x", R, Eqn(Call("actualError", G, A, B, F.Id("x")),
                        Call("abs", Seq(F.Id("x"), Minus, A)))), Close, Sp, Land, Sp,
                    Call("sSup", Call("V", G, A, B)), Sp, Eq, Sp, D(1), Plus, Call("abs", A), Sp, Land, Sp,
                    Eqn(Call("nodalDerivativeNorm", A, B), Seq(D(2), Open, D(1), Plus, Call("abs", A), Close)),
                    Sp, Land, Sp, Eqn(Seq(Frac, Grp(D(1)), Grp(D(2)), Call("nodalDerivativeNorm", A, B)),
                        Seq(D(1), Plus, Call("abs", A))), Sp, Land, Sp,
                    Exists, Sp, F.Id("x"), Sp, InMacro, Sp, Call("Icc", Seq(Minus, D(1)), D(1)), Comma, Sp,
                    Eqn(Call("nodalDerivativeNorm", A, B), Call("normNodalDerivative", A, B, F.Id("x"))))))),
                "For every admissible a,b both original value sets are nonempty and bounded. For every member, compactness gives an actual point attaining the disk norm and an actual real point attaining the inner supremum. The existential witness is explicitly the entire quadratic quadratic(z)=z squared divided by two. It has disk norm one, slope a, error |x-a| and inner supremum 1+|a|. This value is attained at -1 for a nonnegative and at 1 for a nonpositive, with both endpoints when a=0. The actual nodal derivative norm is 2(1+|a|), so its half-norm is 1+|a|; a real endpoint attains the norm. The norm value set is nonempty and bounded. The coarse estimate uses the horizontal transport theorem and the imaginary-axis bound sqrt(1+b squared) M(g), whose sum with |a| M(g) is at most 2 M(g). This gives uniformError at most two. The following classification supplies the sharp upper estimate uniformError at most 1+|a|.", DescribeRole.Theorem),
            Entry("complete", "complete_classification", "The complete original uniform identity",
                CompleteStatement,
                "For every real a,b with b>0 and a squared plus b squared at most one, every member of the original arbitrary-complex entire class and every real x in the closed interval obey the sharp pointwise error bound 1+|a|. The original nested supremum equals 1+|a| and half the actual nodal derivative norm. The entire class and the inner and outer value sets are nonempty and bounded. Every entire member attains its disk norm and inner supremum on the original compact domains. The actual entire quadratic g(z)=z squared divided by two belongs to the original class, has disk norm one and slope a, and has error |x-a| for every real x. Its inner supremum equals the outer supremum, so it attains the outer optimization. The far endpoint -1 attains that value for a>=0 and the endpoint 1 does so for a<=0; both endpoints attain it at a=0. A real endpoint also attains the actual nodal derivative norm. To obtain the upper estimate, take h=g double prime and H=g prime minus g prime at zero. The actual vertical-segment FTC identifies the normalized primitive average with S(g,0,b)-g prime at zero. The sharp primitive bound gives |g prime(x)-S(g,0,b)|<=M(g). Actual horizontal transport adds |a|M(g). Multiplying by M(g)<=1 bounds each member and each point. The two suprema are then bounded in their original order; no limit is exchanged with a supremum. The quadratic gives the reverse inequality. All equalities and estimates use the closed admissibility inequality throughout, including b=1, x=-1, x=1 and every nonreal unit-circle conjugate pair.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("schur-conjugate-slope-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
