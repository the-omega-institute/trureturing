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
        Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
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
                        Frac, Grp(Z, Minus, Grp(A, Minus, B, F.Id("i"))), Grp(D(2), B, F.Id("i")),
                        Call("g", Seq(A, Plus, B, F.Id("i"))), Plus,
                        Frac, Grp(Grp(A, Plus, B, F.Id("i")), Minus, Z), Grp(D(2), B, F.Id("i")),
                        Call("g", Seq(A, Minus, B, F.Id("i")))))))))),
                "For b>0 the displayed affine polynomial interpolates g at the distinct conjugate nodes. The formula uses complex division.", DescribeRole.Definition),
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
                    Call("sSup", Call("V", G, A, B)), Sp, Eq, Sp, D(1), Plus, Call("abs", A))))),
                "For every admissible a,b both original value sets are nonempty and bounded. For every member, compactness gives an actual point attaining the disk norm and an actual real point attaining the inner supremum. The existential witness is explicitly the entire quadratic quadratic(z)=z squared divided by two. It has disk norm one, slope a, error |x-a| and inner supremum 1+|a|. This value is attained at -1 for a nonnegative and at 1 for a nonpositive, with both endpoints when a=0. A separate coarse estimate gives uniformError at most two. The sharp upper estimate uniformError at most 1+|a| remains unproved here; this theorem does not assert the full classification.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("schur-conjugate-slope-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
