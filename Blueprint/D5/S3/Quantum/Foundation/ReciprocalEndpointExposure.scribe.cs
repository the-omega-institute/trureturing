using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ReciprocalEndpointExposureDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula R => Seq(Mathbb, Grp(V("R")));

    public DocumentDefinition Create()
    {
        Formula v = V("V"), cone = V("C"), u = V("u"), p = V("p"), x = V("x"), y = V("y"), h = V("h");
        Formula dual = C("LinearMap", R, v), k = C("base", cone, u), pure = C("pure", cone, u);
        Formula complement = new Formula.Binary(u, FormulaBinaryOperator.Subtract, h);
        Formula zero = new Formula.SetBuilder(y, y, And(In(y, k), Eq(App(h, y), D(0))));
        Formula one = new Formula.SetBuilder(y, y, And(In(y, k), Eq(App(complement, y), D(1))));
        Formula singleton = new Formula.SetLiteral([p]);
        Formula result = Ex("h", dual, And(C("proper", cone, u, h), And(Eq(zero, singleton),
            And(C("confirms", cone, u, p, complement), And(Eq(one, singleton), C("IsExposed", R, k, singleton))))));
        Formula premise = And(C("IsClosed", cone), And(
            All("x", v, Imp(And(In(x, cone), Seq(x, Neq, Sp, D(0))), Seq(D(0), F.Lt, Sp, App(u, x)))),
            Eq(C("span", R, cone), C("top", C("Submodule", R, v)))));
        Formula statement = All("V", V("Type"), Seq(
            Seq(OpenBracket, C("NormedAddCommGroup", v), CloseBracket),
            Seq(OpenBracket, C("NormedSpace", R, v), CloseBracket),
            Seq(OpenBracket, C("FiniteDimensional", R, v), CloseBracket),
            All("C", C("PointedCone", R, v), All("u", dual,
                Imp(premise, All("p", pure, Imp(
                    All("x", pure, Le(C("comparison", cone, u, p, x), C("comparison", cone, u, x, p))), result)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "One-sided pure endpoint comparison exposes the original endpoint.",
            H("Original reciprocal endpoint exposure"), Blocks(
                Paragraph(Text("Let V be an arbitrary finite dimensional real normed space, C its original closed pointed generating convex cone, and u an original linear functional strictly positive on every nonzero element of C. The original normalized base is K={x in C:u(x)=1}; P is all of ext(K). An original proper effect is a linear f satisfying 0<=f<=u on every cone vector. The original comparison T_p(y) is the infimum of f(y) over ALL proper f with f(p)=1. Every linear functional is continuous in finite dimension, so the continuous-dual representation used in the proof preserves this entire effect domain.")),
                Describe.Lean(DescribeId.Create("reciprocal-endpoint-exposure"),
                    DeclarationHandle.Create("D5/S3/Quantum/Foundation/ReciprocalEndpointExposure.reciprocal_endpoint_exposure"),
                    H("A single endpoint and its complete original fibres"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Fix any original pure p and assume only T_p(x)<=T_x(p) for every original pure x. There is one actual original proper linear h whose zero fibre in the WHOLE K is {p}. Its actual proper complement u-h confirms p and has value-one fibre {p}; that singleton is an exposed subset of the original K. No exclusion-ball, weak-pair, global reciprocity, least-effect, spectrality or compact-pure-set premise is used. The theorem also covers a singleton K and dimension one. Existence of the normalized point already rules out a zero carrier, so an extra nontriviality hypothesis is unnecessary.")),
                        Paragraph(Text("Use the original ContinuousFrameSum.effects_compact theorem, whose hypotheses are only strict positivity and generation. Intersect the entire original effect interval with evaluation zero at p to obtain the compact convex set G. It contains zero. Choose h in its intrinsic interior, which is its interior relative to its affine span. Since zero belongs to G, that affine span is its linear span. A relative ball at h and a uniform norm bound on G provide a>0 with h-a g in G for every g in G. Thus g<=c h on the whole cone with c=1/a. Taking g=u-f for every original confirmer f of p and using the original infimum gives 1-c h(y)<=T_p(y) on all K. This is uniform scalar domination, without asserting that c h is proper or that a least confirmer exists. A zero span or zero h causes no division by a norm or by max(h).")),
                        Paragraph(Text("Suppose the zero fibre Z contains y different from p. A linear functional ell separates y and p. Let alpha=max_Z ell>ell(p), and A=max_K ell-min_K ell. For t=n+1 choose an extreme point x_n of the exposed maximum face of ell-t h. Exposed-face extreme-point transfer makes x_n an ORIGINAL pure point. Maximality gives t h(x_n)<=ell(x_n)-alpha and 0<=h(x_n)<=A/t. Let m=max_K(ell-t h), b=min_K(ell-t h), and d=m-b. Since ell is nonconstant on Z, d>0. Construct the actual original linear effect e=((ell-t h)-b u)/d. Original cone_bound proves 0<=e<=u on the entire cone; e(x_n)=1. The one-sided premise at x_n and the original infimum bound imply 1-c h(x_n)<=e(p). The identities d(1-e(p))=m-ell(p) and d<=A+t yield 0<alpha-ell(p)<=c(A h(x_n)+ell(x_n)-alpha).")),
                        Paragraph(Text("Compactness of K supplies a convergent subsequence x_n tending to v in K. The A/t bound gives h(v)=0, so v belongs to Z. Maximality gives ell(x_n)>=alpha, while the definition of alpha gives ell(v)<=alpha. Hence ell(v)=alpha, and the last positive lower bound tends to zero, a contradiction. The limit v need not be pure; the proof uses neither closedness of P nor continuity in the first comparison argument. Thus the entire zero fibre is {p}. On K, u=1 identifies the complement's entire value-one fibre with this zero fibre. The same complement is a continuous linear exposing functional. When K is a singleton, the contradiction branch is empty and the construction remains valid, including G={0}.")),
                        Paragraph(Text("This proves the complete Theorem 114.3 of Quantum Origin IX, through its original estimate IX114.12. The displayed equation IX114.3 belongs to a different statement. Under PR, apply this theorem directly at each p, using the corresponding equality as the one-sided inequality. This gives exposedness of every original pure point without introducing another mathematical declaration. Relative-interior existence, compact subsequence extraction, exposed-face transfer and finite-dimensional dual separation are pinned library tools; the uniform original zero-effect domination and the penalized comparison contradiction are the live new derivation. No literature priority or physical realization is asserted."))), DescribeRole.Theorem))));
    }
}
