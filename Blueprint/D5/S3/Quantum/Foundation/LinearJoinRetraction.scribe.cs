using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class LinearJoinRetractionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/LinearJoinRetraction.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, F.Le, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula E => C("EuclideanSpace", R, V("J"));
    private static Formula Hm => C("HermitianMat", V("J"), R);
    private static Formula Tr(Formula x) => C("trace", x);
    private static Formula Rank(Formula x) => C("rankOne", x);
    private static Formula Comp(Formula l, Formula p, Formula x) => C("comparison", C("sectionCone", l), C("traceUnit", l), p, x);
    private static Formula Proper(Formula l, Formula f) => C("proper", C("sectionCone", l), C("traceUnit", l), f);
    private static Formula Confirm(Formula l, Formula p, Formula f) => And(Proper(l, f), Eq(App(f, p), D(1)));

    private static Formula G2(Formula l) => All("p", C("pureRanks", l),
        All("q", C("pureRanks", l), All("r", C("pureRanks", l), Imp(
            And(Eq(Comp(l, V("p"), V("q")), D(0)), Eq(Comp(l, V("p"), V("r")), D(0))),
            Eq(Comp(l, V("p"), C("midpoint", V("q"), V("r"))), D(0))))));

    public DocumentDefinition Create()
    {
        Formula l = V("L"), y = V("Y"), z = V("Z"), u = V("U"), w = V("W"), v = V("v");
        Formula s = C("inter", u, w), j = V("j"), x = V("X"), p = V("p"), q = V("q"), r = V("r");
        Formula f = V("f"), g = V("g"), b = V("b"), ly = C("sideSpace", b), cy = C("sideCone", b), ub = C("sideVectorSpace", b);
        Formula dual = C("LinearMap", R, l, R), localDual = C("LinearMap", R, ly, R);
        Formula rog = All("X", Hm, Imp(In(x, l), Imp(Le(D(0), x),
            Ex("m", V("Nat"), Ex("v", C("Function", C("Fin", V("m")), E), And(
                All("j", C("Fin", V("m")), And(Ne(App(v, j), D(0)), In(Rank(App(v, j)), l))),
                Eq(x, C("sum", C("Fin", V("m")), C("rankOneFamily", v)))))))));
        Formula rays = All("v", E, Imp(Ne(v, D(0)),
            Iff(In(Rank(v), l), Or(In(v, y), In(v, z)))));
        Formula overlap = All("v", E, Iff(And(In(v, y), In(v, z)), And(Ne(v, D(0)), In(v, s))));
        Formula assumptions = And(In(D(1), l), And(rog, And(rays, And(overlap,
            And(Eq(C("span", R, y), u), And(Eq(C("span", R, z), w),
            And(Eq(C("sup", u, w), C("top", E)), And(C("omitsZero", y), C("omitsZero", z)))))))));
        Formula support = All("X", Hm, And(
            Iff(In(x, cy), And(In(x, l), And(Le(D(0), x), C("rangeContained", x, ub)))),
            Iff(In(x, cy), And(In(x, ly), Le(D(0), x)))));
        Formula extension = All("g", localDual, Imp(Proper(ly, g), And(
            Proper(l, C("compose", g, V("R"))), Eq(C("restrict", C("compose", g, V("R")), ly), g))));
        Formula onto = All("g", localDual, Imp(Proper(ly, g), Ex("f", dual,
            And(Proper(l, f), Eq(C("restrict", f, ly), g)))));
        Formula retract = Ex("R", C("LinearMap", R, l, ly), And(
            All("X", l, Eq(App(V("R"), x), C("congruence", C("matrix", b), x))), And(
            All("X", ly, Eq(App(V("R"), x), x)), And(
            All("X", l, Imp(Le(D(0), x), And(In(App(V("R"), x), cy), Le(Tr(App(V("R"), x)), Tr(x))))), extension))));
        Formula attained = All("p", ly, All("X", ly, Imp(Eq(Tr(p), D(1)), Imp(Le(D(0), x),
            Ex("g", localDual, And(Confirm(ly, p, g), Eq(App(g, x), Comp(ly, p, x))))))));
        Formula zero = All("p", ly, All("X", ly, Imp(Eq(Tr(p), D(1)), Imp(Le(D(0), x),
            Iff(Eq(Comp(ly, p, x), D(0)), Ex("g", localDual, And(Confirm(ly, p, g), Eq(App(g, x), D(0)))))))));
        Formula pure = Eq(C("extremePoints", R, C("base", ly)), C("pureRanks", ly));
        Formula pureLift = All("p", C("pureRanks", ly), In(p, C("pureRanks", l)));
        Formula exact = All("p", ly, All("X", ly, Eq(Comp(l, p, x), Comp(ly, p, x))));
        Formula g2 = Imp(G2(l), G2(ly));
        Formula side = And(support, And(C("ROG", ly), And(pure, And(pureLift,
            And(retract, And(onto, And(exact, And(attained, And(zero, g2)))))))));
        Formula statement = All("J", V("Type"), Seq(
            OpenBracket, C("Fintype", V("J")), CloseBracket, Sp,
            OpenBracket, C("DecidableEq", V("J")), CloseBracket, Sp,
            All("L", C("Submodule", R, Hm), All("Y", C("Set", E), All("Z", C("Set", E),
            All("U", C("Submodule", R, E), All("W", C("Submodule", R, E),
            Imp(assumptions, All("b", V("Bool"), side)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual matrix congruence retractions of full real ROG PSD sections, with inherited trace, all supported positive matrices, the entire proper interval and native comparison.",
            H("Real ROG projective joins"), Blocks(
                Paragraph(Text("J is an arbitrary finite index type with decidable equality. E is the original normalized real Euclidean vector space, and H is HermitianMat J R, hence the real symmetric matrices. L is a real subspace of H containing the identity. Its cone is exactly L intersect PSD, its unit is trace, and its entire base consists of the trace-one PSD elements. ROG means that every original positive X is a finite sum of nonzero vv-transpose in L. The projective sets Y and Z are represented by their full inverse images of nonzero vectors: zero is omitted, their union is exactly all nonzero v with vv-transpose in L, their spans are U and W, U+W=E, and their intersection is all nonzero vectors of S=U intersect W.")),
                Paragraph(Text("For b=false take Y,U, and for b=true take Z,W. sideSpace(b) is the real span of every vv-transpose on that side, and sideCone(b) is the conic hull of those same matrices. rangeContained(X,U) means the entire image of X lies in U. The original trace restricts to each side. There is no assumption that the side identity projector lies in sideSpace.")),
                Describe.Lean(DescribeId.Create("real-join-retractions"), DeclarationHandle.Create(Owner + "real_join_retractions"),
                    H("Both original supported sections and their entire effects"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The displayed hypotheses are precisely RealJoin. The conclusion is SideConclusion for it and its exchange. Both sides are the entire supported original PSD cones and real ROG sections. Their normalized pure points equal the extreme points of the full local base and include into the original pure set. The actual linear R maps are restrictions of congruence X maps to T X T-transpose, fix the whole side span, are positive on every original positive X, and decrease its original trace. Every local proper functional g extends as g composed with this R, including its upper bound by the original unit; restriction is onto the whole local interval.")),
                        Paragraph(Text("For the Y side, T fixes U and restricts on W to Euclidean orthogonal projection onto S. The two prescriptions agree on S and therefore glue. For the Z side exchange U and W. No orthogonality between U and W and no global contraction bound on T is assumed. On each Y generator the vector is fixed; each Z generator is sent into S, where every nonzero projective ray belongs to both sides. Orthogonal projection decreases its squared norm, which is the rank one trace. The same original ROG decomposition proves positivity and the trace bound for every positive matrix. Identity membership ensures that original positives span L, so congruence restricts from all of L into the side span.")),
                        Paragraph(Text("For X=sum_j v(j)v(j)-transpose, each positive summand is below X. The existing PSD kernel order theorem and orthogonal-complement identity place each nonzero v(j) in the range of X. Thus if X is supported on U, every decomposition vector lies in U. A Z vector in U lies in S and hence in Y. This proves the supported-cone identity without assuming that the original decomposition already had side-supported vectors. It also gives the local ROG decomposition.")),
                        Paragraph(Text("comparison(L,p,X) is the infimum of f(X) over every real linear functional f on L with 0<=f(A)<=trace(A) for all PSD A in L and f(p)=1. The complete sets of confirming readings agree locally and globally, so exact comparison holds for every local p and X, including every mixed state. On the original section, identity majorization bounds the norm of every proper functional by card(J). The closed full proper interval is consequently compact in the finite dimensional dual. The confirming subset at trace(p)=1 is nonempty because trace itself confirms p, so the infimum is attained. Restriction supplies the corresponding local minimum, even when the side identity projector is absent.")),
                        Paragraph(Text("nativeG2(L) quantifies every p,q,r in the whole normalized native rank one set: comparison(p,q)=0 and comparison(p,r)=0 imply comparison(p,(q+r)/2)=0. Each zero is equivalent to one full proper effect confirming p at one and vanishing at the indicated state. The two antecedents may have different effects; minimum attainment gives one common confirming effect for the midpoint conclusion. Local pure inclusion and exact comparison apply original nativeG2 and transport the conclusion back. This uses the original pure and mixed domain and the entire proper interval.")),
                        Paragraph(Text("All coordinates use the given normalized real trace carrier. Transport to an earlier arbitrary strictly positive unit requires the separate original unit-preserving cone isomorphism and its full dual transport. The statements here provide mathematical maps and do not assert physical preparation or implementation of those maps. No classification of later real ROG branches and no literature priority is asserted."))), DescribeRole.Theorem))));
    }
}
