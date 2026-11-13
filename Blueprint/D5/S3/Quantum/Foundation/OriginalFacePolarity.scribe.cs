using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalFacePolarityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalFacePolarity.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] xs) => xs.Length == 1 ? xs[0] : new Formula.Logic(xs[0], FormulaLogicOperator.And, And(xs[1..]));
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula NotIn(Formula a, Formula b) => C("not", In(a, b));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula K => C("base", V("C"), V("u"));
    private static Formula P => C("pure", V("C"), V("u"));
    private static Formula L => C("Line", V("C"), V("u"));
    private static Formula Sets => C("Set", V("V"));
    private static Formula Dp(Formula p) => C("exclusion", V("C"), V("u"), p);
    private static Formula Perp(Formula f) => C("zeroComplement", V("C"), V("u"), f);
    private static Formula Val(Formula x) => C("value", x);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula Singleton(Formula x) => new Formula.SetLiteral([x]);
    private static Formula Empty => new Formula.SetLiteral([]);
    private static Formula Face(Formula x) => And(C("Convex", R, x), C("IsExtreme", R, K, x));
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", V("V")), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, V("V")), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, V("V")), CloseBracket, Sp,
        All("C", C("PointedCone", R, V("V")), All("u", C("LinearMap", R, V("V"), R), body))));

    public DocumentDefinition Create()
    {
        Formula p = V("p"), q = V("q"), r = V("r"), f = V("F"), g = V("G"), x = V("x"), m = V("M"), l = V("L"), e = V("e"), b = V("b");
        Formula strict = All("x", V("V"), Imp(In(x, V("C")), Imp(Ne(x, D(0)), Seq(D(0), F.Lt, Sp, App(V("u"), x)))));
        Formula hypotheses = And(C("Nontrivial", V("V")), C("IsClosed", V("C")), strict,
            Eq(C("span", R, V("C")), C("top")), C("exclusionBalls", V("C"), V("u")), C("pairProper", V("C"), V("u")));
        Formula incidence = All("p", P, All("L", L, Iff(In(p, l), In(App(C("inverse", e), l), App(e, p)))));
        Formula endpoints = And(Eq(Perp(Empty), K), Eq(Perp(K), Empty),
            All("p", P, And(Eq(Perp(Singleton(Val(p))), Dp(p)), Eq(Perp(Dp(p)), Singleton(Val(p))))));
        Formula allFaces = And(All("F", Sets, Face(Perp(f))),
            All("F", Sets, Imp(Face(f), Eq(Perp(Perp(f)), f))),
            C("Antitone", C("zeroComplement", V("C"), V("u"))),
            All("F", Sets, All("G", Sets, Imp(And(Face(f), Face(g)),
                Iff(C("subset", f, g), C("subset", Perp(g), Perp(f)))))));
        Formula boundaries = And(All("p", P, All("b", C("ExclusionChart", V("C"), V("u"), p),
            Eq(C("inter", Dp(p), P), C("image", C("param", b), C("sphere", D(0), D(1)))))),
            All("L", L, All("M", L, Imp(Eq(C("inter", Val(l), P), C("inter", Val(m), P)), Eq(l, m)))));
        Formula intersections = All("L", L, All("M", L, Imp(Ne(l, m),
            Ex("r", P, Eq(C("inter", Val(l), Val(m)), Singleton(Val(r)))))));
        Formula plane = Imp(C("thickExclusionBalls", V("C"), V("u")),
            C("Nonempty", C("ProjectivePlane", P, L)));
        Formula full = And(C("Nonempty", P), Ex("e", C("Equiv", P, L), And(
            All("p", P, Eq(Val(App(e, p)), Dp(p))), intersections,
            All("p", P, NotIn(p, App(e, p))), incidence, endpoints, allFaces, boundaries, plane)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The original zero relation identifies every pure point with an entire nonpoint proper face, reverses the whole face order, and gives a projective plane when the exclusion balls have dimension at least two.",
            H("Original face polarity and the projective plane"), Blocks(
                Describe.Lean(DescribeId.Create("pure-pair-in-ball"), DeclarationHandle.Create("D5/S3/Quantum/Foundation/OriginalFacePolarity.pure_pair_in_ball"), H("Two original pure points in every exclusion ball"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every entire positive-dimensional exclusion ball contains two distinct original pure points. Compact convex faciality and Krein-Milman prevent its pure boundary from collapsing to one point."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("chart-boundary"), DeclarationHandle.Create("D5/S3/Quantum/Foundation/OriginalFacePolarity.chart_boundary"), H("Whole original pure boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The intersection of the entire exclusion face with all original pure states equals the image of the whole Euclidean unit sphere under its original ball chart."))), DescribeRole.Theorem),

                Paragraph(Text("Let V be a nonzero finite dimensional real normed vector space. C is the original closed generating pointed convex cone, and the real-linear functional u is strictly positive on C except at zero. K is the entire normalized base, P is the set of all its extreme points, and proper effects are all real-linear f satisfying 0<=f<=u on C. D(p) is the entire original mixed-state exclusion set. Every D(p) is an injective affine image of a whole closed unit ball of positive finite dimension; each entire minimal face of a distinct pure pair is proper. No finiteness or closedness of P, closedness premise on input faces, least effect, numerical reciprocity, common support, projectivity, self-duality, Jordan model or Born rule is assumed.")),
                Def("Line", "All nonpoint proper original faces", StatementSource.FromAuthor(Disp(Context(
                    All("F", Sets, Iff(In(f, L), And(C("Nontrivial", f), Face(f), Ne(f, K))))))),
                    "The line carrier is the subtype of all original convex extreme subsets F of K which contain two different points and differ from K. Point-line incidence is membership of the original point value in F. There is no closedness field. Its representation by the pure boundary F intersect P is proved injective."),
                Def("zeroComplement", "The guarded zero complement", StatementSource.FromAuthor(Disp(Context(
                    All("F", Sets, All("x", V("V"), Iff(In(x, Perp(f)), And(In(x, K),
                        All("q", P, Imp(In(Val(q), f), In(x, Dp(q))))))))))),
                    "The intersection is taken inside K, over every original pure q whose value belongs to F. In particular an empty index set gives K. The first endpoint x may be any mixed state of K; it is never restricted to P."),
                Def("thickExclusionBalls", "The extra dimension condition", StatementSource.FromAuthor(Disp(Context(
                    Iff(C("thickExclusionBalls", V("C"), V("u")), All("p", P,
                        Ex("b", C("ExclusionChart", V("C"), V("u"), p), new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, C("dim", b)))))))),
                    "Only the projective-plane conclusion uses this stronger condition. The other identities allow dimension one and therefore line segments."),
                Def("FacePolarity", "The full original-face structure", StatementSource.FromAuthor(Disp(Context(
                    Iff(C("Nonempty", C("FacePolarity", V("C"), V("u"))), full)))),
                    "The structure contains a point-line equivalence with value D(p), singleton intersections of distinct lines, no self-incidence, incidence reversal with the inverse equivalence, all four zero-complement endpoints, convex faciality of every zero complement, double complementation on every original convex face, inclusion reversal and its equivalence on faces, the whole pure-boundary chart identity and injectivity of the boundary representation. It also contains an actual Mathlib Configuration.ProjectivePlane on these original carriers under the extra dimension condition. The equivalence supplies both inverse identities."),
                Describe.Lean(DescribeId.Create("original-face-polarity"), DeclarationHandle.Create(Owner + "original_face_polarity"),
                    H("Original point-face duality, mixed double orthogonality and projective polarity"),
                    StatementSource.FromAuthor(Disp(Context(Imp(hypotheses, full)))), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For different D(p) and D(q), the whole minimal face of p,q is D(r). Original zero symmetry puts r in their intersection. The intersection is an original convex face of both whole balls. If it contained two points, ball facial rigidity would make it equal both balls. It is therefore exactly the original pure singleton r. This argument uses only that the balls differ, before injectivity of p to D(p) has been proved.")),
                        Paragraph(Text("Suppose different pure p,q had the same exclusion L, and let M be their whole minimal face. Since p belongs to M and does not belong to L, the two nonpoint proper faces differ. Their unique pure intersection r belongs to both. Zero symmetry puts p,q in D(r), so original minimality gives M contained in D(r). Ball rigidity gives M=D(r), contradicting r in M and r not in D(r). Thus p to D(p) is injective. The complete classification of original proper faces gives surjectivity onto the entire line carrier.")),
                        Paragraph(Text("Every compact nonpoint exclusion ball has two different extreme points: if its extreme set were a singleton, the closed-convex-hull form of Krein-Milman would collapse the whole ball to that singleton. These extreme points are original pure points because D(p) is a face of K. Choose two such a,b in D(p). Injectivity and the intersection theorem give D(a) intersect D(b)={p}. Every mixed x in the zero complement of D(p) lies in both sets, hence equals p. The reverse inclusion uses zero symmetry for every pure point of D(p). The two chosen points are proof witnesses; the zero-complement definition retains its entire pure index set.")),
                        Paragraph(Text("The pure carrier is nonempty because the original pure-span theorem gives span(P)=V and V is nonzero. Antitonicity places K's zero complement inside {p} and inside D(p), so it is empty. The empty and pure-singleton endpoints follow from the guarded definition. Each zero complement is a convex face of K by the faciality of every exclusion, including the empty-index case. The complete classification of all original proper convex faces then proves double complementation for empty, K, singleton and ball faces, without assuming any input face closed. Applying antitonicity twice gives the equivalence of the two face inclusion orders.")),
                        Paragraph(Text("An injective affine chart transports extreme points in both directions. The entire extreme set of a closed Euclidean unit ball is its unit sphere, so D(p) intersect P is exactly the image of the whole sphere. Two different original faces cannot share this boundary, since it contains two points while their intersection is a singleton. For chart dimension at least two, the images of e0, minus e0 and e1 are three different pure points on the line.")),
                        Paragraph(Text("The actual configuration has original pure points and all original nonpoint proper faces as lines. A line's pole is a point outside it, and each point lies outside its pole-line. Distinct lines intersect uniquely, and distinct pure points determine their whole minimal pair face. To construct the nondegenerate configuration, choose three different a,b,d on a line and c outside it. On the line cd choose e different from c,d. Uniqueness of intersections makes e avoid ab, ac and bc. With p1=a,p2=b,p3=c and l1=ae,l2=bc,l3=be, the required eight assertions are a not in bc, a not in be, b not in ae, b in bc, b in be, c not in ae, c in bc and c not in be. These fill Configuration.ProjectivePlane on the original carriers.")),
                        Paragraph(Text("The point-line equivalence and original pure zero symmetry identify p in L with the inverse pole of L in D(p). Together with p not in D(p), this is an incidence-reversing polarity without absolute points. No field coordinatization, Desargues property, projective-plane classification or physical realization follows here. When segments are allowed the face identities remain valid; the projective-plane conclusion retains its separate dimension premise. No literature priority is asserted."))), DescribeRole.Theorem))));
    }

    private static DocumentBlock Def(string name, string title, StatementSource statement, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(title),
            statement, AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
