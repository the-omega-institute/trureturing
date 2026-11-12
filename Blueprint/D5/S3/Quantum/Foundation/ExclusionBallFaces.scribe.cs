using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ExclusionBallFacesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ExclusionBallFaces.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, F.Lt, Sp, b);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula K => C("base", Cone, Unit);
    private static Formula P => C("pure", Cone, Unit);
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula Set => C("Set", Space);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula Dp(Formula p) => C("exclusion", Cone, Unit, p);
    private static Formula Pair(Formula p, Formula q) => C("pairBase", Cone, Unit, p, q);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));
    private static Formula Strict => All("x", Space, Imp(In(V("x"), Cone),
        Imp(Ne(V("x"), D(0)), Lt(D(0), App(Unit, V("x"))))));

    public DocumentDefinition Create()
    {
        Formula p = V("p"), q = V("q"), r = V("r"), f = V("f"), face = V("F");
        Formula cut = Eq(Dp(p), C("inter", K, C("ker", f)));
        Formula geometry = All("p", P,
            And(C("Nontrivial", Dp(p)), And(C("IsCompact", Dp(p)),
            And(C("Convex", R, Dp(p)), And(C("IsExposed", R, K, Dp(p)),
            And(C("IsExtreme", R, K, Dp(p)), And(Ne(Dp(p), K),
                Ex("f", Dual, And(C("confirms", Cone, Unit, p, f), cut)))))))));
        Formula classification = All("F", Set, Imp(C("Nonempty", face),
            Imp(C("Convex", R, face), Imp(C("IsExtreme", R, K, face), Imp(Ne(face, K),
                Or(Ex("p", P, Eq(face, new Formula.SetLiteral([p]))),
                   Ex("p", P, Eq(face, Dp(p)))))))));
        Formula pairResult = Imp(C("pairProper", Cone, Unit), And(
            All("p", P, All("q", P, Imp(Ne(p, q), Ex("r", P, Eq(Pair(p, q), Dp(r)))))),
            C("wholePairBalls", Cone, Unit)));
        Formula statement = Context(Imp(C("IsClosed", Cone), Imp(Strict,
            Imp(Eq(C("span", R, Cone), C("top")), Imp(C("exclusionBalls", Cone, Unit),
                And(geometry, And(classification, pairResult)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Nondegenerate entire exclusion balls expose and exhaust the original proper convex faces; proper pure pairs then generate whole balls.",
            H("Entire exclusion balls and all original proper faces"), Blocks(
                Paragraph(Text("The original finite dimensional real normed carrier V has a closed generating cone C and a real-linear unit u strictly positive on every nonzero cone vector. Strict positivity excludes nonzero lines. K is the entire normalized base, P consists of all its extreme points, and proper effects are all real-linear f with 0<=f<=u on C. No finite or closed pure carrier, restricted effect menu, least effect, Jordan representation, projectivity or effect extension is an input. The argument also covers the zero carrier whenever its hypotheses hold.")),
                Def("ExclusionChart", "A whole nondegenerate exclusion ball", StatementSource.WithoutFormula(),
                    "For a specified original point p, the chart has a natural dimension d>0, an affine map from EuclideanSpace R (Fin d) to V, injectivity on the entire Euclidean space, and equality of the image of the entire closed unit ball with exclusion(C,u,p). These are its only fields. Dimension one, giving a line segment, is included. Facial structure and exposedness are conclusions."),
                Def("exclusionBalls", "The entire mixed-state ball condition", StatementSource.FromAuthor(Disp(Context(
                    Iff(C("exclusionBalls", Cone, Unit), All("p", P, C("Nonempty", C("ExclusionChart", Cone, Unit, p))))))),
                    "For every original pure p there is such a chart of its full original exclusion set. A mixed state x belongs to that set precisely when x belongs to K and some original proper confirmer f of p has f(x)=0. The confirmer may initially depend on x."),
                Def("pairProper", "Properness of every whole pure-pair face", StatementSource.FromAuthor(Disp(Context(
                    Iff(C("pairProper", Cone, Unit), All("p", P, All("q", P, Imp(Ne(p, q), Ne(Pair(p, q), K)))))))),
                    "pairBase is the existing intersection of the entire original base with every native cone face containing both p and q. Properness compares this whole set with K. It does not compare a selected slice or only the segment joining the two points."),
                Describe.Lean(DescribeId.Create("exclusion-ball-faces"), DeclarationHandle.Create(Owner + "exclusion_ball_faces"),
                    H("Common exposure, all-face exhaustion and entire pair balls"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Each full exclusion set is nonpoint, compact, convex, exposed and extreme in K, and differs from K. One original proper confirmer cuts it out exactly as K intersect ker(f); inter denotes set intersection. Every nonempty proper original convex face is either an original pure singleton or an entire exclusion ball. There is no closed-face premise. If pairProper also holds, each whole minimal face of distinct pure points equals an entire exclusion set, and the existing wholePairBalls predicate follows.")),
                        Paragraph(Text("Convexity of each entire exclusion ball implies original mixed-state midpoint gluing. The existing zero_gluing_common_effect then produces one original confirmer vanishing on every exclusion. Its negative functional exposes that full set, while confirmation at p makes the face proper. Compactness and nonpointness come directly from the full nondegenerate ball chart.")),
                        Paragraph(Text("The existing base_face_lift identifies any convex face of K with the entire normalized slice of an original cone face, without assuming closedness. A proper cone face misses the cone interior: if it contained an interior point, extension of each original direction to an open segment would force it to contain the whole cone. The generating condition gives nonempty cone interior, so geometric Hahn-Banach supplies a nonzero functional nonnegative on the entire cone and zero on that entire face. A compact exposed maximum face contains an original pure maximizer. Dividing the functional by that strictly positive maximum gives one original proper confirmer and places the initial face inside its full exclusion set.")),
                        Paragraph(Text("Pull the original face back through the injective affine ball chart. If it contains two distinct points, their midpoint is interior to the entire strictly convex ball. A face containing an interior point is the whole ball. This holds in dimension one as well. A remaining singleton is pure because it is itself an extreme subset of K. Under pairProper, the entire original pair base is a nonpoint proper convex face, so the classification identifies it with a full exclusion ball and transports the existing BallChart without replacing the minimal face.")),
                        Paragraph(Text("The exposing confirmer is not asserted to be least. Reciprocal pure values, point-ball duality, rank-three or Jordan reconstruction, Born rules, composites and physical realization require their separate mathematical and operational premises. The result is a consequence within the original finite dimensional full-effect model; no literature priority is asserted."))), DescribeRole.Theorem))));
    }

    private static DocumentBlock Def(string name, string title, StatementSource statement, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(title),
            statement, AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
