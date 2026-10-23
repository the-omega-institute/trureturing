using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BanachGeometry;

internal sealed class PolyhedralBJRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/BanachGeometry/PolyhedralBJRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mannamandalpaulsain2025improvement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete real Banach plane refutes the assertion that any independent extreme-point basis detects scalar isometries in every polyhedral space.",
        H("Independent extreme-point tests in a polyhedral Banach plane"),
        Blocks(
            Paragraph(Text("Manna, Mandal, Paul and Sain, arXiv:2511.20345v1, final Open Question: “Open Question: In an n-dimensional polyhedral Banach space, does the preservation of Birkhoff-James orthogonality by a bounded linear operator at any n linearly independent extreme points necessarily imply that the operator is a scalar multiple of an isometry?” The standing field is real or complex. Preservation at a point quantifies every direction, with every scalar of the base field in each orthogonality inequality.")),
            Entry("field-assertion", "fieldClaim", "The source assertion over one field", FieldClaim(),
                "For a scalar field K with RCLike structure, fieldClaim K quantifies every complete finite-dimensional normed K-space E, every natural dimension n equal to finrank K E, every independent tuple v indexed by Fin n of actual extreme unit points, and every continuous linear endomorphism T. The polyhedral premise is finiteness of the native real-convex extremePoints of Metric.closedBall 0 1, using the real structure obtained by restricting scalars. At every selected vᵢ and for every y, the all-K-scalar input inequality implies the all-K-scalar output inequality. The conclusion is literal equality T = c • U.toContinuousLinearMap for one unrestricted c in K and a native K-linear isometry U. The scalar zero is included. The tuple is chosen before T; preservation at all independent tuples is not assumed.",
                DescribeRole.Definition),
            Entry("whole-question", "claim", "The complete real-or-complex assertion",
                Disp(Iff(V("claim"), And(Call("fieldClaim", Real), Call("fieldClaim", Complex)))),
                "The closed proposition is the conjunction of the real and complex instances of fieldClaim. It has no free space, dimension, tuple, operator or scalar parameter. One legal real instance suffices to refute this conjunction; no complex counterexample is needed.",
                DescribeRole.Definition),
            Entry("facet-plane", "facetPlane", "The three-reading plane",
                Disp(Eq(V("facetPlane"), Call("setOf", Eq(At(V("w"), D(2)),
                    Sub(At(V("w"), D(1)), Div(At(V("w"), D(0)), D(2))))))),
                "The submodule of Fin 3 → ℝ is defined by w₂ = w₁ − w₀/2. It inherits the actual sup norm, metric and real normed-space structure from this ambient space. Its unit ball is a section of the cube; its extreme points are proved inside the section, rather than identified with the ambient cube vertices.",
                DescribeRole.Definition),
            Entry("native-carrier", "Plane", "The complete normed carrier",
                Disp(Eq(V("Plane"), V("facetPlane"))),
                "Plane is the subtype of facetPlane. Submodules of finite-dimensional real spaces are finite dimensional. The coordinate equivalence below proves finrank ℝ Plane = 2; finite-dimensional completeness supplies CompleteSpace Plane.",
                DescribeRole.Definition),
            Entry("point-coordinates", "point", "The norm and the selected unit vectors",
                Disp(And(Eq(Call("point", V("a"), V("b")),
                    Call("tuple", V("a"), Add(V("a"), V("b")), Add(Div(V("a"), D(2)), V("b")))),
                    Eq(Norm(Call("point", V("a"), V("b"))),
                        Call("max", Call("max", Abs(V("a")), Abs(Add(V("a"), V("b")))),
                            Abs(Add(Div(V("a"), D(2)), V("b"))))))),
                "Write p = point 1 0, q = point 0 1 and r = point (−1) (3/2). The actual closed unit ball consists exactly of points whose three facet readings have absolute value at most one. Every actual extreme point has at least two active readings: otherwise a nonzero tangent fixing the sole active reading permits a small feasible segment in both directions. Solving the three possible pairs of active equations places every extreme point in {±p, ±q, ±r}, so the actual extreme-point set is finite. At p the first two readings equal one; at q the last two equal one. Any proper convex decomposition of either point forces these two readings of each endpoint to equal one, hence forces the endpoint to be the point itself. Thus p and q are genuine extreme unit points.",
                DescribeRole.Definition),
            Entry("linear-coordinates", "coordinates", "Algebraic coordinates and independence",
                Disp(Eq(Call("coordinates", Call("tuple", V("a"), V("b"))),
                    Call("point", V("a"), V("b")))),
                "The inverse coordinate map is w ↦ (w₀, w₁ − w₀). This is an algebraic linear equivalence from ℝ × ℝ, without an assertion that the usual product norm is preserved. Mapping the standard two-vector basis through it gives the selected independent tuple (p,q).",
                DescribeRole.Definition),
            Entry("bounded-operator", "operator", "The continuous linear endomorphism",
                Disp(Eq(At(V("operator"), Call("point", V("a"), V("b"))),
                    Call("point", Add(V("a"), V("b")), Mul(Div(Sub(D(0), D(3)), D(2)), V("b"))))),
                "The operator has coordinate formula T(a,b) = (a+b, −3b/2). Conjugating this linear map by coordinates and applying finite-dimensional continuity constructs an actual Plane →L[ℝ] Plane. In particular Tp = p and Tq = point 1 (−3/2). For a direction (a,b), orthogonality at p implies a(a+b) ≤ 0, and orthogonality at q implies (a+b)(a/2+b) ≤ 0. The existing active_not_BJ theorem supplies necessity for these all-direction statements. At the outputs the corresponding signed products are (a+b)(a−b/2) = (3/2)a(a+b) − (a+b)²/2 and (a+b)(b−a/2) = 3(a+b)(a/2+b) − 2(a+b)². They are nonpositive under the respective input hypotheses. Opposite weak signs ensure that for every real scalar, some active signed facet stays at least one. This proves full local preservation at p and q, including zero directions, zero slopes and both scalar signs.",
                DescribeRole.Definition),
            Entry("source-refutation", "result", "Refutation of the whole question",
                Disp(new Formula.Not(V("claim"))),
                "The real carrier, its dimension and completeness, finite actual extreme-point set, selected independent extreme unit tuple, continuous operator and full preservation implications instantiate every premise of the real source assertion. If T = cU for any scalar and native linear isometry, norm_smul and U.norm_map force ‖Tz‖ = |c| ‖z‖ for every z. But ‖p‖ = ‖r‖ = 1, ‖Tp‖ = 1 and ‖Tr‖ = 2. These equalities contradict a common |c|, including c = 0. The theorem has the literal type Not claim. It answers the universal question negatively; it does not classify polyhedral norms or their K-numbers. The positive sup-norm theorem LinfKNumber.result concerns a different norm and retains its conclusion.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("manna-mandal-paul-sain-2025-polyhedral-extreme-tests"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula All(string x, Formula type, Formula body) => Seq(Forall, Sp, V(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string x, Formula type, Formula body) => Seq(Exists, Sp, V(x), Colon, Sp, type, Comma, Sp, body);

    private static Formula FieldClaim()
    {
        Formula v = At(V("v"), V("i"));
        Formula input = All("t", V("K"), Le(Norm(v), Norm(Add(v, Mul(V("t"), V("y"))))));
        Formula output = All("t", V("K"), Le(Norm(At(V("T"), v)),
            Norm(Add(At(V("T"), v), Mul(V("t"), At(V("T"), V("y")))))));
        Formula preserves = All("i", Call("Fin", V("n")), All("y", V("E"), Imp(input, output)));
        Formula hypotheses = And(And(Call("CompleteNormedSpace", V("K"), V("E")),
            Call("FiniteDimensional", V("K"), V("E"))),
            And(Eq(Call("finrank", V("K"), V("E")), V("n")),
                And(Call("Finite", Call("extremePoints", Real, Call("closedBall", D(0), D(1)))),
                    And(Call("LinearIndependent", V("K"), V("v")),
                        All("i", Call("Fin", V("n")), And(
                            new Formula.Relation(v, FormulaRelationOperator.MemberOf,
                                Call("extremePoints", Real, Call("closedBall", D(0), D(1)))),
                            Eq(Norm(v), D(1))))))));
        Formula conclusion = Some("c", V("K"), Some("U", Call("LinearIsometry", V("K"), V("E"), V("E")),
            Eq(V("T"), Mul(V("c"), Call("toContinuousLinearMap", V("U"))))));
        return Disp(Iff(Call("fieldClaim", V("K")), All("E", V("Type"),
            All("n", Nat, All("v", Call("Function", Call("Fin", V("n")), V("E")),
                All("T", Call("ContinuousLinearMap", V("K"), V("E"), V("E")),
                    Imp(hypotheses, Imp(preserves, conclusion))))))));
    }
}
