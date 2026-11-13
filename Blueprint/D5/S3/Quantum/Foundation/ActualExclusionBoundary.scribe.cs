using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ActualExclusionBoundaryDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mem(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Inst(string s, params Formula[] xs) =>
        F.Seq(F.OpenBracket, Call(s, xs), F.CloseBracket, F.Sp);

    private static Formula Statement()
    {
        var V = Id("V"); var C = Id("C"); var u = Id("u"); var real = Id("Real");
        var x = Id("x"); var y = Id("y"); var p = Id("p");
        var K = Call("base", C, u); var P = Call("pure", C, u);
        var S = Call("intrinsicFrontier", real, K);
        Formula D(Formula q) => Call("exclusion", C, u, q);
        var strict = All("x", V, Imp(And(Mem(x, C),
            new Formula.Relation(x, FormulaRelationOperator.NotEqual, F.D(0))),
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, Call("u", x))));
        var assumptions = And(Call("IsClosed", C), And(strict,
            And(new Formula.Relation(Call("span", real, C), FormulaRelationOperator.Equal, Id("top")),
                Call("exclusionBalls", C, u))));
        var cover = All("x", V, Imp(Mem(x, S), Ex("p", P, Mem(x, D(p)))));
        var common = Ex("p", P, And(Mem(x, D(p)), Mem(y, D(p))));
        var midpoint = All("x", V, Imp(Mem(x, K), All("y", V, Imp(Mem(y, K),
            new Formula.Logic(Mem(Call("midpoint", real, x, y), S),
                FormulaLogicOperator.Iff, common)))));
        return All("V", Id("Types"), F.Seq(Inst("NormedAddCommGroup", V),
            Inst("NormedSpace", real, V), Inst("FiniteDimensional", real, V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(assumptions, And(cover, midpoint))))));
    }

    private static Formula QuotientStatement()
    {
        var V = Id("V"); var C = Id("C"); var u = Id("u"); var real = Id("Real");
        var K = Call("base", C, u); var P = Call("pure", C, u);
        var S = Call("intrinsicFrontier", real, K); var r = Id("r");
        var x = Id("x"); var y = Id("y"); var p = Id("p"); var q = Id("s");
        Formula D(Formula a) => Call("exclusion", C, u, a);
        var repeated = All("p", P, Ex("s", P, And(
            new Formula.Relation(p, FormulaRelationOperator.NotEqual, q),
            new Formula.Relation(D(q), FormulaRelationOperator.Equal, D(p)))));
        var Q = Call("Quotient", r); var projection = Call("QuotientMk", r);
        var data = And(All("x", S, All("y", S,
                new Formula.Logic(Call("r", x, y), FormulaLogicOperator.Iff,
                    Mem(Call("midpoint", real, x, y), S)))),
            And(All("x", S, All("y", S,
                new Formula.Logic(Call("r", x, y), FormulaLogicOperator.Iff,
                    Ex("p", P, And(Mem(x, D(p)), Mem(y, D(p))))))),
                And(Call("IsClosed", Call("RelationGraph", r)),
                    And(Call("CompactSpace", Q), And(Call("TTwoSpace", Q),
                        And(Call("Continuous", projection),
                            And(Call("Surjective", projection), Call("IsClosedMap", projection))))))));
        return All("V", Id("Types"), F.Seq(Inst("NormedAddCommGroup", V),
            Inst("NormedSpace", real, V), Inst("FiniteDimensional", real, V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(And(Call("OriginalEBDomain", C, u), repeated),
                    Ex("r", Call("Setoid", S), data))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole original exclusions cover the actual relative boundary and detect its boundary midpoints.",
        H("The actual boundary and common whole exclusions"),
        Blocks(Describe.Lean(DescribeId.Create("original-boundary-cover-and-midpoint"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_boundary_cover_and_midpoint"),
            H("Boundary coverage and the midpoint criterion"),
            StatementSource.FromAuthor(F.Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("V is the original finite dimensional real normed vector space, C the original closed generating pointed cone, and u its actual strictly positive linear unit. The notation base(C,u) means the entire set K of cone points with u equal to one, and pure(C,u) means all extreme points of K. The exclusion D(p) uses all original proper effects f with f(p)=1 and consists of all x in K for which one such f has f(x)=0. No restriction of states or effects is made.")),
                Paragraph(Text("The predicate exclusionBalls requires, for each original pure p, an injective affine parametrization of the entire D(p) by a closed Euclidean unit ball of a positive dimension. Dimensions may vary with p. IntrinsicFrontier is the boundary inside the actual affine span of K. LinearMaps denotes real linear maps, span the real linear span, and top the whole vector space.")),
                Paragraph(Text("At an actual relative boundary point x, membership in the interior of the cone would give membership in the relative interior of its normalized base by restricting to the unit affine hyperplane. Thus x is outside the cone interior. The cone has nonempty interior because it generates V. A geometric Hahn–Banach support functional f therefore attains its maximum on the cone at x. Cone scaling and the zero vector force f(x)=0 and f to be nonpositive on the cone.")),
                Paragraph(Text("The maximizer set of f on the whole K is a convex exposed face containing x. It is proper: if every original pure point maximized f, pure spanning would force f=0. The existing EB face classification makes this face either a whole exclusion or a pure singleton. In the singleton case a pure point of the nonempty compact exclusion of x, together with the symmetry supplied by complementary original effects, places x in a whole exclusion as well.")),
                Paragraph(Text("Each whole exclusion lies in the actual relative boundary. Its common original confirming effect vanishes there but equals one at its confirming pure point. A relative interior point could be extended slightly away from that pure point along the same affine line while remaining in K; linearity would give a negative proper-effect value, which is impossible.")),
                Paragraph(Text("If the midpoint of two points of K is on the boundary, coverage puts that midpoint in one whole exclusion. The extreme-set property forces both endpoints into that same exclusion. Conversely, convexity keeps the midpoint in any common exclusion, hence on the actual boundary. Equal endpoints and the degenerate ambient space remain in scope.")),
                Paragraph(Text("This is the original-boundary midpoint bridge needed for IX116.6. It uses neither Pair properness nor injectivity, orthogonality axioms, common centers or global singleton labels. To obtain the all-repeated contradiction one must still prove repeated-block isolation, use that isolation to establish transitivity of the common-ball relation, construct its actual compact Hausdorff quotient, construct the common rational slice and convex neighborhood controls, and complete the radial homotopy obstruction. Existence of a singleton-labelled ball, its propagation and continuum multiplicity are not conclusions here. No originality claim is made."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-all-repeated-boundary-quotient"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_all_repeated_boundary_quotient"),
            H("The literal all-repeated boundary quotient"),
            StatementSource.FromAuthor(F.Disp(QuotientStatement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("OriginalEBDomain abbreviates exactly the closedness, strict positivity, generating span and whole positive-dimensional exclusion-ball hypotheses in the preceding statement, with the same V, C and u. The extra assumption says that every original pure label p has a distinct original pure label s with the same entire exclusion set. This is the all-repeated contradiction branch, not an extra assumption on the eventual EB-only existence theorem.")),
                Paragraph(Text("RelationGraph(r) is the set of boundary pairs (x,y) with r(x,y). Setoid means an equivalence relation; QuotientMk is its canonical projection onto its actual quotient. The theorem constructs r as the literal boundary-midpoint predicate and proves that its classes are exactly the whole exclusion blocks through the second displayed equivalence.")),
                Paragraph(Text("To prove isolation, two shared distinct points force two whole exclusion balls to coincide, by applying the existing strict ball-face theorem to their intersection. If a repeated ball meets another different ball, their singleton intersection is pure. The two distinct labels of the repeated ball then force every pure point of that ball to have one common exclusion. Zero symmetry puts all those pure points in the other ball. Compact convex hull generation and maximality force equality, a contradiction. Thus different whole balls are disjoint in this branch, and the midpoint criterion makes the literal relation transitive.")),
                Paragraph(Text("The actual boundary is a closed subset of compact K. The midpoint map is continuous, so its inverse image of that boundary is a closed relation graph. The saturation of a closed boundary subset is the projection of the intersection of this graph with a compact product. It is closed, proving that the actual quotient projection is closed. Its fibers are compact by the same graph argument. The proper-map product theorem then makes the product projection a quotient map; the closed graph descends to the closed diagonal, proving the actual quotient Hausdorff. Compactness descends from the compact actual boundary.")),
                Paragraph(Text("This construction places no ENR, metrizability, finite dimension, fibration or local contractibility hypothesis on the quotient. The common rational Baire slice, ray-avoiding finite-neighborhood data, radial homotopy and sphere contradiction are further obligations. The full original theorem is not settled by construction of this quotient."))),
            DescribeRole.Theorem))));
}
