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
                            And(Call("Surjective", projection), And(Call("IsClosedMap", projection),
                                All("b", Q, Ex("p", P, new Formula.Relation(
                                    Call("AmbientImage", Call("Fiber", projection, Id("b"))),
                                    FormulaRelationOperator.Equal, D(p))))))))))));
        return All("V", Id("Types"), F.Seq(Inst("NormedAddCommGroup", V),
            Inst("NormedSpace", real, V), Inst("FiniteDimensional", real, V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(And(Call("OriginalEBDomain", C, u), repeated),
                    Ex("r", Call("Setoid", S), data))))));
    }

    private static Formula Conj(params Formula[] xs)
    {
        var result = xs[^1];
        for (var i = xs.Length - 2; i >= 0; i--) result = And(xs[i], result);
        return result;
    }

    private static Formula RationalSliceStatement()
    {
        var V = Id("V"); var C = Id("C"); var u = Id("u"); var real = Id("Real");
        var S = Call("intrinsicFrontier", real, Call("base", C, u));
        var r = Id("r"); var Q = Call("Quotient", r); var projection = Call("QuotientMk", r);
        var f = Id("f"); var t = Id("t"); var O = Id("O"); var b = Id("b");
        var x = Id("x"); var y = Id("y"); var p = Id("p"); var c = Id("c");
        Formula Eq(Formula a, Formula d) => new Formula.Relation(a, FormulaRelationOperator.Equal, d);
        Formula Lt(Formula a, Formula d) => new Formula.Relation(a, FormulaRelationOperator.LessThan, d);
        var properties = Conj(
            All("x", S, All("y", S, new Formula.Logic(Call("r", x, y), FormulaLogicOperator.Iff,
                Mem(Call("midpoint", real, x, y), S)))),
            Call("CompactSpace", Q), Call("TTwoSpace", Q), Call("Continuous", projection),
            Call("IsClosedMap", projection),
            All("b", Q, Ex("p", Call("pure", C, u),
                Eq(Call("AmbientImage", Call("Fiber", projection, b)), Call("exclusion", C, u, p)))));
        var crossing = All("b", Q, Imp(Mem(b, O), Ex("x", S, Ex("y", S, Conj(
            Eq(Call("QuotientMk", r, x), b), Eq(Call("QuotientMk", r, y), b),
            Lt(Call("f", x), Call("RealCast", t)), Lt(Call("RealCast", t), Call("f", y)))))));
        var n = Id("n"); var j = Id("j"); var W = Id("W"); var N = Id("N");
        var v = Id("v"); var A = Id("A"); var fin = Call("Fin", n);
        var ray = Call("PositiveRay", Call("Subtract", v, c));
        var control = All("j", fin, All("b", Q, Imp(Mem(b, Call("W", j)),
            All("x", S, Imp(Eq(Call("QuotientMk", r, x), b),
                Mem(Call("Subtract", x, c), Call("N", j)))))));
        var alternative = All("j", fin, new Formula.Logic(Call("Disjoint", Call("N", j), ray),
            FormulaLogicOperator.Or, Call("Subset", Call("W", j), O)));
        var averaged = Ex("A", Call("ContinuousMaps", Q, V), Conj(
            All("b", Q, Mem(Call("A", b), Call("TranslatedBase", C, u, c))),
            All("b", Q, Call("NotSameRay", real, Call("Subtract", v, c), Call("A", b))),
            All("x", S, Call("NotMember", F.D(0), Call("segment", real,
                Call("Subtract", x, c), Call("A", Call("QuotientMk", r, x)))))));
        var controls = Ex("v", S, Conj(Mem(Call("QuotientMk", r, v), O),
            Lt(Call("RealCast", t), Call("f", v)),
            Ex("n", Id("Naturals"), Ex("W", Call("Maps", fin, Call("Sets", Q)),
                Ex("N", Call("Maps", fin, Call("Sets", V)), Conj(
                    All("j", fin, Call("IsOpen", Call("W", j))),
                    All("b", Q, Ex("j", fin, Mem(b, Call("W", j)))),
                    All("j", fin, Call("Convex", real, Call("N", j))),
                    All("j", fin, Call("NotMember", F.D(0), Call("N", j))),
                    alternative, control, averaged))))));
        var level = Ex("c", V, And(Mem(c, Call("intrinsicInterior", real, Call("base", C, u))),
            And(Eq(Call("f", c), Call("RealCast", t)), controls)));
        var slice = Ex("f", Call("LinearMaps", real, V, real), Ex("t", Id("Rationals"),
            Ex("O", Call("Sets", Q), Conj(
                new Formula.Relation(f, FormulaRelationOperator.NotEqual, F.D(0)),
                Call("IsOpen", O), Call("Nonempty", O), level,
                Call("Subset", O, Call("Image", projection, Call("BoundaryLevelSet", f, t))), crossing))));
        return All("V", Id("Types"), F.Seq(Inst("NormedAddCommGroup", V),
            Inst("NormedSpace", real, V), Inst("FiniteDimensional", real, V), Inst("Nontrivial", V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(And(Call("OriginalEBDomain", C, u), Call("AllRepeated", C, u)),
                    Ex("r", Call("Setoid", S), And(properties, slice)))))));
    }

    private static Formula HomotopyStatement()
    {
        var V = Id("V"); var C = Id("C"); var u = Id("u"); var real = Id("Real");
        var K = Call("base", C, u); var S = Call("intrinsicFrontier", real, K);
        var E = Call("direction", Call("affineSpan", real, K));
        var c = Id("c"); var v = Id("v"); var x = Id("x"); var z = Id("z");
        Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
        var endpoints = Conj(
            All("x", S, Eq(Call("H", Call("Pair", F.D(0), x)), Call("Subtract", x, c))),
            All("x", S, Eq(Call("H", Call("Pair", F.D(1), x)), Call("Subtract", c, v))),
            All("z", Call("Product", Id("UnitInterval"), S),
                new Formula.Relation(Call("H", z), FormulaRelationOperator.NotEqual, F.D(0))));
        var maps = Ex("H", Call("ContinuousMaps", Call("Product", Id("UnitInterval"), S), E), endpoints);
        var withBoundary = Ex("v", S, And(Call("Nontrivial", E), maps));
        var conclusion = Ex("c", V, And(Mem(c, Call("intrinsicInterior", real, K)), withBoundary));
        return All("V", Id("Types"), F.Seq(Inst("NormedAddCommGroup", V),
            Inst("NormedSpace", real, V), Inst("FiniteDimensional", real, V), Inst("Nontrivial", V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(And(Call("OriginalEBDomain", C, u), Call("AllRepeated", C, u)), conclusion)))));
    }

    private static Formula SingletonStatement(bool propagation)
    {
        var V = Id("V"); var C = Id("C"); var u = Id("u"); var real = Id("Real");
        var P = Call("pure", C, u); var p = Id("p"); var q = Id("q"); var t = Id("s");
        Formula Unique(Formula a) => All("s", P, Imp(
            new Formula.Relation(Call("exclusion", C, u, t), FormulaRelationOperator.Equal,
                Call("exclusion", C, u, a)),
            new Formula.Relation(t, FormulaRelationOperator.Equal, a)));
        var conclusion = propagation
            ? All("p", P, Imp(Unique(p), All("q", P,
                Imp(Mem(q, Call("exclusion", C, u, p)), Unique(q)))))
            : Ex("p", P, Unique(p));
        return All("V", Id("Types"), F.Seq(Inst("NormedAddCommGroup", V),
            Inst("NormedSpace", real, V), Inst("FiniteDimensional", real, V),
            propagation ? F.Seq() : Inst("Nontrivial", V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(Call("OriginalEBDomain", C, u), conclusion)))));
    }

    private static Formula FamilyStatement()
    {
        var V = Id("V"); var C = Id("C"); var u = Id("u"); var real = Id("Real");
        var P = Call("pure", C, u); var p = Id("p"); var q = Id("q"); var t = Id("s");
        var labels = Id("labels"); var a = Id("a"); var b = Id("b");
        Formula Unique(Formula x) => All("s", P, Imp(
            new Formula.Relation(Call("exclusion", C, u, t), FormulaRelationOperator.Equal,
                Call("exclusion", C, u, x)),
            new Formula.Relation(t, FormulaRelationOperator.Equal, x)));
        var thick = All("q", P, Ex("b", Call("ExclusionChart", C, u, q),
            new Formula.Relation(F.D(2), FormulaRelationOperator.LessThanOrEqual, Call("dim", b))));
        var family = Ex("labels", Call("Embeddings", real, P), Conj(
            All("a", real, Mem(Call("labels", a), Call("exclusion", C, u, p))),
            Call("Injective", Call("WholeBallFamily", C, u, labels)),
            All("a", real, Unique(Call("labels", a)))));
        var conclusion = Ex("p", P, Conj(Unique(p),
            All("q", P, Imp(Mem(q, Call("exclusion", C, u, p)), Unique(q))), Imp(thick, family)));
        return All("V", Id("Types"), F.Seq(Inst("NormedAddCommGroup", V),
            Inst("NormedSpace", real, V), Inst("FiniteDimensional", real, V), Inst("Nontrivial", V),
            All("C", Call("PointedCone", real, V), All("u", Call("LinearMaps", real, V, real),
                Imp(Call("OriginalEBDomain", C, u), conclusion)))));
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
                Paragraph(Text("MixedExclusionGeometry.frontier_covered applies the positive support-confirmer theorem to the nonzero nonnegative functional -f. It gives an original pure label p and an original proper effect confirming p that vanishes on the entire zero face of f, hence at x. Thus x belongs to the entire original exclusion D(p). This boundary coverage uses closedness, strict positivity and generating span; it does not require the whole-ball hypothesis.")),
                Paragraph(Text("Each whole exclusion lies in the actual relative boundary. Its common original confirming effect vanishes there but equals one at its confirming pure point. A relative interior point could be extended slightly away from that pure point along the same affine line while remaining in K; linearity would give a negative proper-effect value, which is impossible.")),
                Paragraph(Text("If the midpoint of two points of K is on the boundary, coverage puts that midpoint in one whole exclusion. The extreme-set property forces both endpoints into that same exclusion. Conversely, convexity keeps the midpoint in any common exclusion, hence on the actual boundary. Equal endpoints and the degenerate ambient space remain in scope.")),
                Paragraph(Text("This is the original-boundary midpoint bridge needed for IX116.6. It uses neither Pair properness nor injectivity, orthogonality axioms, common centers or global singleton labels. The following theorem supplies repeated-block isolation, transitivity and the actual compact Hausdorff quotient in the all-repeated contradiction branch. The common rational slice, convex neighborhood controls and radial homotopy obstruction remain further obligations. Existence of a singleton-labelled ball, its propagation and continuum multiplicity are not conclusions here. No originality claim is made."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-all-repeated-boundary-quotient"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_all_repeated_boundary_quotient"),
            H("The literal all-repeated boundary quotient"),
            StatementSource.FromAuthor(F.Disp(QuotientStatement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("OriginalEBDomain abbreviates exactly the closedness, strict positivity, generating span and whole positive-dimensional exclusion-ball hypotheses in the preceding statement, with the same V, C and u. The extra assumption says that every original pure label p has a distinct original pure label s with the same entire exclusion set. This is the all-repeated contradiction branch, not an extra assumption on the eventual EB-only existence theorem.")),
                Paragraph(Text("RelationGraph(r) is the set of boundary pairs (x,y) with r(x,y). Setoid means an equivalence relation; QuotientMk is its canonical projection onto its actual quotient. The theorem constructs r as the literal boundary-midpoint predicate and proves that its classes are exactly the whole exclusion blocks through the second displayed equivalence.")),
                Paragraph(Text("To prove isolation, two shared distinct points force two whole exclusion balls to coincide, by applying the existing strict ball-face theorem to their intersection. If a repeated ball meets another different ball, their singleton intersection is pure. The two distinct labels of the repeated ball then force every pure point of that ball to have one common exclusion. Zero symmetry puts all those pure points in the other ball. Compact convex hull generation and maximality force equality, a contradiction. Thus different whole balls are disjoint in this branch, and the midpoint criterion makes the literal relation transitive.")),
                Paragraph(Text("The actual boundary is a closed subset of compact K. The midpoint map is continuous, so its inverse image of that boundary is a closed relation graph. The saturation of a closed boundary subset is the projection of the intersection of this graph with a compact product. It is closed, proving that the actual quotient projection is closed. Its fibers are compact by the same graph argument. The proper-map product theorem then makes the product projection a quotient map; the closed graph descends to the closed diagonal, proving the actual quotient Hausdorff. Compactness descends from the compact actual boundary. For each actual quotient point b, the ambient image of its entire projection fiber equals one whole original exclusion D(p); AmbientImage and Fiber denote precisely that image and inverse image of the singleton b. No convex subset or selected smaller ball replaces the full fiber.")),
                Paragraph(Text("This construction places no ENR, metrizability, finite dimension, fibration or local contractibility hypothesis on the quotient. The following results construct the common rational Baire slice, whole-fiber averaging, actual radial homotopy and sphere contradiction; the quotient assertion alone states none of those conclusions."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-all-repeated-rational-slice"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_all_repeated_rational_slice"),
            H("Actual rational slices, convex controls and whole-fiber averaging"),
            StatementSource.FromAuthor(F.Disp(RationalSliceStatement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("OriginalEBDomain has exactly the preceding closed generating pointed cone, strict original unit and entire positive-dimensional exclusion-ball hypotheses. V is nonzero. AllRepeated says every original label has a distinct original label with the same entire exclusion; it is used only as the contradiction branch. The setoid is again the actual boundary-midpoint relation. Its quotient remains compact Hausdorff with continuous closed canonical projection and whole original exclusions as its ambient fibers.")),
                Paragraph(Text("Choose a finite linear coordinate basis of the original V and restrict its coordinates to aff(K). Distinct points in each positive-dimensional whole fiber differ in some coordinate. Two rational heights strictly between their values give a countable family indexed by a finite coordinate and two rationals. Its closed set is the intersection of the projection images of the actual boundary halfspaces below the lower height and above the upper height. Both images are compact and closed; every actual quotient point belongs to one such crossing set.")),
                Paragraph(Text("Apply the pinned compact Hausdorff Baire theorem to this countable closed cover. Some crossing set has nonempty interior O. Let t be the rational midpoint of its heights and f the selected actual coordinate. Every b in O has actual boundary representatives x and y in its same whole fiber with f(x)<t<f(y). In particular the preimage of O contains actual points outside the slice. Convexity of each entire original fiber supplies a representative at the same level t, proving O is contained in the projection image of that one boundary slice. BoundaryLevelSet(f,t) denotes exactly the boundary subtype points x with f(x)=RealCast(t); no independent slice or supplier is assumed.")),
                Paragraph(Text("The same level genuinely meets ri(K). Choose an actual relative interior point c. If f(c)=t it suffices. Otherwise use the straddling endpoint on the opposite side; the open segment from c to that endpoint lies in ri(K), and its linear image contains t. The displayed interior-level witness therefore follows from the original K. The two strict inequalities also force f to be nonzero. With this actual c as origin, each entire shifted fiber is compact and convex and avoids zero. A sufficiently small open metric thickening is a convex neighborhood still avoiding zero. Closedness of the actual quotient projection gives an open label neighborhood on which every entire shifted fiber lies in that same convex neighborhood. Compactness of the actual quotient gives a finite subcover W indexed by Fin(n), with convex controls N avoiding zero. The displayed control applies to every boundary point x in every whole fiber over W(j), not just to selected representatives. Choose an actual boundary point v over O with f(v)>t. The positive ray R through v-c is closed. A ray from c meets the actual boundary only once: a smaller positive multiple is on an open segment from c to a boundary point, hence is in ri(K); a larger multiple gives the same contradiction with the roles reversed. Thus every whole fiber over a label outside O avoids R. For such labels, choose its convex thickening disjoint from both zero and R; for labels in O, intersect the label neighborhood with O. This supplies the displayed exceptional-label/ray-avoidance alternative for the actual finite controls. Subtract(x,c) is the ambient vector x-c and NotMember is nonmembership. RealCast is the rational-to-real coercion; AmbientImage and Fiber retain the meanings in the preceding statement.")),
                Paragraph(Text("The source conclusion also instantiates FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map on this actual quotient and these whole original fibers shifted by c. For each label in O choose its representative in the same level slice; elsewhere choose any actual quotient representative. With L the kernel of f, L intersect R is contained in the zero singleton because f(v-c)>0. The resulting continuous A takes values in TranslatedBase(C,u,c), avoids R and has zero-free segments from every point of every whole shifted fiber. PositiveRay(w) is exactly the set of z with SameRay(real,w,z), including zero; NotSameRay is its negation. TranslatedBase is exactly the image of the entire original K under z mapped to z-c, and ContinuousMaps means continuous maps. No normalized replacement or independent fiber supplier enters this instantiation. The following results construct the radial homotopy and transport it to the existing sphere noncontractibility theorem. This rational-slice assertion alone does not state singleton-label existence, boundary propagation or continuum multiplicity. This is an application of existing convex geometry and Baire theory, with no originality claim."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-all-repeated-zero-free-homotopy"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_all_repeated_zero_free_homotopy"),
            H("A zero-free homotopy in the actual affine direction space"),
            StatementSource.FromAuthor(F.Disp(HomotopyStatement())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let E be the direction of aff(K). The origin c belongs to the relative interior of the entire original K, and v belongs to its entire relative boundary S. Every vector x-c and every actual average A(pi(x)) lies in E because both endpoints lie in aff(K). Join x-c to A(pi(x)) by the first straight homotopy. Its zero avoidance is precisely the already established entire-fiber segment condition. Join A(pi(x)) to c-v by a second straight homotopy. If this second segment met zero, its endpoints would give SameRay(v-c,A(pi(x))), contrary to the actual positive-ray avoidance. Both are homotopies in the punctured E; their concatenation has the displayed endpoints. Since c is a relative interior point and v is a relative boundary point, v-c is nonzero, proving E nontrivial from the original geometry. The all-repeated premise belongs only to this contradiction branch. Product, Pair, UnitInterval and direction have their literal Cartesian-product, ordered-pair, closed unit-interval and affine-direction meanings; ambient coercions at the two endpoints are implicit."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-singleton-label-exists"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_singleton_label_exists"),
            H("Existence of an original singleton-label whole exclusion"),
            StatementSource.FromAuthor(F.Disp(SingletonStatement(false))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Suppose every original label had another label with the same whole exclusion. The preceding actual zero-free homotopy is then available. Translate aff(K) by its actual relative interior point c, identifying its direction E with aff(K), and let T be the preimage of the entire K. T is compact and convex, with zero in its interior. Apply the pinned gaugeRescaleHomeomorph from T to the closed unit ball. Its closure and interior image formulas give its frontier image formula, so restriction yields an actual homeomorphism J from the entire original relative boundary to the unit sphere of E. The gauge map fixes zero. Consequently applying it to the actual nowhere-zero homotopy, then normalizing and precomposing with J inverse, gives a sphere homotopy from its identity to a constant. Its initial endpoint follows from the exact translated-boundary formula for J, and its terminal endpoint is independent of the boundary input. This contradicts the existing compiled TauCeti noncontractibility theorem in the nontrivial finite-dimensional real normed space E. Thus an original singleton label exists. No new homology theorem, quotient regularity, equal ball dimensions, common fiber center or Pair premise is used."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-singleton-label-propagation"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_singleton_label_propagation"),
            H("Propagation over every original pure boundary point"),
            StatementSource.FromAuthor(F.Disp(SingletonStatement(true))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Apply SingleLabelNormalBody.single_label_neighbor directly to the original closed generating cone, strictly positive unit, entire exclusion-ball charts, globally singleton label p and any original pure q in D(p). Its SingleLabel predicate unfolds to uniqueness among all original pure labels, so the exact full conclusion follows with no additional assumptions. This propagation combines with singleton-label existence in original_singleton_label_family. In the repeated-ball isolation argument, SingleLabelNormalBody.equal_of_two_points gives equality of whole exclusions from two distinct shared points."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-singleton-label-family"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/ActualExclusionBoundary.original_singleton_label_family"),
            H("The original global singleton-label family and continuum multiplicity"),
            StatementSource.FromAuthor(F.Disp(FamilyStatement())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There exists an original pure p whose entire whole exclusion has the singleton label p. Every original pure q in that entire ball, equivalently every point of its entire ball boundary, is globally a singleton label. If every original label admits a whole-ball chart of dimension at least two, the selected chart b has two distinct coordinate indices. For each real parameter a form the Euclidean vector with coordinates 1, a and zeros, and normalize it to the unit sphere. Its zeroth coordinate before normalization is one, so it is nonzero. If two normalized vectors coincide, they lie on the same positive ray; comparison of the zeroth coordinates forces the ray scalar to be one, and comparison of the first coordinates forces the real parameters equal. The injective affine chart maps this sphere family to actual original pure boundary points of D(p). The propagation theorem makes each of these labels globally unique. Thus two of their entire exclusions can agree only when the labels, and hence the real parameters, agree. The resulting real-indexed embedding provides a subfamily of exactly continuum many original labels and pairwise distinct entire original balls. Embeddings means injective functions; WholeBallFamily(C,u,labels) is exactly the function a mapped to exclusion(C,u,labels(a)). The extra thickness premise quantifies over every original pure label and asks for a whole chart of dimension at least two; it assumes no equality of dimensions. The conclusion uses the entire original base, pure set and original effects throughout. This is a mathematical consequence within the stated model; it makes no physical realization or originality claim."))),
            DescribeRole.Theorem))));
}
