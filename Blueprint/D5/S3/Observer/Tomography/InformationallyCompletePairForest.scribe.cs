using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class InformationallyCompletePairForestDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Observer/Tomography/InformationallyCompletePairForest";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Observer/gudder2019finiteconvexeffect");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two finite real random variables determine every probability weight exactly when their joint value map is injective and their bipartite fiber graph is a forest.",
        H("Informationally complete pairs and forests"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distribution"),
                DeclarationHandle.Create(Module + ".distribution"),
                H("The distribution on an arbitrary set"),
                StatementSource.FromAuthor(Disp(DistributionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real random variable f on a finite type α and a real weight μ, "
                    + "the value of the distribution on δ is the sum of μ over the points "
                    + "whose f-values lie in δ. This is the distribution in Section 5, "
                    + "lines 435–439 of the TeX source, extended to arbitrary real weights "
                    + "and arbitrary finite types. No measurability restriction is needed "
                    + "on δ because the sum is finite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-ic-pair"),
                DeclarationHandle.Create(Module + ".IsICPair"),
                H("Informational completeness of a pair"),
                StatementSource.FromAuthor(Disp(IsICPairFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The pair f, g is informationally complete if equality of both "
                    + "distributions forces equality of the probability weights μ and ν. "
                    + "Probability means that every weight is nonnegative and the sum of "
                    + "the weights is one. Equality of distributions is equality as functions "
                    + "on all subsets of the real line. This is the definition at line 474 "
                    + "of Section 5 of the TeX source; the finite type α may also be empty "
                    + "or have a single element."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fiber-graph"),
                DeclarationHandle.Create(Module + ".fiberGraph"),
                H("The bipartite fiber graph"),
                StatementSource.FromAuthor(Disp(FiberGraphFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The vertices are two tagged copies of the real line. A left vertex "
                    + "a and a right vertex b are adjacent exactly when some x has f(x) = a "
                    + "and g(x) = b. SimpleGraph.fromRel makes this relation symmetric and "
                    + "excludes loops. There are no edges within either tagged copy, and "
                    + "values outside the ranges of f and g are isolated vertices. Several "
                    + "points with the same joint value give the same simple edge; injectivity "
                    + "of the joint value map records the absence of that multiplicity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The forest characterization"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The joint value map is injective exactly when every nonempty "
                        + "intersection of an f-level set and a g-level set is a singleton. "
                        + "This is complementarity in Section 5, lines 507–508 of the TeX "
                        + "source. The equivalence characterizes the IC pairs asked for at "
                        + "line 588: complementarity must be accompanied by acyclicity of "
                        + "the fiber graph. It holds for every finite α, including the empty "
                        + "and singleton cases.")),
                    Paragraph(Text(
                        "First, two distributions for f are equal if and only if the "
                        + "weights have equal sums on every f-level set. Evaluating the "
                        + "distributions on singletons proves necessity. For sufficiency, "
                        + "group the finite sum over the inverse image of any δ by the "
                        + "finitely many f-values occurring there, and apply equality on "
                        + "each level set.")),
                    Paragraph(Text(
                        "If the joint value map is not injective, take distinct points "
                        + "x and y with both f(x) = f(y) and g(x) = g(y). The point masses "
                        + "at x and y are distinct probabilities, but each random variable "
                        + "has the same distribution under the two point masses. Thus an "
                        + "IC pair has an injective joint value map.")),
                    Paragraph(Text(
                        "Assume the joint value map is injective. A trail p from u to v "
                        + "in the fiber graph determines a signed weight w on α. Its "
                        + "f-level sum at a is the indicator of u = Sum.inl(a) minus the "
                        + "indicator of v = Sum.inl(a); its g-level sum at b is the "
                        + "indicator of v = Sum.inr(b) minus the indicator of u = Sum.inr(b). "
                        + "Moreover, w is nonzero exactly at the points whose edges occur "
                        + "in p, and every absolute weight is at most one. To construct w, "
                        + "start with the zero weight on the empty trail. Prepending an "
                        + "edge from left to right adds the point mass with coefficient one "
                        + "at its unique point; prepending an edge from right to left adds "
                        + "the point mass with coefficient minus one. The trail condition "
                        + "keeps that edge out of the tail, so its previous weight is zero. "
                        + "Injectivity identifies its point uniquely, preserving the support "
                        + "description and the absolute bound. The marginal sums telescope "
                        + "to the stated endpoint indicators.")),
                    Paragraph(Text(
                        "Any nonzero w with absolute weights at most one and zero sums "
                        + "on all f-level sets and g-level sets gives distinct probabilities "
                        + "with equal distributions. Indeed, a nonzero coordinate makes α "
                        + "nonempty. Let n be its cardinality cast from a natural number to "
                        + "a real number, so n is positive. Summing the f-level sums gives "
                        + "total weight zero. Put μ(x) = (1 + w(x))/n and ν(x) = 1/n. "
                        + "The absolute bound makes μ nonnegative, and both total weights "
                        + "are one. The zero level sums make the two distributions agree "
                        + "for f and for g, while a nonzero coordinate of w makes μ and ν "
                        + "distinct.")),
                    Paragraph(Text(
                        "A cycle is a nonempty closed trail. Its endpoint indicators "
                        + "cancel, so the signed trail weight has zero sums on every level "
                        + "set. Some edge occurs in the cycle, and the exact support "
                        + "description makes this weight nonzero. The preceding perturbation "
                        + "then contradicts informational completeness. Combining this with "
                        + "injectivity proves that every IC pair has an acyclic fiber graph.")),
                    Paragraph(Text(
                        "Conversely, suppose the joint value map is injective and the "
                        + "fiber graph is acyclic. Let probabilities μ and ν have equal "
                        + "distributions for f and for g. For w = μ − ν, every f-level sum "
                        + "and every g-level sum is zero. Suppose w is nonzero, and retain "
                        + "only the edges arising from points where w is nonzero; call this "
                        + "graph H. It is a subgraph of the fiber graph and hence acyclic. "
                        + "Its edge set is contained in the image of finite α, so H has "
                        + "finitely many edges and is locally finite. A nonzero coordinate "
                        + "supplies an edge of H. Its connected component C contains both "
                        + "tagged endpoints, and is therefore a nontrivial tree with finitely "
                        + "many edges. Such a tree has vertices of degree one; choose one "
                        + "of them, u, with its unique neighbor q.")),
                    Paragraph(Text(
                        "The edge from u to q comes from a point y with w(y) nonzero. "
                        + "If u is a left vertex a, every other point z in the f-level set "
                        + "at a has weight zero: a nonzero weight would give another "
                        + "neighbor of u in C, so uniqueness of q forces g(z) = g(y), "
                        + "and injectivity then forces z = y. Thus the f-level sum is "
                        + "w(y), contradicting its vanishing. If u is a right vertex, "
                        + "the identical argument uses its g-level set and forces equality "
                        + "of the f-values. Both possibilities contradict w(y) being "
                        + "nonzero. Consequently w = 0, so μ = ν and the pair is IC."))),
                DescribeRole.Theorem))));

    private static Formula DistributionFormula() => FiniteBinders(
        All("f", RealWeights, All("μ", RealWeights, All("δ", At(Qualified("Set"), Reals),
            Equal(Typed(LocalCall("distribution", X("f"), X("μ"), X("δ")), Reals),
                At(Qualified("Finset", "sum"),
                    At(Qualified("Finset", "filter"),
                        LambdaOf("x", Alpha, Member(At(X("f"), X("x")), X("δ"))),
                        Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), Alpha))),
                    LambdaOf("x", Alpha, At(X("μ"), X("x")))))))));

    private static Formula IsICPairFormula() => PairBinders(Equivalence(
        LocalCall("IsICPair", X("f"), X("g")),
        All("μ", RealWeights, All("ν", RealWeights,
            Implies(Probability(X("μ")), Implies(Probability(X("ν")),
                Implies(Equal(LocalCall("distribution", X("f"), X("μ")),
                        LocalCall("distribution", X("f"), X("ν"))),
                    Implies(Equal(LocalCall("distribution", X("g"), X("μ")),
                            LocalCall("distribution", X("g"), X("ν"))),
                        Equal(X("μ"), X("ν"))))))))));

    private static Formula FiberGraphFormula()
    {
        Formula noEdges = At(Qualified("Function", "const"), Reals, Qualified("False"));
        Formula jointFiber = Some("x", Alpha, And(
            Equal(At(X("f"), X("x")), X("a")),
            Equal(At(X("g"), X("x")), X("b"))));
        Formula relation = LambdaOf("v", Vertex, LambdaOf("w", Vertex,
            At(Qualified("Sum", "elim"),
                LambdaOf("a", Reals, At(Qualified("Sum", "elim"), noEdges,
                    LambdaOf("b", Reals, jointFiber), X("w"))),
                noEdges, X("v"))));
        return PairBinders(Equal(
            Typed(LocalCall("fiberGraph", X("f"), X("g")), At(Qualified("SimpleGraph"), Vertex)),
            At(Qualified("SimpleGraph", "fromRel"), relation)));
    }

    private static Formula ResultFormula() => PairBinders(Equivalence(
        LocalCall("IsICPair", X("f"), X("g")),
        And(At(Qualified("Function", "Injective"), LambdaOf("x", Alpha,
                Pair(At(X("f"), X("x")), At(X("g"), X("x"))))),
            At(Qualified("SimpleGraph", "IsAcyclic"), LocalCall("fiberGraph", X("f"), X("g"))))));

    private static Formula FiniteBinders(Formula body) => All("α", Seq(Qualified("Type"), Star),
        Seq(OpenBracket, At(Qualified("Fintype"), Alpha), CloseBracket, Sp,
            OpenBracket, At(Qualified("DecidableEq"), Alpha), CloseBracket, Comma, Sp,
            Parenthesized(body)));
    private static Formula PairBinders(Formula body) => FiniteBinders(
        All("f", RealWeights, All("g", RealWeights, body)));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula RealWeights => new Formula.TypeArrow(Alpha, Reals);
    private static Formula Vertex => At(Qualified("Sum"), Reals, Reals);
    private static Formula X(string name) => name switch
    {
        "α" => Alpha,
        "μ" => Mu,
        "ν" => Nu,
        "δ" => DeltaLower,
        _ => F.Id(name),
    };
    private static Formula LocalCall(string name, params Formula[] args) => At(
        Qualified("D5", "S3", "Observer", "Tomography", "InformationallyCompletePairForest", name), args);
    private static Formula Probability(Formula weight) => At(
        Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), weight);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
