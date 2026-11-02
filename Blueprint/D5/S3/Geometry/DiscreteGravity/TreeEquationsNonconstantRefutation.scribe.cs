using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.DiscreteGravity;

internal sealed class TreeEquationsNonconstantRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Geometry/DiscreteGravity/TreeEquationsNonconstantRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Geometry/huangstoicaxiazhong2020einstein");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cubic tree admits positive nonconstant edge lengths satisfying the tree equations of motion.",
        H("A positive nonconstant solution of the tree equations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("c-val"),
                DeclarationHandle.Create(Module + ".cVal"),
                H("The sum of reciprocal incident lengths"),
                StatementSource.FromAuthor(Disp(CValFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a locally finite simple graph g and a real function ell on ordered pairs of vertices, "
                    + "cVal sums the reciprocal lengths over the neighbours of i. This is c_i in "
                    + "Huang, Stoica, Xia and Zhong, ms.tex line 257. On a tree with positive edge lengths, "
                    + "the shortest-path length P_ij of adjacent vertices equals their edge length "
                    + "(lines 233–237 and 538). The definition itself imposes neither positivity nor symmetry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("d-val"),
                DeclarationHandle.Create(Module + ".dVal"),
                H("The sum of reciprocal squared incident lengths"),
                StatementSource.FromAuthor(Disp(DValFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The quantity dVal sums the reciprocals of the squares of the incident lengths. "
                    + "It is d_i of ms.tex line 255, with the same finite neighbour set as cVal. "
                    + "Both definitions use real division, including its value zero when the denominator is zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ratio"),
                DeclarationHandle.Create(Module + ".ratio"),
                H("The vertex ratio"),
                StatementSource.FromAuthor(Disp(RatioFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The vertex ratio is cVal divided by dVal, the quantity c_i/d_i occurring in "
                    + "the tree equation of motion at ms.tex line 552. No nonzero-denominator hypothesis "
                    + "is part of this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("t-eom"),
                DeclarationHandle.Create(Module + ".tEoM"),
                H("The tree equation residual"),
                StatementSource.FromAuthor(Disp(TEoMFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The residual on an ordered pair i,j is the reciprocal length times the sum of the "
                    + "squared vertex ratios, minus the two ratios. Its vanishing on every edge is "
                    + "the tree equation of motion in ms.tex lines 549–554. The formula defines a real "
                    + "value on every ordered pair; adjacency is required when asserting the equation on edges."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The conjecture on the cubic tree"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimProposition()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The second conjecture in Section 5.2, ms.tex lines 1931–1934, asserts that T₂ "
                    + "has no positive nonconstant solution. The source defines T_q to have degree q+1 "
                    + "at every vertex (line 542) and calls equal edge lengths the constant solution "
                    + "(line 556). Here the assertion ranges over every locally finite simple tree "
                    + "on a type v with degree three everywhere and decidable adjacency. For each "
                    + "real length function symmetric and positive on edges, vanishing of every edge "
                    + "residual would imply a single real value c for all edge lengths. No boundary "
                    + "condition or uniform positive lower bound on lengths is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A cubic tree with a positive nonconstant solution"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use vertices vₙ indexed by integers n and vertices bₙ,𝑤 indexed by an integer "
                        + "and a finite Boolean list w. Define a predecessor p by p(vₙ)=vₙ₋₁, "
                        + "p(bₙ,∅)=vₙ, and p(bₙ,β::w)=bₙ,𝑤. Give vₙ height n and bₙ,𝑤 height "
                        + "n+1+|w|, where the natural list length is included in the integers. "
                        + "Every predecessor lowers height by one. Join two vertices precisely when "
                        + "one is the predecessor of the other; this is symmetric and has no loops.")),
                    Paragraph(Text(
                        "The neighbours of vₙ are vₙ₋₁, vₙ₊₁ and bₙ,∅. The neighbours of bₙ,𝑤 "
                        + "are its predecessor, bₙ,false::w and bₙ,true::w. These lists give all "
                        + "neighbours, with three distinct entries in each case: the two children "
                        + "differ in their first Boolean, and their height exceeds that of the "
                        + "predecessor. Thus the simple graph is locally finite and has degree three everywhere.")),
                    Paragraph(Text(
                        "Every vₙ is connected to v₀ by finitely many spine edges, using integer "
                        + "induction in both directions. Repeatedly removing the first Boolean connects "
                        + "bₙ,𝑤 to vₙ, so all vertices are connected. If a cycle existed, choose "
                        + "a vertex of maximal height on it and rotate the cycle to start there. "
                        + "Each of its two cycle neighbours has height at most that maximum and "
                        + "therefore must be its unique predecessor. This identifies the second "
                        + "and penultimate vertices of the cycle, a contradiction. The graph is a tree.")),
                    Paragraph(Text(
                        "Set sₙ=2ⁿ in the real numbers, with integer exponent n. Then sₙ is positive, "
                        + "sₙ₊₁=2sₙ and sₙ₋₁=sₙ/2. Define a real function L on all ordered pairs by "
                        + "L(vₙ,vₘ)=(5/3)sₖ, L(vₙ,bₘ,𝑤)=sₘ, "
                        + "L(bₙ,𝑤,vₘ)=sₙ and L(bₙ,𝑤,bₘ,𝑧)=sₖ, where k=min(n,m). "
                        + "These expressions are symmetric and positive. On an edge vₙ∼vₙ₊₁ "
                        + "the length is (5/3)sₙ; on every edge in the branch attached to vₙ, "
                        + "including its attachment edge, the length is sₙ.")),
                    Paragraph(Text(
                        "At vₙ the three incident lengths are 5sₙ/6, 5sₙ/3 and sₙ. Summing "
                        + "their reciprocals gives cVal=14/(5sₙ), while summing their reciprocal "
                        + "squares gives dVal=14/(5sₙ²). Their ratio is sₙ. At bₙ,𝑤 all "
                        + "three incident lengths are sₙ, so cVal=3/sₙ, dVal=3/sₙ² and the "
                        + "ratio is again sₙ. Positivity of sₙ permits the divisions in both calculations.")),
                    Paragraph(Text(
                        "First evaluate the residual on each edge from a vertex to its predecessor. "
                        + "For vₙ and vₙ₋₁ the endpoint ratios are sₙ and sₙ/2 and the length "
                        + "is 5sₙ/6. Hence the residual is "
                        + "(sₙ²+(sₙ/2)²)/(5sₙ/6)−sₙ−sₙ/2=0. "
                        + "For bₙ,𝑤 and its predecessor, whether w is empty or nonempty, "
                        + "the ratios at both endpoints and the edge length are sₙ, giving "
                        + "2sₙ²/sₙ−2sₙ=0. Every edge has one of these orientations; symmetry "
                        + "of L and the residual expression gives zero for the reverse orientation as well.")),
                    Paragraph(Text(
                        "The attachment edge v₀∼b₀,∅ has length 1, whereas v₀∼v₁ has length "
                        + "5/3, so the edge lengths cannot all equal a single c. Applying the "
                        + "conjectured implication to this tree and L would give exactly such "
                        + "a c, contradicting these two edge values."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("huang-stoica-xia-zhong-2020-tree-equations-nonconstant"),
                    ResolutionKind.Refuted)))));

    private static Formula CValFormula() => LengthBinders(All("i", X("v"),
        Equal(Typed(LocalCall("cVal", X("g"), X("ell"), X("i")), Reals()),
            SumNeighbours(Div(Typed(D(1), Reals()), EdgeLength(X("i"), X("j")))))));

    private static Formula DValFormula() => LengthBinders(All("i", X("v"),
        Equal(Typed(LocalCall("dVal", X("g"), X("ell"), X("i")), Reals()),
            SumNeighbours(Div(Typed(D(1), Reals()), Square(EdgeLength(X("i"), X("j"))))))));

    private static Formula RatioFormula() => LengthBinders(All("i", X("v"),
        Equal(Typed(VertexRatio(X("i")), Reals()),
            Div(LocalCall("cVal", X("g"), X("ell"), X("i")),
                LocalCall("dVal", X("g"), X("ell"), X("i"))))));

    private static Formula TEoMFormula() => LengthBinders(All("i", X("v"), All("j", X("v"),
        Equal(Typed(LocalCall("tEoM", X("g"), X("ell"), X("i"), X("j")), Reals()),
            Subtract(Subtract(
                Multiply(Div(Typed(D(1), Reals()), EdgeLength(X("i"), X("j"))),
                    Add(Square(VertexRatio(X("i"))), Square(VertexRatio(X("j"))))),
                VertexRatio(X("i"))), VertexRatio(X("j")))))));

    private static Formula ClaimProposition()
    {
        Formula symmetric = OnEdges(Equal(EdgeLength(X("i"), X("j")), EdgeLength(X("j"), X("i"))));
        Formula positive = OnEdges(LessThan(Typed(D(0), Reals()), EdgeLength(X("i"), X("j"))));
        Formula solution = OnEdges(Equal(LocalCall("tEoM", X("g"), X("ell"), X("i"), X("j")),
            Typed(D(0), Reals())));
        Formula constant = Some("c", Reals(), OnEdges(Equal(EdgeLength(X("i"), X("j")), X("c"))));
        return GraphBinders(Instance(
            At(Qualified("DecidableRel"), At(Qualified("SimpleGraph", "Adj"), X("g"))),
            Arrow(At(Qualified("SimpleGraph", "IsTree"), X("g")),
                Arrow(All("i", X("v"), Equal(At(Qualified("SimpleGraph", "degree"), X("g"), X("i")),
                        Typed(D(3), Naturals()))),
                    All("ell", LengthType(), Arrow(symmetric, Arrow(positive, Arrow(solution, constant))))))));
    }

    private static Formula GraphBinders(Formula body) => All("v", Qualified("Type"),
        All("g", At(Qualified("SimpleGraph"), X("v")),
            Instance(At(Qualified("SimpleGraph", "LocallyFinite"), X("g")), body)));
    private static Formula LengthBinders(Formula body) => GraphBinders(All("ell", LengthType(), body));
    private static Formula LengthType() => Arrow(X("v"), Arrow(X("v"), Reals()));
    private static Formula OnEdges(Formula body) => All("i", X("v"), All("j", X("v"),
        Arrow(At(Qualified("SimpleGraph", "Adj"), X("g"), X("i"), X("j")), body)));
    private static Formula SumNeighbours(Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(X("j"), Sp, InMacro, Sp,
            At(Qualified("SimpleGraph", "neighborFinset"), X("g"), X("i")))),
        Sp, Parenthesized(body));
    private static Formula EdgeLength(Formula i, Formula j) => At(X("ell"), i, j);
    private static Formula VertexRatio(Formula i) => LocalCall("ratio", X("g"), X("ell"), i);
    private static Formula Local(string name) => Qualified("D5", "S3", "Geometry", "DiscreteGravity",
        "TreeEquationsNonconstantRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula hypothesis, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(hypothesis), Parenthesized(conclusion));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
}
