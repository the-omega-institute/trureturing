using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CollisionPrefixDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Walks/CollisionPrefix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered directed edge-collision counts",
        H("Ordered directed edge-collision counts"), Blocks(
            Paragraph(Text("A walk of length k is a function from Fin(k+1) to the vertex type. Its edge at i is the ordered pair of its vertices at i and i+1. Thus loops are included, the first position is distinguished, and no rotations are identified. Write E(w) for the finite image of the edge map and end(w) for the last vertex. The prefix deletes only the final edge and its terminal vertex. Collision(v,w) means that w starts at v, its prefix edges are pairwise distinct, its final edge occurs in the prefix, and every vertex is visited.")),
            Definition("Walk", "Ordered vertex walks", "For every vertex type V and natural k, Walk(V,k) is the function type Fin(k+1) to V."),
            Definition("edge", "Actual directed edges", "For any walk w and i in Fin(k), edge(w,i) is (w(i),w(i+1)), with both vertices interpreted in Fin(k+1)."),
            Definition("initialWalk", "Deleting the last edge", "For a walk of length k+1, initialWalk restricts its vertex function to the first k+1 positions."),
            Definition("Collision", "First collision at the final edge", "The walk starts at v, its first k directed edges are distinct, its final edge repeats one of them, and its vertex function is surjective."),
            Definition("OrderedEdges", "Source edge sequences", "An element consists of k+1 ordered pairs. The first tail is v, and each edge head equals the next edge tail."),
            Definition("orderedEdgesEquiv", "Reconstructing vertex walks", "For every V, v in V and natural k, based vertex walks of length k+1 are equivalent to OrderedEdges(V,v,k). The inverse writes v followed by the successive edge heads. Both composites are the identity."),
            Definition("SourceCollision", "Collision directly on ordered edges", "The first k edges are distinct, the last repeats one of them, and each vertex is either v or a head of one of the k+1 edges."),
            Definition("sourceCollisionEquiv", "Exact source collision correspondence", "For every V, v and k, collision vertex walks of length k+1 are equivalent to ordered edge sequences satisfying SourceCollision. The equivalence preserves the distinguished start, adjacency, distinctness, final repetition and vertex coverage. For finite V both carriers are finite and consequently have equal cardinalities."),
            Describe.Lean(DescribeId.Create("collision-prefix-structure"),
                DeclarationHandle.Create(Owner + "prefix_structure"),
                H("The two omitted-edge configurations"),
                StatementSource.FromAuthor(PrefixFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A trail of length n*n-1 on Fin(n), for n at least two, omits a unique ordered edge (a,b). Summing outgoing minus incoming incidences along the walk telescopes to the difference between its start and endpoint indicators. Summing over every directed pair gives zero, so removing (a,b) leaves the reverse indicator difference. Evaluating this identity at a and b leaves exactly two possibilities: b is the start and a the endpoint, or the omitted edge is a loop at another vertex and the walk is closed. Every vertex occurs because at least one of its n outgoing edges survives the single deletion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("collision-walk-prefix-structure"),
                DeclarationHandle.Create(Owner + "collision_prefix_structure"),
                H("The actual prefix of an edge-collision walk"),
                StatementSource.FromAuthor(CollisionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an edge-collision walk of length (n*n-1)+1, the same alternatives hold for its actual prefix with the specified starting vertex v. This length equals n*n for n at least two. The prefix already visits every vertex. The cardinality argument below retains these two classes separately."))),
                DescribeRole.Theorem),
            Definition("Euler", "Full ordered Euler walks", "Euler(n,v) consists of actual walks of length n*n starting at v whose edge map is bijective onto Fin(n) times Fin(n). The incidence sum proves that every such walk ends at v, and surjectivity of the edge map proves that it visits every vertex."),
            Definition("longCollisionEquiv", "Appending the repeated final edge", "For every n and v in Fin(n), collision walks of length n*n+1 are equivalent to Euler(n,v) times Fin(n). Delete the final edge in one direction. In the other, append the selected destination to the full Euler walk. All directed edges have already occurred, so the appended edge repeats one. The two operations are inverse on linear ordered walks."),
            Definition("collisionCount", "The literal collision count", "The value at total length zero is zero. At length k+1 the value is the finite cardinality of the source's ordered edge sequences satisfying SourceCollision, with fixed start v on n labeled vertices."),
            Definition("eulerCount", "The Euler-walk count", "The finite cardinality of Euler(n,v), with the first vertex and cut fixed."),
            Describe.Lean(DescribeId.Create("collision-long-count"),
                DeclarationHandle.Create(Owner + "long_count"), H("The denominator count"),
                StatementSource.FromAuthor(LongCountFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the exact source collision correspondence and the append/delete equivalence, then take finite cardinalities. The equality supplies the denominator factor n without assuming a factorial formula. The numerator and positivity are supplied separately below."))),
                DescribeRole.Theorem),
            Definition("insertLoop", "Inserting at a linear cut", "For every vertex type V, natural k, walk w of length k and cut p in Fin(k+1), insertLoop duplicates w(p) immediately after p. It inserts the loop (w(p),w(p)); every other edge retains its position through the order-preserving map skipping p."),
            Definition("removeLoop", "Deleting a marked loop", "For every V, k, walk w of length k+1 and edge position p, removeLoop deletes the head of that edge. If the marked edge is a loop, deletion and insertion are inverse."),
            Definition("MissingLoop", "Trails missing one specified loop", "For n, fixed start v and vertex a, MissingLoop(n,v,a) consists of length n*n-1 walks starting at v with injective edge map and edge image exactly all directed pairs except (a,a)."),
            Definition("MarkedLoop", "Retaining the insertion cut", "For n, v and a, MarkedLoop(n,v,a) pairs a MissingLoop trail with a vertex position p at which the trail equals a. Positions remain distinct even when their vertex values agree."),
            Definition("loopInsertionEquiv", "The marked loop bijection", "For n at least two and all v,a in Fin(n), inserting the missing loop at the marked cut is an equivalence from MarkedLoop(n,v,a) to Euler(n,v). The inverse locates the unique loop (a,a), deletes its head vertex, and retains its position. The construction applies also to a=v, retaining both boundary cuts when distinct."),
            Theorem("loop_count", "Counting the noninitial loop cuts", LoopCountFormula(),
                "For a different from v, a missing-loop trail is closed at v, so neither boundary cut is at a. Its cuts at a correspond bijectively to its outgoing edges (a,b), b different from a. There are exactly n-1. The marked-loop bijection therefore gives E=(n-1)L(a)."),
            Definition("ReturnTrail", "Prefixes completed by their closing edge", "For n and v, ReturnTrail(n,v) consists of length n*n-1 trails starting at v whose unique omitted edge goes from their endpoint back to v."),
            Definition("returnTrailEquiv", "Completing the return prefix", "For n at least two and v in Fin(n), append v to a ReturnTrail to obtain an Euler walk. Deleting the last edge is the inverse. This counts these linear prefixes by E."),
            Theorem("short_count", "The numerator count", ShortCountFormula(),
                "Partition almost-complete collision prefixes by the omitted-edge classification. A ReturnTrail has n-1 repeated-edge choices, excluding the omitted edge back to v. A trail missing (a,a), a different from v, ends at v and has all n final choices. The loop bijections give (n-1)L(a)=E; summing over the n-1 vertices and cancelling n-1 gives the sum of L(a) equal to E. Thus the numerator is (n-1)E+nE=(2n-1)E."),
            Theorem("euler_nonempty", "Constructing a full Euler walk", EulerNonemptyFormula(),
                "Start with the zero-length walk at v. Extend the trail by an unused outgoing edge, reserving each edge (a,v) until every other outgoing edge from a is used. If the endpoint has no unused departure, incidence balance forces it to be v. All edges entering v must then have occurred; the reserved-last-exit invariant forces every directed edge to have occurred. Hence the construction extends until exactly n*n distinct edges are used. This works for every n with a specified v in Fin(n)."),
            Theorem("long_count_positive", "Positive source denominator", PositiveFormula(),
                "The constructed Euler walk makes its finite count positive. The exact denominator bijection gives T(n,n*n+1)=nE, which is positive for n at least two."),
            Theorem("collision_ratio", "The exact all-n rational ratio", RatioFormula(),
                "For every n at least two and arbitrary fixed v in Fin(n), substitute the two source count identities and cancel the positive Euler count. Both carriers count ordered walks with loops and vertex coverage; no rotation quotient or separate factorial count is assumed.",
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a396659-edge-collision-ratio"),
                    ResolutionKind.Proved, [DeclarationHandle.Create(Owner + "long_count_positive")])))));

    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("collision-prefix-definition-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, Formula formula, string text,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("collision-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem, resolution);

    private static Formula Times(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Minus(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Square(Formula n) => Times(n, n);
    private static Formula Next(Formula a) => new Formula.Binary(a, FormulaBinaryOperator.Add, D(1));
    private static Formula Based(Formula body) => All("n", Call("Nat"), Imp(Le(D(2), F.Id("n")),
        All("v", Call("Fin", F.Id("n")), body)));
    private static Formula LoopCountFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v"), a = F.Id("a");
        return Disp(Based(All("a", Call("Fin", n), Imp(new Formula.Not(Eq(a, v)),
            Eq(Call("eulerCount", n, v), Times(Minus(n, D(1)),
                Call("card", Call("MissingLoop", n, v, a))))))));
    }
    private static Formula ShortCountFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v");
        return Disp(Based(Eq(Call("collisionCount", n, v, Square(n)),
            Times(Minus(Times(D(2), n), D(1)), Call("eulerCount", n, v)))));
    }
    private static Formula EulerNonemptyFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v");
        return Disp(All("n", Call("Nat"), All("v", Call("Fin", n),
            Call("Nonempty", Call("Euler", n, v)))));
    }
    private static Formula PositiveFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v");
        return Disp(Based(new Formula.Relation(D(0), FormulaRelationOperator.LessThan,
            Call("collisionCount", n, v, Next(Square(n))))));
    }
    private static Formula RatioFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v");
        return Disp(Based(Eq(new Formula.Fraction(Call("collisionCount", n, v, Square(n)),
            Call("collisionCount", n, v, Next(Square(n)))),
            new Formula.Fraction(Minus(Times(D(2), n), D(1)), n))));
    }

    private static Formula LongCountFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v");
        Formula length = new Formula.Binary(new Formula.Binary(n, FormulaBinaryOperator.Multiply, n),
            FormulaBinaryOperator.Add, D(1));
        return Disp(All("n", Call("Nat"), All("v", Call("Fin", n),
            Eq(Call("collisionCount", n, v, length),
                new Formula.Binary(n, FormulaBinaryOperator.Multiply, Call("eulerCount", n, v))))));
    }

    private static Formula PrefixFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w");
        return Disp(All("n", Call("Nat"), Imp(Le(D(2), n),
            All("w", Call("Walk", Call("Fin", n), Size(n)),
                Imp(Call("Injective", Call("edge", w)), Conclusion(n, w, Call("at", w, D(0))))))));
    }

    private static Formula CollisionFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v"), w = F.Id("w");
        Formula length = new Formula.Binary(Size(n), FormulaBinaryOperator.Add, D(1));
        return Disp(All("n", Call("Nat"), Imp(Le(D(2), n),
            All("v", Call("Fin", n), All("w", Call("Walk", Call("Fin", n), length),
                Imp(Call("Collision", v, w), Conclusion(n, Call("prefix", w), v)))))));
    }

    private static Formula Conclusion(Formula n, Formula w, Formula start)
    {
        Formula a = F.Id("a"), b = F.Id("b"), end = Call("end", w);
        Formula first = And(Eq(b, start), Eq(end, a));
        Formula second = And(Eq(a, b), And(new Formula.Not(Eq(a, start)), Eq(end, start)));
        Formula missing = Eq(Call("E", w), Call("erase", Call("univ"), Call("pair", a, b)));
        return And(Call("Surjective", w), Ex("a", Call("Fin", n),
            Ex("b", Call("Fin", n), And(missing, new Formula.Logic(first, FormulaLogicOperator.Or, second)))));
    }

    private static Formula Size(Formula n) => new Formula.Binary(
        new Formula.Binary(n, FormulaBinaryOperator.Multiply, n), FormulaBinaryOperator.Subtract, D(1));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
}
