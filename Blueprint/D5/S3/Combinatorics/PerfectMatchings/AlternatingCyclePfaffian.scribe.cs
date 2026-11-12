using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class AlternatingCyclePfaffianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual alternating-cycle flips transport canonical Pfaffian coefficients; odd opposition on actual nice cycles makes all matching coefficients equal.",
        H("Actual cycle transport and matching signs"),
        Blocks(Describe.Lean(DescribeId.Create("matching-equivalence"),
            DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.matchingEquiv"),
            H("The matching equivalence"), StatementSource.FromAuthor(MatchDefinition()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a perfect matching M, matchingMate chooses the unique vertex adjacent to each vertex. Symmetry makes this map involutive; looplessness excludes fixed points. Conversely, a partner map p defines a spanning subgraph by adjacency p(v) = w. Involutivity supplies symmetry, and the partner is the unique neighbor. The two constructions are inverse, including on the empty vertex type. The matching objects are Mathlib SimpleGraph.Subgraph objects, rather than an additional matching datatype."))),
            DescribeRole.Definition),

            Paragraph(Text("For an enumeration e from V to Fin(2n), an actual perfect matching is transported to the complete graph and converted by matchingEquiv into its partner map. Its canonical listing c orders each pair increasingly and then orders pairs by their first endpoints. Given actual dart bits epsilon, dartSign(d) is the integer unit (-1) raised to epsilon(d), using the ZMod(2) action on integer units. It equals one at bit zero and minus one at bit one. The reversal hypothesis is epsilon(symm(d)) = 1 + epsilon(d); it implies dartSign(symm(d)) = -dartSign(d). The matching coefficient matchingTau(e,epsilon,M) is sign(c) times the product of these signs on the actual directed matching edges listed by c. Reordering the pairs or reversing individual pairs gives the same signed unit factor.")),
            Paragraph(Text("For any commutative ring R and weights w on the actual undirected edges of G, orientedMatrix(e,epsilon,w) has entry intCast(dartSign(x,y)) times w({x,y}) on an actual edge and zero on nonedges. Its diagonal is explicitly zero, including in characteristic two. matchingWeight(w,M) multiplies over the subtype of actual undirected edges of M; partitionFunction(w) sums these products over actual perfect-matching subgraphs. Empty products are one and empty sums are zero. The nice-cycle hypothesis NiceOdd(epsilon) quantifies over actual simple even closed walks p whose actual vertex-deleted induced complement has an actual perfect matching; it requires the sum of epsilon along p.darts to be one in ZMod(2). These definitions do not assume a common matching sign.")),
            Paragraph(Text("The native FixedPointFreeInvolution carrier consists of involutive fixed-point-free permutations. For each n, a partner map in P(n) becomes such a permutation by Equiv.ofBijective applied to its involutive underlying function; forgetting the permutation structure is the inverse. Both composites preserve the underlying partner function pointwise. Thus the original partner maps and native carrier describe exactly the same pairings, including n = 0. This correspondence concerns the partner action; the Pfaffian coefficient remains the sign of the normalized listing permutation, not the sign of the involutive partner permutation.")),
            Describe.Lean(DescribeId.Create("cycle-flip"),
            DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.alternating_cycle_flip"),
            H("A flip and its actual complement"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let G be any simple graph, M an actual perfect-matching subgraph, and p an actual simple closed walk. Write C for p.toSubgraph and let Alt(C,M) mean that among two distinct edges of C incident to a vertex, precisely one belongs to M. No embedding, connectedness, finiteness, orientation, or weight assumption is required for this statement.")),
                Paragraph(Text("The flipped graph has edge set equal to the symmetric difference of M and C. Its edges are still actual G-edges. Mathlib's perfect-matching symmetric-difference theorem proves that the resulting spanning subgraph is a perfect matching. The displayed adjacency equivalence toggles exactly the cycle edges and preserves all other edges, including shared matching edges outside C.")),
                Paragraph(Text("Every vertex of C has two distinct neighbors in C. Alternation places precisely one of those edges in M. Restricting M to the vertices of C gives a perfect matching there. Those vertices are enumerated injectively by the walk indices before the repeated endpoint. The even-cardinality theorem for actual perfect matchings therefore proves that p has even length. Uniqueness of the matching partner also prevents an M-edge from crossing between the vertices of C and their complement. Restricting the same M to the induced graph on the complementary vertex set gives an actual perfect matching there. The notation Induce(G,Complement(Verts(C))) denotes this graph, with vertices the subtype of original vertices outside C.")),
                Paragraph(Text("The same actual complement matching supplies the nice-cycle premise in the coefficient and uniformity statements below."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cycle-transport"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.alternating_cycle_transport"),
                H("Transport of the actual coefficient"), StatementSource.FromAuthor(Transport()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/RibbonEmbeddings/cimasoni2007dimers")),
                Blocks(
                    Paragraph(Text("Let PM(G) denote the subtype of actual perfect-matching subgraphs. For M in PM(G), tau(e,epsilon,M) is matchingTau, the genuine canonical permutation coefficient multiplied by the actual directed-edge signs. The theorem constructs N in PM(G) with exactly the displayed toggle adjacency and proves the coefficient product. It assumes reversal of epsilon and actual alternation, without assuming nice-cycle oddness or equality of matching signs.")),
                    Paragraph(Text("Rotate the vertices of p once in walk order and fix every vertex outside p. The simple-cycle condition makes this a permutation. Its support has the even cardinality length(p), so its sign is minus one. Among the two cycle neighbors of each cycle vertex, precisely one is its M-partner. The rotation therefore sends every M-edge on the cycle to the complementary cycle edge. Each outside M-edge has both endpoints outside the cycle and is fixed. Applying this permutation to the canonical listing of M gives a listing of the actual flipped matching N; signed listing normalization identifies its value with tau(e,epsilon,N).")),
                    Paragraph(Text("For an M-pair x,y on the cycle, multiply the sign on x,y by the sign on its rotated pair. The result is the product of the forward dart signs at x and y. If the listed pair points backward, reversal negates both factors and leaves their product unchanged. For an outside pair the identical sign occurs twice and its product is one in the integer units. Reindexing over all vertices gives the dart product around p, with the single minus sign contributed by the cycle rotation. The argument preserves a common outside pairing even when its labels interleave with cycle labels. This is the composition-cycle sign relation of Cimasoni and Reshetikhin, Section 5.1, realized here on actual simple-graph subgraphs and walks."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-coefficients"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.niceOdd_matching_tau_eq"),
                H("Nice cycles force a common sign"), StatementSource.FromAuthor(Uniform()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/RibbonEmbeddings/cimasoni2007dimers")),
                Blocks(
                    Paragraph(Text("For two actual perfect matchings, their spanning symmetric difference has degree zero or two. If it is nonempty, its finite component through a disagreement edge supplies an actual simple cycle. The cycle is alternating with respect to the first matching and lies in the same original graph. Its induced vertex-deleted complement has the perfect matching supplied by that first matching. NiceOdd makes its dart-sign product minus one. The transport relation then makes the coefficients of the matching and its flip equal.")),
                    Paragraph(Text("Flipping removes the chosen cycle from the disagreement graph. Its edge set strictly decreases, so induction on the finite number of disagreement edges ends at the second matching. Shared matching edges are outside the disagreement graph throughout. The proof includes disconnected graphs and the case M = N. It requires neither an embedding nor existence of a perfect matching as an extra hypothesis; the statement quantifies over any two that exist."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-identity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.weighted_pfaffian_identity"),
                H("One unit for all weights and coefficient rings"), StatementSource.FromAuthor(Identity()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/RibbonEmbeddings/cimasoni2007dimers")),
                Blocks(
                    Paragraph(Text("Use listingEquiv to reindex the independently defined standard sum by the supplied partner maps. A partner map is supported precisely when all its paired vertices are joined by actual G-edges. The supplied complete-graph pairingGraph is pulled back along e with this support proof, giving an actual perfect matching; matchingPairing is its inverse. This reuses the original mate and inverse chain and introduces no second pairing or Pfaffian core.")),
                    Paragraph(Text("An unsupported pairing has a zero matrix factor, so its contribution is zero without a nonzero-weight premise. For an actual matching, the canonical pair slots biject with its actual undirected edge subtype. Injectivity follows from distinct permutation slots, and surjectivity follows from uniqueness of the matching partner. Thus its matrix product equals the cast of matchingTau times matchingWeight, with each actual undirected edge counted once. Summing and using the common coefficient proves the displayed formula over an arbitrary CommRing. No division is used.")),
                    Paragraph(Text("The coefficient uniformity is supplied by actual alternating-cycle transport and induction on disagreement edges. Consequently the graph, cycle, complement matching, listing and weight factors all belong to the same actual realization. The signed identity permits negative and zero weights, shared matching edges, disconnected graphs and coefficient rings of characteristic two.")),
                    Paragraph(Text("For nonnegative real weights, each edge-once matching product is nonnegative, so Z = partitionFunction(w) is nonnegative. Apply the displayed identity at R = Real. The integer value of orientationUnit is one or minus one, hence its real absolute value is one. Multiplicativity of absolute value and abs(Z) = Z give abs(Pf(A(e,epsilon,w))) = Z. This consequence uses precisely the additional hypothesis that every actual edge weight is nonnegative; the signed identity requires no such hypothesis.")),
                    Paragraph(Text("When V is empty, the standard sum has one empty pairing and the actual graph has one empty matching, so both values are one. With no perfect matching, every pairing contribution vanishes and the partition sum is empty, so both values are zero. These cases are included in the formula. This conditional algebraic theorem does not construct planar orientations or geometric embeddings, prove the determinant-square identity, introduce square roots, or establish algorithmic complexity or hardness results."))),
                DescribeRole.Theorem)
        )));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Either(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Adj(Formula graph, Formula x, Formula y) => Call("Adj", graph, x, y);
    private static Formula Perfect(Formula matching) => Call("IsPerfectMatching", matching);
    private static Formula Statement()
    {
        Formula vtype = F.Id("V"), g = F.Id("G"), m = F.Id("M"), v = F.Id("v"), p = F.Id("p"),
            n = F.Id("N"), x = F.Id("x"), y = F.Id("y");
        Formula c = Call("toSubgraph", p);
        Formula toggle = Iffn(Adj(n, x, y), Either(Both(Adj(m, x, y), new Formula.Not(Adj(c, x, y))),
            Both(Adj(c, x, y), new Formula.Not(Adj(m, x, y)))));
        Formula flipped = Ex("N", Call("Subgraph", g), Both(Perfect(n), All("x", vtype, All("y", vtype, toggle))));
        Formula complement = Ex("N", Call("Subgraph", Call("Induce", g, Call("Complement", Call("Verts", c)))), Perfect(n));
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", vtype),
            All("M", Call("Subgraph", g), All("v", vtype, All("p", Call("Walk", g, v, v),
                Imp(Perfect(m), Imp(Call("IsCycle", p), Imp(Call("IsAlternating", Call("spanningCoe", c), Call("spanningCoe", m)),
                    Both(Call("Even", Call("length", p)), Both(flipped, complement)))))))))));
    }

    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Tau(Formula e, Formula eps, Formula m) => Call("matchingTau", e, eps, m);
    private static Formula Transport()
    {
        Formula vtype = F.Id("V"), g = F.Id("G"), n = F.Id("n"), e = F.Id("e"),
            eps = F.Id("epsilon"), m = F.Id("M"), k = F.Id("N"), v = F.Id("v"),
            p = F.Id("p"), x = F.Id("x"), y = F.Id("y");
        Formula c = Call("toSubgraph", p);
        Formula toggle = All("x", vtype, All("y", vtype,
            Iffn(Adj(k, x, y), Either(Both(Adj(m, x, y), new Formula.Not(Adj(c, x, y))),
                Both(Adj(c, x, y), new Formula.Not(Adj(m, x, y)))))));
        Formula product = Call("Product", Call("Map", Call("dartSign", eps), Call("darts", p)));
        Formula result = Ex("N", Call("PM", g), Both(toggle,
            Eqn(Mul(Tau(e, eps, m), Tau(e, eps, k)), new Formula.Negate(product))));
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", vtype),
            All("n", Seq(Mathbb, Grp(F.Id("N"))),
            All("e", Call("Equiv", vtype, Call("Fin", Mul(D(2), n))),
            All("epsilon", Call("Function", Call("Dart", g), Call("ZMod", D(2))),
            All("M", Call("PM", g), All("v", vtype, All("p", Call("Walk", g, v, v),
                Imp(Call("Reverses", eps), Imp(Call("IsCycle", p),
                Imp(Call("IsAlternating", Call("spanningCoe", c), Call("spanningCoe", m)), result))))))))))));
    }
    private static Formula Uniform()
    {
        Formula vtype = F.Id("V"), g = F.Id("G"), n = F.Id("n"), e = F.Id("e"),
            eps = F.Id("epsilon"), m = F.Id("M"), k = F.Id("N");
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", vtype),
            All("n", Seq(Mathbb, Grp(F.Id("N"))),
            All("e", Call("Equiv", vtype, Call("Fin", Mul(D(2), n))),
            All("epsilon", Call("Function", Call("Dart", g), Call("ZMod", D(2))),
            All("M", Call("PM", g), All("N", Call("PM", g),
                Imp(Call("Reverses", eps), Imp(Call("NiceOdd", eps),
                    Eqn(Tau(e, eps, m), Tau(e, eps, k))))))))))));
    }

    private static Formula Identity()
    {
        Formula v = F.Id("V"), g = F.Id("G"), n = F.Id("n"), r = F.Id("R"),
            e = F.Id("e"), eps = F.Id("epsilon"), w = F.Id("w");
        Formula result = new Formula.Relation(
            Call("pfaffian", Call("orientedMatrix", e, eps, w)), FormulaRelationOperator.Equal,
            Mul(Call("IntCast", Call("IntegerValue", Call("orientationUnit", e, eps))),
                Call("partitionFunction", w)));
        return Disp(All("V", Call("Type"), Seq(OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), All("n", Seq(Mathbb, Grp(F.Id("N"))),
            All("R", Call("Type"), Seq(OpenBracket, Call("CommRing", r), CloseBracket, Sp,
            All("e", Call("Equiv", v, Call("Fin", Mul(D(2), n))),
            All("epsilon", Call("Function", Call("Dart", g), Call("ZMod", D(2))),
            All("w", Call("Function", Call("edgeSet", g), r),
                Imp(Call("Reverses", eps), Imp(Call("NiceOdd", eps), result))))))))))));
    }

    private static Formula MatchCall(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula MatchAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula MatchEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula MatchNat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula MatchFin(Formula n) => MatchCall("Fin", n);
    private static Formula MatchTimes(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula MatchDefinition()
    {
        Formula n = F.Id("n"), m = F.Id("M"), labels = MatchFin(MatchTimes(D(2), n));
        Formula domain = Seq(OpenBrace, m, Colon, MatchCall("Subgraph", MatchCall("CompleteGraph", labels)), Sp, Mid, Sp,
            MatchCall("IsPerfectMatching", m), CloseBrace);
        return Disp(MatchAll("n", MatchNat, MatchEq(MatchCall("TypeOf", MatchCall("matchingEquiv", n)), MatchCall("Equiv", domain, MatchCall("P", n)))));
    }
}
