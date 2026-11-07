using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ComponentPacking;

internal sealed class HausmannQuestion54RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/hausmann2026weightedmaxcut");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized Petersen graph GP(7,2) refutes the full independent-side component-order-three assertion in Hausmann Question 5.4.",
        H("A counterexample to Hausmann Question 5.4"),
        Blocks(
            Node("OddGirthFive", "Odd girth exactly five", OddFormula(),
                "For a simple graph G on V, there is a vertex v and a closed walk w at v that is a simple cycle of length five. Every simple cycle of odd length has length at least five. The universal condition permits even cycles; neither connectivity nor any other restriction is implicit.",
                DescribeRole.Definition),
            Node("SmallComponents", "Order of each induced component", SmallFormula(),
                "For every connected component C of the actual induced graph G[R], Nat.card C.supp counts its vertices and is at most three. Since V is finite, these supports are finite. Singleton components are included. This is a component-order bound, not a degree bound, a path-length bound, or a bound on the total size of R.",
                DescribeRole.Definition),
            Node("claim", "The entire universal source assertion", ClaimFormula(),
                "For every finite vertex type V and simple undirected graph G, degree at most three and odd girth exactly five imply the existence of subsets L and R. They are disjoint, their union is all of V, L is independent, and every component of G[R] has at most three vertices. Fintype and decidable instances express finite presentations and can be supplied classically for every finite graph. There is no size cutoff or connectedness, planarity, regularity, maximum-average-degree, weighting, or construction hypothesis. The claim is the affirmative assertion asked in Question 5.4, not Questions 5.3 or 5.5.",
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hausmann54-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Use vertices 0 through 13 with edges {0,1}, {0,6}, {0,7}, {1,2}, {1,8}, {2,3}, {2,9}, {3,4}, {3,10}, {4,5}, {4,11}, {5,6}, {5,12}, {6,13}, {7,9}, {7,12}, {8,10}, {8,13}, {9,11}, {10,12}, {11,13}. These are the edges u_i u_(i+1), u_i v_i and v_i v_(i+2), with indices modulo seven and u_i=i, v_i=7+i. The explicit edge list fixes the labels.")),
                    Paragraph(Text("The graph is simple, every degree is at most three, and no three vertices form a triangle. The closed walk 0,1,2,9,7,0 is a simple five-cycle. Mathlib's lower bound of three for a simple-cycle length and its equivalence between a three-cycle and a three-clique exclude every shorter odd cycle. These facts establish all the source input conditions on this one graph.")),
                    Paragraph(Text("For an arbitrary independent subset L, split on membership of the least undecided vertex. In the inclusion branch its neighbours cannot belong to L. In the exclusion branch that vertex lies outside L. Once four certified outside vertices span a connected tree, the branch terminates. The complete proof tree has 93 nodes and 47 leaves; no maximality or cardinality restriction on L is imposed. At every leaf the four labels are distinct, and the second, third and fourth each have an earlier neighbour. All concrete adjacency and distinctness facts are checked by kernel reduction.")),
                    Paragraph(Text("Exhaustiveness of L union R places these four outside vertices in R. The adjacency-to-component lemma puts all four in one connected component of the induced graph. Their distinctness gives an injection from Fin 4 into its support, hence that component has at least four vertices. This contradicts SmallComponents. Thus every possible partition is excluded, and one legal finite graph refutes the universal assertion over all finite graphs.")),
                    Paragraph(Text("This refutes the proposed component-order-three structural route. It makes no claim about the weighted 4/5 conjecture, Questions 5.3 or 5.5, minimality of the witness, or literature priority. The known residual-order-six theorem and sparsity-conditioned order-three results do not imply the assertion refuted here."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hausmann-2026-question-5-4-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula Id(string x) => F.Id(x);
    private static Formula Call(string x, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. args]);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Exists(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    private static Formula OddFormula()
    {
        var g = Id("G"); var v = Id("v"); var w = Id("w");
        var cycle = Call("IsCycle", w); var len = Call("length", w);
        return Disp(All("V", Id("Type"), All("G", Call("SimpleGraph", Id("V")),
            Iff(Call("OddGirthFive", g), And(
                Exists("v", Id("V"), Exists("w", Call("Walk", g, v, v), And(cycle, Eq(len, D(5))))),
                All("v", Id("V"), All("w", Call("Walk", g, v, v),
                    Imp(cycle, Imp(Call("Odd", len), Le(D(5), len))))))))));
    }

    private static Formula SmallFormula()
    {
        var g = Id("G"); var r = Id("R");
        return Disp(All("V", Id("Type"), All("G", Call("SimpleGraph", Id("V")),
            All("R", Call("Set", Id("V")), Iff(Call("SmallComponents", g, r),
                All("C", Call("ConnectedComponent", Call("induce", g, r)),
                    Le(Call("NatCard", Call("supp", Id("C"))), D(3))))))));
    }

    private static Formula ClaimFormula()
    {
        var v = Id("V"); var g = Id("G"); var l = Id("L"); var r = Id("R");
        var conclusion = Exists("L", Call("Set", v), Exists("R", Call("Set", v),
            And(Call("Disjoint", l, r), And(Eq(Call("union", l, r), Call("univ", v)),
                And(Call("IsIndepSet", g, l), Call("SmallComponents", g, r))))));
        return Disp(Iff(Id("claim"), All("V", Id("Type"),
            Seq(OpenBracket, Call("Fintype", v), CloseBracket,
                OpenBracket, Call("DecidableEq", v), CloseBracket,
                All("G", Call("SimpleGraph", v),
                    Seq(OpenBracket, Call("DecidableRel", Call("Adj", g)), CloseBracket,
                        Imp(All("v", v, Le(Call("degree", g, Id("v")), D(3))),
                            Imp(Call("OddGirthFive", g), conclusion))))))));
    }

    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("hausmann54-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
