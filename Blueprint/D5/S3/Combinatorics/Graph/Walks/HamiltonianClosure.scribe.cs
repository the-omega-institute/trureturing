using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class HamiltonianClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint degree sums close spanning paths, preserve Hamiltonicity under one closure edge, and imply Ore's theorem.",
        H("Hamiltonian closure and Ore's theorem"),
        Blocks(
            Paragraph(Text("Let V be an arbitrary finite vertex type in any universe and G a simple undirected graph on V. Write n for its cardinality and deg(G,v) for the cardinality of the neighbor set of v. The Lean statements use Fintype, decidable equality, and decidable adjacency to present these finite objects; classical instances supply those presentations without additional mathematical restrictions. IsHamiltonian and IsHamiltonianCycle are the native graph and walk predicates.")),
            Describe.Lean(DescribeId.Create("path-rerouting"),
                DeclarationHandle.Create(Prefix + "exists_hamiltonian_cycle_of_path"),
                H("A spanning path closes after rerouting"),
                StatementSource.FromAuthor(PathFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every a,b in V and every actual G-walk p from a to b, assume p is Hamiltonian, n is at least three, and deg(G,a)+deg(G,b) is at least n. There exists an actual Hamiltonian cycle based at a. No edge between a and b is assumed.")),
                    Paragraph(Text("Enumerate the spanning path as x(0),...,x(n-1). Among the n-1 positions between consecutive vertices, the positions i with a adjacent to x(i+1) number deg(G,a), and those with b adjacent to x(i) number deg(G,b). Their sum exceeds n-1, so the two sets meet. At such an i, keep the prefix through x(i), connect to b, follow the reversed suffix to x(i+1), and return to a. The prefix support and the reversed suffix support partition every vertex exactly once. The native path-ring splicing theorem constructs the actual cycle from these pieces and the two real connecting edges."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-edge-closure"),
                DeclarationHandle.Create(Prefix + "isHamiltonian_sup_edge_iff"),
                H("Bondy--Chvatal single-edge closure"),
                StatementSource.FromAuthor(ClosureFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every u,v in V, if u differs from v, u and v are nonadjacent in G, and n is at most deg(G,u)+deg(G,v), then G sup edge(u,v) is Hamiltonian if and only if G is Hamiltonian. Both degrees belong to G before adding the edge. There is no connectedness or external lower-cardinality hypothesis. Empty, singleton, and two-vertex types remain included under the stated premises.")),
                    Paragraph(Text("Distinct nonadjacent endpoints each have degree at most n-2, and the degree-sum bound therefore implies n is at least three. If a Hamilton cycle of the augmented graph uses the added edge, open that actual edge with the native cycle-slicing theorem. The resulting spanning path uses only original edges, transfers back to G, and closes by endpoint rerouting. If the cycle does not use the added edge, transfer it directly. The opposite implication is graph monotonicity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ore-degree-sum"),
                DeclarationHandle.Create(Prefix + "ore"),
                H("Ore's degree-sum criterion"),
                StatementSource.FromAuthor(OreFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If n is at least three and every distinct nonadjacent pair u,v in V satisfies n at most deg(G,u)+deg(G,v), then G is Hamiltonian. The quantifier covers all such pairs in an arbitrary finite graph. No minimum-degree or connectedness strengthening is imposed.")),
                    Paragraph(Text("Induct on the finite number of ordered distinct nonadjacent pairs. If there are none, G is complete and the native complete-graph theorem applies. Otherwise add one absent edge. The number of missing ordered pairs strictly decreases, and degree monotonicity preserves the Ore condition. Apply the induction hypothesis to the augmented graph and the single-edge closure equivalence to return to G."))),
                DescribeRole.Theorem),
            Paragraph(Text("These are known theorems of Bondy and Chvatal and of Ore. The proof adapts Juan Pablo Traverso Gianini's MengerHamilton/ClosureAux.lean and Hamiltonian.lean at immutable jtraverso/menger-hamiltonian commit 35c5f684f9bfbd244bd0999ce725623ab571adb6. It retains the endpoint index-counting and missing-edge induction arguments while using the receiver's native Walk interfaces, cycle opening and path-ring splicing. The donor's cyclic-arrangement framework, complete-graph construction, Menger, Dirac and Chvatal--Erdos developments are outside this result. The source note gives the original paper locators, software attribution, license and retirement condition. No originality or reading of the original full papers is claimed.")))));

    private static Formula PathFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), a = F.Id("a"), b = F.Id("b"), p = F.Id("p"), c = F.Id("c");
        Formula n = Call("card", v);
        Formula body = Imp(And(Call("IsHamiltonian", p), And(Le(D(3), n),
            Le(n, Add(Call("degree", g, a), Call("degree", g, b))))),
            Ex("c", Call("Walk", g, a, a), Call("IsHamiltonianCycle", c)));
        return Disp(FiniteGraphs(All("a", v, All("b", v, All("p", Call("Walk", g, a, b), body)))));
    }

    private static Formula ClosureFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), u = F.Id("u"), w = F.Id("v");
        Formula condition = And(Ne(u, w), And(Not(Call("Adj", g, u, w)),
            Le(Call("card", v), Add(Call("degree", g, u), Call("degree", g, w)))));
        Formula body = Iff(Call("IsHamiltonian", Call("sup", g, Call("edge", u, w))), Call("IsHamiltonian", g));
        return Disp(FiniteGraphs(All("u", v, All("v", v, Imp(condition, body)))));
    }

    private static Formula OreFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), u = F.Id("u"), w = F.Id("v");
        Formula pairs = All("u", v, All("v", v, Imp(And(Ne(u, w), Not(Call("Adj", g, u, w))),
            Le(Call("card", v), Add(Call("degree", g, u), Call("degree", g, w))))));
        return Disp(FiniteGraphs(Imp(And(Le(D(3), Call("card", v)), pairs), Call("IsHamiltonian", g))));
    }

    private static Formula FiniteGraphs(Formula body) => All("V", Call("Type"),
        Imp(Call("Finite", F.Id("V")), All("G", Call("SimpleGraph", F.Id("V")), body)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
