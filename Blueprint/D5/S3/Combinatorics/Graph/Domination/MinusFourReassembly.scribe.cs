using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class MinusFourReassemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/alikhanigriswold2026integerdominationroots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rooted-component decomposition gives a general weighted domination identity. Its checked application to the published graph, followed by support replication, gives connected graphs of unbounded order with root minus four.",
        H("Rooted decomposition and the connected minus-four family"),
        Blocks(
            Definition("evaluation", "Ordinary domination evaluation", "evaluation",
                "For a finite vertex type V with Fintype and DecidableEq instances, evaluation(H,x) sums x to the cardinality of S over all ordinary dominating subsets S of H, each counted once. The subsets need not be connected."),
            Definition("decomposition", "Arbitrary finite rooted decomposition", "Decomposition",
                "The record contains natural numbers n, k and m, a size for every branch in Fin m, a graph on Fin n with decidable adjacency, and a vertex equivalence from Fin k disjoint union the dependent branch types. Each branch has a root, an internal leaf and a finite set of incident core vertices. The leaf has exactly the root as its global neighbor, the root is adjacent to that leaf, every nonroot branch vertex has only internal neighbors, and every core vertex has exactly its internal core neighbors and the incident branch roots as neighbors. All dimensions are arbitrary; no size bound, weight or source edge list occurs in this interface. The local graph laws are explicit input obligations."),
            Definition("branch-graph", "The induced branch graph", "branchGraph",
                "For decomposition d and branch i, branchGraph(d,i) pulls d.graph back along the branch part of d.labels."),
            Definition("local-domination", "Internal branch domination", "localDominating",
                "For every branch vertex v, either v is in S or there exists w in S adjacent to v in branchGraph(d,i). This is internal ordinary domination, including domination of the branch root."),
            Definition("messages", "Root-conditioned weighted messages", "message",
                "For arbitrary decomposition d, integer x, branch i and Boolean b, message(d,x,i,b) sums x to the cardinality of S over all subsets S of branch i that internally dominate and whose root membership decides to b. The definition contains no precomputed message values."),
            Definition("core-coverage", "Coverage by core and selected roots", "coreCovered",
                "For core subset Z and root-index subset A, every core vertex is selected in Z, adjacent to a core vertex selected in Z, or incident to a root indexed by A."),
            Definition("table-evaluation", "Core evaluation of arbitrary message data", "tableEvaluation",
                "For arbitrary table mapping each branch and Boolean root state to an integer, tableEvaluation(d,x,table) sums over all core subsets Z and root-index subsets A. A covered pair contributes x to card(Z) times the product over i of table(i,decide(i in A)); an uncovered pair contributes zero."),
            Definition("state-evaluation", "The exact branch-message expression", "stateEvaluation",
                "This is the same core expression with table(i,b) equal to message(d,x,i,b). Every core subset and root-state subset occurs once."),
            Node("reassembly", "General weighted restriction and reassembly", "reassembly", Reassembly(),
                "Restrict a subset along the vertex equivalence to a core subset and one local subset per branch. Disjoint assembly and restriction are inverse, and assembly cardinality is the core cardinality plus the sum of local cardinalities. Domination of each branch leaf forces internal domination of its root, while the nonroot-neighbor law handles all other branch vertices. The core-neighbor law gives exactly coreCovered. This yields a bijection between ordinary dominating sets and covered core/root states with internally dominating branch choices. Transport the cardinality weights along this bijection. The pinned Fintype.prod_sum identity factors the independent branch choices, giving exactly stateEvaluation for every d and integer x."),
            Node("message-soundness", "Soundness of the message checker", "zero_of_messages", Soundness(),
                "The inputs are an arbitrary d, integer x and table. The first premise requires every entry to equal the exact message for that same d, weight and root state; the second requires the covered core expression for the same table to vanish. Substitute the first premise into the general reassembly identity and then use the second. Both premises are checked in the live application below. This theorem does not assume the graph's evaluation is zero."),
            Node("family-result", "The complete connected unbounded-order event", "result", FamilyEvent(),
                "The application supplies the published 33-vertex graph with its actual 36 edges. Its core is the four-cycle on labels zero through three; branch sizes are 2,2,2,2,6,3,3,9. The vertex equivalence and all local graph laws are checked as input fields of this particular decomposition. At weight minus four, the selected-root message vector is 12,12,12,12,972,-36,-36,-20736 and the omitted-root vector is -4,-4,-4,-4,-1024,16,16,5888. The exact message equalities and covered core cancellation are kernel decisions passed directly to zero_of_messages. They are not retained as separate positive finite theorems. The original ConsecutiveCycleSumsGraph.connected_of_predecessor supplier proves base connectedness from the decreasing parent map on the full vertex set; the pinned induced-universe isomorphism transports its conclusion to the base graph. Vertex five has sole neighbor four. Use N+1 copies of the base, connect their supports four to a hub, and add one hub pendant. The existing replication equivalences and leaf domination identity give evaluation x(x+2) times the base evaluation to the power N+1. At minus four this is zero, and copied paths through the support prove connectedness. The order is 33(N+1)+2, which exceeds N. A finite vertex equivalence gives the exact graph on Fin n.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alikhani-griswold-2026-connected-minus-four-family"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The source question is Section 4 item 3 of Alikhani and Griswold, arXiv:2608.00109v1. The base graph and its reported finite root are prior art. The graph data and proofs here are independently written with attribution. The general weighted composition and its family application are repository derivations, without a worldwide priority claim. The conclusion uses ordinary domination and requires only graph connectedness; it imposes no degree, cyclomatic number or connected-subset condition. No smallest-order or other-root claim is made."))), []));

    private static DocumentBlock Definition(string id, string title, string name, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, resolution);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(FormulaDsl.Id(name))), [.. args]);
    private static Formula Nat => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula Integer => Seq(Mathbb, Grp(FormulaDsl.Id("Z")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(FormulaDsl.Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Seq(FormulaDsl.Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula ImpliesF(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Reassembly()
    {
        var d = FormulaDsl.Id("d"); var x = FormulaDsl.Id("x");
        return All("d", FormulaDsl.Id("Decomposition"), All("x", Integer,
            Eq(Call("evaluation", Call("graph", d), x), Call("stateEvaluation", d, x))));
    }
    private static Formula Soundness()
    {
        var d = FormulaDsl.Id("d"); var x = FormulaDsl.Id("x"); var table = FormulaDsl.Id("table");
        var i = FormulaDsl.Id("i"); var b = FormulaDsl.Id("b");
        var entries = All("i", Call("Fin", Call("m", d)), All("b", FormulaDsl.Id("Bool"),
            Eq(Call("message", d, x, i, b), Call("table", i, b))));
        var tableType = Seq(Call("Fin", Call("m", d)), Sp, To, Sp, FormulaDsl.Id("Bool"), Sp, To, Sp, Integer);
        return All("d", FormulaDsl.Id("Decomposition"), All("x", Integer, All("table", tableType,
            ImpliesF(entries, ImpliesF(Eq(Call("tableEvaluation", d, x, table), D(0)),
                Eq(Call("evaluation", Call("graph", d), x), D(0)))))));
    }
    private static Formula FamilyEvent()
    {
        var n = FormulaDsl.Id("n"); var graph = FormulaDsl.Id("G"); var set = FormulaDsl.Id("S");
        var weight = new Formula.Power(P(Seq(Minus, D(4))), Call("card", set));
        var sum = Seq(new Formula.Subscript(Sum, Seq(set, InMacro, Call("domSets", graph))), Sp, weight);
        return All("N", Nat, Some("n", Nat,
            And(new Formula.Relation(FormulaDsl.Id("N"), FormulaRelationOperator.LessThan, n),
                Some("G", Call("SimpleGraph", Call("Fin", n)), And(Call("Connected", graph), Eq(sum, D(0)))))));
    }
}
