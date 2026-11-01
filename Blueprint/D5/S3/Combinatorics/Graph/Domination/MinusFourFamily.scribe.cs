using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class MinusFourFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/alikhanigriswold2026integerdominationroots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source graph has the published 33 labels and 36 edges; its base evaluation is an explicit premise of the family reduction.",
        H("Exact source labels and the unbounded-order reduction"),
        Blocks(
            Node("source-edges", "The authenticated finite edge data", "sourceEdges", DescribeRole.Definition,
                "The 36 unordered source edges are independently encoded from Alikhani and Griswold, On the Integer Domination Root Conjecture, arXiv:2608.00109v1. The four-cycle has vertices 0,1,2,3. The eight attached components occupy labels 4 through 32. The explicit edge list determines the graph; the source branch description is not used as a certificate."),
            Node("source-graph", "The actual source graph", "sourceGraph", DescribeRole.Definition,
                "Adjacency holds when either orientation belongs to sourceEdges. The graph is loopless by kernel finite decision and undirected by symmetry of the disjunction. Vertex 5 has sole neighbor 4. Connectedness is proved using a parent for every nonzero label, with each parent strictly smaller and joined by an actual source edge. Strong induction on the label gives a path to vertex 0."),
            Node("family-reduction", "The exact original event conditional on the base root", "result_of_base_root", DescribeRole.Theorem,
                "Assume precisely that evaluation(sourceGraph,minus four) equals zero. For every natural N choose r=N+1 copies attached at the actual support 4, retaining its actual internal leaf 5. The weighted support theorem gives eight times zero to the positive power r, hence zero. Connectedness follows from the copy paths. The vertex count is 33r+2, strictly greater than N. Fintype.equivFin relabels the actual replicated vertex type onto Fin n. The graph isomorphism transports domination bijectively and the finset map preserves cardinality, hence every weight. This yields the full existential event on Fin n, with no requirement that dominating subsets be connected."),
            Paragraph(Text("The base premise is discharged by the exact restriction/reassembly identity and finite component calculations in MinusFourReassembly and MinusFourBaseStates. The published report alone is not used as a proof. The question in Section 4 item 3 asks for an infinite family. The strictly increasing orders supply pairwise nonisomorphic graphs. The published base itself earns no new-resolution credit. No minimum-order, other-integer-root, degree-bound or cyclomatic-number assertion follows."))), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            Statement(declaration), declaration == "sourceEdges"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static StatementSource Statement(string declaration) => declaration == "result_of_base_root"
        ? StatementSource.FromAuthor(Disp(ImpliesF(Eq(BaseValue, D(0)), FamilyEvent())))
        : StatementSource.WithoutFormula();

    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Integer => Seq(Mathbb, Grp(Id("Z")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.And, P(right));
    private static Formula ImpliesF(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Implies, P(right));
    private static Formula MinusFour => P(Seq(Minus, D(4)));
    private static Formula BaseValue => Call("evaluation", Id("sourceGraph"), MinusFour);
    private static Formula FamilyEvent()
    {
        var n = Id("n"); var graph = Id("G"); var set = Id("S");
        var weight = new Formula.Power(MinusFour, Call("card", set));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(set, InMacro, Call("domSets", graph))), Sp, weight);
        return All("N", Nat, Some("n", Nat,
            And(new Formula.Relation(Id("N"), FormulaRelationOperator.LessThan, n),
                Some("G", Call("SimpleGraph", Call("Fin", n)),
                    And(Call("Connected", graph), Eq(sum, D(0)))))));
    }
}
