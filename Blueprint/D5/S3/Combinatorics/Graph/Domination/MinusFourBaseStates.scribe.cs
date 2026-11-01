using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class MinusFourBaseStatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/MinusFourBaseStates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The component calculation uses subsets of at most nine vertices and a separate four-core/eight-root expression.",
        H("Eight component messages and the four-cycle cancellation"),
        Blocks(
            Node("branch-size", "Sizes of the actual components", "branchSize", DescribeRole.Definition,
                "After deleting core vertices 0,1,2,3, the consecutive component sizes are 2,2,2,2,6,3,3,9. Their starting labels are 4,6,8,10,12,18,21,24."),
            Node("branch-start", "Starting labels", "branchStart", DescribeRole.Definition,
                "Each component interval begins at the specified published root label. Together the intervals contain exactly labels 4 through 32."),
            Node("branch-label", "Local labels mapped to the source", "branchLabel", DescribeRole.Definition,
                "A local vertex v in component i is sent to branchStart(i)+v in Fin 33. A finite bound proves this label is in range."),
            Node("branch-graph", "Actual internal component edges", "branchGraph", DescribeRole.Definition,
                "The graph of a component is the comap of the actual source graph along branchLabel. Its edges come from the published edge list, including the nine-vertex component at root 24."),
            Node("root", "The component root", "root", DescribeRole.Definition,
                "The first local label, zero, is the component root in each of the eight intervals."),
            Node("local-domination", "Ordinary domination internal to a component", "localDominating", DescribeRole.Definition,
                "Every local vertex belongs to S or has a branchGraph neighbor in S. All vertices, including the root, are required to be internally dominated."),
            Node("message", "Root-conditioned weighted sums", "message", DescribeRole.Definition,
                "For each component and Boolean b, sum the cardinality weight at minus four over its internally dominating subsets whose root membership is b. Each sum ranges over at most 512 subsets. The root-selected values are 12,12,12,12,972,minus 36,minus 36,minus 20736. The root-omitted values are minus 4,minus 4,minus 4,minus 4,minus 1024,16,16,5888. These finite sums are computed by Lean kernel decision, using no native certificate."),
            Node("root-neighbors", "The exact core-to-root incidences", "rootNeighbors", DescribeRole.Definition,
                "The root neighbor sets in the core are {0},{2},{2},{2},{0,1},{1,2},{2,3},{3}, in component order."),
            Node("core-covered", "Ordinary domination of the core", "coreCovered", DescribeRole.Definition,
                "A chosen core set Z and chosen root-index set A cover a core vertex when it belongs to Z, has a selected core neighbor along an actual source edge, or is adjacent to a selected component root."),
            Node("state-evaluation", "The finite core expression", "stateEvaluation", DescribeRole.Definition,
                "For all 16 core subsets Z and all 256 root selections A, retain the term exactly when coreCovered holds. Multiply the core cardinality weight by the eight matching component messages. The product-sum expression has 4096 core/root cases; it does not enumerate all subsets of the 33-vertex graph."),
            Node("reassembly-reduction", "Reduction through the exact weighted bridge", "result_of_reassembly", DescribeRole.Theorem,
                "Assume that evaluation(sourceGraph,minus four) equals stateEvaluation. Substitution of the kernel-verified local messages into this state expression gives zero by kernel finite decision. The source family reduction then gives connected graphs on Fin n of unbounded order with vanishing ordinary domination sum. The premise is the exact global restriction/reassembly bridge, including domination and cardinality weights. The conditional theorem does not supply that bridge."),
            Paragraph(Text("Each component root has an internal leaf. Domination of that leaf forces either the root or its leaf to be selected, so external core help cannot enlarge the internally dominating family. MinusFourReassembly supplies the exact restriction/union correspondence: each source dominating set occurs once, and its cardinality is the sum of the core and component cardinalities. The conditional reduction separates this combinatorial bridge from the small finite arithmetic computations."))), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            Statement(declaration), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static StatementSource Statement(string declaration) => declaration == "result_of_reassembly"
        ? StatementSource.FromAuthor(Disp(ImpliesF(Eq(BaseValue, Id("stateEvaluation")), FamilyEvent())))
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
