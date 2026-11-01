using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class MinusFourReassemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact restriction and union correspondence connects the actual source graph to the eight-component weighted calculation.",
        H("Restriction, root states, and the connected family"),
        Blocks(
            Node("source-reassembly", "The exact weighted reassembly identity", "source_reassembly",
                "The source vertex coordinates are the disjoint sum of Fin 4 and the eight dependent component types. The map sends a core coordinate to its own label and a component coordinate to branchStart(i)+v. Its bijectivity is checked on the actual 33 labels. Assembly takes the disjoint union of the core set and the eight local sets, then maps through this equivalence. Restriction and assembly are inverse, and the cardinality is the core cardinality plus the sum of the component cardinalities. No vertex or subset is lost or duplicated. Every component root has its actual local leaf at coordinate one. Global domination of this leaf forces its root or leaf to be selected and hence forces internal domination of the root. Every other component vertex has only internal neighbors. The exact core-neighbor characterization is the four-cycle adjacency together with the published root incidences. Thus an assembled set dominates exactly when all eight local sets internally dominate and the selected core and roots cover the core. Partitioning each local family by its root membership gives the typed configuration family. The map from these configurations to domSets(sourceGraph) is injective by restriction and surjective by the domination characterization. The equivalence transports the sum of cardinality weights. Fintype.prod_sum separates the independent component choices and their sums are exactly the eight messages. The resulting expression is stateEvaluation."),
            Node("family-result", "The complete unbounded-order ordinary-domination event", "result",
                "For every natural N there exist n greater than N and a connected finite simple undirected graph G on Fin n whose sum of minus four raised to the cardinality of S over all ordinary dominating subsets S is zero. The exact reassembly identity supplies the premise of the finite-state reduction. Its local messages and core cancellation give the base value zero. The existing support-replication construction uses N+1 copies of the actual 33-vertex base, attaches their actual support 4 to one hub, and adds the hub pendant. Its order is 33(N+1)+2. Since leaf 5 remains internal in each copy, partial domination outside support 4 equals full domination. The weighted replication value is eight times the positive power N+1 of the base value. Copy paths through support 4 prove connectedness, and graph isomorphism transport gives the exact Fin n statement while preserving domination, cardinality and weights."),
            Paragraph(Text("The source question is Section 4 item 3 of Alikhani and Griswold, arXiv:2608.00109v1. The source graph and its reported finite root are prior results, and the source graph is encoded independently from its explicit edge list. This argument addresses the connected unbounded-family event. It does not require a dominating subset to be connected, or impose a fixed degree or cyclomatic number. It asserts no result about the smallest possible order or about other integer roots. The library search supplies existing domination, leaf, transport, replication and finite-sum interfaces; the reassembly and family application are repository derivations without a worldwide priority claim."))), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            Statement(declaration), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static StatementSource Statement(string declaration) => StatementSource.FromAuthor(Disp(
        declaration == "result" ? FamilyEvent() : Eq(BaseValue, FormulaDsl.Id("stateEvaluation"))));

    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(FormulaDsl.Id(name))), [.. args]);
    private static Formula Nat => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(FormulaDsl.Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Seq(FormulaDsl.Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.And, P(right));
    private static Formula MinusFour => P(Seq(Minus, D(4)));
    private static Formula BaseValue => Call("evaluation", FormulaDsl.Id("sourceGraph"), MinusFour);
    private static Formula FamilyEvent()
    {
        var n = FormulaDsl.Id("n"); var graph = FormulaDsl.Id("G"); var set = FormulaDsl.Id("S");
        var weight = new Formula.Power(MinusFour, Call("card", set));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(set, InMacro, Call("domSets", graph))), Sp, weight);
        return All("N", Nat, Some("n", Nat,
            And(new Formula.Relation(FormulaDsl.Id("N"), FormulaRelationOperator.LessThan, n),
                Some("G", Call("SimpleGraph", Call("Fin", n)),
                    And(Call("Connected", graph), Eq(sum, D(0)))))));
    }
}
