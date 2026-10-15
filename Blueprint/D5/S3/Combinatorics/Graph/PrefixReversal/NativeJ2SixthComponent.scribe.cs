using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2SixthComponentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SixthComponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two remaining independently specified J2 ports are joined by a sixth actual complete path component.",
        H("The Sixth Actual J2 Path Component"),
        Blocks(Describe.Lean(DescribeId.Create("native-j2-sixth-full-component"),
            DeclarationHandle.Create(Prefix + "native_j2_sixth_full_component"),
            H("The Actual Component from L1 to Bar L0"),
            StatementSource.FromAuthor(ComponentFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every m at least five, the theorem constructs an actual simple path in "
                + "survivingGraph(m) from port(m,(1,false,true)) to port(m,(0,true,true)). "
                + "Its support consists exactly of all vertices reachable from the first port, "
                + "and it contains every actual surviving edge incident to that component.")),
                Paragraph(Text(
                "Apply the endpoint-aware six-cut slicing theorem to the same actual F2 Hamilton "
                + "cycle containing the six independently specified marked edges. Map and transfer "
                + "the resulting subtype walks into the actual surviving graph. Their supports "
                + "partition the full F2 domain and their edges are exactly the surviving inventory. "
                + "Disjointness and edge saturation therefore make each piece a whole component. "
                + "Every port is a graph leaf, so it can occur only at a path endpoint. The five "
                + "constructed literal word components exclude ten of the twelve ports from the "
                + "component of L1. The actual surviving a edge at L1 rules out a nil piece. "
                + "Its other endpoint must consequently be bar L0, and reversing the actual "
                + "slice when necessary earns the stated orientation."))), DescribeRole.Theorem),
            Paragraph(Text("Higher actual recursive expansion and Hamilton cycles for all sizes "
                + "remain separate obligations.")))));

    private static Formula ComponentFormula()
    {
        Formula m = F.Id("m"), w = F.Id("w"), x = F.Id("x"), y = F.Id("y");
        Formula graph = Call("survivingGraph", m);
        Formula start = Call("port", m, Call("Tuple3", D(1), Call("False"), Call("True")));
        Formula finish = Call("port", m, Call("Tuple3", D(0), Call("True"), Call("True")));
        Formula Reach(Formula v) => Call("Reachable", graph, start, v);
        Formula vertices = All("x", Call("Configuration", m),
            Iff(Call("Member", x, Call("Support", w)), Reach(x)));
        Formula edges = All("x", Call("Configuration", m), All("y", Call("Configuration", m),
            Iff(And(Call("Adj", graph, x, y), Reach(x)),
                Call("Member", Call("Sym2Pair", x, y), Call("Edges", w)))));
        Formula body = Some("w", Call("Walk", graph, start, finish),
            And(Call("IsPath", w), And(vertices, edges)));
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m), body)));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
