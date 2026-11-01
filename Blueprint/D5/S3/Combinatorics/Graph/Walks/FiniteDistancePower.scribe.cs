using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class FiniteDistancePowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual component supports and maximal independent Finsets retain their full spectra at every positive faithful power.", H("Finite-path powers of disconnected graphs"), Blocks(
            Paragraph(Text("Fix a finite vertex type V and a simple graph G. The existing graphPower(G,d) joins distinct vertices only when their extended distance is at most d, so unreachable vertices are never joined. The frozen power(G,d), which uses natural distance, is used only on connected graphs. For a finite block map b:V to iota, assume every edge has both endpoints in the same block. Restriction keeps the actual subtype vertices, and assembly takes the disjoint union of their images in V. Empty blocks are harmless; in particular the results apply to arbitrary finite disjoint unions of nonempty graphs.")),
            Node("power_adj_iff_walk", "The exact finite-walk semantics",
                All("d",C("Nat"),All("u",I("V"),All("v",I("V"),Iff(C("Adj",C("graphPower",I("G"),I("d")),I("u"),I("v")),And(C("Distinct",I("u"),I("v")),Ex("p",C("Walk",I("G"),I("u"),I("v")),Le(C("length",I("p")),I("d")))))))),
                "A finite extended-distance bound supplies a shortest native walk. Conversely, the length of any native joining walk bounds extended distance. The distinctness condition retains looplessness."),
            Node("power_reachable_iff", "Positive powers preserve reachability",
                All("d",C("Nat"),Imp(Le(D(1),I("d")),All("u",I("V"),All("v",I("V"),Iff(C("Reachable",C("graphPower",I("G"),I("d")),I("u"),I("v")),C("Reachable",I("G"),I("u"),I("v"))))))),
                "Replace each power edge by its bounded base walk to obtain one direction. Every base edge remains a power edge when d is positive, giving the converse. The induced quotient equivalence identifies the actual connected components."),
            Node("power_eq_connected", "Agreement with the existing connected supplier",
                All("d",C("Nat"),Imp(C("Connected",I("G")),Eq(C("graphPower",I("G"),I("d")),C("power",I("G"),I("d"))))),
                "Connectedness makes every extended distance finite. Converting it to natural distance therefore preserves exactly the adjacency bound, including exponent zero."),
            Node("spectrum_partition", "The full Minkowski sum on closed blocks",
                All("n",C("Nat"),Iff(C("mem",I("n"),C("spectrum",I("G"))),Ex("k",C("Function",I("iota"),C("Nat")),And(All("i",I("iota"),C("mem",C("apply",I("k"),I("i")),C("spectrum",C("induce",I("G"),C("fiber",I("b"),I("i")))))),Eq(C("sum",I("k")),I("n")))))),
                "An independent dominating Finset restricts to one in every closed block. Conversely, assemble any chosen family of blockwise maximal independent Finsets. Independence and domination are both checked on the actual vertices, and the disjoint cardinality sum gives both necessity and every attainable sum."),
            Node("all_powers_components", "The exact disconnected well-covered-powers criterion",
                Iff(All("d",C("Nat"),Imp(Le(D(1),I("d")),C("WellCovered",C("graphPower",I("G"),I("d"))))),All("C",C("Components",I("G")),C("WCP",C("componentGraph",I("C"))))),
                "At each exponent, well-coveredness of the union is equivalent to well-coveredness of every actual component. The forward direction varies one block set while holding the others fixed. Each component graph is connected, so its faithful power agrees with the existing connected power. No connected-only predicate is imposed on the disconnected union."),
            Node("spectrum_power_components", "Every positive power has the full component sum",
                All("d",C("Nat"),Imp(Le(D(1),I("d")),All("n",C("Nat"),Iff(C("mem",I("n"),C("spectrum",C("graphPower",I("G"),I("d")))),Ex("k",C("Function",C("Components",I("G")),C("Nat")),And(All("C",C("Components",I("G")),C("mem",C("apply",I("k"),I("C")),C("spectrum",C("power",C("componentGraph",I("C")),I("d"))))),Eq(C("sum",I("k")),I("n")))))))),
                "Every joining walk stays in its closed component support. Inducing the base graph therefore loses no finite paths, and inducing the faithful power gives exactly the component power. Apply the full restriction-and-assembly formula to obtain both spectrum inclusions.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
