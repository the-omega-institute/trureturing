using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class BinaryRungSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every admissible cardinality is realized by an actual maximal independent vertex set, including both closing twists.", H("Exact maximal-independent spectra for binary cyclic matchings"), Blocks(
            Paragraph(Text("A vertex is (i,b), where i lies in Fin(m+2) and b lies in ZMod 2. The graph contains the rung edge and the two orientations of forward matching transport. The function closing(m,q) is zero except at the closing edge, where it adds q. Spectrum means cardinalities of actual finite independent sets that dominate every omitted vertex. The parameter m is arbitrary natural, so m+2 includes the two-rung boundary. For a prism we instead write r+3, covering every cycle length at least three.")),
            Node("closing_spectrum", "Complete twisted spectrum",
                All("m",C("Nat"),All("q",C("ZMod",D(2)),All("k",C("Nat"),Iff(C("mem",I("k"),C("spectrum",C("graph",C("closing",I("m"),I("q"))))),And(Le(C("add",I("m"),D(2)),C("mul",D(2),I("k"))),And(Le(I("k"),C("add",I("m"),D(2))),Eq(C("castZMod2",I("k")),I("q")))))))),
                "Independence permits at most one selected vertex in each rung. Maximality forbids two consecutive empty rungs, giving m+2 at most twice the cardinality. Transporting the selected labels around the cycle gives the parity constraint. Conversely, place the requested number of occupied rungs with gaps of size at most one and solve the binary phase recursion. The resulting vertex Finset is independent and dominates every omitted vertex; its closing phase is exactly its cardinality modulo two."),
            Node("prism_spectrum", "All native prisms",
                All("r",C("Nat"),All("k",C("Nat"),Iff(C("mem",I("k"),C("spectrum",C("prism",I("r")))),And(Le(C("add",I("r"),D(3)),C("mul",D(2),I("k"))),And(Le(I("k"),C("add",I("r"),D(3))),C("Even",I("k"))))))),
                "The zero closing twist is proved equal to the native Cartesian graph cycleGraph(r+3) box-product K2 on the same vertices. The two spectrum directions therefore give exactly the even cardinalities between the ceiling of half the rung count and the rung count."),
            Node("prism_wellCovered_iff", "First-power prism classification",
                All("r",C("Nat"),Iff(C("WellCovered",C("prism",I("r"))),Or(Eq(I("r"),D(0)),Eq(I("r"),D(2))))),
                "The attained even spectrum is a singleton precisely for three or five rungs. Outside those two orders it contains two distinct admissible cardinalities."),
            Node("twisted_wellCovered_iff", "First-power twisted classification",
                All("m",C("Nat"),Iff(C("WellCovered",C("graph",C("closing",I("m"),D(1)))),Le(I("m"),D(2)))),
                "The attained odd spectrum is a singleton precisely for two, three or four rungs. The two-rung graph includes its repeated closing boundary rather than assuming a longer cycle.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
