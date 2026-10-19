using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class GeneralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var g = I("G"); var v = I("V"); var n = I("n");
        var delta = C("maxDegree", g);
        var color = C("Colorable", g, delta);
        var exception = Or(Not(C("CliqueFree", g, Add(delta, D(1)))),
            And(Eq(delta, D(2)), C("HasOddCycle", g)));
        var cycle = Exists("n", C("Nat"), And(C("Odd", n),
            And(Le(D(5), n), C("Nonempty", C("GraphIso", C("cycleGraph", n), g)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every finite graph that cannot be colored with its maximum degree contains a maximum-degree-plus-one clique or an odd cycle at maximum degree two. Connected exceptions are complete graphs or entire odd cycles.",
            H("Brooks' theorem and connected exceptions"), Blocks(
                Node("brooks", "brooks-alternative", "The arbitrary-degree alternative",
                    Graphs(Imp(Not(color), exception)),
                    "The coloring construction follows Rabern's surgery proof. Delete a maximal independent set, color the smaller induced graph, and extend across its clique or cycle obstruction. The low-degree vertex extension is supplied by its existing coloring theorem. The degree has no upper bound. The vertex type may be empty, and neither connectedness nor regularity is assumed."),
                Node("brooks_connected", "connected-alternative", "Complete graphs and entire odd cycles",
                    Graphs(Imp(C("Connected", g), Or(color, Or(Eq(g, C("completeGraph", v)), cycle)))),
                    "A clique with maximum degree plus one vertices saturates every member's neighbors. No edge can leave it, so connectedness makes it the whole graph. A cycle in a graph of maximum degree at most two likewise saturates every cycle vertex. Connectedness makes its support all vertices and its edges all edges. The cycle length therefore equals the number of vertices. Its native cycle copy is bijective and reflects adjacency because both neighbor sets have cardinality two. A three-cycle is complete; every remaining odd cycle has length at least five. Complete graphs with one, two or three vertices are included."))));
    }
    private static DocumentBlock Node(string selector, string id, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(
            "D5/S3/Combinatorics/Graph/Brooks/General." + selector), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/rabern2023brooks")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula I(string n) => F.Id(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Exists(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Graphs(Formula b) => All("V", C("Type"), Inst("Fintype", I("V"),
        All("G", C("SimpleGraph", I("V")), Inst("DecidableRel", C("Adj", I("G")), b))));
}
