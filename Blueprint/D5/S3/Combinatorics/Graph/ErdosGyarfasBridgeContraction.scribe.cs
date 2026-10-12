using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ErdosGyarfasBridgeContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identifying the endpoints of a bridge preserves proper two-colourings, "
            + "minimum degree at least three, and the lengths of all cycles.",
        H("Bridge Contraction in Bipartite Graphs"),
        Blocks(
            Node("contraction", "Identifying the endpoints", "contraction", null,
                "For a graph G on V and vertices u and v, the contracted graph has vertex "
                    + "type {x in V | x differs from v}. Distinct remaining vertices x and y "
                    + "are adjacent precisely when G joins x to y, when x=u and G joins v "
                    + "to y, or when y=u and G joins x to v. The edge joining u and v is discarded.",
                DescribeRole.Definition),
            Node("cycle-confinement", "A cycle stays on one side of a cut vertex", "cycle_side_confinement", null,
                "Let G be any simple graph on V, a a vertex, and S a predicate on V. "
                    + "Suppose every edge x-y with x and y different from a satisfies S(x) "
                    + "if and only if S(y). For every closed walk p that is a cycle, either "
                    + "every vertex in its support equals a or satisfies S, or every vertex "
                    + "in its support equals a or fails S. Rotate a cycle containing a to "
                    + "begin there; its interior is a path avoiding a.", DescribeRole.Theorem),
            Node("colouring", "Two-colourability is preserved", "contraction_colorable",
                ColouringFormula(),
                "Use the original colouring on the component of u after deletion of the bridge. "
                    + "Exchange the colours of u and v on all other components. The redirected "
                    + "edges then have distinct endpoint colours.", DescribeRole.Theorem),
            Node("minimum-degree", "Minimum degree is preserved", "contraction_min_degree",
                DegreeFormula(),
                "The endpoints of a bridge have no common neighbour. Every other vertex "
                    + "retains its neighbours after the redirection, while the merged vertex "
                    + "has the disjoint union of the two endpoint neighbourhoods with the "
                    + "bridge endpoints omitted. Its degree is at least four.", DescribeRole.Theorem),
            Node("cycle-lift", "Cycles lift with unchanged length", "contraction_cycle_lift",
                LiftFormula(),
                "The merged vertex separates the two sides of the deleted bridge. A cycle "
                    + "lies wholly on one side together with that vertex. Inclusion lifts a "
                    + "cycle on the u side; replacing the merged vertex by v lifts a cycle "
                    + "on the other side. Both maps are injective on their respective sides.",
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Const(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula GraphContext(Formula body) =>
        All("V", Const("Type"), All("G", Call("SimpleGraph", F.Id("V")),
            All("u", F.Id("V"), All("v", F.Id("V"), body))));
    private static Formula Contracted() => Call("contraction", F.Id("G"), F.Id("u"), F.Id("v"));
    private static Formula Bridge() => Call("IsBridge", F.Id("G"), Call("Sym2", F.Id("u"), F.Id("v")));
    private static Formula ColouringFormula() => Disp(GraphContext(
        Imp(Bridge(), Imp(Call("Colorable", F.Id("G"), D(2)), Call("Colorable", Contracted(), D(2))))));
    private static Formula DegreeFormula() => Disp(GraphContext(
        Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("DecidableRel", Call("Adj", F.Id("G"))), CloseBracket, Sp,
            Imp(Bridge(), Imp(Call("Adj", F.Id("G"), F.Id("u"), F.Id("v")),
                Imp(All("z", F.Id("V"), Le(D(3), Call("degree", F.Id("G"), F.Id("z")))),
                    All("x", Call("ContractVertex", F.Id("v")),
                        Le(D(3), Call("degree", Contracted(), F.Id("x"))))))))));
    private static Formula LiftFormula() => Disp(GraphContext(
        Imp(Ne(F.Id("u"), F.Id("v")), Imp(Bridge(),
            All("w", Call("ContractVertex", F.Id("v")),
                All("p", Call("Walk", Contracted(), F.Id("w"), F.Id("w")),
                    Imp(Call("IsCycle", F.Id("p")), Exists("z", F.Id("V"),
                        Exists("q", Call("Walk", F.Id("G"), F.Id("z"), F.Id("z")),
                            And(Call("IsCycle", F.Id("q")),
                                Eq(Call("length", F.Id("q")), Call("length", F.Id("p")))))))))))));
}
