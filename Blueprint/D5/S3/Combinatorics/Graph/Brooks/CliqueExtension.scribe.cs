using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class CliqueExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var g = I("G"); var v = I("V"); var n = I("n"); var f = I("f");
        var almost = C("cliqueMinusEdge", Seq(n, Sp, Minus, Sp, D(1)));
        var outside = C("Colorable", C("Induce", g, C("Compl", C("Range", f))), n);
        var body = All("n", C("Nat"), Imp(Le(D(3), n),
            Imp(Le(C("maxDegree", g), n), Imp(C("CliqueFree", g, Add(n, D(1))),
                All("f", C("Copy", almost, g), Imp(outside, C("Colorable", g, n)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A coloring outside a maximum-size clique with one missing edge extends across that copy; clique colorings can also avoid nonconstant prescribed outside colors.",
            H("Clique color extensions"), Blocks(
                Paragraph(Text("The graph cliqueMinusEdge(k) is the complete graph on Fin(k+2) with the edge between zero and one deleted. A Copy is injective and preserves adjacency; it need not reflect every nonedge.")),
                Describe.Lean(DescribeId.Create("almost-clique-extension"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Brooks/CliqueExtension.of_cliqueMinusEdge_copy"),
                    H("Extending over a clique with one missing edge"),
                    StatementSource.FromAuthor(Disp(Graphs(body))),
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/rabern2023brooks")),
                    Blocks(Paragraph(Text("For n at least three, assume maximum degree at most n and no clique of size n+1. In a copy of the almost-clique, each endpoint of the missing edge has at most one outside neighbor. Choose a common color for those endpoints that avoids both outside colors, then assign the remaining n-1 colors injectively to the other vertices. Degree saturation excludes outside neighbors at those other vertices. In the surgery argument, Hall's theorem supplies a clique coloring that avoids one outside color at each vertex whenever those forbidden colors are not all equal."))),
                    DescribeRole.Theorem))));
    }
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula I(string n) => F.Id(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Graphs(Formula b) => All("V", C("Type"), Inst("Fintype", I("V"),
        All("G", C("SimpleGraph", I("V")), Inst("DecidableRel", C("Adj", I("G")), b))));
}
