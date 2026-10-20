using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class ColoringExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var g = I("G"); var v = I("V");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Odd closed walks contain odd cycles; finite graphs admit the greedy degree bound and color-preserving vertex extensions.",
            H("Coloring extensions and degree reduction"), Blocks(
                Describe.Lean(DescribeId.Create("odd-cycle"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Brooks/ColoringExtension.HasOddCycle"),
                    H("An actual odd cycle"),
                    StatementSource.FromAuthor(Disp(All("V", C("Type"), All("G", C("SimpleGraph", v),
                        Iff(C("HasOddCycle", g), Exists("x", v,
                            Exists("p", C("Walk", g, I("x"), I("x")),
                                And(C("IsCycle", I("p")), C("Odd", C("length", I("p"))))))))))),
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/rabern2023brooks")),
                    Blocks(Paragraph(Text("An odd cycle is a closed walk satisfying the native cycle predicate and having odd length. Containing such a cycle does not by itself say that all vertices or edges belong to it."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("greedy-degree-bound"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Brooks/ColoringExtension.colorable_maxDegree_succ"),
                    H("The greedy maximum-degree bound"),
                    StatementSource.FromAuthor(Disp(Graphs(C("Colorable", g, Add(C("maxDegree", g), D(1)))))),
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/rabern2023brooks")),
                    Blocks(Paragraph(Text("Add vertices one at a time. At most the maximum degree colors are forbidden, so one of the maximum degree plus one colors remains. The vertex type may be empty. Deleting a maximal independent set lowers the maximum degree, and adding that set back costs at most one color. Prescribed-color extensions preserve colors already assigned; they allow the later path construction to keep its endpoint colors fixed."))),
                    DescribeRole.Theorem))));
    }
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
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Graphs(Formula b) => All("V", C("Type"), Inst("Fintype", I("V"),
        All("G", C("SimpleGraph", I("V")), Inst("DecidableRel", C("Adj", I("G")), b))));
}
