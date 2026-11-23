using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeRootedCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero color-difference mark identifies a conflict at the edge to the parent.",
        H("Rooted tree color coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-mark"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.zero_pattern_iff"),
                H("Zero marks and equal colors"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Combinatorics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("Each non-root vertex indexes its edge to its parent. The color equivalence stores the root color and the differences on these edges. Evaluation at the indexed edge gives zero exactly when the endpoints started with the same color. This is the edge-coordinate version of the independent conflicts used in Theorem 10."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var a = F.Id("A");
        var t = F.Id("T");
        var r = F.Id("r");
        var c = F.Id("c");
        var x = F.Id("x");
        var marks = Call("snd", At(Call("edgeColorEquiv", t, r), c));
        var zero = Equal(At(marks, Call("edgeEquiv", t, r, x)), D(0));
        var conflict = Equal(At(c, Call("val", x)), At(c, Call("parent", t, r, x)));
        var point = All("x", Call("Away", v, r), Seq(zero, Sp, Iff, Sp, conflict));
        return All("V", F.Id("Type"), All("A", F.Id("Type"), Seq(Instance("AddGroup", a),
            All("T", Call("Tree", v), All("r", v, All("c", Arrow(v, a), point))))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);
}
