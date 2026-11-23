using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeFiniteLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sequential move count has the same finite law as the number of occupied ordinary bins.",
        H("Exact colored Cayley-tree move-count law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-sizes"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.native_daemon_occupancy"),
                H("Count law at every positive size"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("The source numerator sums the weights of legal terminal histories at a given length over every rooted tree and initial coloring. The denominator is the number of uniform ranking and colored-tree samples. On the other side the numerator counts words with the given occupancy, and the denominator counts all marked words. The anchor is zero, and a bin survives a throw exactly when its mark in the additive color group is zero."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var p = F.Id("P");
        var e = F.Id("e");
        var j = F.Id("j");
        var v = Call("Fin", n);
        var a = D(0);
        var colored = Call("Colored", v, Call("ZMod", k));
        var spell = Call("Throws", a, Call("ZMod", k));
        var den = Call("card", Call("SourceSample", n, k));
        var urnDen = Call("card", spell);
        var moved = Call("card", Call("TotalNumerator", e, p, j));
        var hit = Call("frequency", spell, F.Id("occupied"), j);
        var sizes = Equal(Call("card", Call("Away", a)), Subtract(n, D(1)));
        var microstates = Equal(Call("card", Call("Throw", v, Call("ZMod", k))), Multiply(n, k));
        var some = All("b", v, Equal(Call("card", Call("BinFiber", Call("some", F.Id("b")))), D(1)));
        var none = Equal(Call("card", Call("BinFiber", F.Id("none"))), Multiply(n, Subtract(k, D(1))));
        var law = Seq(Equal(Multiply(moved, urnDen), Multiply(hit, den)), Sp, Land, Sp,
            D(0), Lt, den, Sp, Land, Sp, D(0), Lt, urnDen, Sp, Land, Sp, sizes, Sp,
            Land, Sp, microstates, Sp, Land, Sp, Open, some, Close, Sp, Land, Sp, none);
        var parameters = All("K", F.Id("Type"), All("e", Call("Embedding", Call("ZMod", k), F.Id("K")),
            All("P", Seq(Open, F.Id("s"), Colon, Sp, colored, Close, Sp, To, Sp,
                Call("FreePolicy", F.Id("K"), Call("graph", F.Id("s")))), All("j", Nat, law))));
        return All("n", Nat, All("k", Nat,
            Seq(D(0), Lt, n, Sp, Implies, Sp, D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, parameters)));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
}
