using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeNormalLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sequential recoloring count on a uniformly rooted colored Cayley tree converges after exact standardization.",
        H("The colored Cayley-tree central limit theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("colored-tree-limit"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt"),
                H("Central limit theorem for the sequential move count"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Combinatorics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("Section 6 of de Panafieu, Mathieu, Potop-Butucaru and Tixeuil asks for this limit. The palette of initial colors is fixed at size k, and each row N has N plus one vertices. The ambient palette and valid policy may depend on the row. The count records actual updates from sequential uniform enabled choices. The expectation and variance are those under the independent uniform native source inputs and the conditional scheduler law. Exact equality of count distributions transports both moments and the standardized law to the occupancy model."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("N");
        var k = F.Id("k");
        var kFamily = F.Id("K");
        var e = F.Id("e");
        var size = Add(n, D(1));
        var rowPalette = At(kFamily, n);
        var rowEmbedding = At(e, n);
        var colored = Call("Colored", Call("Fin", size), Call("ZMod", k));
        var policyRows = Seq(Open, n, Colon, Sp, Nat, Close, Sp, To, Sp,
            Open, F.Id("s"), Colon, Sp, colored, Close, Sp, To, Sp,
            Call("FreePolicy", rowPalette, Call("graph", F.Id("s"))));
        var realCount = Lam("t", Call("SourceSample", size, k),
            Call("realCast", Call("sourceCount", rowEmbedding, F.Id("t"))));
        var positive = Seq(D(0), Lt, Call("Var", realCount, Call("sourceMeasure", size, k)));
        var eventually = Call("Eventually", Lam("N", Nat, positive), F.Id("atTop"));
        var rows = Lam("N", Nat, Call("sourceStandardizedLaw", size, k, rowEmbedding));
        var convergence = Call("Tendsto", rows, F.Id("atTop"), Call("nhds", Call("gaussianReal", D(0), D(1))));
        var result = Seq(eventually, Sp, Land, Sp, convergence);
        var family = All("K", Arrow(Nat, F.Id("Type")),
            All("e", Seq(Open, n, Colon, Sp, Nat, Close, Sp, To, Sp,
                Call("Embedding", Call("ZMod", k), rowPalette)),
                Seq(Call("Nonempty", policyRows), Sp, Implies, Sp, result)));
        return All("k", Nat, Seq(D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, family));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Lam(string x, Formula type, Formula body) =>
        Seq(Open, F.Id(x), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
}
