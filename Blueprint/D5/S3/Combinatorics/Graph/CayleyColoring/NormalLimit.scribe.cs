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
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("Section 6 of de Panafieu, Mathieu, Potop-Butucaru and Tixeuil asks for this limit. The palette of initial colors is fixed at size k, and each row N has N plus one vertices. The ambient palette and valid policy may depend on the row. The count records actual updates from sequential uniform enabled choices. The expectation and variance are those under the independent uniform native source inputs and the conditional scheduler law. Exact equality of count distributions transports both moments and the standardized law to the occupancy model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-tree-probability-source-standardized"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.sourceStandardized"),
                H("Source count standardized by its own moments"),
                StatementSource.FromAuthor(Disp(StandardizedCount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("Here T is the source count as a real-valued function. Its mean and variance use the uniform source measure on the entire sample."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-tree-probability-source-standardized-law"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.sourceStandardizedLaw"),
                H("Law of the standardized source count"),
                StatementSource.FromAuthor(Disp(StandardizedLaw())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("This is the pushforward of the source measure by the exactly standardized count, regarded as a probability measure on the real line."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-tree-probability-source-moments"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.source_moments"),
                H("Source moments"),
                StatementSource.FromAuthor(Disp(MomentTransport())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The source mean and variance are the corresponding mean and variance for the row of n minus one throws."))),
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

    private static Formula StandardizedCount()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var e = F.Id("e");
        var sample = F.Id("s");
        var count = RealCount(n, k, e);
        var measure = Call("sourceMeasure", n, k);
        var centered = Subtract(At(count, sample), Integral(count, measure));
        var standardDeviation = Seq(Sqrt, Grp(Call("Var", count, measure)));
        var ratio = new Formula.Fraction(centered, standardDeviation);
        return All("n", Nat, All("k", Nat, UnderSourceEmbedding(k,
            All("s", Call("SourceSample", n, k), Equal(Call("sourceStandardized", e, sample), ratio)))));
    }

    private static Formula StandardizedLaw()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var e = F.Id("e");
        var hn = DefinitionDsl.Id("hn");
        var hk = DefinitionDsl.Id("hk");
        var law = Call("sourceStandardizedLaw", hn, hk, e);
        var map = Call("map", Call("sourceStandardized", e), Call("sourceMeasure", n, k));
        return All("n", Nat, All("k", Nat, All("hn", Seq(D(0), Lt, n),
            All("hk", Seq(D(2), Sp, Leq, Sp, k), UnderSourceEmbedding(k,
                Equal(Call("val", law), map))))));
    }

    private static Formula MomentTransport()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var m = Subtract(n, D(1));
        var e = F.Id("e");
        var policy = Seq(Open, F.Id("s"), Colon, Sp,
            Call("Colored", Call("Fin", n), Call("ZMod", k)), Close, Sp, To, Sp,
            Call("FreePolicy", F.Id("K"), Call("graph", F.Id("s"))));
        var sourceCount = RealCount(n, k, e);
        var sourceMeasure = Call("sourceMeasure", n, k);
        var occupancyCount = Call("literalCount", n, m);
        var occupancyMeasure = Call("literalMeasure", n, k, m);
        var expectation = Equal(Integral(sourceCount, sourceMeasure), Integral(occupancyCount, occupancyMeasure));
        var variance = Equal(Call("Var", sourceCount, sourceMeasure), Call("Var", occupancyCount, occupancyMeasure));
        return All("n", Nat, All("k", Nat, Seq(D(0), Lt, n, Sp, Implies, Sp,
            D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, UnderSourceEmbedding(k,
                Seq(Call("Nonempty", policy), Sp, Implies, Sp, expectation, Sp, Land, Sp, variance)))));
    }

    private static Formula UnderSourceEmbedding(Formula k, Formula body) =>
        Seq(OpenBracket, Call("NeZero", k), CloseBracket, Sp, All("K", F.Id("Type"),
            All("e", Call("Embedding", Call("ZMod", k), F.Id("K")), body)));

    private static Formula RealCount(Formula n, Formula k, Formula e) =>
        Lam("t", Call("SourceSample", n, k), Call("realCast", Call("sourceCount", e, F.Id("t"))));

    private static Formula Integral(Formula count, Formula measure) =>
        Seq(Int, Sp, At(count, F.Id("x")), Sp, F.Id("d"), measure, Open, F.Id("x"), Close);
}
