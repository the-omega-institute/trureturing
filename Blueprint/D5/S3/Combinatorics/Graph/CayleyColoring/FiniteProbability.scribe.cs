using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeFiniteProbabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native move count and literal occupancy have identical distributions in every positive row.",
        H("From marked draws to the source probability law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("word-pushforward"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.microstate_word_law"),
                H("Coordinatewise pushforward of the marked word"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The marked word is uniform on functions from the throw coordinates to pairs of a bin and a color mark. This is the product of uniform pair measures. Pushforward along the coordinatewise bin map therefore yields the product of the one-throw laws. The result includes the empty word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.source_occupancy_law"),
                H("Equality of source and occupancy distributions"),
                StatementSource.FromAuthor(Disp(Statement2())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("The source samples a root, a native labeled tree, and each initial color independently and uniformly. A uniform ranking supplies the conditional law of the legal sequential histories for any valid free-color policy. The native all-size count law is converted to equal singleton masses, and reindexing the non-anchor coordinates preserves exactly which ordinary bins appear."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var m = F.Id("m");
        var w = F.Id("w");
        var i = F.Id("i");
        var times = Call("Fin", m);
        var pairs = Seq(Call("Fin", n), Sp, Times, Sp, Call("ZMod", k));
        var words = Arrow(times, pairs);
        var wordMap = Lam("w", words, Lam("i", times, Call("bin", At(w, i))));
        var law = Equal(Call("map", Call("uniform", words), wordMap), Call("literalMeasure", n, k, m));
        return All("n", Nat, All("k", Nat, Seq(Instance("NeZero", k), All("m", Nat,
            Seq(D(0), Lt, n, Sp, Implies, Sp, D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, law)))));
    }

    private static Formula Statement2()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var K = F.Id("K");
        var e = F.Id("e");
        var native = Call("SourceSample", n, k);
        var colored = Call("Colored", Call("Fin", n), Call("ZMod", k));
        var m = Subtract(n, D(1));
        var count = Lam("t", native, Call("realCast", Call("sourceCount", e, F.Id("t"))));
        var law = Call("IdentDistrib", count, Call("literalCount", n, m),
            Call("sourceMeasure", n, k), Call("literalMeasure", n, k, m));
        var policy = Seq(Open, F.Id("s"), Colon, Sp, colored, Close, Sp, To, Sp,
            Call("FreePolicy", K, Call("graph", F.Id("s"))));
        // The conclusion is independent of the particular admissible free-color policy.
        var premise = Call("Nonempty", policy);
        var parameters = All("K", F.Id("Type"), All("e", Call("Embedding", Call("ZMod", k), K),
            Seq(premise, Sp, Implies, Sp, law)));
        return All("n", Nat, All("k", Nat, Seq(Instance("NeZero", k), D(0), Lt, n, Sp, Implies,
            Sp, D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, parameters)));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Lam(string x, Formula type, Formula body) =>
        Seq(Open, F.Id(x), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
}
