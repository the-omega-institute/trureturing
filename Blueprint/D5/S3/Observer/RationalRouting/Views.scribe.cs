using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.RationalRouting;

internal sealed class ViewsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original rational, chronological word, rooted named path and indexed memory retain one another exactly.",
        H("Finite original-view reconstruction"),
        Blocks(
            Paragraph(Text("The root pair is (1,1). L sends (p,q) to (p,p+q) and R sends it to (p+q,q). encode executes the head first. The decoder subtracts the smaller positive coordinate from the larger and appends the peeled last letter to the recursively decoded predecessor. Every recursive step decreases p+q. The input rational uses its reduced positive numerator and denominator, and all inverse arithmetic is on this known output pair.")),
            Describe.Lean(DescribeId.Create("original-rational-views-reconstruct"),
                DeclarationHandle.Create("D5/S3/Observer/RationalRouting/Views.original_views_reconstruct"),
                H("Actual-image finite inverses"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive coprime pair the encoder of its decoded chronological word is that same pair. For every finite Boolean word the decoded encoded pair is that very word, including the empty word. Its pair ratio equals the attained response of the actual chronological source started at 1, and decoding that ratio returns the same word.")),
                    Paragraph(Text("For every positive rational x, each of B,T,S,M and their full joint output has a finite decoder returning x. B is x itself. T is its entire chronological word. S retains the distinguished root occurrence (0,(1,1)), the indexed final occurrence, and every oriented edge with its name, source index, target index and both endpoint pairs. M retains every indexed prefix pair from index 0 through the original word length. The full output contains all four. Equal numeric vertex values do not collapse occurrence indices or edge names.")),
                    Paragraph(Text("The path decoder reads the edge names in their rooted orientation. The memory decoder reads its final indexed pair, rather than replacing the table by a scalar length. The constructions and decoders are finite computations on their actual images. Composing the rational decoder of one view with the construction of another gives the corresponding actual-image transport in either direction. No unknown archive, acquired infinite thread, extra source motion or inverse physical action is used."))),
                DescribeRole.Theorem))));

    private static Formula Statement() => Disp(Seq(
        Open, Forall, Sp, F.Id("p"), Comma, F.Id("q"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        D(0), Lt, F.Id("p"), Land, D(0), Lt, F.Id("q"), Land, Call("Coprime", F.Id("p"), F.Id("q")),
        Longrightarrow, Call("encode", Call("decode", F.Id("p"), F.Id("q"))), Eq, Open, F.Id("p"), Comma, F.Id("q"), Close, Close, Land, Sp,
        Open, Forall, Sp, F.Id("w"), Comma, Call("decode", Call("encode", F.Id("w"))), Eq, F.Id("w"), Close, Land, Sp,
        Open, Forall, Sp, F.Id("V"), Comma, F.Id("x"), Comma, D(0), Lt, F.Id("x"),
        Longrightarrow, Sp, Call("recover", F.Id("V"), Call("original", F.Id("V"), F.Id("x"))), Eq, F.Id("x"), Close,
        Land, Sp, Open, Forall, Sp, F.Id("w"), Comma,
        Call("ratio", Call("encode", F.Id("w"))), Eq, Call("attain", F.Id("w"), D(1)), Close, Land, Sp,
        Open, Forall, Sp, F.Id("w"), Comma,
        Call("originalWord", Call("ratio", Call("encode", F.Id("w")))), Eq, F.Id("w"), Close));
}
