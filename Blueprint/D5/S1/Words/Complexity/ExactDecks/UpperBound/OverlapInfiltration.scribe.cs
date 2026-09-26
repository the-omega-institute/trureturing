using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.UpperBound;

internal sealed class ExactDecksUpperBoundOverlapInfiltrationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Overlap infiltrations encode products of actual scattered counts with multiplicity.",
        H("OverlapInfiltration"),
        Blocks(
            Paragraph(Text(
                "The infiltration product and its top-degree shuffle stratum are classical and "
                + "are also used in the cited source. The list-valued definitions retain one "
                + "entry per alignment, so coincident output words remain repeated. The final "
                + "unconditional recovery theorem is the repository bridge used by the exact "
                + "asymptotic upper injection.")),
            D("overlap-infiltrations", "overlapInfiltrations", "Overlap infiltrations with multiplicity",
                "For words left,right over a decidable alphabet, overlapInfiltrations recursively records a left-only, right-only, and, when the leading letters agree, shared-position branch. It is a list, so distinct alignments yielding the same merged word remain distinct entries.", DescribeRole.Definition, true),
            D("ordinary-shuffles", "ordinaryShuffles", "Ordinary shuffles with multiplicity",
                "ordinaryShuffles recursively interleaves the two words using the left-only and right-only branches, retaining one list entry per positional choice.", DescribeRole.Definition, true),
            D("scattered-count-product", "scatteredCount_mul_eq_sum_overlapInfiltrations", "The actual infiltration product identity",
                "For all left,right,source over a decidable alphabet, scatteredCount left source times scatteredCount right source equals the sum of scatteredCount merged source over the full overlapInfiltrations list, including repeated merged words.", literature: true),
            D("top-overlap-is-shuffle", "overlapInfiltrations_filter_top_length", "The top-length stratum is shuffle",
                "Filtering overlapInfiltrations left right to merged words of length left.length+right.length gives literal list equality with ordinaryShuffles left right, preserving every multiplicity.", literature: true))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "overlapInfiltrations" => RecursiveDefinition("overlapInfiltrations", true),
        "ordinaryShuffles" => RecursiveDefinition("ordinaryShuffles", false),
        "scatteredCount_mul_eq_sum_overlapInfiltrations" => Seq(Forall, Sp,
            F.Id("left"), Comma, F.Id("right"), Comma, F.Id("source"), Comma,
            Sp, Equal(Multiply(Call("scatteredCount", F.Id("left"), F.Id("source")),
                Call("scatteredCount", F.Id("right"), F.Id("source"))),
                Call("sum", Call("overlapInfiltrations", F.Id("left"),
                    F.Id("right")), Call("lambda", F.Id("merged"),
                    Call("scatteredCount", F.Id("merged"), F.Id("source")))))),
        "overlapInfiltrations_filter_top_length" => Seq(Forall, Sp,
            F.Id("left"), Comma, F.Id("right"), Comma, Sp,
            Equal(Call("filterLength", Call("overlapInfiltrations", F.Id("left"),
                    F.Id("right")), Add(Call("length", F.Id("left")),
                    Call("length", F.Id("right")))),
                Call("ordinaryShuffles", F.Id("left"), F.Id("right")))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };

    private static Formula RecursiveDefinition(string name, bool allowOverlap)
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var u = F.Id("u");
        var v = F.Id("v");
        var left = Call("mapCons", a, Call(name, u, Call("cons", b, v)));
        var right = Call("mapCons", b, Call(name, Call("cons", a, u), v));
        var branch = allowOverlap
            ? Call("append", Call("append", left, right),
                Call("ifThenElse", Equal(a, b),
                    Call("mapCons", a, Call(name, u, v)), F.Id("empty")))
            : Call("append", left, right);
        return Seq(
            Open, Forall, Sp, v, Comma,
            Equal(Call(name, F.Id("empty"), v), Call("singleton", v)), Close, Land,
            Open, Forall, Sp, u, Comma,
            Equal(Call(name, u, F.Id("empty")), Call("singleton", u)), Close, Land,
            Forall, Sp, a, Comma, b, Comma, u, Comma, v, Comma,
            Equal(Call(name, Call("cons", a, u), Call("cons", b, v)), branch));
    }
}
