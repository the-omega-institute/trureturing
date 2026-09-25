using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ShuffleOrders.Binary;

internal sealed class ShuffleOrdersBinaryBinaryScheduleOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary schedules track ordered occurrences from two fixed sources.",
        H("BinaryScheduleOrder"),
        Blocks(
            Paragraph(Text(
                "The source paper uses shuffle products and retains their alignment multiplicities. "
                + "This repository module supplies the fixed-source occurrence bookkeeping needed "
                + "later: equal letters and duplicate source factors are never identified.")),
            D("side", "Side", "Two source labels",
                "Side is the two-constructor type first|second, with decidable equality; it records which unchanged source supplies each scheduled position.", DescribeRole.Definition),
            D("annotate-two-from", "annotateTwoFrom", "Occurrence annotation with offsets",
                "Given initial occurrence counters for both sides and a Side list, annotateTwoFrom labels every schedule entry by its zero-based occurrence number within that side and increments only the selected counter.", DescribeRole.Definition),
            D("annotate-two", "annotateTwo", "Zero-based occurrence annotation",
                "annotateTwo starts annotateTwoFrom at counter zero for both sources.", DescribeRole.Definition),
            D("shift-pair-occurrences", "shiftPairOccurrences", "Shift occurrence coordinates",
                "shiftPairOccurrences firstOffset secondOffset adds the matching offset to an annotated first or second occurrence without changing its side.", DescribeRole.Definition),
            D("annotate-two-from-add", "annotateTwoFrom_add", "Offset naturality",
                "For all offsets, schedules, and starting counters, annotation from offset starts equals mapping shiftPairOccurrences over annotation from the unshifted starts.", literature: false))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "Side" => Equal(F.Id("Side"), Call("TwoConstructors", F.Id("first"),
            F.Id("second"))),
        "annotateTwoFrom" => Seq(Forall, Sp, F.Id("p"), Comma, F.Id("q"),
            Comma, F.Id("s"), Comma, Sp,
            Equal(Call("annotateTwoFrom", F.Id("p"), F.Id("q"), F.Id("empty")),
                F.Id("empty")), Land,
            Equal(Call("annotateTwoFrom", F.Id("p"), F.Id("q"),
                    Call("cons", F.Id("first"), F.Id("s"))),
                Call("cons", Call("pair", F.Id("first"), F.Id("p")),
                    Call("annotateTwoFrom", Add(F.Id("p"), Num(1)), F.Id("q"),
                        F.Id("s")))), Land,
            Equal(Call("annotateTwoFrom", F.Id("p"), F.Id("q"),
                    Call("cons", F.Id("second"), F.Id("s"))),
                Call("cons", Call("pair", F.Id("second"), F.Id("q")),
                    Call("annotateTwoFrom", F.Id("p"), Add(F.Id("q"), Num(1)),
                        F.Id("s"))))),
        "annotateTwo" => Seq(Forall, Sp, F.Id("s"), Comma,
            Equal(Call("annotateTwo", F.Id("s")),
                Call("annotateTwoFrom", Num(0), Num(0), F.Id("s")))),
        "shiftPairOccurrences" => Seq(Forall, Sp, F.Id("p"), Comma,
            F.Id("q"), Comma, F.Id("i"), Comma, Sp,
            Equal(Call("shiftPairOccurrences", F.Id("p"), F.Id("q"),
                    Call("pair", F.Id("first"), F.Id("i"))),
                Call("pair", F.Id("first"), Add(F.Id("p"), F.Id("i")))), Land,
            Equal(Call("shiftPairOccurrences", F.Id("p"), F.Id("q"),
                    Call("pair", F.Id("second"), F.Id("i"))),
                Call("pair", F.Id("second"), Add(F.Id("q"), F.Id("i"))))),
        "annotateTwoFrom_add" => Seq(Forall, Sp, F.Id("p"), Comma,
            F.Id("q"), Comma, F.Id("u"), Comma, F.Id("v"), Comma,
            F.Id("s"), Comma, Sp,
            Equal(Call("annotateTwoFrom", Add(F.Id("p"), F.Id("u")),
                    Add(F.Id("q"), F.Id("v")), F.Id("s")),
                Call("map", Call("annotateTwoFrom", F.Id("u"), F.Id("v"),
                    F.Id("s")), Call("shiftPairOccurrences", F.Id("p"), F.Id("q"))))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
