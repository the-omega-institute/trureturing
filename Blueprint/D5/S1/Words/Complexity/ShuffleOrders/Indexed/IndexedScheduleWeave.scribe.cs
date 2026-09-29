using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ShuffleOrders.Indexed;

internal sealed class ShuffleOrdersIndexedIndexedScheduleWeaveDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleWeave";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected indexed traces can be refilled monotonically in fixed positions.",
        H("IndexedScheduleWeave"),
        Blocks(
            Paragraph(Text(
                "This module iterates the binary fixed-source promotion theorem over a list of "
                + "factors. Schedule labels are source positions, not factor values, so repeated "
                + "equal factors and repeated letters retain distinct identities.")),
            D("mapm-length", "mapM_length", "Successful option traversal preserves length",
                "For any read : B->Option A, entries, and word, entries.mapM read=some word implies word.length=entries.length."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Seq(Forall, Sp,
                F.Id("read"), Comma, F.Id("entries"), Comma, F.Id("word"), Comma,
                Equal(Call("mapM", F.Id("entries"), F.Id("read")),
                    Call("some", F.Id("word"))), Rightarrow,
                Equal(Call("length", F.Id("word")), Call("length", F.Id("entries")))))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
