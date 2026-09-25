using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ShuffleOrders.Binary;

internal sealed class ShuffleOrdersBinaryBinaryScheduleEvaluationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary schedule evaluation compares swapped fixed-source prefixes.",
        H("BinaryScheduleEvaluation"),
        Blocks(
            Paragraph(Text(
                "The source paper uses shuffle products and retains their alignment multiplicities. "
                + "This repository module supplies the fixed-source occurrence bookkeeping needed "
                + "later: equal letters and duplicate source factors are never identified.")),
            D("read-two", "readTwo", "Read an annotated binary occurrence",
                "readTwo first second reads index i from the source selected by Side and returns Option A, preserving the occurrence coordinate.", DescribeRole.Definition),
            D("evaluate-two", "evaluateTwo", "Evaluate a fixed-source schedule",
                "evaluateTwo maps occurrence annotation through readTwo and sequences the options; the source words are never permuted or replaced.", DescribeRole.Definition),
            D("valid-two-schedule", "ValidTwoSchedule", "Consume each source exactly once",
                "A binary schedule is valid for first and second exactly when its counts of Side.first and Side.second equal the respective source lengths.", DescribeRole.Definition))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
