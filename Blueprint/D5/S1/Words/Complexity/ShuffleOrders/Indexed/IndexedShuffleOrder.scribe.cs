using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ShuffleOrders.Indexed;

internal sealed class ShuffleOrdersIndexedIndexedShuffleOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedShuffleOrder";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indexed Lyndon schedule evaluation is bounded by factor concatenation.",
        H("IndexedShuffleOrder"),
        Blocks(
            Paragraph(Text(
                "This module iterates the binary fixed-source promotion theorem over a list of "
                + "factors. Schedule labels are source positions, not factor values, so repeated "
                + "equal factors and repeated letters retain distinct identities.")),
            D("evaluate-schedule-le-flatten", "evaluateSchedule_le_flatten", "Ordered Lyndon concatenation is maximal",
                "For linearly ordered A, Lyndon factors in pairwise nonincreasing order, a valid indexed schedule, and successful evaluation word, one has word<=factors.flatten. The proof promotes the leading factor occurrence by occurrence and never collapses duplicate factor identities.", literature: false))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
