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
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "readTwo" => Seq(Forall, Sp, F.Id("first"), Comma, F.Id("second"),
            Comma, F.Id("i"), Comma, Sp,
            Equal(Call("readTwo", F.Id("first"), F.Id("second"),
                    Call("pair", F.Id("firstSide"), F.Id("i"))),
                Call("getOptional", F.Id("first"), F.Id("i"))), Land,
            Equal(Call("readTwo", F.Id("first"), F.Id("second"),
                    Call("pair", F.Id("secondSide"), F.Id("i"))),
                Call("getOptional", F.Id("second"), F.Id("i")))),
        "evaluateTwo" => Seq(Forall, Sp, F.Id("first"), Comma,
            F.Id("second"), Comma, F.Id("schedule"), Comma, Sp,
            Equal(Call("evaluateTwo", F.Id("first"), F.Id("second"), F.Id("schedule")),
                Call("mapM", Call("annotateTwo", F.Id("schedule")),
                    Call("readTwo", F.Id("first"), F.Id("second"))))),
        "ValidTwoSchedule" => Seq(Forall, Sp, F.Id("first"), Comma,
            F.Id("second"), Comma, F.Id("schedule"), Comma, Sp,
            Call("ValidTwoSchedule", F.Id("first"), F.Id("second"), F.Id("schedule")),
            Iff, Equal(Call("count", F.Id("schedule"), F.Id("firstSide")),
                Call("length", F.Id("first"))), Land,
            Equal(Call("count", F.Id("schedule"), F.Id("secondSide")),
                Call("length", F.Id("second")))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
