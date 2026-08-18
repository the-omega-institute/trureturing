using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NodupAssembly;

internal sealed class PeriodElevenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("Nodup", Id("seg0"));

        const string declarationPrefix = "D5/S0/Tower/NodupAssembly/PeriodEleven.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "No state code is shared by two of the seventy-four period-eleven representatives.",
            H("Period Eleven Assembly"),
            Blocks(
                Paragraph(Text(
                    "The fold is the same shape as at the two shorter levels, only longer: "
                        + "nineteen groups rather than nine, because this level is grouped by "
                        + "four. The concatenation is right associated because that is the "
                        + "shape the append and disjointness lemmas expect, and the eighteen "
                        + "tails are named so that no line carries the whole nesting.")),
                Paragraph(Text(
                    "Unlike the shorter levels this one calls the pinned library's append "
                        + "lemma directly instead of a local adapter. The adapter restated a "
                        + "lemma that the library already had with the same three hypotheses; "
                        + "that duplication is recorded and is not carried forward here.")),
                Describe.Lean(
                    DescribeId.Create("period-eleven-codes-have-no-duplicates"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_period_eleven_state_codes_nodup"),
                    H("Period eleven codes have no duplicates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The components were already proved: nineteen within-group statements "
                            + "and one hundred and seventy-one across-group statements. Only "
                            + "their combination was missing. That the nineteen groups partition "
                            + "the seventy-four representatives exactly is a property of the "
                            + "group definitions rather than of this theorem, and was checked by "
                            + "reading them."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartA")),
            ]));
    }
}
