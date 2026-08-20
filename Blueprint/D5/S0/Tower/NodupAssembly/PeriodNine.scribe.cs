using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NodupAssembly;

internal sealed class PeriodNineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("Nodup", Id("nineAllCodes"));

        const string declarationPrefix = "D5/S0/Tower/NodupAssembly/PeriodNine.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "No state code is shared by two of the twenty-six period-nine representatives.",
            H("Period Nine Assembly"),
            Blocks(
                Paragraph(Text(
                    "This assembly was deferred three times, at periods nine, ten and eleven, "
                        + "each time on the ground that the shape after the append lemma does "
                        + "not match a flat tuple. That was true and not an obstacle: the append "
                        + "lemma wants a pairwise inequality where the components give "
                        + "disjointness, and the gap is a three-line adapter. The fold over six "
                        + "groups is then mechanical.")),
                Describe.Lean(
                    DescribeId.Create("period-nine-codes-have-no-duplicates"),
                    DeclarationHandle.Create(declarationPrefix + "nine_all_codes_nodup"),
                    H("Period nine codes have no duplicates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The components were already proved: six within-group statements and "
                            + "fifteen across-group statements. Only their combination was "
                            + "missing."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineDistinct")),
            ]));
    }
}
