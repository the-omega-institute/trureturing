using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NodupAssembly;

internal sealed class PeriodTenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("Nodup", Id("seg0"));

        const string declarationPrefix = "D5/S0/Tower/NodupAssembly/PeriodTen.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "No state code is shared by two of the forty-two period-ten representatives.",
            H("Period Ten Assembly"),
            Blocks(
                Paragraph(Text(
                    "The adapter and the append lemma come from the period-nine assembly rather "
                        + "than being restated, so there is one definition of each. The "
                        + "concatenation is right associated because that is the shape the "
                        + "append and disjointness lemmas expect; the nine tails are named so "
                        + "that no line carries the whole nesting.")),
                Describe.Lean(
                    DescribeId.Create("period-ten-codes-have-no-duplicates"),
                    DeclarationHandle.Create(declarationPrefix + "ten_all_codes_nodup"),
                    H("Period ten codes have no duplicates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The components were already proved: nine within-group statements and "
                            + "thirty-six across-group statements. Only their combination was "
                            + "missing, and it was deferred once at each of three levels before "
                            + "being retried."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NodupAssembly/PeriodNine")),
            ]));
    }
}
