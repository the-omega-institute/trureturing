using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicElevenDistinct;

internal sealed class PartADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("Nodup", Call("flatMap", Id("orbitStates"), Id("elevenOrbitsG01")));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartA.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-eleven phase codes, part A.",
            H("Period Eleven Distinct A"),
            Blocks(
                Paragraph(Text(
                    "Grouping is by four here, not by five as at the shorter levels. Five was "
                        + "tried first and every across-group statement hit the default "
                        + "heartbeat budget; a probe showed three and four both clear it, and "
                        + "four gives the fewest pairs among the workable sizes. The budget was "
                        + "not raised.")),
                Describe.Lean(
                    DescribeId.Create("period-eleven-group-one-codes-are-distinct"),
                    DeclarationHandle.Create(declarationPrefix + "eleven_g01_state_codes_nodup"),
                    H("Period Eleven Distinct A"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Assembling the components into one statement over the whole list is "
                            + "not done here, as at the shorter levels, and remains open."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenData")),
            ]));
    }
}
