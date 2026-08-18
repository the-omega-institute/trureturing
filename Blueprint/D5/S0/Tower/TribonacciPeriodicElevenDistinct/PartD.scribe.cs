using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicElevenDistinct;

internal sealed class PartDDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("Disjoint",
            Call("flatMap", Id("orbitStates"), Id("elevenOrbitsG05")),
            Call("flatMap", Id("orbitStates"), Id("elevenOrbitsG10")));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicElevenDistinct/PartD.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-eleven phase codes, part D.",
            H("Period Eleven Distinct D"),
            Blocks(
                Paragraph(Text(
                    "Grouping is by four here, not by five as at the shorter levels. Five was "
                        + "tried first and every across-group statement hit the default "
                        + "heartbeat budget; a probe showed three and four both clear it, and "
                        + "four gives the fewest pairs among the workable sizes. The budget was "
                        + "not raised.")),
                Describe.Lean(
                    DescribeId.Create("period-eleven-g05-and-g10-share-no-code"),
                    DeclarationHandle.Create(declarationPrefix + "eleven_g05_g10_state_codes_disjoint"),
                    H("Period Eleven Distinct D"),
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
