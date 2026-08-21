using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolPinsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The module's sole public theorem discharges every indexed protocol clause.",
        H("Inline Consensus Protocol Pins"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-required-inline-consensus-fixture-suite-is-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "required_fixture_suite_is_pinned"),
                H("The required inline-consensus fixture suite is pinned"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("clause"), Comma, Esc,
                    Call("ClauseObject", F.Id("clause"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RequiredFixtureSuite unfolds to forall clause, ClauseObject clause. ClauseId "
                        + "has ten constructors, and ClauseObject defines one proposition for each "
                        + "constructor.")),
                    Paragraph(Text(
                        "The theorem proves exactly that quantified family. Its intermediate fixture "
                        + "obligations are local proofs inside required_fixture_suite_is_pinned, not "
                        + "standalone public declarations."))),
                DescribeRole.Theorem))));
}
