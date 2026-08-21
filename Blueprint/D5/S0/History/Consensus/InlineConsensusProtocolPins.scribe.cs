using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolPinsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Aggregate mutation pins for the complete inline consensus protocol contract.",
        H("Inline Consensus Protocol Pins"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-required-inline-consensus-fixture-suite-is-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "required_fixture_suite_is_pinned"),
                H("The required inline-consensus fixture suite is pinned"),
                StatementSource.FromAuthor(Disp(F.Id("RequiredFixtureSuite"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RequiredFixtureSuite is the conjunction declared in Lean. It includes the "
                        + "stage and carrier equations, disclosure and completion contracts, internal "
                        + "model wiring, Boolean correspondences, router optimality, bounded-run "
                        + "guarantees, named executable and negative fixtures, and the clause, permit-"
                        + "freshness, carrier-governance, and executable-routing pins.")),
                    Paragraph(Text(
                        "The proof supplies each conjunct from a named Lean theorem and also supplies "
                        + "ClauseObject for every ClauseId. The displayed proposition is the named "
                        + "RequiredFixtureSuite itself; it does not strengthen that conjunction or "
                        + "claim correspondence to any external protocol prose."))),
                DescribeRole.Theorem))));
}
