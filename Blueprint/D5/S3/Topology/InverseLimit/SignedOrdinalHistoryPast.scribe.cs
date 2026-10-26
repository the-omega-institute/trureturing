using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryPastDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact strict-past proper limit input", H("The exact strict-past proper limit input"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalhistorypast-0"),
                DeclarationHandle.Create(Owner + "strictLaws"), H("Original eligible A through F on one strict past"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A pairwise coherent family of already constructed states below a proper successor-limit ordinal defines a literal Prefix. Each carrier and restriction is read from a later state of that same past. Each whole birth is its original Q; permanent N is read from the original outgoing maximum event, whose successor arrival lies strictly below the limit. Incoming I and J are read at the carrier stage. Canonical birth and arrival equalities identify A, B, C, E and regular bounded F with actual predecessor evidence, while pairwise coherence gives DI and DJ. No completed-history or future-stage semantic predicate enters these proper-limit input laws.")),
                    Paragraph(Text("The four-slot escape registration remains unfinished under issue 21750; the Reg mirror checks exact source reconstruction and does not claim declared_validated."))), DescribeRole.Theorem))));
}
