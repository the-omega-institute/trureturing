using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryPastDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryPast.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact strict-past proper limit input", H("The exact strict-past proper limit input"), Blocks(
            Describe.Lean(DescribeId.Create("strict-past-carrier-readback"),
                DeclarationHandle.Create(Owner + "carrier_read"), H("Exact earlier carrier readback"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For cutoffs at most omega-one, every carrier of an actual earlier state equals the strict prefix carrier at that same coordinate. Coordinates at most omega use the actual initial invariant; later coordinates use pairwise same-run coherence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("post-run-born-pack-read"),
                DeclarationHandle.Create(Owner + "bornPack_read"), H("Canonical whole old birth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Each whole birth is the original Q at its row and equals the transported old birth in every later actual state."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("post-run-post-i-read"),
                DeclarationHandle.Create(Owner + "postI_read"), H("Post-run incoming I"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At any proper cutoff the eligible I equals the actual incoming state I."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("post-run-post-j-read"),
                DeclarationHandle.Create(Owner + "postJ_read"), H("Post-run incoming J"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At any proper cutoff the eligible J equals the actual incoming state J."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("post-run-post-n-read"),
                DeclarationHandle.Create(Owner + "postN_read"), H("Post-run permanent N"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The original outgoing maximum reservoir equals each eligible incoming oldN. At a successor cutoff the outgoing last-row event is read only after the run is complete."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("post-run-post-laws"),
                DeclarationHandle.Create(Owner + "postLaws"), H("Every proper post-run slice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Original A through F and DI/DJ hold at every proper cutoff. The last row retains its actual whole birth and disjoint reservoirs even though E and F have strictly older row domains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-past-i-readback"),
                DeclarationHandle.Create(Owner + "I_read"), H("Incoming I readback"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("On every actual earlier state and strictly older row, the strict Data.I equals that state's actual incoming predecessor I."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-past-j-readback"),
                DeclarationHandle.Create(Owner + "J_read"), H("Incoming J readback"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a strictly older row and eligible old label, strict Data.J equals the actual incoming predecessor J at that earlier carrier stage."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalhistorypast-0"),
                DeclarationHandle.Create(Owner + "strictLaws"), H("Original eligible A through F on one strict past"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A pairwise coherent family of already constructed states below a proper successor-limit ordinal defines a literal Prefix. Each carrier and restriction is read from a later state of that same past. Each whole birth is its original Q; permanent N is read from the original outgoing maximum event, whose successor arrival lies strictly below the limit. Incoming I and J are read at the carrier stage. Canonical birth and arrival equalities identify A, B, C, E and regular bounded F with actual predecessor evidence, while pairwise coherence gives DI and DJ. No completed-history or future-stage semantic predicate enters these proper-limit input laws."))), DescribeRole.Theorem))));
}
