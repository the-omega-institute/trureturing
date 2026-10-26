using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryTaskDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryTask.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intrinsic delayed semantics of the original birth", H("Intrinsic delayed semantics of the original birth"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalhistorytask-0"),
                DeclarationHandle.Create(Owner + "local_semantics"), H("Local tasks and original whole birth tests"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The natural code uses the fixed mathlib equivalence from naturals to pairs of naturals, indexing the original birth clopen table B. Intrinsic validity means distinct whole measure labels, disjoint source and target clopens, original target Dirac points in V and the target clopen, and original source variation supported on the source clopen. On the old eligible row and label domain this is equivalent to the actual executable DelayedTask predicate on Q. No I, J, F, future carrier or final continuous map is part of intrinsic validity.")),
                    Paragraph(Text("The four-slot escape registration remains unfinished under issue 21750; the Reg mirror checks exact source reconstruction and does not claim declared_validated."))), DescribeRole.Theorem))));
}
