using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryTaskDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryTask.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intrinsic delayed semantics of the original birth", H("Intrinsic delayed semantics of the original birth"), Blocks(
            Describe.Lean(DescribeId.Create("literal-intrinsic-cast"),
                DeclarationHandle.Create(Owner + "intrinsic_cast"), H("Intrinsic semantics under literal equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Intrinsic delayed validity is invariant under equality transport of the entire original birth pack. The final realization uses this equivalence to execute a delayed request on the same original Q."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalhistorytask-0"),
                DeclarationHandle.Create(Owner + "local_semantics"), H("Local tasks and original whole birth tests"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The natural code uses the fixed mathlib equivalence from naturals to pairs of naturals, indexing the original birth clopen table B. Intrinsic validity means distinct whole measure labels, disjoint source and target clopens, original target Dirac points in V and the target clopen, and original source variation supported on the source clopen. On the old eligible row and label domain this is equivalent to the actual executable DelayedTask predicate on Q. No I, J, F, future carrier or final continuous map is part of intrinsic validity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stable-original-birth-semantics"),
                DeclarationHandle.Create(Owner + "stable_local"), H("Stability from canonical whole birth coherence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For two actual coherent proper states, an older row and eligible source and target labels, the local delayed predicate at the later Q is equivalent to Intrinsic on the earlier canonical whole birth. Preparation first reads the older predecessor pack, coherence identifies it with the original Q, and literal carrier equality transports that same pack. The global semantic condition is a consequence of these equalities, not an input to the local executor."))), DescribeRole.Theorem))));
}
