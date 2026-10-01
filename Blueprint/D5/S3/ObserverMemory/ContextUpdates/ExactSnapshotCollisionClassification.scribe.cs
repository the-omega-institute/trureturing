using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ContextUpdates;

internal sealed class ExactSnapshotCollisionClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact decoding and source injectivity are characterized by collisions on reachable branches.",
        H("Exact Snapshot Collision Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-recovery-iff-branches"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.exact_recovery_iff_branch_conditions"),
                H("Exact recovery is equivalent to the branch collision conditions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a surjective characteristic and a finite set of at least three senders, "
                        + "a deterministic protocol has a decoder recovering the target on "
                        + "all sources exactly when every reachable branch has fibre separation and satisfies "
                        + "the one-exception-or-common-involution alternative. Fibre separation means that every "
                        + "reply map is injective on each of chi inverse zero and chi inverse one. The alternative "
                        + "requires either at most one noninjective sender or an element tau with chi(tau)=1 and "
                        + "tau+tau=0 such that every nontrivial reply collision y versus x has y-x=tau.")),
                    Paragraph(Text(
                        "For necessity, complete the parity with another sender to separate equal-characteristic "
                        + "inputs. For collisions d and e at two distinct senders, a third sender completes "
                        + "the parity. Comparing the two collisions in the same and opposite orientations forces "
                        + "d+e=0 and d-e=0. Fixing one collision in each of two senders then makes all "
                        + "nontrivial collision differences equal to the same odd involution.")),
                    Paragraph(Text(
                        "For sufficiency with one possible exceptional sender, all other coordinates are fixed, "
                        + "parity fixes the last characteristic, and fibre separation fixes the last value. "
                        + "For a common involution, induction over the sender set makes the total difference "
                        + "either zero or tau; equal parity excludes tau.")),
                    Paragraph(Text(
                        "The reverse implication constructs a decoder by assigning to each observation the "
                        + "unique target value on its source fibre; observations outside the image receive an "
                        + "arbitrary value. Empty branches therefore impose no condition. Only actual collision "
                        + "pairs are constrained: not every pair differing by tau must be merged. Both the "
                        + "exceptional sender and tau may depend on the branch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-injective-iff-branch-single"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.source_injective_iff_branch_single"),
                H("Source injectivity is equivalent to at most one noninjective sender per branch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the protocol has an exact decoder. The observation map is injective on the "
                        + "actual source space exactly when every reachable branch has at most one noninjective "
                        + "sender. The characteristic is surjective and there are at least three senders.")),
                    Paragraph(Text(
                        "If two senders collide, the common odd involution and a third sender produce two distinct "
                        + "sources with the same observation. If at most one sender is noninjective, all other "
                        + "coordinates are fixed by their replies. Exact decoding fixes the total sum and hence "
                        + "the remaining coordinate; the clock then fixes the kernel offset."))),
                DescribeRole.Theorem))));
}
