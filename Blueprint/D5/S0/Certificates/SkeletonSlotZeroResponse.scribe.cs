using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class SkeletonSlotZeroResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/SkeletonSlotZeroResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every slot candidate has a shared-zero response factorization and exact recurrent-capacity rank constraints.",
        H("Shared Zero Responses of Slot Skeletons"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-advance"),
                DeclarationHandle.Create(Prefix + "advance"),
                H("Advance"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse the single zero transition of the existing serialization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-advance-add"),
                DeclarationHandle.Create(Prefix + "advance_add"),
                H("Advance add"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All zero lengths are iterates of the same map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-evalfrom-zero-prefix"),
                DeclarationHandle.Create(Prefix + "evalFrom_zero_prefix"),
                H("Evalfrom zero prefix"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An arbitrary number of zero blocks can be removed using the original Option-valued evaluation, including every possible continuation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-gapslot"),
                DeclarationHandle.Create(Prefix + "gapSlot"),
                H("Gapslot"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After entering a transient slot, k+1 zeroes followed by one select this slot. Different k use the same zeroTarget, slotOf and returnTarget."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-evalfrom-one-zero-gap"),
                DeclarationHandle.Create(Prefix + "evalFrom_one_zero_gap"),
                H("Evalfrom one zero gap"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shared-gap factorization is tied to existing block evaluation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-probe"),
                DeclarationHandle.Create(Prefix + "probe"),
                H("Probe"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact one-hot readout of either a digit or a selected transient slot. The latter is a latent structural readout, not a supplied arithmetic oracle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-response"),
                DeclarationHandle.Create(Prefix + "response"),
                H("Response"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sampled joint zero responses with arbitrary row access states and delays."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-reach"),
                DeclarationHandle.Create(Prefix + "reach"),
                H("Reach"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One-hot intermediate recurrent states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-readout"),
                DeclarationHandle.Create(Prefix + "readout"),
                H("Readout"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The continuation response of each recurrent state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-response-factorization"),
                DeclarationHandle.Create(Prefix + "response_factorization"),
                H("Response factorization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sampled joint response factors through the actual recurrent carrier. No reachability, state ordering or self-loop restriction is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-response-rank-le"),
                DeclarationHandle.Create(Prefix + "response_rank_le"),
                H("Response rank le"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every candidate supplies a completion whose response rank is at most r."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-response-det-eq-zero"),
                DeclarationHandle.Create(Prefix + "response_det_eq_zero"),
                H("Response det eq zero"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every square response minor larger than the recurrent capacity vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("skeletonslotzeroresponse-capacity-ge-of-right-inverse"),
                DeclarationHandle.Create(Prefix + "capacity_ge_of_right_inverse"),
                H("Capacity ge of right inverse"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied right inverse is an exact finite lower-bound certificate for this response, requiring neither numerical rank thresholds nor determinants."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/SkeletonSlotCNF"))
        ]));
}
