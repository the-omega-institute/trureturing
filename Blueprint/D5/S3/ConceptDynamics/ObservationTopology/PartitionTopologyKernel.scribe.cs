using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class PartitionTopologyKernelDocument : IScribeDocumentDefinition
{
    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inseparability in a readout partition topology is exactly equality in the readout "
            + "kernel.",
        H("Partition Topology Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("partition-inseparability-is-readout-equality"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel."
                    + "partition_inseparable_iff_kernel"),
            H("Partition-topology inseparability is equality of readouts"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The partition topology is induced by the readout into a discrete "
                        + "coordinate space. Every open set is therefore a union of readout "
                        + "fibers.")),
                Paragraph(Text(
                    "Equal readouts place two states in the same fiber, so no open set can "
                        + "distinguish them.")),
                Paragraph(Text(
                    "If the readouts differ, the preimage of the singleton containing the "
                        + "first readout is open and contains exactly one of the two states. "
                        + "Thus topological inseparability is equivalent to kernel equality."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("B");
        Formula readout = F.Id("readout");
        Formula first = F.Id("x");
        Formula second = F.Id("y");

        return Disp(Seq(
            Forall, Sp, readout, Colon, Sp, Call("Concept", state, coordinate),
            Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, state, Comma, Sp,
            Call(
                "Inseparable",
                Call("partitionTopology", readout),
                first,
                second),
            Sp, Iff, Sp,
            Apply(readout, first), Sp, Eq, Sp, Apply(readout, second), Dot));
    }
}
